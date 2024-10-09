section \<open>Total heap semantics of statements\<close>

theory TotalSemantics
imports ViperCommon.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

definition vals_well_typed :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a val) list \<Rightarrow> vtyp list \<Rightarrow> bool"
  where "vals_well_typed A vs ts \<equiv> map (get_type A) vs = ts"

lemma vals_well_typed_same_lengthD:
  assumes "vals_well_typed A vs ts"
  shows "length vs = length ts"
  using assms
  unfolding vals_well_typed_def
  by auto

fun exh_if_total :: "bool \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total"  where
  "exh_if_total False _ = RFailure"
| "exh_if_total True \<omega> = RNormal \<omega>"

lemma exh_if_total_normal:
  assumes "exh_if_total b \<omega> = RNormal \<omega>"
  shows b
  using assms
  by (auto elim: exh_if_total.elims)

lemma exh_if_total_normal_2:
  assumes "exh_if_total b \<omega> = RNormal \<omega>'"
  shows "\<omega> = \<omega>'"
  using assms
  by (auto elim: exh_if_total.elims)

lemma exh_if_total_failure:
  assumes "exh_if_total b \<omega> = RFailure"
  shows "\<not>b"
  using assms
  by (auto elim: exh_if_total.elims)

definition exhale_perm_single :: "preal mask \<Rightarrow> heap_loc \<Rightarrow> preal option \<Rightarrow> (preal mask) set"
  where "exhale_perm_single m lh p_opt =
      {m'| m' q. 
               (p_opt = None \<longrightarrow> pgt q pnone) \<and>
               option_fold ((=) q) (q \<noteq> pnone \<and> pgt (m lh) q) p_opt \<and>
               m' = m(lh := (m lh) - q)
       }"

inductive red_exhale :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "'a full_total_state \<Rightarrow> bool" and \<omega>0 :: "'a full_total_state"
  where

\<comment>\<open>exhale acc(e.f, p)\<close>
  ExhAcc: 
  "\<lbrakk>  mh = get_mh_total_full \<omega>;
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega> 
                          ( exh_if_total (p \<ge> 0 \<and> (if r = Null then p = 0 else pgte (mh (a,f)) (Abs_preal p)))
                                         (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((mh (a,f)) - (Abs_preal p)))
                          )"

\<comment>\<open>Exhaling wildcard removes some non-zero permission that is less than the current permission held.\<close>
| ExhAccWildcard:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     a = the_address r;
     \<comment>\<open>If the reduction leads to failure (i.e. the left-hand side \<^prop>\<open>mh (a,f) \<noteq> 0 \<and> r \<noteq> Null\<close> is false),
        then any instantiation of \<^term>\<open>q\<close> works (\<^term>\<open>q\<close> is relevant only in the case of success).\<close>
     mh (a,f) \<noteq> 0 \<and> r \<noteq> Null \<Longrightarrow> q > 0 \<and> mh (a,f) > q 
   \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f Wildcard)) \<omega>
                          (exh_if_total (mh (a,f) \<noteq> 0 \<and> r \<noteq> Null) 
                                        (update_mh_loc_total_full \<omega> (a,f) (mh (a,f) - q)))"
\<comment>\<open>exhale acc(P(es), p)\<close>
| ExhAccPred:
   "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt R (Some \<omega>0) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>
            (exh_if_total (p \<ge> 0 \<and> pgte (mp(pred_id, v_args)) (Abs_preal p)) 
                          (update_mp_loc_total_full \<omega> (pred_id, v_args) (mp (pred_id, v_args) - (Abs_preal p))))"
| ExhAccPredWildcard:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt R (Some \<omega>0) e_args \<omega> (Some v_args);
     \<comment>\<open>If the reduction leads to failure (i.e. the left-hand side \<^prop>\<open>mp (pred_id, v_args) \<noteq> 0\<close> is false),
       then any instantiation of \<^term>\<open>q\<close> works (\<^term>\<open>q\<close> is relevant only in the case of success).\<close>
     mp (pred_id, v_args) \<noteq> 0 \<Longrightarrow> q > 0 \<and> mp (pred_id, v_args) > q    
   \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>
                          (exh_if_total (mp (pred_id, v_args) \<noteq> 0)
                                        (update_mp_loc_total_full \<omega> (pred_id, v_args) (mp (pred_id, v_args) - q)))"

| ExhPure:
  "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Pure e)) \<omega> (exh_if_total b \<omega>)"

\<comment>\<open>exhale A && B\<close>
| ExhStarNormal: 
 "\<lbrakk> red_exhale ctxt R \<omega>0 A \<omega> (RNormal \<omega>'); 
    red_exhale ctxt R \<omega>0 B \<omega>' res\<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (A && B) \<omega> res"
| ExhStarFailure: 
 "\<lbrakk> red_exhale ctxt R \<omega>0 A \<omega> RFailure \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (A && B) \<omega> RFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
| ExhImpTrue: 
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
    red_exhale ctxt R \<omega>0 A \<omega> res \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (Imp e A) \<omega> res" 
| ExhImpFalse:  
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
    red_exhale ctxt R \<omega>0 (Imp e A) \<omega> (RNormal \<omega>)"

\<comment>\<open>exhale e ? A : B\<close>
| ExhCondTrue: 
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
    red_exhale ctxt R \<omega>0 A \<omega> res \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (CondAssert e A B) \<omega> res"
| ExhCondFalse: 
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False); 
    red_exhale ctxt R \<omega>0 B \<omega> res \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (CondAssert e A B) \<omega> res" 

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this results in failure.\<close>
| ExhSubExpFailure: 
  "\<lbrakk> direct_sub_expressions_assertion A \<noteq> [];
     red_pure_exps_total ctxt R (Some \<omega>0) (direct_sub_expressions_assertion A) \<omega> None  \<rbrakk> \<Longrightarrow> 
     red_exhale ctxt R \<omega>0 A \<omega> RFailure"

inductive_cases ExhStar_case: "red_exhale ctxt R \<omega>0 (A && B) m_pm res"
inductive_cases ExhImp_case: "red_exhale ctxt R \<omega>0 (Imp e B) m_pm res"


lemma ExhPure_case: 
  assumes "red_exhale ctxt R \<omega>0 (Atomic (Pure e)) \<omega> res"
      and "\<And>b. ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<Longrightarrow> res = (exh_if_total b \<omega>) \<Longrightarrow> P"
      and "ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> res = RFailure \<Longrightarrow> P"
    shows "P"
  using assms 
  by (cases) (auto elim: red_pure_exp_total_elims)

definition havoc_locs_heap :: "'a total_heap \<Rightarrow> heap_loc set \<Rightarrow> 'a total_heap set"
  where "havoc_locs_heap hh locs = { hh' | hh'. (\<forall>lh. lh \<notin> locs \<longrightarrow> hh' lh = hh lh) }"

lemma havoc_locs_heap_empty: "havoc_locs_heap hh {} = {hh}"
  unfolding havoc_locs_heap_def
  by blast

text\<open>\<^term>\<open>havoc_locs_heap hh locs\<close> denotes the set of heaps that differ with \<^term>\<open>hh\<close> only on \<^term>\<open>locs\<close>\<close>

definition havoc_locs_state :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> heap_loc set \<Rightarrow> 'a full_total_state set"
  where "havoc_locs_state ctxt \<omega> locs = 
    { update_hh_total_full \<omega> hh' | (\<omega>' :: 'a full_total_state) (hh' :: 'a total_heap). 
                                   total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh' \<and>
                                   hh' \<in> havoc_locs_heap (get_hh_total_full \<omega>) locs}"

lemma havoc_locs_state_empty:
  assumes "\<omega>' \<in> havoc_locs_state ctxt \<omega> {}"
  shows "\<omega> = \<omega>'"
  using assms
  unfolding havoc_locs_state_def
  by (simp add: havoc_locs_heap_empty)  

lemma havoc_locs_state_same_store: "\<omega>' \<in> havoc_locs_state ctxt \<omega> locs \<Longrightarrow> get_store_total \<omega>' = get_store_total \<omega>"
  unfolding havoc_locs_state_def
  by force

lemma havoc_locs_state_same_trace: "\<omega>' \<in> havoc_locs_state ctxt \<omega> locs \<Longrightarrow> get_trace_total \<omega>' = get_trace_total \<omega>"
  unfolding havoc_locs_state_def
  by force

lemma havoc_locs_state_same_mask: "\<omega>' \<in> havoc_locs_state ctxt \<omega> locs \<Longrightarrow> get_m_total_full \<omega>' = get_m_total_full \<omega>"
  unfolding havoc_locs_state_def
  by force

lemma havoc_locs_state_well_typed_heap: "\<omega>' \<in> havoc_locs_state ctxt \<omega> locs \<Longrightarrow> 
                                    total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>')"  
proof -
  assume "\<omega>' \<in> havoc_locs_state ctxt \<omega> locs"

  from this obtain hh' where "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh'" and
                            "\<omega>' = update_hh_total_full \<omega> hh'"
    unfolding havoc_locs_state_def
    by blast

  thus ?thesis
    by simp
qed

inductive fold_rel :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  where 
    FoldRelNormal: 
      "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
       red_exhale ctxt R \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 (RNormal \<omega>1);
       \<omega>' = \<lparr> get_store_total = get_store_total \<omega>, 
              get_trace_total = get_trace_total \<omega>,
              get_total_full = update_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) (padd (get_mp_total (get_total_full \<omega>1) (pred_id, vs)) q)
             \<rparr> \<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> (RNormal \<omega>')"
  | FoldRelFailure:
       "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       \<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>;
       red_exhale ctxt R \<omega>0 (syntactic_mult (Rep_preal q) pred_body) \<omega>0 RFailure \<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> RFailure"    

inductive_cases FoldRelNormalCase: "fold_rel ctxt R pred_id vs q \<omega> (RNormal \<omega>')"
inductive_cases FoldRelFailureCase: "fold_rel ctxt R pred_id vs q \<omega> RFailure"


fun sub_expressions :: "stmt \<Rightarrow> pure_exp list" where
  "sub_expressions (If p _ _) = [p]"
| "sub_expressions (LocalAssign _ e) = [e]"
| "sub_expressions (FieldAssign e1 _ e2) = [e1, e2]"
| "sub_expressions (Unfold _ exps pw) = exps @ sub_expressions_exp_or_wildcard pw"
| "sub_expressions (Fold _ exps pw) = exps @ sub_expressions_exp_or_wildcard pw"
| "sub_expressions (MethodCall _ m exps ) = exps"
| "sub_expressions _ = []"

\<comment>\<open>TODO: duplicated from Viper session\<close>
fun modif :: "stmt \<Rightarrow> var set" where
  "modif (If b s1 s2) = modif s1 \<union> modif s2"
| "modif (Seq a b) = modif a \<union> modif b"
| "modif (LocalAssign x e) = {x}"
| "modif (Havoc x) = {x}"
| "modif (Scope l s) = shift_down_set (modif s)" (* We ignore variables from this scope, and we shift the other ones *)
| "modif (MethodCall y name es) = set y"
| "modif (While b I s) = modif s"
| "modif _ = {}"

definition reset_state_after_call :: "var list \<Rightarrow> 'a val list \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow>'a full_total_state" where
  "reset_state_after_call targets vs \<omega>BeforeCall \<omega> = 
       \<lparr> get_store_total = (map_upds (get_store_total \<omega>BeforeCall) targets vs),
         get_trace_total = get_trace_total \<omega>BeforeCall,
         get_total_full = get_total_full \<omega> \<rparr>"

inductive red_stmt_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "('a full_total_state \<Rightarrow> bool)" where
\<comment>\<open>Atomic statements\<close>
   RedSkip: "red_stmt_total ctxt R \<Lambda> Skip \<omega> (RNormal \<omega>)" 
| RedInhale: 
 "\<lbrakk> red_inhale ctxt R A \<omega> res \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Inhale A) \<omega> res"

\<comment>\<open>Note that exhale is demonic here (even locally). For instance, exhale acc(x.f, wildcard) * acc(x.f, 1/2)
always has at least one failure transition. This is in-sync with the Carbon implementation.\<close>

| RedExhale:
 "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>_exh);
    \<omega>' \<in> havoc_locs_state ctxt \<omega>_exh ({loc. get_mh_total_full \<omega> loc > 0 \<and> get_mh_total_full \<omega>_exh loc = 0})
    \<comment>\<open>We havoc all locations \<^term>\<open>l\<close> for which both of the following conditions hold:
        (1) there is no direct permission to \<^term>\<open>l\<close> after the exhale
        (2) the exhale removed nonzero permission to \<^term>\<open>l\<close>\<close>
    \<comment>\<open>Once full support for Viper predicates is added, then this exhale semantics needs to also 
      take \<^term>\<open>R\<close> into account.\<close> \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
| RedExhaleFailure:
 "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> RFailure \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> RFailure"
| RedAssert:
 "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>_exh) \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> (RNormal \<omega>)"
| RedAssertFailure:
 "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> RFailure \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> RFailure"

\<comment>\<open>TODO: Add semantics for \<^term>\<open>Assume A\<close>. \<close>

| RedHavoc:
  "\<lbrakk> \<Lambda> x = Some ty;
     get_type (absval_interp_total ctxt) v = ty \<rbrakk> \<Longrightarrow>
   red_stmt_total ctxt R \<Lambda> (Havoc x) \<omega> (RNormal (update_var_total \<omega> x v))"
\<comment>\<open>only reduce assignment if RHS has the type expected by LHS \<close>
| RedLocalAssign:
 "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v);
    \<Lambda> x = Some ty; 
    get_type (absval_interp_total ctxt) v = ty \<rbrakk> \<Longrightarrow> 
   red_stmt_total ctxt R \<Lambda> (LocalAssign x e) \<omega> (RNormal (update_var_total \<omega> x v))"
| RedFieldAssign: 
 "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr));
    (addr,f) \<in> get_writeable_locs \<omega>;
    ctxt, R, (Some \<omega>)  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v;
    declared_fields (program_total ctxt) f = Some ty;
    get_type (absval_interp_total ctxt) v = ty \<rbrakk> \<Longrightarrow> 
    red_stmt_total ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (RNormal (update_hh_loc_total_full \<omega> (addr,f) v))"
\<comment>\<open>Is null case handled in NestedPermSem?\<close>
| RedFieldAssignFailure: 
 "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
    \<comment>\<open>the reduction of the right-hand-side is technically not required for this rule 
       (irrelevant if well-typed), but matches Viper's current reduction order\<close>
    ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v; 
    r = Null \<or> (the_address r,f) \<notin>  get_writeable_locs \<omega> \<rbrakk> \<Longrightarrow> 
    red_stmt_total ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> RFailure"
| RedMethodCall:
  " \<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) es \<omega> (Some v_args);
      program.methods (program_total ctxt) m = Some mdecl;     
      \<comment>\<open>method call reduces only if argument values and return values have the correct type\<close>
      vals_well_typed (absval_interp_total ctxt) v_args (method_decl.args mdecl); 
      list_all2 (\<lambda> y t. y = Some t) (map \<Lambda> ys) (method_decl.rets mdecl); 
      \<comment>\<open>non-deterministically select values for return variables that conform to the declared type\<close>
      vals_well_typed (absval_interp_total ctxt) v_rets (method_decl.rets mdecl); 
      red_stmt_total ctxt R \<Lambda> (Exhale (method_decl.pre mdecl)) 
                               \<comment>\<open>arguments: 0,1,2,...,n-1\<close>
                              \<lparr> get_store_total = (shift_and_add_list_alt Map.empty v_args), 
                                get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                                get_total_full = get_total_full \<omega> \<rparr>
                              resPre;
      resPre = RFailure \<or> resPre = RMagic \<Longrightarrow> res = resPre;
      \<And> \<omega>Pre. resPre = RNormal \<omega>Pre \<Longrightarrow> 
      \<comment>\<open>can't use havoc here directly in a natural way to get updated state\<close>
            (red_stmt_total ctxt R \<Lambda> (Inhale (method_decl.post mdecl))                                     
                               \<comment>\<open>arguments: 0,1,2,...,n-1 return variables: n,n+1,...\<close>
                              \<lparr> get_store_total = (shift_and_add_list_alt Map.empty (v_args@v_rets)), 
                                get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                                get_total_full = get_total_full \<omega>Pre \<rparr>
                              resPost \<and>
            res = map_stmt_result_total (reset_state_after_call ys v_rets \<omega>) resPost) \<rbrakk> \<Longrightarrow>        
      red_stmt_total ctxt R \<Lambda> (MethodCall ys m es) \<omega> res"
 \<comment>\<open>Labels are not overwritten (would not be possible anyway in well-formed programs)\<close>
| RedLabel:  "\<lbrakk> \<omega>' = (if get_trace_total \<omega> lbl = None then 
                             update_trace_total \<omega> ((get_trace_total \<omega>)(lbl \<mapsto> get_total_full \<omega>)) 
                      else \<omega>) \<rbrakk> \<Longrightarrow> 
              red_stmt_total ctxt R \<Lambda> (Label lbl) \<omega> (RNormal \<omega>')"   
| RedUnfold:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p);     
     W' = {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr> \<and> unfold_rel ctxt R pred_id v_args (Abs_preal v_p) (get_total_full \<omega>) \<phi>' \<and> R \<omega>'};
     th_result_rel (v_p > 0 \<and> v_p \<le> Rep_preal (get_mp_total_full \<omega> (pred_id, v_args))) True W' res \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> res"

\<comment>\<open>\<^const>\<open>unfold_rel\<close> constrains permission \<^term>\<open>p\<close> to be strictly positive\<close>
| RedUnfoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     unfold_rel ctxt R pred_id v_args p (get_total_full \<omega>) \<phi>';
     \<omega>' = \<omega> \<lparr> get_total_full := \<phi>' \<rparr> \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args Wildcard) \<omega> (RNormal \<omega>')"
| RedUnfoldWildcardFailure:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     get_mp_total_full \<omega> (pred_id, v_args) = pnone \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args Wildcard) \<omega> RFailure"
\<comment>\<open>TODO: unfold acc(P(x),0)\<close>

\<comment>\<open>One should be able to prove that if \<omega> is unfolding consistent, then so is \<omega>' after a fold, without
  explicitly pruning states. This is because folds just replace permissions with a predicate instance 
  (and even if there is a wildcard, we know that there must be at least one transition for the
 newly generated predicate instance, namely the one before the fold)\<close>
| RedFold:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p);     
     fold_rel ctxt R pred_id v_args (Abs_preal v_p) \<omega> res
 \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args (PureExp e_p)) \<omega> res"

| RedFoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);     
     fold_rel ctxt R pred_id v_args p \<omega> res \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args Wildcard) \<omega> res"
\<comment>\<open>TODO: fold acc(P(x),0)\<close>

\<comment>\<open>Composite statements\<close>
| RedScope:
    "\<lbrakk>  get_type (absval_interp_total ctxt) v = \<tau>;
       red_stmt_total ctxt R (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega> v) res;
       res_unshift = map_stmt_result_total (unshift_state_total 1) res \<rbrakk> \<Longrightarrow>

      red_stmt_total ctxt R \<Lambda> (Scope \<tau> scopeBody) \<omega> res_unshift"
 | RedIfTrue: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
      red_stmt_total ctxt R \<Lambda> s_thn \<omega> res \<rbrakk> \<Longrightarrow> 
      red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> res"
 | RedIfFalse: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
      red_stmt_total ctxt R \<Lambda> s_els \<omega> res \<rbrakk> \<Longrightarrow> 
      red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> res"
 | RedSeq:
   "\<lbrakk> red_stmt_total ctxt R \<Lambda> s1 \<omega> (RNormal \<omega>');
      red_stmt_total ctxt R \<Lambda> s2 \<omega>' res \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> res"
 | RedSeqFailureOrMagic:
   "\<lbrakk> red_stmt_total ctxt R \<Lambda> s1 \<omega> res; 
      res = RFailure \<or> res = RMagic \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> res"
(* TODO while loops *)
\<comment>\<open>Failure subexpression\<close>
| RedSubExpressionFailure: 
  "\<lbrakk> sub_expressions s \<noteq> [];
    red_pure_exps_total ctxt R (Some \<omega>) (sub_expressions s) \<omega> None  \<rbrakk> \<Longrightarrow> 
    red_stmt_total ctxt R \<Lambda> s \<omega> RFailure"

inductive_cases RedLocalAssign_case: 
     "red_stmt_total ctxt R \<Lambda> (LocalAssign x e) \<omega> (RNormal (update_var_total \<omega> x v))"

inductive_cases RedSkip_case: "red_stmt_total ctxt R \<Lambda> Skip \<omega> res"
inductive_cases RedSeqNormal_case: "red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> (RNormal \<omega>')"
inductive_cases RedSeqFailureOrMagic_case: "red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> RFailure"
inductive_cases RedIfNormal_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> (RNormal \<omega>')"
inductive_cases RedIfFailure_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> RFailure"
inductive_cases RedIf_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> res"
inductive_cases RedInhale_case: "red_stmt_total ctxt R \<Lambda> (Inhale A) \<omega> res"
inductive_cases RedExhale_case: "red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> res"
inductive_cases RedExhaleNormal_case: "red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
inductive_cases RedExhaleFailure_case: "red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> RFailure"
inductive_cases RedAssertNormal_case: "red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> (RNormal \<omega>')"
inductive_cases RedAssertFailure_case: "red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> RFailure"
inductive_cases RedScope_case: "red_stmt_total ctxt R \<Lambda> (Scope \<tau> scopeBody) \<omega> res_unshift"

lemmas red_stmt_total_inversion_thms =
   RedSkip_case
   RedLocalAssign_case
   RedIf_case
   RedSeqNormal_case
   RedSeqFailureOrMagic_case
   RedInhale_case
   RedExhale_case
   RedExhaleNormal_case
   RedExhaleFailure_case
   RedAssertNormal_case
   RedAssertFailure_case

subsection \<open>Correctness of Viper methods\<close>

definition vpr_store_well_typed :: "('a \<Rightarrow> abs_type) \<Rightarrow> type_context \<Rightarrow> 'a store \<Rightarrow> bool"
  where "vpr_store_well_typed A \<Lambda> \<sigma> \<equiv> \<forall>x t. \<Lambda> x = Some t \<longrightarrow> map_option (\<lambda>v. get_type A v) (\<sigma> x) = Some t"

definition vpr_method_correct_total_aux :: 
          "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl 
                \<Rightarrow> ('a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool) 
               \<Rightarrow>  bool" where
  "vpr_method_correct_total_aux ctxt R mdecl CorrectWrtPre \<equiv>
         (\<forall>(\<omega> :: 'a full_total_state) rpre. 
            vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args mdecl @ method_decl.rets mdecl)) (get_store_total \<omega>) \<longrightarrow>
            total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>) \<longrightarrow>
            is_empty_total_full \<omega> \<longrightarrow>
            red_inhale ctxt R (method_decl.pre mdecl) \<omega> rpre \<longrightarrow>
            (
              rpre \<noteq> RFailure \<and>
              (\<forall>\<omega>pre. rpre = RNormal \<omega>pre \<longrightarrow> 
               CorrectWrtPre ctxt R mdecl \<omega>pre \<omega>
              )
            )
         )"

lemma vpr_method_correct_total_aux_normalD:
  assumes "vpr_method_correct_total_aux ctxt R mdecl CorrectWrtPre"
      and "red_inhale ctxt R (method_decl.pre mdecl) \<omega> (RNormal \<omega>pre)"
      and "vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args mdecl @ method_decl.rets mdecl)) (get_store_total \<omega>)"
      and "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>)"
      and "is_empty_total_full \<omega>"
    shows "CorrectWrtPre ctxt R mdecl \<omega>pre \<omega>"
  using assms
  unfolding vpr_method_correct_total_aux_def
  by blast

definition vpr_postcondition_framed :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a total_state \<Rightarrow> 'a store \<Rightarrow> bool"
  where "vpr_postcondition_framed ctxt R postcondition \<phi>pre \<sigma> \<equiv>
               (\<forall>mh trace. total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total mh) \<longrightarrow>
                     wf_mask_simple (get_mh_total mh) \<longrightarrow>
                    \<comment>\<open>old state given by state that satisfies precondition, any other available labels
                       are irrelevant, since well-formed postconditions can only have the label \<^const>\<open>old_label\<close>\<close>
                     trace old_label = Some \<phi>pre \<longrightarrow>
                     assertion_framing_state ctxt R postcondition
                             \<lparr> get_store_total = \<sigma>,
                               get_trace_total = trace, 
                               get_total_full = mh \<rparr>
                )"

lemma vpr_postcondition_framed_assertion_framing_state:
  assumes "vpr_postcondition_framed ctxt R postcondition \<phi>pre \<sigma>"
      and "\<omega> = \<lparr> get_store_total = \<sigma>, get_trace_total = trace, get_total_full = mh \<rparr>"
      and "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total mh)"
      and "wf_mask_simple (get_mh_total mh)"
      and "trace old_label = Some \<phi>pre"
    shows "assertion_framing_state ctxt R postcondition \<omega>"
  using assms
  unfolding vpr_postcondition_framed_def
  by blast

definition vpr_method_body_correct :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "vpr_method_body_correct ctxt R mdecl \<omega>pre \<equiv>
            (\<forall>rbody. red_stmt_total ctxt R 
                                (nth_option (method_decl.args mdecl @ method_decl.rets mdecl))
                                (Seq (the (method_decl.body mdecl)) (Exhale (method_decl.post mdecl)))
                                (update_trace_total \<omega>pre (Map.empty(old_label \<mapsto> get_total_full \<omega>pre))) 
                                rbody \<longrightarrow> rbody \<noteq> RFailure)
                        \<comment>\<open>  (rbody \<noteq> RFailure \<and> 
                            (\<forall>\<omega>body. rbody = RNormal \<omega>body \<longrightarrow> 
                                (\<forall> rpost. red_exhale ctxt R \<omega>body (method_decl.post mdecl) \<omega>body rpost \<longrightarrow> rpost \<noteq> RFailure)
                            )
                          )\<close>
                "


definition vpr_method_correct_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_correct_total ctxt R mdecl \<equiv>
         vpr_method_correct_total_aux ctxt R mdecl 
          (\<lambda>ctxt R mdecl \<omega>pre \<omega>. 
                vpr_postcondition_framed ctxt R (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>) \<and>
                (\<forall>mbody. method_decl.body mdecl = Some mbody \<longrightarrow> vpr_method_body_correct ctxt R mdecl \<omega>pre)
          )
       "

definition vpr_method_correct_total_expanded :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_correct_total_expanded ctxt R mdecl \<equiv>
         (\<forall>(\<omega> :: 'a full_total_state) rpre. 
            vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args mdecl @ method_decl.rets mdecl)) (get_store_total \<omega>) \<longrightarrow>
            total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>) \<longrightarrow>
            is_empty_total_full \<omega> \<longrightarrow>
            red_inhale ctxt R (method_decl.pre mdecl) \<omega> rpre \<longrightarrow>
            (
              rpre \<noteq> RFailure \<and>
              (\<forall>\<omega>pre. rpre = RNormal \<omega>pre \<longrightarrow> 
                \<comment>\<open>\<^term>\<open>get_store_total \<omega>\<close> should be equal to \<^term>\<open>get_store_total \<omega>pre\<close> since inhale does not change the store.\<close>
                vpr_postcondition_framed ctxt R (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>) \<and>
                (\<forall>mbody. method_decl.body mdecl = Some mbody \<longrightarrow> vpr_method_body_correct ctxt R mdecl \<omega>pre)
              )
            )
         )"

text \<open>\<^const>\<open>vpr_method_correct_total\<close> specifies when a Viper method is correct. The definition
      uses \<^const>\<open>vpr_method_correct_total_aux\<close>.  \<^const>\<open>vpr_method_correct_total_aux\<close>  allows one
      to obtain variations of method correctness (for example, to just specify that the specifications
      are framed as shown below). \<^const>\<open>vpr_method_correct_total_expanded\<close> a version of the Viper
      method correctness where  \<^const>\<open>vpr_method_correct_total_aux\<close> is expanded. The lemma below
      confirms that the version defined via  \<^const>\<open>vpr_method_correct_total_aux\<close> and the
      expanded version are equivalent.\<close>

lemma vpr_method_correct_total_2_new_equiv:
  "vpr_method_correct_total ctxt R mdecl = vpr_method_correct_total_expanded ctxt R mdecl"
  unfolding vpr_method_correct_total_def vpr_method_correct_total_expanded_def vpr_method_correct_total_aux_def
  by blast

definition vpr_method_spec_correct_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_spec_correct_total ctxt R mdecl \<equiv>
         vpr_method_correct_total_aux ctxt R mdecl 
          (\<lambda>ctxt R mdecl \<omega>pre \<omega>. 
                vpr_postcondition_framed ctxt R (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>)
          )
       "

definition vpr_all_method_spec_correct_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> bool" where
  "vpr_all_method_spec_correct_total ctxt R Pr \<equiv> \<forall>m mdecl. methods Pr m = Some mdecl \<longrightarrow> vpr_method_spec_correct_total ctxt R mdecl"

lemma vpr_method_spec_correct_total_from_all:
  assumes "vpr_all_method_spec_correct_total ctxt R Pr"
      and "methods Pr m = Some mdecl"
    shows "vpr_method_spec_correct_total ctxt R mdecl"
  using assms
  unfolding vpr_all_method_spec_correct_total_def
  by blast    

subsection \<open>Alternative introduction rules\<close>

lemma red_exhale_acc_normalI:
  assumes "ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
      and "ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
      and "a = the_address r"
      and "p \<ge> 0 \<and> (if r = Null then p = 0 else pgte (get_mh_total_full \<omega> (a,f)) (Abs_preal p))" (is "?Success")
      and "\<omega>' = (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((get_mh_total_full \<omega> (a,f)) - (Abs_preal p)))" (is "\<omega>' = ?\<omega>def")
    shows "red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega> (RNormal \<omega>')"
proof -
  have Eq: "RNormal \<omega>' = exh_if_total ?Success ?\<omega>def"
    using assms
    by auto

  show ?thesis
    apply (subst Eq)
    apply (rule ExhAcc)
    using assms
    by auto
qed

lemma red_exhale_acc_failureI:
  assumes "ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
      and "ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
      and "a = the_address r"
      and "\<not>(p \<ge> 0 \<and> (if r = Null then p = 0 else pgte (get_mh_total_full \<omega> (a,f)) (Abs_preal p)))" (is "\<not>?Success")
    shows "red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega> RFailure"
proof -
  have Eq: "RFailure = exh_if_total ?Success (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((get_mh_total_full \<omega> (a,f)) - (Abs_preal p)))"
    using assms
    by auto
  show ?thesis
    apply (subst Eq)
    apply (rule ExhAcc)
    using assms
    by auto
qed

subsection \<open>Well-formed state consistency\<close>

text \<open>Many of the theorems are parametrized by the state consistency. Many of the theorems require
certain properties on the state consistency. The following well-formedness definition captures
these properties.\<close>

definition wf_total_consistency 
  where "wf_total_consistency ctxt R Rt \<equiv> 
               mono_prop_downward R \<and>
               (\<forall>\<omega>. is_empty_total_full \<omega> \<longrightarrow> R \<omega>) \<and>
               (\<forall>\<omega> \<omega>' \<Lambda> stmt. R \<omega> \<longrightarrow> red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>') \<longrightarrow> R \<omega>') \<and>
               \<comment>\<open>The following statement ensures that states in the body of a scope preserve consistency.\<close>
               (\<forall>\<omega> v. R \<omega> \<longrightarrow> R (shift_and_add_state_total \<omega> v)) \<and> 
               (\<forall>\<omega>. R \<omega> \<longleftrightarrow> (Rt (get_total_full \<omega>) \<and> (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> Rt \<phi>)) )"

lemma total_consistencyI:
  assumes "wf_total_consistency ctxt R Rt"
      and "Rt (get_total_full \<omega>)"
      and "\<And> lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R \<omega>"
  using assms
  unfolding wf_total_consistency_def
  by blast

lemma wf_total_consistency_trivial: "wf_total_consistency ctxt (\<lambda>_.True) (\<lambda>_.True)"
  unfolding wf_total_consistency_def mono_prop_downward_def
  by blast

lemma total_consistency_red_stmt_preserve:
  assumes "wf_total_consistency ctxt R Rt" 
      and "R \<omega>"
      and "red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "R \<omega>'"
  using assms
  unfolding wf_total_consistency_def
  by blast

lemma total_consistency_store_update:
  assumes "wf_total_consistency ctxt R Rt" 
      and "R \<omega>" 
      and "get_total_full \<omega>' = get_total_full \<omega>" 
      and "get_trace_total \<omega>' = get_trace_total \<omega>"
    shows "R \<omega>'"
  using assms
  unfolding wf_total_consistency_def
  by metis

lemma total_consistency_store_update_2:
  assumes "wf_total_consistency ctxt R Rt" 
      and "R \<omega>" 
    shows "R (\<omega> \<lparr> get_store_total := \<sigma> \<rparr>)"
  using assms total_consistency_store_update
  by fastforce

lemma total_consistency_trace_update:
  assumes "wf_total_consistency ctxt R Rt" 
      and "R \<omega>" 
      and "get_store_total \<omega>' = get_store_total \<omega>"
      and "get_total_full \<omega>' = get_total_full \<omega>" 
      and "\<And> lbl \<phi>. get_trace_total \<omega>' lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R \<omega>'"
  using assms 
  unfolding wf_total_consistency_def
  by simp

lemma total_consistency_trace_update_2:
  assumes "wf_total_consistency ctxt R Rt" 
      and "R \<omega>" 
      and "\<And> lbl \<phi>. t lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R (\<omega> \<lparr> get_trace_total := t \<rparr>)"
  using assms 
  unfolding wf_total_consistency_def
  by simp

lemma wf_total_consistency_trace_mono_downwardD:
  assumes "wf_total_consistency ctxt R Rt"
  shows "mono_prop_downward R"
  using assms
  unfolding wf_total_consistency_def
  by blast

subsection \<open>Experimental definitions\<close>

definition assertion_sat :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "assertion_sat \<Lambda> R ctxt A \<omega> = 
            (\<forall> res. red_stmt_total \<Lambda> R ctxt (Assert A) \<omega> res \<longrightarrow> res \<noteq> RFailure)"

text \<open>Note that \<^const>\<open>assertion_sat\<close> is ``demonic'', i.e., every reduction of asserting \<^term>\<open>A\<close> must
be a non-failing state, which is in-sync with the semantics of assert statements in programs. We might
want to change both to be ``locally angelic''. \<close>

definition heap_dep_interp_wf :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> bool"
  where 
    "heap_dep_interp_wf ctxt StateCons \<Lambda> \<equiv> \<forall>fid fdecl. ViperLang.funs (program_total ctxt) fid = Some fdecl \<longrightarrow> 
       (\<exists>fsem. fun_interp_total ctxt fid = Some fsem \<and>
            (\<forall>vs \<omega>.   
               ( ( \<not>vals_well_typed (absval_interp_total ctxt) vs (args fdecl) ) \<longrightarrow> fsem vs \<omega> = None) \<and>

               ( 
                 ( vals_well_typed (absval_interp_total ctxt) vs (args fdecl) \<and> assertion_self_framing_store ctxt StateCons (pre fdecl) (nth_option vs) ) \<longrightarrow>

                     ( (\<not>assertion_sat ctxt StateCons \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs))) \<longrightarrow>
                           fsem vs \<omega> = Some VFailure ) \<and>
  
                     (assertion_sat ctxt StateCons \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs)) \<longrightarrow>
                         (\<exists>v. fsem vs \<omega> = Some (Val v) \<and> get_type (absval_interp_total ctxt) v = ret fdecl \<and>
                              if_Some (\<lambda>e. ctxt, StateCons, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v)) (body fdecl) ) )
              )
            )
       )"

definition heap_dep_fun_obligations :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> bool"
  where
    "heap_dep_fun_obligations ctxt StateCons \<Lambda> \<equiv> 
       \<forall> fid fdecl vs e p. 
          ( ViperLang.funs (program_total ctxt) fid = Some fdecl \<and>            
            body fdecl = Some e \<and>
            vals_well_typed (absval_interp_total ctxt) vs (args fdecl) \<and>
            post fdecl = Some p)  \<longrightarrow>
             (
              assertion_self_framing_store ctxt StateCons (pre fdecl) (nth_option vs) \<and>
                (\<forall> \<omega> extVal.
                  assertion_sat ctxt StateCons \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs)) \<longrightarrow>
    
                    ctxt, StateCons, (Some (update_store_total \<omega> (nth_option vs))) \<turnstile> \<langle>e; (update_store_total \<omega> (nth_option vs))\<rangle> [\<Down>]\<^sub>t extVal \<and>
                      ((\<exists> v. extVal = Val v \<and>
                         assertion_sat ctxt StateCons \<Lambda> p (update_store_total \<omega> (nth_option (vs@[v])))))
                )
             )"

definition predicate_obligations :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> bool"
  where
    "predicate_obligations ctxt StateCons \<equiv>
       \<forall> pid pdecl vs e.
        ( ViperLang.predicates (program_total ctxt) pid = Some pdecl \<and>
          predicate_decl.body pdecl = Some e \<and>
          vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl) ) \<longrightarrow>
          assertion_self_framing_store ctxt StateCons e (nth_option vs)"

(* TODO loops

definition havoc_vars_state :: "'a full_total_state \<Rightarrow> var set \<Rightarrow> 'a full_total_state set"
  where "havoc_vars_state \<omega> havoced_vars = { update_store_total \<omega> \<sigma>' | \<sigma>'. 
                                      dom \<sigma>' = dom (get_store_total \<omega>) \<and>
                                      (\<forall> x \<in> dom (get_store_total \<omega>) - havoced_vars. get_store_total \<omega> x = \<sigma>' x) }"
 | RedWhile:
   "\<lbrakk> red_stmt_total ctxt R \<Lambda> (Exhale invariant) \<omega> (RNormal \<omega>AfterExh);
      (\<And> \<omega>AfterHavoc \<omega>AfterInh \<omega>AfterBody res. havoc_vars \<omega>AfterExh (modif loop_body) \<omega>AfterHavoc \<Longrightarrow>
          (ctxt, R, (Some \<omega>AfterHavoc) \<turnstile> \<langle>cond; \<omega>AfterHavoc\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<Longrightarrow>
          red_inhale ctxt R invariant \<omega>AfterHavoc (RNormal \<omega>AfterInh) \<Longrightarrow>
          red_stmt_total ctxt R \<Lambda> loop_body \<omega>AfterInh (RNormal \<omega>AfterBody) \<Longrightarrow>
          red_stmt_total ctxt R \<Lambda> (Assert invariant) \<omega>AfterBody res \<Longrightarrow> 
          res \<noteq> RFailure))      
       \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (While cond invariant loop_body) \<omega> \<omega>'"

 | RedWhileNormal:
    "\<lbrakk> red_stmt_total ctxt R \<Lambda> (Exhale invariant) \<omega> (RNormal \<omega>AfterExh);
       \<omega>AfterHavoc \<in> havoc_vars_state \<omega>AfterExh (modif loop_body);
       red_inhale ctxt R invariant \<omega>AfterHavoc (RNormal \<omega>AfterInh);
       ctxt, R, (Some \<omega>AfterInh) \<turnstile> \<langle>cond; \<omega>AfterInh\<rangle> [\<Down>]\<^sub>t Val (VBool False)
     \<rbrakk> \<Longrightarrow> red_stmt_total ctxt R \<Lambda> (While cond invariant loop_body) \<omega> (RNormal \<omega>AfterInh)"

\<comment>\<open>TODO: intermediate failures\<close>
  | RedWhileFailure:
   "\<lbrakk> red_stmt_total ctxt R \<Lambda> (Exhale invariant) \<omega> (RNormal \<omega>AfterExh); \<comment>\<open>failure option 1\<close>
      \<omega>AfterHavoc \<in> havoc_vars_state \<omega>AfterExh (modif loop_body); 
      red_inhale ctxt R invariant                                       \<comment>\<open>failure option 2\<close>
            (empty_full_total_state 
                        (get_store_total \<omega>AfterHavoc) 
                        (get_trace_total \<omega>AfterHavoc)
                        (get_h_total_full \<omega>AfterHavoc))
            (RNormal \<omega>AfterInh);
      ctxt, R, (Some \<omega>AfterInh) \<turnstile> \<langle>cond; \<omega>AfterInh\<rangle> [\<Down>]\<^sub>t Val (VBool True); \<comment>\<open>failure option 3\<close>
      red_stmt_total ctxt R \<Lambda> loop_body \<omega> (RNormal \<omega>AfterInh);            \<comment>\<open>failure option 4\<close>
      red_stmt_total ctxt R \<Lambda> (Exhale invariant) \<omega>AfterInh RFailure \<rbrakk> \<Longrightarrow> \<comment>\<open>failure option 5\<close>
      red_stmt_total ctxt R \<Lambda> (While cond invariant loop_body) \<omega> RFailure"
*)

end
