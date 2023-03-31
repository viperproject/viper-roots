section \<open>Total heap semantics of statements\<close>

theory TotalSemantics
imports Viper.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" TotalUtil
begin

datatype 'a exhale_result = ExhaleNormal "'a full_total_state" | ExhaleFailure

fun exh_if_total :: "bool \<Rightarrow> 'a full_total_state \<Rightarrow> 'a exhale_result"  where
  "exh_if_total False _ = ExhaleFailure"
| "exh_if_total True m = ExhaleNormal m"


definition exhale_perm_single :: "mask \<Rightarrow> heap_loc \<Rightarrow> prat option \<Rightarrow> mask set"
  where "exhale_perm_single m lh p_opt =
      {m'| m' q. 
               (p_opt = None \<longrightarrow> pgt q pnone) \<and>
               option_fold ((=) q) (q \<noteq> pnone \<and> pgt (m lh) q) p_opt \<and>
               m' = m(lh := psub (m lh) q)
       }"

inductive red_exhale :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a  exhale_result \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "'a full_total_state \<Rightarrow> bool" and \<omega>0 :: "'a full_total_state"
  where

\<comment>\<open>exhale acc(e.f, p)\<close>
  ExhAcc: 
  "\<lbrakk>  mh = get_mh_total_full \<omega>;
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega> 
                          ( exh_if_total (p \<ge> 0 \<and> pgte (mh (a,f)) (Abs_prat p) \<and> r \<noteq> Null)
                                         (update_mh_total_full \<omega> (mh( (a,f) := psub (mh (a,f)) (Abs_prat p)))) )"

\<comment>\<open>Exhaling wildcard removes some non-zero permission that is less than the current permission held.\<close>
| ExhAccWildcard:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     q = (SOME p. p \<noteq> pnone \<and> pgt (mh (a,f)) p) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f Wildcard)) \<omega>
                         (exh_if_total (mh (a,f) \<noteq> pnone \<and> r \<noteq> Null) 
                                       (update_mh_total_full \<omega> (mh( (a,f) := q))))"
\<comment>\<open>exhale acc(P(es), p)\<close>
| ExhAccPred:
   "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>
            (exh_if_total (p \<ge> 0 \<and> pgte (mp(pred_id, v_args)) (Abs_prat p) \<and> r \<noteq> Null) 
                          (update_mp_total_full \<omega> (mp( (pred_id, v_args) := psub (mp (pred_id, v_args)) (Abs_prat p)))))"
| ExhAccPredWildcard:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     q = (SOME p. p \<noteq> pnone \<and> pgt (mp (a,f)) p) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>
                         (exh_if_total (mp (a,f) \<noteq> pnone)
                                       (update_mp_total_full \<omega> (mp ( (pred_id, v_args) := q ))))"

| ExhPure:
  "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
     red_exhale ctxt R \<omega>0 (Atomic (Pure e)) \<omega> (exh_if_total b \<omega>)"
| SubAtomicFailure: 
  "\<lbrakk> (sub_expressions_atomic A) \<noteq> [];
     red_pure_exps_total ctxt R (Some \<omega>0) (sub_expressions_atomic A) \<omega> None  \<rbrakk> \<Longrightarrow> 
     red_exhale ctxt R \<omega>0 (Atomic A) \<omega> ExhaleFailure"

\<comment>\<open>exhale A && B\<close>
| ExhStarNormal: 
 "\<lbrakk> red_exhale ctxt R \<omega>0 A \<omega> (ExhaleNormal \<omega>'); 
    red_exhale ctxt R \<omega>0 B \<omega>' res\<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (A && B) \<omega> res"
| ExhStarFailure: 
 "\<lbrakk> red_exhale ctxt R \<omega>0 A \<omega> ExhaleFailure \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (A && B) \<omega> ExhaleFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
| ExhImpTrue: 
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
    red_exhale ctxt R \<omega>0 A \<omega> res \<rbrakk> \<Longrightarrow>
    red_exhale ctxt R \<omega>0 (Imp e A) \<omega> res" 
| ExhImpFalse:  
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
    red_exhale ctxt R \<omega>0 (Imp e A) \<omega> (ExhaleNormal \<omega>)"
| ExhImpFailure:
 "\<lbrakk> ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> 
   red_exhale ctxt R \<omega>0 (Imp e A) \<omega> ExhaleFailure"


inductive_cases ExhStar_case: "red_exhale ctxt R \<omega>0 (A && B) m_pm res"

definition havoc_undef_locs :: "'a total_heap \<Rightarrow> 'a predicate_heap \<Rightarrow> mask \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a total_heap \<times> 'a predicate_heap) set"
  where "havoc_undef_locs hh hp mh mp = 
           { (hh', hp') | hh' hp'. 
                (\<forall>lh. mh lh \<noteq> pnone \<longrightarrow> hh' lh = hh lh) \<and>
                (\<forall>lp. mp lp \<noteq> pnone \<longrightarrow> 
                          hp' lp = hp lp \<and>
                         (\<forall>lh \<in> get_lhset_pheap hp lp. hh' lh = hh lh) \<and>
                         (\<forall>lp2 \<in> get_lpset_pheap hp lp. hp' lp2 = hp lp2)) }"

text\<open>\<^term>\<open>havoc_undef_locs hh hp mh mp\<close> denotes the set of heaps that coincide with \<^term>\<open>(hh,hp)\<close> w.r.t.
the permission masks \<^term>\<open>(mh,mp)\<close>. This means the heaps agree on all heap and predicate locations for 
which direct permission is held in \<^term>\<open>(mh,mp)\<close> or which is part of a predicate snapshot in \<^term>\<open>hp\<close> 
of a directly owned (w.r.t. \<^term>\<open>mp\<close>) predicate\<close>

definition exhale_state :: "'a full_total_state \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a full_total_state set"
  where "exhale_state \<omega> m = 
    {\<omega>' | \<omega>'. get_store_total \<omega>' = get_store_total \<omega> \<and>
              get_trace_total \<omega>' = get_trace_total \<omega> \<and>
              m = (get_mh_total_full \<omega>', get_mp_total_full \<omega>') \<and>
              wf_mask_simple (get_mh_total_full \<omega>') \<and>
              (get_hh_total_full \<omega>', get_hp_total_full \<omega>') \<in> 
                   havoc_undef_locs (get_hh_total_full \<omega>) (get_hp_total_full \<omega>) (fst m) (snd m)}"

lemma exhale_state_same_store: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_store_total \<omega>' = get_store_total \<omega>"
  by (simp add: exhale_state_def)

lemma exhale_state_same_trace: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_trace_total \<omega>' = get_trace_total \<omega>"
  by (simp add: exhale_state_def)

inductive fold_rel :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> prat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  where 
    FoldRelNormal: 
      "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       red_exhale ctxt R (update_store_total \<omega> (nth_option vs)) (syntactic_mult (Rep_prat q) pred_body) (update_store_total \<omega> (nth_option vs)) (ExhaleNormal \<omega>');   
       \<omega>2 = update_mp_total_full \<omega>' ( (get_mp_total_full \<omega>')( (pred_id,vs) :=  padd (m (pred_id, vs)) q)) \<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> (RNormal \<omega>2)"
  | FoldRelFailure:
       "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       red_exhale ctxt R (update_store_total \<omega> (nth_option vs)) (syntactic_mult (Rep_prat q) pred_body) (update_store_total \<omega> (nth_option vs)) ExhaleFailure \<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> RFailure"    

fun sub_expressions :: "stmt \<Rightarrow> pure_exp list" where
  "sub_expressions (If p _ _) = [p]"
| "sub_expressions (LocalAssign _ e) = [e]"
| "sub_expressions (FieldAssign e1 _ e2) = [e1, e2]"
| "sub_expressions (Unfold _ exps pw) = exps @ sub_expressions_exp_or_wildcard pw"
| "sub_expressions (Fold _ exps pw) = exps @ sub_expressions_exp_or_wildcard pw"
| "sub_expressions _ = []"

\<comment>\<open>TODO: duplicated from Viper session\<close>
fun modif :: "stmt \<Rightarrow> var set" where
  "modif (If b s1 s2) = modif s1 \<union> modif s2"
| "modif (Seq a b) = modif a \<union> modif b"
| "modif (LocalAssign x e) = {x}"
| "modif (Havoc x) = {x}"
| "modif (Scope l s) = shift_down_set (modif s)" (* We ignore variables from this scope, and we shift the other ones *)
| "modif (MethodCall x name y) = set y"
| "modif (While b I s) = modif s"
| "modif _ = {}"

inductive red_stmt_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "('a full_total_state \<Rightarrow> bool)" and \<Lambda> :: "type_context"  where
\<comment>\<open>Atomic statements\<close>
   RedSkip: "red_stmt_total ctxt R \<Lambda> Skip \<omega> (RNormal \<omega>)" 
 | RedInhale: 
   "\<lbrakk> red_inhale ctxt R A \<omega> res \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Inhale A) \<omega> res"
 | RedExhale:
   "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> (ExhaleNormal \<omega>_exh);
      \<omega>' \<in> exhale_state \<omega>_exh (get_m_total_full \<omega>_exh) \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
 | RedExhaleFailure:
   "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> RFailure"
 | RedAssert:
   "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> (ExhaleNormal \<omega>_exh) \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> (RNormal \<omega>)"
 | RedAssertFailure:
   "\<lbrakk> red_exhale ctxt R \<omega> A \<omega> ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Assert A) \<omega> RFailure"

\<comment>\<open>Note that exhale is demonic here (even locally). For instance, exhale acc(x.f, wildcard) * acc(x.f, 1/2)
always has at least one failure transition. This is in-sync with the recent Carbon upgrade.\<close>


\<comment>\<open>TODO: Add semantics for \<^term>\<open>Assume A\<close>. \<close>

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

| RedUnfold:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p);     
     W' = {\<omega>2. unfold_rel ctxt R pred_id v_args (Abs_prat v_p) \<omega> \<omega>2 \<and> total_heap_consistent ctxt \<omega>2};
     th_result_rel (v_p > 0 \<and> v_p \<le> Rep_prat (get_mp_total_full \<omega> (pred_id, v_args))) True W' res \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> res"

\<comment>\<open>\<^const>\<open>unfold_rel\<close> constrains permission \<^term>\<open>p\<close> to be strictly positive\<close>
| RedUnfoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     unfold_rel ctxt R pred_id v_args p \<omega> \<omega>' \<rbrakk> \<Longrightarrow>
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
     fold_rel ctxt R pred_id v_args (Abs_prat v_p) \<omega> res
 \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args (PureExp e_p)) \<omega> res"

| RedFoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);     
     fold_rel ctxt R pred_id v_args p \<omega> res \<rbrakk> \<Longrightarrow>
    red_stmt_total ctxt R \<Lambda> (Fold pred_id e_args Wildcard) \<omega> res"
\<comment>\<open>TODO: fold acc(P(x),0)\<close>

\<comment>\<open>Composite statements\<close>
| RedScope:
    "\<lbrakk>  v \<in> set_from_type (absval_interp_total ctxt) \<tau>;
       red_stmt_total ctxt R \<Lambda> scopeBody (shift_and_add_state_total \<omega> v) res;
       res_unshift = map_stmt_result_total (unshift_state_total 0) res \<rbrakk> \<Longrightarrow>

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
 | RedSeqFailure:
   "\<lbrakk> red_stmt_total ctxt R \<Lambda> s1 \<omega> RFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> RFailure"
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
inductive_cases RedSeqFailure_case: "red_stmt_total ctxt R \<Lambda> (Seq s1 s2) \<omega> RFailure"
inductive_cases RedIfNormal_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> (RNormal \<omega>')"
inductive_cases RedIfFailure_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> RFailure"
inductive_cases RedIf_case: "red_stmt_total ctxt R \<Lambda> (If e_b s_thn s_els) \<omega> res"
inductive_cases RedInhale_case: "red_stmt_total ctxt R \<Lambda> (Inhale A) \<omega> res"

lemmas red_stmt_total_inversion_thms =
   RedSkip_case
   RedLocalAssign_case
   RedIf_case
   RedSeqNormal_case
   RedSeqFailure_case
   RedInhale_case

definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_mh_total_full \<omega> = zero_mask \<and> get_mp_total_full \<omega> = zero_mask"

subsection \<open>Correctness\<close>

definition vals_well_typed :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a val) list \<Rightarrow> vtyp list \<Rightarrow> bool"
  where "vals_well_typed A vs ts \<equiv> map (get_type A) vs = ts"

definition assertion_sat :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "assertion_sat \<Lambda> R ctxt A \<omega> = 
            (\<forall> res. red_stmt_total \<Lambda> R ctxt (Assert A) \<omega> res \<longrightarrow> res \<noteq> RFailure)"

text \<open>Note that \<^const>\<open>assertion_sat\<close> is ``demonic'', i.e., every reduction of asserting \<^term>\<open>A\<close> must
be a non-failing state, which is in-sync with the semantics of assert statements in programs. We might
want to change both to be ``locally angelic''. \<close>

definition heap_dep_interp_wf :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> bool"
  where 
    "heap_dep_interp_wf ctxt R \<Lambda> \<equiv> \<forall>fid fdecl. ViperLang.funs (program_total ctxt) fid = Some fdecl \<longrightarrow> 
       (\<exists>fsem. fun_interp_total ctxt fid = Some fsem \<and>
            (\<forall>vs \<omega>.   
               ( ( \<not>vals_well_typed (absval_interp_total ctxt) vs (args fdecl) ) \<longrightarrow> fsem vs \<omega> = None) \<and>

               ( 
                 ( vals_well_typed (absval_interp_total ctxt) vs (args fdecl) \<and> assertion_self_framing_store ctxt (pre fdecl) (nth_option vs) ) \<longrightarrow>

                     ( (\<not>assertion_sat ctxt R \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs))) \<longrightarrow>
                           fsem vs \<omega> = Some VFailure ) \<and>
  
                     (assertion_sat ctxt R \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs)) \<longrightarrow>
                         (\<exists>v. fsem vs \<omega> = Some (Val v) \<and> get_type (absval_interp_total ctxt) v = ret fdecl \<and>
                              if_Some (\<lambda>e. ctxt, R, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v)) (body fdecl) ) )
              )
            )
       )"

definition heap_dep_fun_obligations :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> bool"
  where
    "heap_dep_fun_obligations ctxt R \<Lambda> \<equiv> 
       \<forall> fid fdecl vs e p. 
          ( ViperLang.funs (program_total ctxt) fid = Some fdecl \<and>            
            body fdecl = Some e \<and>
            vals_well_typed (absval_interp_total ctxt) vs (args fdecl) \<and>
            post fdecl = Some p)  \<longrightarrow>
             (
              assertion_self_framing_store ctxt (pre fdecl) (nth_option vs) \<and>
                (\<forall> \<omega> extVal.
                  assertion_sat ctxt R \<Lambda> (pre fdecl) (update_store_total \<omega> (nth_option vs)) \<longrightarrow>
    
                    ctxt, R, (Some (update_store_total \<omega> (nth_option vs))) \<turnstile> \<langle>e; (update_store_total \<omega> (nth_option vs))\<rangle> [\<Down>]\<^sub>t extVal \<and>
                      ((\<exists> v. extVal = Val v \<and>
                         assertion_sat ctxt R \<Lambda> p (update_store_total \<omega> (nth_option (vs@[v])))))
                )
             )"

definition predicate_obligations :: "'a total_context \<Rightarrow> bool"
  where
    "predicate_obligations ctxt \<equiv>
       \<forall> pid pdecl vs e.
        ( ViperLang.predicates (program_total ctxt) pid = Some pdecl \<and>
          predicate_decl.body pdecl = Some e \<and>
          vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl) ) \<longrightarrow>
          assertion_self_framing_store ctxt e (nth_option vs)"

definition stmt_correct_total :: " 'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> stmt \<Rightarrow>  bool"
  where "stmt_correct_total ctxt R \<Lambda> s \<equiv>
         heap_dep_interp_wf ctxt R \<Lambda> \<longrightarrow>           
           heap_dep_fun_obligations ctxt R \<Lambda> \<and>
           predicate_obligations ctxt \<and>
           (\<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
                red_stmt_total ctxt R \<Lambda> s \<omega> r \<longrightarrow> r \<noteq> RFailure)"

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
