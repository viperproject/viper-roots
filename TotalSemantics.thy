section \<open>Total heap semantics of statements\<close>

theory TotalSemantics
imports Viper.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" TotalUtil
begin

datatype 'a exhale_result = ExhaleNormal "mask \<times> 'a predicate_mask" | ExhaleFailure

fun exh_if_total :: "bool \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a exhale_result"  where
  "exh_if_total False _ = ExhaleFailure"
| "exh_if_total True m = ExhaleNormal m"


definition exhale_perm_single :: "mask \<Rightarrow> heap_loc \<Rightarrow> prat option \<Rightarrow> mask set"
  where "exhale_perm_single m lh p_opt =
      {m'| m' q. 
               (p_opt = None \<longrightarrow> pgt q pnone) \<and>
               option_fold ((=) q) (q \<noteq> pnone \<and> pgt (m lh) q) p_opt \<and>
               m' = m(lh := psub (m lh) q)
       }"

inductive red_exhale :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a  exhale_result \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "'a full_total_state \<Rightarrow> bool" and \<omega>0 :: "'a full_total_state"
  where

\<comment>\<open>exhale acc(e.f, p)\<close>
    ExhAcc: 
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
       ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       a = the_address r \<rbrakk> \<Longrightarrow>
       red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) (m,pm) 
                           (exh_if_total (p \<ge> 0 \<and> pgte (m(a,f)) (Abs_prat p) \<and> r \<noteq> Null) (m( (a,f) := psub (m (a,f)) (Abs_prat p)),pm)) "

 \<comment>\<open>Exhaling wildcard removes some non-zero permission that is less than the current permission held.\<close>
  | ExhAccWildcard:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       q = (SOME p. p \<noteq> pnone \<and> pgt (m(a,f)) q) \<rbrakk> \<Longrightarrow>
       red_exhale ctxt R \<omega>0 (Atomic (Acc e_r f Wildcard)) (m,pm) 
                           (exh_if_total (m(a,f) \<noteq> pnone \<and> r \<noteq> Null) 
                                         (m( (a,f) := q),pm))"

\<comment>\<open>exhale acc(P(es), p)\<close>
  | ExhAccPred:
     "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
       ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<rbrakk> \<Longrightarrow>
      red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) (m,pm)
              (exh_if_total (p \<ge> 0 \<and> pgte (pm(pred_id, v_args)) (Abs_prat p) \<and> r \<noteq> Null) 
                            (m, pm( (pred_id, v_args) := psub (pm (pred_id, v_args)) (Abs_prat p))))"
  | ExhAccPredWildcard:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
       q \<in> {p. p \<noteq> pnone \<and> pgt (m(a,f)) q} \<rbrakk> \<Longrightarrow>
       red_exhale ctxt R \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) (m,pm) 
                           (exh_if_total (m(a,f) \<noteq> pnone)
                                         (m, pm ( (pred_id, v_args) := q )))"

  | ExhPure:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m; 
       ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
       red_exhale ctxt R \<omega>0 (Atomic (Pure e)) (m,pm) (if b then ExhaleNormal (m,pm) else ExhaleFailure)"
  | SubAtomicFailure: 
    "\<lbrakk> e \<in> sub_expressions_atomic A ;
      ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure  \<rbrakk> \<Longrightarrow> 
       red_exhale ctxt R \<omega>0 (Atomic A) (m,pm) ExhaleFailure"

\<comment>\<open>exhale A && B\<close>
  |  ExhSepNormal: 
   "\<lbrakk> red_exhale ctxt R \<omega>0 A m_pm (ExhaleNormal m_pm'); 
      red_exhale ctxt R \<omega>0 B m_pm' res\<rbrakk> \<Longrightarrow>
      red_exhale ctxt R \<omega>0 (A && B) m_pm res"
 | ExhSepFailureMagic: 
   "\<lbrakk> red_exhale ctxt R \<omega>0 A m_pm ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_exhale ctxt R \<omega>0 (A && B) m_pm ExhaleFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
 | ExhImpTrue: 
   "\<lbrakk>  \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm);
      ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_exhale ctxt R \<omega>0 A m_pm res \<rbrakk> \<Longrightarrow>
      red_exhale ctxt R \<omega>0 (Imp e A) m_pm res" 
 | ExhImpFalse:  
   "\<lbrakk> \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm);
      ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_exhale ctxt R \<omega>0 (Imp e A) m_pm (ExhaleNormal m_pm)"
 | ExhImpFailure:
   "\<lbrakk> \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm); 
      ctxt, R, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> 
     red_exhale ctxt R \<omega>0 (Imp e A) m_pm ExhaleFailure"

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
              get_m_total_full \<omega>' = m \<and>
              get_h_total_full \<omega>' \<in> 
                   havoc_undef_locs (get_hh_total_full \<omega>) (get_hp_total_full \<omega>) (fst m) (snd m)}"

lemma exhale_state_same_store: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_store_total \<omega>' = get_store_total \<omega>"
  by (simp add: exhale_state_def)

lemma exhale_state_same_trace: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_trace_total \<omega>' = get_trace_total \<omega>"
  by (simp add: exhale_state_def)

inductive fold_rel :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> prat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a standard_result \<Rightarrow> bool"
  where 
    FoldRelNormal: 
      "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       red_exhale ctxt R (update_store_total \<omega> (nth_option vs)) (syntactic_mult (Rep_prat q) pred_body) (get_m_total_full \<omega>) (ExhaleNormal m');    
       mp'' = (snd m')( (pred_id,vs) :=  padd (m (pred_id, vs)) q);
       \<omega>2 = update_m_total_full \<omega> (fst m') mp''\<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> (RNormal \<omega>2)"
  | FoldRelFailure:
       "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
       ViperLang.predicate_decl.body pred_decl = Some pred_body;
       q \<noteq> pnone;
       red_exhale ctxt R (update_store_total \<omega> (nth_option vs)) (syntactic_mult (Rep_prat q) pred_body) (get_m_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow> 
       fold_rel ctxt R pred_id vs q \<omega> RFailure"    

fun sub_expressions :: "stmt \<Rightarrow> pure_exp set" where
  "sub_expressions (If p _ _) = {p}"
| "sub_expressions (LocalAssign _ e) = {e}"
| "sub_expressions (FieldAssign e1 _ e2) = {e1, e2}"
| "sub_expressions (Unfold _ l pw) = set l \<union> sub_expressions_exp_or_wildcard pw"
| "sub_expressions (Fold _ l pw) = set l \<union> sub_expressions_exp_or_wildcard pw"
| "sub_expressions _ = {}"
\<comment>\<open>TODO: \<^const>\<open>sub_expressions\<close> is duplicated from ViperLang\<close>

inductive red_stmt_total_single_set :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow>  stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> (stmt+unit) \<times> ('a standard_result) \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "('a full_total_state \<Rightarrow> bool)" and \<Lambda> :: "type_context"  where
\<comment>\<open>Atomic statements\<close>
   RedSkip: "red_stmt_total_single_set ctxt R \<Lambda> Skip \<omega> (Inr (), RNormal \<omega>)" 
 | RedInhale: 
   "\<lbrakk> red_inhale ctxt R A \<omega> res \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Inhale A) \<omega> (Inr (), res)"
 | RedExhale:
   "\<lbrakk> red_exhale ctxt R \<omega> A (get_m_total_full \<omega>) (ExhaleNormal m');
      \<omega>' \<in> exhale_state \<omega> m' \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Exhale A) \<omega> (Inr (), RNormal \<omega>')"
 | RedExhaleFailure:
   "\<lbrakk> red_exhale ctxt R \<omega> A (get_m_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Exhale A) \<omega> (Inr (), RFailure)"
 | RedAssert:
   "\<lbrakk> red_exhale ctxt R \<omega> A (get_m_total_full \<omega>) (ExhaleNormal m') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Assert A) \<omega> (Inr (), RNormal \<omega>)"
 | RedAssertFailure:
   "\<lbrakk> red_exhale ctxt R \<omega> A (get_m_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Assert A) \<omega> (Inr (), RFailure)"

\<comment>\<open>Note that exhale is demonic here (even locally). For instance, exhale acc(x.f, wildcard) * acc(x.f, 1/2)
always has at least one failure transition, which is not in-sync with Carbon's reordering heuristic for
wildcards. We might want to make exhale locally angelic instead. The premise in Failure rule would have to 
be changed to\<^term>\<open>\<forall>res. red_exhale Pr ctxt \<omega> A (get_m_total_full \<omega>) res \<longrightarrow> res = ExhaleFailure\<close>\<close>


\<comment>\<open>TODO: Add semantics for \<^term>\<open>Assume A\<close>. \<close>

\<comment>\<open>only reduce assignment if RHS has the type expected by LHS \<close>
 | RedLocalAssign:
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v);
      \<Lambda> x = Some ty; 
      get_type (absval_interp_total ctxt) v = ty \<rbrakk> \<Longrightarrow> 
     red_stmt_total_single_set ctxt R \<Lambda> (LocalAssign x e) \<omega> (Inr (), (RNormal (update_var_total \<omega> x v)))"
 | RedFieldAssign: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr));
      get_mh_total_full \<omega> (addr,f) = pwrite;
      ctxt, R, (Some \<omega>)  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (Inr (), (RNormal (update_hh_loc_total_full \<omega> (addr,f) v)))"
\<comment>\<open>Is null case handled in NestedPermSem?\<close>
 | RedFieldAssignFailure: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
      r = Null \<or> get_mh_total_full \<omega> (the_address r,f) \<noteq> pwrite \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (Inr (), (RNormal (update_hh_loc_total_full \<omega> (addr,f) v)))"

| RedUnfold:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p);     
     W' = {\<omega>2. unfold_rel ctxt R pred_id v_args (Abs_prat v_p) \<omega> \<omega>2 \<and> total_heap_consistent ctxt \<omega>2};
     th_result_rel (v_p > 0 \<and> v_p \<le> Rep_prat (get_mp_total_full \<omega> (pred_id, v_args))) True W' res \<rbrakk> \<Longrightarrow>
    red_stmt_total_single_set ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (Inr (), res)"

\<comment>\<open>\<^const>\<open>unfold_rel\<close> constrains permission \<^term>\<open>p\<close> to be strictly positive\<close>
| RedUnfoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     unfold_rel ctxt R pred_id v_args p \<omega> \<omega>' \<rbrakk> \<Longrightarrow>
    red_stmt_total_single_set ctxt R \<Lambda> (Unfold pred_id e_args Wildcard) \<omega> (Inr (), RNormal \<omega>')"
| RedUnfoldWildcardFailure:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
     get_mp_total_full \<omega> (pred_id, v_args) = pnone \<rbrakk> \<Longrightarrow>
    red_stmt_total_single_set ctxt R \<Lambda> (Unfold pred_id e_args Wildcard) \<omega> 
      (Inr (), RFailure)"
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
    red_stmt_total_single_set ctxt R \<Lambda> (Fold pred_id e_args (PureExp e_p)) \<omega> (Inr (), res)"

| RedFoldWildcard:
  "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);     
     fold_rel ctxt R pred_id v_args p \<omega> res \<rbrakk> \<Longrightarrow>
    red_stmt_total_single_set ctxt R \<Lambda> (Fold pred_id e_args Wildcard) \<omega> (Inr (), res)"
\<comment>\<open>TODO: fold acc(P(x),0)\<close>

\<comment>\<open>Composite statements\<close>

 | RedIfTrue: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set ctxt R \<Lambda> (If e_b s1 s2) \<omega> (Inl s1, RNormal \<omega>)"
 | RedIfFalse: 
   "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set ctxt R \<Lambda> (If e_b s1 s2) \<omega> (Inl s2, RNormal \<omega>)"
 | RedIfFailure:
    "\<lbrakk> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
       red_stmt_total_single_set ctxt R \<Lambda> (If e_b s1 s2) \<omega> (Inr (), RFailure)"
 | RedSeq1:
   "\<lbrakk> red_stmt_total_single_set ctxt R \<Lambda> s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: 
   "\<lbrakk> red_stmt_total_single_set ctxt R \<Lambda> s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set ctxt R \<Lambda> (Seq s1 s2) \<omega> (Inl s2, r'')"

\<comment>\<open>Failure subexpression\<close>
| RedSubExpressionFailure: 
  "\<lbrakk> e \<in> sub_expressions s; ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure  \<rbrakk> \<Longrightarrow> 
    red_stmt_total_single_set ctxt R \<Lambda> s \<omega> (Inr (), RFailure)"

inductive_cases RedLocalAssign_case: 
     "red_stmt_total_single_set ctxt R \<Lambda> (LocalAssign x e) \<omega> (Inr (), (RNormal (update_var_total \<omega> x v)))"

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a standard_result"

inductive red_stmt_total_single :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where 
    NormalSingleStep: "\<lbrakk> red_stmt_total_single_set ctxt R \<Lambda> s \<omega> res \<rbrakk> \<Longrightarrow> 
       red_stmt_total_single ctxt R \<Lambda> ((Inl s, RNormal \<omega>)) res"

inductive_cases NormalSingleStep_case [elim]: "red_stmt_total_single ctxt R \<Lambda> ((Inl s, RNormal \<omega>)) res"

abbreviation red_stmt_total_multi :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "red_stmt_total_multi ctxt R \<Lambda> \<equiv> rtranclp (red_stmt_total_single ctxt R \<Lambda>)"

definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_m_total_full \<omega> = (zero_mask, zero_mask)"

fun is_failure_config :: "'a stmt_config \<Rightarrow> bool"
  where "is_failure_config config \<longleftrightarrow> (snd config) = RFailure"

fun is_normal_config :: "'a stmt_config \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "is_normal_config config \<omega> \<longleftrightarrow> (snd config) = RNormal \<omega>"

subsection \<open>Correctness\<close>

definition vals_well_typed :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a val) list \<Rightarrow> vtyp list \<Rightarrow> bool"
  where "vals_well_typed A vs ts \<equiv> map (get_type A) vs = ts"

definition assertion_sat :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "assertion_sat \<Lambda> R ctxt A \<omega> = 
            (\<forall> res. red_stmt_total_single_set \<Lambda> R ctxt (Assert A) \<omega> res \<longrightarrow> (snd res) \<noteq> RFailure)"

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
                red_stmt_total_multi ctxt R \<Lambda> ((Inl s, RNormal \<omega>)) r \<longrightarrow> \<not>is_failure_config r)"

end
