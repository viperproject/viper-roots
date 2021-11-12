theory TotalSemantics
imports Viper.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" TotalUtil
begin

(*datatype 'a result = Failure | Set (select_set: "'a full_total_state set")*)


(*
lemma InhPureNormal:
  assumes "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and
          "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        shows "red_inhale Pr \<Delta> havoc_new (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using InhPureNormalMagic[OF assms]
  by simp
*)

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


inductive red_exhale :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a  exhale_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and \<omega>0 :: "'a full_total_state"
  where

\<comment>\<open>exhale acc(e.f, p)\<close>
    ExhAcc: 
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
       Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       a = the_address r \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) (m,pm) 
                           (exh_if_total (p \<ge> 0 \<and> pgte (m(a,f)) (Abs_prat p) \<and> r \<noteq> Null) (m( (a,f) := psub (m (a,f)) (Abs_prat p)),pm)) "

 \<comment>\<open>Exhaling wildcard removes some non-zero permission that this is less than the current permission held\<close>
  | ExhAccWildcard:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       q \<in> {p. p \<noteq> pnone \<and> pgt (m(a,f)) q} \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f Wildcard)) (m,pm) 
                           (exh_if_total (m(a,f) \<noteq> pnone \<and> r \<noteq> Null) 
                                         (m( (a,f) := q),pm))"

\<comment>\<open>exhale acc(P(es), p)\<close>
  | ExhAccPred:
     "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (map Val v_args);
       Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) (m,pm)
              (exh_if_total (p \<ge> 0 \<and> pgte (pm(pred_id, v_args)) (Abs_prat p) \<and> r \<noteq> Null) 
                            (m, pm( (pred_id, v_args) := psub (pm (pred_id, v_args)) (Abs_prat p))))"
  | ExhAccPredWildcard:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m;
       red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (map Val v_args);
       q \<in> {p. p \<noteq> pnone \<and> pgt (m(a,f)) q} \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) (m,pm) 
                           (exh_if_total (m(a,f) \<noteq> pnone)
                                         (m, pm ( (pred_id, v_args) := q )))"

\<comment>\<open>exhale other cases\<close>
  | ExhPure:
    "\<lbrakk> \<omega> = update_mh_total_full \<omega>0 m; 
       Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Pure e)) (m,pm) (if b then ExhaleNormal (m,pm) else ExhaleFailure)"
  | SubAtomicFailure: 
    "\<lbrakk> e \<in> sub_expressions_atomic A ;
      Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure  \<rbrakk> \<Longrightarrow> 
       red_exhale Pr \<Delta> \<omega>0 (Atomic A) (m,pm) ExhaleFailure"

\<comment>\<open>exhale A && B\<close>
  |  ExhSepNormal: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A m_pm (ExhaleNormal m_pm'); 
      red_exhale Pr \<Delta> \<omega>0 B m_pm' res\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m_pm res"
 | ExhSepFailureMagic: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A m_pm ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m_pm ExhaleFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
 | ExhImpTrue: 
   "\<lbrakk>  \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm);
      Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_exhale Pr \<Delta> \<omega>0 A m_pm res \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Imp e A) m_pm res" 
 | ExhImpFalse:  
   "\<lbrakk> \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm);
      Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_exhale Pr \<Delta> \<omega>0 (Imp e A) m_pm (ExhaleNormal m_pm)"
 | ExhImpFailure:
   "\<lbrakk> \<omega> = update_m_total_full \<omega>0 (fst m_pm) (snd m_pm); 
      Pr, \<Delta>, get_valid_locs \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> 
     red_exhale Pr \<Delta> \<omega>0 (Imp e A) m_pm ExhaleFailure"


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

(* Currently, red_stmt_total_single is a function. But if angelism is added, then it would not be a 
function *) (* inhale (acc(x.f) && x.f = 5 \<Longrightarrow> 0/0 = 0/0) *)

inductive red_stmt_total_single_set :: "program \<Rightarrow> 'a interp \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> (stmt+unit) \<times> ('a standard_result) \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" where
   RedSkip: " red_stmt_total_single_set Pr \<Delta> Skip \<omega> (Inr (), RNormal \<omega>)" 
 | RedInhale: 
   "\<lbrakk> red_inhale Pr \<Delta> A \<omega> res \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Inhale A) \<omega> (Inr (), res)"
 | RedExhale: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) (ExhaleNormal m');
      \<omega>' \<in> exhale_state \<omega> m' \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Exhale A) \<omega> (Inr (), RNormal \<omega>')"
 | RedExhaleFailure:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Exhale A) \<omega> (Inr (), RFailure)"
 | RedAssert:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) (ExhaleNormal m') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Assert A) \<omega> (Inr (), RNormal \<omega>)"
 | RedAssertFailure:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Assert A) \<omega> (Inr (), RFailure)"


\<comment>\<open>TODO: Add semantics for \<^term>\<open>Assume A\<close>. Should be the same as \<^term>\<open>Assert A\<close>, except that 
        \<^term>\<open>Assert A\<close> goes to failure iff \<^term>\<open>Assume A\<close> goes to magic. The back-ends implement it
        differently correctly. \<close>
 (*| RedAssume: "red_stmt_total_single_set Pr (Assume A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) True A \<omega>))"*)
(* | RedExhale: "red_stmt_total_single_set Pr (Exhale A) \<omega> 
                     (Inr (), map_option_2 (\<lambda>xs. Set (\<Union>m \<in> xs. exhale_state \<omega> m)) Failure (handle_exhale_2 Pr \<omega> A (get_total_mask_full \<omega>)))"*)
 | RedLocalAssign:
   "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<rbrakk> \<Longrightarrow> 
     red_stmt_total_single_set Pr \<Delta> (LocalAssign x e) \<omega> (Inr (), (RNormal (update_store_total \<omega> x v)))"
(*
| RedLocalAssignFailure:
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow> 
   red_stmt_total_single_set Pr \<Delta> (LocalAssign x e) \<omega> (Inr (), RFailure)"
 | RedFieldAssign: 
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>; 
      wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr));
      get_mask_total_full \<omega> (addr,f) \<noteq> pnone;
      Pr, \<Delta>  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> (FieldAssign e_r f e) \<omega> (Inr (), (RNormal (update_heap_total_full \<omega> (addr,f) v)))"
 | RedFieldAssignFailure: 
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> 
      \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<or> 
      (Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null)) \<or> 
      get_mask_total_full \<omega> (addr,f) \<noteq> pnone \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> (FieldAssign e_r f e) \<omega> (Inr (), RFailure)"
 | RedIfTrue: 
   "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> (If e_b s1 s2) \<omega> (Inl s1, RNormal \<omega>)"
 | RedIfFalse: 
   "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
      wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> (If e_b s1 s2) \<omega> (Inl s2, RNormal \<omega>)"
 | RedIfFailure:
    "\<lbrakk> \<not>wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow>
       red_stmt_total_single_set Pr \<Delta> (If e_b s1 s2) \<omega> (Inr (), RFailure)"
 | RedSeq1:
   "\<lbrakk> red_stmt_total_single_set Pr \<Delta> s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: 
   "\<lbrakk> red_stmt_total_single_set Pr \<Delta> s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> (Seq s1 s2) \<omega> (Inl s2, r'')"
*)
type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a standard_result"

inductive red_stmt_total_single :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where 
    NormalSingleStep: "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s \<omega> res \<rbrakk> \<Longrightarrow> 
       red_stmt_total_single Pr \<Delta> conf ((Inl s, RNormal \<omega>)) res"

abbreviation red_stmt_total_multi :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "red_stmt_total_multi Pr \<Delta> conf \<equiv> rtranclp (red_stmt_total_single Pr \<Delta> conf)"

definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_mask_total_full \<omega> = zero_mask"

fun is_failure_config :: "'a stmt_config \<Rightarrow> bool"
  where "is_failure_config config \<longleftrightarrow> (snd config) = RFailure"

fun is_normal_config :: "'a stmt_config \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "is_normal_config config \<omega> \<longleftrightarrow> (snd config) = RNormal \<omega>"

(* todo: incorporate precondition *)
(* first argument is just there to fix 'a *)
definition stmt_verifies_total :: "'a \<Rightarrow> program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow>  bool"
  where "stmt_verifies_total dummy Pr \<Delta> conf s \<equiv> 
         \<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
           red_stmt_total_multi Pr \<Delta> conf ((Inl s, RNormal \<omega>)) r \<longrightarrow> \<not>is_failure_config r"

end