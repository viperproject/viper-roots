theory TotalExpressionsExperiment
imports TotalExpressions
begin

section \<open>This theory is used to experiment with definitions and lemmas that could potentially be added 
later to the TotalExpressions theory\<close>

(* Pure quantifier rules (ignore for now)
(* todo fix interpretation in set_from_type *)
| RedForallTrue: "\<lbrakk> \<And>v. v \<in> set_from_type f ty \<longrightarrow> Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk> \<Longrightarrow> 
     Pr, ctxt, \<omega>_def \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
| RedForallFalse: "\<lbrakk> v \<in> set_from_type f ty ; Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk>
  \<Longrightarrow> Pr, ctxt, \<omega>_def \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
(* not clear if one wants to avoid that forall can reduce to false and failure in the same state *)
| RedForallFailure:  "\<lbrakk> v \<in> set_from_type f ty ; Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, ctxt, \<omega>_def \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

(* todo fix interpretation in set_from_type *)
| RedExistsTrue: "\<lbrakk> v \<in> set_from_type f ty ; Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk> \<Longrightarrow>
  Pr, ctxt, \<omega>_def \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
(* not clear if one wants to avoid that forall can reduce to true and failure in the same state *)
| RedExistsFalse: "\<lbrakk> \<And> v. v \<in> set_from_type f ty \<Longrightarrow> Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
  Pr, ctxt, \<omega>_def \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
| RedExistsFailure: "\<lbrakk>v \<in> set_from_type f ty ; Pr, ctxt, \<omega>_def \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
  Pr, ctxt, \<omega>_def \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
*)
(*
| RedForallFalse: "\<lbrakk> v \<in> set_from_type ctxt ty ; Pr, ctxt \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk>
  \<Longrightarrow> Pr, ctxt \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"*)

(*
(* perm(P(...)) = 0 if equirecursive *)
| RedPermPred: "\<lbrakk> list_all2 (\<lambda>e v. Pr, ctxt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vals \<rbrakk>
  \<Longrightarrow> Pr, ctxt \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_prat (get_pm \<omega> (p, vals))))"
*)
(*| RedLet: "\<lbrakk> Pr, ctxt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, ctxt \<turnstile> \<langle>e2; shift_and_add_state \<omega> v1\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow> Pr, ctxt \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>]\<^sub>t r" *)


(* QP inhale rules (ignore for now)
| InhQP:
 "\<lbrakk>  \<And>v. v \<in> set_from_type placeholder ty \<Longrightarrow> ctxt, R, Some (shift_and_add_state \<omega> v) \<turnstile> \<langle>e_r; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address (q1 v))));
    \<And>v. v \<in> set_from_type placeholder ty \<Longrightarrow> ctxt, R, Some (shift_and_add_state \<omega> v) \<turnstile> \<langle>e_p; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t (Val (VPerm (q2 v)));
    \<And>v. v \<in> set_from_type placeholder ty \<Longrightarrow> ctxt, R, Some (shift_and_add_state \<omega> v) \<turnstile> \<langle>cond; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t (Val (VBool (q3 v)));
    m = get_mh_total_full \<omega>;
    inj_on q2 {v. v \<in> (set_from_type placeholder ty) \<and> q3 v \<and> q2 v > 0 } ;
   \<And>v. v \<in> set_from_type placeholder ty \<Longrightarrow> m' ((q1 v), f) = (if (q3 v) \<and> (q2 v > 0) then padd (m ((q1 v), f)) (Abs_prat (q2 v)) else m ((q1 v), f));
   \<And>v. v \<notin> set_from_type placeholder ty \<Longrightarrow> m' ((q1 v), f) = m ((q1 v, f))
 \<rbrakk> \<Longrightarrow>
   red_inhale ctxt R (ForAll ty (Imp cond (Atomic (Acc e_r f (PureExp e_p))))) \<omega> (RNormal \<omega>')"

| InhQPFailure:
 "\<lbrakk>  v \<in> set_from_type placeholder ty;
     red_inhale ctxt R (Imp cond (Atomic (Acc e_r f (PureExp e_p)))) (shift_and_add_state \<omega> v) RFailure
 \<rbrakk> \<Longrightarrow>
   red_inhale ctxt R (ForAll ty (Imp cond (Atomic (Acc e_r f (PureExp e_p))))) \<omega> RFailure"
*)
(*
lemma red_total_with_wf_implies_without_wf:
  assumes "Pr, ctxt_vpr, Some \<omega>' \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<Longrightarrow> Pr, ctxt_vpr, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
          "red_pure_exps_total Pr ctxt Some \<omega>' es \<omega> (Some vs) \<Longrightarrow> red_pure_exps_total Pr ctxt None \<omega>' es \<omega> (Some vs)"
*)

subsection \<open>Simplified induction principles\<close>

lemma conj2conj2: "A \<and> B \<and> C \<Longrightarrow> C"
  apply (drule conjunct2)
  apply (drule conjunct2)
  by assumption

lemma conj2conj2conj1: "A \<and> B \<and> C \<and> D \<Longrightarrow> C"
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct1)
  by assumption

(*
lemmas red_inhale_induct_aux = mp[OF conj2conj2conj1[OF 
      red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.induct[where ?P1.0 = "\<lambda> a b c d. True" and ?P2.0 = "\<lambda> a b c d. True" and ?P4.0 = "\<lambda> a b c d e. True"]]]

lemma red_inhale_induct [consumes 1, case_names InhAcc InhAccPred InhAccWildcard InhAccPredWildcard 
InhPureNormalMagic InhSubFailure InhSepNormal InhSepFailureMagic InhImpTrue InhImpFalse InhImpFailure]:
  assumes "red_inhale Pr ctxt R A \<omega> res" and
    "(\<And>\<omega> e_r r e_p p W' R f res.
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<Longrightarrow>
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<Longrightarrow>
            W' = inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_prat p)) \<Longrightarrow>
            th_result_rel (0 \<le> p) (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<Longrightarrow> P R (Atomic (Acc e_r f (PureExp e_p))) \<omega> res)" and
    "(\<And>\<omega> e_p p e_args v_args W' R pred_id res.
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<Longrightarrow>
            red_pure_exps_total Pr ctxt (Some \<omega>) e_args \<omega> (Some v_args) \<Longrightarrow>
            W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) (Some (Abs_prat p)) \<Longrightarrow>
            th_result_rel (0 \<le> p) (W' \<noteq> {}) W' res \<Longrightarrow> P R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res)" and
    "(\<And>\<omega> e_r r W' R f res.
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<Longrightarrow>
            W' = inhale_perm_single R \<omega> (the_address r, f) None \<Longrightarrow>
            th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<Longrightarrow> P R (Atomic (Acc e_r f Wildcard)) \<omega> res)" and
    "(\<And>\<omega> e_args v_args W' R pred_id res.
            red_pure_exps_total Pr ctxt (Some \<omega>) e_args \<omega> (Some v_args) \<Longrightarrow>
            W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) None \<Longrightarrow>
            th_result_rel True (W' \<noteq> {}) W' res \<Longrightarrow> P R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res)"
    "(\<And>\<omega> e b R.
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<Longrightarrow>
            P R (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic))" and
    "(\<And>e A \<omega> R.
            e \<in> sub_expressions_atomic A \<Longrightarrow> Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> True \<Longrightarrow> P R (Atomic A) \<omega> RFailure)" and
    "(\<And>R A \<omega> \<omega>'' B res.
            red_inhale Pr ctxt R A \<omega> (RNormal \<omega>'') \<Longrightarrow>
            P R A \<omega> (RNormal \<omega>'') \<Longrightarrow> red_inhale Pr ctxt R B \<omega>'' res \<Longrightarrow> P R B \<omega>'' res \<Longrightarrow> P R (A && B) \<omega> res)" and
    "(\<And>R A \<omega> resA B. red_inhale Pr ctxt R A \<omega> resA \<Longrightarrow> P R A \<omega> resA \<Longrightarrow> resA = RFailure \<or> resA = RMagic \<Longrightarrow> P R (A && B) \<omega> resA)" and
    "(\<And>\<omega> e R A res.
            Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<Longrightarrow>
            red_inhale Pr ctxt R A \<omega> res \<Longrightarrow> P R A \<omega> res \<Longrightarrow> P R (Imp e A) \<omega> res)" and
    "(\<And>\<omega> e R A. Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<Longrightarrow> P R (Imp e A) \<omega> (RNormal \<omega>))" and
    "(\<And>\<omega> e R A. Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P R (Imp e A) \<omega> RFailure)" and
    "(\<And>\<omega> e R A. Pr, ctxt, (Some \<omega>) \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P R (Imp e A) \<omega> RFailure)"
 shows "P R A \<omega> res"
  apply (rule red_inhale_induct_aux[where ?P3.0=P])
  apply simp
  by (tactic \<open>resolve_tac @{context} @{thms assms} 1\<close>, assumption+)+ (auto intro: assms(1))
*)

end