theory TotalSemProperties
imports TotalSemantics
begin

subsection \<open>Induction schemes\<close>

subsection \<open>Inhale\<close>

text \<open>Inhale only changes mask\<close>

lemma inhale_perm_single_store_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_store_total \<omega>' = get_store_total \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by auto

lemma inhale_perm_single_trace_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_trace_total \<omega>' = get_trace_total \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by auto

lemma inhale_perm_single_heap_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_h_total_full \<omega>' = get_h_total_full \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by fastforce

lemma inhale_perm_single_pred_store_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred R \<omega> lh popt"
  shows "get_store_total \<omega>' = get_store_total \<omega>"
  using assms
  unfolding inhale_perm_single_pred_def
  by auto

lemma inhale_perm_single_pred_trace_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred R \<omega> lh popt"
  shows "get_trace_total \<omega>' = get_trace_total \<omega>"
  using assms
  unfolding inhale_perm_single_pred_def
  by auto

lemma inhale_perm_single_pred_heap_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred R \<omega> lh popt"
  shows "get_h_total_full \<omega>' = get_h_total_full \<omega>"
  using assms 
  unfolding inhale_perm_single_pred_def
  by fastforce

lemmas inhale_perm_single_only_mask_changed=
  inhale_perm_single_store_same
  inhale_perm_single_trace_same
  inhale_perm_single_heap_same

lemmas inhale_perm_pred_single_only_mask_changed=
  inhale_perm_single_pred_store_same
  inhale_perm_single_pred_trace_same
  inhale_perm_single_pred_heap_same

lemma inhale_only_changes_mask:
  shows "ctxt, R, x1 \<turnstile> \<langle>x2;x3\<rangle> [\<Down>]\<^sub>t x4 \<Longrightarrow> True" and
        "red_pure_exps_total ctxt R x5 x6 x7 x8 \<Longrightarrow> True" and
        "red_inhale ctxt R A \<omega> res \<Longrightarrow> (\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow> 
             get_store_total \<omega>' = get_store_total \<omega> \<and>
             get_trace_total \<omega>' = get_trace_total \<omega> \<and>
             get_h_total_full \<omega>' = get_h_total_full \<omega>)" and
        "unfold_rel ctxt R x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction rule: red_exp_inhale_unfold_inducts)
  case (InhAcc \<omega> e_r r e_p p W' f res)
  then show ?case 
    by (metis inhale_perm_single_only_mask_changed singleton_iff th_result_rel_normal)
next
  case (InhAccPred \<omega> e_p p e_args v_args W' pred_id res)
  then show ?case 
  using inhale_perm_pred_single_only_mask_changed th_result_rel_normal by blast
next
  case (InhAccWildcard \<omega> e_r r W' f res)
  then show ?case     
    by (metis inhale_perm_single_only_mask_changed th_result_rel_normal)
next
  case (InhAccPredWildcard \<omega> e_args v_args W' pred_id res)
  then show ?case
    using inhale_perm_pred_single_only_mask_changed th_result_rel_normal by blast
next
  case (InhPure \<omega> e b)
  then show ?case
    by (metis stmt_result_total.distinct(3) stmt_result_total.inject)
next
  case (InhSubAtomicFailure A \<omega>)
  then show ?case by simp
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  then show ?case by presburger
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case by simp
next
  case (InhImpTrue \<omega> e A res)
  then show ?case by simp
next
  case (InhImpFalse \<omega> e A)
  then show ?case by simp
next
  case (InhImpFailure \<omega> e A)
  then show ?case by simp
qed (rule HOL.TrueI)+

text \<open>inhale preserves failure for smaller states if there is no permission introspection\<close>
thm red_exp_inhale_unfold_inducts
lemma inhale_no_perm_failure_preserve_mono:
  shows "ctxt, R, x1 \<turnstile> \<langle>x2;x3\<rangle> [\<Down>]\<^sub>t x4 \<Longrightarrow> True" and
        "red_pure_exps_total ctxt R x5 x6 x7 x8 \<Longrightarrow> True" and
        \<comment>\<open>TODO: add no permission introspection property\<close>
        "red_inhale ctxt R A \<omega>1 res1 \<Longrightarrow> \<omega>2 \<le> \<omega>1 \<Longrightarrow> res1 \<noteq> RMagic \<Longrightarrow> 
              (res1 = RFailure \<longrightarrow> red_inhale ctxt R A \<omega>2 RFailure) \<and>
              (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> (\<exists>\<omega>2'. \<omega>2' \<le> \<omega>1' \<and> red_inhale ctxt R A \<omega>2 (RNormal \<omega>2')))" and
        "unfold_rel ctxt R x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction arbitrary:  and and \<omega>2 rule: red_exp_inhale_unfold_inducts)
  case (InhAcc \<omega> e_r r e_p p W' f res)
  then show ?case sorry
next
  case (InhAccPred \<omega> e_p p e_args v_args W' pred_id res)
  then show ?case sorry
next
  case (InhAccWildcard \<omega> e_r r W' f res)
  then show ?case sorry
next
  case (InhAccPredWildcard \<omega> e_args v_args W' pred_id res)
  then show ?case sorry
next
  case (InhPure \<omega> e b)
  then show ?case sorry
next
  case (InhSubAtomicFailure A \<omega>)
  then show ?case sorry
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  then show ?case sorry
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case sorry
next
  case (InhImpTrue \<omega> e A res)
  then show ?case sorry
next
  case (InhImpFalse \<omega> e A)
  then show ?case sorry
next
  case (InhImpFailure \<omega> e A)
  then show ?case sorry
qed (rule HOL.TrueI)+

(*
lemma inhale_perm_single_mupd:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "\<exists>mh. wf_mask_simple mh \<and> \<omega>' = update_mh_total_full \<omega> mh"
proof -
  from assms obtain m q where 
       "\<omega>' = update_mh_total_full \<omega> m" and
       A1:"pgte pwrite (padd (get_mh_total_full \<omega> lh) q)" and
       A2:"m = (get_mh_total_full \<omega>)(lh := (padd (get_mh_total_full \<omega> lh) q))"
    unfolding inhale_perm_single_def
    by blast
  have "wf_mask_simple (get_mh_total_full \<omega>)"
    
  hence "wf_mask_simple m"
    unfolding wf_mask_simple_def
    using A1 A2
    by auto
  thus ?thesis using A2 \<open>\<omega>' = _\<close>
    by blast
qed
*)
(*
lemma inhale_perm_single_h_eq: 
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> hloc popt"
  shows "get_h_total_full \<omega>' = get_h_total_full \<omega>"
  using assms inhale_perm_single_mupd update_mh_total_full_hh_eq by blast 

lemma inhale_perm_single_pred_mupd:
  assumes  "\<omega>' \<in> inhale_perm_single_pred R \<omega> lp popt"
  shows "\<exists>mp. \<omega>' = update_mp_total_full \<omega> mp"
  using assms inhale_perm_single_pred_def
  by blast

lemma inhale_perm_single_pred_h_eq: 
  assumes  "\<omega>' \<in> inhale_perm_single_pred R \<omega> lp popt"
  shows "get_h_total_full \<omega>' = get_h_total_full \<omega>"
  using assms inhale_perm_single_pred_mupd update_mp_total_h_full_eq
  by blast
*)

(*
lemma inhale_heap_unchanged: 
  assumes "red_inhale Pr \<Delta> R A \<omega> (RNormal \<omega>')"
  shows "get_h_total_full \<omega> = get_h_total_full \<omega>'"
  using assms
proof (induct R A \<omega> "(RNormal \<omega>')" arbitrary: \<omega>' rule: red_inhale_induct)
  case (InhAcc \<omega> e_r r e_p p W' R f)
  hence "\<omega>' \<in> W'" using th_result_rel_normal  by blast
  thus ?case using \<open>W' = _\<close> inhale_perm_single_h_eq by metis
next
  case (InhAccPred \<omega> e_p p e_args v_args W' R pred_id)
  hence "\<omega>' \<in> W'" using th_result_rel_normal  by blast
  thus ?case using \<open>W' = _\<close> inhale_perm_single_pred_h_eq by metis
next
case (InhAccWildcard \<omega> e_r r W' R f)
  hence "\<omega>' \<in> W'" using th_result_rel_normal  by blast
  thus ?case using \<open>W' = _\<close> inhale_perm_single_h_eq by metis
next
case (InhAccPredWildcard \<omega> e_args v_args W' R pred_id)
  hence "\<omega>' \<in> W'" using th_result_rel_normal  by blast
  thus ?case using \<open>W' = _\<close> inhale_perm_single_pred_h_eq by metis
next
case (InhPureNormalMagic \<omega> e b R)
  then show ?case
    by (insert InhPureNormalMagic.hyps, cases b) auto    
qed auto
*)

subsection \<open>Unfold leads to one normal successor state\<close>

(*
lemma unfold_at_least_one:
  assumes "ViperLang.predicates Pr pred_id = Some pdecl" and
          "ViperLang.predicate_decl.body pdecl = Some pbody" and
          C: "total_heap_consistent Pr \<Delta> \<omega>" and
          RedArgs: "red_pure_exps_total Pr \<Delta> (Some \<omega>) e_args \<omega> (Some v_args)" and
          RedPerm: "Pr, \<Delta>, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
          PredPerm:"pgte (get_mp_total_full \<omega> (pred_id, v_args)) (Abs_prat p)"
          "p > 0"
  shows "\<exists> \<omega>'. total_heap_consistent Pr \<Delta> \<omega>' \<and> red_stmt_total_single_set Pr \<Delta> \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (Inr (), RNormal \<omega>')"
proof -
  let ?q = "(Abs_prat p)"
  from \<open>p > 0\<close> have "?q \<noteq> pnone" using positive_rat_prat
    by simp    
  with assms obtain \<omega>' where URel:"unfold_rel Pr \<Delta> pred_id v_args ?q \<omega> \<omega>'" and C\<omega>': "total_heap_consistent Pr \<Delta> \<omega>'"
    by (metis option.distinct(1) option_fold.simps(1) total_heap_consistent.cases)

  from \<open>p > 0\<close> have PEq:"Rep_prat (Abs_prat p) = p"
    using Abs_prat_inverse by auto
  
  show ?thesis
    apply (rule exI[where ?x=\<omega>'])
    apply (rule conjI[OF \<open>total_heap_consistent Pr \<Delta> \<omega>'\<close>])
    apply (rule RedUnfold)
       apply (rule RedArgs)
      apply (rule RedPerm)
     apply (rule refl)
    apply (rule THResultNormal_alt)
      apply (simp add: URel C\<omega>')
     apply (rule conjI[OF \<open>p > 0\<close>])
     using PredPerm PEq pgte.rep_eq
     by auto
qed

lemma fold_normal_consistent:
  assumes "fold_rel Pr \<Delta> pred_id v_args p \<omega> (RNormal \<omega>')" and
       C: "total_heap_consistent Pr \<Delta> \<omega>"
     shows "total_heap_consistent Pr \<Delta> \<omega>'"
  using assms
proof cases
case (FoldRelNormal pred_decl pred_body m' mp'' m)
then show ?thesis oops
*)
end