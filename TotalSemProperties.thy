theory TotalSemProperties
imports TotalSemantics
begin

section \<open>Inhale leaves heap unchanged\<close>

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
    using get_mask_total_full_wf by blast
  hence "wf_mask_simple m"
    unfolding wf_mask_simple_def
    using A1 A2
    by auto
  thus ?thesis using A2 \<open>\<omega>' = _\<close>
    by blast
qed

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

section \<open>Unfold leads to one normal successor state\<close>

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

subsection \<open>Basic properties\<close>

lemma red_stmt_total_single_final:
  assumes "red_stmt_total_single Pr ctxt \<Lambda> (Inr (), q) z"
  shows "False"
  using assms
  by cases

lemma red_stmt_total_multi_final:
  assumes "red_stmt_total_multi Pr ctxt \<Lambda> r1 r2" and "r1 = (Inr(), q)"
  shows "r2 = (Inr (), q)"
  using assms
  by (induction arbitrary: q)
     (auto dest: red_stmt_total_single_final)


lemma red_stmt_total_single_normal_source:
  assumes "red_stmt_total_single Pr ctxt_vpr \<Lambda>_vpr y y'"
 shows "\<exists>\<omega>. snd y = RNormal \<omega>"
  using assms
  by (cases) auto

lemma red_stmt_total_multi_normal_source:
  assumes "red_stmt_total_multi Pr ctxt_vpr \<Lambda>_vpr y y'" and
          "snd y' = RNormal \<omega>'"
  shows "\<exists>\<omega>. snd y = RNormal \<omega>"
  using assms
  by (induction arbitrary: \<omega>')
     (auto dest: red_stmt_total_single_normal_source)


end