theory HavocRelation
imports BackwardsSimulation
begin

subsection \<open>Havoc at exhale is sufficient\<close>

definition equal_on_mask :: "mask \<Rightarrow> 'a total_heap \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "equal_on_mask m h1 h2 \<equiv> \<forall> l. m(l) \<noteq> pnone \<longrightarrow> h1(l) = h2(l)"

lemma equal_on_mask_refl: "equal_on_mask m h h"
  by (simp add: equal_on_mask_def)

definition havoc_rel :: "'a simulation_rel"
  where "havoc_rel \<omega> \<omega>' \<equiv> get_mask_total_full \<omega> = get_mask_total_full \<omega>' \<and> 
                          equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>') \<and>
                          get_store_total \<omega> = get_store_total \<omega>'"

lemma init_havoc_rel: "is_empty_total \<omega> \<Longrightarrow> havoc_rel \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2"
  by (simp add: havoc_rel_def is_empty_total_def)

lemma total_havoc_rel: "\<exists> \<omega>'. havoc_rel \<omega> \<omega>'"
  by (rule exI[where ?x=\<omega>]) (simp add: havoc_rel_def equal_on_mask_refl)

lemma havoc_rel_same_store: "havoc_rel \<omega> \<omega>' \<Longrightarrow> get_store_total \<omega> = get_store_total \<omega>'"
  by (simp add: havoc_rel_def)

lemma havoc_rel_same_mask: "havoc_rel \<omega> \<omega>' \<Longrightarrow> get_mask_total_full \<omega> = get_mask_total_full \<omega>'"
  by (simp add: havoc_rel_def)

lemma havoc_rel_eq_on_mask: "havoc_rel \<omega> \<omega>' \<Longrightarrow> equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>')"
  by (auto simp add: havoc_rel_def)

lemma havoc_rel_refl: "havoc_rel \<omega> \<omega>"
  by (simp add: equal_on_mask_refl havoc_rel_def)

lemma havoc_rel_traceupd: "havoc_rel \<omega> (update_trace_total \<omega> \<pi>)"
  unfolding havoc_rel_def
  apply (intro conjI)
    apply simp  
   apply (simp add: equal_on_mask_refl)
  apply simp
  done

lemma havoc_rel_sym: "havoc_rel \<omega> \<omega>' \<Longrightarrow> havoc_rel \<omega>' \<omega>"
  by (simp add: havoc_rel_def equal_on_mask_def)

lemma havoc_rel_valid_locs: 
  assumes "havoc_rel \<omega>1 \<omega>2"
  shows "get_valid_locs \<omega>1 = get_valid_locs \<omega>2"
  using havoc_rel_eq_on_mask[OF assms] havoc_rel_same_mask[OF assms]
  unfolding equal_on_mask_def get_valid_locs_def
  by simp

lemma havoc_rel_valid_locs_2:
  assumes "havoc_rel \<omega>1 \<omega>2"
  shows "\<forall>l\<in>get_valid_locs \<omega>1.
       get_heap_total_full \<omega>1 l = get_heap_total_full \<omega>2 l"
  using assms
  by (metis (mono_tags, lifting) equal_on_mask_def get_valid_locs_def havoc_rel_eq_on_mask mem_Collect_eq prat_pgt_pnone)

lemma havoc_rel_valid_locs_3:
  assumes "havoc_rel \<omega>1 \<omega>2" and "wf_mask_simple m"
  shows "\<forall>l\<in>get_valid_locs \<omega>1.
            get_heap_total_full (update_mask_total_full \<omega>1 m) l = get_heap_total_full (update_mask_total_full \<omega>2 m) l"
  using assms havoc_rel_valid_locs_2
  by (metis update_mask_total_full_same_heap)

text \<open>The following lemma would follow directly from determinism of expression evaluation.\<close>
lemma pure_exp_eval_true_false:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  shows "\<not>(Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True))"
  oops

lemma wd_not_fail:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>"
  shows "v \<noteq> VFailure"
  using assms
proof (induction)
  case (RedCondExpFalse e1 \<omega> e3 r e2)
  then show ?case 
    using pure_exp_eval_true_false
    by fastforce
next
  case (RedBinopFailure e1 \<omega> v1 e2 v2 bop)
  then show ?case 
    using wd_binop_safe
    by force
next
  case (RedOldFailure t l e uz va)
  then show ?case by simp
next
  case (RedPropagateFailure e e' \<omega>)
  then show ?case oops
qed auto

lemma havoc_rel_expr_eval_same: 
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and "havoc_rel \<omega> \<omega>'"
  shows "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t v"
  using assms
proof (induction)
case (RedLit l uu)
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
  case (RedVar \<sigma> n v uv uw)
  hence "get_store_total \<omega>' = \<sigma>"
    unfolding havoc_rel_def by simp
  from this obtain \<pi> \<phi> where "\<omega>' = (\<sigma>,\<phi>,\<pi>)"
    using get_store_total.elims 
    by (metis prod.exhaust_sel)
  then show ?case using RedVar
    by (auto intro!: red_pure_exp_total.intros)
next
case (RedUnop e \<omega> v unop v')
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
  case (RedBinopLazy e1 \<omega> v1 bop v e2)
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
case (RedBinop e1 \<omega> v1 e2 v2 bop v)
  then show ?case 
   by (meson red_pure_exp_total.RedBinop wd_pure_exp_total.simps(4))
next
  case (RedCondExpTrue e1 \<omega> e2 r e3)
  then show ?case 
    by (meson red_pure_exp_total.RedCondExpTrue wd_pure_exp_total.simps(5))
next
  case (RedCondExpFalse e1 \<omega> e3 r e2)
  then show ?case using pure_exp_eval_true_false red_pure_exp_total.RedCondExpFalse
    by (metis wd_pure_exp_total.simps(5))
next
  case (RedPermNull e \<omega> f)
  then show ?case by auto    
next
  case (RedResult \<sigma> v ux uy)
  then show ?case by auto
next
  case (RedBinopRightFailure e1 \<omega> v1 e2 bop)
  then show ?case 
    using red_pure_exp_total.RedBinopRightFailure wd_pure_exp_total.simps(4) by blast
next
  case (RedBinopFailure e1 \<omega> v1 e2 v2 bop)
  then show ?case 
    by (meson red_pure_exp_total.RedBinopFailure wd_pure_exp_total.simps(4))
next
case (RedOldFailure t l e uz va)
  then show ?case by auto
next
  case (RedPropagateFailure e e' \<omega>)
  then show ?case oops
next
  case (RedField e \<omega> a f v)
  thus ?case
    by (smt (verit, ccfv_threshold) equal_on_mask_def havoc_rel_def prat_pgt_pnone red_pure_exp_total.RedField wd_pure_exp_total.simps(6))
next
  case (RedPerm e \<omega> a f)
  then show ?case
    by (metis havoc_rel_def red_pure_exp_total.RedPerm wd_pure_exp_total.simps(8))
qed

lemma havoc_rel_wd_same:
  assumes "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and "havoc_rel \<omega> \<omega>'"
  shows "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>'"
  using assms havoc_rel_sym[OF assms(2)]
  apply (induction Pr \<Delta> CInhale e \<omega> rule: wd_pure_exp_total.induct)
                apply clarsimp
               apply clarsimp
              apply clarsimp
             apply clarsimp
             apply (blast dest: havoc_rel_expr_eval_same)
            apply clarsimp
            apply (blast dest: havoc_rel_expr_eval_same)
           apply (metis havoc_rel_expr_eval_same havoc_rel_same_mask wd_pure_exp_total.simps(6))
           apply (simp add: havoc_rel_expr_eval_same havoc_rel_same_mask)
         apply clarsimp+
  done

lemma havoc_rel_expr_eval_same_exhale: 
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and 
          "wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>" and 
          "\<forall>l \<in> locs. get_heap_total_full \<omega> l = get_heap_total_full \<omega>' l"
          "get_mask_total_full \<omega> = get_mask_total_full \<omega>'" and
          "get_store_total \<omega> = get_store_total \<omega>'"
  shows "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t v"
  using assms
proof (induction)
  case (RedVar \<sigma> n v uv uw)
  show ?case 
    apply (cases \<omega>')
    apply simp
    apply (rule red_pure_exp_total.RedVar)
    using RedVar by simp
  next
    case (RedCondExpFalse e1 \<omega> e3 r e2)
    then show ?case using pure_exp_eval_true_false
      by (metis red_pure_exp_total.RedCondExpFalse wd_pure_exp_total.simps(5))
  next
    case (RedPropagateFailure e e' \<omega>)
    then show ?case oops 
  next
    case (RedField e \<omega> a f v)
    hence "(a,f) \<in> locs" by simp
    hence "get_heap_total_full \<omega> (a,f) = get_heap_total_full \<omega>' (a,f)"      
      using RedField
      by blast 
    thus ?case      
      by (metis RedField.IH RedField.hyps(2) RedField.prems(1) RedField.prems(2) RedField.prems(3) RedField.prems(4) red_pure_exp_total.RedField wd_pure_exp_total.simps(7))
  next
    case (RedPerm e \<omega> a f)
    then show ?case
      by (metis red_pure_exp_total.RedPerm wd_pure_exp_total.simps(8))
  qed (auto intro: red_pure_exp_total.intros)

definition havoc_rel_ext :: "heap_loc set \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "havoc_rel_ext locs \<omega> \<omega>' \<equiv>
          (\<forall>l \<in> locs. get_heap_total_full \<omega> l = get_heap_total_full \<omega>' l) \<and>
          (get_mask_total_full \<omega> = get_mask_total_full \<omega>') \<and>
          (get_store_total \<omega> = get_store_total \<omega>')"

lemma havoc_rel_expr_eval_same_exhale_2: 
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and 
          "wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>" and 
          "havoc_rel_ext locs \<omega> \<omega>'"
        shows "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t v"
  using assms havoc_rel_expr_eval_same_exhale 
  unfolding havoc_rel_ext_def
  by blast

lemma havoc_rel_expr_eval_same_exhale_3: 
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; update_mask_total_full \<omega>1 m\<rangle> [\<Down>]\<^sub>t v" and 
          "wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>1)) e (update_mask_total_full \<omega>1 m)" and 
          "havoc_rel \<omega>1 \<omega>2" and
          "wf_mask_simple m"
  shows "Pr, \<Delta> \<turnstile> \<langle>e; update_mask_total_full \<omega>2 m\<rangle> [\<Down>]\<^sub>t v"
  apply (rule havoc_rel_expr_eval_same_exhale[OF assms(1) assms(2)])
    apply (rule havoc_rel_valid_locs_3[OF assms(3-4)])
   apply (metis assms(4) get_update_mask_total_full)
  by (metis assms(3) fstI get_store_total.simps havoc_rel_same_store update_mask_total_full.simps)

lemma havoc_rel_wd_same_exhale:
  assumes "wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>" and 
          "\<forall>l \<in> locs. get_heap_total_full \<omega> l = get_heap_total_full \<omega>' l"
          "get_mask_total_full \<omega> = get_mask_total_full \<omega>'"
  shows "wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>'"
  using assms
  oops
 (*
  apply (induction Pr \<Delta> "(CExhale locs)" e \<omega> rule: wd_pure_exp_total.induct)
                apply clarsimp
               apply clarsimp
              apply clarsimp


proof (induction Pr \<Delta> "(CExhale locs)" e \<omega> arbitrary: \<omega> \<omega>' rule: wd_pure_exp_total.induct)
  case (4 Pr \<Delta> e1 bop e2 \<omega>)
  have Wd:"wd_pure_exp_total Pr \<Delta> (CExhale locs) e1 \<omega>'"
    using "4.hyps"(1) "4.prems"(1) "4.prems"(2) "4.prems"(3) wd_pure_exp_total.simps(4) by blast
  show ?case 
    apply simp  
    apply (rule conjI[OF Wd])
    apply (rule allI, rule impI, rule impI)
    apply (rule conjI)
     apply (rule allI, rule impI)
     apply (frule  havoc_rel_expr_eval_same_exhale)
         apply (rule Wd)
    using "4.prems"(2)
        apply blast
    using "4.prems"
       apply simp
    using "4.prems"
      apply simp
    
    oops
*)

lemma havoc_rel_wd_same_exhale_2:
  assumes "wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>1)) e (update_mask_total_full \<omega>1 m)" and
          "havoc_rel \<omega>1 \<omega>2" and "wf_mask_simple m"
        shows "wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>2)) e (update_mask_total_full \<omega>2 m)"
  apply (subst HOL.sym[OF havoc_rel_valid_locs[OF assms(2)]])
  apply (rule havoc_rel_wd_same_exhale)
    apply (rule assms(1))
   apply (rule havoc_rel_valid_locs_3[OF assms(2) assms(3)])
  by (metis assms(3) get_update_mask_total_full)

lemma havoc_rel_backwards:
  assumes "\<omega>' \<in> inhale_perm_single True \<omega> (a, f) p_opt" and 
          "havoc_rel \<omega>' \<omega>2'"
  shows "havoc_rel \<omega> (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  using assms
proof -
  let ?m = "get_mask_total_full \<omega>"
  let ?h = "get_heap_total_full \<omega>"
  let ?m' = "get_mask_total_full \<omega>'"
  let ?h' = "get_heap_total_full \<omega>'"
  let ?h2' = "get_heap_total_full \<omega>2'"
  from \<open>havoc_rel \<omega>' \<omega>2'\<close> have "equal_on_mask ?m' ?h' ?h2'"
    using havoc_rel_def by blast

  from \<open>\<omega>' \<in> inhale_perm_single _ _ _ _\<close> obtain v q where
    AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) q))" and
    UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)" and
    SameStore: "get_store_total \<omega>' = get_store_total \<omega>"
    unfolding inhale_perm_single_def
    by auto
  
  have EqOnMask:"equal_on_mask ?m ?h ?h2'"
    unfolding equal_on_mask_def
  proof clarify
    fix hl    
    assume SomePerm:"?m hl \<noteq> pnone"
    hence "?m' hl \<noteq> pnone"
      using AddPerm padd_pos
      by auto      
    hence "?h' hl = ?h2' hl" using \<open>equal_on_mask ?m' ?h' ?h2'\<close>
      unfolding equal_on_mask_def
      by blast
    thus "?h hl = ?h2' hl" 
      using SomePerm UpdateHeap
      by (metis fun_upd_apply)      
  qed

  thus ?thesis
    unfolding havoc_rel_def
    apply (intro conjI)
      apply (metis get_mask_total_full_wf get_update_mask_total_full)
     apply (metis EqOnMask get_mask_total_full_wf update_mask_total_full_same_heap)
    apply (metis (no_types, hide_lams) SameStore \<open>havoc_rel \<omega>' \<omega>2'\<close> get_mask_total_full_wf havoc_rel_same_store old.prod.inject update_mask_total_full.simps update_mask_total_full_multiple)
    done
qed

lemma havoc_inhale_normal_rel:
  assumes "red_inhale Pr \<Delta> True A \<omega> res" and "res = RNormal \<omega>'" and "havoc_rel \<omega>' \<omega>2'" 
  shows "red_inhale Pr \<Delta> False A (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) (RNormal \<omega>2') \<and> havoc_rel \<omega> (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  using assms
proof (induction arbitrary: \<omega>' \<omega>2')
  case (InhSepNormal inh_assume A \<omega> \<omega>'' B res)
  thus ?case
    by (metis get_mask_total_full_wf red_inhale.InhSepNormal update_mask_total_full_multiple)
next
  case (InhImpTrue e \<omega> A res)
  let ?\<omega>2="(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  from InhImpTrue.IH[OF \<open>res = _\<close> \<open>havoc_rel \<omega>' _\<close>] have
    A1:"red_inhale Pr \<Delta> False A ?\<omega>2 (RNormal \<omega>2')" and
    "havoc_rel \<omega> ?\<omega>2"
    by auto
  moreover have A2:"Pr, \<Delta> \<turnstile> \<langle>e;?\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)" using InhImpTrue havoc_rel_expr_eval_same
    by blast
  show ?case
    apply (rule conjI)
     apply (rule red_inhale.InhImpTrue)
       apply (rule havoc_rel_wd_same)
        apply (rule \<open>wd_pure_exp_total Pr \<Delta> _ _ _\<close>)
       apply (rule \<open>havoc_rel \<omega> ?\<omega>2\<close>)
      apply (rule A2)
     apply (rule A1)
    apply (rule \<open>havoc_rel \<omega> ?\<omega>2\<close>)
    done
next
  case (InhImpFalse e \<omega> inh_assume A)
  hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"
    by (metis Rep_total_state_inverse get_heap_total_full.simps get_hm_total_full.simps get_hm_total_full_comp get_store_total.simps get_trace_total.simps havoc_rel_same_mask prod.exhaust_sel stmt_result_total.inject update_mask_total_def update_mask_total_full.simps)
  from InhImpFalse have HRel:"havoc_rel \<omega> \<omega>2'" by simp
  show ?case 
    apply (rule conjI)
    apply (subst StateEq)
     apply (rule red_inhale.InhImpFalse)
       apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ _ _\<close> HRel])
     apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)\<close> \<open>wd_pure_exp_total _ _ _ _ _\<close> ])
     apply (rule HRel)
    apply (subst StateEq)
    apply (rule HRel)
    done
next
  case (InhAcc e_r \<omega> a e_p p \<omega>' f \<omega>'')
    from InhAcc have "havoc_rel \<omega>' \<omega>2'" by simp
    let ?m = "get_mask_total_full \<omega>"
    let ?h = "get_heap_total_full \<omega>"
    let ?m' = "get_mask_total_full \<omega>'"
    let ?h' = "get_heap_total_full \<omega>'"
    from \<open>\<omega>' \<in> _\<close> obtain v where
      AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) (Abs_prat p)))" and
      UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)"
      unfolding inhale_perm_single_def
      by auto

  let ?\<omega>2 = "update_mask_total_full \<omega>2' ?m"
  let ?h2 = "get_heap_total_full ?\<omega>2"
  let ?h2' = "get_heap_total_full \<omega>2'"  
  have "?h2 = ?h2'"
    using update_mask_total_full_same_heap get_mask_total_full_wf
    by blast  

  have HRel:"havoc_rel \<omega> ?\<omega>2"
    using \<open>\<omega>' \<in> _\<close> \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_backwards
    by blast

  have "red_inhale Pr \<Delta> False (Atomic (Acc e_r f e_p)) ?\<omega>2 (RNormal \<omega>2')"
    apply rule
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
        apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>\<close> HRel]) 
       apply (rule \<open>0 \<le> p\<close>)
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
     apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>\<close> HRel])
    apply (unfold inhale_perm_single_def)
    apply rule
    apply (rule exI)+
    apply (intro conjI)
          apply (rule HOL.refl)
         apply simp
        apply simp
       apply simp
      apply (metis AddPerm fun_upd_same get_mask_total_full_wf get_update_mask_total_full wf_mask_simple_def)
     apply (metis AddPerm HRel \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_def)
    using \<open>get_heap_total_full (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = get_heap_total_full \<omega>2'\<close> apply auto
    done  
  then show ?case using HRel
    by simp
next
  case (InhAccWildcard e_r \<omega> a \<omega>' f \<omega>'')
    from InhAccWildcard have "havoc_rel \<omega>' \<omega>2'" by simp
    let ?m = "get_mask_total_full \<omega>"
    let ?h = "get_heap_total_full \<omega>"
    let ?m' = "get_mask_total_full \<omega>'"
    let ?h' = "get_heap_total_full \<omega>'"
    from \<open>\<omega>' \<in> inhale_perm_single _ _ _ _\<close> obtain v p where
      AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) p))" and
              "p \<noteq> pnone" and
      UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)"
      unfolding inhale_perm_single_def
      by auto

  let ?\<omega>2 = "update_mask_total_full \<omega>2' ?m"
  let ?h2 = "get_heap_total_full ?\<omega>2"
  let ?h2' = "get_heap_total_full \<omega>2'"  
  have "?h2 = ?h2'"
    using update_mask_total_full_same_heap get_mask_total_full_wf
    by blast

  have HRel:"havoc_rel \<omega> ?\<omega>2"
    using \<open>\<omega>' \<in> _\<close> \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_backwards
    by blast

  have "red_inhale Pr \<Delta> False (Atomic (AccWildcard e_r f)) ?\<omega>2 (RNormal \<omega>2')"
    apply rule
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
    apply (unfold inhale_perm_single_def)
    apply rule
    apply (rule exI)+
    apply (intro conjI)
          apply (rule HOL.refl)
         apply simp
        apply simp
       apply simp
       apply (rule \<open>p \<noteq> pnone\<close>)
      apply (metis AddPerm fun_upd_same get_mask_total_full_wf get_update_mask_total_full wf_mask_simple_def)
     apply (metis AddPerm HRel \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_def)
    using \<open>get_heap_total_full (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = get_heap_total_full \<omega>2'\<close> apply auto
    done  
  then show ?case using HRel
    by simp
next
  case (InhInhaleExhale inh_assume A \<omega> res B)
  then show ?case 
    using red_inhale.InhInhaleExhale by blast
next
  case (InhPureNormalMagic e \<omega> b inh_assume)
  hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"      
    by (metis havoc_rel_same_mask stmt_result_total.distinct(3) stmt_result_total.inject update_mask_total_full_same) 
  from InhPureNormalMagic have HRel:"havoc_rel \<omega> \<omega>2'"
    by (metis stmt_result_total.distinct(3) stmt_result_total.inject)
  show ?case
    apply (rule conjI)
    apply (subst StateEq)
     apply (rule InhPureNormal)
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
     apply (rule havoc_rel_expr_eval_same[OF _ \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
    using \<open>Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> InhPureNormalMagic.prems(1) stmt_result_total.distinct(3)
    apply (simp split: if_split_asm)
    apply (subst StateEq, rule HRel)
    done
qed (auto)

method inh_fail_basic_tac for \<omega> :: "'a full_total_state" uses local_assms intro = 
  (rule exI[where ?x=\<omega>], 
   rule conjI[OF havoc_rel_refl],
   insert local_assms,
   blast intro!:intro)

lemma havoc_inhale_failure_rel:
  assumes "red_inhale Pr \<Delta> True A \<omega> res" and "res = RFailure"
  shows "\<exists> \<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_inhale Pr \<Delta> False A \<omega>2 RFailure"
  using assms
proof (induction)
  case (InhSepNormal A \<omega> \<omega>A B res)
  from this obtain \<omega>B where
     "havoc_rel \<omega>A \<omega>B" and "red_inhale Pr \<Delta> False B \<omega>B RFailure"
    by auto
  thus ?case
    using havoc_inhale_normal_rel InhSepNormal.hyps(1) red_inhale.InhSepNormal by blast
next
  case (InhSepFailureMagic A \<omega> resA B)
  then show ?case 
    using red_inhale.InhSepFailureMagic by blast
next
  case (InhImpTrue e \<omega> A res)
  then show ?case 
    by (meson InhImpFailure havoc_rel_expr_eval_same red_inhale.InhImpTrue)
next
  case (InhImpFailure e \<omega> A)
  then show ?case 
  by (meson havoc_rel_sym havoc_rel_wd_same red_inhale.InhImpFailure total_havoc_rel)
next
case (InhAssumeAccFail2 e_r \<omega> a e_p p f)
  show ?case 
    by (inh_fail_basic_tac \<omega> local_assms:local.InhAssumeAccFail2 intro: red_inhale.InhAssumeAccFail2)
next
  case (InhAssumeAccWildcardFail2 e_r \<omega> a e_p p f)
    show ?case 
     by (inh_fail_basic_tac \<omega> local_assms:local.InhAssumeAccWildcardFail2 intro: red_inhale.InhAssumeAccWildcardFail2)   
next
  case (InhInhaleExhale A \<omega> res B)
  then show ?case
  using red_inhale.InhInhaleExhale by blast
next
  case (InhPureNormalMagic e \<omega> b)
  then show ?case by (simp split: if_split_asm)
next
  case (InhPureFail e \<omega>)
  show ?case 
    by (inh_fail_basic_tac \<omega> local_assms:local.InhPureFail intro: red_inhale.InhPureFail)
qed auto

lemma havoc_rel_exhale_state:
  assumes "havoc_rel \<omega>1 \<omega>2" and "\<omega>1 \<in> exhale_state \<omega> m"
  shows "\<omega>2 \<in> exhale_state (update_trace_total \<omega> (get_trace_total \<omega>2)) m"
proof -
  from \<open>\<omega>1 \<in> exhale_state \<omega> m\<close>
  have EqMask:"get_mask_total_full \<omega>1 = m" and
       HavocLoc:"get_heap_total_full \<omega>1 \<in> havoc_undef_locs (get_heap_total_full \<omega>) m" 
    by (auto simp add: exhale_state_def)

  have "get_heap_total_full \<omega>2 \<in> havoc_undef_locs (get_heap_total_full \<omega>) m"
    unfolding havoc_undef_locs_def
    apply rule
    apply (rule exI)
    apply (rule conjI[OF HOL.refl])
    apply (rule allI, rule impI)
    apply (insert havoc_rel_eq_on_mask[OF assms(1)])
    apply (subst (asm) EqMask)
    apply (insert HavocLoc, unfold havoc_undef_locs_def)
    apply (unfold equal_on_mask_def)
    using prat_pgt_pnone by fastforce

  show ?thesis
    unfolding exhale_state_def
    apply rule
    apply (rule exI)
    apply (intro conjI)
        apply (rule HOL.refl)
       apply (metis assms(1) assms(2) exhale_state_same_store havoc_rel_same_store update_trace_total_store_same)
      apply simp
     apply (metis EqMask assms(1) havoc_rel_same_mask)
    using \<open>get_heap_total_full \<omega>2 \<in> havoc_undef_locs (get_heap_total_full \<omega>) m\<close> by auto
qed

lemma exp_rel_aux:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>1\<rangle> [\<Down>]\<^sub>t Val v"
  shows "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
  oops

definition exhale_rel_inv :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> mask \<Rightarrow> bool"
  where "exhale_rel_inv \<omega>1 \<omega>2 m \<equiv>            
           havoc_rel (update_mask_total_full \<omega>1 m) (update_mask_total_full \<omega>2 m) \<and>
           wf_mask_simple m"

lemma havoc_rel_red_exhale:
  assumes "red_exhale Pr \<Delta> \<omega>1 A m res" and 
          "havoc_rel \<omega>1 \<omega>2" and
          "exhale_rel_inv \<omega>1 \<omega>2 m"
  shows "red_exhale Pr \<Delta> \<omega>2 A m res \<and> (\<forall>m'. res = ExhaleNormal m' \<longrightarrow> exhale_rel_inv \<omega>1 \<omega>2 m')"
  using assms
proof induction
  case (ExhSepNormal A m m'' B res)
  then show ?case 
    using red_exhale.ExhSepNormal by blast
next
  case (ExhSepFailureMagic A m B)
  then show ?case
    using red_exhale.ExhSepFailureMagic by blast
next
  case (ExhImpTrue \<omega> m e A res)
  note HRel=\<open>havoc_rel \<omega>1 \<omega>2\<close>
  let ?\<omega>1' = "update_mask_total_full \<omega>1 m" and ?\<omega>2' = "(update_mask_total_full \<omega>2 m)"
  from ExhImpTrue have HRelNew:"havoc_rel ?\<omega>1' ?\<omega>2'"
    sledgehammer
  have Eval:"Pr, \<Delta> \<turnstile> \<langle>e; ?\<omega>2'\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using havoc_rel_expr_eval_same_exhale_3 \<open>\<omega> = _\<close> ExhImpTrue.IH ExhImpTrue.hyps(2) ExhImpTrue.hyps(3) HRel by blast
  have Wd:"wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>1)) e (update_mask_total_full \<omega>2 m)"
    using havoc_rel_wd_same_exhale_2 \<open>\<omega> = _\<close>
    by (metis ExhImpTrue.IH ExhImpTrue.hyps(2) HRel havoc_rel_valid_locs)

  show ?case
    apply (rule conjI)
     apply rule
        apply (rule HOL.refl)
    using Wd havoc_rel_valid_locs[OF HRel] apply simp
    apply (rule Eval)
    using ExhImpTrue.IH HRel by blast+    
next
  case (ExhImpFalse \<omega> m e A)
  thus ?case
next
  case (ExhImpFailure e \<omega>_orig m A)
  then show ?case oops
next
  case (ExhAcc \<omega> m e_r a e_p p f locs m')
  then show ?case oops
next
  case (ExhAccFail1 e_r \<omega> r e_p p locs f m)
  then show ?case oops
next
case (ExhAccFail2 \<omega> m e_r a e_p p locs f)
  then show ?case oops
next
  case (ExhAccWildcard \<omega> m e_r a p f locs m')
  then show ?case oops
next
  case (ExhAccWildcardFail1 e_r \<omega> r locs f m)
  then show ?case oops
next
  case (ExhAccWildcardFail2 \<omega> m e_r a locs f)
  then show ?case oops
next
  case (ExhInhaleExhale B m res A)
  then show ?case oops
next
  case (ExhPure \<omega> m locs e b)
  then show ?case oops
next
  case (ExhPureFail \<omega> m locs e)
  then show ?case oops
qed

lemma havoc_rel_red_exhale_2:
  assumes "red_exhale Pr \<Delta> \<omega>1 A m res" and "havoc_rel \<omega>1 \<omega>2"
  shows "red_exhale Pr \<Delta> \<omega>2 A m res"
  using assms havoc_rel_red_exhale
  by blast

lemma havoc_rel_store_update:
  assumes "havoc_rel (update_store_total \<omega> x v) \<omega>1"
  shows "\<exists>\<omega>2. \<omega>1 = update_store_total \<omega>2 x v"
  using assms
  unfolding havoc_rel_def
  by (metis Rep_total_state_inverse fstI fun_upd_same fun_upd_triv get_heap_total_full.simps get_hm_total_full_comp update_mask_total_def update_mask_total_full.simps update_mask_total_full_same update_store_total.elims)

lemma havoc_rel_store_update_3:
  assumes "havoc_rel (update_store_total \<omega> x v) \<omega>2'"
  shows "\<exists>\<omega>2. \<omega>2' = update_store_total \<omega>2 x v \<and> havoc_rel \<omega> \<omega>2"
proof -
  from assms obtain \<omega>2_first where "\<omega>2' = update_store_total \<omega>2_first x v" 
    using havoc_rel_store_update by blast
  hence *:"get_mask_total_full \<omega>2' = get_mask_total_full \<omega>2_first"
    by (simp add: update_store_total_mask_same)
  have **:"equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>2_first)"
    using assms \<open>\<omega>2' = _\<close> update_store_total_heap_same update_store_total_mask_same
    unfolding havoc_rel_def
    by fastforce
 
  let ?\<omega>2 = "(get_store_total \<omega>, get_trace_total \<omega>2_first, get_hm_total_full \<omega>2_first)"
  have "havoc_rel \<omega> ?\<omega>2"
    unfolding havoc_rel_def
    apply (intro conjI)
       using * assms havoc_rel_same_mask apply fastforce
     using ** apply simp
    apply simp
    done

  show ?thesis
    apply (rule exI[where ?x="?\<omega>2"])
    apply (rule conjI)
     apply (rule full_total_state_eq)
        using \<open>\<omega>2' = _\<close>
        apply (metis Pair_inject assms havoc_rel_same_store update_mask_total_full.simps update_mask_total_full_same update_store_total.simps)
       apply (simp add: \<open>\<omega>2' = _\<close>)
      apply (simp add: \<open>\<omega>2' = _\<close>)
     apply (metis \<open>havoc_rel \<omega> _\<close> assms havoc_rel_same_mask update_store_total_mask_same)
    using \<open>havoc_rel \<omega> _\<close> by auto
qed

lemma havoc_rel_heap_update:
  assumes "havoc_rel (update_heap_total_full \<omega> l v) \<omega>2'" and "get_mask_total_full \<omega> l \<noteq> pnone"
  shows "\<exists>\<omega>2. \<omega>2' = (update_heap_total_full \<omega>2 l v) \<and> havoc_rel \<omega> \<omega>2"
proof -
  let ?h ="get_heap_total_full \<omega>"
  let ?\<omega>2="update_heap_total_full \<omega>2' l (?h l)"

  from assms have HeapLoc:"get_heap_total_full \<omega>2' l = v"
    apply (unfold havoc_rel_def)
    apply (unfold equal_on_mask_def)
    by (metis update_heap_total_full_lookup_1 update_heap_total_full_mask_same)

  show ?thesis
    apply (rule exI[where ?x="?\<omega>2"])
    apply (rule conjI)
     apply (rule full_total_state_eq)
        apply simp
       apply simp
      apply (simp only: update_heap_total_overwrite_full)
      apply (rule HOL.ext)
      apply (case_tac "x = l")
       apply (simp only: update_heap_total_full_lookup_1)
       apply (rule HeapLoc)
      apply (rule HOL.sym[OF update_heap_total_full_lookup_2])
      apply simp
     apply (simp only: update_heap_total_full_mask_same)
    unfolding havoc_rel_def
    apply (intro conjI)
     apply (simp only: update_heap_total_full_mask_same)
      apply (metis assms(1) havoc_rel_same_mask update_heap_total_full_mask_same)
    apply (smt (z3) assms equal_on_mask_def havoc_rel_def update_heap_total_full_lookup_1 update_heap_total_full_lookup_2 update_heap_total_full_mask_same)
    by (metis assms(1) fstI get_store_total.simps havoc_rel_same_store update_heap_total_full.simps)
qed

method step_havoc_failure_tac uses W2'Eq IntroRule=
        (rule exI,
         rule conjI[OF havoc_rel_refl],
        subst W2'Eq,
        (rule, rule),
        (rule IntroRule))

lemma step_havoc_rel:
  assumes "red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=True\<rparr> (Inl s,  RNormal \<omega>) w'" and 
          "lift_sim_rel havoc_rel w' w2'"
  (*shows   "(is_failure_config w' \<longrightarrow> (\<exists>\<omega>2 w2'. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> m\<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) w2' \<and> is_failure_config w2')) \<and>
                (\<forall> s' \<omega>' \<omega>2'. is_normal_config w' \<omega>' \<longrightarrow> havoc_rel \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) (Inl s', RNormal \<omega>2')))"*)
  shows "\<exists>\<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) w2'"
  using assms
  proof (cases)
    case NormalSingleStep
    then show ?thesis using assms(2)
    proof (induction arbitrary: w2')
      case RedSkip
      then show ?case
       by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.elims(2) lift_sim_rel_def prod.exhaust_sel red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedSkip snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
    next
    case (RedInhale A \<omega> res)
    show ?case
    proof (cases res)
    case RMagic
    then show ?thesis 
      using assms(2) lift_sim_rel_not_magic
      by (metis RedInhale.prems snd_conv)
    next
      case RFailure
      with RedInhale have "w2' = (Inr (), RFailure)"
        unfolding lift_sim_rel_def
        using RedInhale.prems lift_sim_rel_fail_3 by blast
      with RFailure RedInhale NormalSingleStep assms(2) havoc_inhale_failure_rel
      show ?thesis
        by (metis conf.select_convs(1) red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedInhale)
    next
      case (RNormal \<omega>')
      with RedInhale obtain \<omega>2' where "w2' = (Inr (), RNormal \<omega>2')" and "havoc_rel \<omega>' \<omega>2'"
        unfolding lift_sim_rel_def      
        by (metis fst_conv is_failure_config.simps is_normal_config.elims(2) snd_conv stmt_result_total.distinct(5) stmt_result_total.inject surjective_pairing)
      with \<open>res = _\<close> RedInhale assms(2) havoc_inhale_normal_rel
      obtain \<omega>2 where "havoc_rel \<omega> \<omega>2" and "red_inhale Pr \<Delta> False A \<omega>2 (RNormal \<omega>2')"
        by (metis (full_types) conf.select_convs(1))
      then show ?thesis
        by (metis (full_types) \<open>w2' = (Inr (), RNormal \<omega>2')\<close> conf.select_convs(1) red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedInhale)
      qed
    next
      case (RedExhale \<omega> A m' \<omega>')   
      from this obtain \<omega>2' where "w2' = (Inr (), RNormal \<omega>2')" and "havoc_rel \<omega>' \<omega>2'"
        unfolding lift_sim_rel_def
        by (metis fst_conv is_failure_config.elims(2) is_normal_config.elims(2) prod.exhaust_sel snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
      have Eq:"\<And> \<pi>. get_mask_total_full (update_trace_total \<omega> \<pi>) = get_mask_total_full \<omega>"
        by simp
      show ?case
        apply (rule exI)
        apply (rule conjI[OF havoc_rel_traceupd])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)   
         apply (rule havoc_rel_red_exhale_2)
          apply (subst Eq)
          apply (rule \<open>red_exhale _ _ _ _ _ _\<close>)
          apply (rule havoc_rel_traceupd)
        apply (rule havoc_rel_exhale_state[OF \<open>havoc_rel \<omega>' \<omega>2'\<close> \<open>\<omega>' \<in> _\<close>])
        done        
    next
      case (RedExhaleFailure \<omega> A)
      from this have "w2' = (Inr (), RFailure)"
        using lift_sim_rel_fail_3 by blast
      show ?case
        by (step_havoc_failure_tac W2'Eq: \<open>w2' = _\<close> IntroRule: \<open>red_exhale _ _ _ _ _ _\<close>)      
    next
      case (RedAssert \<omega> A m')
      from this obtain \<omega>2 where "w2' = (Inr (), RNormal \<omega>2)" and HRel:"havoc_rel \<omega> \<omega>2"
        unfolding lift_sim_rel_def
        by (metis fst_conv is_failure_config.elims(2) is_normal_config.elims(2) prod.exhaust_sel snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
        apply (rule havoc_rel_red_exhale_2[OF _ HRel])
        using \<open>red_exhale _ _ _ _ _ _\<close> HRel
        unfolding havoc_rel_def
         apply simp
        done
    next
      case (RedAssertFailure \<omega> A)
        from this have "w2' = (Inr (), RFailure)"
        using lift_sim_rel_fail_3 by blast
      show ?case
        by (step_havoc_failure_tac W2'Eq: \<open>w2' = _\<close> IntroRule: \<open>red_exhale _ _ _ _ _ _\<close>)
    next
      case (RedLocalAssign e \<omega> v x)
      from assms(2) obtain \<omega>2' \<omega>2 where "w2' = (Inr (), RNormal \<omega>2')" and 
        "\<omega>2' = update_store_total \<omega>2 x v" and HRel:"havoc_rel \<omega> \<omega>2"
        using havoc_rel_store_update_3
        unfolding lift_sim_rel_def      
        by (metis RedLocalAssign.prems fst_conv is_normal_config.simps lift_sim_rel_normal snd_conv surjective_pairing)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>, subst \<open>\<omega>2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        done
    next
      case (RedLocalAssignFailure e \<omega> x)
      have "w2' = (Inr (), RFailure)" 
        using RedLocalAssignFailure.prems lift_sim_rel_fail_3 by blast
      show ?case
        by (step_havoc_failure_tac W2'Eq: \<open>w2' = _\<close> IntroRule: \<open>\<not>_\<close>)
    next
      case (RedFieldAssign e_r \<omega> e addr f v)
      from assms(2) havoc_rel_heap_update \<open>get_mask_total_full \<omega> (addr, f) \<noteq> pnone\<close> obtain \<omega>2 where
        HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inr (), RNormal (update_heap_total_full \<omega>2 (addr, f) v))"
        unfolding lift_sim_rel_def
        by (metis RedFieldAssign.prems fst_conv is_normal_config.simps lift_sim_rel_normal snd_conv surjective_pairing)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
            apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
          apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
          apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
         apply (metis \<open>get_mask_total_full \<omega> (addr, f) \<noteq> pnone\<close> HRel havoc_rel_same_mask)
        apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        done
    next
      case (RedFieldAssignFailure e_r \<omega> e f)
      hence "w2' = (Inr (), RFailure)"
        using lift_sim_rel_fail_3 by blast       
      show ?case
        by (step_havoc_failure_tac W2'Eq: \<open>w2' = _\<close> IntroRule: RedFieldAssignFailure(1))
    next
      case (RedIfTrue e_b \<omega> s1 s2)
      from this obtain \<omega>2 where HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inl s1, RNormal \<omega>2)"      
        by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.simps lift_sim_rel_def prod.exhaust_sel snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
      show ?case 
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        done
    next
      case (RedIfFalse e_b \<omega> s1 s2)
        from this obtain \<omega>2 where HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inl s2, RNormal \<omega>2)"      
        by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.simps lift_sim_rel_def prod.exhaust_sel snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        done
    next 
      case (RedIfFailure e_b s1 s2)
      hence "w2' = (Inr (), RFailure)"
        using assms(2) lift_sim_rel_fail_3 by blast
      show ?case
        by (step_havoc_failure_tac W2'Eq: \<open>w2' = _\<close> IntroRule: \<open>\<not>_\<close>)
    next
      case (RedSeq1 s1 \<omega> s'' r'' s2)      
      from \<open>lift_sim_rel _ _ w2'\<close> obtain r2' where "w2' = (Inl (Seq s'' s2), r2')"
        unfolding lift_sim_rel_def
        by (metis eq_fst_iff)
      from \<open>w2' = _\<close> \<open>lift_sim_rel _ _ w2'\<close> have Rel:"lift_sim_rel havoc_rel (Inl s'', r'') (Inl s'', r2')"
        unfolding lift_sim_rel_def
        by auto
      from RedSeq1.IH[OF Rel] show ?case 
        by (metis Inl_inject Pair_inject \<open>w2' = _\<close> red_stmt_total_single.NormalSingleStep red_stmt_total_single.cases red_stmt_total_single_set.RedSeq1)        
    next
      case (RedSeq2 s1 \<omega> r'' s2)      
      from \<open>lift_sim_rel _ _ w2'\<close> obtain r2' where "w2' = (Inl s2, r2')"
        unfolding lift_sim_rel_def
        by (metis fst_conv surjective_pairing)
      from \<open>w2' = _\<close> \<open>lift_sim_rel _ _ w2'\<close> have Rel:"lift_sim_rel havoc_rel (Inr (), r'') (Inr (), r2')"
        unfolding lift_sim_rel_def
        by auto
      from RedSeq2.IH[OF Rel] show ?case
        by (metis \<open>w2' = _\<close> prod.inject red_stmt_total_single.NormalSingleStep red_stmt_total_single.cases red_stmt_total_single_set.RedSeq2 sum.inject(1))         
    qed
qed

lemma verification_havoc:
  assumes "stmt_verifies_total (dummy :: 'a) Pr \<Delta> \<lparr>havoc_inhale = False\<rparr> s"
  shows "stmt_verifies_total (dummy :: 'a) Pr \<Delta> \<lparr>havoc_inhale = True\<rparr> s"
  apply (rule backwards_simulation)
     apply (erule init_havoc_rel)
     apply assumption
    apply (rule allI, rule total_havoc_rel)
   apply (erule step_havoc_rel)
   apply assumption
  apply (rule assms)
  done

end