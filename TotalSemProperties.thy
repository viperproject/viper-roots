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

lemma inhale_perm_single_Some_leq:
  assumes "\<omega>0 \<le> \<omega>1" and
          ConsistencyAntiMono: "\<And> \<omega> \<omega>'. \<omega> \<le> \<omega>' \<Longrightarrow> R \<omega>' \<Longrightarrow> R \<omega>" 
  shows "\<forall> \<omega>1' \<in> inhale_perm_single R \<omega>1 lh (Some p). \<exists>\<omega>0' \<le> \<omega>1'. \<omega>0' \<in> inhale_perm_single R \<omega>0 lh (Some p)"
proof 
  fix \<omega>1'
  assume "\<omega>1' \<in> inhale_perm_single R \<omega>1 lh (Some p)"
  hence "\<omega>1' = update_mh_loc_total_full \<omega>1 lh (padd (get_mh_total_full \<omega>1 lh) p)"
    using inhale_perm_single_nonempty
    by blast

  let ?\<omega>0' = "update_mh_loc_total_full \<omega>0 lh (padd (get_mh_total_full \<omega>0 lh) p)"

  have AtMostWrite: "pgte pwrite (padd (get_mh_total_full \<omega>1 lh) p)"
    using \<open>\<omega>1' \<in> _\<close>
    unfolding inhale_perm_single_def
    by simp
    

  from \<open>\<omega>0 \<le> \<omega>1\<close> have "(get_mh_total_full \<omega>0 lh) \<le> (get_mh_total_full \<omega>1 lh)"
    using less_eq_full_total_stateD_2 
    by (auto dest: le_funD)

  hence *: "(padd (get_mh_total_full \<omega>0 lh) p) \<le> (padd (get_mh_total_full \<omega>1 lh) p)"
    by (simp add: padd_mono)

  hence "?\<omega>0' \<le> \<omega>1'"
    using \<open>\<omega>1' = _\<close> assms update_mh_loc_total_full_mono 
    by blast

  moreover have "?\<omega>0' \<in> inhale_perm_single R \<omega>0 lh (Some p)"
    apply (rule inhale_perm_single_elem)
       apply (rule HOL.refl)
    using ConsistencyAntiMono \<open>\<omega>1' \<in> _\<close> \<open>?\<omega>0' \<le> \<omega>1'\<close>
    unfolding inhale_perm_single_def
      apply blast
     apply simp
    using AtMostWrite *
    by (metis (no_types, opaque_lifting) decompose_larger_than_one decompose_smaller_than_one linorder_less_linear not_pgte_charact order.strict_trans2 order_less_irrefl padd_pgte pgte_antisym)

  ultimately show "\<exists>\<omega>0'\<le>\<omega>1'. \<omega>0' \<in> inhale_perm_single R \<omega>0 lh (Some p)"
    using inhale_perm_single_nonempty
    by blast
qed  

lemma inhale_no_perm_failure_preserve_mono:
  assumes ConsistencyAntiMono: "\<And> \<omega> \<omega>'. \<omega> \<le> \<omega>' \<Longrightarrow> R \<omega>' \<Longrightarrow> R \<omega>"
  shows "ctxt, R, \<omega>_def1 \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow> 
        \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
        \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
        (if resE = VFailure then ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure
         else ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure \<or>
              ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE)" and
        "red_pure_exps_total ctxt R \<omega>_def1 es \<omega>1 resES \<Longrightarrow> 
         \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
         \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
         (if resES = None then red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 None
          else red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 None \<or>
               red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 resES)" and
        \<comment>\<open>TODO: add no permission introspection property\<close>
        "red_inhale ctxt R A \<omega>1 res1 \<Longrightarrow> \<omega>2 \<le> \<omega>1 \<Longrightarrow> res1 \<noteq> RMagic \<Longrightarrow> 
              (res1 = RFailure \<longrightarrow> red_inhale ctxt R A \<omega>2 RFailure) \<and>
              (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                    (red_inhale ctxt R A \<omega>2 RFailure \<or> 
                           (\<exists>\<omega>2'. \<omega>2' \<le> \<omega>1' \<and> 
                           red_inhale ctxt R A \<omega>2 (RNormal \<omega>2'))
                    )
              )" and
        "unfold_rel ctxt R x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction arbitrary: \<omega>2 \<omega>_def2 and \<omega>2 \<omega>_def2 and \<omega>2 rule: red_exp_inhale_unfold_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case sorry
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case sorry
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case sorry
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case sorry
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case sorry
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case sorry
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case sorry
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case sorry
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case sorry
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case sorry
next
  case (RedOld \<omega> l \<phi> \<omega>_def e v)
  then show ?case sorry
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case sorry
next
  case (RedField \<omega>_def e \<omega> a f v)
  then show ?case sorry
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case sorry
next
  case (RedFunApp fname f \<omega>_def es \<omega> vs res)
  then show ?case sorry
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case sorry
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case sorry
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case sorry
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case sorry
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case sorry
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case sorry
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case sorry
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case sorry
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case sorry
next
  case (InhAcc \<omega> e_r r e_p p W' f res)
  hence Leq: "Some \<omega>2 \<le> Some \<omega>"
    by simp
  with InhAcc consider (RefFail) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                       (RefSuccess) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by meson
  thus ?case
  proof cases
    case RefFail
    have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 RFailure"
      apply (rule InhSubAtomicFailure)
      using RefFail
      by (auto intro!: red_exp_inhale_unfold_intros)      
    thus ?thesis 
      by simp
  next
    case RefSuccess
      from Leq InhAcc consider (PermFail) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                               (PermSuccess) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
        by metis
      then show ?thesis 
      proof cases
        case PermFail
           have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 RFailure"
             apply (rule InhSubAtomicFailure)
             apply simp+
             apply (rule RedExpListCons)
             by (auto intro!: RefSuccess RedExpListCons PermFail RedExpListFailure)                      
           then show ?thesis 
             by simp
      next
        case PermSuccess
        then show ?thesis 
        proof (cases "res = RFailure")
          case True
          have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 RFailure"
            apply (rule red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.InhAcc)
               apply (rule RefSuccess)
              apply (rule PermSuccess)
             apply blast
            using True InhAcc.hyps THResultFailure th_result_rel_failure_2 by fastforce
          thus ?thesis
            by simp            
        next
          case False
          with InhAcc.hyps obtain \<omega>' where "res = RNormal \<omega>'" and "\<omega>' \<in> W'"
            by (metis InhAcc.prems(2) th_result_rel.cases)
          
          show ?thesis 
          proof (cases "r = Null")
            case True
            have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal \<omega>2)"
              apply (rule red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.InhAcc)
              apply (rule RefSuccess)
                apply (rule PermSuccess)
               apply simp
              apply (simp add: \<open>r = Null\<close>)
              using InhAcc.hyps THResultNormal_alt True \<open>res = RNormal \<omega>'\<close> th_result_rel_normal by fastforce
            thus ?thesis
              using \<open>res = _\<close> \<open>\<omega>2 \<le> _\<close> InhAcc.IH True \<open>\<omega>' \<in> W'\<close>
              by fastforce              
          next
            case False
            hence "\<omega>' \<in> inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_prat p))"
              using InhAcc \<open>\<omega>' \<in> W'\<close>
              by presburger
            from this obtain \<omega>'' where "\<omega>'' \<le> \<omega>'" and "\<omega>'' \<in> inhale_perm_single R \<omega>2 (the_address r, f) (Some (Abs_prat p))"
              using \<open>\<omega>2 \<le> \<omega>\<close>  inhale_perm_single_Some_leq ConsistencyAntiMono
              by blast
            have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal \<omega>'')"
              apply (rule red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.InhAcc)
              apply (rule RefSuccess)
                apply (rule PermSuccess)
               apply simp
              apply (simp add: False)
              using \<open>\<omega>'' \<in> _\<close>
              by (metis (full_types) InhAcc.hyps THResultNormal_alt \<open>res = RNormal \<omega>'\<close> emptyE th_result_rel_normal)            
            then show ?thesis 
              using \<open>\<omega>'' \<le> \<omega>'\<close> \<open>res = _\<close>              
              by blast
          qed
        qed
      qed
    qed  
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
  hence "Some \<omega>2 \<le> Some \<omega>"
    by simp
  from this consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    using InhPure
    by meson
  thus ?case 
  proof cases
    case 1
    have "red_inhale ctxt R (Atomic (Pure e)) \<omega>2 RFailure"
      apply (rule InhSubAtomicFailure)
      using 1
      by (auto intro!: red_exp_inhale_unfold_intros)
    thus ?thesis
      by simp          
  next
    case 2
    then show ?thesis 
      using InhPure.prems(1) red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.InhPure by force
  qed   
next
  case (InhSubAtomicFailure A \<omega>)
  hence "Some \<omega>2 \<le> Some \<omega>"
    by simp
  then show ?case 
    using InhSubAtomicFailure red_inhale_intros
    by meson
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  hence *: "red_inhale ctxt R A \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>''. red_inhale ctxt R A \<omega>2 (RNormal \<omega>2'))" (is "?FailA \<or> ?SuccessA")
    by blast

  show ?case
  proof (rule conjI, rule impI)
    assume "res = RFailure"
    thus "red_inhale ctxt R (A && B) \<omega>2 RFailure"
      using InhStarNormal 
      by (blast intro: red_inhale_intros)
  next
    show "\<forall>\<omega>1'. res = RNormal \<omega>1' \<longrightarrow>
           red_inhale ctxt R (A && B) \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>1'. red_inhale ctxt R (A && B) \<omega>2 (RNormal \<omega>2'))"
      using * InhStarNormal
      by (blast intro: red_inhale_intros)
  qed
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case 
    by (blast intro: red_inhale_intros)        
next
  case (InhImpTrue \<omega> e A res)
  hence "Some \<omega>2 \<le> Some \<omega>"
    by simp
  from this consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using InhImpTrue
    by meson    
  thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (blast intro!: red_inhale_intros)
  next
    case 2
    then show ?thesis 
      using InhImpTrue red_inhale_intros
      by metis      
  qed  
next
  case (InhImpFalse \<omega> e A)
    hence "Some \<omega>2 \<le> Some \<omega>"
    by simp
  from this consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using InhImpFalse
    by meson
  thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (blast intro!: red_inhale_intros)
  next
    case 2
    thus ?thesis
      using InhImpFalse 
      by (blast intro!: red_inhale_intros)
  qed  
next
  case (InhImpFailure \<omega> e A)
  hence "Some \<omega>2 \<le> Some \<omega>"
    by simp
  hence "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure"
    using InhImpFailure
    by simp
  thus ?case
    by (blast intro!: red_inhale_intros)      
qed (rule HOL.TrueI)+

subsection \<open>Exhale\<close>

lemma exhale_only_changes_total_state_aux:
  assumes
         "red_exhale ctxt R A \<omega>def \<omega> res" and "res = RNormal \<omega>'"
  shows  "get_store_total \<omega>' = get_store_total \<omega> \<and>
          get_trace_total \<omega>' = get_trace_total \<omega> \<and>
          get_h_total_full \<omega>' = get_h_total_full \<omega>"
  using assms
proof (induction arbitrary: \<omega>')
  case (ExhAcc mh \<omega> e_r r e_p p a f)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhAccWildcard mh \<omega> e_r r q a f)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhAccPred mp \<omega> e_args v_args e_p p pred_id r)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhAccPredWildcard mp \<omega> e_args v_args q a f pred_id)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhPure e \<omega> b)
  then show ?case 
    by (auto elim: exh_if_total.elims)
next
  case (SubAtomicFailure A \<omega>)
  then show ?case by fastforce
next
  case (ExhStarNormal A \<omega> \<omega>' B res)
  then show ?case by presburger
next
  case (ExhStarFailure A \<omega> B)
  then show ?case by blast
next
  case (ExhImpTrue e \<omega> A res)
  then show ?case by blast
next
  case (ExhImpFalse e \<omega> A)
  then show ?case by fastforce
next
  case (ExhImpFailure e \<omega> A)
  then show ?case by fast
qed

lemma exhale_only_changes_total_state:
  assumes "red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
  shows "get_store_total \<omega> = get_store_total \<omega>' \<and>
         get_trace_total \<omega> = get_trace_total \<omega>'"
  using assms
proof cases
  case (RedExhale \<omega>_exh)
  then show ?thesis 
    using exhale_only_changes_total_state_aux
    unfolding exhale_state_def
    by (metis exhale_state_same_store exhale_state_same_trace \<open>\<omega>' \<in> _\<close>)
qed

subsection \<open>Relationship inhale and exhale\<close>

lemma exhale_normal_result_smaller:
  assumes "red_exhale ctxt StateCons \<omega>def A \<omega> (RNormal \<omega>')"
  shows "\<omega> \<succeq> \<omega>'"
  sorry

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