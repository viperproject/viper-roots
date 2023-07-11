theory TotalSemProperties
imports TotalSemantics
begin

subsection \<open>Auxiliary lemmas\<close>

lemma pure_exp_pred_subexp:
  assumes "pure_exp_pred p e"
  shows "list_all (pure_exp_pred p) (sub_pure_exp_total e)"
  using assms
  by (cases e) simp_all

lemma atomic_assert_subexp:
  assumes "atomic_assert_pred p_atm p_e atm"
  shows "list_all (pure_exp_pred p_e) (sub_expressions_atomic atm)"
  using assms
  apply (cases atm)
    apply simp_all  
  apply (metis atomic_assert_pred_rec.simps(2) atomic_assert_pred_rec.simps(3) list.pred_inject(1) list.pred_inject(2) pure_exp_pred.simps sub_expressions_exp_or_wildcard.cases sub_expressions_exp_or_wildcard.simps(1) sub_expressions_exp_or_wildcard.simps(2))
  by (metis atomic_assert_pred_rec.simps(4) atomic_assert_pred_rec.simps(5) list.pred_inject(1) list.pred_inject(2) sub_expressions_exp_or_wildcard.cases sub_expressions_exp_or_wildcard.simps(1) sub_expressions_exp_or_wildcard.simps(2))

subsection \<open>Expression evaluation\<close>

lemma red_exp_unop_sub_failure:
  assumes "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>Unop uop e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (auto intro: red_exp_inhale_unfold_intros)

lemma red_exp_binop_sub_left_failure:
  assumes "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (auto intro: red_exp_inhale_unfold_intros)

lemma red_exp_field_sub_failure:
  assumes "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (auto intro: red_exp_inhale_unfold_intros)

lemma red_exp_condexp_sub_failure:
  assumes "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>cond; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>CondExp cond thn els; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (auto intro: red_exp_inhale_unfold_intros)

subsubsection \<open>Main lemmas\<close>

\<comment>\<open>The generalization of the following lemma to function calls will require a condition on the function interpretation,
   which states how the well-definedness of functions is affected when adjusting the well-definedness state.\<close>

lemma red_pure_exp_different_def_state:
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow>
           res = Val v \<Longrightarrow>
           no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
           ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<or> ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" and
          "red_pure_exps_total ctxt StateCons \<omega>def_opt es \<omega> resES \<Longrightarrow>
           resES = Some vs \<Longrightarrow>
           list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
           red_pure_exps_total ctxt StateCons \<omega>def_opt' es \<omega> (Some vs) \<or> red_pure_exps_total ctxt StateCons \<omega>def_opt' es \<omega> None" and
          "red_inhale ctxt StateCons A \<omega>1 res1 \<Longrightarrow> True" and
          "unfold_rel ctxt StateCons x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction arbitrary: v \<omega>def_opt' and vs \<omega>def_opt' rule: red_exp_inhale_unfold_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  from this consider (Normal) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" | 
                     (Failure) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case 
  proof cases
    case Normal
    then show ?thesis 
      using RedBinopLazy
      by (auto intro: red_exp_inhale_unfold_intros)
  next
    case Failure  
    have "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      apply (rule RedSubFailure)
      by (auto intro: red_exp_inhale_unfold_intros Failure)      
    thus ?thesis 
      by simp
  qed    
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v3)
  from this consider (NormalE1) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" |
                     (FailureE1) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by fastforce
  then show ?case 
  proof cases
    case NormalE1   
    from RedBinop consider (NormalE2) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" |
                           (FailureE2) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
      by auto
    then show ?thesis 
    proof (cases)
      case NormalE2
      then show ?thesis 
        using RedBinop NormalE1
        by (auto intro: red_exp_inhale_unfold_intros)
    next
      case FailureE2
      have "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        apply (rule RedBinopRightFailure)
           apply (rule NormalE1)
          apply (rule FailureE2)
        using RedBinop
         apply blast
        using \<open>eval_binop v1 bop v2 = BinopNormal v3\<close>        
        by (metis binop_result.disc(1) binop_result.discI)
      thus ?thesis
        by simp
    qed      
  next
    case FailureE1
    then show ?thesis 
      by (blast intro: red_exp_binop_sub_left_failure)      
  qed
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnop \<omega>_def e \<omega> v1 unop v2)
  from this consider (Normal) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" |
                     (Failure) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by fastforce
  thus ?case
  proof cases
    case Normal
    with RedUnop show ?thesis 
    by (auto intro: red_exp_inhale_unfold_intros)      
  next
    case Failure
    then show ?thesis 
      by (auto intro: red_exp_unop_sub_failure)
  qed
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case 
    using red_exp_condexp_sub_failure TotalExpressions.RedCondExpTrue
    by fastforce
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case 
    using red_exp_condexp_sub_failure TotalExpressions.RedCondExpFalse
    by fastforce
next
  case (RedOld \<omega> l \<phi> \<omega>_def e v)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedField \<omega>_def e \<omega> a f v1)
  from this consider (NormalRef) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
                   | (FailRef) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case
  proof cases
    case NormalRef
    show ?thesis
     using NormalRef RedField TotalExpressions.RedField
     by (fastforce split: if_split if_split_asm)
  next
    case FailRef
    then show ?thesis 
      by (blast intro: red_exp_field_sub_failure)
  qed
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  from this consider (NormalHd) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v" |
                     (FailHd) "ctxt, StateCons, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case 
  proof cases
    case NormalHd
    from RedExpListCons obtain vs' where "vs = v#vs'" and "res = Some vs'"
      by blast
   
    with RedExpListCons consider
        (NormalTl) "red_pure_exps_total ctxt StateCons \<omega>def_opt' es \<omega> (Some vs')"
      | (FailTl) "red_pure_exps_total ctxt StateCons \<omega>def_opt' es \<omega> None"
      by auto

    then show ?thesis
    proof cases
      case NormalTl
      then show ?thesis 
        using NormalHd \<open>vs = _\<close>
        by (auto intro: red_exp_inhale_unfold_intros)
    next
      case FailTl
      then show ?thesis 
      using NormalHd
      by (auto intro: red_exp_inhale_unfold_intros)
    qed
  next
    case FailHd
    then show ?thesis 
      by (auto intro: red_exp_inhale_unfold_intros)      
  qed
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
qed (rule HOL.TrueI)+

\<comment>\<open>The generalization of the following lemma to function calls will require a restriction on the function interpretation,
   which states that the mask has no effect on function values.\<close>

lemma red_pure_exp_only_differ_on_mask:
  shows "ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow>
         no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
         get_store_total \<omega> = get_store_total \<omega>' \<and> 
         get_trace_total \<omega> = get_trace_total \<omega>' \<and>
         get_h_total_full \<omega> = get_h_total_full \<omega>' \<Longrightarrow>
         ctxt, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t resE" and
        "red_pure_exps_total ctxt StateCons \<omega>def_opt es \<omega> resES \<Longrightarrow>
                 list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
                 get_store_total \<omega> = get_store_total \<omega>' \<and> 
                 get_trace_total \<omega> = get_trace_total \<omega>' \<and>
                 get_h_total_full \<omega> = get_h_total_full \<omega>' \<Longrightarrow>
                 red_pure_exps_total ctxt StateCons \<omega>def_opt es \<omega>' resES" and
        "red_inhale ctxt StateCons A \<omega>1 res1 \<Longrightarrow> True" and
        "unfold_rel ctxt StateCons x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction arbitrary: \<omega>' and \<omega>' rule: red_exp_inhale_unfold_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedOld \<omega> l \<phi> \<omega>_def e v)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedField \<omega>_def e \<omega> a f v)
  hence "get_hh_total_full \<omega>' (a,f) = v"
    by simp

  moreover from RedField have "ctxt, StateCons, \<omega>_def \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by simp

  ultimately show ?case 
    by (fastforce intro: TotalExpressions.RedField)
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  from \<open>no_perm_pure_exp e' \<and> no_unfolding_pure_exp e'\<close> have
     "list_all (\<lambda>e. no_perm_pure_exp e) (sub_pure_exp_total e')" and
     "list_all (\<lambda>e. no_unfolding_pure_exp e) (sub_pure_exp_total e')"
    using pure_exp_pred_subexp
    by blast+
  hence "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (sub_pure_exp_total e')"
    by (simp add: list_all_length)    
  with RedSubFailure show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)    
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
  by (auto intro: red_exp_inhale_unfold_intros)
qed (rule HOL.TrueI)+

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
  assumes ConsistencyDownwardMono: "\<And> \<omega> \<omega>'. \<omega> \<le> \<omega>' \<Longrightarrow> R \<omega>' \<Longrightarrow> R \<omega>"
  shows "ctxt, R, \<omega>_def1 \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow> 
        no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
        \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
        \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
        (if resE = VFailure then ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure
         else ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure \<or>
              ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE)" and
        "red_pure_exps_total ctxt R \<omega>_def1 es \<omega>1 resES \<Longrightarrow> 
         list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
         \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
         \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
         (if resES = None then red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 None
          else red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 None \<or>
               red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 resES)" and
        \<comment>\<open>TODO: add no permission introspection property\<close>
        "red_inhale ctxt R A \<omega>1 res1 \<Longrightarrow> 
              no_perm_assertion A \<and> no_unfolding_assertion A \<Longrightarrow>
              \<omega>2 \<le> \<omega>1 \<Longrightarrow> res1 \<noteq> RMagic \<Longrightarrow> 
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
  moreover from this have Leq: "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhAcc have SubExpConstraint: "no_perm_pure_exp e_r \<and> no_unfolding_pure_exp e_r \<and> no_perm_pure_exp e_p \<and> no_unfolding_pure_exp e_p"
    by simp
  ultimately consider (RefFail) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
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
      from Leq SubExpConstraint InhAcc consider (PermFail) "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
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
            by (metis InhAcc.prems(3) th_result_rel.cases)
          
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
              using \<open>\<omega>2 \<le> \<omega>\<close>  inhale_perm_single_Some_leq ConsistencyDownwardMono
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
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhPure have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
    by simp
  ultimately consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
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
      using InhPure.prems(2) red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.InhPure
      by force
  qed   
next
  case (InhSubAtomicFailure A \<omega>)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhSubAtomicFailure have "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (sub_expressions_atomic A)"
    sorry
  ultimately show ?case 
    using InhSubAtomicFailure red_inhale_intros
    by meson
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  moreover from this have SubAssertionConstraint: "no_perm_assertion A \<and> no_unfolding_assertion A \<and> no_perm_assertion B \<and> no_unfolding_assertion B"
    by simp
  ultimately have *: "red_inhale ctxt R A \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>''. red_inhale ctxt R A \<omega>2 (RNormal \<omega>2'))" (is "?FailA \<or> ?SuccessA")
    by blast

  show ?case
  proof (rule conjI, rule impI)
    assume "res = RFailure"
    thus "red_inhale ctxt R (A && B) \<omega>2 RFailure"
      using InhStarNormal SubAssertionConstraint
      by (auto intro: red_inhale_intros)
  next
    show "\<forall>\<omega>1'. res = RNormal \<omega>1' \<longrightarrow>
           red_inhale ctxt R (A && B) \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>1'. red_inhale ctxt R (A && B) \<omega>2 (RNormal \<omega>2'))"
      using * InhStarNormal SubAssertionConstraint
      by (blast intro: red_inhale_intros)
  qed
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case 
    by (auto intro: red_inhale_intros)        
next
  case (InhImpTrue \<omega> e A res)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhImpTrue have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_perm_assertion A \<and> no_unfolding_assertion A"
    by simp
  ultimately consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by metis
  thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (blast intro!: red_inhale_intros)
  next
    case 2
    then show ?thesis 
      using InhImpTrue red_inhale_intros SubConstraint
      by metis
  qed  
next
  case (InhImpFalse \<omega> e A)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhImpFalse have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
    by simp
  ultimately consider "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
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

lemma exhale_normal_result_smaller:
  assumes "red_exhale ctxt StateCons \<omega>def A \<omega> res" and
          "res = RNormal \<omega>'"
        shows "\<omega> \<succeq> \<omega>'"
  using assms
proof (induction arbitrary: \<omega>')
  case (ExhAcc mh \<omega> e_r r e_p p a f)
  then show ?case sorry
next
  case (ExhAccWildcard mh \<omega> e_r r q a f)
  then show ?case sorry
next
  case (ExhAccPred mp \<omega> e_args v_args e_p p pred_id r)
  then show ?case sorry
next
  case (ExhAccPredWildcard mp \<omega> e_args v_args q a f pred_id)
  then show ?case sorry
next
  case (ExhPure e \<omega> b)
  then show ?case sorry
next
  case (SubAtomicFailure A \<omega>)
  then show ?case sorry
next
  case (ExhStarNormal A \<omega> \<omega>' B res)
  then show ?case sorry
next
  case (ExhStarFailure A \<omega> B)
  then show ?case sorry
next
  case (ExhImpTrue e \<omega> A res)
  then show ?case sorry
next
  case (ExhImpFalse e \<omega> A)
  then show ?case sorry
next
  case (ExhImpFailure e \<omega> A)
  then show ?case sorry
qed

subsection \<open>Relationship inhale and exhale\<close>
  
lemma exhale_inhale_normal:
  assumes RedExh: "red_exhale ctxt StateCons \<omega>def A \<omega> res" 
      and "res = RNormal \<omega>'"
      and "mono_prop_downward StateCons"
      and "no_perm_assertion A \<and> no_unfolding_assertion A"
      and "assertion_framing_state ctxt StateCons A \<omega>_inh"
      and "\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'"
      and ValidInh':"StateCons \<omega>_inh' \<and> valid_heap_mask (get_mh_total_full \<omega>_inh')"
    shows "red_inhale ctxt StateCons A \<omega>_inh (RNormal \<omega>_inh')"
  using assms exhale_normal_result_smaller[OF RedExh[simplified \<open>res = _\<close>], OF HOL.refl]
proof (induction arbitrary: \<omega>_inh \<omega>_inh' \<omega>')
  case (ExhAcc mh \<omega> e_r r e_p p a f)
  let ?A = "(Acc e_r f (PureExp e_p))"
  note AssertionFramed = \<open>assertion_framing_state ctxt StateCons (Atomic (Acc e_r f (PureExp e_p))) \<omega>_inh\<close>

  have SubExp: "sub_expressions_atomic ?A = [e_r, e_p]"
    by simp

  from \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close> and \<open>\<omega> \<succeq> \<omega>'\<close> have 
    OnlyMaskChanged:
    "get_store_total \<omega>_inh = get_store_total \<omega> \<and>
     get_trace_total \<omega>_inh = get_trace_total \<omega> \<and>
     get_h_total_full \<omega>_inh = get_h_total_full \<omega>"
    by (metis full_total_state_greater_only_mask_changed greater_def greater_equiv minus_smaller)


  have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_r;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VRef r)" (is ?RedRefInh)
  proof (rule ccontr)
    from OnlyMaskChanged ExhAcc have
       RedRefAux: "ctxt, StateCons, Some \<omega>def \<turnstile> \<langle>e_r;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    using red_pure_exp_only_differ_on_mask
    by fastforce

    assume "\<not>?RedRefInh"
    moreover have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_r;\<omega>_inh\<rangle> [\<Down>]\<^sub>t (Val (VRef r)) \<or>
          ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_r;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
      using red_pure_exp_different_def_state(1)[OF RedRefAux] ExhAcc
      by simp
    ultimately show False
      using AssertionFramed SubExp
      unfolding assertion_framing_state_def
      by (metis InhSubAtomicFailure RedExpListFailure list.distinct(1))
  qed

  have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_p;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" (is ?RedPermInh)
  proof (rule ccontr)
    from OnlyMaskChanged ExhAcc have
       Aux: "ctxt, StateCons, Some \<omega>def \<turnstile> \<langle>e_p;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using red_pure_exp_only_differ_on_mask
    by fastforce

    assume "\<not>?RedPermInh"
    moreover have *: "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_p;\<omega>_inh\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<or>
          ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_p;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
      using red_pure_exp_different_def_state(1)[OF Aux] ExhAcc
      by simp

    moreover have "red_inhale ctxt StateCons (Atomic ?A) \<omega>_inh RFailure"
    proof -
      from * \<open>\<not>?RedPermInh\<close> have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e_p;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
        by blast

      thus ?thesis
        using \<open>?RedRefInh\<close> InhSubAtomicFailure TotalExpressions.RedExpListCons RedExpListFailure
        by (metis None_eq_map_option_iff SubExp neq_Nil_conv)
    qed

    ultimately show False
      using AssertionFramed 
      unfolding assertion_framing_state_def
      by blast
  qed
      
  show ?case
  proof (cases "r = Null")
    case True
    hence "\<omega> = \<omega>'"
      using ExhAcc(5)
      by (simp add: exh_if_total_normal_2)

    have "\<omega>_inh' = \<omega>_inh"
      using \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>[simplified \<open>\<omega> = \<omega>'\<close>]
            full_total_state_defined_core_same_2 plus_minus_empty
      by (metis option.sel)

    show ?thesis
      apply (rule InhAcc[OF \<open>?RedRefInh\<close> \<open>?RedPermInh\<close>])
       apply simp
      using \<open>\<omega>_inh' = \<omega>_inh\<close> \<open>r = Null\<close> ExhAcc.prems(1) THResultNormal \<open>\<omega> = \<omega>'\<close> exh_if_total_normal 
      by fastforce
  next
    case False
    from this obtain a where "r = Address a"
      using ref.exhaust by blast    

    hence PermConditions: "0 \<le> p \<and> pgte (mh (a, f)) (Abs_prat p)"
      using ExhAcc.hyps(4) ExhAcc.prems(1) exh_if_total_normal by fastforce

    from \<open>r = Address a\<close> have "\<omega>' = update_mh_loc_total_full \<omega> (a, f) (mh (a, f) - Abs_prat p)"
      using ExhAcc.hyps(4) ExhAcc.prems(1) exh_if_total_normal_2 by auto

    let ?m\<Delta> = "\<lambda>loc. if loc = (a,f) then (Abs_prat p) else pnone"

    let ?p' = "(padd (get_mh_total_full \<omega>_inh (a,f)) (Abs_prat p))"
    have "\<omega>_inh' = update_mh_loc_total_full \<omega>_inh (a,f) ?p'" (is "_ = ?upd_\<omega>_inh")        

    proof -
      from \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>
      have "\<omega>_inh' = update_m_total_full \<omega>_inh (add_masks (get_mh_total_full \<omega>_inh) (get_mh_total_full (\<omega> \<ominus> \<omega>')))
                                               (add_masks (get_mp_total_full \<omega>_inh) (get_mp_total_full (\<omega> \<ominus> \<omega>')))"
        using plus_Some_full_total_state_eq
        by blast
      moreover have "(add_masks (get_mp_total_full \<omega>_inh) (get_mp_total_full (\<omega> \<ominus> \<omega>'))) = (get_mp_total_full \<omega>_inh)"
      proof -
        have "get_mp_total_full (\<omega> \<ominus> \<omega>') = zero_mask"
          apply (simp only: minus_full_total_state_mask[OF \<open>\<omega> \<succeq> \<omega>'\<close>])
          by (simp add: \<open>\<omega>' = _\<close> minus_masks_empty)

        thus ?thesis
          by (simp add: add_masks_zero_mask)
      qed
      moreover have "add_masks (get_mh_total_full \<omega>_inh) (get_mh_total_full (\<omega> \<ominus> \<omega>')) =  
                               (get_mh_total_full \<omega>_inh)( (a,f) := ?p')" (is "?lhs = ?rhs")
      proof -
        have *: "get_mh_total_full (\<omega> \<ominus> \<omega>') = get_mh_total_full \<omega> - (get_mh_total_full \<omega>)( (a,f) := (get_mh_total_full \<omega> (a, f) - Abs_prat p))"
          apply (simp only: minus_full_total_state_mask[OF \<open>\<omega> \<succeq> \<omega>'\<close> ])
          by (simp add: \<open>\<omega>' =_\<close> \<open>mh = _\<close>)

        show ?thesis
          unfolding add_masks_def
        proof (subst *, standard)
          fix hl
          let ?mh_inh = "get_mh_total_full \<omega>_inh"
          let ?mh = "get_mh_total_full \<omega>"

          show "padd (?mh_inh hl) ((?mh - ?mh((a, f) := ?mh (a, f) - Abs_prat p)) hl) =
                     (?mh_inh((a, f) := padd (?mh_inh (a, f)) (Abs_prat p))) hl"
          proof (cases "hl = (a,f)")
            case True
            then show ?thesis 
              using PermConditions[simplified \<open>mh = _\<close>, THEN HOL.conjunct2, THEN minus_prat_gte]
              by simp
          next
            case False
            then show ?thesis
              using zero_prat_def
              by (simp add: minus_prat_def)
          qed
        qed
      qed

      ultimately show ?thesis
        by simp
    qed        

    hence "get_mh_total_full \<omega>_inh' (a,f) = (padd (get_mh_total_full \<omega>_inh (a,f)) (Abs_prat p))"
      by simp

    hence PermConstraint': "pgte pwrite (padd (get_mh_total_full \<omega>_inh (a, f)) (Abs_prat p))"
      using ExhAcc.prems(6)
      unfolding valid_heap_mask_def
      by metis
      
    let ?W = "inhale_perm_single StateCons \<omega>_inh (a, f) (Some (Abs_prat p))"

    have "\<omega>_inh' \<in> ?W"
      unfolding inhale_perm_single_def
      apply (rule Set.CollectI)
      apply (rule exI)+
      apply (intro conjI)
          apply simp
      using ExhAcc
         apply blast
        apply simp
       apply (rule PermConstraint')
      apply (simp add: \<open>\<omega>_inh' = _\<close>)
      done
      
      show ?thesis        
       apply (rule InhAcc[OF \<open>?RedRefInh\<close> \<open>?RedPermInh\<close>])
       apply simp
      using PermConditions \<open>\<omega>_inh' \<in> ?W\<close>
      by (smt (verit) False Set.set_insert THResultNormal \<open>r = Address a\<close> insert_not_empty ref.sel)
  qed
next
  case (ExhAccWildcard mh \<omega> e_r r q a f)
  then show ?case sorry
next
  case (ExhAccPred mp \<omega> e_args v_args e_p p pred_id r)
  then show ?case sorry
next
  case (ExhAccPredWildcard mp \<omega> e_args v_args q a f pred_id)
  then show ?case sorry
next
  case (ExhPure e \<omega> b)
  hence "b = True"
    using exh_if_total_normal exh_if_total_normal_2 by blast

  from ExhPure have "\<omega>' = \<omega>"
    by (auto elim: exh_if_total.elims)
  hence "\<omega>_inh' = \<omega>_inh"
    using \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>
    by (metis full_total_state_defined_core_same_2 option.inject plus_minus_empty)

  note OnlyMaskChanged = minus_full_total_state_only_mask_different_2[OF \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>]
  with ExhPure have RedAux: "ctxt, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool True)"    
    using red_pure_exp_only_differ_on_mask
    unfolding \<open>b = True\<close>
    by fastforce

  have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
  proof -
    have "\<not> ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
      using \<open>assertion_framing_state ctxt StateCons (Atomic (Pure e)) \<omega>_inh\<close>
      unfolding assertion_framing_state_def
      by (metis (no_types, opaque_lifting) InhSubAtomicFailure RedExpListFailure not_None_eq red_exp_list_failure_Nil sub_expressions_atomic.simps(1))

    thus ?thesis
      using red_pure_exp_different_def_state(1)[OF RedAux] ExhPure
      by auto
  qed

  then show ?case
    by (auto intro: inh_pure_normal simp: \<open>\<omega>_inh' = \<omega>_inh\<close>)
next
  case (SubAtomicFailure A \<omega>)
  then show ?case by simp \<comment>\<open>contradiction\<close>
next
  case (ExhStarNormal A \<omega> \<omega>'' B res)
  hence "\<omega> \<succeq> \<omega>''" and "\<omega>'' \<succeq> \<omega>'"
    by (simp_all add: exhale_normal_result_smaller)

  note AssertionFraming = \<open>assertion_framing_state ctxt StateCons (A && B) \<omega>_inh\<close>
  hence AssertionFramingA: "assertion_framing_state ctxt StateCons A \<omega>_inh"
    using assertion_framing_star
    by blast

  from ExhStarNormal have ConstraintA: "no_perm_assertion A \<and> no_unfolding_assertion A" and
                          ConstraintB: "no_perm_assertion B \<and> no_unfolding_assertion B"
    by simp_all

  have "\<omega> \<ominus> \<omega>' \<succeq> \<omega> \<ominus> \<omega>''"
    using \<open>\<omega>'' \<succeq> \<omega>'\<close> \<open>\<omega> \<succeq> \<omega>''\<close> minus_greater
    by blast

  moreover from this obtain \<omega>_inh'' where \<omega>_inh''_Some: "\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>'') = Some \<omega>_inh''"
    using \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close> 
    by (metis commutative compatible_smaller)

  ultimately have "\<omega>_inh' \<succeq> \<omega>_inh''"
    using \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>
    by (metis (full_types) addition_bigger commutative)
    
  hence \<omega>_inh''_valid: "StateCons \<omega>_inh'' \<and> valid_heap_mask (get_mh_total_full \<omega>_inh'')"
    using \<open>StateCons \<omega>_inh' \<and> valid_heap_mask (get_mh_total_full \<omega>_inh')\<close> 
          \<open>mono_prop_downward StateCons\<close>[simplified mono_prop_downward_def] valid_heap_mask_downward_mono
          full_total_state_greater_mask 
    by blast
    
  have RedInhA: "red_inhale ctxt StateCons A \<omega>_inh (RNormal \<omega>_inh'')"
    using ExhStarNormal.IH(1)[OF _ \<open>mono_prop_downward StateCons\<close> ConstraintA AssertionFramingA \<omega>_inh''_Some \<omega>_inh''_valid] ExhStarNormal.prems
          \<open>\<omega> \<succeq> \<omega>''\<close>
    by simp

  with AssertionFraming have AssertionFramingB: "assertion_framing_state ctxt StateCons B \<omega>_inh''"
    using assertion_framing_star
    by blast

  have \<omega>_inh'_Some2: "\<omega>_inh'' \<oplus> (\<omega>'' \<ominus> \<omega>') = Some \<omega>_inh'"
    using \<omega>_inh''_Some \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close> \<open>\<omega>'' \<succeq> \<omega>'\<close>
    by (smt (z3) \<open>\<omega> \<succeq> \<omega>''\<close> asso1 commutative minus_and_plus minus_equiv_def)

  have "red_inhale ctxt StateCons B \<omega>_inh'' (RNormal \<omega>_inh')"
  using ExhStarNormal.IH(2)[OF _ \<open>mono_prop_downward StateCons\<close> ConstraintB AssertionFramingB \<omega>_inh'_Some2 ] ExhStarNormal.prems
          \<open>\<omega>'' \<succeq> \<omega>'\<close>
  by simp

  then show ?case 
  using RedInhA
  by (fastforce intro: InhStarNormal)    
next
  case (ExhStarFailure A \<omega> B)
  then show ?case by simp \<comment>\<open>contradiction\<close>
next
  case (ExhImpTrue e \<omega> A res)
  with minus_full_total_state_only_mask_different_2[OF \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>]
  have RedAux: "ctxt, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool True)"    
    using red_pure_exp_only_differ_on_mask
    by fastforce

  note AssertionFraming = \<open>assertion_framing_state ctxt StateCons (assert.Imp e A) \<omega>_inh\<close>

  have RedExpInh: "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
  proof -
    have "\<not> ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
      using AssertionFraming
      unfolding assertion_framing_state_def
      using InhImpFailure by blast

    thus ?thesis
      using red_pure_exp_different_def_state(1)[OF RedAux] ExhImpTrue
      by auto
  qed

  hence "assertion_framing_state ctxt StateCons A \<omega>_inh"
    using assertion_framing_imp AssertionFraming
    by blast

  hence "red_inhale ctxt StateCons A \<omega>_inh (RNormal \<omega>_inh')"
    using ExhImpTrue
    by auto

  thus ?case
    using RedExpInh
    by (auto intro: red_inhale_intros)  
next
  case (ExhImpFalse e \<omega> A)
  hence "\<omega>_inh' = \<omega>_inh"
    by (metis full_total_state_defined_core_same_2 option.inject plus_minus_empty stmt_result_total.inject)

  have "ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  proof -
    have RedAux: "ctxt, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
      using ExhImpFalse minus_full_total_state_only_mask_different_2[OF \<open>\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'\<close>]
            red_pure_exp_only_differ_on_mask
      by fastforce

    have "\<not> (ctxt, StateCons, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure)"
      using \<open>assertion_framing_state ctxt StateCons (assert.Imp e A) \<omega>_inh\<close> InhImpFailure
      unfolding assertion_framing_state_def
      by blast

    thus ?thesis
      using red_pure_exp_different_def_state(1)[OF RedAux] ExhImpFalse
      by auto
  qed            

  then show ?case 
    by (auto intro: red_inhale_intros simp: \<open>\<omega>_inh' = \<omega>_inh\<close>)  
next
  case (ExhImpFailure e \<omega> A)
  then show ?case by simp \<comment>\<open>contradiction\<close>
qed

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