theory TraceIndepProp
imports TotalSemProperties
begin 



subsection \<open>Auxiliary definitions and lemmas\<close>

fun exp_in_paper_subset_no_rec :: "pure_exp \<Rightarrow> bool"
  where 
  "exp_in_paper_subset_no_rec (pure_exp.Var x) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.ELit lit) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.Unop uop e) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.Binop e1 bop e2) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.CondExp cond e1 e2) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.FieldAcc e f) \<longleftrightarrow> True"
| "exp_in_paper_subset_no_rec (pure_exp.Old lbl e) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.Perm e f) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.PermPred pname es) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.FunApp f es) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec pure_exp.Result \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.Unfolding pname es e) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.Let e e_body) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.PExists ty e) \<longleftrightarrow> False"
| "exp_in_paper_subset_no_rec (pure_exp.PForall ty e) \<longleftrightarrow> False"

abbreviation exp_in_paper_subset
  where "exp_in_paper_subset \<equiv> pure_exp_pred exp_in_paper_subset_no_rec"

fun atomic_assert_in_paper_subset_no_rec :: "pure_exp atomic_assert \<Rightarrow> bool"
  where
    "atomic_assert_in_paper_subset_no_rec (Pure e) = True"
  | "atomic_assert_in_paper_subset_no_rec (Acc e f (PureExp p)) = True"
  | "atomic_assert_in_paper_subset_no_rec (Acc e f Wildcard) = True"
  | "atomic_assert_in_paper_subset_no_rec (AccPredicate pred es q) = False"

abbreviation atomic_assert_in_paper_subset :: "pure_exp atomic_assert \<Rightarrow> bool"
  where "atomic_assert_in_paper_subset \<equiv> atomic_assert_pred atomic_assert_in_paper_subset_no_rec exp_in_paper_subset_no_rec"


fun assert_in_paper_subset_no_rec :: "(pure_exp, pure_exp atomic_assert) assert \<Rightarrow> bool"
  where
  "assert_in_paper_subset_no_rec (assert.Atomic A_atm) \<longleftrightarrow> True"
| "assert_in_paper_subset_no_rec (assert.Imp e A) \<longleftrightarrow> True"
| "assert_in_paper_subset_no_rec (assert.CondAssert e A B) \<longleftrightarrow> True"
| "assert_in_paper_subset_no_rec (A && B) \<longleftrightarrow> True"
| "assert_in_paper_subset_no_rec (assert.ImpureAnd A B) \<longleftrightarrow> False"
| "assert_in_paper_subset_no_rec (assert.ImpureOr A B) \<longleftrightarrow> False"
| "assert_in_paper_subset_no_rec (assert.ForAll _ A) \<longleftrightarrow> False"
| "assert_in_paper_subset_no_rec (assert.Exists _ A) \<longleftrightarrow> False"
| "assert_in_paper_subset_no_rec (assert.Wand A B) \<longleftrightarrow> False"

abbreviation assertion_in_paper_subset :: "(pure_exp, pure_exp atomic_assert) assert \<Rightarrow> bool"
  where 
    "assertion_in_paper_subset \<equiv> assert_pred assert_in_paper_subset_no_rec atomic_assert_in_paper_subset_no_rec exp_in_paper_subset_no_rec "

fun stmt_in_paper_subset_no_rec :: "stmt \<Rightarrow> bool"
  where
  "stmt_in_paper_subset_no_rec (Inhale A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (Exhale A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Assert A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Assume A) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (LocalAssign x e) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (FieldAssign e1 f e2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Havoc x) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (If e s1 s2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (Seq s1 s2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (MethodCall ys m es) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (While e A s) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Unfold pred es p) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Fold pred es p) \<longleftrightarrow> False" 
| "stmt_in_paper_subset_no_rec (Package A B) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Apply A B) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Label lbl) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Scope vty s) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec Skip \<longleftrightarrow> True"

abbreviation stmt_in_paper_subset
  where "stmt_in_paper_subset \<equiv> stmt_pred stmt_in_paper_subset_no_rec assertion_in_paper_subset exp_in_paper_subset"

lemma havoc_locs_state_trace_indep:
  assumes "\<omega> \<in> havoc_locs_state ctxt \<omega>_exh locs"
  shows "update_trace_total \<omega> t \<in> havoc_locs_state ctxt (update_trace_total \<omega>_exh t) locs" 
        (is "?\<omega>' \<in> havoc_locs_state ctxt ?\<omega>_exh' locs")
proof -
  from assms obtain hh' where
      "\<omega> = update_hh_total_full \<omega>_exh hh'"
  and HeapWellTyped: "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh'"
  and "hh' \<in> havoc_locs_heap (get_hh_total_full \<omega>_exh) locs"
    unfolding havoc_locs_state_def
    by blast

  hence "?\<omega>' = update_hh_total_full ?\<omega>_exh' hh'"
    by simp
  moreover from \<open>hh' \<in> _\<close> have "hh' \<in> havoc_locs_heap (get_hh_total_full ?\<omega>_exh') locs"
    by simp
  ultimately show ?thesis 
    using HeapWellTyped
    unfolding havoc_locs_state_def
    by blast
qed

lemma stmt_in_paper_subset_sub_expressions:
  assumes "stmt_in_paper_subset s"
  shows "list_all exp_in_paper_subset (sub_expressions s)"
  using assms
  apply (induction s)
  by simp_all

subsection \<open>Property\<close>

abbreviation states_differ_only_on_trace :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "states_differ_only_on_trace \<omega>1 \<omega>2 \<equiv> get_store_total \<omega>1 = get_store_total \<omega>2 \<and> 
                                              get_total_full \<omega>1 = get_total_full \<omega>2"

lemma states_differ_trace_update_trace_eq:
  assumes "states_differ_only_on_trace \<omega>1 \<omega>2"
  shows "update_trace_total \<omega>2 (get_trace_total \<omega>1) = \<omega>1"
  apply (rule full_total_state.equality)
  using assms
  by simp_all

lemma states_differ_trace_update_trace_eq_2:
  shows "states_differ_only_on_trace \<omega>1 (update_trace_total \<omega>1 t)"
  by simp
 
lemma exp_eval_inh_no_old_exp_trace_indep:
  shows "ctxt, (\<lambda>_. True), \<omega>_def1 \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow> 
        exp_in_paper_subset e \<Longrightarrow>
        states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow> 
        \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow> 
        (\<omega>_def2 \<noteq> None \<and> \<omega>_def1 \<noteq> None \<Longrightarrow> states_differ_only_on_trace (the \<omega>_def1) (the \<omega>_def2)) \<Longrightarrow>        
         ctxt, (\<lambda>_. True), \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE" and
        "red_pure_exps_total ctxt (\<lambda>_. True) \<omega>_def1 es \<omega>1 resES \<Longrightarrow> 
         list_all (\<lambda>e. exp_in_paper_subset e) es \<Longrightarrow>
        states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow> 
        \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow> 
        (\<omega>_def2 \<noteq> None \<and> \<omega>_def1 \<noteq> None \<Longrightarrow> states_differ_only_on_trace (the \<omega>_def1) (the \<omega>_def2)) \<Longrightarrow>
        red_pure_exps_total ctxt (\<lambda>_. True) \<omega>_def2 es \<omega>2 resES" and
        "red_inhale ctxt (\<lambda>_. True) A \<omega>1 res1 \<Longrightarrow> 
              assertion_in_paper_subset A \<Longrightarrow>
              states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow>
              (res1 = RFailure \<longrightarrow> red_inhale ctxt (\<lambda>_. True) A \<omega>2 RFailure) \<and>
              (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                     red_inhale ctxt (\<lambda>_. True) A \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))
              )" and
        "unfold_rel ctxt (\<lambda>_. True) x12 x13 x14 x15 x16 \<Longrightarrow> True"
proof (induction arbitrary: \<omega>2 \<omega>_def2 and \<omega>2 \<omega>_def2 and \<omega>2 rule: red_exp_inhale_unfold_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case 
    by (auto intro!: red_exp_inhale_unfold_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case 
    by (auto intro!: red_exp_inhale_unfold_intros)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case 
    by (auto intro!: red_exp_inhale_unfold_intros)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case 
    by (auto intro!: red_exp_inhale_unfold_intros)
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  show ?case
  apply (rule TotalExpressions.RedBinop)
    using RedBinop
    by auto
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  show ?case
    apply (rule TotalExpressions.RedBinopRightFailure)
    using RedBinopRightFailure
    by auto
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  show ?case
    apply (rule TotalExpressions.RedBinopOpFailure)
    using RedBinopOpFailure
    by auto
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
  show ?case 
    apply (rule TotalExpressions.RedUnop)
    using RedUnop
    by auto
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  show ?case
    apply (rule TotalExpressions.RedCondExpTrue)
    using RedCondExpTrue by auto
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  show ?case
    apply (rule TotalExpressions.RedCondExpFalse)
    using RedCondExpFalse by auto
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  then show ?case by simp
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case by simp
next
  case (RedField \<omega>_def e \<omega> a f v)
  hence AddrEval: "ctxt, (\<lambda>_. True), \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by simp

  show ?case
  proof (cases "(if_Some (\<lambda>res. (a, f) \<in> get_valid_locs res) \<omega>_def)")
    case True
    then show ?thesis 
      apply simp
      apply (cases \<omega>_def2)
       apply simp
       apply (rule RedField_no_def_normalI)
      using AddrEval
        apply blast
      using RedField
       apply simp
      apply simp
      apply (rule RedField_def_normalI)
      using AddrEval
        apply blast
      unfolding get_valid_locs_def
      using RedField
      by auto
  next
    case False
    then show ?thesis
      apply simp
      apply (cases \<omega>_def2)
       apply (simp add: RedField.prems(3))
      apply simp
      apply (rule RedField_def_failureI)
      using AddrEval
        apply blast
      using RedField
       apply blast
      unfolding get_valid_locs_def
      using RedField
      by auto
  qed
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  hence "ctxt, (\<lambda>_. True), \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef Null)"
    by simp
  thus ?case  
    by (auto intro!: TotalExpressions.RedFieldNullFailure)    
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by simp
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by simp
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by simp
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case by simp
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<phi>' \<omega>'_def ubody v)
  then show ?case by simp
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  hence "red_pure_exps_total ctxt (\<lambda>_. True) \<omega>_def2 (sub_pure_exp_total e') \<omega>2 None"
    using pure_exp_pred_subexp
    by presburger
  thus ?case 
    using RedSubFailure
    by (auto intro!: TotalExpressions.RedSubFailure)
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case 
    using TotalExpressions.RedExpListCons
    by (metis (no_types, lifting) list_all_simps(1))
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case 
    using TotalExpressions.RedExpListFailure
    by (metis (no_types, lifting) list_all_simps(1))
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
    using TotalExpressions.RedExpListNil
    by metis
next
  case (InhAcc \<omega> e_r r e_p p W' f res)  
  hence RcvRed: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by auto
  moreover from InhAcc have PermRed: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_p;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    by auto

  from \<open>th_result_rel _ _ _ _\<close>
  show ?case
  proof (cases rule: th_result_rel.cases)
    case (THResultNormal \<omega>')
    show ?thesis
    proof (cases "r = Null")
      case True
      hence "res = RNormal \<omega>"
        using THResultNormal \<open>W' = _\<close>
        by simp
      have RedInh2: "red_inhale ctxt (\<lambda>_. True) (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal \<omega>2)"
        apply (rule TotalExpressions.InhAcc[OF RcvRed PermRed])
        using \<open>r = Null\<close> THResultNormal
        by (auto intro: THResultNormal_alt)
      show ?thesis
        apply (simp add: \<open>res = RNormal \<omega>\<close>)
        using RedInh2 \<open>states_differ_only_on_trace \<omega> \<omega>2\<close> states_differ_trace_update_trace_eq             
        by (metis update_trace_total.elims)
    next
      case False
      hence "\<omega>' = update_mh_loc_total_full \<omega> (the_address r, f) (padd (get_mh_total_full \<omega> (the_address r, f)) (Abs_preal p))"
        using THResultNormal inhale_perm_single_nonempty \<open>W' = _\<close>
        by fastforce

      let ?W2' = "(if r = Null then {\<omega>2} else inhale_perm_single (\<lambda>_. True) \<omega>2 (the_address r,f) (Some (Abs_preal p)))"
      let ?\<omega>2' = "update_mh_loc_total_full \<omega>2 (the_address r, f) (padd (get_mh_total_full \<omega>2 (the_address r, f)) (Abs_preal p))"

      have "?\<omega>2' \<in> inhale_perm_single (\<lambda>_. True) \<omega>2 (the_address r, f) (Some (Abs_preal p))"
        apply (rule inhale_perm_single_elem)
        using \<open>\<omega>' \<in> W'\<close> \<open>W' = _\<close> \<open>r \<noteq> Null\<close> \<open>\<omega>' = _\<close> \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
        unfolding inhale_perm_single_def 
        by auto

      have "red_inhale ctxt (\<lambda>_. True) (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal ?\<omega>2')"
        apply (rule TotalExpressions.InhAcc[where ?W' = ?W2',OF RcvRed PermRed])
         apply (rule HOL.refl)
        apply (rule THResultNormal_alt)
        using inhale_perm_single_nonempty \<open>?\<omega>2' \<in> _\<close> \<open>r \<noteq> Null\<close>
          apply fastforce
        using THResultNormal \<open>?\<omega>2' \<in> _\<close> 
        by auto
      moreover have "?\<omega>2' = (update_trace_total \<omega>' (get_trace_total \<omega>2))"
        apply (simp add: \<open>\<omega>' = _\<close>)
        apply (rule full_total_state.equality)
        by (simp_all add:  \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>)        
      ultimately show ?thesis
        using \<open>res = _\<close> \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
        by simp        
      qed
  next
    case THResultMagic
    then show ?thesis by simp
  next
    case THResultFailure
    then show ?thesis 
      using RcvRed PermRed TotalExpressions.InhAcc th_result_rel.THResultFailure 
      by fastforce
  qed
next
  case (InhAccPred \<omega> e_args v_args e_p p W' pred_id res)
  then show ?case by simp
next
  case (InhAccWildcard \<omega> e_r r W' f res)
  then show ?case sorry
next
  case (InhAccPredWildcard \<omega> e_args v_args W' pred_id res)
  then show ?case by simp
next
  case (InhPure \<omega> e b)
  hence "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    by simp
  thus ?case
    using TotalExpressions.InhPure
    by (metis (full_types) InhPure.prems(2) states_differ_trace_update_trace_eq stmt_result_total.distinct(1) stmt_result_total.distinct(3) stmt_result_total.distinct(5) stmt_result_total.inject)    
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  hence RedA: "red_inhale ctxt (\<lambda>_. True) A \<omega>2
             (RNormal (update_trace_total \<omega>'' (get_trace_total \<omega>2)))"
    by simp

  show ?case
  proof (cases res)
    case RMagic
    then show ?thesis 
      by simp
  next
    case RFailure
    then show ?thesis 
      using RedA InhStarNormal TotalExpressions.InhStarNormal
      by (metis assert_pred.elims(2) assert_pred_rec.simps(4) stmt_result_total.distinct(5) update_trace_total_hm_same update_trace_total_store_same)
  next
    case (RNormal \<omega>''')
    then show ?thesis 
      using RedA InhStarNormal TotalExpressions.InhStarNormal
      by (metis (no_types, lifting) assert_pred.elims(2) assert_pred_rec.simps(4) inhale_only_changes_mask(3) update_trace_total_hm_same)     
  qed        
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case
    using TotalExpressions.InhStarFailureMagic
    by (metis assert_pred.simps assert_pred_rec.simps(4) stmt_result_total.distinct(3) stmt_result_total.distinct(5))
next
  case (InhImpTrue \<omega> e A res)
  hence RedE: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by simp
  show ?case 
  proof (cases res)
    case RFailure
    hence *: "red_inhale ctxt (\<lambda>_. True) A \<omega>2 RFailure"
      using InhImpTrue
      by auto
    thus ?thesis
      using \<open>res = _\<close> TotalExpressions.InhImpTrue[OF RedE]
      by auto
  next
    case (RNormal \<omega>')
    hence *: "red_inhale ctxt (\<lambda>_. True) A \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using InhImpTrue
      by auto
    thus ?thesis
      using \<open>res = _\<close> TotalExpressions.InhImpTrue[OF RedE]
      by auto
  qed (simp)        
next
  case (InhImpFalse \<omega> e A)
  hence RedE: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by simp
  thus ?case
    using TotalExpressions.InhImpFalse[OF RedE]
    by (metis InhImpFalse.prems(2) states_differ_trace_update_trace_eq stmt_result_total.distinct(5) stmt_result_total.inject)
next
  case (InhCondAssertTrue \<omega> e A res B)
  hence RedCond: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by simp

  show ?case
  proof (cases res)
    case RFailure
    hence "red_inhale ctxt (\<lambda>_. True) A \<omega>2 RFailure"
      using InhCondAssertTrue
      by auto    
    then show ?thesis 
      using RedCond RFailure
      by (auto intro: TotalExpressions.InhCondAssertTrue)
  next
    case (RNormal \<omega>1')
    hence "red_inhale ctxt (\<lambda>_. True) A \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))"
      using InhCondAssertTrue
      by auto
    then show ?thesis 
      using RedCond RNormal
      by (auto intro: TotalExpressions.InhCondAssertTrue)
  qed simp
next
  case (InhCondAssertFalse \<omega> e B res A)
  hence RedCond: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by simp

  show ?case
  proof (cases res)
    case RFailure
    hence "red_inhale ctxt (\<lambda>_. True) B \<omega>2 RFailure"
      using InhCondAssertFalse
      by auto    
    then show ?thesis 
      using RedCond RFailure
      by (auto intro: TotalExpressions.InhCondAssertFalse)
  next
    case (RNormal \<omega>1')
    hence "red_inhale ctxt (\<lambda>_. True) B \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))"
      using InhCondAssertFalse
      by auto
    then show ?thesis 
      using RedCond RNormal
      by (auto intro: TotalExpressions.InhCondAssertFalse)
  qed simp
next
  case (InhSubExpFailure A \<omega>)
  hence "list_all exp_in_paper_subset (direct_sub_expressions_assertion A)"
    using assert_pred_subexp by presburger
  hence "red_pure_exps_total ctxt (\<lambda>_. True) (Some \<omega>2) (direct_sub_expressions_assertion A) \<omega>2 None"
    using InhSubExpFailure
    by fastforce
  thus ?case
    using InhSubExpFailure 
    by (auto intro!: TotalExpressions.InhSubExpFailure)
next
  case (UnfoldRelStep pred_id pred_decl pred_body m \<phi> vs q m' \<omega> \<omega>')
  then show ?case by simp
qed

lemma red_exh_trace_indep:
  assumes "red_exhale ctxt (\<lambda>_. True) \<omega>def1 A \<omega>1 res1"
      and "assertion_in_paper_subset A"
      and "states_differ_only_on_trace \<omega>1 \<omega>2"
      and "states_differ_only_on_trace \<omega>def1 \<omega>def2"
    shows "(res1 = RFailure \<longrightarrow> red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 RFailure) \<and>
           (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                     red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))
           )"
  using assms
proof (induction arbitrary: \<omega>2)
  case (ExhAcc mh \<omega> e_r r e_p p a f)
  hence RedRcv2: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    and RedPerm2: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e_p;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhAcc(2)]
          exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhAcc(3)]
    by auto

  let ?cond = "\<lambda>mh. 0 \<le> p \<and> (if (r = Null) then (p = 0) else (PosReal.pgte (mh (a, f)) (Abs_preal p)))"
  let ?\<omega>' = "if (r = Null) then \<omega> else (update_mh_loc_total_full \<omega> (a, f) (mh (a, f) - Abs_preal p))"
  let ?res = "exh_if_total (?cond mh) ?\<omega>'"

  show ?case
  proof (cases ?res)
    case RFailure
    hence "\<not>(?cond mh)"
      by (auto elim: exh_if_total.elims)
    hence "\<not>(?cond (get_mh_total_full \<omega>2))"
      using \<open>mh = _\<close> \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
      by auto
    show ?thesis 
      apply (simp add: RFailure)
      apply (rule red_exhale_acc_failureI[OF RedRcv2 RedPerm2])
       apply (rule \<open>a = _\<close>)
      by (simp add: \<open>\<not>(?cond (get_mh_total_full \<omega>2))\<close>)
  next
    case (RNormal \<omega>')
    hence "?cond mh" and
          "\<omega>' = (if (r = Null) then \<omega> else (update_mh_loc_total_full \<omega> (a, f) (mh (a, f) - Abs_preal p)))"
      by (auto elim: exh_if_total.elims)
    hence "?cond (get_mh_total_full \<omega>2)"
      using \<open>mh = _\<close> \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
      by auto
    show ?thesis
      apply (simp add: RNormal)
      apply (rule red_exhale_acc_normalI[OF RedRcv2 RedPerm2])
        apply (rule \<open>a = _\<close>)
      using \<open>?cond (get_mh_total_full \<omega>2)\<close>
       apply blast
      apply (cases "r = Null"; rule full_total_state.equality)
      using \<open>\<omega>' = _\<close> \<open>mh = _\<close>
      by (auto simp add: \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>)
  qed simp
next
  case (ExhAccWildcard mh \<omega> e_r r a q f)
  then show ?case sorry
next
  case (ExhAccPred mp \<omega> e_args v_args e_p p pred_id)
  then show ?case by simp
next
  case (ExhAccPredWildcard mp \<omega> e_args v_args q pred_id)
  then show ?case by simp
next
  case (ExhPure e \<omega> b)
  hence RedExp2: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhPure(1)]
    by simp
  show ?case
  proof (cases b)
    case True
    then show ?thesis 
      apply simp
      using RedExp2 red_exhale.ExhPure ExhPure
      by (metis (full_types) exh_if_total.simps(2) states_differ_trace_update_trace_eq update_trace_total.simps)
  next
    case False
    then show ?thesis 
      apply simp
      using RedExp2 red_exhale.ExhPure ExhPure
      by fastforce
  qed    
next
  case (ExhStarNormal A \<omega> \<omega>' B res)
  hence RedA2: "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2
           (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
    by simp
  let ?\<omega>2' = "(update_trace_total \<omega>' (get_trace_total \<omega>2))"
  show ?case 
  proof (cases res)
    case RFailure
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 B ?\<omega>2' RFailure"
      using ExhStarNormal
      by auto      
    then show ?thesis 
      using ExhStarNormal RedA2 red_exhale.ExhStarNormal RFailure
      by (metis stmt_result_total.distinct(5))      
  next
    case (RNormal \<omega>'')
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 B ?\<omega>2' (RNormal (update_trace_total \<omega>'' (get_trace_total ?\<omega>2')))"
      using ExhStarNormal.IH(2)[where ?\<omega>2.0 = ?\<omega>2'] ExhStarNormal
      by simp    
    then show ?thesis 
      using ExhStarNormal RedA2 red_exhale.ExhStarNormal RNormal
      by fastforce
  qed simp
next
  case (ExhStarFailure A \<omega> B)
  hence RedA2: "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 RFailure"
    by simp
  then show ?case 
    using red_exhale.ExhStarFailure
    by fast    
next
  case (ExhImpTrue e \<omega> A res)
  hence RedCond2: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhImpTrue(1)]
    by simp
  show ?case
  proof (cases res)
    case RFailure
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 RFailure"
      using ExhImpTrue
      by simp
    then show ?thesis 
      using ExhImpTrue RedCond2 RFailure
      by (auto intro: red_exhale.ExhImpTrue)
  next
    case (RNormal \<omega>')
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using ExhImpTrue
      by simp
    then show ?thesis 
      using ExhImpTrue RedCond2 RNormal
      by (auto intro: red_exhale.ExhImpTrue)
  qed simp
next
  case (ExhImpFalse e \<omega> A)
  hence RedCond2: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhImpFalse(1)]
    by simp
  thus ?case
    apply simp
    using ExhImpFalse red_exhale.ExhImpFalse
    by (metis states_differ_trace_update_trace_eq update_trace_total.simps)    
next
  case (ExhCondTrue e \<omega> A res B)
  hence RedCond: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhCondTrue(1)]
    by simp
  show ?case
  proof (cases res)
    case RFailure
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 RFailure"
      using ExhCondTrue
      by simp
    then show ?thesis 
      using RedCond RFailure
      by (auto intro: red_exhale.ExhCondTrue)
  next
    case (RNormal \<omega>')
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 A \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using ExhCondTrue
      by simp
    then show ?thesis 
      using RedCond RNormal
      by (auto intro: red_exhale.ExhCondTrue)
  qed simp
next
  case (ExhCondFalse e \<omega> B res A)
  hence RedCond: "ctxt, (\<lambda>_. True), Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF ExhCondFalse(1)]
    by simp
  show ?case
  proof (cases res)
    case RFailure
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 B \<omega>2 RFailure"
      using ExhCondFalse
      by simp
    then show ?thesis 
      using RedCond RFailure
      by (auto intro: red_exhale.ExhCondFalse)
  next
    case (RNormal \<omega>')
    hence "red_exhale ctxt (\<lambda>_. True) \<omega>def2 B \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using ExhCondFalse
      by simp
    then show ?thesis 
      using RedCond RNormal
      by (auto intro: red_exhale.ExhCondFalse)
  qed simp
next
  case (ExhSubExpFailure A \<omega>)
  hence SubexpInSubset: "list_all exp_in_paper_subset (direct_sub_expressions_assertion A)"
    using assert_pred_subexp
    by simp
  hence "red_pure_exps_total ctxt (\<lambda>_. True) (Some \<omega>def2) (direct_sub_expressions_assertion A) \<omega>2 None"
    using exp_eval_inh_no_old_exp_trace_indep(2)[OF ExhSubExpFailure(2)] ExhSubExpFailure
    by fastforce
  then show ?case 
    using ExhSubExpFailure
    by (auto intro: red_exhale.ExhSubExpFailure)    
qed

lemma red_stmt_trace_indep:
  assumes "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> stmt \<omega>1 res1"
      and "stmt_in_paper_subset stmt"
      \<comment>\<open>Note we do not need the method pre- and postconditions in \<^term>\<open>program.methods (program_total ctxt)\<close>
         to be restricted, because during method calls the old state is given by the current state before 
         the call, which is the same in both states\<close>
      and "states_differ_only_on_trace \<omega>1 \<omega>2"
    shows "(res1 = RFailure \<longrightarrow> red_stmt_total ctxt  (\<lambda>_. True) \<Lambda> stmt \<omega>2 RFailure) \<and>
           (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                     red_stmt_total ctxt  (\<lambda>_. True) \<Lambda> stmt \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))
           )"
  using assms
proof (induction arbitrary: \<omega>2)
  case (RedSkip \<Lambda> \<omega>)
  then show ?case 
    using TotalSemantics.RedSkip
    by (metis states_differ_trace_update_trace_eq stmt_result_total.distinct(5) stmt_result_total.inject)
next
  case (RedInhale A \<omega> res \<Lambda>)
  note Aux = TotalSemantics.RedInhale exp_eval_inh_no_old_exp_trace_indep(3)[OF RedInhale(1)]
  show ?case
  proof (cases res)
    case RFailure
    hence "red_inhale ctxt (\<lambda>_. True) A \<omega>2 RFailure"
      using Aux RedInhale
      by auto
    then show ?thesis 
      using TotalSemantics.RedInhale RFailure
      by blast
  next
    case (RNormal \<omega>')
    hence "red_inhale ctxt (\<lambda>_. True) A \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using Aux RedInhale
      by auto
    then show ?thesis 
      using TotalSemantics.RedInhale RNormal
      by blast
  qed simp
next
  case (RedExhale \<omega> A \<omega>_exh \<omega>' \<Lambda>)
  hence RedExh2: "red_exhale ctxt (\<lambda>_. True) \<omega>2 A \<omega>2 (RNormal (update_trace_total \<omega>_exh (get_trace_total \<omega>2)))"
    using red_exh_trace_indep[OF RedExhale(1)]
    by auto
  have *: "{loc. PosReal.pnone < get_mh_total_full \<omega> loc \<and> get_mh_total_full \<omega>_exh loc = PosReal.pnone} =
        {loc.
         PosReal.pnone < get_mh_total_full \<omega>2 loc \<and> get_mh_total_full (update_trace_total \<omega>_exh (get_trace_total \<omega>2)) loc = PosReal.pnone}"
    using \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
    by simp
  show ?case 
    apply simp
    apply (rule TotalSemantics.RedExhale[OF RedExh2])
    using  havoc_locs_state_trace_indep[OF \<open>\<omega>' \<in> _\<close>, simplified *]
    by simp
next
  case (RedExhaleFailure \<omega> A \<Lambda>)
  hence "red_exhale ctxt (\<lambda>_. True) \<omega>2 A \<omega>2 RFailure"
    using red_exh_trace_indep
    by fastforce
  thus ?case 
    by (auto intro!: TotalSemantics.RedExhaleFailure)
next
  case (RedAssert \<omega> A \<omega>_exh \<Lambda>)
  hence RedExh2: "red_exhale ctxt (\<lambda>_. True) \<omega>2 A \<omega>2 (RNormal (update_trace_total \<omega>_exh (get_trace_total \<omega>2)))"
    using red_exh_trace_indep[OF RedAssert(1)]
    by auto
  thus ?case
    using TotalSemantics.RedAssert RedAssert
    by (metis states_differ_trace_update_trace_eq stmt_result_total.distinct(5) stmt_result_total.inject)
next
  case (RedAssertFailure \<omega> A \<Lambda>)
  hence "red_exhale ctxt (\<lambda>_. True) \<omega>2 A \<omega>2 RFailure"
    using red_exh_trace_indep
    by fastforce
  thus ?case 
    by (auto intro!: TotalSemantics.RedAssertFailure)
next
  case (RedHavoc \<Lambda> x ty v \<omega>)
  then show ?case
    sorry
next
  case (RedLocalAssign \<omega> e v \<Lambda> x ty)
  hence "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
    using exp_eval_inh_no_old_exp_trace_indep(1)
    by fastforce
  hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (LocalAssign x e) \<omega>2 (RNormal (update_var_total \<omega>2 x v))"
    using RedLocalAssign
    by (blast intro!: TotalSemantics.RedLocalAssign)
  moreover have "update_var_total \<omega>2 x v = (update_trace_total (update_var_total \<omega> x v) (get_trace_total \<omega>2))"
    apply (rule full_total_state.equality)
    using \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
    by auto
  ultimately show ?case
    by auto        
next
  case (RedFieldAssign \<omega> e_r addr f e v ty \<Lambda>)
  hence RedRef: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr))" and
        RedRHS: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF RedFieldAssign.hyps(1)]
          exp_eval_inh_no_old_exp_trace_indep(1)[OF RedFieldAssign.hyps(3)]
    by simp_all

  have "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (FieldAssign e_r f e) \<omega>2 (RNormal (update_hh_loc_total_full \<omega>2 (addr,f) v))"
    apply (rule TotalSemantics.RedFieldAssign)
    using RedFieldAssign
    unfolding get_writeable_locs_def
    by (auto intro: RedRef RedRHS)    
  moreover have "update_hh_loc_total_full \<omega>2 (addr,f) v = 
                 update_trace_total (update_hh_loc_total_full \<omega> (addr, f) v) (get_trace_total \<omega>2)"
    apply (rule full_total_state.equality)
    using \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
    by auto
  ultimately show ?case 
    by simp
next
  case (RedFieldAssignFailure \<omega> e_r r e v f \<Lambda>)
  hence RedRef: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
        RedRHS: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"    
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF RedFieldAssignFailure(1)]
          exp_eval_inh_no_old_exp_trace_indep(1)[OF RedFieldAssignFailure(2)]
    by simp_all
  then show ?case 
    using RedFieldAssignFailure
    unfolding get_writeable_locs_def
    by (simp add: get_writeable_locs_def red_stmt_total.RedFieldAssignFailure)
next
  case (RedMethodCall \<omega> es v_args m mdecl \<Lambda> ys v_rets resPre res resPost)
  hence RedArgs: "red_pure_exps_total ctxt (\<lambda>_. True) (Some \<omega>2) es \<omega>2 (Some v_args)"
    using exp_eval_inh_no_old_exp_trace_indep(2)[OF RedMethodCall(1)]
    by auto

  have RedExhPre: "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (Exhale (method_decl.pre mdecl)) (state_during_exhale_pre_call \<omega>2 v_args) resPre"
    using RedMethodCall
    by auto

  show ?case
  proof (cases resPre)
    case RMagic
    then show ?thesis 
      using RedMethodCall
      by simp
  next
    case RFailure
    have "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (MethodCall ys m es) \<omega>2 RFailure"
      apply (rule TotalSemantics.RedMethodCall[OF RedArgs])
      using RFailure RedMethodCall
      by auto
    then show ?thesis 
      using RFailure RedMethodCall
      by blast                 
  next
    case (RNormal \<omega>Pre)
    let ?res2 = "map_stmt_result_total (reset_state_after_call ys v_rets \<omega>2) resPost"
    have RedInhPost: "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (Inhale (method_decl.post mdecl)) (state_during_inhale_post_call \<omega>2 \<omega>Pre v_args v_rets) resPost"
      using RNormal RedMethodCall
      by simp
    have RedCall: "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (MethodCall ys m es) \<omega>2 ?res2"
      apply (rule TotalSemantics.RedMethodCall[OF RedArgs])
      using RedMethodCall RNormal 
            apply (solves \<open>simp\<close>)+
      using RedInhPost
      by auto    

    show ?thesis 
    proof (cases resPost)
      case RMagic
      then show ?thesis 
        using RNormal RedMethodCall
        by simp
    next
      case RFailure
      then show ?thesis 
        using RedCall[simplified reset_state_after_call_def] RedMethodCall RNormal
        by auto
    next
      case (RNormal \<omega>Post)
      hence "res = RNormal (reset_state_after_call ys v_rets \<omega> \<omega>Post)"
        using RedMethodCall \<open>resPre = RNormal \<omega>Pre\<close>
        by auto
      moreover have "?res2 = RNormal (reset_state_after_call ys v_rets \<omega> \<omega>Post\<lparr>get_trace_total := get_trace_total \<omega>2\<rparr>)"
        apply (simp add: \<open>resPost = _\<close> reset_state_after_call_def)
        using \<open>states_differ_only_on_trace \<omega> \<omega>2\<close>
        by simp

      ultimately show ?thesis
        using RedCall
        by auto
    qed
  qed
next
  case (RedLabel \<omega>' \<omega> lbl \<Lambda>)
  then show ?case by simp
next
  case (RedUnfold \<omega> e_args v_args e_p v_p W' pred_id res \<Lambda>)
  then show ?case by simp
next
  case (RedUnfoldWildcard \<omega> e_args v_args pred_id p \<phi>' \<omega>' \<Lambda>)
  then show ?case by simp
next
  case (RedUnfoldWildcardFailure \<omega> e_args v_args pred_id \<Lambda>)
  then show ?case by simp
next
  case (RedFold \<omega> e_args v_args e_p v_p pred_id res \<Lambda>)
  then show ?case by simp
next
  case (RedFoldWildcard \<omega> e_args v_args pred_id p res \<Lambda>)
  then show ?case by simp
next
  case (RedScope v \<tau> \<Lambda> scopeBody \<omega> res res_unshift)
  show ?case 
  proof (cases res)
    case RMagic
    then show ?thesis 
      using RedScope
      by simp
  next
    case RFailure
    hence "red_stmt_total ctxt (\<lambda>_. True) (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega>2 v) RFailure"
      using RedScope  
      by simp      
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (Scope \<tau> scopeBody) \<omega>2 RFailure"
      using TotalSemantics.RedScope RedScope
      by (metis map_stmt_result_total.simps(3))
    thus ?thesis
      using RFailure RedScope
      by simp
  next
    case (RNormal \<omega>Body)
    let ?\<omega>Body2 = "(update_trace_total \<omega>Body (get_trace_total (shift_and_add_state_total \<omega>2 v)))"
    have "red_stmt_total ctxt (\<lambda>_. True) (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega>2 v) (RNormal ?\<omega>Body2)"
      using RNormal RedScope.IH[where ?\<omega>2.0="(shift_and_add_state_total \<omega>2 v)"] RedScope
      by auto
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (Scope \<tau> scopeBody) \<omega>2 (RNormal (unshift_state_total 1 ?\<omega>Body2))"
      using TotalSemantics.RedScope RedScope
      by (metis map_stmt_result_total.simps(1))
    moreover have "res_unshift = RNormal (unshift_state_total 1 \<omega>Body)"
      using RNormal RedScope
      by simp
    moreover have "update_trace_total (unshift_state_total 1 \<omega>Body) (get_trace_total \<omega>2) = (unshift_state_total 1 ?\<omega>Body2)"
      apply (rule full_total_state.equality)
      by auto
    ultimately show ?thesis     
      by (metis stmt_result_total.distinct(5) stmt_result_total.inject)
  qed
next
  case (RedIfTrue \<omega> e_b \<Lambda> s_thn res s_els)
  hence RedCond2: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_b;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF RedIfTrue(1)]
    by simp
  show ?case
  proof (cases res)
    case RFailure
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s_thn \<omega>2 RFailure"
      using RedIfTrue
      by auto
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (stmt.If e_b s_thn s_els) \<omega>2 RFailure"
      using RedCond2 TotalSemantics.RedIfTrue
      by metis
    thus ?thesis 
      using RFailure
      by blast
  next
    case (RNormal \<omega>')
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s_thn \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using RedIfTrue
      by auto
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (stmt.If e_b s_thn s_els) \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using RedCond2 TotalSemantics.RedIfTrue
      by metis
    thus ?thesis
      using RNormal RedCond2 TotalSemantics.RedIfTrue RedIfTrue
      by blast
  qed simp
next
  case (RedIfFalse \<omega> e_b \<Lambda> s_els res s_thn)
  hence RedCond2: "ctxt, (\<lambda>_. True), Some \<omega>2 \<turnstile> \<langle>e_b;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using exp_eval_inh_no_old_exp_trace_indep(1)[OF RedIfFalse(1)]
    by simp
  show ?case
  proof (cases res)
    case RFailure
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s_els \<omega>2 RFailure"
      using RedIfFalse
      by auto
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (stmt.If e_b s_thn s_els) \<omega>2 RFailure"
      using RedCond2 TotalSemantics.RedIfFalse 
      by metis
    thus ?thesis 
      using RFailure
      by blast
  next
    case (RNormal \<omega>')
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s_els \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using RedIfFalse
      by auto
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (stmt.If e_b s_thn s_els) \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
      using RedCond2 TotalSemantics.RedIfFalse
      by metis
    thus ?thesis
      using RNormal RedCond2 TotalSemantics.RedIfTrue RedIfTrue
      by blast
  qed simp
next
  case (RedSeq \<Lambda> s1 \<omega> \<omega>' s2 res)
  hence RedS1: "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s1 \<omega>2 (RNormal (update_trace_total \<omega>' (get_trace_total \<omega>2)))"
    by simp
  let ?\<omega>2' = "(update_trace_total \<omega>' (get_trace_total \<omega>2))"
  show ?case
  proof (cases res)
    case RFailure
    with RedSeq.IH(2)[where ?\<omega>2.0 = ?\<omega>2']
    have "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s2 ?\<omega>2' RFailure"
      using RedSeq
      by auto
    with RedS1 TotalSemantics.RedSeq RFailure
    show ?thesis
      by fast      
  next
    case (RNormal \<omega>'')
    with RedSeq.IH(2)[where ?\<omega>2.0 = ?\<omega>2']
    have "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s2 ?\<omega>2' (RNormal (update_trace_total \<omega>'' (get_trace_total ?\<omega>2')))"
      using RedSeq
      by auto    
    then show ?thesis 
      using RedS1 TotalSemantics.RedSeq RNormal
      by fastforce
  qed simp
next
  case (RedSeqFailureOrMagic \<Lambda> s1 \<omega> res s2)
  show ?case 
  proof (cases res)
    case RFailure
    hence "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s1 \<omega>2 RFailure"
      using RedSeqFailureOrMagic
      by auto
    then show ?thesis 
      using RFailure TotalSemantics.RedSeqFailureOrMagic
      by blast
  next
    case (RNormal \<omega>')
    then show ?thesis 
      using RedSeqFailureOrMagic
      by simp
  qed simp
next
  case (RedSubExpressionFailure s \<omega> \<Lambda>)
  hence ExpsInSubset: "list_all exp_in_paper_subset (sub_expressions s)"
    using stmt_in_paper_subset_sub_expressions
    by blast
  hence "red_pure_exps_total ctxt (\<lambda>_. True) (Some \<omega>2) (sub_expressions s) \<omega>2 None"
    using RedSubExpressionFailure exp_eval_inh_no_old_exp_trace_indep(2)
    by fastforce    
  thus ?case 
    using RedSubExpressionFailure 
    by (auto intro: TotalSemantics.RedSubExpressionFailure)
qed



end