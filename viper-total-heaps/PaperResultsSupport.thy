theory PaperResultsSupport
imports ViperBoogieEndToEnd
begin

definition vpr_method_correct_paper :: "'a total_context \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_correct_paper ctxt m \<equiv>
         \<forall>(\<sigma>\<^sub>v :: 'a full_total_state) r\<^sub>v. 
            \<comment>\<open>These first two premises state that the store must be well-typed w.r.t. the arguments and result
               variable types and that the heap must be well-typed w.r.t. the field declarations. Both
               of these premises were omitted in the paper for the sake of presentation (as pointed out
               in footnote 7 on line 832 in the paper).\<close>
            vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args m @ method_decl.rets m)) (get_store_total \<sigma>\<^sub>v) \<longrightarrow>
            total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<sigma>\<^sub>v) \<longrightarrow>
                          
            \<comment>\<open>The following premise corresponds to \<open>\<forall>l. \<pi>(\<sigma>\<^sub>v)(l) = 0\<close> in the paper\<close>
            is_empty_total_full \<sigma>\<^sub>v \<longrightarrow>

            (\<forall>mbody. method_decl.body m = Some mbody \<longrightarrow>
              (               
                red_stmt_total ctxt (\<lambda>_. True) (nth_option (method_decl.args m @ method_decl.rets m))
                                    (Seq (Inhale (method_decl.pre m)) (Seq mbody (Exhale (method_decl.post m))))
                                    \<sigma>\<^sub>v
                                    r\<^sub>v \<longrightarrow>
                r\<^sub>v \<noteq> RFailure
              )
            )"

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

fun atomic_assert_in_paper_subset :: "pure_exp atomic_assert \<Rightarrow> bool"
  where
    "atomic_assert_in_paper_subset (Pure e) = True"
  | "atomic_assert_in_paper_subset (Acc e f (PureExp p)) = True"
  | "atomic_assert_in_paper_subset (Acc e f Wildcard) = False"
  | "atomic_assert_in_paper_subset (AccPredicate pred es q) = False"

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
    "assertion_in_paper_subset \<equiv> assert_pred assert_in_paper_subset_no_rec atomic_assert_in_paper_subset exp_in_paper_subset_no_rec "

fun stmt_in_paper_subset_no_rec :: "stmt \<Rightarrow> bool"
  where
  "stmt_in_paper_subset_no_rec (Inhale A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (Exhale A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Assert A) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Assume A) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (LocalAssign x e) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (FieldAssign e1 f e2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (ViperLang.Havoc x) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (If e s1 s2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (Seq s1 s2) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (MethodCall ys m es) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (While e A s) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec (Unfold pred es p) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Fold pred es p) \<longleftrightarrow> False" 
| "stmt_in_paper_subset_no_rec (Package A B) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Apply A B) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Label lbl) \<longleftrightarrow> False"
| "stmt_in_paper_subset_no_rec (Scope vty s) \<longleftrightarrow> True"
| "stmt_in_paper_subset_no_rec Skip \<longleftrightarrow> True"

abbreviation stmt_in_paper_subset
  where "stmt_in_paper_subset \<equiv> stmt_pred_rec stmt_in_paper_subset_no_rec assertion_in_paper_subset exp_in_paper_subset"


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
  then show ?case by simp
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
  then show ?case sorry
next
  case (InhCondAssertFalse \<omega> e B res A)
  then show ?case sorry
next
  case (InhSubExpFailure A \<omega>)
  then show ?case sorry
next
  case (UnfoldRelStep pred_id pred_decl pred_body m \<phi> vs q m' \<omega> \<omega>')
  then show ?case by simp
qed

lemma correctness_stronger:
  assumes "vpr_method_correct_total ctxt (\<lambda>_.True) m"
      and "method_decl.body m = Some mbody"
    shows "vpr_method_correct_paper ctxt m"
  unfolding vpr_method_correct_paper_def
proof (rule allI | rule impI)+
  fix \<sigma>\<^sub>v r\<^sub>v mbody
  assume StoreWt: "vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args m @ rets m)) (get_store_total \<sigma>\<^sub>v)"
     and HeapWt: "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<sigma>\<^sub>v)"
     and EmptyInit: "is_empty_total_full \<sigma>\<^sub>v"
     and SomeBody: "method_decl.body m = Some mbody"
     and RedStmt: "red_stmt_total ctxt (\<lambda>_. True) (nth_option (method_decl.args m @ rets m))
          (Seq (Inhale (method_decl.pre m)) (Seq mbody (Exhale (method_decl.post m)))) \<sigma>\<^sub>v r\<^sub>v"

  let ?\<Lambda> = "(nth_option (method_decl.args m @ rets m))"

  note Aux = assms(1)[simplified vpr_method_correct_total_2_new_equiv vpr_method_correct_total_expanded_def]

  from RedStmt
  show "r\<^sub>v \<noteq> RFailure"
  proof (cases)
    case (RedSeq \<sigma>1)
    hence "red_inhale ctxt (\<lambda>_. True) (method_decl.pre m) \<sigma>\<^sub>v (RNormal \<sigma>1)"
      by (auto elim: RedInhale_case)

    with Aux StoreWt HeapWt EmptyInit
    have "(\<forall>mbody. method_decl.body m = Some mbody \<longrightarrow> vpr_method_body_correct ctxt (\<lambda>_. True) m \<sigma>1)"
      by blast
    hence AuxBody: "\<forall>r. red_stmt_total ctxt (\<lambda>_.True) ?\<Lambda>
                                (Seq mbody (Exhale (method_decl.post m)))
                                (update_trace_total \<sigma>1 (Map.empty(old_label \<mapsto> get_total_full \<sigma>1))) 
                                r \<longrightarrow> r \<noteq> RFailure"
      using SomeBody
      unfolding vpr_method_body_correct_def 
      by auto

    show "r\<^sub>v \<noteq> RFailure"
    proof 
      assume "r\<^sub>v = RFailure"
      with RedSeq(2) have "red_stmt_total ctxt (\<lambda>_.True) ?\<Lambda>
                                (Seq mbody (Exhale (method_decl.post m)))
                                (update_trace_total \<sigma>1 (Map.empty(old_label \<mapsto> get_total_full \<sigma>1))) 
                                RFailure"
        sorry
      thus False
        using AuxBody
        by blast
    qed
  next
    case RedSeqFailureOrMagic
    hence "red_inhale ctxt (\<lambda>_. True) (method_decl.pre m) \<sigma>\<^sub>v r\<^sub>v"
      by (auto elim: RedInhale_case)
    with Aux StoreWt HeapWt EmptyInit
    show ?thesis
      by blast
  qed simp
qed


end