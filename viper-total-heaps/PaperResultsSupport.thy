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

abbreviation states_differ_only_on_trace :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "states_differ_only_on_trace \<omega>1 \<omega>2 \<equiv> get_store_total \<omega>1 = get_store_total \<omega>2 \<and> 
                                              get_total_full \<omega>1 = get_total_full \<omega>2"

lemma exp_eval_inh_no_old_exp_trace_indep:
  shows "ctxt, R, \<omega>_def1 \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow> 
        no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_old_pure_exp e \<Longrightarrow>
        states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow> 
        \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow> 
        (\<omega>_def2 \<noteq> None \<and> \<omega>_def1 \<noteq> None \<Longrightarrow> states_differ_only_on_trace (the \<omega>_def1) (the \<omega>_def2)) \<Longrightarrow>        
         ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE" and
        "red_pure_exps_total ctxt R \<omega>_def1 es \<omega>1 resES \<Longrightarrow> 
         list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_old_pure_exp e) es \<Longrightarrow>
        states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow> 
        \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow> 
        (\<omega>_def2 \<noteq> None \<and> \<omega>_def1 \<noteq> None \<Longrightarrow> states_differ_only_on_trace (the \<omega>_def1) (the \<omega>_def2)) \<Longrightarrow>
        red_pure_exps_total ctxt R \<omega>_def2 es \<omega>2 resES" and
        "red_inhale ctxt R A \<omega>1 res1 \<Longrightarrow> 
              no_perm_assertion A \<and> no_unfolding_assertion A  \<and> no_old_assertion A \<Longrightarrow>
              states_differ_only_on_trace \<omega>1 \<omega>2 \<Longrightarrow>  res1 \<noteq> RMagic \<Longrightarrow> 
              (res1 = RFailure \<longrightarrow> red_inhale ctxt R A \<omega>2 RFailure) \<and>
              (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                    (red_inhale ctxt R A \<omega>2 (RNormal (update_trace_total \<omega>1' (get_trace_total \<omega>2)))
              )
        )" and
        "unfold_rel ctxt R x12 x13 x14 x15 x16 \<Longrightarrow> True"
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
  hence AddrEval: "ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
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
  hence "ctxt, R, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef Null)"
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
  hence "red_pure_exps_total ctxt R \<omega>_def2 (sub_pure_exp_total e') \<omega>2 None"
    using Ball_set_list_all pure_exp_pred_subexp
    by (metis (mono_tags, lifting))
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
  hence "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by auto
  moreover from InhAcc have "ctxt, R, Some \<omega>2 \<turnstile> \<langle>e_p;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    by auto
  ultimately show ?case
    using InhAcc
    sorry  
next
  case (InhAccPred \<omega> e_args v_args e_p p W' pred_id res)
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