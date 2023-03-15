theory InhaleRel
  imports ExpRel ExprWfRel TotalViper.ViperBoogieTranslationInterface Simulation
begin

definition inhale_rel ::
     "('a full_total_state \<Rightarrow> 'a vbpl_absval nstate \<Rightarrow> bool)
     \<Rightarrow> 'a total_context
        \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
           \<Rightarrow> bigblock list
                    \<Rightarrow> 'a econtext_bpl
                       \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert
                          \<Rightarrow> bigblock \<times> cont \<Rightarrow> bigblock \<times> cont \<Rightarrow> bool"
  where "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv>
         rel_general R R 
           (\<lambda> \<omega> \<omega>'. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>'))
           (\<lambda> \<omega>. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure)
           P ctxt \<gamma> \<gamma>'"


lemma inhale_rel_intro:
  assumes
    "\<And>\<omega> ns \<omega>'. 
      R \<omega> ns \<Longrightarrow> 
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
      (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and

    "\<And>\<omega> ns.
      R \<omega> ns \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure \<Longrightarrow>
      (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_intro)

definition inhale_rel_aux
  where "inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res \<equiv>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                   \<comment>\<open>Normal Viper inhale executions can be simulated by normal Boogie executions\<close>
                   (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                   \<comment>\<open>If a Viper inhale executions fails, then there is a failing Boogie execution\<close>
                   (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure))"

lemma inhale_rel_intro_2:
  assumes
    "\<And>\<omega> ns res. 
      R \<omega> ns \<Longrightarrow> 
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> res \<Longrightarrow>
      inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def inhale_rel_aux_def
  by (auto intro: rel_intro)

lemma inhale_rel_aux_intro:
  assumes "\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow>
           (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and
          "res = RFailure \<Longrightarrow> (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
        shows "inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res"
  using assms
  unfolding inhale_rel_aux_def
  by blast

lemma inhale_rel_normal_elim:
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>')"
  shows "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns')"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_success_elim)

lemma inhale_rel_failure_elim:
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure"
  shows "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  using assms
  unfolding inhale_rel_def rel_general_def
  by auto

subsection \<open>Structural rules\<close>

lemma inhale_rel_star: 
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" and
          "inhale_rel R ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
        shows "inhale_rel R ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
  using assms
  unfolding inhale_rel_def
  apply (rule rel_general_comp)
  by (auto elim: InhStar_case)

lemma inhale_rel_imp:
  assumes 
   ExpWfRel:          
        "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr StateCons P ctxt cond 
         \<gamma>1
         (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont)" 
        (is "expr_wf_rel _ ctxt_vpr StateCons P ctxt cond _ ?\<gamma>_if") and
   EmptyElse: "is_empty_bigblock empty_else_block" and
   ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl" and
   RhsRel: "inhale_rel R ctxt_vpr StateCons P ctxt A (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
                (is "inhale_rel R _ _ _ _ _ ?\<gamma>_thn (next, cont)")
              shows "inhale_rel R ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont)"
  using wf_rel_general_1[OF ExpWfRel] RhsRel
  unfolding inhale_rel_def
proof (rule rel_general_cond)
  show "rel_general R R (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>') (\<lambda>_. False) P ctxt (empty_else_block, convert_list_to_cont [] (KSeq next cont)) (next, cont)"
    apply (rule rel_intro)
    using red_ast_bpl_empty_block_2[OF EmptyElse]
    apply fastforce
    by simp
next
  fix \<omega> \<omega>' ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> (RNormal \<omega>')" and "R \<omega> ns"
  thus "((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> red_inhale ctxt_vpr StateCons A \<omega> (RNormal \<omega>') \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> \<omega> = \<omega>')"
    apply (cases)
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
    apply (metis val_rel_vpr_bpl.simps(2))
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
    by (metis val_rel_vpr_bpl.simps(2))
next
  fix \<omega> ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> RFailure" and "R \<omega> ns"
  thus "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
       ((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> red_inhale ctxt_vpr StateCons A \<omega> RFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> False)"
    apply (cases)
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
     apply (metis val_rel_vpr_bpl.simps(2))
    by auto
qed

subsection \<open>Field access predicate rule\<close>

definition inhale_acc_normal_premise
  where "inhale_acc_normal_premise ctxt StateCons e_r f e_p p r \<omega> \<omega>' \<equiv>
       ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<and>
       ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> 
       p \<ge> 0 \<and>
       (p > 0 \<longrightarrow> r \<noteq> Null) \<and>
       (let W' = (if r = Null then {\<omega>} else inhale_perm_single StateCons \<omega> (the_address r,f) (Some (Abs_prat p))) in
       (W' \<noteq> {} \<and> \<omega>' \<in> W'))"

lemma inhale_rel_field_acc:
  assumes 
    MaskUpdWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    WfRcv: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" and
  
    PosPermRel:  "\<And>p. rel_general R R'
                  (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>' \<and> (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0))
                  (\<lambda> \<omega>. (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0))
                  P ctxt \<gamma>2 \<gamma>3" and
     UpdInhRel: "\<And>p r. rel_general R' R
                  (\<lambda> \<omega> \<omega>'. inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r \<omega> \<omega>')
                  (\<lambda> \<omega>. False) P ctxt \<gamma>3 \<gamma>'"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"
proof (rule inhale_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns"
  hence Rext0: "state_rel_ext R \<omega> \<omega> ns"
    by simp

  assume RedInh: "red_inhale ctxt_vpr StateCons (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega> res"
  thus "inhale_rel_aux R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>' \<omega> ns res"
  proof (cases)
    case (InhAcc r p W')
    from this obtain ns1 where Rext1: "state_rel_ext R \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF WfRcv Rext0]
      by blast
    with InhAcc obtain ns2 where "state_rel_ext R \<omega> \<omega> ns2" and Red2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF WfPerm Rext1] red_ast_bpl_transitive
      by blast
    hence "R \<omega> ns2"
      by simp

    show ?thesis
    proof (rule inhale_rel_aux_intro)
      \<comment>\<open>Normal case\<close>
      
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      hence "0 \<le> p" and "W' \<noteq> {}" and "0 < p \<longrightarrow> r \<noteq> Null" and "\<omega>' \<in> W'"
      using th_result_rel_normal InhAcc
      by blast+

      with InhAcc and \<open>res = _\<close> have InhNormalPremise:"inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r \<omega> \<omega>'"
        unfolding inhale_acc_normal_premise_def 
        by presburger

      from InhAcc \<open>0 \<le> p\<close> obtain ns3 where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>3, Normal ns3)" and "R' \<omega> ns3" 
        using rel_success_elim[OF PosPermRel \<open>R \<omega> ns2\<close>] Red2 red_ast_bpl_transitive
        by blast

      thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
        using rel_success_elim[OF UpdInhRel _ InhNormalPremise] RedInh \<open>res = _\<close> red_ast_bpl_transitive 
        by blast
    next
      \<comment>\<open>Failure case\<close>
      assume "res = RFailure"
      hence "p < 0"
        using th_result_rel_failure_2 InhAcc
        by fastforce

      with InhAcc show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
        using rel_failure_elim[OF PosPermRel \<open>R \<omega> ns2\<close>] Red2 red_ast_bpl_transitive
        by blast
    qed
  next 
    case InhSubAtomicFailure
    hence SubexpFailCases: 
          "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
           (\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> 
                ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
      by (auto elim: red_exp_list_failure_elim)  
    show ?thesis
    proof (rule inhale_rel_aux_intro)
      show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      proof (cases "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure")
        case True
        then show ?thesis 
          using wf_rel_failure_elim[OF WfRcv] \<open>R \<omega> ns\<close>
          by blast
      next
        case False
        then show ?thesis 
          using wf_rel_normal_elim[OF WfRcv] \<open>R \<omega> ns\<close> 
                wf_rel_failure_elim[OF WfPerm] SubexpFailCases red_ast_bpl_transitive
          by metis
      qed
    qed (simp add: \<open>res = _\<close>)
  qed
qed

definition pred_eq
  where "pred_eq x v = (x = v)"

lemma pos_perm_rel:
  assumes ExpRel: "exp_rel_vpr_bpl (state_rel_ext R) ctxt_vpr ctxt e_p e_p_bpl" and
         DisjAux: "temp_perm \<notin> {heap_var Tr, mask_var Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
          StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel Pr TyRep Tr AuxPred ctxt \<omega> ns" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_perm = Some (TPrim TReal)" and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         WritePermConst: "zero_perm = const_repr Tr CNoPerm"

\<comment>\<open>TODO: handle case e_p is statically determined to be non-negative\<close>
  shows "rel_general R
                  (state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt)
                  (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>' \<and> (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0))
                  (\<lambda> \<omega>. (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0))
                  P ctxt 
                  ((BigBlock name (Lang.Assign temp_perm e_p_bpl # Assert ((Var temp_perm) \<guillemotleft>Ge\<guillemotright> (Var zero_perm)) # cs) s tr), cont) 
                  (BigBlock name cs s tr, cont)" (is "rel_general R ?R' ?Success ?Fail  P ctxt ?\<gamma> ?\<gamma>'")
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and
         A: "\<omega> = \<omega>' \<and> ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> 0 \<le> p"
  from this have
    RedPerm:  "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and "0 \<le> p" 
    by auto

  note StateRelInst = StateRel[OF \<open>R \<omega> ns\<close>]
  let ?p_bpl = "real_of_rat p"

  from RedPerm have RedPermBpl: "red_expr_bpl ctxt e_p_bpl ns (RealV ?p_bpl)"
    using exp_rel_vpr_bpl_elim[OF ExpRel] \<open>R \<omega> ns\<close>
    by (metis val_rel_vpr_bpl.simps(5))

  let ?ns' = "update_var (var_context ctxt) ns temp_perm (RealV ?p_bpl)"

  have StateRelInst2: "state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV ?p_bpl))) ctxt \<omega> ?ns'"
    using state_rel_new_auxvar[OF StateRelInst DisjAux _ TyInterp LookupTyTemp]
    unfolding pred_eq_def
    by simp

  moreover have "red_ast_bpl P ctxt
              (?\<gamma>, Normal ns)
              ((BigBlock name (Assert ((Var temp_perm) \<guillemotleft>Ge\<guillemotright> (Var zero_perm)) # cs) s tr, cont), Normal ?ns')"
      (is "red_ast_bpl P ctxt _ (?\<gamma>'',_)")
    apply (rule red_ast_bpl_one_simple_cmd)
    by (fastforce intro!: RedAssign LookupTyTemp RedPermBpl)

  moreover have "red_ast_bpl P ctxt (?\<gamma>'', Normal ?ns') (?\<gamma>', Normal ?ns')"
    apply (rule red_ast_bpl_one_simple_cmd)
    using \<open>0 \<le> p\<close>
    by (auto intro!: RedAssertOk Semantics.RedBinOp Semantics.RedVar 
                        boogie_const_rel_lookup[OF state_rel0_boogie_const[OF state_rel_state_rel0[OF StateRelInst2]]] 
                simp: \<open>zero_perm = _\<close>)

  ultimately show "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>, Normal ns) ((BigBlock name cs s tr, cont), Normal ns') \<and>                         
                              state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega>' ns'"
    using RedPerm red_ast_bpl_transitive A
    by fast
next
  fix \<omega> ns
  assume "R \<omega> ns"
  assume "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> p < 0"
  from this have RedPerm: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and "p < 0" 
    by auto

  note StateRelInst = StateRel[OF \<open>R \<omega> ns\<close>]
  let ?p_bpl = "real_of_rat p"

  from RedPerm have RedPermBpl: "red_expr_bpl ctxt e_p_bpl ns (RealV ?p_bpl)"
    using exp_rel_vpr_bpl_elim[OF ExpRel] \<open>R \<omega> ns\<close>
    by (metis val_rel_vpr_bpl.simps(5))

  let ?ns' = "update_var (var_context ctxt) ns temp_perm (RealV ?p_bpl)"

  have StateRelInst2: "state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV ?p_bpl))) ctxt \<omega> ?ns'"
    using  state_rel_new_auxvar[OF StateRelInst DisjAux _ TyInterp LookupTyTemp]
    unfolding pred_eq_def
    by simp
  
  moreover have "red_ast_bpl P ctxt
              (?\<gamma>, Normal ns)
              ((BigBlock name (Assert ((Var temp_perm) \<guillemotleft>Ge\<guillemotright> (Var zero_perm)) # cs) s tr, cont), Normal ?ns')"
      (is "red_ast_bpl P ctxt _ (?\<gamma>'',_)")
    apply (rule red_ast_bpl_one_simple_cmd)
    by (fastforce intro!: RedAssign LookupTyTemp RedPermBpl)

  moreover have "red_ast_bpl P ctxt (?\<gamma>'', Normal ?ns') (?\<gamma>', Failure)"
    apply (rule red_ast_bpl_one_simple_cmd)
    using \<open>p < 0\<close>
    by (auto intro!: RedAssertFail Semantics.RedBinOp Semantics.RedVar 
                        boogie_const_rel_lookup[OF state_rel0_boogie_const[OF state_rel_state_rel0[OF StateRelInst2]]] 
                simp: \<open>zero_perm = _\<close> )

  ultimately show 
       "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (?\<gamma>, Normal ns) c'"
    using red_ast_bpl_transitive
    by fastforce
qed

lemma upd_inh_rel:
  assumes
    StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>                            
                           state_rel (program_total ctxt_vpr) TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega> ns" and
              "temp_perm \<notin> dom AuxPred" and
    WfTyRep:  "wf_ty_repr_bpl TyRep" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and
    HeapUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
                   "new_perm = (mask_read_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<guillemotleft>Lang.Add\<guillemotright> (Var temp_perm)" and
    MaskVar: "m_bpl = mask_var Tr " and
    FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    RcvRel: "exp_rel_vpr_bpl (state_rel_ext R) ctxt_vpr ctxt e_rcv_vpr e_rcv_bpl"
  shows "rel_general R 
                  (state_rel (program_total ctxt_vpr) TyRep Tr AuxPred ctxt)
                  (\<lambda> \<omega> \<omega>'. inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>')
                  (\<lambda> \<omega>. False) P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'

  assume "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'" and
         "R \<omega> ns"
  from this obtain W' where InhAccNormal: 
       "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
       "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
       "p \<ge> 0"
       "(p > 0 \<longrightarrow> r \<noteq> Null)"
       "W' = (if r = Null then {\<omega>} else inhale_perm_single StateCons \<omega> (the_address r, f_vpr) (Some (Abs_prat p)))"
       "W' \<noteq> {}" 
       "\<omega>' \<in> W'"
    unfolding inhale_acc_normal_premise_def
    by metis

  show "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns) 
                                 ((BigBlock name cs str tr, cont), Normal ns') \<and>
             state_rel (program_total ctxt_vpr) TyRep Tr AuxPred ctxt \<omega>' ns'"
  proof -
    from \<open>R \<omega> ns\<close> InhAccNormal have RedRcvBpl: "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))"
      using exp_rel_vpr_bpl_elim_2[OF RcvRel] 
      by (metis val_rel_vpr_bpl.simps(3))

    note StateRelInst = StateRel[OF \<open>R \<omega> ns\<close>]

    hence LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some (RealV (real_of_rat p))"
      using state_rel_aux_pred_sat_lookup_2
      unfolding pred_eq_def      
      by (metis (full_types) fun_upd_same)

    have StateRelInst2: "state_rel (program_total ctxt_vpr) TyRep Tr AuxPred ctxt \<omega> ns"
      using \<open>temp_perm \<notin> _\<close> state_rel_aux_pred_remove[OF StateRelInst]
      by (metis fun_upd_None_if_notin_dom map_le_imp_upd_le upd_None_map_le)
      
    obtain f_bpl \<tau>_vpr where
      FieldLookup: "declared_fields (program_total ctxt_vpr) f_vpr = Some \<tau>_vpr" and
      TyTr: "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl" and
      FieldTr: "field_translation Tr f_vpr = Some f_bpl" and
      "e_f_bpl = Lang.Var f_bpl"
    using FieldRelSingle
    by (auto elim: field_rel_single_elim)

    hence FieldLookupBpl: "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField (NormalField f_bpl \<tau>_vpr)))"
        (is "_ = Some (AbsV (AField ?f_bpl_val))")
      using state_rel0_field_rel[OF state_rel_state_rel0[OF StateRelInst]]
      unfolding field_rel_def
      by fastforce
    
    hence FieldTy: "field_ty_fun_opt TyRep (NormalField f_bpl \<tau>_vpr) = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])"      
      using TyTr
      by simp
  
    obtain mb where
          LookupMask: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
          LookupMaskTy: "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
          MaskRel: "mask_rel (program_total ctxt_vpr) (field_translation Tr) (get_mh_total_full \<omega>) mb"
      using state_rel_obtain_mask[OF StateRelInst]
      by blast

    let ?mb' = "mb ( (r, ?f_bpl_val) := mb (r, ?f_bpl_val) + (real_of_rat p))"
  
    have
      "red_expr_bpl ctxt (mask_read_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) ns
                         (RealV (mb (r, ?f_bpl_val)))"
      using mask_read_wf_apply[OF MaskReadWf] LookupMask RedRcvBpl FieldLookupBpl \<open>e_f_bpl = _\<close> Semantics.RedVar FieldTy \<open>m_bpl = _\<close>
      by meson
  
    hence "red_expr_bpl ctxt new_perm ns (RealV (mb (r, ?f_bpl_val) + (real_of_rat p)))"
      apply (subst \<open>new_perm = _\<close>)
      by (auto intro!: Semantics.RedVar Semantics.RedBinOp LookupTempPerm)
          
    hence RedMaskUpdBpl:
      "red_expr_bpl ctxt m_upd_bpl
                         ns (AbsV (AMask ?mb'))" 
      using \<open>e_f_bpl = _\<close> FieldTy \<open>m_bpl = _\<close> \<open>m_upd_bpl = _\<close>
      by (auto intro!: mask_update_wf_apply[OF MaskUpdateWf] Semantics.RedVar intro: LookupMask RedRcvBpl FieldLookupBpl)

    let ?ns' = "update_var (var_context ctxt) ns m_bpl (AbsV (AMask ?mb'))"

    have RedAstBpl:
       "red_ast_bpl P ctxt ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns) 
                           ((BigBlock name cs str tr, cont), Normal ?ns')"
      using \<open>m_bpl = _\<close> LookupMaskTy TyInterp RedMaskUpdBpl
      by (auto intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssign)
  
    show ?thesis
    proof (cases "r = Null")
      case True
      hence "p = 0"
        using \<open>0 < p \<longrightarrow> r \<noteq> Null\<close> \<open>0 \<le> p\<close> by linarith
      hence "ns = ?ns'"
        using update_var_same_state[OF LookupMask]
        by (simp add: \<open>m_bpl = _\<close>)
      moreover have "\<omega>' = \<omega>"
        using True \<open>\<omega>' \<in> W'\<close> InhAccNormal by fastforce
      ultimately show ?thesis 
        using RedAstBpl StateRelInst2 
        by auto
    next
      case False
      from this obtain a where "r = Address a" 
        using ref.exhaust by auto
      hence InhSingle: "\<omega>' \<in> inhale_perm_single StateCons \<omega> (a, f_vpr) (Some (Abs_prat p))"
        using InhAccNormal 
        by simp        

      let ?\<omega>_perm = "get_mh_total_full \<omega> (a, f_vpr)"       

      from InhSingle have
            "pgte pwrite (padd ?\<omega>_perm (Abs_prat p))" and 
            "\<omega>' = update_mh_loc_total_full \<omega> (a,f_vpr) (padd ?\<omega>_perm (Abs_prat p))"
        unfolding inhale_perm_single_def
        by force+

      have "?mb' = (mask_bpl_upd_normal_field mb (Address a) f_bpl \<tau>_vpr ( mb (r, ?f_bpl_val) + real_of_rat p))"
        unfolding mask_bpl_upd_normal_field_def
        by (simp add: \<open>r = _\<close>)

      have Aux: "mb (r, NormalField f_bpl \<tau>_vpr) + real_of_rat p = real_of_rat (Rep_prat (padd (get_mh_total_full \<omega> (a, f_vpr)) (Abs_prat p)))"
      proof -
        have "(Rep_prat (Abs_prat p)) = p"
          using Abs_prat_inverse \<open>p \<ge> 0\<close> 
          by simp

        have "(Rep_prat (padd (get_mh_total_full \<omega> (a, f_vpr)) (Abs_prat p))) = (Rep_prat (get_mh_total_full \<omega> (a, f_vpr))) + (Rep_prat (Abs_prat p))"
          by (simp add: padd.rep_eq)
        also have "... = (Rep_prat (get_mh_total_full \<omega> (a, f_vpr))) + p"
          using \<open>p \<ge> 0\<close> Abs_prat_inverse
          by simp
        finally show ?thesis
        using MaskRel FieldLookup FieldTr \<open>r = Address a\<close>
        unfolding mask_rel_def
        by (simp add: of_rat_add)
      qed

      have "state_rel (program_total ctxt_vpr) TyRep Tr AuxPred ctxt \<omega>' ?ns'"
        apply (subst \<open>\<omega>' = _\<close>)
        apply (subst \<open>?mb' = _\<close>)
        apply (subst \<open>m_bpl = _\<close>)
        apply (rule state_rel_mask_update_3[OF StateRelInst2])
               apply simp
              apply (simp add: TyInterp)
             apply (simp add: LookupMask)
            apply (rule \<open>pgte pwrite _ \<close>)
           apply (simp add: FieldLookup)
          apply (simp add: FieldTr)
         apply (simp add: TyTr)
        by (simp add: Aux) 
      thus ?thesis
        using RedAstBpl
        by blast
    qed
  qed
qed (simp)

end