theory ExhaleRel
  imports ExpRel ExprWfRel TotalViper.ViperBoogieTranslationInterface Simulation ViperBoogieRelUtil
begin

definition exhale_rel :: 
    "('a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'b nstate \<Rightarrow> bool)
     \<Rightarrow> 'a total_context
        \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
           \<Rightarrow> bigblock list \<Rightarrow> 'b econtext_bpl_general \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> bigblock \<times> cont \<Rightarrow> bigblock \<times> cont \<Rightarrow> bool"
  where "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv>
         rel_general (uncurry R) (uncurry R)
           \<comment>\<open>The well-definedness state remains the same\<close>
           (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. (fst \<omega>0_\<omega>) = (fst \<omega>0_\<omega>') \<and> red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) (RNormal (snd \<omega>0_\<omega>')))
           (\<lambda> \<omega>0_\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) RFailure)
           P ctxt \<gamma> \<gamma>'"

lemma exhale_rel_intro:
  assumes "\<And> \<omega>0 \<omega> \<omega>' ns. R \<omega>0 \<omega> ns \<Longrightarrow>
                      red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
                      \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>0 \<omega>' ns'" and
          "\<And> \<omega>0 \<omega> ns. R \<omega>0 \<omega> ns \<Longrightarrow>
                      red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> RFailure \<Longrightarrow>
                      \<exists>\<gamma>'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
  shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  using assms
  unfolding exhale_rel_def
  by (auto intro: rel_intro)

lemma exhale_rel_intro_2:
  assumes
    "\<And>\<omega>0 \<omega> ns res. 
      R \<omega>0 \<omega> ns \<Longrightarrow> 
      red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> res \<Longrightarrow>
      rel_vpr_aux (\<lambda>\<omega>' ns. R \<omega>0 \<omega>' ns) P ctxt \<gamma> \<gamma>' ns res"
  shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding exhale_rel_def rel_vpr_aux_def
  by (auto intro: rel_intro)

lemma exhale_rel_normal_elim:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and
          "R \<omega>0 \<omega> ns" and
          "red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> (RNormal \<omega>')"
  shows "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>0 \<omega>' ns'"
  using assms
  unfolding exhale_rel_def rel_general_def
  by simp

lemma exhale_rel_failure_elim:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and
          "R \<omega>0 \<omega> ns" and
          "red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> RFailure"
        shows "\<exists>\<gamma>'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"  
  using assms
  unfolding exhale_rel_def rel_general_def
  by simp

subsection \<open>Propagation rules\<close>

lemma exhale_rel_propagate_pre:
  assumes "\<And> \<omega>0 \<omega> ns. R \<omega>0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R \<omega>0 \<omega> ns'" and
          "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>1 \<gamma>2"
        shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>2"
  using assms rel_propagate_pre
  unfolding exhale_rel_def
  by (auto intro: rel_propagate_pre assms(1))

lemma exhale_rel_propagate_post:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega>0 \<omega> ns. R \<omega>0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega>0 \<omega> ns'"
  shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>2"
  using assms
  unfolding exhale_rel_def
  by (auto intro: rel_propagate_post)

subsection \<open>Structural rules\<close>

lemma exhale_rel_star: 
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" and
          "exhale_rel R ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
        shows "exhale_rel R ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
  using assms
  unfolding exhale_rel_def
  apply (rule rel_general_comp)
  by (fastforce elim: ExhStar_case)+

lemma exhale_rel_imp:
  assumes 
   ExpWfRel:          
        "expr_wf_rel R ctxt_vpr StateCons P ctxt cond 
         \<gamma>1
         (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont)" 
        (is "expr_wf_rel _ ctxt_vpr StateCons P ctxt cond _ ?\<gamma>_if") and
   EmptyElse: "is_empty_bigblock empty_else_block" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt cond cond_bpl" and
   RhsRel: "exhale_rel R ctxt_vpr StateCons P ctxt A (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
                (is "exhale_rel R _ _ _ _ _ ?\<gamma>_thn (next, cont)") 
              shows "exhale_rel R ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont)"
  (*using RhsRel*)
  unfolding exhale_rel_def 
  thm rel_general_cond[OF rev_iffD1_def[OF wf_rel_inst_eq_1[OF ExpWfRel] wf_rel_inst_def]]
  thm uncurry.simps
proof (simp only: uncurry.simps, rule rel_general_cond[OF rev_iffD1_def[OF wf_rel_inst_eq_1[OF ExpWfRel] wf_rel_inst_def]])
  show "rel_general (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)) (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)) (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>') (\<lambda>_. False) P ctxt (empty_else_block, convert_list_to_cont [] (KSeq next cont)) (next, cont)"
    apply (rule rel_intro)
    using red_ast_bpl_empty_block_2[OF EmptyElse]
    apply fastforce
    by simp
next
  let ?Success = "\<lambda>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<and> red_exhale ctxt_vpr StateCons (fst \<omega>) (assert.Imp cond A) (snd \<omega>) (RNormal (snd \<omega>'))"
  let ?SuccessExp = "\<lambda>\<omega> \<omega>'. \<omega> = \<omega>' \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"
  let ?SuccessThn = "\<lambda>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<and> red_exhale ctxt_vpr StateCons (fst \<omega>) A (snd \<omega>) (RNormal (snd \<omega>'))"
  let ?Fail ="\<lambda>\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>) (assert.Imp cond A) (snd \<omega>) RFailure"
  let ?FailThn = "\<lambda>\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>) A (snd \<omega>) RFailure"
  let ?FailExp = "\<lambda>\<omega>. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

  show "rel_general (\<lambda>a. R (fst a) (snd a)) (\<lambda>a. R (fst a) (snd a)) ?SuccessThn ?FailThn P ctxt (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
    using RhsRel
    unfolding exhale_rel_def
    by simp
  
  show "\<And> \<omega> \<omega>' ns. ?Success \<omega> \<omega>' \<Longrightarrow> R (fst \<omega>) (snd \<omega>) ns \<Longrightarrow>
                        ?SuccessExp \<omega> \<omega> \<and> \<comment>\<open>implicit assumption that success of conditional does not lead to side effects\<close>
                       ((red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> ?SuccessThn \<omega> \<omega>') \<or> 
                       (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> \<omega> = \<omega>'))"
  proof - 
    fix \<omega> \<omega>' ns
    assume Success:"?Success \<omega> \<omega>'" and R: "R (fst \<omega>) (snd \<omega>) ns"
    from conjunct2[OF \<open>?Success \<omega> \<omega>'\<close>]
    show "?SuccessExp \<omega> \<omega> \<and> \<comment>\<open>implicit assumption that success of conditional does not lead to side effects\<close>
                       ((red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> ?SuccessThn \<omega> \<omega>') \<or> 
                       (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> \<omega> = \<omega>'))"
      apply cases
       apply (rule conjI)
      apply blast
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] Success
      apply (metis R val_rel_vpr_bpl.simps(2))
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] Success
      by (metis R prod_eqI val_rel_vpr_bpl.simps(2))
  qed

 show "\<And> \<omega> ns. ?Fail \<omega> \<Longrightarrow> R (fst \<omega>) (snd \<omega>) ns \<Longrightarrow> 
               ?FailExp \<omega> \<or>
               (?SuccessExp \<omega> \<omega> \<and>
                 ( (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> ?FailThn \<omega>) \<or> 
                   (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> False) )
               )"
 proof -
   fix \<omega> ns
   assume Fail: "?Fail \<omega>" and "R (fst \<omega>) (snd \<omega>) ns" 
   thus "?FailExp \<omega> \<or>
               (?SuccessExp \<omega> \<omega> \<and>
                 ( (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> ?FailThn \<omega>) \<or> 
                   (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> False) )
               )"
     apply cases
     using exp_rel_vpr_bpl_elim_2[OF ExpRel] Fail
      apply (metis val_rel_vpr_bpl.simps(2))
     by fast
 qed
qed

subsection \<open>Field access predicate rule\<close>

definition exhale_field_acc_rel_perm_success
  where "exhale_field_acc_rel_perm_success ctxt_vpr StateCons \<omega> r p f \<equiv>
          p \<ge> 0 \<and>
         (if r = Null then p = 0 else (Rep_prat (get_mh_total_full \<omega> (the_address r,f))) \<ge> p)"

definition exhale_field_acc_rel_assms
  where "exhale_field_acc_rel_assms ctxt StateCons e_r f e_p r p \<omega>0 \<omega>  \<equiv>
            ctxt, StateCons, Some \<omega>0 \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<and>
            ctxt, StateCons, Some \<omega>0 \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"

lemma exhale_field_acc_rel_assms_perm_eval:
  assumes "exhale_field_acc_rel_assms ctxt StateCons e_r f e_p r p \<omega>0 \<omega>"
  shows "ctxt, StateCons, Some \<omega>0 \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
  using assms
  unfolding exhale_field_acc_rel_assms_def
  by blast

lemma exhale_field_acc_rel_assms_ref_eval:
  assumes "exhale_field_acc_rel_assms ctxt StateCons e_r f e_p r p \<omega>0 \<omega>"
  shows "ctxt, StateCons, Some \<omega>0 \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
  using assms
  unfolding exhale_field_acc_rel_assms_def
  by blast

definition exhale_acc_normal_premise
  where "exhale_acc_normal_premise ctxt StateCons e_r f e_p p r \<omega>0 \<omega> \<omega>' \<equiv>
       exhale_field_acc_rel_assms ctxt StateCons e_r f e_p r p \<omega>0 \<omega>  \<and>
       exhale_field_acc_rel_perm_success ctxt StateCons \<omega> r p f \<and>
       (if r = Null then \<omega>' = \<omega> else
          let mh = get_mh_total_full \<omega> in 
              \<omega>' = update_mh_loc_total_full \<omega> (the_address r,f) (psub (mh (the_address r,f)) (Abs_prat p))
       )"

lemma exhale_field_acc_rel:
  assumes 
    WfRcv: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" and
    CorrectPermRel:  
            "\<And>r p. rel_general (uncurry R) (R' r p)
                  (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. \<omega>0_\<omega> = \<omega>0_\<omega>' \<and> 
                                  exhale_field_acc_rel_assms ctxt_vpr StateCons e_rcv_vpr f e_p r p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)  \<and>
                                  exhale_field_acc_rel_perm_success ctxt_vpr StateCons (snd \<omega>0_\<omega>) r p f)
                  (\<lambda> \<omega>0_\<omega>. exhale_field_acc_rel_assms ctxt_vpr StateCons e_rcv_vpr f e_p r p (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) \<and>
                           \<not> exhale_field_acc_rel_perm_success ctxt_vpr StateCons  (snd \<omega>0_\<omega>) r p f)
                  P ctxt \<gamma>2 \<gamma>3" and
    
    UpdExhRel: "\<And>r p. rel_general (R' r p) (uncurry R) \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                      (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. fst \<omega>0_\<omega> = fst \<omega>0_\<omega>' \<and> exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) (snd \<omega>0_\<omega>'))
                      (\<lambda>_. False) 
                      P ctxt \<gamma>3 \<gamma>'"
  shows "exhale_rel R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"
proof (rule exhale_rel_intro_2)
  fix \<omega>0 \<omega> ns res
  assume R0:"R \<omega>0 \<omega> ns" 
  assume "red_exhale ctxt_vpr StateCons \<omega>0 (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega> res"
  
  thus "rel_vpr_aux (R \<omega>0) P ctxt \<gamma> \<gamma>' ns res"
  proof cases
    case (ExhAcc mh r p a)
    from this obtain ns1 where R1: "R \<omega>0 \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF WfRcv R0]
      by blast
    with ExhAcc obtain ns2 where "R \<omega>0 \<omega> ns2" and Red2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF WfPerm R1] red_ast_bpl_transitive
      by blast

    hence R2_conv:"uncurry R (\<omega>0, \<omega>) ns2"
      by simp

    have BasicAssms: "exhale_field_acc_rel_assms ctxt_vpr StateCons e_rcv_vpr f e_p r p \<omega>0 \<omega>"
        unfolding exhale_field_acc_rel_assms_def
        using ExhAcc
        by blast

    show ?thesis
    proof (rule rel_vpr_aux_intro)
      \<comment>\<open>Normal case\<close>
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      with ExhAcc have PermCorrect: "0 \<le> p \<and> (if (r = Null) then (p = 0) else (pgte (mh (a, f)) (Abs_prat p)))"
        using exh_if_total_failure by fastforce \<comment>\<open>using exh_if_total_normal seems to be surprisingly slower\<close>
      hence PermSuccess: "exhale_field_acc_rel_perm_success ctxt_vpr StateCons \<omega> r p f"
        unfolding exhale_field_acc_rel_perm_success_def
        using \<open>mh = _\<close> \<open>a = _\<close> pgte.rep_eq Abs_prat_inverse
        by auto
      from this obtain ns3 where Red3: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>3, Normal ns3)" and R3: "R' r p (\<omega>0, \<omega>) ns3"
        using BasicAssms rel_success_elim[OF CorrectPermRel R2_conv] red_ast_bpl_transitive[OF Red2]
        by (metis fst_eqD snd_eqD)

      from ExhAcc BasicAssms PermSuccess \<open>res = RNormal \<omega>'\<close> have
        NormalPremise: "exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r \<omega>0 \<omega> \<omega>'"
         unfolding exhale_acc_normal_premise_def
         using exh_if_total_normal_2 \<open>res = exh_if_total _ _\<close> \<open>res = RNormal \<omega>'\<close>
         by fastforce
        
       thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>0 \<omega>' ns'"
         using rel_success_elim[OF UpdExhRel R3] red_ast_bpl_transitive[OF Red3] 
         by (metis (no_types, lifting) old.prod.inject prod.collapse uncurry.elims)
    next 
      \<comment>\<open>Failure case\<close>
      assume "res = RFailure"
      with ExhAcc have PermCorrect: "\<not> (0 \<le> p \<and> (if (r = Null) then (p = 0) else (pgte (mh (a, f)) (Abs_prat p))))"
        using exh_if_total_failure by fastforce \<comment>\<open>using exh_if_total_normal seems to be surprisingly slower\<close>
      thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
        using ExhAcc BasicAssms rel_failure_elim[OF CorrectPermRel R2_conv] red_ast_bpl_transitive[OF Red2]
              Abs_prat_inverse pgte.rep_eq
        unfolding exhale_field_acc_rel_perm_success_def        
        by (metis fst_conv mem_Collect_eq snd_conv)
    qed
  next
    case SubAtomicFailure
    hence SubexpFailCases: 
          "ctxt_vpr, StateCons, Some \<omega>0 \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
           (\<exists>v. ctxt_vpr, StateCons, Some \<omega>0 \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> 
                ctxt_vpr, StateCons, Some \<omega>0 \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
      by (auto elim: red_exp_list_failure_elim)

    show ?thesis
    proof (rule rel_vpr_aux_intro)
      show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      proof (cases "ctxt_vpr, StateCons, Some \<omega>0 \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure")
        case True
        then show ?thesis 
          using wf_rel_failure_elim[OF WfRcv \<open>R \<omega>0 \<omega> ns\<close>]
          by blast          
      next
        case False
        then show ?thesis 
          using wf_rel_normal_elim[OF WfRcv \<open>R \<omega>0 \<omega> ns\<close>]
                wf_rel_failure_elim[OF WfPerm] SubexpFailCases red_ast_bpl_transitive
          by blast
      qed
    qed (simp add: \<open>res = _\<close>)
  qed
qed

lemma psub_smaller:
  assumes "pgte p q"
  shows "pgte p (psub p q)"
  unfolding psub_def
proof -
  from assms have DiffNonNegative: "Rep_prat p - Rep_prat q \<ge> 0"
    by (transfer) simp

  have "Rep_prat p \<ge> Rep_prat p - Rep_prat q"
    by (transfer) simp
  

  hence "(Rep_prat p) \<ge> Rep_prat (Abs_prat (Rep_prat p - Rep_prat q))"
    using Abs_prat_inverse DiffNonNegative
    by fastforce
    
  thus "pgte p (Abs_prat (Rep_prat p - Rep_prat q))"    
    by (simp add: pgte.rep_eq)
qed
  
lemma exhale_rel_field_acc_upd_rel:
assumes StateRel: "\<And> \<omega>0_\<omega> ns. R \<omega>0_\<omega> ns \<Longrightarrow>                            
                           state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) ns" and
        "temp_perm \<notin> dom AuxPred" and
    WfTyRep:  "wf_ty_repr_bpl TyRep" and
    MaskDefDifferent: "mask_var_def Tr \<noteq> mask_var Tr" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
                   "new_perm = (mask_read_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<guillemotleft>Lang.Sub\<guillemotright> (Var temp_perm)" and
    MaskVar: "m_bpl = mask_var Tr " and
    FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
    RcvRel: "exp_rel_vpr_bpl (state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt) ctxt_vpr ctxt e_rcv_vpr e_rcv_bpl"
shows "rel_general R (uncurry (state_rel Pr TyRep Tr AuxPred ctxt)) 
                      (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. fst \<omega>0_\<omega> = fst \<omega>0_\<omega>' \<and> exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>) (snd \<omega>0_\<omega>'))
                      (\<lambda>_. False)
                      P ctxt 
                      (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont)
                      (BigBlock name cs str tr, cont)"
proof (rule rel_general_conseq_output,
       rule mask_upd_rel[OF StateRel WfTyRep TyInterp MaskUpdateWf MaskUpdateBpl MaskVar FieldRelSingle])
  fix \<omega>0_\<omega>def \<omega>' ns
  assume "fst \<omega>0_\<omega>def = fst \<omega>' \<and> exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r (fst \<omega>0_\<omega>def) (snd \<omega>0_\<omega>def) (snd \<omega>')"
  thus "fst \<omega>' = (if (mask_var_def Tr = mask_var Tr \<and> r \<noteq> Null) then (snd \<omega>') else (fst \<omega>0_\<omega>def)) \<and>

         snd \<omega>' = (if (r = Null) then (snd \<omega>0_\<omega>def) else (update_mh_loc_total_full (snd \<omega>0_\<omega>def) (the_address r, f)
                                                   (psub (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r,f)) (Abs_prat p))))"
    using MaskDefDifferent
    unfolding exhale_acc_normal_premise_def exhale_field_acc_rel_perm_success_def
    by presburger
next
  fix \<omega>0_\<omega>def \<omega>' ns
  assume R:"R \<omega>0_\<omega>def ns"
  assume "fst \<omega>0_\<omega>def = fst \<omega>' \<and> exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r (fst \<omega>0_\<omega>def) (snd \<omega>0_\<omega>def) (snd \<omega>')"
  thus "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))"
    using RcvRel StateRel[OF R]
    unfolding exhale_acc_normal_premise_def exhale_field_acc_rel_assms_def
    by (fastforce elim: exp_rel_vpr_bpl_elim_2)
next
  fix \<omega>0_\<omega>def \<omega>' ns
  assume R:"R \<omega>0_\<omega>def ns" and
        ExhPremise:
            "fst \<omega>0_\<omega>def = fst \<omega>' \<and> 
            exhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r (fst \<omega>0_\<omega>def) (snd \<omega>0_\<omega>def) (snd \<omega>')"

  note StateRelInst = StateRel[OF R]
 
  have LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some (RealV (real_of_rat p))"
       using state_rel_aux_pred_sat_lookup_2[OF StateRelInst]
       unfolding pred_eq_def      
       by (metis (full_types) fun_upd_same)
  
  from ExhPremise have 
    "p \<ge> 0" and
    RedRcvVpr: "ctxt_vpr, StateCons, Some (fst \<omega>0_\<omega>def) \<turnstile> \<langle>e_rcv_vpr; snd \<omega>0_\<omega>def\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
    EnoughPerm: "(if r = Null then p = 0 else (Rep_prat (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r,f))) \<ge> p)"
    unfolding exhale_acc_normal_premise_def exhale_field_acc_rel_perm_success_def exhale_field_acc_rel_assms_def
    by blast+

  hence PermAtMostOne: "pgte pwrite (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r, f))"
    using state_rel_wf_mask_simple[OF StateRelInst]
    unfolding wf_mask_simple_def
    by simp

  have "red_expr_bpl ctxt new_perm ns
        (if (r = Null) then (RealV 0) else 
                            (RealV (real_of_rat (Rep_prat (psub (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r, f)) (Abs_prat p))))))"
        (is ?conjunct1)
    apply (subst \<open>new_perm = _\<close>)
    apply (rule RedBinOp)
      apply (rule exp_rel_perm_access_2[OF MaskReadWf StateRelInst RedRcvVpr FieldRelSingle])
         apply simp
        apply simp
       apply (rule RcvRel)
      apply (simp add: \<open>m_bpl = _\<close>)
     apply (fastforce intro: RedVar LookupTempPerm)
    apply (cases "r = Null")
    using EnoughPerm
     apply simp

    apply simp
    using \<open>p \<ge> 0\<close> psub_aux Abs_prat_inverse
    by (metis EnoughPerm get_mh_total_full.simps of_rat_less_eq) 

  moreover have "(r \<noteq> Null \<longrightarrow> pgte pwrite (psub (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r, f)) (Abs_prat p)))" 
        (is ?conjunct2)
  proof (rule impI)
    assume "r \<noteq> Null"
    hence "pgte (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r,f)) (Abs_prat p)"
      using \<open>p \<ge> 0\<close> Abs_prat_inverse EnoughPerm
      by (simp add: pgte.rep_eq)
    thus "pgte pwrite (psub (get_mh_total_full (snd \<omega>0_\<omega>def) (the_address r, f)) (Abs_prat p))"
      using PermAtMostOne psub_smaller PermAtMostOne pgte_transitive
      by blast
  qed

  ultimately show "?conjunct1 \<and> ?conjunct2"
    by blast
next
  fix \<omega>0_\<omega>def' ns
  assume "uncurry (state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt) \<omega>0_\<omega>def' ns"
  thus "uncurry (state_rel Pr TyRep Tr AuxPred ctxt) \<omega>0_\<omega>def' ns"
    using \<open>temp_perm \<notin> _\<close> state_rel_aux_pred_remove
    using map_add_upd_left map_le_def by fastforce
qed (auto)

    

end