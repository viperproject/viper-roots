theory ExhaleRel
  imports ExpRel ExprWfRel TotalViper.ViperBoogieTranslationInterface Simulation
begin

definition exhale_rel :: 
    "('a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'b nstate \<Rightarrow> bool)
     \<Rightarrow> 'a total_context
        \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
           \<Rightarrow> bigblock list \<Rightarrow> 'b econtext_bpl_general \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> bigblock \<times> cont \<Rightarrow> bigblock \<times> cont \<Rightarrow> bool"
  where "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv>
         rel_general (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)) (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>))
           \<comment>\<open>The well-definedness state remains the same\<close>
           (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. (fst \<omega>0_\<omega>) = (fst \<omega>0_\<omega>') \<and> red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) (ExhaleNormal (snd \<omega>0_\<omega>')))
           (\<lambda> \<omega>0_\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) ExhaleFailure)
           P ctxt \<gamma> \<gamma>'"


lemma exhale_rel_intro:
  assumes "\<And> \<omega>0 \<omega> \<omega>' ns. R \<omega>0 \<omega> ns \<Longrightarrow>
                      red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> (ExhaleNormal \<omega>') \<Longrightarrow>
                      \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>0 \<omega>' ns'" and
          "\<And> \<omega>0 \<omega> ns. R \<omega>0 \<omega> ns \<Longrightarrow>
                      red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr \<omega> ExhaleFailure \<Longrightarrow>
                      \<exists>\<gamma>'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
  shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  using assms
  unfolding exhale_rel_def
  by (auto intro: rel_intro)

lemma exhal_rel_normal_elim:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and
          "R \<omega>0 m ns" and
          "red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr m (ExhaleNormal m')"
  shows "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>0 m' ns'"
  using assms
  unfolding exhale_rel_def rel_general_def
  by (metis fst_eqD snd_conv)

lemma exhale_rel_failure_elim:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and
          "R \<omega>0 m ns" and
          "red_exhale ctxt_vpr StateCons \<omega>0 assertion_vpr m ExhaleFailure"
        shows "\<exists>\<gamma>'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"  
  using assms
  unfolding exhale_rel_def rel_general_def
  by (metis fst_conv snd_conv surjective_pairing)

subsection \<open>Propagation rules\<close>

lemma exhale_rel_propagate_pre:
  assumes "\<And> \<omega>0 m ns. R \<omega>0 m ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R \<omega>0 m ns'" and
          "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>1 \<gamma>2"
        shows "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>2"
  using assms(2)
  unfolding exhale_rel_def
  by (auto intro: rel_propagate_pre assms(1))

lemma exhale_rel_propagate_post:
  assumes "exhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega>0 m ns. R \<omega>0 m ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega>0 m ns'"
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
  using RhsRel
  unfolding exhale_rel_def  
proof (rule rel_general_cond[OF rev_iffD1_def[OF wf_rel_inst_eq_1[OF ExpWfRel] wf_rel_inst_def]] )
  show "rel_general (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)) (\<lambda>\<omega>0_\<omega>. R (fst \<omega>0_\<omega>) (snd \<omega>0_\<omega>)) (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>') (\<lambda>_. False) P ctxt (empty_else_block, convert_list_to_cont [] (KSeq next cont)) (next, cont)"
    apply (rule rel_intro)
    using red_ast_bpl_empty_block_2[OF EmptyElse]
    apply fastforce
    by simp
next
  let ?Success = "\<lambda>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<and> red_exhale ctxt_vpr StateCons (fst \<omega>) (assert.Imp cond A) (snd \<omega>) (ExhaleNormal (snd \<omega>'))"
  let ?SuccessExp = "\<lambda>\<omega> \<omega>'. \<omega> = \<omega>' \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"
  let ?SuccessThn = "\<lambda>\<omega> \<omega>'. fst \<omega> = fst \<omega>' \<and> red_exhale ctxt_vpr StateCons (fst \<omega>) A (snd \<omega>) (ExhaleNormal (snd \<omega>'))"
  
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

  let ?Fail ="\<lambda>\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>) (assert.Imp cond A) (snd \<omega>) ExhaleFailure"
  let ?FailThn = "\<lambda>\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>) A (snd \<omega>) ExhaleFailure"
  let ?FailExp = "\<lambda>\<omega>. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

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

(*
lemma inhale_field_acc_rel:
  assumes 
    WfRcv: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" and 
    PosPermRel:  "\<And>p. rel_general R (R' p)
                  (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>' \<and> (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0))
                  (\<lambda> \<omega>. (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0))
                  P ctxt \<gamma>2 \<gamma>3" and
     UpdInhRel: "\<And>p r. rel_general (R' p) R
                  (\<lambda> \<omega> \<omega>'. inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r \<omega> \<omega>')
                  (\<lambda> \<omega>. False) P ctxt \<gamma>3 \<gamma>'" \<comment>\<open>Here, the simulation needs to revert back to R\<close>
  shows "inhale_rel R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"
*)

lemma exhale_field_acc_rel:
  assumes 
    WfRcv: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" 

  shows "exhale_rel R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"

                                          


      
end