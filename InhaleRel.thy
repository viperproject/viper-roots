theory InhaleRel
  imports ExpRel ExprWfRel ViperBoogieTranslationInterface Simulation ViperBoogieRelUtil
begin

definition inhale_rel ::
     "('a full_total_state \<Rightarrow> 'a vbpl_absval nstate \<Rightarrow> bool)
     \<Rightarrow> (assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool)
     \<Rightarrow> 'a total_context
        \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
           \<Rightarrow> bigblock list
                    \<Rightarrow> 'a econtext_bpl
                       \<Rightarrow> assertion
                          \<Rightarrow> bigblock \<times> cont \<Rightarrow> bigblock \<times> cont \<Rightarrow> bool"
  where "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv>
         rel_general (\<lambda> \<omega> ns. R \<omega> ns \<and> Q assertion_vpr \<omega>)  R 
           (\<lambda> \<omega> \<omega>'. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>'))
           (\<lambda> \<omega>. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure)
           P ctxt \<gamma> \<gamma>'"
    
lemma inhale_rel_intro:
  assumes
    "\<And>\<omega> ns \<omega>'. 
      R \<omega> ns \<Longrightarrow> 
      Q assertion_vpr \<omega> \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
      (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and
    "\<And>\<omega> ns.
      R \<omega> ns \<Longrightarrow>
      Q assertion_vpr \<omega> \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure \<Longrightarrow>
      (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_intro)

lemma inhale_rel_intro_2:
  assumes
    "\<And>\<omega> ns res. 
      R \<omega> ns \<Longrightarrow> 
      Q assertion_vpr \<omega> \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> res \<Longrightarrow>
      rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res"
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def rel_vpr_aux_def
  by (auto intro: rel_intro)

lemma inhale_rel_normal_elim:
  assumes "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "Q assertion_vpr \<omega>"
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>')"
  shows "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns')"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_success_elim)

lemma inhale_rel_failure_elim:
  assumes "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "Q assertion_vpr \<omega>" and
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure"
  shows "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  using assms
  unfolding inhale_rel_def rel_general_def
  by auto

subsection \<open>Inhale relation invariant\<close>

definition is_inh_rel_invariant
  where "is_inh_rel_invariant ctxt StateCons Q  \<equiv>
          (\<forall> A1 A2 \<omega>. Q (A1 && A2) \<omega> \<longrightarrow> 
                  (Q A1 \<omega>) \<and>
                  (\<forall>\<omega>'. red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>') \<longrightarrow> Q A2 \<omega>')) \<and>
          (\<forall> e A \<omega>. Q (assert.Imp e A) \<omega> \<longrightarrow> ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)) \<longrightarrow> Q A \<omega>)"

lemma is_inh_rel_invariant_intro:
  assumes "\<And> A1 A2 \<omega>. Q (A1 && A2) \<omega> \<Longrightarrow> Q A1 \<omega>" and
          "\<And> A1 A2 \<omega> \<omega>'. Q (A1 && A2) \<omega> \<Longrightarrow> red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>') \<Longrightarrow> Q A2 \<omega>'" and
          "\<And> e A \<omega>. Q (assert.Imp e A) \<omega> \<Longrightarrow> 
                    ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)) \<Longrightarrow> Q A \<omega>"
        shows "is_inh_rel_invariant ctxt StateCons Q"
  using assms
  unfolding is_inh_rel_invariant_def
  by blast

subsubsection \<open>Invariant instantiations\<close>

lemma is_assertion_red_invariant_inh:
  "is_inh_rel_invariant ctxt_vpr StateCons (assertion_framing_state ctxt_vpr StateCons)"
  by (blast intro: is_inh_rel_invariant_intro dest: assertion_framing_star assertion_framing_imp)

subsection \<open>Propagation rules\<close>

lemma inhale_propagate_pre:
  assumes PropagateBpl: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q assertion_vpr \<omega> \<Longrightarrow>
               \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R \<omega> ns'"
      and InhRel: "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>1 \<gamma>2"
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>2"   
  unfolding inhale_rel_def
  apply (rule rel_propagate_pre[OF _ InhRel[simplified inhale_rel_def]])
  by (fastforce intro: PropagateBpl)

lemma inhale_propagate_post:
  assumes "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>1" 
      and "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega> ns'"
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt assertion_vpr \<gamma>0 \<gamma>2"
  using assms rel_propagate_post
  unfolding inhale_rel_def
  by blast

subsection \<open>Structural rules\<close>

lemma inhale_rel_star: 
  assumes Invariant1: "\<And> \<omega>. Q (A1 && A2) \<omega> \<Longrightarrow> Q A1 \<omega>"
      and Invariant2: "\<And> \<omega> \<omega>'. Q (A1 && A2) \<omega> \<Longrightarrow> red_inhale ctxt_vpr StateCons A1 \<omega> (RNormal \<omega>') \<Longrightarrow> Q A2 \<omega>'"
      and InhRelA1: "inhale_rel R Q ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" 
      and InhRelA2: "inhale_rel R Q ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
    shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
  text\<open>Idea of proof:
       \<^item> use general composition rule where the intermediate relation is chosen to be \<^term>\<open>\<lambda>\<omega> ns. R \<omega> ns \<and> Q A2 \<omega>\<close>
       \<^item> Prove the first premise by weakening the input relation from \<^term>\<open>\<lambda>\<omega> ns. R \<omega> ns \<and> Q (A1 && A2) \<omega>\<close> to \<^term>\<open>\<lambda>\<omega> ns. R \<omega> ns \<and> Q A1 \<omega>\<close>
         and by adjusting the output relation \<^term>\<open>\<lambda>\<omega> ns. R \<omega> ns \<and> Q A2 \<omega>\<close> to \<^term>\<open>R\<close> (\<^term>\<open>R\<close> is strong enough
         given the additional assumptions when adjusting the output relation)\<close>
  unfolding inhale_rel_def
  apply (rule rel_general_comp[where ?R2.0="\<lambda>\<omega> ns. R \<omega> ns \<and> Q A2 \<omega>"])
     apply (rule rel_general_conseq_input_output)
       apply (rule InhRelA1[simplified inhale_rel_def])
      apply (simp add: Invariant1)
     apply (fastforce dest: Invariant2)
    apply (rule InhRelA2[simplified inhale_rel_def])
  by (auto elim: InhStar_case)

lemma inhale_rel_star_2: 
  assumes Invariant: "is_inh_rel_invariant ctxt_vpr StateCons Q"
      and InhRelA1: "inhale_rel R Q ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" 
      and InhRelA2: "inhale_rel R Q ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
    shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
  using assms
  unfolding is_inh_rel_invariant_def
  by (blast intro!: inhale_rel_star)

lemma inhale_rel_imp:
  assumes Invariant: "\<And>\<omega>. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)) \<Longrightarrow> Q (assert.Imp cond A) \<omega> \<Longrightarrow> Q A \<omega>"
      and ExpWfRel:          
          "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns \<and> Q (assert.Imp cond A) \<omega>) ctxt_vpr StateCons P ctxt cond 
            \<gamma>1
            (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont)" 
        (is "expr_wf_rel _ ctxt_vpr StateCons P ctxt cond _ ?\<gamma>_if")
      and EmptyElse: "is_empty_bigblock empty_else_block"
      and ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl"
      and RhsRel: "inhale_rel R Q ctxt_vpr StateCons P ctxt A (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" 
                 (is "inhale_rel R Q _ _ _ _ _ ?\<gamma>_thn (next, cont)")
    shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont)"
  unfolding inhale_rel_def
proof (rule rel_general_cond,
       fastforce intro: rel_general_conseq_input_output[OF wf_rel_general_1[OF ExpWfRel]],
       rule RhsRel[simplified inhale_rel_def])
  show "rel_general R R (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>') (\<lambda>_. False) P ctxt (empty_else_block, convert_list_to_cont [] (KSeq next cont)) (next, cont)"
    apply (rule rel_intro)
    using red_ast_bpl_empty_block_2[OF EmptyElse]
    apply fastforce
    by simp
next
  fix \<omega> \<omega>' ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> (RNormal \<omega>')" and "R \<omega> ns \<and> Q (assert.Imp cond A) \<omega>"
  thus "((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> (R \<omega> ns \<and> Q A \<omega>) \<and> red_inhale ctxt_vpr StateCons A \<omega> (RNormal \<omega>') \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R \<omega> ns \<and> \<omega> = \<omega>')"
    apply (cases)
    using ExpRel
    by (fastforce elim: exp_rel_vpr_bpl_elim_2 simp: Invariant)+
next
  fix \<omega> ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> RFailure" and "R \<omega> ns \<and> Q (assert.Imp cond A) \<omega>"
  thus "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
       ((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> (R \<omega> ns \<and> Q A \<omega>) \<and> red_inhale ctxt_vpr StateCons A \<omega> RFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R \<omega> ns \<and> False)"
    apply (cases)
    using ExpRel
    by (fastforce elim: exp_rel_vpr_bpl_elim_2 simp: Invariant)+
qed

lemma inhale_rel_imp_2:
  assumes Invariant: "is_inh_rel_invariant ctxt_vpr StateCons Q"
      and ExpWfRel:          
          "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns \<and> Q (assert.Imp cond A) \<omega>) ctxt_vpr StateCons P ctxt cond 
            \<gamma>1
            (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont)" 
        (is "expr_wf_rel _ ctxt_vpr StateCons P ctxt cond _ ?\<gamma>_if")
      and EmptyElse: "is_empty_bigblock empty_else_block"
      and ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl"
      and RhsRel: "inhale_rel R Q ctxt_vpr StateCons P ctxt A (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" 
                 (is "inhale_rel R Q _ _ _ _ _ ?\<gamma>_thn (next, cont)")
    shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont)"
  using assms
  unfolding is_inh_rel_invariant_def
  by (blast intro!: inhale_rel_imp)

subsection \<open>Field access predicate rule\<close>

definition inhale_acc_normal_premise
  where "inhale_acc_normal_premise ctxt StateCons e_r f e_p p r \<omega> \<omega>' \<equiv>
       ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<and>
       ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> 
       p \<ge> 0 \<and>
       (p > 0 \<longrightarrow> r \<noteq> Null) \<and>
       (let W' = (if r = Null then {\<omega>} else inhale_perm_single StateCons \<omega> (the_address r,f) (Some (Abs_prat p))) in
       (W' \<noteq> {} \<and> \<omega>' \<in> W'))" 

lemma inhale_acc_normal_premise_red_inhale:
  assumes "inhale_acc_normal_premise ctxt StateCons e_r f e_p p r \<omega> \<omega>'"
  shows "red_inhale ctxt StateCons (Atomic (Acc e_r f (PureExp e_p))) \<omega> (RNormal \<omega>')"
  apply (rule InhAcc)
     apply (insert assms[simplified inhale_acc_normal_premise_def])
     apply blast
    apply blast
   apply blast  
  apply (rule THResultNormal_alt)
    apply metis
   apply argo
  by meson

lemma inhale_field_acc_rel:
  assumes 
    WfRcv: "expr_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega> ns \<and> \<omega>def = \<omega> \<and> Q (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega>) 
                        ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega> ns \<and> \<omega>def = \<omega> \<and> Q (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega>)
                        ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" and 
    PosPermRel:  "\<And>p. rel_general R (R' p)
                  (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>' \<and> (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0))
                  (\<lambda> \<omega>. (ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0))
                  P ctxt \<gamma>2 \<gamma>3" and
     UpdInhRel: "\<And>p r. rel_general (R' p) R \<comment>\<open>Here, the simulation needs to revert back to R\<close>
                  (inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r)
                  (\<lambda> \<omega>. False) P ctxt \<gamma>3 \<gamma>'" 
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"
proof (rule inhale_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and "Q (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega>"
  hence Rext0: "state_rel_ext R \<omega> \<omega> ns"
    by simp

  assume RedInh: "red_inhale ctxt_vpr StateCons (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega> res"
  thus "rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res"
  proof (cases)
    case (InhAcc r p W')
    from this obtain ns1 where Rext1: "state_rel_ext R \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF WfRcv] Rext0 \<open>Q _ \<omega>\<close>
      by blast
    moreover obtain ns2 where "state_rel_ext R \<omega> \<omega> ns2" and  "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)"
      using InhAcc wf_rel_normal_elim[OF WfPerm] Rext1 \<open>Q _ \<omega>\<close>
      by blast
    ultimately have "R \<omega> ns2" and Red2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using red_ast_bpl_transitive
      by blast+

    show ?thesis
    proof (rule rel_vpr_aux_intro)
      \<comment>\<open>Normal case\<close>
      
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      hence "0 \<le> p" and "W' \<noteq> {}" and "0 < p \<longrightarrow> r \<noteq> Null" and "\<omega>' \<in> W'"
      using th_result_rel_normal InhAcc
      by blast+

      with InhAcc and \<open>res = _\<close> have InhNormalPremise:"inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f e_p p r \<omega> \<omega>'"
        unfolding inhale_acc_normal_premise_def 
        by presburger
    
      from InhAcc \<open>0 \<le> p\<close> obtain ns3 where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>3, Normal ns3)" and "R' p \<omega> ns3" 
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
    from this consider 
          (RcvFail) "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure" |
          (RcvNormal) "\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> 
                           ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      by (auto elim: red_exp_list_failure_elim)  
    thus ?thesis
    proof (cases)
      case RcvFail
      then show ?thesis 
        using  \<open>R \<omega> ns\<close> \<open>Q _ \<omega>\<close> wf_rel_failure_elim[OF WfRcv]        
        unfolding \<open>res = _\<close>
        by (auto intro!: rel_vpr_aux_intro)
    next
      case RcvNormal
      with wf_rel_normal_elim[OF WfRcv] \<open>R \<omega> ns\<close> \<open>Q _ \<omega>\<close>
      obtain ns' where "R \<omega> ns'" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns')"
        by blast

      moreover from RcvNormal wf_rel_failure_elim[OF WfPerm] \<open>R \<omega> ns'\<close> \<open>Q _ \<omega>\<close> obtain c' where
        "red_ast_bpl P ctxt (\<gamma>1, Normal ns') c' \<and> snd c' = Failure"
        by blast

      ultimately show ?thesis 
        using red_ast_bpl_transitive
        unfolding rel_vpr_aux_def \<open>res = _\<close>
        by blast        
    qed
  qed
qed

lemma pos_perm_rel_trivial_inh:
  assumes  "e_p = ELit lit" and
           "val_of_lit lit = ((VPerm p2) :: 'a ValueAndBasicState.val)" and
           "p2 \<ge> 0"
  shows "rel_general R
                     R
       (\<lambda>\<omega> \<omega>'. \<omega> = \<omega>' \<and> ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> 0 \<le> p)
       (\<lambda>\<omega>. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p :: 'a ValueAndBasicState.val) \<and> p < 0) P ctxt
       \<gamma> \<gamma>"
  apply (rule rel_general_success_refl)
  using assms TotalExpressions.RedLit_case extended_val.inject 
   apply fastforce
  by simp

lemma pos_perm_rel_nontrivial_inh:
assumes "zero_perm = const_repr Tr CNoPerm"
shows "rel_general (state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt)
                   (state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt)
     (\<lambda>\<omega> \<omega>'. \<omega> = \<omega>' \<and> ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> 0 \<le> p)
     (\<lambda>\<omega>. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> p < 0) P ctxt
     (BigBlock name (cmd.Assert (expr.Var temp_perm \<guillemotleft>Ge\<guillemotright> expr.Var zero_perm) # cs) s tr, cont)
     (BigBlock name cs s tr, cont)" (is "rel_general ?R ?R ?Success ?Fail P ctxt ?\<gamma> ?\<gamma>'")
  apply (rule rel_general_convert)
  apply (rule pos_perm_rel_nontrivial)
     apply (rule \<open>zero_perm = _\<close>)
    apply simp  
   apply force
  by simp

lemma inhale_rcv_lookup:
  assumes "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns" and
          "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'" and
          ExpRel: "exp_rel_vpr_bpl (state_rel_ext (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt))
                          ctxt_vpr ctxt e_rcv_vpr e_rcv_bpl" 
        shows "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))" 
  using assms(1-2) exp_rel_vpr_bpl_elim_2[OF ExpRel] 
  unfolding inhale_acc_normal_premise_def  
  by (metis val_rel_vpr_bpl.simps(3))

lemma inhale_field_acc_non_null_rcv_rel:
  assumes  StateRel: "state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega> ns" (is "?R \<omega> ns") and
       InhAccNormal: "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'" and
 RcvRel: "exp_rel_vpr_bpl (state_rel_ext (state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt)) 
                          ctxt_vpr ctxt e_rcv_vpr e_rcv_bpl" and
 NullConst: "null_const = const_repr Tr CNull" and
 NoPermConst: "no_perm_const = const_repr Tr CNoPerm"
  shows 
          "\<exists>ns'. red_ast_bpl P ctxt 
               ( (BigBlock name ((Assume (((Var temp_perm) \<guillemotleft>Gt\<guillemotright> (Var no_perm_const)) \<guillemotleft>Imp\<guillemotright> (e_rcv_bpl \<guillemotleft>Neq\<guillemotright> Var null_const))) # cs) str tr, cont) , Normal ns) 
                ( (BigBlock name cs str tr, cont), Normal ns') \<and> 
                 ?R \<omega> ns'" (is "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> ?R _ _")
proof (rule exI[where ?x="ns"])
  from InhAccNormal exp_rel_vpr_bpl_elim_2[OF RcvRel] \<open>?R \<omega> ns\<close> have RedRcvBpl: "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))"
    unfolding inhale_acc_normal_premise_def
    by (metis val_rel_vpr_bpl.simps(3))

  from \<open>?R \<omega> ns\<close> have LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some (RealV (real_of_rat p))"
    using state_rel_aux_pred_sat_lookup_2
    unfolding pred_eq_def      
    by (metis (full_types) fun_upd_same)

  from InhAccNormal have "p > 0 \<longrightarrow> r \<noteq> Null"
    unfolding inhale_acc_normal_premise_def
    by blast


  have "red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns)"
    apply (rule red_ast_bpl_one_simple_cmd)
    by (fastforce intro!: Semantics.RedAssumeOk RedVar Semantics.RedBinOp LookupTempPerm boogie_const_rel_lookup[OF state_rel0_boogie_const_rel[OF state_rel_state_rel0[OF \<open>?R \<omega> ns\<close>]]] 
                 intro: RedRcvBpl
                 simp: \<open>p > 0 \<longrightarrow> r \<noteq> Null\<close> \<open>null_const = _\<close> \<open>no_perm_const = _\<close>)

  thus "red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns) \<and> ?R \<omega> ns"
    using StateRel
    by blast
qed

lemma inhale_rel_field_acc_upd_rel:
  assumes
    StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>                            
                           state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega> ns" and
              "temp_perm \<notin> dom AuxPred" and
    WfConsistency: "wf_total_consistency ctxt_vpr StateCons Rt"  and
    WfTyRep:  "wf_ty_repr_bpl TyRep" and
    MaskVarDefSame: "mask_var_def Tr = mask_var Tr" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
                   "new_perm = (mask_read_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<guillemotleft>Lang.Add\<guillemotright> (Var temp_perm)" and
    MaskVar: "m_bpl = mask_var Tr " and
    FieldRelSingle: "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    RcvRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt) ctxt_vpr ctxt e_rcv_vpr e_rcv_bpl"
  shows "rel_general R 
                  (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
                  (\<lambda> \<omega> \<omega>'. inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>')
                  (\<lambda> \<omega>. False) P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
proof (rule rel_general_conseq_output,
       rule mask_upd_rel_2[OF StateRel _ WfTyRep MaskVarDefSame TyInterp MaskUpdateWf MaskUpdateBpl MaskVar FieldRelSingle])
  fix \<omega> ns
  assume "R \<omega> ns"
  thus "R \<omega> ns"
    by simp
next
  let ?lh = "(the_address r, f_vpr)"
  fix \<omega> \<omega>'
  assume InhPremise: "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'"
  hence 
    "\<omega>' \<in> (if (r = Null) then {\<omega>} else (inhale_perm_single StateCons \<omega> ?lh (Some (Abs_prat p))))"
       (is "\<omega>' \<in> ?W'")
    unfolding inhale_acc_normal_premise_def
    by metis

  show " \<omega>' = ite_vc (r = Null) \<omega> (update_mh_loc_total_full \<omega> ?lh (padd (get_mh_total_full \<omega> (the_address r, f_vpr)) (Abs_prat p)))"
   
  proof (cases "r = Null")
    case True
    then show ?thesis 
      using InhPremise
      unfolding inhale_acc_normal_premise_def
      by simp
  next
    case False
    have "inhale_perm_single StateCons \<omega> ?lh (Some (Abs_prat p)) = 
          {update_mh_loc_total_full \<omega> ?lh (padd (get_mh_total_full \<omega> ?lh) (Abs_prat p))}"
      apply (rule inhale_perm_single_nonempty)
      using \<open>\<omega>' \<in> _\<close> False
      by fastforce
    thus ?thesis 
      using \<open>\<omega>' \<in> _\<close> False
      by auto
  qed
next
  fix \<omega> \<omega>' ns
  assume "R \<omega> ns" 

  assume "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'"
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    unfolding inhale_acc_normal_premise_def
    by blast

  thus "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))"
    using exp_rel_vpr_bpl_elim_2[OF RcvRel] StateRel[OF \<open>R \<omega> ns\<close>]
    by (metis val_rel_vpr_bpl.simps(3))
next
  fix \<omega> \<omega>' ns
  assume "R \<omega> ns" 
  note StateRelInst = StateRel[OF \<open>R \<omega> ns\<close>]

  let ?p' = "(padd (get_mh_total_full \<omega> (the_address r, f_vpr)) (Abs_prat p))"

  assume InhPremise: "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'"
  hence RedRcvVpr: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and "p \<ge> 0" and
                   "p > 0 \<longrightarrow> r \<noteq> Null"
    unfolding inhale_acc_normal_premise_def 
    by blast+

  from InhPremise have AtMostWritePerm: "r \<noteq> Null \<Longrightarrow> pgte pwrite ?p'" 
    unfolding inhale_acc_normal_premise_def inhale_perm_single_def
    by force

  have
       LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some (RealV (real_of_rat p))"
      using state_rel_aux_pred_sat_lookup_2[OF StateRelInst]
      unfolding pred_eq_def      
      by (metis (full_types) fun_upd_same)

  show "red_expr_bpl ctxt new_perm ns
         (if (r = Null) then (RealV 0) else (RealV (real_of_rat (Rep_prat (padd (get_mh_total_full \<omega> (the_address r, f_vpr)) (Abs_prat p)))))) \<and>
        (r \<noteq> Null \<longrightarrow> pgte pwrite ?p')"
    apply (rule conjI)
    apply (subst \<open>new_perm = _\<close>)
    apply (rule RedBinOp)
      apply (rule exp_rel_perm_access_2[OF MaskReadWf StateRelInst RedRcvVpr FieldRelSingle])
         apply simp
        apply simp
       apply (rule RcvRel)
    apply (simp add: \<open>m_bpl = _\<close>)
     apply (fastforce intro: RedVar LookupTempPerm)
    using \<open>p \<ge> 0\<close> \<open>p > 0 \<longrightarrow> r \<noteq> Null\<close> padd_aux
     apply force
    using AtMostWritePerm
    by simp
next
  fix \<omega> ns
  assume StateRel: "state_rel_def_same Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega> ns"
  thus "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"    
    using \<open>temp_perm \<notin> _\<close> state_rel_aux_pred_remove[OF StateRel]
    by (metis fun_upd_None_if_notin_dom map_le_imp_upd_le upd_None_map_le)
next
  fix \<omega> \<omega>' ns a
  assume "R \<omega> ns" and "r = Address a" and
         InhAccPremise: "inhale_acc_normal_premise ctxt_vpr StateCons e_rcv_vpr f_vpr e_p p r \<omega> \<omega>'"

  from RedInhale[OF inhale_acc_normal_premise_red_inhale[OF InhAccPremise]] 
       state_rel_consistent[OF StateRel[OF \<open>R \<omega> ns\<close>]] 
  show "StateCons \<omega>'"
    using total_consistency_red_stmt_preserve[OF WfConsistency]
    by blast
qed

subsection \<open>Misc\<close>

lemma inhale_rel_refl:
  assumes "\<And> \<omega> res. red_inhale ctxt_vpr StateCons A \<omega> res \<Longrightarrow> (res \<noteq> RFailure \<and> (\<forall> \<omega>'. res = RNormal \<omega>' \<longrightarrow> \<omega>' = \<omega>)) "
  shows "inhale_rel R Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>"
  using assms
  by (auto intro!: inhale_rel_intro intro: red_ast_bpl_refl)

lemma inhale_rel_true: "inhale_rel R Q ctxt_vpr StateCons P ctxt (Atomic (Pure (ELit (ViperLang.LBool True)))) \<gamma> \<gamma>"
proof (rule inhale_rel_refl)
  fix \<omega> res
  assume "red_inhale ctxt_vpr StateCons (Atomic (Pure (ELit (ViperLang.lit.LBool True)))) \<omega> res"

  from this obtain b where 
    "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>(ELit (ViperLang.lit.LBool True));\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b)" and
    "res = (if b then RNormal \<omega> else RMagic)"
    apply (rule InhPure_case)
    by (auto elim: red_exp_list_failure_elim red_pure_exp_total_elims)

  thus " res \<noteq> RFailure \<and> (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow> \<omega>' = \<omega>) "
    by simp
qed

end