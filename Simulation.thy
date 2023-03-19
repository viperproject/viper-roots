section \<open>Generic definitions for simulations between front-ends and Boogie\<close>

theory Simulation
imports BoogieInterface
begin

definition rel_general :: "('v \<Rightarrow> 'a nstate \<Rightarrow> bool) \<Rightarrow>
                               ('v \<Rightarrow> 'a nstate \<Rightarrow> bool) \<Rightarrow> 
                                ('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow>
                                ('v \<Rightarrow> bool) \<Rightarrow>
                                ast \<Rightarrow> 'a econtext_bpl_general \<Rightarrow>
                                (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>' \<equiv>
      \<comment>\<open>for all states in the input relation\<close>
      \<forall> \<omega> ns. R \<omega> ns \<longrightarrow> 
             (\<forall>\<omega>'. Success \<omega> \<omega>' \<longrightarrow>
                 \<comment>\<open>success can be simulated by an Boogie execution that reaches \<gamma>' s.t. 
                    the output relation is respected\<close>
                 (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'))) \<and>
             (Fail \<omega> \<longrightarrow> 
                 \<comment>\<open>failure is preserved by Boogie\<close>
                (\<exists>c'. snd c' = Failure \<and>
                      red_ast_bpl P ctxt (\<gamma>, Normal ns) c'))"

subsection \<open>Introduction and Elimination rules\<close>

lemma rel_intro:
  assumes 
  "\<And>\<omega> ns \<omega>'. 
          R \<omega> ns \<Longrightarrow> 
          Success \<omega> \<omega>' \<Longrightarrow>
          \<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')" and
  "\<And>\<omega> ns.
          R \<omega> ns \<Longrightarrow> 
          Fail \<omega> \<Longrightarrow>
          \<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  shows "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>'"
  using assms
  unfolding rel_general_def 
  by blast

lemma rel_success_elim:
  assumes "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "Success \<omega> \<omega>'"
    shows   "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')"
  using assms
  unfolding rel_general_def
  by blast

lemma rel_failure_elim:
  assumes "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "Fail \<omega>"
  shows "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  using assms
  unfolding rel_general_def
  by blast

subsection \<open>Propagation rules\<close>

lemma rel_propagate_pre:
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> (\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega> \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "rel_general R1 R2 Success Fail P ctxt \<gamma>1 \<gamma>2"
        shows "rel_general R0 R2 Success Fail P ctxt \<gamma>0 \<gamma>2"  
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Success \<omega> \<omega>'"

  with \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using rel_success_elim[OF assms(2)] \<open>Success \<omega> \<omega>'\<close>
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Fail \<omega>"

  with \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using rel_failure_elim[OF assms(2)] \<open>Fail \<omega>\<close>
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
qed

text \<open>Same as rel_propagate_pre but where \<^prop>\<open>R1 = R2\<close>\<close>
lemma rel_propagate_pre_2: 
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> (\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega> \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "rel_general R1 R1 Success Fail P ctxt \<gamma>1 \<gamma>2"
   shows "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>2" 
  using assms rel_propagate_pre
  by blast

lemma rel_propagate_post:
  assumes "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>1" and
          "\<And> \<omega> ns. R1 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega> ns'"
        shows "rel_general R0 R2 Success Fail P ctxt \<gamma>0 \<gamma>2"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         "Success \<omega> \<omega>'"  
  from this obtain ns1 where 
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega>' ns1"
    using assms(1) rel_success_elim 
    by metis 

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using assms(2)
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns
  assume "R0 \<omega> ns" and
         "Fail \<omega>"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using assms(1) rel_failure_elim 
    by meson
qed

text \<open>If failure is infeasible, then we can assume success when propagating\<close>

lemma rel_propagate_pre_success:
  assumes NoFailure: "\<And> \<omega>. \<not> Fail \<omega>"
          "\<And> \<omega> \<omega>' ns. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "rel_general R1 R2 Success Fail P ctxt \<gamma>1 \<gamma>2"
        shows "rel_general R0 R2 Success Fail P ctxt \<gamma>0 \<gamma>2"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Success \<omega> \<omega>'"

  with assms(2) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using rel_success_elim[OF assms(3)] \<open>Success \<omega> \<omega>'\<close> red_ast_bpl_transitive
    by blast
qed (simp add: NoFailure)

lemma rel_propagate_pre_success_2:
  assumes NoFailure: "\<And> \<omega>. \<not> Fail \<omega>"
          "\<And> \<omega> \<omega>' ns. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R0 \<omega> ns'" and
          "rel_general R0 R1 Success Fail P ctxt \<gamma>1 \<gamma>2"
        shows "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>2"
  apply (rule rel_propagate_pre_success)
  using assms
  by auto  

subsection \<open>General structural rules\<close>

text \<open>Composition rule\<close>

lemma rel_general_comp:
  assumes 
   Rel1: "rel_general R1 R2 Success1 Fail1 P ctxt \<gamma>1 \<gamma>2" and
   Rel2: "rel_general R2 R3 Success2 Fail2 P ctxt \<gamma>2 \<gamma>3" and
   SuccessComp: "\<And> \<omega> \<omega>'. Success3 \<omega> \<omega>' \<Longrightarrow> (\<exists> \<omega>''. Success1 \<omega> \<omega>'' \<and> Success2 \<omega>'' \<omega>')" and
   FailComp: "\<And> \<omega>. Fail3 \<omega> \<Longrightarrow> (Fail1 \<omega> \<or> (\<exists>\<omega>''. Success1 \<omega> \<omega>'' \<and> Fail2 \<omega>''))"
 shows 
   "rel_general R1 R3 Success3 Fail3 P ctxt \<gamma>1 \<gamma>3"  
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R1 \<omega> ns" and "Success3 \<omega> \<omega>'"
  with SuccessComp obtain \<omega>'' where "Success1 \<omega> \<omega>''" and "Success2 \<omega>'' \<omega>'"
    by auto

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>3, Normal ns') \<and> R3 \<omega>' ns'"
    using rel_success_elim[OF Rel1 \<open>R1 \<omega> ns\<close>] rel_success_elim[OF Rel2] red_ast_bpl_transitive
    by fast
next
  fix \<omega> ns
  assume "R1 \<omega> ns" and "Fail3 \<omega>"

  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) c'"
  proof (cases "Fail1 \<omega>")
    case True
    then show ?thesis
      using rel_failure_elim[OF Rel1 \<open>R1 _ _\<close>]
      by blast
  next
    case False
    with FailComp[OF \<open>Fail3 \<omega>\<close>] obtain \<omega>'' where "Success1 \<omega> \<omega>''" and "Fail2 \<omega>''"
      by auto
      
    then show ?thesis
      using rel_success_elim[OF Rel1 \<open>R1 \<omega> ns\<close>] rel_failure_elim[OF Rel2] red_ast_bpl_transitive
      by fast
  qed
qed

text \<open>Conditional rule\<close>

lemma rel_general_cond:
  assumes 
          RelCondExp: "rel_general R R SuccessExp FailExp P ctxt 
                           \<gamma> 
                           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)"
                           (is "rel_general R R SuccessExp FailExp P ctxt \<gamma> ?\<gamma>_if") and
          RelThn: "rel_general R R SuccessThn FailThn P ctxt (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" and
          RelElse: "rel_general R R SuccessElse FailElse P ctxt (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)" and
          SuccessCond: "\<And> \<omega> \<omega>' ns. Success \<omega> \<omega>' \<Longrightarrow> R \<omega> ns \<Longrightarrow>
                        SuccessExp \<omega> \<omega> \<and> \<comment>\<open>implicit assumption that success of conditional does not lead to side effects\<close>
                       ((red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> SuccessThn \<omega> \<omega>') \<or> 
                       (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> SuccessElse \<omega> \<omega>'))"  and
          FailCond: "\<And> \<omega> ns. Fail \<omega> \<Longrightarrow> R \<omega> ns \<Longrightarrow> 
               FailExp \<omega> \<or>
               (SuccessExp \<omega> \<omega> \<and>
                 ( (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> FailThn \<omega>) \<or> 
                   (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> FailElse \<omega>) )
               )" 
        shows "rel_general R R Success Fail P ctxt \<gamma> (next, cont)"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and "Success \<omega> \<omega>'"
  have "SuccessExp \<omega> \<omega>"
    using SuccessCond[OF \<open>Success \<omega> \<omega>'\<close> \<open>R \<omega> ns\<close>]
    by simp

  with rel_success_elim[OF RelCondExp \<open>R \<omega> ns\<close>]  
  obtain ns1 where RedToIf: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>_if, Normal ns1)" and "R \<omega> ns1"
    by blast

  have Branch: "(red_expr_bpl ctxt cond_bpl ns1 (BoolV True) \<and> SuccessThn \<omega> \<omega>') \<or> 
                (red_expr_bpl ctxt cond_bpl ns1 (BoolV False) \<and> SuccessElse \<omega> \<omega>')" 
                            (is "?thn_branch \<or> ?els_branch")
    using SuccessCond[OF \<open>Success \<omega> \<omega>'\<close> \<open>R \<omega> ns1\<close>]
    by simp

  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) ((next, cont), Normal ns') \<and> R \<omega>' ns'"
  proof (cases ?thn_branch)
    case True
    hence "SuccessThn \<omega> \<omega>'" by simp

    have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((thn_hd, convert_list_to_cont thn_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfTrue)
      using True by blast

    then show ?thesis 
      using RedToIf rel_success_elim[OF RelThn \<open>R \<omega> ns1\<close> \<open>SuccessThn \<omega> \<omega>'\<close>] red_ast_bpl_transitive
      by blast
  next
    case False
    hence RedExpFalse:"red_expr_bpl ctxt cond_bpl ns1 (BoolV False)" and "SuccessElse \<omega> \<omega>'" using Branch
      by auto

    have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((els_hd, convert_list_to_cont els_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfFalse)
      using RedExpFalse by blast

    then show ?thesis
      using RedToIf rel_success_elim[OF RelElse \<open>R \<omega> ns1\<close> \<open>SuccessElse \<omega> \<omega>'\<close>] red_ast_bpl_transitive
      by blast
  qed
next
  fix \<omega> ns
  assume "R \<omega> ns" and "Fail \<omega>"
  hence FailBranch: "FailExp \<omega> \<or> SuccessExp \<omega> \<omega>" 
    using FailCond
    by blast

  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof (cases "FailExp \<omega>")
    case True
    then show ?thesis 
      using rel_failure_elim[OF RelCondExp \<open>R \<omega> ns\<close>] 
      by blast
  next
    case False
    hence "SuccessExp \<omega> \<omega>"
      using FailBranch
      by auto

    with rel_success_elim[OF RelCondExp \<open>R \<omega> ns\<close>]  
    obtain ns1 where RedToIf: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>_if, Normal ns1)" and "R \<omega> ns1"
      by blast

    hence FailBranch2: "( (red_expr_bpl ctxt cond_bpl ns1 (BoolV True) \<and> FailThn \<omega>) \<or> 
                   (red_expr_bpl ctxt cond_bpl ns1 (BoolV False) \<and> FailElse \<omega>) )" (is "?thn_branch \<or> ?els_branch")
      using FailCond[OF \<open>Fail \<omega>\<close>] False
      by blast      

    show ?thesis
    proof (cases ?thn_branch)
      case True
      hence "FailThn \<omega>"
        by simp

      have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((thn_hd, convert_list_to_cont thn_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfTrue)
      using True by blast
      then show ?thesis 
        using RedToIf rel_failure_elim[OF RelThn \<open>R \<omega> ns1\<close> \<open>FailThn \<omega>\<close>] red_ast_bpl_transitive
        by blast
    next
      case False
      hence RedExpFalse: "red_expr_bpl ctxt cond_bpl ns1 (BoolV False)" and "FailElse \<omega>"
        using FailBranch2
        by auto

      have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((els_hd, convert_list_to_cont els_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfFalse)
      using RedExpFalse by blast
      then show ?thesis 
        using RedToIf rel_failure_elim[OF RelElse \<open>R \<omega> ns1\<close> \<open>FailElse \<omega>\<close>] red_ast_bpl_transitive
        by blast
    qed
  qed
qed

subsection \<open>Misc rules\<close>

lemma rel_general_success_refl:
  assumes "\<And> \<omega>. \<not> Fail \<omega>" and
          "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> \<omega> = \<omega>'"
        shows "rel_general R R Success Fail P ctxt \<gamma> \<gamma>"
  using assms
  by (auto intro!: rel_intro intro: red_ast_bpl_refl)
    

end