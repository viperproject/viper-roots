section \<open>Generic definitions for simulations between front-ends and Boogie\<close>

theory Simulation
imports BoogieInterface TotalUtil
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

lemma rel_general_success_refl:
  assumes "\<And> \<omega>. \<not> Fail \<omega>" and
          "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> \<omega> = \<omega>'"
        shows "rel_general R R Success Fail P ctxt \<gamma> \<gamma>"
  using assms
  by (auto intro!: rel_intro intro: red_ast_bpl_refl)

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

subsection \<open>Conversions\<close>

definition rel_ext 
  where "rel_ext R \<equiv> (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)"


lemma rel_general_convert:
assumes "rel_general (uncurry (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)) (uncurry (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R' \<omega> ns))
                     (\<lambda>\<omega> \<omega>'. fst \<omega> = snd \<omega> \<and> fst \<omega>' = snd \<omega>' \<and> Success (snd \<omega>) (snd \<omega>'))
                     (\<lambda>\<omega>. fst \<omega> = snd \<omega> \<and> Fail (fst \<omega>))  P ctxt \<gamma> \<gamma>'"
shows "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>'"
  using assms
  unfolding rel_general_def rel_ext_def
  by auto

lemma rel_general_convert_2:
assumes "rel_general (uncurry (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)) (uncurry (\<lambda>\<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R' \<omega> ns))
                     (\<lambda>\<omega> \<omega>'. fst \<omega> = snd \<omega> \<and> fst \<omega>' = snd \<omega>' \<and> Success (snd \<omega>) (snd \<omega>'))
                     (\<lambda>\<omega>. fst \<omega> = snd \<omega> \<and> Fail (fst \<omega>))  P ctxt \<gamma> \<gamma>'"
shows "rel_general R R' Success Fail P ctxt \<gamma> \<gamma>'"
  using assms
  unfolding rel_general_def rel_ext_def
  by auto

subsection \<open>Rule of consequence\<close>

lemma rel_general_conseq:
assumes Rel: "rel_general R0' R1' Success' Fail' P ctxt \<gamma> \<gamma>'" and
        Input: "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> R0' \<omega> ns" and
        Output: "\<And> \<omega> \<omega>' ns. (\<exists>ns0. R0 \<omega> ns0) \<Longrightarrow> R1' \<omega>' ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> R1 \<omega>' ns" and
        Success: "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> Success' \<omega> \<omega>'" and
        Fail: "\<And> \<omega>. Fail \<omega>  \<Longrightarrow> Fail' \<omega>"
      shows "rel_general R0 R1 Success Fail P ctxt \<gamma> \<gamma>'"
  apply (rule rel_intro)
  using Input Output Success Fail rel_success_elim[OF Rel] rel_failure_elim[OF Rel]
  by meson+

lemma rel_general_conseq_input:
assumes Rel: "rel_general R0' R1 Success Fail P ctxt \<gamma> \<gamma>'" and
        Input: "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> R0' \<omega> ns"
      shows "rel_general R0 R1 Success Fail P ctxt \<gamma> \<gamma>'"
  using assms
  by (rule rel_general_conseq)

lemma rel_general_conseq_output:
assumes Rel: "rel_general R0 R1' Success Fail P ctxt \<gamma> \<gamma>'" and
        Output: "\<And> \<omega> \<omega>' ns. (\<exists>ns0. R0 \<omega> ns0) \<Longrightarrow> R1' \<omega>' ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> R1 \<omega>' ns"
      shows "rel_general R0 R1 Success Fail P ctxt \<gamma> \<gamma>'"
  by (rule rel_general_conseq[OF Rel _ Output])

lemmas rel_general_conseq_input_output = rel_general_conseq_output[OF rel_general_conseq_input]   

lemma rel_general_conseq_fail:
  assumes  Rel: "rel_general R0 R1 Success Fail' P ctxt \<gamma> \<gamma>'" and
           Fail: "\<And> \<omega>. Fail \<omega>  \<Longrightarrow> Fail' \<omega>"
         shows "rel_general R0 R1 Success Fail P ctxt \<gamma> \<gamma>'"
  by (rule rel_general_conseq[OF Rel _ _ _ Fail])

subsection \<open>Propagation rules\<close>

lemma rel_propagate_pre:
  assumes \<comment>\<open>"\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> (\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega> \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and\<close>
          "red_ast_bpl_rel (\<lambda> \<omega> ns. ((\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega>) \<and> R0 \<omega> ns) R1 P ctxt \<gamma>0 \<gamma>1"
      and "rel_general R1 R2 Success Fail P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R2 Success Fail P ctxt \<gamma>0 \<gamma>2"  
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Success \<omega> \<omega>'"

  with \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    unfolding red_ast_bpl_rel_def
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using rel_success_elim[OF assms(2)] \<open>Success \<omega> \<omega>'\<close>
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Fail \<omega>"

  with \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    unfolding red_ast_bpl_rel_def
    by blast

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using rel_failure_elim[OF assms(2)] \<open>Fail \<omega>\<close>
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
qed

text \<open>Same as rel_propagate_pre but where \<^prop>\<open>R1 = R2\<close>\<close>
lemma rel_propagate_pre_2: 
  assumes "red_ast_bpl_rel (\<lambda> \<omega> ns. ((\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega>) \<and> R0 \<omega> ns) R1 P ctxt \<gamma>0 \<gamma>1"
      and "rel_general R1 R1 Success Fail P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>2"
  using assms rel_propagate_pre
  by blast

lemma rel_propagate_pre_2_only_state_rel: 
  assumes "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and "rel_general R1 R1 Success Fail P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>2"
  using assms rel_propagate_pre 
  unfolding red_ast_bpl_rel_def
  by metis  

lemma rel_propagate_post:
  assumes "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>1"
      and "red_ast_bpl_rel R1 R2 P ctxt \<gamma>1 \<gamma>2"
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
    unfolding red_ast_bpl_rel_def
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns
  assume "R0 \<omega> ns" and
         "Fail \<omega>"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using assms(1) rel_failure_elim 
    by meson
qed

lemma rel_propagate_post_2:
  assumes "rel_general R0 R0 Success Fail P ctxt \<gamma>0 \<gamma>1"
      and    "red_ast_bpl_rel R0 R0 P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R0 Success Fail P ctxt \<gamma>0 \<gamma>2"
  using assms rel_propagate_post
  by blast

text \<open>If failure is infeasible, then we can assume success when propagating\<close>

lemma rel_propagate_pre_success:
  assumes NoFailure: "\<And> \<omega>. \<not> Fail \<omega>"
      and "red_ast_bpl_rel (\<lambda> \<omega> ns. (\<exists>\<omega>'. Success \<omega> \<omega>') \<and> R0 \<omega> ns) R1 P ctxt \<gamma>0 \<gamma>1"
      and    "rel_general R1 R2 Success Fail P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R2 Success Fail P ctxt \<gamma>0 \<gamma>2"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Success \<omega> \<omega>'"

  with assms(2) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    unfolding red_ast_bpl_rel_def
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using rel_success_elim[OF assms(3)] \<open>Success \<omega> \<omega>'\<close> red_ast_bpl_transitive
    by blast
qed (simp add: NoFailure)

lemma rel_propagate_pre_success_2:
  assumes NoFailure: "\<And> \<omega>. \<not> Fail \<omega>"
      and "red_ast_bpl_rel (\<lambda> \<omega> ns. (\<exists>\<omega>'. Success \<omega> \<omega>') \<and> R0 \<omega> ns) R0 P ctxt \<gamma>0 \<gamma>1"
      and "rel_general R0 R1 Success Fail P ctxt \<gamma>1 \<gamma>2"
    shows "rel_general R0 R1 Success Fail P ctxt \<gamma>0 \<gamma>2"
  apply (rule rel_propagate_pre_success)
  using assms
  by auto

lemma assert_single_step_rel:
  assumes SuccessCond: "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> \<omega> = \<omega>' \<and> cond \<omega>"
      and FailCond: "\<And>\<omega>. Fail \<omega> \<Longrightarrow> \<not>cond \<omega>"
      and RedBpl: "\<And>\<omega> ns. R \<omega> ns \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV (cond \<omega>))"
    shows "rel_general R R
                       Success
                       Fail
                       P ctxt
                       (BigBlock name (cmd.Assert e_bpl # cs) s tr, cont)
                       (BigBlock name cs s tr, cont)" (is "rel_general ?R ?R ?Success ?Fail P ctxt ?\<gamma> ?\<gamma>'")
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and "Success \<omega> \<omega>'"

  have "red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns)"
    apply (rule red_ast_bpl_one_simple_cmd)
    using SuccessCond[OF \<open>Success \<omega> \<omega>'\<close>] RedBpl[OF \<open>R \<omega> ns\<close>]
    by (auto intro!: RedAssertOk)
  thus "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (cmd.Assert e_bpl # cs) s tr, cont), Normal ns)
            ((BigBlock name cs s tr, cont), Normal ns') \<and>
           R \<omega>' ns'"
    using \<open>R \<omega> ns\<close> SuccessCond[OF \<open>Success \<omega> \<omega>'\<close>]
    by blast
next
  fix \<omega> ns
  assume "R \<omega> ns" and "Fail \<omega>"
  have "red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Failure)"
    apply (rule red_ast_bpl_one_simple_cmd)
    using FailCond[OF \<open>Fail \<omega>\<close>] RedBpl[OF \<open>R \<omega> ns\<close>]
    by (auto intro!: RedAssertFail)

  thus "\<exists>c'. snd c' = Failure \<and>
          red_ast_bpl P ctxt ((BigBlock name (cmd.Assert e_bpl # cs) s tr, cont), Normal ns) c'"
    by auto
qed

lemma rel_propagate_pre_assert:
  assumes Success: "\<And> \<omega> ns \<omega>'. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV True)" and
          Fail: "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> Fail \<omega>  \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV (b \<omega>))" and
          Rel: "rel_general R0 R1 
                       Success (\<lambda>\<omega>. Fail \<omega> \<and> b \<omega>) P ctxt (BigBlock name cs str tr, cont) \<gamma>2"
        shows "rel_general R0 R1 Success Fail P ctxt (BigBlock name ((Lang.Assert e_bpl)#cs) str tr, cont) \<gamma>2"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and "Success \<omega> \<omega>'"
  have "red_ast_bpl P ctxt ((BigBlock name (Lang.Assert e_bpl # cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), Normal ns)"     
    by (auto intro: red_ast_bpl_one_assert RedAssertOk Success[OF \<open>R0 \<omega> ns\<close> \<open>Success _ _\<close>])

  thus "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Lang.Assert e_bpl # cs) str tr, cont), Normal ns) (\<gamma>2, Normal ns') \<and> R1 \<omega>' ns'"
    using rel_success_elim[OF Rel \<open>R0 \<omega> ns\<close> \<open>Success _ _\<close>] red_ast_bpl_transitive
    by blast
next
  fix \<omega> ns
  assume "R0 \<omega> ns" and "Fail \<omega>"
  let ?s' = "if b \<omega> then Normal ns else Failure"
  have "red_ast_bpl P ctxt ((BigBlock name (Lang.Assert e_bpl # cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), ?s')"
   by (auto intro: red_ast_bpl_one_assert RedAssertOk Fail[OF \<open>R0 \<omega> ns\<close> \<open>Fail _\<close>])

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt ((BigBlock name (Lang.Assert e_bpl # cs) str tr, cont), Normal ns) c'"
    using rel_failure_elim[OF Rel \<open>R0 \<omega> ns\<close>] 
    apply (cases "b \<omega>")
    using \<open>Fail _\<close> red_ast_bpl_transitive
     apply fastforce
    by auto
qed

lemma rel_propagate_pre_assert_2:
  assumes RedExpBpl: "\<And> \<omega> ns \<omega>'. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<or> Fail \<omega> \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV (b \<omega>))" and
          Success: "\<And> \<omega> ns \<omega>'. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> b \<omega>" and
          Rel: "rel_general R0 R1 
                       Success (\<lambda>\<omega>. Fail \<omega> \<and> b \<omega>) P ctxt (BigBlock name cs str tr, cont) \<gamma>'"
        shows "rel_general R0 R1 Success Fail P ctxt (BigBlock name ((Lang.Assert e_bpl)#cs) str tr, cont) \<gamma>'"
  apply (rule rel_propagate_pre_assert[OF _ _ Rel])
  using assms
   apply fastforce
  using assms
  by blast

lemma rel_propagate_pre_assume:
  assumes RedExpBpl: "\<And> \<omega> ns \<omega>'. R0 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<or> Fail \<omega> \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV True)" and
                     "rel_general R0 R1 Success Fail P ctxt (BigBlock name cs str tr, cont) \<gamma>'"
  shows "rel_general R0 R1 Success Fail P ctxt (BigBlock name ((Lang.Assume e_bpl)#cs) str tr, cont) \<gamma>'"
proof (rule rel_propagate_pre[OF _ assms(2)], unfold red_ast_bpl_rel_def, (rule allI | rule impI)+)
  fix \<omega> ns
  assume local_assms: "((\<exists>\<omega>'. Success \<omega> \<omega>') \<or> Fail \<omega>) \<and> R0 \<omega> ns"
  hence "red_expr_bpl ctxt e_bpl ns (BoolV True)"
    using RedExpBpl
    by blast
  thus "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Lang.Assume e_bpl # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Normal ns') \<and>
             R0 \<omega> ns'"
    using red_ast_bpl_one_assume[OF RedExpBpl] local_assms
    by metis
qed

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
          RelCondExp: "rel_general R1 R1 SuccessExp FailExp P ctxt 
                           \<gamma> 
                           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)"
                           (is "rel_general R1 R1 SuccessExp FailExp P ctxt \<gamma> ?\<gamma>_if") and

          \<comment>\<open>\<^term>\<open>R1Thn\<close> and \<^term>\<open>R1Else\<close> may differ from \<^term>\<open>R1\<close> because the knowledge that a branch is taken
             provides constrains the states.\<close>

          RelThn: "rel_general R1Thn R2 SuccessThn FailThn P ctxt (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" and
          RelElse: "rel_general R1Else R2 SuccessElse FailElse P ctxt (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)" and
          SuccessCond: "\<And> \<omega> \<omega>' ns. Success \<omega> \<omega>' \<Longrightarrow> R1 \<omega> ns \<Longrightarrow>
                        SuccessExp \<omega> \<omega> \<and> \<comment>\<open>implicit assumption that success of conditional does not lead to side effects\<close>
                       ((red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> R1Thn \<omega> ns \<and> SuccessThn \<omega> \<omega>') \<or> 
                        (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R1Else \<omega> ns \<and> SuccessElse \<omega> \<omega>'))"  and
          FailCond: "\<And> \<omega> ns. Fail \<omega> \<Longrightarrow> R1 \<omega> ns \<Longrightarrow> 
               FailExp \<omega> \<or>
               (SuccessExp \<omega> \<omega> \<and>
                 ( (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> R1Thn \<omega> ns \<and> FailThn \<omega>) \<or> 
                   (red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R1Else \<omega> ns \<and> FailElse \<omega>) )
               )" 
        shows "rel_general R1 R2 Success Fail P ctxt \<gamma> (next, cont)"  
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R1 \<omega> ns" and "Success \<omega> \<omega>'"
  have "SuccessExp \<omega> \<omega>"
    using SuccessCond[OF \<open>Success \<omega> \<omega>'\<close> \<open>R1 \<omega> ns\<close>]
    by simp

  with rel_success_elim[OF RelCondExp \<open>R1 \<omega> ns\<close>]  
  obtain ns1 where RedToIf: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>_if, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  consider (SuccessThn) "red_expr_bpl ctxt cond_bpl ns1 (BoolV True)" and "R1Thn \<omega> ns1" and "SuccessThn \<omega> \<omega>'"
    |      (SuccessElse) "red_expr_bpl ctxt cond_bpl ns1 (BoolV False)" and "R1Else \<omega> ns1" and "SuccessElse \<omega> \<omega>'"
    using SuccessCond[OF \<open>Success \<omega> \<omega>'\<close> \<open>R1 \<omega> ns1\<close>]
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) ((next, cont), Normal ns') \<and> R2 \<omega>' ns'"
  proof (cases)
    case SuccessThn
    have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((thn_hd, convert_list_to_cont thn_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfTrue)
      using SuccessThn by blast

    then show ?thesis 
      using RedToIf rel_success_elim[OF RelThn \<open>R1Thn \<omega> ns1\<close> \<open>SuccessThn \<omega> \<omega>'\<close>] red_ast_bpl_transitive
      by blast
  next
    case SuccessElse
    have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((els_hd, convert_list_to_cont els_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfFalse)
      using SuccessElse by blast

    then show ?thesis
      using RedToIf rel_success_elim[OF RelElse \<open>R1Else \<omega> ns1\<close> \<open>SuccessElse \<omega> \<omega>'\<close>] red_ast_bpl_transitive
      by blast
  qed
next
  fix \<omega> ns
  assume "R1 \<omega> ns" and "Fail \<omega>"
  from this consider (FailExp) "FailExp \<omega>" | (SuccessExp) "\<not>FailExp \<omega> \<and> SuccessExp \<omega> \<omega>" 
    using FailCond
    by blast

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof (cases)
    case FailExp
    then show ?thesis 
      using rel_failure_elim[OF RelCondExp \<open>R1 \<omega> ns\<close>] 
      by blast
  next
    case SuccessExp
    with rel_success_elim[OF RelCondExp \<open>R1 \<omega> ns\<close>]  
    obtain ns1 where RedToIf: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>_if, Normal ns1)" and "R1 \<omega> ns1"
      by blast

    from this consider 
                (FailThn) "red_expr_bpl ctxt cond_bpl ns1 (BoolV True)" "R1Thn \<omega> ns1" "FailThn \<omega>"
            |   (FailElse) "red_expr_bpl ctxt cond_bpl ns1 (BoolV False)" "R1Else \<omega> ns1" "FailElse \<omega>" 
      using FailCond[OF \<open>Fail \<omega>\<close>] SuccessExp
      by blast

    thus ?thesis
    proof (cases)
      case FailThn

      have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((thn_hd, convert_list_to_cont thn_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfTrue)
      using FailThn by blast
      then show ?thesis
        using RedToIf rel_failure_elim[OF RelThn \<open>R1Thn \<omega> ns1\<close> \<open>FailThn \<omega>\<close>]  red_ast_bpl_transitive
        by blast
    next
      case FailElse
      have "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns1) ((els_hd, convert_list_to_cont els_tl (KSeq next cont)), Normal ns1)"
      apply (rule red_ast_bpl_one_step_empty_simple_cmd)
      apply (rule RedParsedIfFalse)
      using FailElse by blast
      then show ?thesis 
        using RedToIf rel_failure_elim[OF RelElse \<open>R1Else \<omega> ns1\<close> \<open>FailElse \<omega>\<close>] red_ast_bpl_transitive
        by blast
    qed
  qed
qed
    
lemma rel_general_cond_2:
  assumes  RedCond: "\<And> \<omega> ns \<omega>'. R1 \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<or> Fail \<omega> \<Longrightarrow> red_expr_bpl ctxt cond_bpl ns (BoolV (b \<omega>))" and
           RelThn: "\<And> \<omega> \<omega>'. rel_general R1 R2 (\<lambda>\<omega> \<omega>'. Success \<omega> \<omega>' \<and> b \<omega>) (\<lambda> \<omega>. Fail \<omega> \<and> b \<omega>) P ctxt (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" and
           RelEls: "\<And> \<omega> \<omega>'. rel_general R1 R2 (\<lambda>\<omega> \<omega>'. Success \<omega> \<omega>' \<and> \<not> (b \<omega>)) (\<lambda> \<omega>. Fail \<omega> \<and> \<not>(b \<omega>)) P ctxt 
                                     (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)"
  shows "rel_general R1 R2 Success Fail P ctxt (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont) (next, cont)"
  apply (rule rel_general_cond[where ?SuccessExp="\<lambda>\<omega> \<omega>'. \<omega> = \<omega>'" and ?FailExp="\<lambda>_. False"])
      apply (rule rel_general_success_refl)
       apply simp
      apply simp
     apply (rule RelThn)
    apply (rule RelEls)
  using RedCond
   apply (metis (full_types))
  using RedCond
  apply (metis (full_types))
  done
  
lemma rel_general_if_2:
  assumes "\<And> \<omega> ns \<omega>'. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<or> Fail \<omega> \<Longrightarrow> red_expr_bpl ctxt e_bpl ns (BoolV (b \<omega>))"
      and "\<And> \<omega> \<omega>'. rel_general (\<lambda> \<omega> ns. R \<omega> ns \<and> b \<omega>) R_thn Success Fail P ctxt (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
      and "\<And> \<omega> \<omega>'. rel_general (\<lambda> \<omega> ns. R \<omega> ns \<and> \<not>b \<omega>) R_els Success Fail P ctxt 
                                     (thn_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)"
      and "rel_general (\<lambda> \<omega> ns. (b \<omega> \<and> R_thn \<omega> ns) \<or> (\<not>b \<omega> \<and> R_els \<omega> ns)) R' Success Fail P ctxt (next, cont) \<gamma>'"
  shows "rel_general R R Success Fail P ctxt (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont) \<gamma>'"
  oops


end