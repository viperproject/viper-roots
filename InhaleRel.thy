theory InhaleRel
  imports ExpRel ExprWfRel TotalViper.ViperBoogieTranslationInterface
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
           \<forall>\<omega> ns res. R \<omega> ns \<longrightarrow> 
             \<comment>\<open>If the Viper inhale reduces\<close>
             red_inhale ctxt_vpr StateCons assertion_vpr \<omega> res \<longrightarrow>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                   \<comment>\<open>Normal Viper inhale executions can be simulated by normal Boogie executions\<close>
                   (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                   \<comment>\<open>If a Viper inhale executions fails, then there is a failing Boogie execution\<close>
                   (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure))"

lemma inhale_rel_intro:
  assumes
    "\<And>\<omega> ns \<omega>'. 
      R \<omega> ns \<Longrightarrow> 
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
      (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and

    "\<And>\<omega> ns \<omega>'.
      R \<omega> ns \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure \<Longrightarrow>
      (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def
  by blast

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
  by fastforce

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
  by blast

lemma inhale_rel_failure_elim:
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure"
  shows "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  using assms
  unfolding inhale_rel_def
  by blast

subsection \<open>Structural rules\<close>

lemma inhale_rel_star: 
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" and
          "inhale_rel R ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
proof (rule inhale_rel_intro)
\<comment>\<open>Normal case\<close>

  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and "red_inhale ctxt_vpr StateCons (A1 && A2) \<omega> (RNormal \<omega>')"
  from this obtain \<omega>'' where
    RedInhA1: "red_inhale ctxt_vpr StateCons A1 \<omega> (RNormal \<omega>'')" and
    RedInhA2: "red_inhale ctxt_vpr StateCons A2 \<omega>'' (RNormal \<omega>')"
    by (auto elim: InhStar_case)

  from inhale_rel_normal_elim[OF assms(1) \<open>R \<omega> ns\<close> RedInhA1]
       inhale_rel_normal_elim[OF assms(2) _ RedInhA2]

  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega>' ns'"
    using red_ast_bpl_transitive
    by blast
next
\<comment>\<open>Failure case\<close>

  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and RedInhale: "red_inhale ctxt_vpr StateCons (A1 && A2) \<omega> RFailure"

  show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure"
  proof (cases "red_inhale ctxt_vpr StateCons A1 \<omega> RFailure")
    case True
    thus ?thesis 
      using inhale_rel_failure_elim[OF assms(1) \<open>R \<omega> ns\<close>]
      by blast
  next
    case False
    with RedInhale obtain \<omega>'' where 
      "red_inhale ctxt_vpr StateCons A1 \<omega> (RNormal \<omega>'')" and
     "red_inhale ctxt_vpr StateCons A2 \<omega>'' RFailure"
      by (auto elim: InhStar_case)

    thus ?thesis
      using inhale_rel_normal_elim[OF assms(1) \<open>R \<omega> ns\<close>] inhale_rel_failure_elim[OF assms(2)] 
            red_ast_bpl_transitive
      by fast
  qed
qed

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
proof (rule inhale_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and RedInh: "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> res"

  from RedInh 
  show "inhale_rel_aux R ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont) \<omega> ns res"
  proof (cases)
    case InhImpTrue

    from this obtain ns' where
      "R \<omega> ns'" and RedToIf: "red_ast_bpl P ctxt (\<gamma>1, Normal ns) (?\<gamma>_if, Normal ns')"
      using wf_rel_normal_elim ExpWfRel \<open>R \<omega> ns\<close>
      by blast

    from InhImpTrue have  RedCondBplTrue: "red_expr_bpl ctxt cond_bpl ns' (BoolV True)"
      using  exp_rel_vpr_bpl_elim_2[OF ExpRel] \<open>R \<omega> ns'\<close>
      by (metis val_rel_vpr_bpl.simps(2))

    hence RedToThn: "red_ast_bpl P ctxt (\<gamma>1, Normal ns) (?\<gamma>_thn, Normal ns')"
      using RedToIf red_ast_bpl_transitive
      by (blast intro!: red_ast_bpl_one_step_empty_simple_cmd RedParsedIfTrue)
         
    show ?thesis
    proof (rule inhale_rel_aux_intro)
     \<comment>\<open>Normal case\<close>
      fix \<omega>'
      assume "res = RNormal \<omega>'"
      with inhale_rel_normal_elim[OF RhsRel \<open>R \<omega> ns'\<close>] \<open>red_inhale ctxt_vpr StateCons A \<omega> res\<close> obtain ns''
        where "R \<omega>' ns''" and "red_ast_bpl P ctxt (\<gamma>1, Normal ns) ((next, cont), Normal ns'')"
        using red_ast_bpl_transitive RedToThn
        by blast

      thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) ((next, cont), Normal ns') \<and> R \<omega>' ns'"
        by fast
    next
      \<comment>\<open>Failure case\<close>
      assume "res = RFailure"
      with inhale_rel_failure_elim[OF RhsRel \<open>R \<omega> ns'\<close>] \<open>red_inhale ctxt_vpr StateCons A \<omega> res\<close>
      show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure"
        using red_ast_bpl_transitive RedToThn
        by blast
    qed
  next
    case InhImpFalse
     from this obtain ns' where
      "R \<omega> ns'" and RedToIf: "red_ast_bpl P ctxt (\<gamma>1, Normal ns) (?\<gamma>_if, Normal ns')"
      using wf_rel_normal_elim ExpWfRel \<open>R \<omega> ns\<close>
      by blast

     from InhImpFalse have  RedCondBplFalse: "red_expr_bpl ctxt cond_bpl ns' (BoolV False)"
      using  exp_rel_vpr_bpl_elim_2[OF ExpRel] \<open>R \<omega> ns'\<close>
      by (metis val_rel_vpr_bpl.simps(2))

    hence "red_ast_bpl P ctxt (?\<gamma>_if, Normal ns') ((next, cont), Normal ns')"
      using red_ast_bpl_empty_else EmptyElse
      by fast

     thus ?thesis 
       using RedToIf \<open>R \<omega> ns'\<close> red_ast_bpl_transitive  \<open>res = RNormal \<omega>\<close>
       by (blast intro!: inhale_rel_aux_intro)          
   next
     case InhImpFailure
     thus ?thesis
       using wf_rel_failure_elim[OF ExpWfRel] \<open>R \<omega> ns\<close>
       by (blast intro!: inhale_rel_aux_intro)
   qed
 qed


end