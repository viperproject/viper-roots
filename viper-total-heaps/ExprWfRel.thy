theory ExprWfRel
imports ViperBoogieBasicRel ViperBoogieFunctionInst ExpRel Simulation TotalSemProperties ViperBoogieRelUtil
begin

subsection \<open>Semantic relation well-definedness\<close>

text \<open>Semantic relation stating when a Boogie statement encodes a well-definedness check of an expression.
Here, we implicitly restrict the Boogie statement to not have gotos and breaks, since we use the KStop continuation.\<close>


text \<open>
Relation that captures a Boogie statement encoding a non-failure check at the Viper level.
The relation permits a Boogie statement modifying its state as long as the modified state is still
related to the original Viper state.

This relation could be made weaker, by permitting Boogie to reduce to failure in the normal case
(would not affect soundness; the current relation does not rule out failing Boogie reductions in the 
normal case, so in terms of completeness the current relation does not say much).
\<close>

type_synonym 'a vpr_state = "'a full_total_state"
type_synonym 'a bpl_state = "('a vbpl_absval) nstate"

definition wf_rel ::
  "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> 'a bpl_state \<Rightarrow> bool) \<Rightarrow> 
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> 'a bpl_state \<Rightarrow> bool) \<Rightarrow>
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ast \<Rightarrow>
   'a econtext_bpl \<Rightarrow>
   (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont)  \<Rightarrow> 
   bool" where
  "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>' \<equiv>
        rel_general 
            (\<lambda> \<omega>def_\<omega> ns. R (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns)
            (\<lambda> \<omega>def_\<omega> ns. R' (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns)
            (\<lambda>\<omega>def_\<omega> \<omega>def_\<omega>'. \<omega>def_\<omega> = \<omega>def_\<omega>' \<and> IsNormal (fst \<omega>def_\<omega>) (snd (\<omega>def_\<omega>)))
            (\<lambda>\<omega>def_\<omega>. IsFailure (fst \<omega>def_\<omega>) (snd (\<omega>def_\<omega>)))
            P ctxt \<gamma> \<gamma>'"

lemma wf_rel_general:
  "wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R' \<omega> ns) IsNormal IsFailure P ctxt \<gamma> \<gamma>' \<longleftrightarrow>
   rel_general R R' (\<lambda>\<omega> \<omega>'. IsNormal \<omega> \<omega> \<and> \<omega> = \<omega>') (\<lambda>\<omega>. IsFailure \<omega> \<omega>) P ctxt \<gamma> \<gamma>'"
  unfolding wf_rel_def rel_general_def
  by auto

lemma wf_rel_general_1:
  "wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R' \<omega> ns) IsNormal IsFailure P ctxt \<gamma> \<gamma>' \<Longrightarrow>
   rel_general R R' (\<lambda>\<omega> \<omega>'. IsNormal \<omega> \<omega> \<and> \<omega> = \<omega>') (\<lambda>\<omega>. IsFailure \<omega> \<omega>) P ctxt \<gamma> \<gamma>'"
  using wf_rel_general
  by blast

abbreviation expr_wf_rel :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow> ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool" where 
  "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>' \<equiv>
   wf_rel R R (\<lambda>\<omega>def \<omega>. \<exists>v. (ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v )) (\<lambda>\<omega>def \<omega>. (ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)) P ctxt \<gamma> \<gamma>'"


definition exprs_wf_rel :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow>  ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr list \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<equiv>
           wf_rel R R (\<lambda>\<omega>def \<omega>. \<exists>vs. red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs)) 
                      (\<lambda>\<omega>def \<omega>. red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None) P ctxt"

fun exprs_wf_rel_alt :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow>  ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr list \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt Nil \<gamma> \<gamma>' = (\<gamma> = \<gamma>')"
  | "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt (e#es) \<gamma> \<gamma>' = 
          (\<exists>\<gamma>''. expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>'' \<and>
            exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma>'' \<gamma>')"


lemma wf_rel_intro [case_names normal failure]:
  assumes
  cases:"\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
         IsNormal \<omega>def \<omega> \<Longrightarrow>
         \<exists> ns'.           
           red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and>
           R' \<omega>def \<omega> ns'" 
    "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
         IsFailure \<omega>def \<omega> \<Longrightarrow> 
         (\<exists>c'.           
          red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and>
          snd c' = Failure)"
 shows "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
  unfolding wf_rel_def rel_general_def
  using assms
  by fastforce

lemma wf_rel_normal_elim:
  assumes 
   "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
   "R \<omega>def \<omega> ns" and 
   "IsNormal \<omega>def \<omega>"
 shows
   "\<exists> ns'. R' \<omega>def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
  using assms
  unfolding wf_rel_def rel_general_def
  by fastforce

lemma exprs_wf_rel_normal_elim:
  assumes 
       "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs)"
  shows
        "\<exists> ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
  using assms
  unfolding exprs_wf_rel_def wf_rel_def rel_general_def
  by fastforce

lemma exprs_wf_rel_alt_normal_elim:
  assumes 
       "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs)"
  shows
        "\<exists> ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
  using assms
proof (induction R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>' arbitrary: ns vs rule: exprs_wf_rel_alt.induct)
  case (1 R ctxt_vpr StateCons P ctxt \<gamma> \<gamma>')
  then show ?case by (auto simp: red_ast_bpl_def)
next
  case (2 R ctxt_vpr StateCons P ctxt e es \<gamma> \<gamma>')

  from this obtain \<gamma>'' where 
    WfRelE:"expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>''" and 
    WfRelEs:"exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma>'' \<gamma>'" by auto

  note RedExps=\<open>red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) (e # es) \<omega> (Some vs)\<close>
  from this obtain v' vs' where "vs = v'#vs'" and
         "red_pure_exp_total ctxt_vpr StateCons (Some \<omega>def) e  \<omega> (Val v')" and
         RedExpsEs:"red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs')"
    by (auto elim: red_exp_list_normal_elim)

  with wf_rel_normal_elim[OF WfRelE \<open>R _ _ _\<close>] obtain ns' where
         R2:"R \<omega>def \<omega> ns'" and RedBpl: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>'', Normal ns')"
    by blast

  obtain ns'' where
    "red_ast_bpl P ctxt (\<gamma>'', Normal ns') (\<gamma>', Normal ns'') \<and> R \<omega>def \<omega> ns''"
    using "2.IH"[OF WfRelEs R2 RedExpsEs]
    by blast

  with RedBpl show ?case
    using red_ast_bpl_transitive by blast
qed

lemma wf_rel_failure_elim:
  assumes 
   "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
   "R \<omega>def \<omega> ns" and 
   "IsFailure \<omega>def \<omega>"
 shows 
   "(\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  using assms
  unfolding wf_rel_def rel_general_def
  by fastforce

lemma exprs_wf_rel_failure_elim:
  assumes 
       "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"
  shows
       "\<exists> c. red_ast_bpl P ctxt (\<gamma>, Normal ns) c \<and> snd c = Failure"
  using assms
  unfolding exprs_wf_rel_def wf_rel_def rel_general_def
  by fastforce
  
lemma exprs_wf_rel_alt_failure_elim:
  assumes 
       "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"
  shows
       "\<exists> c. red_ast_bpl P ctxt (\<gamma>, Normal ns) c \<and> snd c = Failure"
  using assms
proof (induction R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>' arbitrary: ns rule: exprs_wf_rel_alt.induct)
  case (1 R ctxt_vpr StateCons P ctxt \<gamma> \<gamma>')
  then show ?case
    \<comment>\<open>contradiction, since empty list never reduces to \<^const>\<open>None\<close>\<close>
    using red_exp_list_failure_Nil
    by blast
next
  case (2 R ctxt_vpr StateCons P ctxt e es \<gamma> \<gamma>')

  from this obtain \<gamma>'' where
    WfRelE:  "expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>''" and 
    WfRelEs: "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma>'' \<gamma>'"
    by auto

  consider (FailHd) "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
         | (FailTl) v where "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
                       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"
    using 2 
    by (blast elim: red_exp_list_failure_elim)

  thus ?case
  proof cases
    case FailHd
    then show ?thesis 
      using WfRelE \<open>R \<omega>def \<omega> ns\<close> 
      by (blast dest: wf_rel_failure_elim)
  next
    case FailTl
    then show ?thesis 
      using 2 WfRelE WfRelEs red_ast_bpl_transitive
      by (blast dest: wf_rel_normal_elim)      
  qed
qed

lemma exprs_wf_rel_alt_implies_exprs_wf_rel:
  assumes "exprs_wf_rel_alt R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'"
  shows "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'"
  unfolding exprs_wf_rel_def
  apply (rule wf_rel_intro)
   apply (blast intro: exprs_wf_rel_alt_normal_elim[OF assms])
  by (blast intro: exprs_wf_rel_alt_failure_elim[OF assms])

lemma expr_wf_rel_intro:
  assumes
   "\<And>v \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
        ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow>
         \<exists> ns'.           
           red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and>
           R \<omega>def \<omega> ns'" and
    "\<And>v \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
         ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> 
         v = VFailure \<Longrightarrow> 
         (\<exists>c'.           
          red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and>
          snd c' = Failure)"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>'"
 using assms
  by (auto intro: wf_rel_intro)

lemma expr_wf_rel_intro_trivial:
  assumes "\<And>v \<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> v \<noteq> VFailure"  
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>"
proof (rule expr_wf_rel_intro)
next
  fix v \<omega>def \<omega> ns
  assume "R \<omega>def \<omega> ns"
  assume "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  show 
   " \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns') \<and> R \<omega>def \<omega> ns'"
    apply (rule exI)
    apply (rule conjI)
    apply (rule red_ast_bpl_refl)
    by (simp add: \<open>R _ _ _\<close>)
qed (insert assms, fastforce)

lemma wf_rel_no_failure_refl: "wf_rel R R IsNormal (\<lambda>_ _. False) P ctxt \<gamma> \<gamma>" 
  unfolding wf_rel_def red_ast_bpl_def rel_general_def
  by blast

lemma exprs_wf_rel_Nil: "exprs_wf_rel R ctxt_vpr StateCons P ctxt [] \<gamma> \<gamma>"
  unfolding exprs_wf_rel_def 
  apply (rule wf_rel_intro)
  by (auto intro: red_ast_bpl_refl dest: red_exp_list_failure_Nil)

subsection \<open>Propagation rules\<close>


lemma wf_rel_extend_1:
  assumes 
   Wf:"wf_rel R R' IsNormal IsFailure P ctxt \<gamma>1 \<gamma>2" and
   Red:"\<And>\<omega>def \<omega> ns2. R' \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3) \<and> R'' \<omega>def \<omega> ns3"
 shows
   "wf_rel R R'' IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
  using assms
  unfolding wf_rel_def
  by (simp add: red_ast_bpl_relI rel_propagate_post)

lemma wf_rel_extend_1_same_rel:
  assumes 
   "wf_rel R R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>2" and
   "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3) \<and> R \<omega>def \<omega> ns3"
 shows 
  "wf_rel R R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
  using assms wf_rel_extend_1
  by blast

lemma wf_rel_extend_2:
  assumes 
   Red:"\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>1, Normal ns2) (\<gamma>2, Normal ns3) \<and> R' \<omega>def \<omega> ns3" and
   Wf:"wf_rel R' R'' IsNormal IsFailure P ctxt \<gamma>2 \<gamma>3"
 shows 
  "wf_rel R R'' IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
  unfolding wf_rel_def
  apply (rule rel_propagate_pre[where ?R1.0="uncurry R'", simplified red_ast_bpl_rel_def])
  using assms
  unfolding wf_rel_def
  by fastforce+

lemma wf_rel_extend_2_same_rel:
  assumes 
   Red:"\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>1, Normal ns2) (\<gamma>2, Normal ns3) \<and> R \<omega>def \<omega> ns3" and
   Wf:"wf_rel R R IsNormal IsFailure P ctxt \<gamma>2 \<gamma>3"
 shows 
  "wf_rel R R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
  using assms wf_rel_extend_2
  by blast

subsection \<open>Specific expressions\<close>

lemma var_never_fails: 
  assumes "Pr, ctxt_vpr, \<omega>def \<turnstile> \<langle>ViperLang.Var x; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows "v \<noteq> VFailure"
  using assms
  by (cases) auto

lemma lit_never_fails:
  assumes "ctxt_vpr, StateCons, \<omega>def \<turnstile> \<langle>ViperLang.ELit lit; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows "v \<noteq> VFailure"
  using assms
  by (cases) auto

lemma unop_elim:
  assumes "ctxt_vpr, StateCons, \<omega>def \<turnstile> \<langle>ViperLang.Unop uop e; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows 
     "if v = VFailure then 
        ctxt_vpr, StateCons, \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure 
      else 
        \<exists>v'. ctxt_vpr, StateCons, \<omega>def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
  using assms 
  by (cases) (auto elim: red_pure_exps_total_singleton)

lemma var_expr_wf_rel: "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Var x) \<gamma> \<gamma>"
  by (rule expr_wf_rel_intro_trivial) (auto simp: var_never_fails)

lemma lit_expr_wf_rel: "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.ELit lit) \<gamma> \<gamma>"
  by (rule expr_wf_rel_intro_trivial) (auto simp: lit_never_fails)

lemma unop_expr_wf_rel_2:
  assumes "expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>'"
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Unop uop e) \<gamma> \<gamma>'"
  using assms
  by (fastforce dest: unop_elim wf_rel_normal_elim wf_rel_failure_elim
                intro: wf_rel_intro)

abbreviation wf_rel_bop_op 
  where "wf_rel_bop_op R R' ctxt_vpr StateCons P ctxt e1 bop e2 \<equiv>  wf_rel R R'
            (\<lambda>\<omega>def \<omega>. (\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v1) \<and> 
                                ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v2) \<and> 
                                (\<exists>v'. eval_binop v1 bop v2 = BinopNormal v'))
                       )
            (\<lambda>\<omega>def \<omega>. (\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v1) \<and> 
                                ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v2) \<and> 
                                eval_binop v1 bop v2 = BinopOpFailure))
            P ctxt"

lemma binop_eager_expr_wf_rel:
  assumes 
   Lazy:"binop_lazy bop = None" and
   Rel1: "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 \<gamma>1" and
   Rel2: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 \<gamma>1 \<gamma>2" and
   RelOp: "wf_rel_bop_op R R ctxt_vpr StateCons P ctxt e1 bop e2 \<gamma>2 \<gamma>3"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 \<gamma>3"
proof (rule expr_wf_rel_intro)
  text\<open>Normal case\<close>
  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and RedExp:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  from RedExp
  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega>def \<omega> ns'"
  proof cases
    case (RedBinop v1 v2)
      from this obtain ns' where
             "R \<omega>def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast
      from this obtain ns'' where
             "R \<omega>def \<omega> ns''" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns'')"
        using wf_rel_normal_elim[OF Rel2] RedBinop
        using red_ast_bpl_transitive by blast
      thus ?thesis      
        using wf_rel_normal_elim[OF RelOp] RedBinop
        using red_ast_bpl_transitive by blast
  next
    case (RedBinopLazy v1)
    then show ?thesis using \<open>binop_lazy _ = _\<close> eval_binop_lazy_iff_2
      by (metis option.distinct(1))
  qed
next
  text \<open>Failure case\<close>
  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"

  hence Red:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp
  from Red
  show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) c' \<and> snd c' = Failure"
  proof cases 
  next
    case (RedBinopRightFailure v1)    
      from this obtain ns' where
             "R \<omega>def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    moreover from this obtain c' where
      "snd c' = Failure" and
      "red_ast_bpl P ctxt (\<gamma>1, Normal ns') c'"
      using wf_rel_failure_elim[OF Rel2 \<open>R \<omega>def \<omega> ns'\<close>] RedBinopRightFailure
      by blast
    ultimately show ?thesis
      using red_ast_bpl_transitive
      by blast
  next
    case (RedBinopOpFailure v1 v2)
      from this obtain ns' where
         "R \<omega>def \<omega> ns'" and
         "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns')"
        using wf_rel_normal_elim[OF Rel1 R] wf_rel_normal_elim[OF Rel2] red_ast_bpl_def
        by (metis (no_types, lifting) rtranclp_trans)
      then show ?thesis
      using wf_rel_failure_elim[OF RelOp \<open>R \<omega>def \<omega> ns'\<close>] RedBinopOpFailure red_ast_bpl_def
      by (metis (no_types, lifting) rtranclp_trans)      
  next
    case RedSubFailure
    then show ?thesis
      using wf_rel_failure_elim[OF Rel1 R]
      by (fastforce elim: red_pure_exps_total_singleton)
  qed
qed

lemma binop_lazy_expr_wf_rel:
 assumes 
   Lazy:"binop_lazy bop = Some(b1,bResult)" and
   Rel1: "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 \<gamma>1" and
   Rel2a: "expr_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and> 
                        (\<exists>b. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b) \<and> b \<noteq> b1 \<and> 
                             (\<exists> v2. eval_binop b bop v2 \<noteq> BinopTypeFailure))
                       ) ctxt_vpr StateCons P ctxt e2 \<gamma>1 \<gamma>2" and
   Rel2b: "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt \<gamma>1 \<gamma>2"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 \<gamma>2"
proof (rule expr_wf_rel_intro)
  text \<open>Normal case\<close>
    fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and RedExp:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  from RedExp 
  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega>def \<omega> ns'"
  proof cases
    case (RedBinop v1 v2)
    hence "v1 \<noteq> b1" using Lazy eval_binop_lazy_iff by force
    from RedBinop have v1BinopWellTy:"\<exists> v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure"
      by (metis binop_result.distinct(3))
    from RedBinop obtain ns' where
             "R \<omega>def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast
    from this \<open>v1 \<noteq> b1\<close> show ?thesis
      using wf_rel_normal_elim[OF Rel2a] RedBinop v1BinopWellTy
      using red_ast_bpl_transitive by blast
  next
    case (RedBinopLazy v1)
    hence  *:"binop_lazy bop = Some(v1, v)"
      by (simp add: eval_binop_lazy_iff)

    from RedBinopLazy obtain ns' where  
             "R \<omega>def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"            
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    thus ?thesis
      using wf_rel_normal_elim[OF Rel2b \<open>R \<omega>def \<omega> ns'\<close>] RedBinopLazy Lazy *
      by (metis (no_types, lifting) Pair_inject option.inject red_ast_bpl_transitive)
  qed
next
  text \<open>Failure case\<close>
  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"
    hence Red:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp
  from Red
  show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) c' \<and> snd c' = Failure"
  proof cases
  next
    case (RedBinopRightFailure v1)    
      from this obtain ns' where
             Red_s_s':"R \<omega>def \<omega> ns'"
                      "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    from \<open>eval_binop_lazy v1 bop = None\<close> have "v1 \<noteq> b1"
      using Lazy eval_binop_lazy_iff by force
    from this show ?thesis
      using Red_s_s' wf_rel_failure_elim[OF Rel2a HOL.conjI[OF Red_s_s'(1)] RedBinopRightFailure(2)] RedBinopRightFailure(1)
            \<open>\<exists>v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure\<close>
      using red_ast_bpl_transitive by blast
  next
    case (RedBinopOpFailure v1 v2)  
    moreover from this have "binop_lazy bop = None"
      using eval_binop_failure
      by fastforce
    ultimately show ?thesis
      using \<open>binop_lazy bop = Some(_)\<close> option.distinct(1)
      by metis        
  next
    case RedSubFailure
    then show ?thesis
      using wf_rel_failure_elim[OF Rel1 R]
      by (fastforce elim: red_pure_exps_total_singleton)
  qed
qed

inductive_cases RedOldFailure_case:
  "ctxt_vpr, StateCons, \<omega>def_opt \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

lemma old_expr_wf_rel:
  assumes ROld_implies_R: "\<And>\<omega>def \<omega> \<omega>def_old \<omega>_old ns.
                               \<comment>\<open>the first premise gives us information from the state relation that does not depend on the Boogie state\<close>
                               (\<exists>ns'. R \<omega>def \<omega> ns') \<Longrightarrow> 
                               ROld (f \<omega>def \<omega>) \<omega>def_old \<omega>_old ns \<Longrightarrow>
                               \<omega>def_old = \<omega>def \<lparr> get_total_full := the (get_trace_total \<omega> lbl) \<rparr> \<and>
                               \<omega>_old    = \<omega>    \<lparr> get_total_full := the (get_trace_total \<omega> lbl) \<rparr> \<Longrightarrow>
                               R \<omega>def \<omega> ns"
      and R_implies_ROld: "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow>
                          (ROld
                            (f \<omega>def \<omega>)
                            (\<omega>def \<lparr> get_total_full := (the (get_trace_total \<omega> lbl)) \<rparr>)
                            (\<omega> \<lparr> get_total_full := (the (get_trace_total \<omega> lbl)) \<rparr>)
                            ns \<and>
                          expr_wf_rel (ROld (f \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>')"
      and R_implies_trace_exists:"\<And> \<omega>def \<omega> ns.  R \<omega>def \<omega> ns \<Longrightarrow>
                                    get_trace_total \<omega>def lbl \<noteq> None \<and>
                                    get_trace_total \<omega> lbl \<noteq> None"
    shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (pure_exp.Old lbl expr) \<gamma> \<gamma>'"
proof (rule expr_wf_rel_intro)
  let ?IsNormal = "(\<lambda>\<omega>def \<omega>. \<exists>v. (ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>expr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v))"
  let ?IsFailure = "(\<lambda>\<omega>def \<omega>. (ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>expr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure))"
  show "\<And>v \<omega>def \<omega> ns.
       R \<omega>def \<omega> ns \<Longrightarrow>
       ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow>
       \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
  proof -
    fix v \<omega>def \<omega> ns
    assume R: "R \<omega>def \<omega> ns"
       and judgement: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
    from judgement obtain \<phi> where
      trace_is_phi: "get_trace_total \<omega> lbl = Some \<phi>" and
      old_judgement: "ctxt_vpr, StateCons, Some (\<omega>def \<lparr> get_total_full := \<phi> \<rparr>) \<turnstile> \<langle>expr; \<omega>\<lparr> get_total_full := \<phi> \<rparr>\<rangle> [\<Down>]\<^sub>t Val v"
      by(cases) simp
    let ?\<omega>_old = "\<omega> \<lparr> get_total_full := \<phi> \<rparr>"
    let ?\<omega>def_old = "\<omega>def \<lparr> get_total_full := \<phi> \<rparr>"
    from trace_is_phi have \<omega>old_def:
          "?\<omega>def_old = \<omega>def \<lparr> get_total_full := the (get_trace_total \<omega> lbl ) \<rparr> \<and>
           ?\<omega>_old = \<omega> \<lparr> get_total_full := the (get_trace_total \<omega> lbl) \<rparr>"
      by simp
    from R R_implies_ROld trace_is_phi have
      ROld_and_interior_expr_wf: "ROld (f \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns \<and>
             expr_wf_rel (ROld (f \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
      by force
    from old_judgement have is_normal: "?IsNormal ?\<omega>def_old ?\<omega>_old"
      by auto
    from is_normal ROld_and_interior_expr_wf obtain ns' where
      ROld_ns': "ROld (f \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns'" and
      normal_termination: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
      using wf_rel_normal_elim
      by blast
    from ROld_ns' ROld_implies_R \<omega>old_def have R_ns': "R \<omega>def \<omega> ns'" 
      using R 
      by blast
    from normal_termination R_ns' show
      "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
      by auto
  qed
  show "\<And>v \<omega>def \<omega> ns.
       R \<omega>def \<omega> ns \<Longrightarrow>
       ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow>
       v = VFailure \<Longrightarrow> \<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  proof -
    fix v \<omega>def \<omega> ns
    assume R: "R \<omega>def \<omega> ns"
       and v_judgement: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t v"
       and v_failure: "v = VFailure"
    show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
    proof -
      from v_judgement v_failure have
        "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>pure_exp.Old lbl expr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        by simp
      thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      proof (rule RedOldFailure_case)
        show "\<And>\<phi>. get_trace_total \<omega> lbl = Some \<phi> \<Longrightarrow>
                    ctxt_vpr, StateCons, map_option (get_total_full_update (\<lambda>_. \<phi>))
                      (Some \<omega>def) \<turnstile> \<langle>expr;\<omega>\<lparr>get_total_full := \<phi>\<rparr>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow>
                      \<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
         (is "\<And>\<phi>. get_trace_total \<omega> lbl = Some \<phi> \<Longrightarrow>
                    ctxt_vpr, StateCons, map_option (get_total_full_update (\<lambda>_. \<phi>)) (Some \<omega>def) \<turnstile> \<langle>expr;\<omega>\<lparr>get_total_full := \<phi>\<rparr>\<rangle> [\<Down>]\<^sub>t VFailure  \<Longrightarrow>
                    ?conclusion")
        proof -
          fix \<phi>
          assume "get_trace_total \<omega> lbl = Some \<phi>"
          hence the_trace_is_phi: "\<phi> = the (get_trace_total \<omega> lbl)" by simp
          let ?\<omega>_old = "\<omega> \<lparr> get_total_full := \<phi> \<rparr>"
          let ?\<omega>def_old = "\<omega>def \<lparr> get_total_full := \<phi> \<rparr>"
          assume "ctxt_vpr, StateCons, map_option (get_total_full_update (\<lambda>_. \<phi>)) (Some \<omega>def) \<turnstile> \<langle>expr;\<omega>\<lparr>get_total_full := \<phi>\<rparr>\<rangle> [\<Down>]\<^sub>t VFailure"
          hence "ctxt_vpr, StateCons, (Some ?\<omega>def_old) \<turnstile> \<langle>expr;?\<omega>_old\<rangle> [\<Down>]\<^sub>t VFailure" by simp
          hence is_failure: "?IsFailure ?\<omega>def_old ?\<omega>_old" by simp
          from R R_implies_ROld the_trace_is_phi have
            ROld_and_interior_expr_wf: "ROld (f \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns \<and>
            expr_wf_rel (ROld (f \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
            by fastforce
          from ROld_and_interior_expr_wf is_failure show ?conclusion
            using wf_rel_failure_elim
            by fast
        qed
        show "get_trace_total \<omega> lbl = None \<Longrightarrow>
               \<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
         (is "get_trace_total \<omega> lbl = None \<Longrightarrow> ?conclusion")
        proof -
          assume no_trace: "get_trace_total \<omega> lbl = None"
          from no_trace R R_implies_trace_exists have "False" by simp
          thus ?conclusion by simp
        qed
      qed (simp)
    qed
  qed
qed


\<comment>\<open>You could split this theorem into two (one for m and one for h), I proved it here (except for one sorry) to show 
  how it can be done concisely. Also: This theorem should be moved to ViperBoogieBasicRel.thy\<close>

lemma state_rel_add_label:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" 
      and "lbls = label_hm_translation Tr"
      and "lbls' = (((fst lbls)(lbl \<mapsto> h)), ((snd lbls)(lbl \<mapsto> m)))"
      and LabelExists: "get_trace_total \<omega> lbl = Some \<phi>"
      and HeapRel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) h (get_hh_total \<phi>) ns"
      and MaskRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) m (get_mh_total \<phi>) ns"
      and Disj: "{m,h} \<inter>  ( {heap_var Tr, heap_var_def Tr} \<union>
                                      {mask_var Tr, mask_var_def Tr} \<union>
                                       ran (var_translation Tr) \<union>
                                       ran (field_translation Tr) \<union>
                                       range (const_repr Tr) \<union>
                                       dom AuxPred) = {}"
      and "Tr' = Tr \<lparr> label_hm_translation := lbls' \<rparr>"
    shows "state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI, simp_all add: \<open>Tr' = _\<close>) 
  show "disjoint_list
     [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred,
      vars_label_hm_tr lbls']" (is "disjoint_list ?A'")
  proof -
    have "disjoint_list
     ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr),
        range (const_repr Tr), dom AuxPred]@(vars_label_hm_tr lbls # []))" 
      using state_rel_disjoint[OF StateRel] \<open>lbls = _\<close>
      by auto
    hence "disjoint_list
     ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr),
        range (const_repr Tr), dom AuxPred]@((vars_label_hm_tr lbls \<union> {m,h}) # []))" (is "disjoint_list ?A")
      apply (rule disjoint_list_add_set)
      using Disj
      by fastforce
    thus ?thesis
    proof (rule disjoint_list_subset, simp)
      have *: "vars_label_hm_tr lbls' \<subseteq> vars_label_hm_tr lbls \<union> {m,h}"
        unfolding \<open>lbls' = _\<close> vars_label_hm_tr_def
        using ran_map_upd_subset
        by force
      fix i j
      assume "0 \<le> i" and
             "i < length ?A"
      show "?A' ! i \<subseteq> ?A ! i"            
      apply (cases i)
       apply simp
      apply (rename_tac i1)
      apply (case_tac i1)
       apply simp
      apply (rename_tac i2)
      apply (case_tac i2)
      apply simp
      apply (rename_tac i3)
      apply (case_tac i3)
       apply simp
      apply (rename_tac i4)
      apply (case_tac i4)
       apply simp
      apply (rename_tac i5)
      apply (case_tac i5)
       apply simp
      apply (rename_tac i6)
      apply (case_tac i6)
      using *
       apply simp
      by simp
    qed
  qed
  show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) lbls' (get_trace_total \<omega>) ns"
    unfolding label_hm_rel_def
      unfolding label_rel_def
      using \<open>lbls' = _\<close> \<open>lbls = _\<close> LabelExists HeapRel MaskRel state_rel_label_hm_rel[OF StateRel, simplified label_hm_rel_def label_rel_def]
      by auto
qed (insert StateRel[simplified state_rel_def state_rel0_def], (simp | argo)+)
\<comment>\<open>"insert StateRel[simplified state_rel_def state_rel0_def]" adds the state relation assumption in unfolded
form to all subgoals and (simp | argo)+ applies simp or argo until neither works\<close>

lemma old_expr_wf_rel_inst:
  assumes WfTotalConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      (* and "R = state_rel Pr StateCons TyRep Tr AuxPred ctxt" *)
      and "R = (\<lambda>\<omega>def \<omega> ns. state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<and> Q \<omega>def \<omega>)"
      and "lbls = label_hm_translation Tr"
      and OldH: "fst lbls lbl = Some OldH"
      and OldM: "snd lbls lbl = Some OldM"
      and DisjAux: "OldH \<notin> state_rel0_disj_vars Tr AuxPred \<and> OldM \<notin> state_rel0_disj_vars Tr AuxPred \<and> OldH \<noteq> OldM"
      and mh: "m = mask_var Tr \<and> h = heap_var Tr \<and> mdef = mask_var_def Tr \<and> hdef = heap_var_def Tr"
      and "lbls' = (((fst lbls)(lbl := None)), ((snd lbls)(lbl := None)))"
      and "Tr' = Tr \<lparr> heap_var := OldH, mask_var := OldM, heap_var_def := OldH, mask_var_def := OldM, label_hm_translation := lbls' \<rparr>"
      and BodyRel:
         "\<And>p1 p2 p3 p4. expr_wf_rel (state_rel Pr StateCons TyRep Tr' (AuxPred(mdef \<mapsto> p1, hdef \<mapsto> p2, m \<mapsto> p3, h \<mapsto> p4)) ctxt)
                                      ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (pure_exp.Old lbl expr) \<gamma> \<gamma>'"
proof -
  let ?AuxPredFun = "(\<lambda>\<omega>def \<omega>.(AuxPred 
                            (mdef \<mapsto> pred_eq_mask Pr TyRep (field_translation Tr) ctxt mdef \<omega>def)
                            (hdef \<mapsto> pred_eq_heap Pr TyRep (field_translation Tr) ctxt hdef \<omega>def)
                            (m \<mapsto> pred_eq_mask Pr TyRep (field_translation Tr) ctxt m \<omega>)                    
                            (h \<mapsto> pred_eq_heap Pr TyRep (field_translation Tr) ctxt h \<omega>)
                            ))"
  let ?\<Lambda> = "var_context ctxt"

  show ?thesis
  proof (rule old_expr_wf_rel[where ?f = ?AuxPredFun])

    let ?ROld = "\<lambda>AuxPred. state_rel Pr StateCons TyRep Tr' AuxPred ctxt"

    fix \<omega>def :: "'a full_total_state"
    fix \<omega> :: "'a full_total_state"
    fix ns  
    show "\<And> \<omega>def_old \<omega>_old.
       \<exists>ns'. R \<omega>def \<omega> ns' \<Longrightarrow>
       ?ROld (?AuxPredFun \<omega>def \<omega>) \<omega>def_old \<omega>_old ns \<Longrightarrow>
       \<omega>def_old = \<omega>def \<lparr> get_total_full := the (get_trace_total \<omega> lbl)\<rparr> \<and>
       \<omega>_old    = \<omega>    \<lparr> get_total_full := the (get_trace_total \<omega> lbl)\<rparr> \<Longrightarrow>
       R \<omega>def \<omega> ns"
    proof -
      fix \<omega>def_old \<omega>_old
        (* First assumption added here *)
      assume RPrev: "\<exists>ns0. R \<omega>def \<omega> ns0"
        and ROld: "?ROld (?AuxPredFun \<omega>def \<omega>) \<omega>def_old \<omega>_old ns"
        and \<omega>_old: "\<omega>def_old = \<omega>def \<lparr> get_total_full := the (get_trace_total \<omega> lbl) \<rparr> \<and>
                   \<omega>_old    = \<omega>    \<lparr> get_total_full := the (get_trace_total \<omega> lbl) \<rparr>"

      from RPrev \<open>R =_\<close> obtain ns0 where RPrevInst: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns0"
        by auto

      from RPrevInst and OldH OldM obtain \<phi>
        where LabelExists: "get_trace_total \<omega> lbl = Some \<phi>"
          and HeapRelOld: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) OldH (get_hh_total \<phi>) ns"
          and MaskRelOld: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) OldM (get_mh_total \<phi>) ns"
        sorry \<comment>\<open>There should be an auxiliary lemma in ViperBoogieBasicRel that shows this 
              (this lemma can then also be used for the final goal of this theorem)\<close>

      (* Should add a lemma that says this, could be obtains or shows *)

\<comment>\<open>In a first step, let's revert the heap and mask, while leaving the labels.\<close>

      let ?Tr2 = "Tr \<lparr> label_hm_translation := lbls' \<rparr>"
      have "state_rel Pr StateCons TyRep ?Tr2 AuxPred ctxt \<omega>def \<omega> ns"
      proof (rule state_rel_capture_total_state_change_eval_and_def_state[OF _ ROld], simp)
        show "{m, mdef} \<inter> {h, hdef} = {}"
          using RPrev[simplified \<open>R = _\<close>] mh state_rel_mask_var_disjoint
          by blast
      next
        show "field_translation Tr = field_translation ?Tr2"
          using \<open>Tr' = _\<close>
          by auto
      next
        show "{m, h, mdef, hdef} \<inter> dom AuxPred = {}"
        proof -
          have "{m, mdef} \<inter> dom AuxPred = {}"
            using RPrev[simplified \<open>R = _\<close>] mh state_rel_mask_var_disjoint 
            by blast
          moreover have "{h, hdef} \<inter> dom AuxPred = {}"
            using RPrev[simplified \<open>R = _\<close>] mh state_rel_heap_var_disjoint
            by blast
          ultimately show ?thesis
            by auto
        qed
      next
        fix mb :: "'a bpl_mask_ty"
        assume "mdef = m" 
        show "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>) mb =
            mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb"
        proof -
          have ltr: "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>) mb \<Longrightarrow>
                   mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb"
          proof -
            assume "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>) mb"
            thus "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb"
              by (smt (verit) RPrevInst Semantics.val.inject(2) \<open>mdef = m\<close> mask_rel_def mask_var_rel_def mh option.sel state_rel_mask_var_def_rel state_rel_obtain_mask tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) vbpl_absval.inject(5))
          qed
          have rtl: "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb \<Longrightarrow>
                   mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>) mb"
          proof -
            assume "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb"
            show "mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>) mb"
              by (smt (verit) RPrevInst Semantics.val.inject(2) \<open>mask_rel Pr (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) (get_mh_total_full \<omega>def) mb\<close> \<open>mdef = m\<close> mask_rel_def mask_var_rel_def mh option.sel state_rel_mask_var_def_rel state_rel_obtain_mask tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) vbpl_absval.inject(5))
          qed
          show ?thesis
            using ltr rtl
            by auto
        qed
      next
        fix hb :: "'a bpl_heap_ty"
        show "pred_eq_heap_aux Pr TyRep (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) \<omega> hb =
          pred_eq_heap_aux Pr TyRep (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) \<omega>def hb \<and>
          total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>) =
          total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
          by (metis RPrevInst fst_conv get_h_total_full.simps pred_eq_heap_aux_def state_rel_eval_welldef_eq)
      qed (simp add: \<open>Tr' = _\<close> mh)

\<comment>\<open>In a second step, let's revert the labels\<close>
      thus "R \<omega>def \<omega> ns"
      proof (subst \<open>R = _\<close>, intro conjI)
        show "state_rel Pr StateCons TyRep (Tr\<lparr>label_hm_translation := lbls'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
        proof (rule state_rel_add_label, simp, simp, simp)
          show "(get_trace_total \<omega> lbl) = Some \<phi>"
            using LabelExists
            by simp

          show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) OldH (get_hh_total \<phi>) ns"
            using HeapRelOld
            by simp

          show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) OldM (get_mh_total \<phi>) ns"
            using MaskRelOld
            by simp

          show "{OldM, OldH} \<inter>
              ({heap_var (Tr\<lparr>label_hm_translation := lbls'\<rparr>), heap_var_def (Tr\<lparr>label_hm_translation := lbls'\<rparr>)} \<union>
               {mask_var (Tr\<lparr>label_hm_translation := lbls'\<rparr>), mask_var_def (Tr\<lparr>label_hm_translation := lbls'\<rparr>)} \<union>
               ran (var_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) \<union>
               ran (field_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) \<union>
               range (const_repr (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) \<union>
               dom AuxPred) = {}"
          proof -
            have "{OldM, OldH} \<subseteq> vars_label_hm_tr (label_hm_translation Tr)"
              using OldH OldM \<open>lbls = _\<close>
              unfolding vars_label_hm_tr_def
              by (simp add: ranI)

            with state_rel_label_hm_disjoint[OF RPrevInst]
            show ?thesis
              by force 
          qed

          show "Tr = Tr\<lparr>label_hm_translation := lbls', label_hm_translation := (fst lbls'(lbl \<mapsto> OldH), snd lbls'(lbl \<mapsto> OldM))\<rparr>"
          proof -
            have "lbls = (fst lbls'(lbl \<mapsto> OldH), snd lbls'(lbl \<mapsto> OldM))"
              unfolding \<open>lbls' = _\<close>
              using OldH OldM
              by (simp add: map_upd_triv)
            thus ?thesis
              using \<open>lbls = label_hm_translation Tr\<close>
              by fastforce        
          qed
        qed
        show "Q \<omega>def \<omega>"
          using RPrev \<open>R = _\<close>
          by simp
      qed
    qed

    let ?\<omega>def_old = "\<omega>def \<lparr> get_total_full := the (get_trace_total \<omega> lbl)\<rparr>"
    let ?\<omega>_old = "\<omega>\<lparr> get_total_full := the (get_trace_total \<omega> lbl)\<rparr>"
    show "R \<omega>def \<omega> ns \<Longrightarrow>
             ?ROld (?AuxPredFun \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns \<and>
         expr_wf_rel (?ROld (?AuxPredFun \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
    proof -    
      \<comment>\<open>Second assumption: assume R\<close>
      assume R: "R \<omega>def \<omega> ns"
      note RInst = R[simplified \<open>R = _\<close>]

      obtain \<phi> where "get_trace_total \<omega> lbl = Some \<phi>"
        by (metis (mono_tags, lifting) OldM RInst \<open>lbls = _\<close> label_hm_rel_def label_rel_def state_rel_label_hm_rel)

      let ?Tr2 = "Tr \<lparr> label_hm_translation := lbls' \<rparr>"

\<comment>\<open>Step 1: remove OldM and OldH from the translation record so we don't require disjointness with them\<close>
      have "state_rel Pr StateCons TyRep ?Tr2 AuxPred ctxt \<omega>def \<omega> ns"
        unfolding state_rel_def state_rel0_def
      proof(intro conjI)
        show "valid_heap_mask (get_mh_total_full \<omega>def)"
          using RInst state_rel_wf_mask_def_simple
          by blast
        show "valid_heap_mask (get_mh_total_full \<omega>)"
          using RInst state_rel_wf_mask_simple
          by blast
        show "consistent_state_rel_opt (state_rel_opt ?Tr2) \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>"
          using RInst state_rel_consistent
          by fastforce
        show "type_interp ctxt = vbpl_absval_ty TyRep"
          using RInst state_rel_type_interp
          by blast
        show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation ?Tr2) (get_store_total \<omega>) ns"
          using RInst state_rel_store_rel
          by fastforce
        show "disjoint_list (state_rel0_disj_list ?Tr2 AuxPred)"
        proof -
          let ?list_Tr = "state_rel0_disj_list Tr AuxPred"
          let ?list_Tr2 = "state_rel0_disj_list ?Tr2 AuxPred"
          have disjoint_list_Tr: "disjoint_list ?list_Tr"
            using RInst state_rel_disjoint
            by blast
          thus "disjoint_list ?list_Tr2"
          proof (cases "lbls' = lbls")
            case True
            show ?thesis
              using True disjoint_list_Tr \<open>lbls = _ \<close>
              by simp
          next
            case False
            let ?xs = "[{heap_var Tr, heap_var_def Tr},
                      {mask_var Tr, mask_var_def Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr)),
                      dom AuxPred]"
            let ?xs' = "[{heap_var ?Tr2, heap_var_def ?Tr2},
                      {mask_var ?Tr2, mask_var_def ?Tr2},
                      (ran (var_translation ?Tr2)), 
                      (ran (field_translation ?Tr2)),
                      (range (const_repr ?Tr2)),
                      dom AuxPred]"
            have xs_equals_xs': "?xs = ?xs'"
              by simp
            let ?M = "vars_label_hm_tr (label_hm_translation Tr)"
            let ?M' = "vars_label_hm_tr (label_hm_translation ?Tr2)"
            let ?ys = "[]"
            have "?list_Tr = ?xs @ ?M # ?ys"
              by force
            have "?list_Tr2 = ?xs' @ ?M' # ?ys"
              by simp
            have "disjoint_list (?xs' @ ?M' # ?ys)"
            proof (rule disjoint_list_one_subset)
              show "disjoint_list (?xs' @ ?M # ?ys)"
                using disjoint_list_Tr by fastforce
              show "?M' \<subseteq> ?M"
              proof -
                have heap_subset: "ran (fst lbls') \<subseteq> ran (fst lbls)"
                  by (metis (mono_tags, lifting) OldH \<open>lbls' = _\<close> fst_conv fun_upd_same fun_upd_triv fun_upd_upd order_refl ran_map_upd subset_insertI2)
                have map_subset: "ran (snd lbls') \<subseteq> ran (snd lbls)"
                  by (metis (mono_tags, lifting) OldM \<open>lbls' = _\<close> fun_upd_same fun_upd_triv fun_upd_upd order_refl ran_map_upd snd_conv subset_insertI2)
                show "?M' \<subseteq> ?M" 
                  using \<open>lbls = _\<close> heap_subset map_subset vars_label_hm_tr_def
                  by auto
              qed
            qed
            hence "disjoint_list ?list_Tr2" by simp
            thus ?thesis by simp
          qed
        qed
        show "get_store_total \<omega>def = get_store_total \<omega>"
          using RInst state_rel_eval_welldef_eq
          by fastforce
        show "get_h_total_full \<omega>def = get_h_total_full \<omega>"
          using RInst state_rel_eval_welldef_eq
          by fast
        show "get_trace_total \<omega>def = get_trace_total \<omega>"
          using RInst state_rel_eval_welldef_eq
          by blast
        show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) (heap_var ?Tr2) (get_hh_total_full \<omega>) ns"
          using RInst state_rel_heap_var_rel by fastforce
        show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2)(mask_var ?Tr2) (get_mh_total_full \<omega>) ns"
          using RInst state_rel_mask_var_rel
          by force
        show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) (heap_var_def ?Tr2) (get_hh_total_full \<omega>def) ns"
          using RInst state_rel_heap_var_def_rel
          by fastforce
        show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) (mask_var_def ?Tr2) (get_mh_total_full \<omega>def) ns"
          using RInst state_rel_mask_var_def_rel
          by force
        show "field_rel Pr (var_context ctxt) (field_translation ?Tr2) ns"
          using RInst state_rel_field_rel
          by fastforce
        show "boogie_const_rel (const_repr ?Tr2) (var_context ctxt) ns"
          using RInst state_rel_boogie_const_rel
          by force
        show "state_well_typed (type_interp ctxt) (var_context ctxt) [] ns"
          using RInst state_rel_state_well_typed
          by blast
        show "aux_vars_pred_sat (var_context ctxt) AuxPred ns"
          using RInst state_rel_aux_vars_pred_sat
          by fast
        show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) (label_hm_translation ?Tr2) (get_trace_total \<omega>) ns"
          unfolding label_hm_rel_def
        proof (intro conjI)
          let ?HeapPred = "\<lambda>h \<phi>. heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) h (get_hh_total \<phi>)"
          show "label_rel ?HeapPred (fst (label_hm_translation ?Tr2)) (get_trace_total \<omega>) ns"
            unfolding label_rel_def
          proof (intro allI, rule impI)
            fix lbl h
            assume "fst (label_hm_translation ?Tr2) lbl = Some h"
            then obtain \<phi> where
              trace_defined: "get_trace_total \<omega> lbl = Some \<phi>"
              by (smt (verit, best) RInst \<open>lbls = _\<close> \<open>lbls' = _\<close> fst_conv fun_upd_apply label_hm_rel_def label_rel_def option.discI state_rel_label_hm_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9))
            show "\<exists>\<phi>. get_trace_total \<omega> lbl = Some \<phi> \<and> heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) h (get_hh_total \<phi>) ns"
            proof (rule exI)
              show "get_trace_total \<omega> lbl = Some \<phi> \<and> heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) h (get_hh_total \<phi>) ns"
              proof (intro conjI)
                show "get_trace_total \<omega> lbl = Some \<phi>"
                  using trace_defined
                  by simp
                show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) h (get_hh_total \<phi>) ns"
                  by (smt (verit, ccfv_SIG) RInst \<open>fst (label_hm_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) lbl = Some h\<close> \<open>lbls = _\<close> \<open>lbls' = _\<close> fst_conv fun_upd_apply label_hm_rel_def label_rel_def option.discI option.sel state_rel_label_hm_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) trace_defined)
              qed
            qed
          qed
          let ?MaskPred = "\<lambda>m \<phi>. mask_var_rel Pr (var_context ctxt) TyRep (field_translation ?Tr2) m (get_mh_total \<phi>)"
          show "label_rel ?MaskPred (snd (label_hm_translation ?Tr2)) (get_trace_total \<omega>) ns"
            unfolding label_rel_def
          proof (intro allI, rule impI)
            fix lbl h
            assume "snd (label_hm_translation ?Tr2) lbl = Some h"
            then obtain \<phi> where
              trace_defined: "get_trace_total \<omega> lbl = Some \<phi>"
              by (smt (verit, ccfv_threshold) RInst \<open>lbls = _\<close> \<open>lbls' = _\<close> domI label_hm_rel_def label_rel_def map_le_def snd_conv state_rel_label_hm_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) upd_None_map_le)
            show "\<exists>\<phi>. get_trace_total \<omega> lbl = Some \<phi> \<and> mask_var_rel Pr (var_context ctxt) TyRep (field_translation  ?Tr2) h (get_mh_total \<phi>) ns"
              by (smt (verit, ccfv_SIG) RInst \<open>snd (label_hm_translation (Tr\<lparr>label_hm_translation := lbls'\<rparr>)) lbl = Some h\<close> \<open>lbls = _\<close> \<open>lbls' = _\<close> fun_upd_apply label_hm_rel_def label_rel_def option.discI snd_conv state_rel_label_hm_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9))
          qed
          show "\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
            by (meson RInst label_hm_rel_def state_rel_label_hm_rel)
        qed
      qed

        \<comment>\<open>Step 2: change to old state\<close>
      have state_rel_\<omega>_old: "state_rel Pr StateCons TyRep Tr' AuxPred ctxt ?\<omega>def_old ?\<omega>_old ns"
        unfolding state_rel_def state_rel0_def
      proof (intro conjI)
        show "valid_heap_mask (get_mh_total_full ?\<omega>def_old)"
          unfolding wf_mask_simple_def
        proof (intro allI)
          fix hl
          show "get_mh_total_full ?\<omega>def_old  hl \<le> PosReal.pwrite"
            by (metis RInst \<open>get_trace_total \<omega> lbl = _\<close> full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3) get_mh_total_full.elims label_hm_rel_def option.sel state_rel_label_hm_rel wf_mask_simple_def)
        qed
        show "valid_heap_mask (get_mh_total_full (\<omega>\<lparr>get_total_full := the (get_trace_total \<omega> lbl)\<rparr>))"
          using \<open>valid_heap_mask (get_mh_total_full (\<omega>def \<lparr>get_total_full := the (get_trace_total \<omega> lbl)\<rparr>))\<close>
          by force
        show "consistent_state_rel_opt (state_rel_opt Tr') \<longrightarrow> StateCons ?\<omega>def_old \<and> StateCons ?\<omega>_old"
        proof (intro impI)
          assume premise: "consistent_state_rel_opt (state_rel_opt Tr')"
          show "StateCons ?\<omega>def_old \<and> StateCons ?\<omega>_old"
          proof (intro conjI)
            show "StateCons ?\<omega>def_old"
              by (metis WfTotalConsistency get_trace_empty_full_total_state is_empty_empty_full_total_state wf_total_consistency_def)
            thus "StateCons ?\<omega>_old"
              using RInst WfTotalConsistency state_rel_eval_welldef_eq total_consistency_store_update by fastforce
          qed
        qed
        show "type_interp ctxt = vbpl_absval_ty TyRep"
          using RInst state_rel_type_interp by blast
        show "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr') (get_store_total ?\<omega>_old) ns"
        proof -
          have "var_translation Tr' = var_translation Tr"
            using \<open>Tr' = _\<close>
            by simp
          thus "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr') (get_store_total ?\<omega>_old) ns"
            using RInst state_rel_store_rel
            by force
        qed
        show "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
        proof -
          (* First, change the heap *)
          let ?TrOldHeap = "Tr \<lparr> heap_var := OldH, heap_var_def := OldH \<rparr>"
          have "disjoint_list (state_rel0_disj_list ?TrOldHeap AuxPred)"
          proof (rule disjoint_list_change_heap)
            show "disjoint_list (state_rel0_disj_list Tr AuxPred)"
              using RInst state_rel_disjoint by blast
            show "OldH \<notin>  \<Union> (set (ViperBoogieRelUtil.state_rel0_disj_list Tr AuxPred))"
              using DisjAux by simp
          qed (simp)

          (* Next, change the mask *)
          let ?TrOld = "?TrOldHeap \<lparr> mask_var := OldM, mask_var_def := OldM \<rparr>"
          have "disjoint_list (state_rel0_disj_list ?TrOld AuxPred)"
          proof (rule disjoint_list_change_mask)
            show "disjoint_list (state_rel0_disj_list ?TrOldHeap AuxPred)"
              using \<open>disjoint_list (state_rel0_disj_list ?TrOldHeap AuxPred)\<close> by simp
            show "OldM \<notin>  \<Union> (set (ViperBoogieRelUtil.state_rel0_disj_list ?TrOldHeap AuxPred))"
              using DisjAux by simp
          qed (simp)

          (* Finally, remove lbl from labels *)
          show "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
          proof (rule disjoint_list_remove_label)
            show "disjoint_list (ViperBoogieRelUtil.state_rel0_disj_list ?TrOld AuxPred)"
              using \<open>disjoint_list (state_rel0_disj_list ?TrOld AuxPred)\<close> by simp
          next
            show "label_hm_translation Tr' = ((fst (label_hm_translation ?TrOld))(lbl := None),
                                              (snd (label_hm_translation ?TrOld))(lbl := None))"
              using \<open>Tr' = _\<close> \<open>lbls' = _\<close> \<open>lbls = _\<close> by simp
          qed (simp add: \<open>Tr' = _\<close>)
        qed
        show "get_store_total ?\<omega>def_old = get_store_total ?\<omega>_old" using RInst state_rel_eval_welldef_eq by fastforce
        show "get_trace_total ?\<omega>def_old = get_trace_total ?\<omega>_old" using RInst state_rel_eval_welldef_eq by fastforce
        show "get_h_total_full ?\<omega>def_old = get_h_total_full ?\<omega>_old" by simp
        show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full ?\<omega>_old) ns"
        proof -
          have "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (heap_var Tr') (get_hh_total \<phi>) ns"
          proof (rule label_tracked_implies_heap_rel)
            show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
              using RInst state_rel_label_hm_rel by blast
            show "get_trace_total \<omega> lbl = Some \<phi>"
              by (simp add: \<open>get_trace_total \<omega> lbl = Some \<phi>\<close>)
            show "fst (label_hm_translation Tr) lbl = Some (heap_var Tr')"
              using OldH \<open>lbls = _\<close> \<open>Tr' = _\<close> by force
          qed
          thus ?thesis using \<open>get_trace_total \<omega> lbl = Some \<phi>\<close> \<open>Tr' = _\<close> by fastforce
        qed
        show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var Tr') (get_mh_total_full ?\<omega>_old) ns"
        proof -
          have "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (mask_var Tr') (get_mh_total \<phi>) ns"
          proof (rule label_tracked_implies_mask_rel)
            show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
              using RInst state_rel_label_hm_rel by blast
            show "get_trace_total \<omega> lbl = Some \<phi>"
              by (simp add: \<open>get_trace_total \<omega> lbl = Some \<phi>\<close>)
            show "snd (label_hm_translation Tr) lbl = Some (mask_var Tr')"
              using OldM \<open>lbls = _\<close> \<open>Tr' = _\<close> by fastforce
          qed
          thus ?thesis by (simp add: \<open>get_trace_total \<omega> lbl = _\<close> \<open>Tr' = _\<close>)
        qed
        show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full ?\<omega>def_old) ns"
        proof -
          have "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (heap_var_def Tr') (get_hh_total \<phi>) ns"
          proof (rule label_tracked_implies_heap_rel)
            show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
              using RInst state_rel_label_hm_rel by blast
            show "get_trace_total \<omega> lbl = Some \<phi>"
              by (simp add: \<open>get_trace_total \<omega> lbl = Some \<phi>\<close>)
            show "fst (label_hm_translation Tr) lbl = Some (heap_var_def Tr')"
              using OldH \<open>lbls = _\<close> \<open>Tr' = _\<close> by force
          qed
          thus ?thesis
            by (simp add: \<open>get_trace_total \<omega> lbl = _\<close> \<open>Tr' = _\<close>)
        qed
        show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var_def Tr') (get_mh_total_full ?\<omega>def_old) ns"
        proof - 
          have "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (mask_var_def Tr') (get_mh_total \<phi>) ns"
          proof (rule label_tracked_implies_mask_rel)
            show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
              using RInst state_rel_label_hm_rel by blast
            show "get_trace_total \<omega> lbl = Some \<phi>"
              by (simp add: \<open>get_trace_total \<omega> lbl = Some \<phi>\<close>)
            show "snd (label_hm_translation Tr) lbl = Some (mask_var_def Tr')"
              using OldM \<open>lbls = _\<close> \<open>Tr' = _\<close> by fastforce
          qed
          thus ?thesis by (simp add: \<open>get_trace_total \<omega> lbl = Some \<phi>\<close> \<open>Tr' = _\<close>)
        qed
        show "field_rel Pr ?\<Lambda> (field_translation Tr') ns"
          using RInst \<open>Tr' = _\<close> state_rel_field_rel
          by force
        show "boogie_const_rel (const_repr Tr') ?\<Lambda> ns"
          using RInst state_rel_boogie_const_rel \<open>Tr' = _\<close>
          by fastforce
        show "state_well_typed (type_interp ctxt) ?\<Lambda> [] ns"
          using RInst state_rel_state_well_typed
          by fast
        show "aux_vars_pred_sat  ?\<Lambda> AuxPred ns"
          using RInst state_rel_aux_vars_pred_sat
          by fast    
        show "label_hm_rel Pr ?\<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total ?\<omega>_old) ns"
          using \<open>state_rel Pr StateCons TyRep (Tr\<lparr>label_hm_translation := lbls'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns\<close> \<open>Tr' = _\<close> state_rel_label_hm_rel by force
      qed

\<comment>\<open>Step 3: capture original heap and mask variables in auxiliary variables\<close>
      have "state_rel Pr StateCons TyRep Tr' (?AuxPredFun \<omega>def \<omega>) ctxt ?\<omega>def_old ?\<omega>_old ns"
        unfolding state_rel_def state_rel0_def
      proof (intro conjI)
        show "valid_heap_mask (get_mh_total_full ?\<omega>def_old)"
          using state_rel_\<omega>_old state_rel_wf_mask_def_simple by blast
        show "valid_heap_mask (get_mh_total_full ?\<omega>_old)"
          using state_rel_\<omega>_old state_rel_wf_mask_simple by blast
        show "consistent_state_rel_opt (state_rel_opt Tr') \<longrightarrow> StateCons ?\<omega>def_old \<and> StateCons ?\<omega>_old"
          using state_rel_\<omega>_old state_rel_consistent by blast
        show "type_interp ctxt = vbpl_absval_ty TyRep"
          using RInst state_rel_type_interp
          by fast
        show "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr') (get_store_total ?\<omega>_old) ns"
          using state_rel_\<omega>_old state_rel_store_rel
          by fast
        show "get_store_total ?\<omega>def_old = get_store_total ?\<omega>_old"
          using state_rel_\<omega>_old state_rel_eval_welldef_eq by blast
        show "get_trace_total ?\<omega>def_old = get_trace_total ?\<omega>_old"
          using state_rel_\<omega>_old state_rel_eval_welldef_eq by blast
        show "get_h_total_full ?\<omega>def_old = get_h_total_full ?\<omega>_old"
          by simp
        show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full ?\<omega>_old) ns"
          using state_rel_\<omega>_old state_rel_heap_var_rel by blast
        show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var Tr') (get_mh_total_full ?\<omega>_old) ns"
          using state_rel_\<omega>_old state_rel_mask_var_rel by blast
        show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full ?\<omega>def_old) ns"
          using state_rel_\<omega>_old state_rel_heap_var_def_rel by blast
        show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var_def Tr') (get_mh_total_full ?\<omega>def_old) ns"
          using state_rel_\<omega>_old state_rel_mask_var_def_rel by blast
        show "field_rel Pr ?\<Lambda> (field_translation Tr') ns"
          using state_rel_\<omega>_old state_rel_field_rel by blast
        show "boogie_const_rel (const_repr Tr') ?\<Lambda> ns"
          using state_rel_\<omega>_old state_rel_boogie_const_rel by blast
        show "state_well_typed (type_interp ctxt) ?\<Lambda> [] ns"
          using RInst state_rel_state_well_typed by blast
        show "label_hm_rel Pr ?\<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total ?\<omega>_old) ns "
          using state_rel_\<omega>_old state_rel_label_hm_rel by blast
        show "disjoint_list (state_rel0_disj_list Tr' (?AuxPredFun \<omega>def \<omega>))"
          sorry
        show "aux_vars_pred_sat ?\<Lambda> (?AuxPredFun \<omega>def \<omega>) ns"
          unfolding aux_vars_pred_sat_def
        proof(intro allI, rule impI)
          fix x P
          assume PredicateDefined: "?AuxPredFun \<omega>def \<omega> x = Some P"
          let ?xVar = "lookup_var ?\<Lambda> ns x"

          show "has_Some P (lookup_var ?\<Lambda> ns x)"
          proof (cases)
            assume "x \<noteq> mdef \<and> x \<noteq> m \<and> x \<noteq> hdef \<and> x \<noteq> h"
            thus ?thesis
              by (metis (no_types, lifting) RInst aux_vars_pred_sat_def fun_upd_other PredicateDefined state_rel_aux_vars_pred_sat)
          next
            assume "\<not>(x \<noteq> mdef \<and> x \<noteq> m \<and> x \<noteq> hdef \<and> x \<noteq> h)"
            then consider (MDef) "x = mdef" | (M) "x = m" | (HDef) "x = hdef" | (H) "x = h"
              by blast 
            thus ?thesis
            proof cases
              case MDef
              have "?AuxPredFun \<omega>def \<omega> mdef = Some (pred_eq_mask Pr TyRep (field_translation Tr) ctxt mdef \<omega>def)"
                sorry (* Why doesn't this prove? *)
              hence "P = pred_eq_mask Pr TyRep (field_translation Tr) ctxt mdef \<omega>def"
                using MDef PredicateDefined
                by simp
              from RInst state_rel_mask_var_def_rel mask_var_rel_def obtain mb where
                MaskVarValue: "lookup_var ?\<Lambda> ns (mask_var_def Tr) = Some (AbsV (AMask mb))" and
                MaskVarType:  "lookup_var_ty ?\<Lambda> (mask_var_def Tr) = Some (TConSingle (TMaskId TyRep))" and                
                MaskRel:      "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) mb" 
                by blast
              have "pred_eq_mask Pr TyRep (field_translation Tr) ctxt mdef \<omega>def (AbsV (AMask mb))"
                unfolding pred_eq_mask_def
                using MaskVarValue MaskVarType MaskRel mh
                by simp
              hence "P (AbsV (AMask mb))"
                by (simp add: \<open>P = _\<close>)
              thus "has_Some P (lookup_var ?\<Lambda> ns x)"
                by (simp add: MDef MaskVarValue mh)
            next
              case M
              have "?AuxPredFun \<omega>def \<omega> m = Some (pred_eq_mask Pr TyRep (field_translation Tr) ctxt m \<omega>)"
                sorry (* Why doesn't this prove? *)
              hence "P = pred_eq_mask Pr TyRep (field_translation Tr) ctxt m \<omega>"
                using M PredicateDefined
                by simp
              from RInst state_rel_mask_var_rel mask_var_rel_def obtain mb where
                MaskVarValue: "lookup_var ?\<Lambda> ns (mask_var Tr) = Some (AbsV (AMask mb))" and
                MaskVarType:  "lookup_var_ty ?\<Lambda> (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and                
                MaskRel:      "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb" 
                by blast
              have "pred_eq_mask Pr TyRep (field_translation Tr) ctxt m \<omega> (AbsV (AMask mb))"
                unfolding pred_eq_mask_def
                using MaskVarValue MaskVarType MaskRel mh
                by simp
              hence "P (AbsV (AMask mb))"
                by (simp add: \<open>P = _\<close>)
              thus "has_Some P (lookup_var ?\<Lambda> ns x)"
                by (simp add: M MaskVarValue mh)
            next
              case HDef
              have "?AuxPredFun \<omega>def \<omega> hdef = Some (pred_eq_heap Pr TyRep (field_translation Tr) ctxt hdef \<omega>def)"
                sorry (* Why doesn't this prove? *)
              hence "P = pred_eq_heap Pr TyRep (field_translation Tr) ctxt hdef \<omega>def"
                using HDef PredicateDefined
                by simp                                     
              from RInst state_rel_heap_var_def_rel heap_var_rel_def obtain hb where
                 HeapVarValue: "lookup_var ?\<Lambda> ns (heap_var_def Tr) = Some (AbsV (AHeap hb))" and
                 HeapVarType: "lookup_var_ty ?\<Lambda> (heap_var_def Tr) = Some (TConSingle (THeapId TyRep))" and
                 HeapVarTyOpt: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])" and
                 HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>def) hb" and
                 HeapWellTyped: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
                by blast
              have "pred_eq_heap Pr TyRep (field_translation Tr) ctxt hdef \<omega>def (AbsV (AHeap hb))"
                unfolding pred_eq_heap_def pred_eq_heap_aux_def
                using HeapVarType HeapVarTyOpt HeapRel HeapWellTyped mh
                by simp
              hence "P (AbsV (AHeap hb))"
                by (simp add: \<open>P = _\<close>)
              thus "has_Some P (lookup_var ?\<Lambda> ns x)"
                by (simp add: HDef HeapVarValue mh)
            next
              case H
              have "?AuxPredFun \<omega>def \<omega> hdef = Some (pred_eq_heap Pr TyRep (field_translation Tr) ctxt hdef \<omega>def)"
                sorry (* Why doesn't this prove? *)
              hence "P = pred_eq_heap Pr TyRep (field_translation Tr) ctxt h \<omega>"
                using H PredicateDefined
                by simp                                     
              from RInst state_rel_heap_var_rel heap_var_rel_def obtain hb where
                 HeapVarValue: "lookup_var ?\<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
                 HeapVarType: "lookup_var_ty ?\<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
                 HeapVarTyOpt: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])" and
                 HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb" and
                 HeapWellTyped: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
                by blast
              have "pred_eq_heap Pr TyRep (field_translation Tr) ctxt h \<omega> (AbsV (AHeap hb))"
                unfolding pred_eq_heap_def pred_eq_heap_aux_def
                using HeapVarType HeapVarTyOpt HeapRel HeapWellTyped mh
                by simp
              hence "P (AbsV (AHeap hb))"
                by (simp add: \<open>P = _\<close>)
              thus "has_Some P (lookup_var ?\<Lambda> ns x)"
                by (simp add: H HeapVarValue mh)
            qed
          qed
        qed
      qed

\<comment>\<open>first conjunct is done (side remark: the previous and the following are the same theorems (otherwise "by assumption" would not work)\<close>
      hence "?ROld (?AuxPredFun \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns"
        by assumption

      moreover have "expr_wf_rel (?ROld (?AuxPredFun \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
        using BodyRel
        by blast
      ultimately show  
        "?ROld (?AuxPredFun \<omega>def \<omega>) ?\<omega>def_old ?\<omega>_old ns \<and>
         expr_wf_rel (?ROld (?AuxPredFun \<omega>def \<omega>)) ctxt_vpr StateCons P ctxt expr \<gamma> \<gamma>'"
        by auto
    qed
    show "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> get_trace_total \<omega>def lbl \<noteq> None \<and> get_trace_total \<omega> lbl \<noteq> None"
    proof -
      fix \<omega>def \<omega> ns
      assume R: "R \<omega>def \<omega> ns"
      let ?\<omega>_trace_total = "get_trace_total \<omega>"
      let ?\<omega>def_trace_total = "get_trace_total \<omega>def"
      let ?P = "(\<lambda>m \<phi>. mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) m (get_mh_total \<phi>))"
      let ?LabelMap = "(snd (label_hm_translation Tr))"
      from \<open>R = _\<close> R have state_rel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" by simp
      hence "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) ?\<omega>_trace_total ns"
        using state_rel_def state_rel0_label_hm_rel
        by fast
      hence "label_rel ?P ?LabelMap ?\<omega>_trace_total ns \<and>
             label_rel ?P ?LabelMap ?\<omega>_trace_total ns"
        using label_hm_rel_def
        by fast
      hence LabelMap_implies_Some: "(\<forall> lbl h. ?LabelMap lbl = Some h \<longrightarrow> (\<exists>\<phi>. (get_trace_total \<omega>) lbl = Some \<phi> \<and> ?P h \<phi> ns))"
        using label_rel_def
        by meson
      from \<open>lbls = _\<close> OldM have LabelMap: "?LabelMap lbl = Some OldM"
        by simp
      from LabelMap_implies_Some LabelMap have \<omega>_not_none: "?\<omega>_trace_total lbl \<noteq> None"
        by auto
      from state_rel_def state_rel0_def state_rel have \<omega>_trace_is_\<omega>def_trace: "?\<omega>def_trace_total = ?\<omega>_trace_total"
        by blast
      from \<omega>_not_none \<omega>_trace_is_\<omega>def_trace
      show "get_trace_total \<omega>def lbl \<noteq> None \<and> get_trace_total \<omega> lbl \<noteq> None"
        by simp
    qed
  qed
qed

abbreviation wf_rel_fieldacc
  where "wf_rel_fieldacc admissible_locs R R' ctxt_vpr StateCons P ctxt e f \<equiv> wf_rel R R'
           (\<lambda>\<omega>def \<omega>. (\<exists>a. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a))) \<and> 
                       (a,f) \<in> admissible_locs \<omega>def))
           (\<lambda>\<omega>def \<omega>. (\<exists>v. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> 
                           ((v = VRef Null) \<or> (\<exists>a. v = VRef (Address a) \<and> (a,f) \<notin> admissible_locs \<omega>def))))
           P
           ctxt"

lemma field_access_wf_rel:
  assumes ExpWfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma>1 \<gamma>2" and
          FieldAccWfRel: "wf_rel_fieldacc get_valid_locs R R ctxt_vpr StateCons P ctxt e f \<gamma>2 \<gamma>3"
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (FieldAcc e f) \<gamma>1 \<gamma>3"
proof (rule expr_wf_rel_intro)
  text\<open>Normal case\<close>

  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and
         RedExp:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  from RedExp show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega>def \<omega> ns'"
  proof cases
    case (RedField a v')
    hence "(a, f) \<in> get_valid_locs \<omega>def" 
      by (metis extended_val.distinct(1) if_SomeD)

    moreover from RedField obtain ns' where
       R2:"R \<omega>def \<omega> ns'" and
       Red1:"red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns')"
      using wf_rel_normal_elim[OF ExpWfRel R]
      by blast

    ultimately show ?thesis
      using wf_rel_normal_elim[OF FieldAccWfRel R2] red_ast_bpl_transitive RedField
      by blast
  qed
next
  text\<open>Failure case\<close>

  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and
         "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t v" and
         "v = VFailure"
  hence "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp

  thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure"
  proof cases
    case (RedField a v)
    hence InvalidLoc:"(a, f) \<notin> get_valid_locs \<omega>def" 
      by force    

    from RedField obtain ns' where
       R2:"R \<omega>def \<omega> ns'" and
       "red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns')"
      using wf_rel_normal_elim[OF ExpWfRel R]
      by blast

    moreover obtain c' where 
     "red_ast_bpl P ctxt (\<gamma>2, Normal ns') c'" and
     "snd c' = Failure"
      using RedField InvalidLoc wf_rel_failure_elim[OF FieldAccWfRel R2]
      by blast

    ultimately show ?thesis
      using red_ast_bpl_transitive by blast
  next
    case RedFieldNullFailure

    from this obtain ns' where
       R2:"R \<omega>def \<omega> ns'" and
       "red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns')"
      using wf_rel_normal_elim[OF ExpWfRel R]
      by blast

    moreover obtain c' where 
     "red_ast_bpl P ctxt (\<gamma>2, Normal ns') c'" and
     "snd c' = Failure"
      using RedFieldNullFailure wf_rel_failure_elim[OF FieldAccWfRel R2]
      by blast

    ultimately show ?thesis 
      using red_ast_bpl_transitive by blast
  next
    case RedSubFailure
    hence "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      by (fastforce elim: red_pure_exps_total_singleton)
    then show ?thesis using assms(1) wf_rel_failure_elim
      using \<open>R \<omega>def \<omega> ns\<close> by blast
  qed
qed

lemma cond_exp_wf_rel:
  assumes CondWfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt cond 
                       \<gamma>1 (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)"
      and CondExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt cond cond_bpl"
      and ThnWfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_thn 
                       (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
      and ElsWfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e_els 
                       (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)"      
    shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.CondExp cond e_thn e_els) 
                         \<gamma>1
                         (next, cont)"
  using CondWfRel ThnWfRel ElsWfRel
  unfolding wf_rel_def
proof (rule rel_general_cond)
  fix \<omega> \<omega>' ns
  assume R: "R (fst \<omega>) (snd \<omega>) ns"
     and *: "\<omega> = \<omega>' \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>pure_exp.CondExp cond e_thn e_els;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v)" (is "_ \<and> (\<exists>v. ?RedCondVpr v)")
  from this obtain v where  "?RedCondVpr v"
    by blast

  thus "(\<omega> = \<omega> \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v)) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and>
        R (fst \<omega>) (snd \<omega>) ns \<and> \<omega> = \<omega>' \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>e_thn;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and>
        R (fst \<omega>) (snd \<omega>) ns \<and> \<omega> = \<omega>' \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>e_els;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v))"
    apply (cases)
     apply (insert exp_rel_vpr_bplD[OF CondExpRel])
     apply (metis R * val_rel_vpr_bpl.simps(2))
    apply (insert exp_rel_vpr_bplD[OF CondExpRel])
    by (metis R * val_rel_vpr_bpl.simps(2))
next
  fix \<omega> ns
  assume R: "R (fst \<omega>) (snd \<omega>) ns"
  assume "ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>pure_exp.CondExp cond e_thn e_els;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  thus "ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
       (\<omega> = \<omega> \<and> (\<exists>v. ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>cond;snd \<omega>\<rangle> [\<Down>]\<^sub>t Val v)) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and>
        R (fst \<omega>) (snd \<omega>) ns \<and> ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>e_thn;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and>
        R (fst \<omega>) (snd \<omega>) ns \<and> ctxt_vpr, StateCons, Some (fst \<omega>) \<turnstile> \<langle>e_els;snd \<omega>\<rangle> [\<Down>]\<^sub>t VFailure) "
    apply (cases)
      apply (insert exp_rel_vpr_bplD[OF CondExpRel])
      apply (metis R val_rel_vpr_bpl.simps(2))
     apply (metis R val_rel_vpr_bpl.simps(2))
    apply simp
    by (metis option.discI red_pure_exps_total_singleton)
qed

subsubsection \<open>Well-definedness for free if expressions are subexpressions of a framed assertion\<close>

lemma assertion_framing_exprs_wf_rel_inh:
  assumes "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
               assertion_framing_state ctxt_vpr StateCons A \<omega>def \<and>
               get_store_total \<omega> = get_store_total \<omega>def \<and> 
               get_trace_total \<omega> = get_trace_total \<omega>def \<and>
               get_h_total_full \<omega> = get_h_total_full \<omega>def"
      and "es = direct_sub_expressions_assertion A"
      and ExprConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es"
    shows "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>"
proof (cases "es = []")
  case True
  then show ?thesis 
    using exprs_wf_rel_Nil
    by blast
next
  case False
  show ?thesis 
  unfolding exprs_wf_rel_def
proof (rule wf_rel_intro)
  fix contra
  fix \<omega>def \<omega> ns
  assume "R \<omega>def \<omega> ns" and RedExps: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"

  from \<open>R \<omega>def \<omega> ns\<close> have
    AssertionFramed: "assertion_framing_state ctxt_vpr StateCons A \<omega>def" and
    OnlyMaskDiffers: "get_store_total \<omega> = get_store_total \<omega>def \<and> 
     get_trace_total \<omega> = get_trace_total \<omega>def \<and>
     get_h_total_full \<omega> = get_h_total_full \<omega>def"
    using assms
    by auto

  from RedExps OnlyMaskDiffers have "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega>def None"
    using red_pure_exp_only_differ_on_mask(2) ExprConstraint
    by blast
  hence "red_inhale ctxt_vpr StateCons A \<omega>def RFailure"
    apply (cases A)
    using assms \<open>es \<noteq> []\<close>
           apply simp_all
    using InhSubExpFailure AssertionFramed assertion_framing_state_sub_exps_not_failure
      apply blast     
    using inh_imp_failure
    apply (simp add: InhSubExpFailure)
    using inh_cond_assert_failure
    by (simp add: InhSubExpFailure)

  moreover from \<open>R \<omega>def \<omega> ns\<close> have "assertion_framing_state ctxt_vpr StateCons A \<omega>def"
    using assms
    by blast
  ultimately have False
    unfolding assertion_framing_state_def
    by blast

  thus contra
    by blast
   qed (blast intro: red_ast_bpl_refl)
 qed

lemma assertion_framing_exprs_wf_rel_inh_well_def_same:
  assumes "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
               assertion_framing_state ctxt_vpr StateCons A \<omega>def \<and>
               \<omega> = \<omega>def"
      and "es = direct_sub_expressions_assertion A"
    shows "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>"
proof (cases "es = []")
  case True
  then show ?thesis 
    using exprs_wf_rel_Nil
    by blast
next
  case False
  show ?thesis 
  unfolding exprs_wf_rel_def
  proof (rule wf_rel_intro)
    fix contra
    fix \<omega>def \<omega> ns
    assume "R \<omega>def \<omega> ns" and RedExps: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"
  
    from \<open>R \<omega>def \<omega> ns\<close> have
      AssertionFramed: "assertion_framing_state ctxt_vpr StateCons A \<omega>def" and "\<omega> = \<omega>def"
      using assms
      by auto
  
    hence "red_inhale ctxt_vpr StateCons A \<omega>def RFailure"
      apply (cases A)
      using assms \<open>es \<noteq> []\<close>
             apply simp_all
      using InhSubExpFailure RedExps assertion_framing_state_sub_exps_not_failure 
        apply blast
      using inh_imp_failure False InhSubExpFailure RedExps \<open>es = _\<close> apply blast
      using inh_cond_assert_failure False InhSubExpFailure RedExps \<open>es = _\<close> 
      by blast      

    moreover from \<open>R \<omega>def \<omega> ns\<close> have "assertion_framing_state ctxt_vpr StateCons A \<omega>def"
      using assms
      by blast
    ultimately have False
      unfolding assertion_framing_state_def
      by blast
  
    thus contra
      by blast
  qed (blast intro: red_ast_bpl_refl)
qed

lemma exprs_wf_rel_singletonD:
  assumes "exprs_wf_rel R ctxt_vpr StateCons P ctxt [e] \<gamma> \<gamma>"
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>"
proof (rule expr_wf_rel_intro)
  fix v \<omega>def \<omega> ns
  assume "R \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  hence "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) [e] \<omega> (Some [v])"
    by (auto intro: red_exp_inhale_unfold_intros)

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns') \<and> R \<omega>def \<omega> ns'"
    using assms exprs_wf_rel_normal_elim \<open>R _ _ _\<close>
    by blast
next
  fix v \<omega>def \<omega> ns
  assume "R \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"
  hence "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) [e] \<omega> None"
    by (auto intro: red_exp_inhale_unfold_intros)

  thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
    using assms exprs_wf_rel_failure_elim \<open>R _ _ _\<close>
    by blast
qed

subsection \<open>Connecting semantic well-definedness relation with concrete Boogie statements\<close>

lemma wf_rel_bop_op_trivial: 
  assumes "bop \<notin> {IntDiv, PermDiv, ViperLang.Mod}"
  shows "wf_rel_bop_op R R ctxt_vpr StateCons P ctxt e1 bop e2 \<gamma> \<gamma>"  
  apply (rule wf_rel_intro)
   apply (fastforce simp: red_ast_bpl_def)
  using assms eval_binop_not_failure
  by blast

lemma eval_binop_div_mod_normal_types:
  assumes "bop \<in> {IntDiv, PermDiv, ViperLang.Mod}"
          "eval_binop v1 bop v2 = BinopNormal v'"
  shows "((\<exists>i. v1 = VInt i) \<or> (\<exists>p. v1 = VPerm p)) \<and> ((\<exists>i. v2 = VInt i) \<or> (\<exists>p. v2 = VPerm p))"
  by (rule eval_binop.elims[OF assms(2)], insert assms(1), auto)

lemma syn_bop_op_non_trivial_wf_rel:
  assumes Bop:"bop \<in> {IntDiv, PermDiv, ViperLang.Mod}" and
          ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl" and
          ZeroInt: "bop \<in> {IntDiv, ViperLang.Mod} \<Longrightarrow> zero = Lit (LInt 0)" and
          ZeroPerm0: "bop = PermDiv \<Longrightarrow> zero = Lit (LInt 0) \<or> zero = Lit (LReal 0)" and
          \<comment>\<open>The following two premises are used to make sure that \<^term>\<open>zero\<close> is the correct literal
             for permission division. We phrase the premises in terms of the Boogie expressions, since
             for the proof generation we want use Boogie's type safety whenever possible.\<close>
          ZeroIntE2BplWellTy: "bop = PermDiv \<Longrightarrow> zero = Lit (LInt 0) \<Longrightarrow> 
                        (\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> \<exists>i. red_expr_bpl ctxt e2_bpl ns (IntV i))" and
          ZeroRealE2BplWellTy: "bop = PermDiv \<Longrightarrow> zero = Lit (LReal 0) \<Longrightarrow> 
                        (\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> \<exists>r. red_expr_bpl ctxt e2_bpl ns (RealV r))"
        shows "wf_rel_bop_op R R ctxt_vpr StateCons P ctxt e1 bop e2 (BigBlock None ((Assert (e2_bpl \<guillemotleft>Neq\<guillemotright> zero))#cs) str tr, cont) (BigBlock None cs str tr, cont)"
              (is "wf_rel_bop_op _ _ _ _ _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule wf_rel_intro)
\<comment>\<open>Normal case\<close>
  fix v \<omega>def \<omega> ns
  assume R: "R \<omega>def \<omega> ns" and "\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<and> ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2 \<and> (\<exists>v'. eval_binop v1 bop v2 = BinopNormal v')"
  from this obtain v1 v2 v' where Red2:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and EvalBinop: "eval_binop v1 bop v2 = BinopNormal v'"
    by auto
  hence NonZero:"v2 \<noteq> VInt(0) \<and> v2 \<noteq> VPerm(0)"
    using eval_binop_not_failure_2 Bop
    by blast
  from EvalBinop have IntOrPerm:"(\<exists>i. v2 = VInt i) \<or> (\<exists>p. v2 = VPerm p)" using eval_binop_div_mod_normal_types[OF Bop]
    by blast
  from Red2 obtain v2_bpl where RedBpl:"red_expr_bpl ctxt e2_bpl ns v2_bpl" and ValRel:"val_rel_vpr_bpl v2 = v2_bpl"
    using ExpRel exp_rel_vpr_bpl_def exp_rel_vb_single_def R
    by metis
  show "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
  proof (cases \<open>(\<exists>i. v2 = VInt i)\<close>)
    case True
    from this obtain i where "v2 = VInt i" by auto
    hence "v2_bpl = IntV i" and "i \<noteq> 0" using RedBpl ValRel \<open>v2 = _\<close> NonZero by auto
      
    have "zero = Lit (LInt 0)"
    proof (cases "bop = PermDiv")
      case True
      show ?thesis
      proof (rule ccontr)
        assume "zero \<noteq> Lit (Lang.lit.LInt 0)"
        hence "zero = Lit (Lang.lit.LReal 0)"
          using ZeroPerm0 True
          by simp
        thus False
          using \<open>v2_bpl = _\<close> ZeroRealE2BplWellTy RedBpl R
          by (meson Lang.lit.distinct(5) Semantics.val.inject(1) True expr_eval_determ(1))
      qed
    next
      case False
      then show ?thesis
        using Bop ZeroInt by auto
    qed

    have "red_bigblock_small P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns)"
      apply rule+
      using RedBpl 
        apply simp
       apply (subst \<open>zero = _\<close>)
       apply rule
      apply (subst \<open>v2_bpl = _\<close>)
      apply (simp add: \<open>i \<noteq> 0\<close>)
      done
    then show ?thesis 
    using R by (auto simp: red_ast_bpl_def)
  next
    case False
    from this obtain p where "v2 = VPerm p" using IntOrPerm by auto
    hence "v2_bpl = RealV p" and "p \<noteq> 0" using RedBpl ValRel \<open>v2 = _\<close> NonZero by auto

    have "bop = PermDiv"
      apply (insert Bop EvalBinop \<open>v2 = _\<close>)
      apply (erule eval_binop.elims)
                          apply simp_all
       apply (rule eval_perm_perm.elims)
      by fastforce+
    have "zero = Lit (LReal 0)"
      proof (rule ccontr)
        assume "zero \<noteq> Lit (Lang.lit.LReal 0)"
        hence "zero = Lit (Lang.lit.LInt 0)"
          using ZeroPerm0 \<open>bop = PermDiv\<close>
          by simp
        thus False
          using \<open>v2_bpl = _\<close> \<open>bop = PermDiv\<close> ZeroIntE2BplWellTy RedBpl R
          by (meson Lang.lit.distinct(5) Semantics.val.inject(1) expr_eval_determ(1))         
      qed

    have "red_bigblock_small P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns)"
      apply rule+
      using RedBpl 
        apply simp
       apply (subst \<open>zero = _\<close>)
       apply rule
      apply (subst \<open>v2_bpl = _\<close>)
      apply (simp add: \<open>p \<noteq> 0\<close>)
      done
    then show ?thesis 
      using R by (auto simp: red_ast_bpl_def)
  qed
next
\<comment>\<open>Failure case\<close>
  fix v \<omega>def \<omega> ns
  assume R: "R \<omega>def \<omega> ns" and "\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<and> ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2 \<and> (eval_binop v1 bop v2 = BinopOpFailure)"
  from this obtain v1 v2 where Red2:"ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and EvalBinop: "eval_binop v1 bop v2 = BinopOpFailure"
    by auto
  hence IntOrPerm:"v2 = VInt 0 \<or> v2 = VPerm 0"
    by (metis Bop eval_binop_failure_int eval_binop_failure_perm insert_iff)

  from Red2 obtain v2_bpl where RedBpl:"red_expr_bpl ctxt e2_bpl ns v2_bpl" and ValRel:"val_rel_vpr_bpl v2 = v2_bpl"
    using ExpRel exp_rel_vpr_bpl_def exp_rel_vb_single_def R
    by metis

  show "\<exists>c'. red_ast_bpl P ctxt (?\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  proof (cases \<open>v2 = VInt 0\<close>)
    case True
    hence "v2_bpl = IntV 0" using ValRel by simp
    have "zero = Lit (LInt 0)"
    proof (cases "bop = PermDiv")
    case True
    show ?thesis
      proof (rule ccontr)
        assume "zero \<noteq> Lit (Lang.lit.LInt 0)"
        hence "zero = Lit (Lang.lit.LReal 0)"
          using ZeroPerm0 True
          by simp
        thus False
          using \<open>v2_bpl = _\<close> ZeroRealE2BplWellTy RedBpl R
          by (meson Lang.lit.distinct(5) Semantics.val.inject(1) True expr_eval_determ(1))
      qed
    next
      case False
      then show ?thesis
        using Bop ZeroInt by auto
    qed

    have "red_bigblock_small P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Failure)"
      apply rule+
      using RedBpl 
        apply simp
       apply (subst \<open>zero = _\<close>)
       apply rule
      apply (subst \<open>v2_bpl = _\<close>)
      apply simp
      done
    then show ?thesis 
      by (auto simp: red_ast_bpl_def)
  next
    case False
    hence "v2 = VPerm 0" using IntOrPerm 
      by simp
    hence "v2_bpl = RealV 0" using ValRel
      by simp
    have "bop = PermDiv" using \<open>v2 = _\<close> Bop 
      using EvalBinop eval_binop_failure_int by blast
    have "zero = Lit (LReal 0)"
      proof (rule ccontr)
        assume "zero \<noteq> Lit (Lang.lit.LReal 0)"
        hence "zero = Lit (Lang.lit.LInt 0)"
          using ZeroPerm0 \<open>bop = PermDiv\<close>
          by simp
        thus False
          using \<open>v2_bpl = _\<close> \<open>bop = PermDiv\<close> ZeroIntE2BplWellTy RedBpl R
          by (meson Lang.lit.distinct(5) Semantics.val.inject(1) expr_eval_determ(1))         
      qed
    have "red_bigblock_small P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Failure)"
      apply rule+
      using RedBpl 
        apply simp
       apply (subst \<open>zero = _\<close>)
       apply rule
      apply (subst \<open>v2_bpl = _\<close>)
      apply simp
      done
    then show ?thesis 
      by (auto simp: red_ast_bpl_def)
  qed
qed

text \<open>The following lemma uses that \<^term>\<open>\<And>b. b \<longleftrightarrow> (b \<noteq> False)\<close> is true\<close>
lemma lazy_op_eval_bpl:
  assumes   
    Lazy:  "binop_lazy bop = Some(b1,bResult)" and
    RedBpl: "red_expr_bpl ctxt e1_bpl ns (BoolV b)" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl"
          "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl"
        shows "red_expr_bpl ctxt guard ns (BoolV ((VBool b) \<noteq> b1))"
proof -
  have BOp: "bop \<in> {ViperLang.And, ViperLang.BImp, ViperLang.Or}"
    using Lazy
    by (rule binop_lazy.elims) auto

  show ?thesis
  proof (cases "bop = ViperLang.Or")
    case True    
    hence "guard = UnOp Not e1_bpl" using Guard
      by simp

    show ?thesis
      apply (subst \<open>guard = _\<close>)
      apply (rule)
       apply (rule RedBpl)
      apply (insert Lazy)
      apply (subst (asm) \<open>bop = _\<close>)
      by fastforce
  next
    case False
    hence "guard = e1_bpl"
      using Guard BOp
      by simp

    show ?thesis
      apply (subst \<open>guard = _\<close>)
      using RedBpl Lazy BOp False   
      apply simp
      by auto
  qed
qed

text \<open>The following lemma expresses the well-definedness result provided by an
 if-statement encoding for a lazy binary operation in the case where short-circuiting does not apply.\<close>
lemma syn_lazy_bop_short_circuit_wf_rel:
  assumes
   Lazy: "binop_lazy bop = Some(b1,bResult)" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   WfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 (thnHd, (convert_list_to_cont thnTl cont)) \<gamma>'"
               (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma>'' _")
  shows
   Rel2a: "expr_wf_rel (\<lambda>\<omega>def \<omega> s. R \<omega>def \<omega> s \<and> 
                                    (\<exists>b. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b) \<and> b \<noteq> b1 \<and>
                                         (\<exists> v2. eval_binop b bop v2 \<noteq> BinopTypeFailure))) 
                        ctxt_vpr StateCons P ctxt e2 
                        (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) els)) None, cont)
                        \<gamma>'" (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule expr_wf_rel_intro)
  text \<open>Normal case\<close>
  fix v \<omega>def \<omega> ns
  assume Rext:"?R_ext \<omega>def \<omega> ns" (is "?R \<and> ?Re1") and RedExp: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"

  from Rext obtain v1 v2 where RedE1: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and NotB1:"v1 \<noteq> b1" and
                            v1BopWellTy: "eval_binop v1 bop v2 \<noteq> BinopTypeFailure"
    by blast

  from Lazy v1BopWellTy  obtain b where "v1 = VBool b"
    apply (cases bop, simp_all)
    by (cases v1; cases v2; simp)+   

  hence RedE1Bpl:"red_expr_bpl ctxt e1_bpl ns (BoolV b)"
    using ExpRel Rext RedE1
    unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
    by fastforce

  have "red_expr_bpl ctxt guard ns (BoolV (VBool b \<noteq> b1))"
    using lazy_op_eval_bpl Lazy RedE1Bpl Guard
    by blast
  hence TrueEval: "red_expr_bpl ctxt guard ns (BoolV True)"
    using NotB1 RedE1Bpl \<open>v1 = _\<close>
    by simp

   let ?\<gamma>'' = "(thnHd, convert_list_to_cont thnTl cont)"
   from RedExp obtain ns' where 
     Rns': "R \<omega>def \<omega> ns'" and RedThn:"red_ast_bpl P ctxt (?\<gamma>'', Normal ns) (?\<gamma>', Normal ns')"
     using wf_rel_normal_elim[OF WfRel] Rext
     by blast

   have "red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns')"
     unfolding red_ast_bpl_def
    apply (rule converse_rtranclp_into_rtranclp)
     apply rule
     apply (rule RedParsedIfTrue)
    using TrueEval 
     apply blast
    using RedThn
    unfolding red_ast_bpl_def
    by simp

  thus "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> (R \<omega>def \<omega> ns' \<and> ?Re1)"
    using Rns' Rext
    by blast
next
  text \<open>Failure case\<close>
  fix v \<omega>def \<omega> ns
  assume Rext:"?R_ext \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"
  hence E2Fail: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by blast

  from Rext obtain v1 v2 where RedE1: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and NotB1:"v1 \<noteq> b1" and
                            v1BopWellTy: "eval_binop v1 bop v2 \<noteq> BinopTypeFailure"
    by blast

  from Lazy v1BopWellTy  obtain b where "v1 = VBool b"
    apply (cases bop, simp_all)
    by (cases v1; cases v2; simp)+    

  hence RedE1Bpl:"red_expr_bpl ctxt e1_bpl ns (BoolV b)"
    using ExpRel Rext RedE1
    unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
    by (metis val_rel_vpr_bpl.simps(2))

  have "red_expr_bpl ctxt guard ns (BoolV (VBool b \<noteq> b1))"
    using lazy_op_eval_bpl Lazy RedE1Bpl Guard
    by blast

  hence TrueEval: "red_expr_bpl ctxt guard ns (BoolV True)"
    using NotB1 \<open>v1 = _\<close>
    by simp

  let ?\<gamma>'' = "(thnHd, convert_list_to_cont thnTl cont)"
  from WfRel E2Fail obtain c' where "snd c' = Failure" and RedThn: "red_ast_bpl P ctxt (?\<gamma>'', Normal ns) c'"
    using wf_rel_failure_elim Rext
    by blast

  have "red_ast_bpl P ctxt (?\<gamma>, Normal ns) c'" (is "?P c'")
    unfolding red_ast_bpl_def
    apply (rule converse_rtranclp_into_rtranclp)
     apply rule
     apply (rule RedParsedIfTrue)
    using TrueEval 
     apply blast
    using RedThn
    unfolding red_ast_bpl_def
    by simp    

  thus "\<exists>c'. ?P c' \<and> snd c' = Failure"
    using \<open>snd c' = Failure\<close>
    by blast
qed

text \<open>The following lemma expresses the well-definedness result provided by an if-statement encoding 
for a lazy binary operation in the case where short-circuiting applies.\<close>
lemma syn_lazy_bop_no_short_circuit_wf_rel:
  assumes
   Lazy: "binop_lazy bop = Some(b1,bResult)" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl"
  shows
   "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
                       (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, cont)
                       (empty_bigblock elseName, cont)" (is "wf_rel R _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule wf_rel_intro)
  text \<open>Normal case\<close>
  fix \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1"

  moreover obtain b where "b1 = VBool b"
    using Lazy
    by (rule binop_lazy.elims) auto

  ultimately have RedE1Bpl: "red_expr_bpl ctxt e1_bpl ns (BoolV b)"
    using ExpRel R
    unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
    by fastforce

  have "red_expr_bpl ctxt guard ns (BoolV (VBool b \<noteq> b1))"
  using lazy_op_eval_bpl Lazy RedE1Bpl Guard
  by blast

  hence GuardEvalFalse:"red_expr_bpl ctxt guard ns (BoolV False)"
    using \<open>b1 = _\<close> by simp

  have RedAst:"red_ast_bpl P ctxt (?\<gamma>,Normal ns) (?\<gamma>', Normal ns)"
    unfolding red_ast_bpl_def
    apply (rule converse_rtranclp_into_rtranclp)
     apply rule
     apply (fastforce intro: RedParsedIfFalse GuardEvalFalse)
    by simp

  show "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>,Normal ns) (?\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
    using R RedAst
    by auto

next
  text \<open>Failure case (can never happen)\<close>
  fix contra
  assume False
  thus contra
    by simp
qed

lemma syn_lazy_bop_no_short_circuit_seq_wf_rel:
  assumes
   Lazy: "binop_lazy bop = Some(b1,bResult)" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl"
  shows
   "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
                       (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, KSeq bNext cont)
                       (bNext, cont)" (is "wf_rel R _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof -
  have A:"wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
               (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, KSeq bNext cont)
               (empty_bigblock elseName, KSeq bNext cont)"
    by (blast intro!: syn_lazy_bop_no_short_circuit_wf_rel assms)

  show ?thesis
    apply (rule wf_rel_extend_1)
     apply (rule A)
    apply (rule exI, rule conjI)
    unfolding red_ast_bpl_def
     apply (rule converse_rtranclp_into_rtranclp)
      apply rule+
    by simp
qed

lemma syn_lazy_bop_wf_rel:
  assumes
   Lazy: "binop_lazy bop = Some (b1 :: 'a ValueAndBasicState.val, bResult)" and
   Rel1: "expr_wf_rel R (ctxt_vpr :: 'a total_context) StateCons P ctxt e1 \<gamma>0 \<gamma>2" and
   Red2: "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) 
            ((BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) [empty_bigblock elseName])) None, KSeq bNext cont), Normal ns3) \<and>
             R \<omega>def \<omega> ns3"
           (is "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) ((?b_if, ?cont_if), Normal ns3) \<and>
             R \<omega>def \<omega> ns3")
   and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   WfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 (thnHd, (convert_list_to_cont thnTl (KSeq bNext cont))) (bNext, cont)"
               (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma>'' _")
   shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 (bNext, cont)"
proof (rule binop_lazy_expr_wf_rel[OF Lazy])
  show "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 (?b_if, ?cont_if)"
    by (auto intro: wf_rel_extend_1 Rel1 Red2)
next
  show "expr_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
     ctxt_vpr StateCons P ctxt e2 (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock elseName])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_short_circuit_wf_rel[OF Lazy])
    apply (insert Guard)
    by (auto intro: ExpRel WfRel)
next
  show "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock elseName])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_no_short_circuit_seq_wf_rel[OF Lazy])
      apply (insert Guard)
    by (auto intro: ExpRel)
qed

(* remove syn_lazy_bop_wf_rel_2 and just use syn_lazy_bop_wf_rel *)
lemma syn_lazy_bop_wf_rel_2:
  assumes
   Lazy: "binop_lazy bop = Some (b1 :: 'a ValueAndBasicState.val, bResult)" and
   Rel1: "expr_wf_rel R (ctxt_vpr :: 'a total_context) StateCons P ctxt e1 \<gamma>0 \<gamma>2" and
   (* TODO: Red2 is superfluous: can instead use wf_extend rules *)
   Red2: "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) 
            ((BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) [empty_else_block])) None, KSeq bNext cont), Normal ns3) \<and>
             R \<omega>def \<omega> ns3"
           (is "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) ((?b_if, ?cont_if), Normal ns3) \<and>
             R \<omega>def \<omega> ns3") and
   ElseBlockEmpty: "is_empty_bigblock empty_else_block" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   WfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 (thnHd, (convert_list_to_cont thnTl (KSeq bNext cont))) \<gamma>3"
               (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma>'' _") and
   (* TODO: Red3 is superfluous: can instead use wf_extend rules *)
   Red3: "\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>3, Normal ns2) ((bNext, cont), Normal ns3) \<and> R \<omega>def \<omega> ns3"
   shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 (bNext, cont)"
proof (rule binop_lazy_expr_wf_rel[OF Lazy])
  show "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 (?b_if, ?cont_if)"
    by (auto intro: wf_rel_extend_1 Rel1 Red2)
next                                                                             
  from ElseBlockEmpty obtain else_name where "empty_else_block = empty_bigblock else_name" 
    using is_empty_bigblock.elims(2) by auto
  have "expr_wf_rel (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
     ctxt_vpr StateCons P ctxt e2 (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock else_name])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_short_circuit_wf_rel[OF Lazy])
       apply (insert Guard)
       apply simp
      apply simp
     apply (rule ExpRel)
    apply (rule wf_rel_extend_1)
     apply (rule WfRel)
    by (fastforce intro: Red3) 
  thus "expr_wf_rel
     (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
     ctxt_vpr StateCons P ctxt e2 (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_else_block])) None, KSeq bNext cont) (bNext, cont)"
    using \<open>empty_else_block = _\<close>
    by simp
next
  from ElseBlockEmpty obtain else_name where "empty_else_block = empty_bigblock else_name" 
    using is_empty_bigblock.elims(2) by auto
  have "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock else_name])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_no_short_circuit_seq_wf_rel[OF Lazy])
      apply (insert Guard)
    by (auto intro: ExpRel)
  thus "wf_rel R R (\<lambda>\<omega>def \<omega>. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_else_block])) None, KSeq bNext cont) (bNext, cont)"
    using \<open>empty_else_block = _\<close>
    by simp
qed

(* TODO: extract the common parts from this lemma *)
lemma syn_field_access_valid_wf_rel:
  assumes 
         CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
         TyRepWf: "wf_ty_repr_bpl TyRep" and
         EmptyRunTypeContext: "rtype_interp ctxt = []" and
         StateRel: "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
         ExpRel:   "exp_rel_vpr_bpl R ctxt_vpr ctxt e e_r_bpl" and
         FunMap:   "FunMap FHasPerm = has_perm_name" and
         MaskExp:  "e_m_bpl = Lang.Var (mask_var_def Tr)" and
         FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
       TypeParams: "ts = [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]"
   shows "wf_rel_fieldacc get_valid_locs R R ctxt_vpr StateCons P ctxt e f 
           ((BigBlock name ((Assert (FunExp has_perm_name ts [e_m_bpl, e_r_bpl, e_f_bpl]))#cs) str tr), cont)
           ((BigBlock name cs str tr), cont)"
proof (rule wf_rel_intro)

  from FieldRelSingle obtain f_bpl \<tau> where
    FieldRel: "field_translation Tr f = Some f_bpl" and
    RcvExp:   "e_f_bpl = Lang.Var f_bpl" and
    FieldTy: "declared_fields Pr f = Some \<tau>" and
    FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
    by (auto elim: field_rel_single_elim)

  (*note WdStateEq = conjunct1[OF StateRel]*)
  note StateRel0 = state_rel_state_rel0[OF StateRel]
  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns"

  have RedFieldBpl: "red_expr_bpl ctxt e_f_bpl ns ((AbsV (AField (NormalField f_bpl \<tau>))))"    
    using \<open>e_f_bpl = _\<close> FieldRel FieldTy StateRel0[OF R]
    unfolding state_rel0_def field_rel_def
    by (fastforce intro: red_expr_red_exprs.intros)

  obtain m_bpl where RedMaskBpl: "red_expr_bpl ctxt e_m_bpl ns (AbsV (AMask m_bpl))" and
                 MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) m_bpl"
    using \<open>e_m_bpl = _\<close> state_rel0_mask_var_def_rel[OF StateRel0[OF R]]
    unfolding state_rel_def state_rel0_def mask_var_rel_def 
    by (auto intro!: Semantics.RedVar)

  have RedFunHasPerm: "\<And>r. red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef r)) \<Longrightarrow>
                   red_expr_bpl ctxt (FunExp (FunMap FHasPerm) ts [e_m_bpl, e_r_bpl, e_f_bpl]) ns 
           (BoolV ((m_bpl (r, NormalField f_bpl \<tau>)) > 0))"
        apply (subst \<open>ts = _\<close>)
        apply (rule RedFunOp)
          apply (rule ctxt_wf_fun_interp[OF CtxtWf])
         apply (fastforce intro: RedExpListNil RedExpListCons RedMaskBpl RedFieldBpl)
        apply simp
    apply (rule lift_fun_decl_well_typed)
    by (auto simp: vpr_to_bpl_ty_closed[OF TyRepWf FieldTyBpl] FieldTyBpl EmptyRunTypeContext)
  
  from MaskRel have MaskRelLoc:"\<And>a. red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef (Address a))) \<Longrightarrow> 
                                Rep_preal ((get_mh_total_full \<omega>def) (a, f)) = m_bpl (Address a, NormalField f_bpl \<tau>)"
      using FieldTy FieldRel 
      unfolding mask_rel_def
      using if_SomeD by fastforce

  text \<open>Show normal case\<close>
  show "\<exists>a. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<and> (a, f) \<in> get_valid_locs \<omega>def \<Longrightarrow>
          \<exists>ns'. red_ast_bpl P ctxt
                 ((BigBlock name (cmd.Assert (FunExp has_perm_name ts [e_m_bpl, e_r_bpl, e_f_bpl]) # cs) str tr, cont), Normal ns)
                 ((BigBlock name cs str tr, cont), Normal ns') \<and>
                R \<omega>def \<omega> ns'" (is "?A \<Longrightarrow> ?B")
  proof -
    assume "?A"

    from this obtain a where
      RedRcv: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))" and
      ValidLoc: "(a, f) \<in> get_valid_locs \<omega>def"
      by auto

    hence RedRcvBpl: "red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef (Address a)))"
      using exp_rel_vpr_bpl_elim[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))
  
    from ValidLoc have VprHasPerm: "pgt (get_mh_total_full \<omega>def (a,f)) pnone"
      by (simp add: get_valid_locs_def)
  
    with MaskRelLoc[OF RedRcvBpl] have BplHasPerm: "m_bpl (Address a, NormalField f_bpl \<tau>) > 0" 
      by (simp add: PosReal.pgt.rep_eq zero_preal.rep_eq)
  
    have "red_ast_bpl P ctxt
              ((BigBlock name (cmd.Assert (FunExp has_perm_name ts [e_m_bpl, e_r_bpl, e_f_bpl]) # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Normal ns)"
      using RedFunHasPerm[OF RedRcvBpl] BplHasPerm
      by (auto simp: HOL.sym[OF FunMap] intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssertOk)      
    
    thus "?B" using R by blast
  qed

  text \<open>Show failure case\<close>
  show "\<exists>v. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v \<and>
           (v = VRef Null \<or> (\<exists>a. v = VRef (Address a) \<and> (a, f) \<notin> get_valid_locs \<omega>def)) \<Longrightarrow>
       \<exists>c'. red_ast_bpl P ctxt
             ((BigBlock name (cmd.Assert (FunExp has_perm_name ts [e_m_bpl, e_r_bpl, e_f_bpl]) # cs) str tr, cont), Normal ns) c' \<and>
            snd c' = Failure"
       (is "?A \<Longrightarrow> ?B")
  proof -
    assume "?A"

    from this obtain r where
      RedRcv: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
      RcvVal: "r = Null \<or> (\<exists>a. r = Address a \<and> (a, f) \<notin> get_valid_locs \<omega>def)"
      by blast

    have RedRcvBpl: "red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef r))"
      using exp_rel_vpr_bpl_elim[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))

    have BplHasNoPerm: "m_bpl (r, NormalField f_bpl \<tau>) = 0"
    proof (cases rule: disjE[OF RcvVal])
      case 1
      then show ?thesis 
        using MaskRel
        unfolding mask_rel_def
        by blast
    next
      case 2
      then show ?thesis 
        using MaskRel MaskRelLoc ExpRel
        unfolding mask_rel_def get_valid_locs_def        
        by (metis R RedRcv exp_rel_vpr_bpl_elim mem_Collect_eq zero_preal.rep_eq preal_pnone_pgt val_rel_vpr_bpl.simps(3))
    qed

    have "red_ast_bpl P ctxt
              ((BigBlock name (cmd.Assert (FunExp has_perm_name ts [e_m_bpl, e_r_bpl, e_f_bpl]) # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Failure)"
      using RedFunHasPerm[OF RedRcvBpl] BplHasNoPerm
      by (auto simp: HOL.sym[OF FunMap] intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssertFail)
    thus "?B" by auto      
  qed
qed

\<comment>\<open>TODO: write more general lemma that captures wf_rel_field_acc in general (currently lots of duplication
between the lemmas that show wf_rel_field_acc)\<close>
lemma syn_field_access_writeable_wf_rel:
  assumes 
         CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
         TyRepWf: "wf_ty_repr_bpl TyRep" and
         MaskReadWf: "mask_read_wf TyRep ctxt (mask_read Tr)" and
         StateRel: "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr  AuxPred ctxt \<omega>def \<omega> ns" and
         MaskLookup: "mask_lookup = mask_read Tr e_m_bpl e_r_bpl e_f_bpl ts" and
         WritePermConst: "const_repr Tr CWritePerm = writePermConst" and
         ExpRel:   "exp_rel_vpr_bpl R ctxt_vpr ctxt e e_r_bpl" and
         MaskExp:  "e_m_bpl = Lang.Var (mask_var_def Tr)" and
         FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
         TypeParams: "ts = [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]"
   shows "wf_rel_fieldacc get_writeable_locs R R ctxt_vpr StateCons P ctxt e f 
           ((BigBlock name ((Assert ((Var writePermConst) \<guillemotleft>Eq\<guillemotright> mask_lookup))#cs) str tr), cont)
           ((BigBlock name cs str tr), cont)"
proof (rule wf_rel_intro)

  from FieldRelSingle obtain \<tau> f_bpl where
      FieldRel: "field_translation Tr f = Some f_bpl" and     
         RcvExp:   "e_f_bpl = Lang.Var f_bpl" and
          FieldTy: "declared_fields Pr f = Some \<tau>" and
       FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
    by (auto elim: field_rel_single_elim)
  
  note StateRel0 = state_rel_state_rel0[OF StateRel]
  fix v \<omega>def \<omega> ns
  assume R:"R \<omega>def \<omega> ns" 
  hence StateRelInst: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
    using StateRel
    by auto

  have RedFieldBpl: "red_expr_bpl ctxt e_f_bpl ns ((AbsV (AField (NormalField f_bpl \<tau>))))"    
    using \<open>e_f_bpl = _\<close> FieldRel FieldTy StateRel0[OF R]
    unfolding state_rel0_def field_rel_def
    by (fastforce intro: red_expr_red_exprs.intros)

  obtain m_bpl where RedMaskBpl: "red_expr_bpl ctxt e_m_bpl ns (AbsV (AMask m_bpl))" and
                 MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) m_bpl"
    using \<open>e_m_bpl = _\<close> state_rel0_mask_var_def_rel[OF StateRel0[OF R]]
    unfolding state_rel_def state_rel0_def mask_var_rel_def 
    by (auto intro: red_expr_red_exprs.intros)

  have RedMaskLookup: "\<And>r. red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef r)) \<Longrightarrow>
                   red_expr_bpl ctxt mask_lookup ns 
           (RealV ((m_bpl (r, NormalField f_bpl \<tau>))))"
    apply (subst \<open>mask_lookup = _\<close>)
    apply (subst \<open>ts = _\<close>)    
    apply (rule mask_read_wf_apply[OF MaskReadWf])
        apply simp
       apply (rule RedMaskBpl)
      apply simp
     apply (rule RedFieldBpl)
    apply (simp add: FieldTyBpl)
    done

  have RedFullPerm: "red_expr_bpl ctxt (Var writePermConst) ns (RealV 1)"
    using WritePermConst state_rel0_boogie_const_rel[OF state_rel_state_rel0[OF StateRelInst]]
    unfolding boogie_const_rel_def
    by (auto intro: Semantics.RedVar)
  
  from MaskRel have MaskRelLoc:"\<And>a. red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef (Address a))) \<Longrightarrow> 
                                    Rep_preal ((get_mh_total_full \<omega>def) (a, f)) = m_bpl (Address a, NormalField f_bpl \<tau>)"
      using FieldTy FieldRel 
      unfolding mask_rel_def
      by (simp add: if_Some_iff)

  text \<open>Show normal case\<close>
  show "\<exists>a. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<and> (a, f) \<in> get_writeable_locs \<omega>def \<Longrightarrow>
          \<exists>ns'. red_ast_bpl P ctxt
                 ((BigBlock name (cmd.Assert (expr.Var writePermConst \<guillemotleft>Lang.binop.Eq\<guillemotright> mask_lookup) # cs) str tr, cont), Normal ns)
                 ((BigBlock name cs str tr, cont), Normal ns') \<and>
                R \<omega>def \<omega> ns'" (is "?A \<Longrightarrow> ?B")
  proof -
    assume "?A"

    from this obtain a where
      RedRcv: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))" and
      WriteableLocs: "(a, f) \<in> get_writeable_locs \<omega>def"
      by auto

    hence RedRcvBpl: "red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef (Address a)))"
      using exp_rel_vpr_bpl_elim[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))
  
    from WriteableLocs have VprHasPerm: "(get_mh_total_full \<omega>def (a,f)) = pwrite"
      by (simp add: get_writeable_locs_def)
  
    with MaskRelLoc[OF RedRcvBpl] have BplHasPerm: "m_bpl (Address a, NormalField f_bpl \<tau>) = 1"    
      by (simp add: one_preal.rep_eq)
  
    have "red_ast_bpl P ctxt
              ((BigBlock name (cmd.Assert (expr.Var writePermConst \<guillemotleft>Lang.binop.Eq\<guillemotright> mask_lookup) # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Normal ns)"
      using BplHasPerm RedMaskLookup[OF RedRcvBpl] RedFullPerm
      by (auto intro: red_expr_red_exprs.intros intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssertOk)
    
    thus "?B" using R by blast
  qed

  text \<open>Show failure case\<close>
  show "\<exists>v. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v \<and>
           (v = VRef Null \<or> (\<exists>a. v = VRef (Address a) \<and> (a, f) \<notin> get_writeable_locs \<omega>def)) \<Longrightarrow>
       \<exists>c'. red_ast_bpl P ctxt
             ((BigBlock name (cmd.Assert (expr.Var writePermConst \<guillemotleft>Lang.binop.Eq\<guillemotright> mask_lookup) # cs) str tr, cont), Normal ns) c' \<and>
            snd c' = Failure"
       (is "?A \<Longrightarrow> ?B")
  proof -
    assume "?A"

    from this obtain r where
      RedRcv: "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
      RcvVal: "r = Null \<or> (\<exists>a. r = Address a \<and> (a, f) \<notin> get_writeable_locs \<omega>def)"
      by blast

    have RedRcvBpl: "red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef r))"
      using exp_rel_vpr_bpl_elim[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))

    have BplHasNoPerm: "m_bpl (r, NormalField f_bpl \<tau>) \<noteq> 1"
    proof (cases rule: disjE[OF RcvVal])
      case 1
      then show ?thesis 
        using MaskRel
        unfolding mask_rel_def
        by auto
    next
      case 2
      then show ?thesis 
        using MaskRel MaskRelLoc ExpRel
        unfolding mask_rel_def get_writeable_locs_def  
        using RedRcvBpl Rep_preal_inject one_preal.rep_eq by fastforce
    qed

    have "red_ast_bpl P ctxt
              ((BigBlock name (cmd.Assert (expr.Var writePermConst \<guillemotleft>Lang.binop.Eq\<guillemotright> mask_lookup)  # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Failure)"
      using BplHasNoPerm RedMaskLookup[OF RedRcvBpl] RedFullPerm
      by (auto intro: red_expr_red_exprs.intros intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssertFail)
    thus "?B" by auto      
  qed
qed

method wf_rel_bop_op_trivial_tac =
        (rule wf_rel_bop_op_trivial, solves\<open>simp\<close>) 

\<comment>\<open>the following tactic only works for trivial well-definedness checks; see ExprWfRel.thy for a more general 
  tactic expressed in ML\<close>

method wf_tac = (rule var_expr_wf_rel | 
                 rule lit_expr_wf_rel |
                 (rule unop_expr_wf_rel_2, solves \<open>wf_tac\<close>) |
                 (rule binop_eager_expr_wf_rel,
                   solves\<open>simp\<close> \<comment>\<open>binop is eager\<close>,
                   solves \<open>wf_tac\<close> \<comment>\<open>wf e1\<close>,
                   solves \<open>wf_tac\<close> \<comment>\<open>wf_e2\<close>,
                   wf_rel_bop_op_trivial_tac
                 ) |
                 ( rule binop_lazy_expr_wf_rel,
                   solves\<open>simp\<close> \<comment>\<open>binop is lazy\<close>,
                   solves \<open>wf_tac\<close> \<comment>\<open>wf e1\<close>,
                   solves \<open>wf_tac\<close> \<comment>\<open>wf_e2\<close>,
                   rule wf_rel_no_failure_refl
                 )
                )

end