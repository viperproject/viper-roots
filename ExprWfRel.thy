theory ExprWfRel
imports ViperBoogieBasicRel ViperBoogieFunctionInst ExpRel Simulation TotalSemProperties
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
  "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>'  \<equiv>
   \<forall> \<omega>def \<omega> ns.
    R \<omega>def \<omega> ns \<longrightarrow>
     (IsNormal \<omega>def \<omega> \<longrightarrow>
       (\<exists> ns'.
         red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and>
         R' \<omega>def \<omega> ns')
     ) \<and>
     (IsFailure \<omega>def \<omega> \<longrightarrow>
       (\<exists>c'.         
        red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and>
        snd c' = Failure)
     )"

\<comment>\<open>TODO: replace wf_rel by wf_rel_inst and reuse propagation lemmas from rel_general\<close>
definition wf_rel_inst ::
  "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> 'a bpl_state \<Rightarrow> bool) \<Rightarrow> 
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> 'a bpl_state \<Rightarrow> bool) \<Rightarrow>
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ast \<Rightarrow>
   'a econtext_bpl \<Rightarrow>
   (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont)  \<Rightarrow> 
   bool" where
  "wf_rel_inst R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>' \<equiv>
        rel_general 
            (\<lambda> \<omega>def_\<omega> ns. R (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns)
            (\<lambda> \<omega>def_\<omega> ns. R' (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns)
            (\<lambda>\<omega>def_\<omega> \<omega>def_\<omega>'. \<omega>def_\<omega> = \<omega>def_\<omega>' \<and> IsNormal (fst \<omega>def_\<omega>) (snd (\<omega>def_\<omega>)))
            (\<lambda>\<omega>def_\<omega>. IsFailure (fst \<omega>def_\<omega>) (snd (\<omega>def_\<omega>)))
            P ctxt \<gamma> \<gamma>'"

lemma wf_rel_inst_eq:
  "wf_rel R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>' \<longleftrightarrow> wf_rel_inst R R' IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
  unfolding wf_rel_def wf_rel_inst_def rel_general_def
  by auto

lemmas wf_rel_inst_eq_1 = HOL.iffD1[OF wf_rel_inst_eq]

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
  unfolding wf_rel_def
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
  unfolding wf_rel_def
  by blast

lemma exprs_wf_rel_normal_elim:
  assumes 
       "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs)"
  shows
        "\<exists> ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>def \<omega> ns'"
  using assms
  unfolding exprs_wf_rel_def wf_rel_def
  by blast

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
  unfolding wf_rel_def
  by blast

lemma exprs_wf_rel_failure_elim:
  assumes 
       "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"
  shows
       "\<exists> c. red_ast_bpl P ctxt (\<gamma>, Normal ns) c \<and> snd c = Failure"
  using assms
  unfolding exprs_wf_rel_def wf_rel_def
  by blast
  
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
  unfolding wf_rel_def red_ast_bpl_def
  by blast

lemma exprs_wf_rel_Nil: "exprs_wf_rel R ctxt_vpr StateCons P ctxt [] \<gamma> \<gamma>"
  unfolding exprs_wf_rel_def 
  apply (rule wf_rel_intro)
  by (auto intro: red_ast_bpl_refl dest: red_exp_list_failure_Nil)

subsection \<open>Rules to derive semantic well-definedness relation\<close>

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
  unfolding wf_rel_def
  apply (insert assms)
  apply clarify
  by (fastforce dest: unop_elim simp: wf_rel_def split: extended_val.split)

lemma wf_rel_extend_1:
  assumes 
   Wf:"wf_rel R R' IsNormal IsFailure P ctxt \<gamma>1 \<gamma>2" and
   Red:"\<And>\<omega>def \<omega> ns2. R' \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3) \<and> R'' \<omega>def \<omega> ns3"
 shows
   "wf_rel R R'' IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
proof (rule wf_rel_intro)
  fix v \<omega>def \<omega> ns1  
  assume R:"R \<omega>def \<omega> ns1" and "IsNormal \<omega>def \<omega>"
  from this obtain ns2 where "R' \<omega>def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Wf
    unfolding wf_rel_def
    by blast
  from this obtain ns3 where "red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3)" and "R'' \<omega>def \<omega> ns3"
    using Red
    by blast    
  hence "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns3)" using Red1
    by (simp add: red_ast_bpl_def)
  with \<open>R'' \<omega>def \<omega> ns3\<close> show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns') \<and>  R'' \<omega>def \<omega> ns'"
    by blast
qed (insert assms, unfold wf_rel_def, blast)

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
proof (rule wf_rel_intro)
  fix v \<omega>def \<omega> ns1  
  assume R:"R \<omega>def \<omega> ns1" and Normal:"IsNormal \<omega>def \<omega>"
  from this obtain ns2 where "R' \<omega>def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Red
    by blast
  with Normal obtain ns3 where "red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3)" and "R'' \<omega>def \<omega> ns3"
    using Wf
    unfolding wf_rel_def
    by blast
  hence "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns3)" using Red1
    by (simp add: red_ast_bpl_def)
  with \<open>R'' \<omega>def \<omega> ns3\<close> show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns') \<and> R'' \<omega>def \<omega> ns'"
    by blast
next
  fix v \<omega>def \<omega> ns1  
  assume R:"R \<omega>def \<omega> ns1" and Failure:"IsFailure \<omega>def \<omega>"
  from this obtain ns2 where "R' \<omega>def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Red
    by blast
  with Failure show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns1) c' \<and> snd c' = Failure"
    unfolding red_ast_bpl_def
    by (metis (no_types, lifting) Wf red_ast_bpl_def rtranclp_trans wf_rel_failure_elim)
qed

lemma wf_rel_extend_2_same_rel:
  assumes 
   Red:"\<And>\<omega>def \<omega> ns2. R \<omega>def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>1, Normal ns2) (\<gamma>2, Normal ns3) \<and> R \<omega>def \<omega> ns3" and
   Wf:"wf_rel R R IsNormal IsFailure P ctxt \<gamma>2 \<gamma>3"
 shows 
  "wf_rel R R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
  using assms wf_rel_extend_2
  by blast

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
    then show ?thesis using assms wf_rel_failure_elim
      using \<open>R \<omega>def \<omega> ns\<close> by blast
  qed
qed

    

text \<open>In the unfolding relation lemma, the relations R and R' are used to relate to the well-definedness
state outside and inside the unfolding, respectively. The assumptions express how to move from R to
R' and back:
  \<^item> R to R': Via reduction in the Boogie program (basically some initialization code follow by an inhale)
  \<^item> R' to R: The corresponding assumption expresses that R' contains all the information in R. In particular,
   if R has some constraint on a Boogie variable, then R' must have the same constraint. This should
   work for the current encoding, but may be too strong.
TODO: I think the current R' to R does not make sense. One needs to somehow share ns between the two,
which would mean another parameter. Not sure what the most abstract notion is here. One option could be 
to have another Boogie state is input and then one could express two-state invariants such as 
"value stays the same". It would also be interesting to understand whether Benjamin's auxiliary 
constraints make sense here.

lemma unfolding_wf_rel:
  assumes 
        R_to_R': "\<And> \<omega>def \<omega>def' vs \<omega> ns. 
                      R \<omega>def \<omega> ns \<Longrightarrow>
                      unfold_rel ctxt_vpr StateCons p vs pwrite \<omega>def \<omega>def' \<Longrightarrow>                      
                      \<exists>ns'. R' \<omega>def' \<omega> ns' \<and>                             
                            red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns')" and
        R'_to_R: "\<And> \<omega>def \<omega>def' \<omega> ns ns'. R \<omega>def \<omega> ns \<Longrightarrow> R' \<omega>def' \<omega> ns' \<Longrightarrow> R \<omega>def \<omega> ns'" and
        WfRelArgs: "exprs_wf_rel R' ctxt_vpr StateCons P ctxt xs \<gamma>1 \<gamma>2" and
        WfRel: "expr_wf_rel R' ctxt_vpr StateCons P ctxt ubody \<gamma>2 \<gamma>3"
      shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (Unfolding p xs ubody) \<gamma>1 \<gamma>3"
  oops
\<close>

subsubsection \<open>Well-definedness for free if expressions are subexpressions of a framed assertion\<close>

lemma assertion_framing_exprs_wf_rel_inh:
  assumes "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> 
               assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def \<and>
               get_store_total \<omega> = get_store_total \<omega>def \<and> 
               get_trace_total \<omega> = get_trace_total \<omega>def \<and>
               get_h_total_full \<omega> = get_h_total_full \<omega>def"
      and "es = sub_expressions_atomic A"
      and ExprConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es"
    shows  "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>"
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
    AssertionFramed: "assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def" and
    OnlyMaskDiffers: "get_store_total \<omega> = get_store_total \<omega>def \<and> 
     get_trace_total \<omega> = get_trace_total \<omega>def \<and>
     get_h_total_full \<omega> = get_h_total_full \<omega>def"
    using assms
    by auto

  from RedExps OnlyMaskDiffers have "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega>def None"
    using red_pure_exp_only_differ_on_mask(2) ExprConstraint
    by blast
  hence "red_inhale ctxt_vpr StateCons (Atomic A) \<omega>def RFailure"
    using assms \<open>es \<noteq> []\<close> InhSubAtomicFailure
    by blast

  moreover from \<open>R \<omega>def \<omega> ns\<close> have "assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def"
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
               assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def \<and>
               \<omega> = \<omega>def"
      and "es = sub_expressions_atomic A"
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
      AssertionFramed: "assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def" and "\<omega> = \<omega>def"
      using assms
      by auto
  
    hence "red_inhale ctxt_vpr StateCons (Atomic A) \<omega>def RFailure"
      using assms \<open>es \<noteq> []\<close> InhSubAtomicFailure RedExps
      by blast
  
    moreover from \<open>R \<omega>def \<omega> ns\<close> have "assertion_framing_state ctxt_vpr StateCons (Atomic A) \<omega>def"
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
    hence "v2_bpl = RealV (real_of_rat p)" and "p \<noteq> 0" using RedBpl ValRel \<open>v2 = _\<close> NonZero by auto

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
                               real_of_rat (Rep_prat ((get_mh_total_full \<omega>def) (a, f))) = (m_bpl (Address a, NormalField f_bpl \<tau>))"
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
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))
  
    from ValidLoc have VprHasPerm: "pgt (get_mh_total_full \<omega>def (a,f)) pnone"
      by (simp add: get_valid_locs_def)
  
    with MaskRelLoc[OF RedRcvBpl] have BplHasPerm: "m_bpl (Address a, NormalField f_bpl \<tau>) > 0"    
      using prat_positive_transfer
      by blast
  
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
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] RedRcv R   
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
        by (metis  R RedRcv exp_rel_vpr_bpl_elim mem_Collect_eq of_rat_0 zero_prat.rep_eq prat_pnone_pgt val_rel_vpr_bpl.simps(3))
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
                               real_of_rat (Rep_prat ((get_mh_total_full \<omega>def) (a, f))) = (m_bpl (Address a, NormalField f_bpl \<tau>))"
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
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] RedRcv R   
      by (metis val_rel_vpr_bpl.simps(3))
  
    from WriteableLocs have VprHasPerm: "(get_mh_total_full \<omega>def (a,f)) = pwrite"
      by (simp add: get_writeable_locs_def)
  
    with MaskRelLoc[OF RedRcvBpl] have BplHasPerm: "m_bpl (Address a, NormalField f_bpl \<tau>) = 1"    
      by (simp add: one_prat.rep_eq)
  
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
      using exp_rel_vpr_bpl_elim_2[OF ExpRel] RedRcv R   
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
        using RedRcvBpl Rep_prat_inject one_prat.rep_eq by fastforce
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