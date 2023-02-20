theory ExprWfRel
imports ViperBoogieBasicRel
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
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow> bool) \<Rightarrow>
   ast \<Rightarrow>
   'a econtext_bpl \<Rightarrow>
   (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont)  \<Rightarrow> 
   bool" where
  "wf_rel R IsNormal IsFailure P ctxt \<gamma> \<gamma>'  \<equiv>
   \<forall> \<omega>_def \<omega> ns.
    R \<omega>_def \<omega> ns \<longrightarrow>
     (IsNormal \<omega>_def \<omega> \<longrightarrow>
       (\<exists> ns'.
         R \<omega>_def \<omega> ns' \<and>
         red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns'))
     ) \<and>
     (IsFailure \<omega>_def \<omega> \<longrightarrow>
       (\<exists>c'. 
        snd c' = Failure \<and>
        red_ast_bpl P ctxt (\<gamma>, Normal ns) c')
     )"

text \<open>TODO: change v to VFailure in the normal case\<close>

abbreviation expr_wf_rel :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow> ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool" where 
  "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>' \<equiv>
   wf_rel R (\<lambda>\<omega>_def \<omega>. \<exists>v. (ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v )) (\<lambda>\<omega>_def \<omega>. (ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)) P ctxt \<gamma> \<gamma>'"

fun exprs_wf_rel :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow>  ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr list \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "exprs_wf_rel R ctxt_vpr StateCons P ctxt Nil \<gamma> \<gamma>' = (\<gamma> = \<gamma>')"
  | "exprs_wf_rel R ctxt_vpr StateCons P ctxt (e#es) \<gamma> \<gamma>' = 
          (\<exists>\<gamma>''. expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>'' \<and>
            exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma>'' \<gamma>')"

lemma wf_rel_intro [case_names normal failure]:
  assumes
  cases:"\<And>v \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> 
         IsNormal \<omega>_def \<omega> \<Longrightarrow>
         \<exists> ns'.
           R \<omega>_def \<omega> ns' \<and>
           red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')" 
    "\<And>v \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> 
         IsFailure \<omega>_def \<omega> \<Longrightarrow> 
         (\<exists>c'. 
          snd c' = Failure \<and>
          red_ast_bpl P ctxt (\<gamma>, Normal ns) c')"
 shows "wf_rel R IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
  unfolding wf_rel_def
  using assms
  by fastforce

lemma wf_rel_normal_elim:
  assumes 
   "wf_rel R IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
   "R \<omega>_def \<omega> ns" and 
   "IsNormal \<omega>_def \<omega>"
 shows
   "\<exists> ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
  using assms
  unfolding wf_rel_def
  by blast

lemma exprs_wf_rel_elim:
  assumes 
       "exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>'" and
       "R \<omega>_def \<omega> ns"
       "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>_def) es \<omega> (Some vs)"
  shows
        "\<exists> ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
  using assms
proof (induction R ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>' arbitrary: ns vs rule: exprs_wf_rel.induct)
  case (1 R ctxt_vpr StateCons P ctxt \<gamma> \<gamma>')
  then show ?case by (auto simp: red_ast_bpl_def)
next
  case (2 R ctxt_vpr StateCons P ctxt e es \<gamma> \<gamma>')

  from this obtain \<gamma>'' where 
    WfRelE:"expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma> \<gamma>''" and 
    WfRelEs:"exprs_wf_rel R ctxt_vpr StateCons P ctxt es \<gamma>'' \<gamma>'" by auto

  note RedExps=\<open>red_pure_exps_total ctxt_vpr StateCons (Some \<omega>_def) (e # es) \<omega> (Some vs)\<close>
  from this obtain v' vs' where "vs = v'#vs'" and
         "red_pure_exp_total ctxt_vpr StateCons (Some \<omega>_def) e  \<omega> (Val v')" and
         RedExpsEs:"red_pure_exps_total ctxt_vpr StateCons (Some \<omega>_def) es \<omega> (Some vs')"
    using RedExpList_case
    by (metis (no_types, lifting) RedExpList list_all2_Cons1)

  with wf_rel_normal_elim[OF WfRelE \<open>R _ _ _\<close>] obtain ns' where
         R2:"R \<omega>_def \<omega> ns'" and RedBpl: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>'', Normal ns')"
    by blast

  obtain ns'' where
    "R \<omega>_def \<omega> ns'' \<and> red_ast_bpl P ctxt (\<gamma>'', Normal ns') (\<gamma>', Normal ns'')"
    using "2.IH"[OF WfRelEs R2 RedExpsEs]
    by blast

  with RedBpl show ?case
    by (auto simp: red_ast_bpl_def)
qed

lemma wf_rel_failure_elim:
  assumes 
   "wf_rel R IsNormal IsFailure P ctxt \<gamma> \<gamma>'"
   "R \<omega>_def \<omega> ns" and 
   "IsFailure \<omega>_def \<omega>"
 shows 
   "(\<exists>c'. snd c' = Failure \<and>
          red_ast_bpl P ctxt (\<gamma>, Normal ns) c')"
  using assms
  unfolding wf_rel_def
  by blast

lemma expr_wf_rel_intro:
  assumes
    "\<And>v \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> 
         ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> 
         v = VFailure \<Longrightarrow> 
         (\<exists>c'. 
          snd c' = Failure \<and>
          red_ast_bpl P ctxt (\<gamma>, Normal ns) c')" and
   "\<And>v \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> 
        ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> v \<noteq> VFailure \<Longrightarrow>
         \<exists> ns'.
           R \<omega>_def \<omega> ns' \<and>
           red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>'"
 using assms
  by (auto intro: wf_rel_intro)

lemma expr_wf_rel_intro_trivial:
  assumes "\<And>v \<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> v \<noteq> VFailure"  
  shows "expr_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma> \<gamma>"
proof (rule expr_wf_rel_intro)
next
  fix v \<omega>_def \<omega> ns
  assume "R \<omega>_def \<omega> ns"
  assume "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  assume "v \<noteq> VFailure"
  show 
   " \<exists>ns'. R \<omega>_def \<omega> ns' \<and>
           red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns')"
    apply (rule exI)
    apply (rule conjI)
     apply (rule \<open>R _ _ _\<close>)
    by (simp add: red_ast_bpl_def)
qed (insert assms, fastforce)

lemma wf_rel_no_failure_refl: "wf_rel R IsNormal (\<lambda>_ _. False) P ctxt \<gamma> \<gamma>" 
  unfolding wf_rel_def red_ast_bpl_def
  by blast

subsection \<open>Rules to derive semantic well-definedness relation\<close>

lemma var_never_fails: 
  assumes "Pr, ctxt_vpr, \<omega>_def \<turnstile> \<langle>ViperLang.Var x; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows "v \<noteq> VFailure"
  using assms
  by (cases) auto

lemma lit_never_fails:
  assumes "ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>ViperLang.ELit lit; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows "v \<noteq> VFailure"
  using assms
  by (cases) auto

lemma unop_elim:
  assumes "ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>ViperLang.Unop uop e; \<omega>\<rangle> [\<Down>]\<^sub>t v"
  shows 
     "if v = VFailure then 
        ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure 
      else 
        \<exists>v'. ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
  using assms
  by (cases) auto

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
   Wf:"wf_rel R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>2" and
   Red:"\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3) \<and> R \<omega>_def \<omega> ns3"
 shows
   "wf_rel R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
proof (rule wf_rel_intro)
  fix v \<omega>_def \<omega> ns1  
  assume R:"R \<omega>_def \<omega> ns1" and "IsNormal \<omega>_def \<omega>"
  from this obtain ns2 where "R \<omega>_def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Wf
    unfolding wf_rel_def
    by blast
  from this obtain ns3 where "red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3)" and "R \<omega>_def \<omega> ns3"
    using Red
    by blast    
  hence "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns3)" using Red1
    by (simp add: red_ast_bpl_def)
  with \<open>R \<omega>_def \<omega> ns3\<close> show "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns')"
    by blast
qed (insert assms, unfold wf_rel_def, blast)

lemma wf_rel_extend_2:
  assumes 
   Red:"\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>1, Normal ns2) (\<gamma>2, Normal ns3) \<and> R \<omega>_def \<omega> ns3" and
   Wf:"wf_rel R IsNormal IsFailure P ctxt \<gamma>2 \<gamma>3"
 shows 
  "wf_rel R IsNormal IsFailure P ctxt \<gamma>1 \<gamma>3"
proof (rule wf_rel_intro)
  fix v \<omega>_def \<omega> ns1  
  assume R:"R \<omega>_def \<omega> ns1" and Normal:"IsNormal \<omega>_def \<omega>"
  from this obtain ns2 where "R \<omega>_def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Red
    by blast
  with Normal obtain ns3 where "red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>3, Normal ns3)" and "R \<omega>_def \<omega> ns3"
    using Wf
    unfolding wf_rel_def
    by blast
  hence "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns3)" using Red1
    by (simp add: red_ast_bpl_def)
  with \<open>R \<omega>_def \<omega> ns3\<close> show "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>3, Normal ns')"
    by blast
next
  fix v \<omega>_def \<omega> ns1  
  assume R:"R \<omega>_def \<omega> ns1" and Failure:"IsFailure \<omega>_def \<omega>"
  from this obtain ns2 where "R \<omega>_def \<omega> ns2" and Red1: "red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2)" using Red
    by blast
  with Failure show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) c'"
    unfolding red_ast_bpl_def
    by (metis (no_types, lifting) Wf red_ast_bpl_def rtranclp_trans wf_rel_failure_elim)
qed

abbreviation wf_rel_bop_op 
  where "wf_rel_bop_op R ctxt_vpr StateCons P ctxt e1 bop e2 \<equiv>  wf_rel R 
            (\<lambda>\<omega>_def \<omega>. (\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v1) \<and> ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v2) \<and> (\<exists>v'. eval_binop v1 bop v2 = BinopNormal v')))
            (\<lambda>\<omega>_def \<omega>. (\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v1) \<and> ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v2) \<and> eval_binop v1 bop v2 = BinopOpFailure))
            P 
            ctxt"

lemma binop_eager_expr_wf_rel:
  assumes 
   Lazy:"binop_lazy bop = None" and
   Rel1: "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 \<gamma>1" and
   Rel2: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 \<gamma>1 \<gamma>2" and
   RelOp: "wf_rel_bop_op R ctxt_vpr StateCons P ctxt e1 bop e2 \<gamma>2 \<gamma>3"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 \<gamma>3"
proof (rule expr_wf_rel_intro)
  text \<open>Failure case\<close>
  fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"

  hence Red:"ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp
  from Red
  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
  proof cases 
  next
    case (RedBinopRightFailure v1)    
      from this obtain ns' where
             "R \<omega>_def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    moreover from this obtain c' where
      "snd c' = Failure" and
      "red_ast_bpl P ctxt (\<gamma>1, Normal ns') c'"
      using wf_rel_failure_elim[OF Rel2 \<open>R \<omega>_def \<omega> ns'\<close>] RedBinopRightFailure
      by blast
    ultimately show ?thesis
      by (fastforce simp: red_ast_bpl_def)
  next
    case (RedBinopOpFailure v1 v2)
      from this obtain ns' where
         "R \<omega>_def \<omega> ns'" and
         "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns')"
        using wf_rel_normal_elim[OF Rel1 R] wf_rel_normal_elim[OF Rel2] red_ast_bpl_def
        by (metis (no_types, lifting) rtranclp_trans)
      then show ?thesis
      using wf_rel_failure_elim[OF RelOp \<open>R \<omega>_def \<omega> ns'\<close>] RedBinopOpFailure red_ast_bpl_def
      by (metis (no_types, lifting) rtranclp_trans)      
  next
    case (RedSubFailure e)
    then show ?thesis
      using wf_rel_failure_elim[OF Rel1 R]
      by fastforce
  qed
next
  text\<open>Normal case\<close>
  fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v \<noteq> VFailure"
  from this obtain val where "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val val)"
    by (metis extended_val.exhaust)
  thus "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>3, Normal ns')"
  proof cases
    case (RedBinop v1 v2)
      from this obtain ns' where
             "R \<omega>_def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast
      from this obtain ns'' where
             "R \<omega>_def \<omega> ns''" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns'')"
        using wf_rel_normal_elim[OF Rel2] RedBinop
        by (metis (no_types, lifting) red_ast_bpl_def rtranclp_trans) 
      thus ?thesis      
        using wf_rel_normal_elim[OF RelOp] RedBinop
        by (metis (no_types, lifting) red_ast_bpl_def rtranclp_trans) 
  next
    case (RedBinopLazy v1)
    then show ?thesis using \<open>binop_lazy _ = _\<close> eval_binop_lazy_iff_2
      by (metis option.distinct(1))
  qed
qed

lemma binop_lazy_expr_wf_rel:
 assumes 
   Lazy:"binop_lazy bop = Some(b1,bResult)" and
   Rel1: "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 \<gamma>1" and
   Rel2a: "expr_wf_rel (\<lambda>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<and> 
                        (\<exists>b. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b) \<and> b \<noteq> b1 \<and> 
                             (\<exists> v2. eval_binop b bop v2 \<noteq> BinopTypeFailure))
                       ) ctxt_vpr StateCons P ctxt e2 \<gamma>1 \<gamma>2" and
   Rel2b: "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt \<gamma>1 \<gamma>2"
 shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 \<gamma>2"
proof (rule expr_wf_rel_intro)
  text \<open>Failure case\<close>
  fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"
    hence Red:"ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp
  from Red
  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
  proof cases
  next
    case (RedBinopRightFailure v1)    
      from this obtain ns' where
             Red_s_s':"R \<omega>_def \<omega> ns'"
                      "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    from \<open>eval_binop_lazy v1 bop = None\<close> have "v1 \<noteq> b1"
      using Lazy eval_binop_lazy_iff by force
    from this show ?thesis
      using Red_s_s' wf_rel_failure_elim[OF Rel2a HOL.conjI[OF Red_s_s'(1)] RedBinopRightFailure(2)] RedBinopRightFailure(1)
            \<open>\<exists>v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure\<close>
      by (fastforce simp: red_ast_bpl_def)
  next
    case (RedBinopOpFailure v1 v2)  
    moreover from this have "binop_lazy bop = None"
      using eval_binop_failure
      by fastforce
    ultimately show ?thesis
      using \<open>binop_lazy bop = Some(_)\<close> option.distinct(1)
      by metis        
  next
    case (RedSubFailure e)
    then show ?thesis
      using wf_rel_failure_elim[OF Rel1 R]
      by fastforce
  qed
next
  text \<open>Normal case\<close>
    fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v \<noteq> VFailure"
  from this obtain val where "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t (Val val)"
    by (metis extended_val.exhaust)
  thus "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns')"
  proof cases
    case (RedBinop v1 v2)
    hence "v1 \<noteq> b1" using Lazy eval_binop_lazy_iff by force
    from RedBinop have v1BinopWellTy:"\<exists> v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure"
      by (metis binop_result.distinct(3))
    from RedBinop obtain ns' where
             "R \<omega>_def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast
    from this \<open>v1 \<noteq> b1\<close> show ?thesis
      using wf_rel_normal_elim[OF Rel2a] RedBinop v1BinopWellTy
      by (metis (no_types, lifting) red_ast_bpl_def rtranclp_trans)
  next
    case (RedBinopLazy v1)
    hence  *:"binop_lazy bop = Some(v1, val)"
      by (simp add: eval_binop_lazy_iff)

    from RedBinopLazy obtain ns' where
             "R \<omega>_def \<omega> ns'" and
             "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns')"
      using wf_rel_normal_elim[OF Rel1 R] 
      by blast

    thus ?thesis
      using wf_rel_normal_elim[OF Rel2b \<open>R \<omega>_def \<omega> ns'\<close>] RedBinopLazy Lazy *
      by (auto simp: red_ast_bpl_def)
  qed
qed

abbreviation wf_rel_fieldacc
  where "wf_rel_fieldacc R ctxt_vpr StateCons P ctxt e f \<equiv> wf_rel R
           (\<lambda>\<omega>_def \<omega>. (\<exists>a. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a))) \<and> 
                       (a,f) \<in> get_valid_locs \<omega>_def))
           (\<lambda>\<omega>_def \<omega>. (\<exists>a. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a))) \<and> 
                       (a,f) \<notin> get_valid_locs \<omega>_def))
           P
           ctxt"

abbreviation wf_rel_nonnull
  where "wf_rel_nonnull R ctxt_vpr StateCons P ctxt e \<equiv> wf_rel R           
           (\<lambda>\<omega>_def \<omega>. (\<exists>v. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> v \<noteq> (VRef Null)))
           (\<lambda>\<omega>_def \<omega>. (\<exists>v. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<and> v = (VRef Null)))
           P
           ctxt"

lemma field_access_wf_rel:
  assumes ExpWfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e \<gamma>1 \<gamma>2" and
          WfRelNonNull: "wf_rel_nonnull R ctxt_vpr StateCons P ctxt e \<gamma>2 \<gamma>3" and
          FieldAccWfRel: "wf_rel_fieldacc R ctxt_vpr StateCons P ctxt e f \<gamma>3 \<gamma>4"
        shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (FieldAcc e f) \<gamma>1 \<gamma>3"
proof (rule expr_wf_rel_intro)
  fix v \<omega>_def \<omega> ns
  assume "R \<omega>_def \<omega> ns" and
         "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t v" and
         "v = VFailure"
  hence "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) c'"
  proof cases
    case (RedField a v)
    hence "(a, f) \<notin> get_valid_locs \<omega>_def" 
      by force    
    moreover have "VRef (Address a) \<noteq> VRef Null"      
      by blast
    ultimately show ?thesis using assms RedField wf_rel_failure_elim red_ast_bpl_def
     by (smt (verit, ccfv_SIG) \<open>R \<omega>_def \<omega> ns\<close> rtranclp_trans wf_rel_normal_elim) (*TODO, the smt tactic does not always work here*)
  next
    case RedFieldNullFailure
    then show ?thesis using assms wf_rel_failure_elim wf_rel_normal_elim \<open>R \<omega>_def \<omega> ns\<close> red_ast_bpl_def
      by (smt (verit, ccfv_threshold) rtranclp_trans)
  next
    case (RedSubFailure e')
    hence "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      by simp
    then show ?thesis using assms wf_rel_failure_elim
      using \<open>R \<omega>_def \<omega> ns\<close> by blast
  qed
next
  fix v \<omega>_def \<omega> ns
  assume "R \<omega>_def \<omega> ns" and
         "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t v" and
         "v \<noteq> VFailure"
  from this obtain val where "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t Val val"
    by (metis extended_val.exhaust)
  thus "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>3, Normal ns')"
  proof cases
    case (RedField a v')
    hence "(a, f) \<in> get_valid_locs \<omega>_def" 
      by (metis extended_val.distinct(1) if_SomeD)
    moreover have "VRef (Address a) \<noteq> VRef Null"    
      by simp
    ultimately show ?thesis using assms wf_rel_normal_elim RedField \<open>R \<omega>_def \<omega> ns\<close> rtranclp_trans red_ast_bpl_def
      by (smt (verit, ccfv_SIG))
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
\<close>

lemma unfolding_wf_rel:
  assumes 
        R_to_R': "\<And> \<omega>_def \<omega>_def' vs \<omega> ns. 
                      R \<omega>_def \<omega> ns \<Longrightarrow>
                      unfold_rel ctxt_vpr StateCons p vs pwrite \<omega>_def \<omega>_def' \<Longrightarrow>                      
                      \<exists>ns'. R' \<omega>_def' \<omega> ns' \<and>                             
                            red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns')" and
        R'_to_R: "\<And> \<omega>_def \<omega>_def' \<omega> ns ns'. R \<omega>_def \<omega> ns \<Longrightarrow> R' \<omega>_def' \<omega> ns' \<Longrightarrow> R \<omega>_def \<omega> ns'" and
        WfRelArgs: "exprs_wf_rel R' ctxt_vpr StateCons P ctxt xs \<gamma>1 \<gamma>2" and
        WfRel: "expr_wf_rel R' ctxt_vpr StateCons P ctxt ubody \<gamma>2 \<gamma>3"
      shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (Unfolding p xs ubody) \<gamma>1 \<gamma>3"
  oops
(*
proof (rule expr_wf_rel_intro)
  fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and
         "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Unfolding p xs ubody;\<omega>\<rangle> [\<Down>]\<^sub>t v" and
         "v = VFailure"

  hence RedFail:"ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Unfolding p xs ubody;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp
  from RedFail
  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>1, Normal ns) c'"
  proof cases
    case (RedUnfoldingDef vs \<omega>'_def)
    with R R_to_R' obtain ns' where R': "R' \<omega>'_def \<omega> ns'" and 
                                    RedBpl: "red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns')"
      by blast
    from RedUnfoldingDef wf_rel_failure_elim[OF WfRel R'] obtain c' where
      "snd c' = Failure" and "red_ast_bpl ctxt (\<gamma>'', Normal ns') c'"
      by blast
    with RedBpl show ?thesis
      by fastforce
  next
    case (RedSubFailure e)
    hence "e \<in> set xs" by simp
    \<comment>\<open>TODO: mismatch Viper and Boogie, Boogie evaluates from left-to-right. Resolve by proving
            that Boogie expression\<close>
    then show ?thesis oops
  qed
next
  fix v \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and
         "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Unfolding p xs ubody;\<omega>\<rangle> [\<Down>]\<^sub>t v" and
         "v \<noteq> VFailure" 
  from this obtain val where "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>Unfolding p xs ubody;\<omega>\<rangle> [\<Down>]\<^sub>t Val val"
    by (metis extended_val.exhaust)
  thus "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')"
  proof cases
    case (RedUnfoldingDef vs \<omega>'_def)
    with R R_to_R'  obtain ns' where R': "R' \<omega>'_def \<omega> ns'" and 
                                     RedBpl: "red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>'', Normal ns')"
      by blast
    from RedUnfoldingDef wf_rel_normal_elim[OF WfRel R'] obtain ns'' where
       R'_2: "R' \<omega>'_def \<omega> ns''" and "red_ast_bpl ctxt (\<gamma>'', Normal ns') (\<gamma>', Normal ns'')"
      by blast
    with RedBpl R'_to_R[OF R R'_2] show ?thesis
      by fastforce      
  qed
qed
*)


subsection \<open>Connecting semantic well-definedness relation with concrete Boogie statements\<close>

lemma wf_rel_bop_op_trivial: 
  assumes "bop \<notin> {IntDiv, PermDiv, ViperLang.Mod}"
  shows "wf_rel_bop_op R ctxt_vpr StateCons P ctxt e1 bop e2 \<gamma> \<gamma>"  
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
                        (\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> \<exists>i. red_expr_bpl ctxt e2_bpl ns (IntV i))" and
          ZeroRealE2BplWellTy: "bop = PermDiv \<Longrightarrow> zero = Lit (LReal 0) \<Longrightarrow> 
                        (\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> \<exists>r. red_expr_bpl ctxt e2_bpl ns (RealV r))"
        shows "wf_rel_bop_op R ctxt_vpr StateCons P ctxt e1 bop e2 (BigBlock None ((Assert (e2_bpl \<guillemotleft>Neq\<guillemotright> zero))#cs) str tr, cont) (BigBlock None cs str tr, cont)"
              (is "wf_rel_bop_op _ _ _ _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule wf_rel_intro)
  fix v \<omega>_def \<omega> ns
  assume R: "R \<omega>_def \<omega> ns" and "\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<and> ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2 \<and> (\<exists>v'. eval_binop v1 bop v2 = BinopNormal v')"
  from this obtain v1 v2 v' where Red2:"ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and EvalBinop: "eval_binop v1 bop v2 = BinopNormal v'"
    by auto
  hence NonZero:"v2 \<noteq> VInt(0) \<and> v2 \<noteq> VPerm(0)"
    using eval_binop_not_failure_2 Bop
    by blast
  from EvalBinop have IntOrPerm:"(\<exists>i. v2 = VInt i) \<or> (\<exists>p. v2 = VPerm p)" using eval_binop_div_mod_normal_types[OF Bop]
    by blast
  from Red2 obtain v2_bpl where RedBpl:"red_expr_bpl ctxt e2_bpl ns v2_bpl" and ValRel:"val_rel_vpr_bpl v2 = v2_bpl"
    using ExpRel exp_rel_vpr_bpl_def exp_rel_vb_single_def R
    by metis
  show "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns')"
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
      using Bop EvalBinop \<open>v2 = _\<close>
      by (metis binop_result.distinct(3) empty_iff eval_binop.simps(18) eval_binop.simps(2) eval_binop_div_mod_normal_types eval_perm_perm.simps(11) eval_perm_perm.simps(12) insert_iff)
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
  fix v \<omega>_def \<omega> ns
  assume R: "R \<omega>_def \<omega> ns" and "\<exists>v1 v2. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<and> ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2 \<and> (eval_binop v1 bop v2 = BinopOpFailure)"
  from this obtain v1 v2 where Red2:"ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and EvalBinop: "eval_binop v1 bop v2 = BinopOpFailure"
    by auto
  hence IntOrPerm:"v2 = VInt 0 \<or> v2 = VPerm 0"
    by (metis Bop eval_binop_failure_int eval_binop_failure_perm insert_iff)

  from Red2 obtain v2_bpl where RedBpl:"red_expr_bpl ctxt e2_bpl ns v2_bpl" and ValRel:"val_rel_vpr_bpl v2 = v2_bpl"
    using ExpRel exp_rel_vpr_bpl_def exp_rel_vb_single_def R
    by metis

  show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (?\<gamma>, Normal ns) c'"
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

text \<open>The following lemma expresses the well-definedness result provided by in an
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
   Rel2a: "expr_wf_rel (\<lambda>\<omega>_def \<omega> s. R \<omega>_def \<omega> s \<and> 
                                    (\<exists>b. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b) \<and> b \<noteq> b1 \<and>
                                         (\<exists> v2. eval_binop b bop v2 \<noteq> BinopTypeFailure))) 
                        ctxt_vpr StateCons P ctxt e2 
                        (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) els)) None, cont)
                        \<gamma>'" (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule expr_wf_rel_intro)
\<comment>\<open>Failure case\<close>
  fix v \<omega>_def \<omega> ns
  assume Rext:"?R_ext \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v = VFailure"
  hence E2Fail: "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by blast

  from Rext obtain v1 v2 where RedE1: "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and NotB1:"v1 \<noteq> b1" and
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

  thus "\<exists>c'. snd c' = Failure \<and> ?P c'"
    using \<open>snd c' = Failure\<close>
    by blast
next
\<comment>\<open>Normal case\<close>
  fix v \<omega>_def \<omega> ns
  assume Rext:"?R_ext \<omega>_def \<omega> ns" (is "?R \<and> ?Re1") and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t v" and "v \<noteq> VFailure"
  from this obtain val where E2Normal: "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val val"
    by (metis extended_val.exhaust)

  from Rext obtain v1 v2 where RedE1: "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and NotB1:"v1 \<noteq> b1" and
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
   from E2Normal obtain ns' where 
     Rns': "R \<omega>_def \<omega> ns'" and RedThn:"red_ast_bpl P ctxt (?\<gamma>'', Normal ns) (?\<gamma>', Normal ns')"
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

  thus "\<exists>ns'. (R \<omega>_def \<omega> ns' \<and> ?Re1) \<and> red_ast_bpl P ctxt (?\<gamma>, Normal ns) (?\<gamma>', Normal ns')"
    using Rns' Rext
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
   "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
                       (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, cont)
                       (empty_bigblock elseName, cont)" (is "wf_rel R _ _ _ _ ?\<gamma> ?\<gamma>'")
proof (rule wf_rel_intro)
\<comment>\<open>Normal case\<close>
  fix \<omega>_def \<omega> ns
  assume R:"R \<omega>_def \<omega> ns" and "ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1"

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

  show "\<exists>ns'. R \<omega>_def \<omega> ns' \<and> red_ast_bpl P ctxt (?\<gamma>,Normal ns) (?\<gamma>', Normal ns')"
    using R RedAst
    by auto

next
\<comment>\<open>Failure case (can never happen)\<close>
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
   "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
                       (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, KSeq bNext cont)
                       (bNext, cont)" (is "wf_rel R _ _ _ _ ?\<gamma> ?\<gamma>'")
proof -
  have *:"wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t (Val b1)) (\<lambda>_ _. False) P ctxt 
               (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl)  [empty_bigblock elseName])) None, KSeq bNext cont)
               (empty_bigblock elseName, KSeq bNext cont)"
    by (blast intro!: syn_lazy_bop_no_short_circuit_wf_rel assms)

  show ?thesis
    apply (rule wf_rel_extend_1)
     apply (rule *)
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
   Red2: "\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) 
            ((BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) [empty_bigblock elseName])) None, KSeq bNext cont), Normal ns3) \<and>
             R \<omega>_def \<omega> ns3"
           (is "\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) ((?b_if, ?cont_if), Normal ns3) \<and>
             R \<omega>_def \<omega> ns3")
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
  show "expr_wf_rel (\<lambda>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
     ctxt_vpr StateCons P ctxt e2 (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock elseName])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_short_circuit_wf_rel[OF Lazy])
    apply (insert Guard)
    by (auto intro: ExpRel WfRel)
next
  show "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock elseName])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_no_short_circuit_seq_wf_rel[OF Lazy])
      apply (insert Guard)
    by (auto intro: ExpRel)
qed

lemma syn_lazy_bop_wf_rel_2:
  assumes
   Lazy: "binop_lazy bop = Some (b1 :: 'a ValueAndBasicState.val, bResult)" and
   Rel1: "expr_wf_rel R (ctxt_vpr :: 'a total_context) StateCons P ctxt e1 \<gamma>0 \<gamma>2" and
   Red2: "\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) 
            ((BigBlock name [] (Some (ParsedIf (Some guard) (thnHd#thnTl) [empty_else_block])) None, KSeq bNext cont), Normal ns3) \<and>
             R \<omega>_def \<omega> ns3"
           (is "\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>2, Normal ns2) ((?b_if, ?cont_if), Normal ns3) \<and>
             R \<omega>_def \<omega> ns3") and
   ElseBlockEmpty: "is_empty_bigblock empty_else_block" and
   Guard: "bop \<in> {ViperLang.And, ViperLang.BImp} \<Longrightarrow> guard = e1_bpl" 
         "bop = ViperLang.Or \<Longrightarrow> guard = UnOp Not e1_bpl" and
   ExpRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   WfRel: "expr_wf_rel R ctxt_vpr StateCons P ctxt e2 (thnHd, (convert_list_to_cont thnTl (KSeq bNext cont))) \<gamma>3"
               (is "expr_wf_rel ?R_ext _ _ _ _ _ ?\<gamma>'' _") and
   Red3: "\<And>\<omega>_def \<omega> ns2. R \<omega>_def \<omega> ns2 \<Longrightarrow> \<exists>ns3. red_ast_bpl P ctxt (\<gamma>3, Normal ns2) ((bNext, cont), Normal ns3) \<and> R \<omega>_def \<omega> ns3"
   shows "expr_wf_rel R ctxt_vpr StateCons P ctxt (ViperLang.Binop e1 bop e2) \<gamma>0 (bNext, cont)"
proof (rule binop_lazy_expr_wf_rel[OF Lazy])
  show "expr_wf_rel R ctxt_vpr StateCons P ctxt e1 \<gamma>0 (?b_if, ?cont_if)"
    by (auto intro: wf_rel_extend_1 Rel1 Red2)
next                                                                             
  from ElseBlockEmpty obtain else_name where "empty_else_block = empty_bigblock else_name" 
    using is_empty_bigblock.elims(2) by auto
  have "expr_wf_rel (\<lambda>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
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
     (\<lambda>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<and> (\<exists>b. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b \<and> b \<noteq> b1 \<and> (\<exists>v2. eval_binop b bop v2 \<noteq> BinopTypeFailure)))
     ctxt_vpr StateCons P ctxt e2 (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_else_block])) None, KSeq bNext cont) (bNext, cont)"
    using \<open>empty_else_block = _\<close>
    by simp
next
  from ElseBlockEmpty obtain else_name where "empty_else_block = empty_bigblock else_name" 
    using is_empty_bigblock.elims(2) by auto
  have "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_bigblock else_name])) None, KSeq bNext cont) (bNext, cont)"
    apply (rule syn_lazy_bop_no_short_circuit_seq_wf_rel[OF Lazy])
      apply (insert Guard)
    by (auto intro: ExpRel)
  thus "wf_rel R (\<lambda>\<omega>_def \<omega>. ctxt_vpr, StateCons, Some \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val b1) (\<lambda>_ _. False) P ctxt
     (BigBlock name [] (Some (ParsedIf (Some guard) (thnHd # thnTl) [empty_else_block])) None, KSeq bNext cont) (bNext, cont)"
    using \<open>empty_else_block = _\<close>
    by simp
qed

method wf_rel_bop_op_trivial_tac =
        (rule wf_rel_bop_op_trivial, solves\<open>simp\<close>) \<comment>\<open>TODO: nontrivial case\<close>

\<comment>\<open>TODO: the following tactic only works for trivial well-definedness checks\<close>

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