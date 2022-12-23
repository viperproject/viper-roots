theory ExpProofGenTest
imports ExpRel ExprWfRel TotalSemProperties
begin

text \<open>
The goal is to generate proofs of Viper programs containing a single \<open>x := e\<close> statement. I will
pursue this goal in three phases:

  \<^item> Phase 1: \<open>e\<close> contains no lazy operations and is trivially well-defined
  \<^item> Phase 2: \<open>e\<close> is trivially well-defined
  \<^item> Phase 3: No restrictions on \<open>e\<close> other than general subset restriction
\<close>

(*
definition assert_rel :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> ViperLang.program \<Rightarrow> 'a total_context \<Rightarrow>  'a astcontext_bpl \<Rightarrow>
       viper_expr \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont)  \<Rightarrow> bool"
  where
   "assert_rel R Pr ctxt_vpr ctxt e_vpr \<gamma> \<gamma>' \<equiv> 
    \<forall> \<omega> ns res. R \<omega> ns \<longrightarrow> 
           red_exhale Pr ctxt_vpr \<omega> (Atomic (Pure e_vpr)) (get_m_total_full \<omega>) res \<longrightarrow>

           (res \<noteq> ExhaleFailure \<longrightarrow> \<comment>\<open>for general exhales would have to take resulting mask into account\<close>
               (\<exists>\<gamma>' ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega> ns')) \<and>
           (res = ExhaleFailure \<longrightarrow> 
              (\<exists>c'.  snd c' = Failure \<and>
                    red_ast_bpl ctxt (\<gamma>, Normal ns) c'))"
*)

text\<open> Points to think about:
  \<^item> backward vs. forward simulation (also tracking single Boogie state vs sets of Boogie states)
\<close>

definition stmt_rel :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                               ('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 
                                'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 
                                type_context \<Rightarrow> 'a astcontext_bpl \<Rightarrow>
                                ViperLang.stmt \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "stmt_rel R R' ctxt_vpr StateCons \<Lambda> ctxt stmt_vpr \<gamma> \<gamma>' \<equiv>
      \<forall> \<omega> ns res. R \<omega> ns \<longrightarrow> 
             red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> res \<longrightarrow>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                 (\<exists>ns'. (red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                (\<exists>c'. snd c' = Failure \<and>
                      red_ast_bpl ctxt (\<gamma>, Normal ns) c'))"

lemma stmt_rel_intro[case_names base step]:
  assumes 
  "\<And>\<omega> ns \<omega>'. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
          \<exists>ns'. (red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')" and
  "\<And>\<omega> ns.
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure \<Longrightarrow>
          \<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
  shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda> ctxt stmt_vpr \<gamma> \<gamma>'"
  using assms
  unfolding stmt_rel_def  
  by blast

lemma stmt_rel_normal_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>')"
    shows   "\<exists>ns'. (red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')"
  using assms
  unfolding stmt_rel_def
  by blast

lemma stmt_rel_failure_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure"
  shows "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
  using assms
  unfolding stmt_rel_def
  by blast

definition type_interp_rel_wf :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a vbpl_absval) absval_ty_fun  \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> bool"
  where "type_interp_rel_wf A_vpr A_bpl Trep \<equiv> 
    \<forall>v ty_vpr ty_bpl. get_type A_vpr v = ty_vpr \<longrightarrow>
                      vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl \<longrightarrow>
                      type_of_val A_bpl (val_rel_vpr_bpl v) = ty_bpl"

lemma type_interp_rel_wf_vbpl: 
  assumes "A_vpr = domain_type Trep"
    shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain d where "domain_translation Trep (A_vpr a) = Some d" and "ty_bpl = TCon (fst d) (snd d)"
      by fastforce
    hence "vbpl_absval_ty Trep (ADomainVal a) = d" using \<open>A_vpr = domain_type Trep\<close>
      by simp
    hence "type_of_vbpl_val Trep (AbsV (ADomainVal a)) = ty_bpl" using \<open>ty_bpl = _\<close>
      by simp
    thus ?thesis using VAbs
      by simp     
  qed (insert * **, auto)
qed

lemma type_interp_rel_wf_vbpl_no_domains:
  assumes "\<And> d. domain_translation Trep d = None"
  shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    fix contra
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain d where "domain_translation Trep (A_vpr a) = Some d"
      by fastforce
    with assms show contra 
      by simp
  qed (insert * **, auto)
qed

lemma assign_rel_simple:
  assumes R_def: (*"R2 = (\<lambda> \<omega> ns. state_rel Pr Trep Tr (econtext_bpl.truncate ctxt) (mask_var Tr) \<omega> \<omega> ns)"
                     "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> state_rel Pr Trep Tr (econtext_bpl.truncate ctxt) (mask_var Tr) \<omega> \<omega> ns)"*)
                   "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R2 \<omega> ns)" and
          VprTy: "\<Lambda>_vpr x_vpr = Some ty" and
          ExpWfRel: "expr_wf_rel R3 ctxt_vpr StateCons ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)" 
                    (is "expr_wf_rel R3 ctxt_vpr StateCons ctxt e_vpr \<gamma> (?b, cont)") and
          BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl" and
          TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl" and
                    \<comment>\<open>Key assignment property for R2\<close>
          RAssign:  "\<And> \<omega> ns v . R2 \<omega> ns \<Longrightarrow>
                           get_type (absval_interp_total ctxt_vpr) v = ty \<Longrightarrow>
                           type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl \<Longrightarrow>
                           R2 (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))" and
          TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep"
  and
          ExpRel: "exp_rel_vpr_bpl R3 ctxt_vpr (econtext_bpl.truncate ctxt) e_vpr e_bpl" 
          
        shows "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
               \<gamma>
               (BigBlock name cs str tr, cont)" (is "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma> ?\<gamma>'") 
proof (cases rule: stmt_rel_intro)
\<comment>\<open>normal case\<close>
  fix \<omega> ns \<omega>'
  assume R: "R2 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> (RNormal \<omega>')"

  show "\<exists>ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R2 \<omega>' ns'"
  proof -
    from RedVpr obtain v where RedEVpr: "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v)" and 
                                "\<omega>' = (update_var_total \<omega> x_vpr v)" and
                                vTyVpr: "get_type (absval_interp_total ctxt_vpr) v = ty"      
      apply (rule red_stmt_total.cases)
      using VprTy
      by auto

    from this obtain ns' where
        R':"R3 \<omega> \<omega> ns'" and
        RedBplWf:"red_ast_bpl ctxt (\<gamma>, Normal ns) ((?b, cont), Normal ns')"
      using R R_def wf_rel_normal_elim[OF ExpWfRel]
      by blast

    let ?v_bpl = "val_rel_vpr_bpl v"
    have RedEBpl:"red_expr_bpl (econtext_bpl.truncate ctxt) e_bpl ns' ?v_bpl"
      apply (rule exp_rel_vpr_bpl_elim_2[OF ExpRel])
      using R' RedEVpr R_def
      by fastforce

    have ValBplTy:"type_of_val (type_interp ctxt) ?v_bpl = instantiate [] ty_bpl"
      using vTyVpr TyRel TyRelWf
      unfolding type_interp_rel_wf_def
      by simp

    let ?ns'' = "update_var (var_context ctxt) ns' x_bpl ?v_bpl"

    have RedBpl: "red_ast_bpl ctxt ((?b, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal ?ns'')"
      apply (rule converse_rtranclp_into_rtranclp)
       apply rule
       apply rule
         apply (rule BplTy)
        apply (rule ValBplTy)
      using RedEBpl
      by auto

    moreover have "R3 \<omega>' \<omega>' ?ns''" 
      apply (subst \<open>\<omega>' = _\<close>)+
      using R_def RAssign R' vTyVpr ValBplTy 
      by auto

    ultimately show ?thesis 
      using RedBplWf R_def \<open>\<omega>' = _\<close>
      by (meson rtranclp_trans)
  qed
next
  \<comment>\<open>Failure case\<close>
  fix \<omega> ns 
  assume "R2 \<omega> ns" and 
         RedVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> RFailure"
  
  from RedVpr show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
  proof cases
  case (RedSubExpressionFailure e)
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp

  then show ?thesis 
    using  R_def \<open>R2 \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
    by blast
  qed
qed

text \<open>Relational rule for Viper assignment \<open>x := e_vpr\<close>\<close>
lemma assign_rel_simple_2:
  assumes R_def: "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R2 \<omega> ns)" and
          VprTy: "\<Lambda>_vpr x_vpr = Some ty" and
          ExpWfRel: "expr_wf_rel R3 ctxt_vpr StateCons ctxt e_vpr \<gamma> \<gamma>'" and
          ProgressToAssign: "\<And>\<omega>_def \<omega> ns2. R3 \<omega>_def \<omega> ns2 \<Longrightarrow> 
                          \<exists>ns3. red_ast_bpl ctxt (\<gamma>', Normal ns2) ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr, cont), Normal ns3) \<and> 
                                R3 \<omega>_def \<omega> ns3" and
          BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl" and
          TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl" and
                    \<comment>\<open>Key assignment property for R2\<close>
          RAssign:  "\<And> \<omega> ns v . R2 \<omega> ns \<Longrightarrow>
                           get_type (absval_interp_total ctxt_vpr) v = ty \<Longrightarrow>
                           type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl \<Longrightarrow>
                           R2 (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))" and
          TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep"
  and
          ExpRel: "exp_rel_vpr_bpl R3 ctxt_vpr (econtext_bpl.truncate ctxt) e_vpr e_bpl" 
          
        shows "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
               \<gamma>
               (BigBlock name cs str tr, cont)"
proof -  
  from ExpWfRel and ProgressToAssign 
  have *:"expr_wf_rel R3 ctxt_vpr StateCons ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)"
    using wf_rel_extend_1
    by blast
  show ?thesis
    apply (rule assign_rel_simple[OF R_def _ *])
    using assms
    by auto
qed

lemma stmt_rel_simple_propagate:
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt stmt_vpr \<gamma>0 \<gamma>2"  
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> (RNormal \<omega>')"

  from \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>ns'. red_ast_bpl ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using stmt_rel_normal_elim[OF assms(2)] RedVpr
    by (meson rtranclp_trans)
next
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> RFailure"

  from \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>0, Normal ns) c'"
    using stmt_rel_failure_elim[OF assms(2)] RedVpr
    by (meson rtranclp_trans)
qed

end