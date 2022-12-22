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
  \<^item> small-step vs big-step semantics
  \<^item> current version is non-compositional, since it does not give information to what the Boogie reduction
    reduces (generalization is not straightforward here, because of the Viper small-step reduction)
\<close>

definition stmt_rel_simple :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                               ('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 
                                'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 
                                type_context \<Rightarrow> 'a astcontext_bpl \<Rightarrow>
                                ViperLang.stmt \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "stmt_rel_simple R R' ctxt_vpr StateCons \<Lambda> ctxt stmt_vpr \<gamma> \<equiv>
      \<forall> \<omega> ns stmt'_vpr res. R \<omega> ns \<longrightarrow> 
             red_stmt_total_multi ctxt_vpr StateCons \<Lambda> (Inl stmt_vpr, RNormal \<omega>) (stmt'_vpr, res) \<longrightarrow>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                 \<comment>\<open>Since the target configuration \<gamma>' is existentially quantified, we cannot connect
                    this result to a subsequent Boogie statement.\<close> 
                 (\<exists>\<gamma>' ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')) \<and>
             (res = RFailure \<longrightarrow> 
                (\<exists>c'.  snd c' = Failure \<and>
                      red_ast_bpl ctxt (\<gamma>, Normal ns) c'))"

lemma stmt_rel_simple_intro[case_names base step]:
  assumes 
  "\<And>\<omega> ns stmt'_vpr \<omega>' res. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total_multi Pr \<Lambda> ctxt_vpr (Inl stmt_vpr, RNormal \<omega>) (stmt'_vpr, RNormal \<omega>') \<Longrightarrow>
          \<exists>\<gamma>' ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'" and
  "\<And>\<omega> ns stmt'_vpr res.
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total_multi Pr \<Lambda> ctxt_vpr (Inl stmt_vpr, RNormal \<omega>) (stmt'_vpr, RFailure) \<Longrightarrow>
          \<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
  shows "stmt_rel_simple R R' Pr \<Lambda> ctxt_vpr ctxt stmt_vpr \<gamma>"
  using assms
  unfolding stmt_rel_simple_def
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
          
  shows "stmt_rel_simple R2 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma>"  
proof (cases rule: stmt_rel_simple_intro)
\<comment>\<open>normal case\<close>
  fix \<omega> ns stmt'_vpr \<omega>' res
  assume R: "R2 \<omega> ns" and    
         RedVpr: "red_stmt_total_multi ctxt_vpr StateCons \<Lambda>_vpr (Inl (LocalAssign x_vpr e_vpr), RNormal \<omega>) (stmt'_vpr, RNormal \<omega>')"

  from RedVpr
  show "\<exists>\<gamma>' ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R2 \<omega>' ns'"
  proof (cases rule: converse_rtranclpE)
    case base
    hence "\<omega>' = \<omega>"
      by auto
    show ?thesis
      apply (rule exI)
      apply (rule exI[where ?x=ns])
      by (auto simp: \<open>\<omega>' = \<omega>\<close> R)
  next
    case (step y)    
    from this obtain stmt''_vpr \<omega>'' where "y = (stmt''_vpr, RNormal \<omega>'')"
      using red_stmt_total_multi_normal_source
      by (metis snd_conv surjective_pairing)

    from step(1) obtain v where RedEVpr: "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v)" and 
                                yEq: "y = (Inr (), RNormal (update_var_total \<omega> x_vpr v))" and
                                "\<omega>'' = (update_var_total \<omega> x_vpr v)" and
                                vTyVpr: "get_type (absval_interp_total ctxt_vpr) v = ty"
      apply (rule NormalSingleStep_case)
      apply (simp only: \<open>y = _\<close>)
      apply (rule red_stmt_total_single_set.cases)
      using VprTy
      by auto

    from this obtain ns' where
        R':"R3 \<omega> \<omega> ns'" and
        RedBplWf:"red_ast_bpl ctxt (\<gamma>, Normal ns) ((?b, cont), Normal ns')"
      using R R_def wf_rel_normal_elim[OF ExpWfRel]
      by blast

    let ?v_bpl = "val_rel_vpr_bpl v"
    let ?ns'' = "update_var (var_context ctxt) ns' x_bpl ?v_bpl"
    have RedEBpl:"red_expr_bpl (econtext_bpl.truncate ctxt) e_bpl ns' ?v_bpl"
      apply (rule exp_rel_vpr_bpl_elim_2[OF ExpRel])
      using R' RedEVpr R_def
      by fastforce

    have ValBplTy:"type_of_val (type_interp ctxt) ?v_bpl = instantiate [] ty_bpl"
      using vTyVpr TyRel TyRelWf
      unfolding type_interp_rel_wf_def
      by simp

    have "red_ast_bpl ctxt ((?b, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal ?ns'')"
      apply (rule converse_rtranclp_into_rtranclp)
       apply rule
       apply rule
         apply (rule BplTy)
        apply (rule ValBplTy)
      using RedEBpl
      by auto

    have "R3 \<omega>'' \<omega>'' ?ns''" 
      apply (subst \<open>\<omega>'' = _\<close>)+
      using R_def RAssign R' vTyVpr ValBplTy 
      by auto

    moreover from step(2) have "\<omega>' = (update_var_total \<omega> x_vpr v)"
      apply (subst (asm) yEq)
      using red_stmt_total_multi_final
      by blast

    ultimately show ?thesis 
      using RedBplWf R_def
      apply (simp only: \<open>\<omega>'' = _\<close>)
      by (meson \<open>red_ast_bpl ctxt ((BigBlock name (Assign x_bpl e_bpl # cs) str tr, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal (update_var (econtext_bpl.var_context ctxt) ns' x_bpl (val_rel_vpr_bpl v)))\<close> rtranclp_trans)
  qed
next
  \<comment>\<open>Failure case\<close>
  fix \<omega> ns stmt'_vpr res
  assume "R2 \<omega> ns" and 
         RedVpr:"red_stmt_total_multi ctxt_vpr StateCons \<Lambda>_vpr (Inl (LocalAssign x_vpr e_vpr), RNormal \<omega>) (stmt'_vpr, RFailure)"
  
  from RedVpr show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
  proof (cases rule: converse_rtranclpE)
    case base
    then show ?thesis by simp
  next
    case (step y)
    from step(1)
    show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl ctxt (\<gamma>, Normal ns) c'"
    proof cases
      case NormalSingleStep
      then show ?thesis 
      proof cases
        case (RedLocalAssign v ty)        
        then show ?thesis using red_stmt_total_multi_final step
          by blast
      next 
        case (RedSubExpressionFailure e)
        hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
          by simp

        then show ?thesis 
          using  R_def \<open>R2 \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
          by blast
      qed
    qed
  qed
qed

text \<open>Relational rule for Viper assignment \<open>x := e_vpr\<close>\<close>
lemma assign_rel_simple_2:
  assumes R_def: (*"R2 = (\<lambda> \<omega> ns. state_rel Pr Trep Tr (econtext_bpl.truncate ctxt) (mask_var Tr) \<omega> \<omega> ns)"
                     "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> state_rel Pr Trep Tr (econtext_bpl.truncate ctxt) (mask_var Tr) \<omega> \<omega> ns)"*)
                   "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R2 \<omega> ns)" and
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
          
        shows "stmt_rel_simple R2 R2 ctxt_vpr StateCons \<Lambda>_vpr ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma>"  
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
  assumes "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R'' \<omega> ns'" and
          "stmt_rel_simple R'' R' Pr ctxt_vpr \<Lambda>_vpr ctxt stmt_vpr \<gamma>'"
  shows "stmt_rel_simple R R' Pr ctxt_vpr \<Lambda>_vpr ctxt stmt_vpr \<gamma>"
  sorry

end