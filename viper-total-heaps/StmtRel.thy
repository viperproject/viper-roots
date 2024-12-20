theory StmtRel
imports ExpRel ExprWfRel InhaleRel ExhaleRel TotalSemProperties ViperBoogieTranslationInterface Simulation
begin

subsection \<open>Statement relation - general statement\<close>

text\<open> Points to think about:
  \<^item> backward vs. forward simulation (also tracking single Boogie state vs sets of Boogie states)
\<close>

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a stmt_result_total"

definition stmt_rel :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                               ('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 
                                'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 
                                type_context \<Rightarrow> ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
                                ViperLang.stmt \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>' \<equiv>
       rel_general R R' 
         (\<lambda> \<omega> \<omega>'. red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>'))
         (\<lambda> \<omega>. red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure)
         P ctxt \<gamma> \<gamma>'"
 
lemma stmt_rel_intro[case_names base step]:
  assumes 
  "\<And>\<omega> ns \<omega>'. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
          \<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')" and
  "\<And>\<omega> ns.
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure \<Longrightarrow>
          \<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'"
  using assms
  unfolding stmt_rel_def 
  by (auto intro: rel_intro)

lemma stmt_rel_intro_2:
  assumes 
  "\<And>\<omega> ns res. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> res \<Longrightarrow>
          rel_vpr_aux R' P ctxt \<gamma> \<gamma>' ns res"
shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'"
  using assms
  unfolding stmt_rel_def rel_vpr_aux_def 
  by (auto intro: rel_intro)

lemma stmt_rel_normal_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>')"
    shows   "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')"
  using assms
  unfolding stmt_rel_def
  by (auto elim: rel_success_elim)

lemma stmt_rel_failure_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure"
  shows "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  using assms 
  unfolding stmt_rel_def rel_general_def
  by blast

subsection \<open>Propagation experiments\<close>




subsection \<open>Propagation rules\<close>

lemma stmt_rel_propagate:
  assumes "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
    shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms rel_propagate_pre
  unfolding red_ast_bpl_rel_def stmt_rel_def 
  by metis

lemma stmt_rel_propagate_pre_2:
  assumes "red_ast_bpl_rel R0 R0 P ctxt \<gamma>0 \<gamma>1"
      and "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
    shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms rel_propagate_pre
  unfolding red_ast_bpl_rel_def stmt_rel_def 
  by metis

lemma stmt_rel_propagate_same_rel:
  assumes "red_ast_bpl_rel R R P ctxt \<gamma>0 \<gamma>1" and
          "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using stmt_rel_propagate assms
  by blast

lemma stmt_rel_propagate_2:
  assumes "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "red_ast_bpl_rel R1 R2 P ctxt \<gamma>1 \<gamma>2"
  shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms
  unfolding stmt_rel_def
  using rel_propagate_post
  by blast

lemma stmt_rel_propagate_3:
  assumes "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "red_ast_bpl_rel R1 R1 P ctxt \<gamma>1 \<gamma>2"
  shows "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms
  unfolding stmt_rel_def
  using rel_propagate_post
  by blast
  
lemma stmt_rel_propagate_2_same_rel:
  assumes "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "red_ast_bpl_rel R R P ctxt \<gamma>1 \<gamma>2"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms stmt_rel_propagate_2
  by blast

subsection \<open>Structural rules\<close>

lemma stmt_rel_seq:
  assumes "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt s1_vpr \<gamma>1 \<gamma>2" and
          "stmt_rel R2 R3 ctxt_vpr StateCons \<Lambda>_vpr P ctxt s2_vpr \<gamma>2 \<gamma>3"
  shows 
    "stmt_rel R1 R3 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Seq s1_vpr s2_vpr) \<gamma>1 \<gamma>3"  
  using assms
  unfolding stmt_rel_def
  apply (rule rel_general_comp)
  by (auto elim: red_stmt_total_inversion_thms)

lemma stmt_rel_seq_same_rel:
  assumes "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s1_vpr \<gamma>1 \<gamma>2" and
          "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s2_vpr \<gamma>2 \<gamma>3"
  shows 
    "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Seq s1_vpr s2_vpr) \<gamma>1 \<gamma>3"
  using assms stmt_rel_seq
  by blast

lemma stmt_rel_if:
  assumes \<comment>\<open>When invoking the wf_rel tactic, apply one of the wf_rel extension lemmas such that the 
            wf_rel tactic itself need not guarantee progress to the if block\<close>
     ExpWfRel:          
          "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt cond 
           \<gamma>1
           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)" and
     ExpRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt cond cond_bpl" and
     ThnRel: "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s_thn (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" and
     ElsRel: "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s_els (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)"
   shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (If cond s_thn s_els) \<gamma>1 (next, cont)"
  using wf_rel_general_1[OF ExpWfRel] ThnRel ElsRel
  unfolding stmt_rel_def    
proof (rule rel_general_cond)
  fix \<omega> \<omega>' ns
  assume "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.If cond s_thn s_els) \<omega> (RNormal \<omega>')"
  thus "((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       ( red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> R \<omega> ns \<and> red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_thn \<omega> (RNormal \<omega>') \<or>
       red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R \<omega> ns \<and> red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_els \<omega> (RNormal \<omega>'))"
    apply (cases)
    using exp_rel_vpr_bplD[OF ExpRel]
    apply (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(2))
    using exp_rel_vpr_bplD[OF ExpRel]
    by (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(2))
next
  fix \<omega> ns
  assume "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.If cond s_thn s_els) \<omega> RFailure"
  thus " ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
       ((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> R \<omega> ns \<and>
        red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_thn \<omega> RFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> R \<omega> ns \<and>
        red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_els \<omega> RFailure)"
    apply(cases)
      apply (insert exp_rel_vpr_bplD[OF ExpRel])
      apply (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(2))
     apply (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(2))
    apply simp
    by (metis option.discI red_pure_exps_total_singleton)
qed

text \<open>Skip relation\<close>

lemma stmt_rel_skip: "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.Skip) \<gamma> \<gamma>"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R2 \<omega> ns" and "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr Skip \<omega> res"
  hence "res = RNormal \<omega>"
    by (auto elim: RedSkip_case)

  thus "rel_vpr_aux R2 P ctxt \<gamma> \<gamma> ns res"    
    using \<open>R2 \<omega> ns\<close> red_ast_bpl_refl 
    by (blast intro: rel_vpr_aux_intro)
qed

subsection \<open>Variable assignment relation\<close>

lemma var_assign_rel:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "StateConsEnabled \<Longrightarrow> (\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>)"
      and VprTy: "\<Lambda>_vpr x_vpr = Some ty"
      and TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep"
      and EmptyRtype: "rtype_interp ctxt = []"
      and ExpWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)" 
                    (is "expr_wf_rel ?R_ext ctxt_vpr StateCons P ctxt e_vpr \<gamma> (?b, cont)")
      and BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl"
      and TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl"
                    \<comment>\<open>Key assignment property for R\<close>
      and RAssign:  "\<And> \<omega> ns v . R \<omega> ns \<Longrightarrow>
                           get_type (absval_interp_total ctxt_vpr) v = ty \<Longrightarrow>
                           type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl \<Longrightarrow>   
                           (StateConsEnabled \<Longrightarrow> StateCons (update_var_total \<omega> x_vpr v)) \<Longrightarrow>                       
                           R (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))"
      and ExpRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt e_vpr e_bpl"
          
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
           \<gamma>
           (BigBlock name cs str tr, cont)" (is "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma> ?\<gamma>'") 
proof (cases rule: stmt_rel_intro)
\<comment>\<open>Normal case\<close>
  fix \<omega> ns \<omega>'
  assume R: "R \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> (RNormal \<omega>')"

  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R \<omega>' ns'"
  proof -
    from RedVpr obtain v where RedEVpr: "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v)" and 
                                "\<omega>' = (update_var_total \<omega> x_vpr v)" and
                                vTyVpr: "get_type (absval_interp_total ctxt_vpr) v = ty"      
      apply (rule red_stmt_total.cases)
      using VprTy
      by auto

    from this obtain ns' where
        R':"?R_ext \<omega> \<omega> ns'" and
        RedBplWf:"red_ast_bpl P ctxt (\<gamma>, Normal ns) ((?b, cont), Normal ns')"
      using R wf_rel_normal_elim[OF ExpWfRel]
      by blast

    let ?v_bpl = "val_rel_vpr_bpl v"
    have RedEBpl:"red_expr_bpl ctxt e_bpl ns' ?v_bpl"
      using R' RedEVpr ExpRel
      by (fastforce dest: exp_rel_vpr_bplD)

    have ValBplTy:"type_of_val (type_interp ctxt) ?v_bpl = instantiate [] ty_bpl"
      using vTyVpr TyRel TyRelWf
      unfolding type_interp_rel_wf_def
      by simp

    let ?ns'' = "update_var (var_context ctxt) ns' x_bpl ?v_bpl"

    have RedBpl: "red_ast_bpl P ctxt ((?b, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal ?ns'')"
      apply (rule red_ast_bpl_one_simple_cmd)
       apply (rule Semantics.RedAssign)
        apply (rule BplTy)
      apply (simp add: EmptyRtype ValBplTy)      
      using RedEBpl
      by auto

    moreover have "?R_ext \<omega>' \<omega>' ?ns''" 
    proof -
      have "StateConsEnabled \<Longrightarrow> StateCons (update_var_total \<omega> x_vpr v)"
        using RedVpr Consistent WfConsistency \<open>R \<omega> ns\<close> \<open>\<omega>' = _\<close> total_consistency_red_stmt_preserve 
        by blast
      thus ?thesis
      apply (subst \<open>\<omega>' = _\<close>)+
      using RAssign R' vTyVpr ValBplTy 
      by auto
    qed

    ultimately show ?thesis 
      using RedBplWf \<open>\<omega>' = _\<close> red_ast_bpl_def
      by (metis (mono_tags, lifting) rtranclp_trans)
  qed
next
  \<comment>\<open>Failure case\<close>
  fix \<omega> ns 
  assume "R \<omega> ns" and 
         RedVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> RFailure"
  
  from RedVpr show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
  case (RedSubExpressionFailure)
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by (fastforce elim: red_pure_exps_total_singleton)

  then show ?thesis 
    using  \<open>R \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
    by blast
  qed
qed

lemma var_assign_rel_inst:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRel: "R = state_rel_def_same (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> (\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>)"
      and VprTy: "\<Lambda>_vpr x_vpr = Some ty"
      and TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep"
      and EmptyRtype: "rtype_interp ctxt = []"
      and ExpWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)" 
                    (is "expr_wf_rel ?R_ext ctxt_vpr StateCons P ctxt e_vpr \<gamma> (?b, cont)")
      and VarTr: "var_translation Tr x_vpr = Some x_bpl"
      and BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl"
      and TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl"
      and ExpRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt e_vpr e_bpl"          
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
           \<gamma>
           (BigBlock name cs str tr, cont)" (is "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma> ?\<gamma>'")
proof (rule var_assign_rel[OF WfConsistency])
  show "\<Lambda>_vpr x_vpr = Some ty"
    by (rule VprTy)
next
  show "vpr_to_bpl_ty Trep ty = Some ty_bpl"
    by (rule TyRel)
next
  show "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt e_vpr \<gamma> (BigBlock name (Assign x_bpl e_bpl # cs) str tr, cont)"
    by (rule ExpWfRel)
next
  fix \<omega> ns v
  assume "R \<omega> ns" 
     and "get_type (absval_interp_total ctxt_vpr) v = ty"
     and TypeOfValBpl: "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl"
     and ConsistentUpdState: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_var_total \<omega> x_vpr v)"

  note StateRelInst = \<open>R \<omega> ns\<close>[simplified StateRel]

  show "R (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))"
    unfolding StateRel
    apply (rule state_rel_store_update_2[OF StateRelInst])
    using assms TypeOfValBpl ConsistentUpdState
    by simp_all
next
  fix \<omega> ns
  assume "R \<omega> ns"
  thus "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>"
    using StateRel state_rel_consistent
    by blast
qed (insert assms, simp_all)

subsection \<open>Field assignment relation\<close>

definition field_assign_normal_premise
  where "field_assign_normal_premise ctxt StateCons e_r f e \<omega> addr v ty \<equiv> 
    ctxt, StateCons, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr)) \<and>
    (addr,f) \<in> get_writeable_locs \<omega> \<and>
    ctxt, StateCons, (Some \<omega>)  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<and>
    declared_fields (program_total ctxt) f = Some ty \<and>
    get_type (absval_interp_total ctxt) v = ty"

lemma field_assign_rel_general:
  assumes SubExpsWfRel: "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt [rcv_vpr,rhs_vpr] \<gamma> \<gamma>1"
      and WriteableLocRel: "wf_rel_fieldacc get_writeable_locs (rel_ext_eq R) (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>1 \<gamma>2"
      and UpdHeapRel: "rel_general R R (\<lambda>\<omega> \<omega>'. \<exists>\<tau>_vpr addr v. \<omega>' = update_hh_loc_total_full \<omega> (addr,f_vpr) v \<and>
                                                       field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v \<tau>_vpr) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  let ?Rext = "rel_ext_eq R"
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
  hence "?Rext \<omega> \<omega> ns" by simp

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> (RNormal \<omega>')"
  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
    proof cases
      case (RedFieldAssign addr v ty_vpr)
      hence "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) [rcv_vpr, rhs_vpr] \<omega> (Some [VRef (Address addr), v])"
        by (auto intro!: TotalExpressions.RedExpListCons TotalExpressions.RedExpListNil)

      from this obtain ns1 where
        "?Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
        using exprs_wf_rel_normal_elim[OF SubExpsWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
        by blast
      with RedFieldAssign obtain ns3 where "?Rext \<omega> \<omega> ns3" and RedNs3: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns3)" 
        using wf_rel_normal_elim[OF WriteableLocRel] red_ast_bpl_transitive
        by blast
      hence "R \<omega> ns3" 
        by simp
  
      have "field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v ty_vpr"
        using RedFieldAssign
        unfolding field_assign_normal_premise_def
        by fastforce
  
      with rel_success_elim[OF UpdHeapRel \<open>R \<omega> ns3\<close>] obtain ns4
        where "red_ast_bpl P ctxt (\<gamma>2, Normal ns3) (\<gamma>', Normal ns4) \<and> R \<omega>' ns4"
        unfolding \<open>\<omega>' = _\<close>
        by blast
  
      thus ?thesis
        using RedNs3 red_ast_bpl_transitive
        by blast     
  qed
next
  let ?Rext = "rel_ext_eq R"
  fix \<omega> ns 
  assume "R \<omega> ns"
  hence "?Rext \<omega> \<omega> ns" by simp
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
    case (RedFieldAssignFailure r v)
    hence "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) [rcv_vpr, rhs_vpr] \<omega> (Some [VRef r, v])"
      by (auto intro!: TotalExpressions.RedExpListCons TotalExpressions.RedExpListNil)
      from this obtain ns1 where
        "?Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
        using exprs_wf_rel_normal_elim[OF SubExpsWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
        by blast   
    with RedFieldAssignFailure obtain \<gamma>' where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
      using wf_rel_failure_elim[OF WriteableLocRel \<open>?Rext \<omega> \<omega> ns1\<close>] red_ast_bpl_transitive
      by (metis (no_types, opaque_lifting) ref.exhaust ref.sel snd_conv surj_pair)
    thus ?thesis
      by (meson snd_conv)
  next
    case RedSubExpressionFailure
    hence RedSubExpFailureAux: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) [rcv_vpr, rhs_vpr] \<omega> None"
      by simp
    thus ?thesis
      using exprs_wf_rel_failure_elim[OF SubExpsWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
      by blast
  qed
qed

lemma field_assign_rel_general_2:
  assumes RcvWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1"
      and RhsWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2"
      and WriteableLocRel: "wf_rel_fieldacc get_writeable_locs (rel_ext_eq R) (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 \<gamma>3"
      and UpdHeapRel: "rel_general R R (\<lambda>\<omega> \<omega>'. \<exists>\<tau>_vpr addr v. \<omega>' = update_hh_loc_total_full \<omega> (addr,f_vpr) v \<and>
                                                       field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v \<tau>_vpr) (\<lambda>_. False) P ctxt \<gamma>3 \<gamma>'"
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) \<gamma> \<gamma>'"
  apply (rule field_assign_rel_general[OF _ WriteableLocRel UpdHeapRel])
  apply (rule exprs_wf_rel_alt_implies_exprs_wf_rel)
  using RcvWfRel RhsWfRel
  by (auto simp del: Product_Type.split_paired_Ex)

lemma field_assign_rel:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "StateConsEnabled \<Longrightarrow> (\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>)"
      and HeapUpdWf: "heap_update_wf TyRep ctxt heap_upd_bpl"
      and DomainTypeEq: "domain_type TyRep = absval_interp_total ctxt_vpr"
      and "type_interp ctxt = vbpl_absval_ty TyRep"
      and RcvWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1"
      and RhsWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2"
      and WriteableLocRel: "wf_rel_fieldacc get_writeable_locs (rel_ext_eq R) (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)" 
      and HeapUpdateBpl: "h_upd_bpl = heap_upd_bpl (Lang.Var h_bpl) rcv_bpl (Lang.Var f_bpl) rhs_bpl [\<tau>_field_bpl, \<tau>_bpl]"
      and DeclaredFieldsSome: "declared_fields (program_total ctxt_vpr) f_vpr = Some \<tau>_vpr \<and> vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl"
      and RcvRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt rcv_vpr rcv_bpl"
      and RhsRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt rhs_vpr rhs_bpl"

      \<comment>\<open>Key field assignment property for R\<close>
      and RFieldAssign:  "\<And> \<omega> ns hb addr v . R \<omega> ns \<Longrightarrow>
                     get_type (domain_type TyRep) v = \<tau>_vpr \<Longrightarrow>
                     (StateConsEnabled \<Longrightarrow> StateCons (update_hh_loc_total_full \<omega> (addr,f_vpr) v)) \<Longrightarrow>
                     (\<exists>hb f_bpl_val. 
                       lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep)) \<and>
                       lookup_var (var_context ctxt) ns h_bpl = Some (AbsV (AHeap hb)) \<and>
                       vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
                       lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
                       field_ty_fun_opt TyRep f_bpl_val = Some (TFieldId TyRep, [\<tau>_field_bpl, \<tau>_bpl]) \<and>
                       R (update_hh_loc_total_full \<omega> (addr,f_vpr) v)
                         (update_var (var_context ctxt) ns h_bpl
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         ))"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
         \<gamma>
         (BigBlock name cs str tr, cont)"   
proof (rule field_assign_rel_general_2[OF RcvWfRel RhsWfRel WriteableLocRel])
  show "rel_general R R
        (\<lambda>\<omega> \<omega>'. \<exists>\<tau>_vpr addr v. \<omega>' = update_hh_loc_total_full \<omega> (addr, f_vpr) v \<and> field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v \<tau>_vpr) (\<lambda>_. False)
        P ctxt (BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont) (BigBlock name cs str tr, cont)"
  proof (rule rel_intro_no_fail)
    let ?Rext = "rel_ext_eq R"
    fix \<omega> ns \<omega>'
    assume "R \<omega> ns"
       and "\<exists>\<tau>_vpr addr v. \<omega>' = update_hh_loc_total_full \<omega> (addr, f_vpr) v \<and> field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v \<tau>_vpr"

    from this obtain \<tau>_vpr addr v
      where "\<omega>' = update_hh_loc_total_full \<omega> (addr, f_vpr) v"
        and FieldPremise:"field_assign_normal_premise ctxt_vpr StateCons rcv_vpr f_vpr rhs_vpr \<omega> addr v \<tau>_vpr"
      by auto

    from \<open>R \<omega> ns\<close> have "?Rext \<omega> \<omega> ns"
      by simp
   
    note FieldPremiseSimp = FieldPremise[simplified  field_assign_normal_premise_def]

    have RedStmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> (RNormal \<omega>')"
      unfolding \<open>\<omega>' = _\<close>
      apply (rule RedFieldAssign)
      using FieldPremiseSimp
      by auto

   moreover have NewValTypeBpl: "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
     using vpr_to_bpl_val_type FieldPremiseSimp
           \<open>domain_type _ = _\<close> DeclaredFieldsSome
     by fastforce

   moreover from RedStmt have "StateConsEnabled \<Longrightarrow> StateCons \<omega>'"
     using total_consistency_red_stmt_preserve[OF WfConsistency] Consistent[OF _ \<open>R \<omega> ns\<close>]
     by simp

   moreover from RedFieldAssign DomainTypeEq have "get_type (domain_type TyRep) v = \<tau>_vpr"
     using DeclaredFieldsSome FieldPremiseSimp 
     by presburger

   ultimately obtain hb f_bpl_val
     where 
           LookupTyHeapBpl: "lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep))" and
           LookupHeapVarBpl: "lookup_var (var_context ctxt) ns  h_bpl = Some (AbsV (AHeap hb))" and
           HeapWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
           LookupFieldVarBpl: "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val))" and           
           FieldTyBpl: "field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [\<tau>_field_bpl, \<tau>_bpl])" and
           "R \<omega>'
                   (update_var (var_context ctxt) ns h_bpl
                   (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
             )" (is "R _ ?ns_upd")
     using RFieldAssign[OF \<open>R \<omega> ns\<close>] \<open>\<omega>' = _\<close> FieldPremiseSimp DeclaredFieldsSome
     by fastforce

   from RcvRel have RedRcvBpl: "red_expr_bpl ctxt rcv_bpl ns (AbsV (ARef (Address addr)))"
     using \<open>?Rext \<omega> \<omega> ns\<close>  FieldPremiseSimp exp_rel_vpr_bpl_elim
     by (metis (mono_tags, lifting) val_rel_vpr_bpl.simps(3))

   from RhsRel have RedRhsBpl: "red_expr_bpl ctxt rhs_bpl ns (val_rel_vpr_bpl v)" 
     using \<open>?Rext \<omega> \<omega> ns\<close>  FieldPremiseSimp exp_rel_vpr_bpl_elim
     by (metis (mono_tags, lifting))

   from HeapUpdWf have 
      RedHeapUpdBpl:
     "red_expr_bpl ctxt (heap_upd_bpl (Lang.Var h_bpl) rcv_bpl (Lang.Var f_bpl) rhs_bpl [\<tau>_field_bpl, \<tau>_bpl])
                             ns (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))"
     apply (rule heap_update_wf_apply)
     using  Semantics.RedVar[OF LookupHeapVarBpl]
           apply simp
          apply (rule HeapWellTyBpl)
         apply (rule RedRcvBpl)
     using Semantics.RedVar[OF LookupFieldVarBpl]
        apply simp
       apply (rule FieldTyBpl)
      apply (rule RedRhsBpl)
     apply (simp add: NewValTypeBpl)
     done

   have HeapUpdWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, [])"
     apply (rule heap_upd_ty_preserved[OF HeapWellTyBpl FieldTyBpl])
     by (simp add: NewValTypeBpl)

   have "red_ast_bpl P ctxt 
           ((BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont), Normal ns) 
           ((BigBlock name cs str tr, cont), Normal ?ns_upd)"
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule Semantics.RedAssign)
       apply (fastforce intro!: LookupTyHeapBpl)
     using HeapUpdWellTyBpl \<open>type_interp ctxt = _\<close>
      apply simp
     by (fastforce intro: RedHeapUpdBpl simp: \<open>h_upd_bpl = _\<close>)
   thus " \<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), Normal ns') \<and> R \<omega>' ns'"
     using \<open>R \<omega>' ?ns_upd\<close>
     by blast  
 qed
qed

text \<open>Version of generic field assignment relation rule where state relation is instantiated\<close>

lemma field_assign_rel_inst:
  assumes WfTyRep: "wf_ty_repr_bpl TyRep"
      and WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and RStateRel: "R = state_rel_def_same (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt"
      and HeapVarDefSame: "heap_var_def Tr = heap_var Tr"
      and "domain_type TyRep = absval_interp_total ctxt_vpr"
      and "type_interp ctxt = vbpl_absval_ty TyRep"
      and HeapUpdWf: "heap_update_wf TyRep ctxt heap_upd_bpl"
      and RcvWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1"
      and RhsWfRel: "expr_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2"
      and WriteableLocRel: "wf_rel_fieldacc get_writeable_locs (rel_ext_eq R) (rel_ext_eq R) ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)"
                   "h_bpl = heap_var Tr"
      and HeapUpdateBpl: "h_upd_bpl = heap_upd_bpl (Lang.Var h_bpl) rcv_bpl (Lang.Var f_bpl) rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]"
      and RcvRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt rcv_vpr rcv_bpl"
      and FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr (Lang.Var f_bpl) \<tau>_bpl"
      and RhsRel: "exp_rel_vpr_bpl (rel_ext_eq R) ctxt_vpr ctxt rhs_vpr rhs_bpl"
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
            \<gamma> (BigBlock name cs str tr, cont)"
proof (rule field_assign_rel[OF WfConsistency, where ?\<tau>_vpr = "the (declared_fields (program_total ctxt_vpr) f_vpr)"])
  let ?\<tau>_vpr = "the (declared_fields (program_total ctxt_vpr) f_vpr)"

  from FieldRelSingle have
          FieldLookup: "declared_fields (program_total ctxt_vpr) f_vpr = Some ?\<tau>_vpr"
      and TyTranslation: "vpr_to_bpl_ty TyRep ?\<tau>_vpr = Some \<tau>_bpl"
      and FieldTranslation: "field_translation Tr f_vpr = Some f_bpl"
    by (auto elim: field_rel_single_elim)

  thus "declared_fields (program_total ctxt_vpr) f_vpr = Some ?\<tau>_vpr \<and> vpr_to_bpl_ty TyRep (the (declared_fields (program_total ctxt_vpr) f_vpr)) = Some \<tau>_bpl"
    by simp

  fix \<omega> ns hb addr v
  assume "R \<omega> ns"
     and NewValVprTy: "get_type (domain_type TyRep) v = ?\<tau>_vpr"
     and ConsistentUpdState: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_hh_loc_total_full \<omega> (addr,f_vpr) v)"

  from \<open>R \<omega> ns\<close> have StateRelInst: "state_rel_def_same (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt \<omega> ns"
    by (simp add: RStateRel)

  let ?\<omega>' = "(update_hh_loc_total_full \<omega> (addr,f_vpr) v)"
  let ?ns' = "\<lambda>f_bpl_val. (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         )"      

  from state_rel_heap_update_2_ext[OF WfTyRep StateRelInst _ ConsistentUpdState ConsistentUpdState  FieldLookup FieldTranslation TyTranslation NewValVprTy]
  obtain hb f_bpl_val where
    "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))"
    "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val))"
    "field_ty_fun_opt TyRep f_bpl_val = Some (TFieldId TyRep, [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])" and
    StateRelInstUpd: "state_rel_def_same (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt ?\<omega>'
     (update_var (var_context ctxt) ns (heap_var Tr) (AbsV (AHeap (hb((Address addr, f_bpl_val) \<mapsto> val_rel_vpr_bpl v)))))"
    using HeapVarDefSame
    by fastforce

  thus "(\<exists>hb f_bpl_val. lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep)) \<and> 
                        lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
                        vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
                        lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
                        field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<and>
                        R ?\<omega>' 
                         (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         ))"
    using state_rel0_heap_var_rel[OF state_rel_state_rel0[OF StateRelInst]]
          state_rel0_heap_var_rel[OF state_rel_state_rel0[OF StateRelInstUpd]]
          RStateRel \<open>h_bpl = _\<close> 
    unfolding heap_var_rel_def
    by auto
next
  fix \<omega> ns
  assume "R \<omega> ns"
  thus "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>"
    using RStateRel state_rel_consistent
    by blast
qed (insert assms, simp_all)

subsection \<open>Inhale statement relation\<close>

lemma inhale_stmt_rel:
  assumes R_to_R': "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> R' \<omega> ns"
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega>" 
      and InhRel: "inhale_rel R' Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale A) \<gamma> \<gamma>'"
  apply (rule stmt_rel_intro)
  using inhale_rel_normal_elim[OF InhRel R_to_R'] inhale_rel_failure_elim[OF InhRel R_to_R'] InvHolds
  by (auto elim: RedInhale_case)

text \<open>The following two lemmas should have the same number of premises such that the same tactic applies.\<close>
lemma inhale_stmt_rel_no_inv:
  assumes True \<comment>\<open>to have some number of premises as framing inv case\<close>
      and True \<comment>\<open>to have some number of premises as framing inv case\<close>
      and InhRel: "inhale_rel R (\<lambda>_ _. True) ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale A) \<gamma> \<gamma>'"
  apply (rule stmt_rel_intro)
  using inhale_rel_normal_elim[OF InhRel] inhale_rel_failure_elim[OF InhRel] 
  by (auto elim: RedInhale_case)

lemma inhale_stmt_rel_inst_framing_inv:
  assumes StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> assertion_framing_state ctxt_vpr StateCons A \<omega>" 
      and InhRel: "inhale_rel (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) (assertion_framing_state ctxt_vpr StateCons) ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
    shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale A) \<gamma> \<gamma>'"
  using assms
  by (rule inhale_stmt_rel) simp_all

subsection \<open>Exhale statement relation\<close>

lemma exhale_stmt_rel:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      \<comment>\<open>The following premise shows the advantage of allowing different input and output relations for
         \<^term>\<open>exhale_rel\<close>. It allows abstracting over any potential setup code that is required for 
         encoding an exhale. Note that if we only allowed the same input and output relation, then
         one would need an additional premise that allows setting up the state. This would not only add
         clutter but also would reduce expressivity because the rule would force an encoding to
         always set up the state before continuing. As a result, one would not be able to, for example,
         justify the encoding \<open>if(*) { exhale A; assume false}\<close>.\<close>
      and ExhaleRel: "exhale_rel (rel_ext_eq R) Rexh Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      and UpdHavoc: "rel_general (uncurry Rexh) (\<lambda>\<omega> ns. R_out (snd \<omega>) ns) 
               (\<lambda>\<omega> \<omega>'. \<comment>\<open>the current evaluation state was reached by exhaling A from the current well-definedness state\<close>
                       red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and> 
                       \<comment>\<open>the updated state is a havoc of the current evaluation state\<close>
                       snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0}) \<and>
                       StateCons (snd \<omega>')
                ) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R R_out ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and RedExhale: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> (RNormal \<omega>')"
  hence "StateCons \<omega>'"
    using Consistent[OF \<open>R \<omega> ns\<close>] WfConsistency total_consistency_red_stmt_preserve
    by blast

  from RedExhale show "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> (RNormal \<omega>') \<Longrightarrow> 
                        \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R_out \<omega>' ns'"
  proof cases
    case (RedExhale \<omega>_exh)
    with exhale_rel_normal_elim[OF ExhaleRel] \<open>R \<omega> ns\<close> obtain ns2 where 
      "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)" and "Rexh \<omega> \<omega>_exh ns2"
      using InvHolds[OF \<open>R \<omega> ns\<close>]
      by blast
      
    moreover from rel_success_elim[OF UpdHavoc, where ?\<omega> = "(\<omega>,\<omega>_exh)" and ?\<omega>'="(\<omega>',\<omega>')"] RedExhale \<open>Rexh \<omega> \<omega>_exh ns2\<close> \<open>StateCons \<omega>'\<close> 
    obtain ns3 where
      "red_ast_bpl P ctxt (\<gamma>2, Normal ns2) (\<gamma>', Normal ns3)" and "R_out \<omega>' ns3"      
      by auto     
    ultimately show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R_out \<omega>' ns'"
    using red_ast_bpl_transitive
    by blast
  qed
next
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" 

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
    case RedExhaleFailure
    with exhale_rel_failure_elim[OF ExhaleRel] \<open>R \<omega> ns\<close> show ?thesis
      using InvHolds[OF \<open>R \<omega> ns\<close>]
      by fastforce
  qed (simp)
qed

text \<open>The following theorem is the same as exhale_stmt_rel except that Rext has been instantiated.
      It seems cumbersome to instantiate Rext properly during the proof generation (with a naive approach
      Isabelle picks a version that ignores the well-definedness state)\<close>

lemma exhale_stmt_rel_inst:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"    
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      and ExhRel: "exhale_rel (rel_ext_eq R) (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt) Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
      and UpdHavoc: "rel_general (uncurry (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt)) (\<lambda>\<omega> ns. R_out (snd \<omega>) ns) 
               (\<lambda>\<omega> \<omega>'. \<comment>\<open>the current evaluation state was reached by exhaling A from the current well-definedness state\<close>
                       red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and> 
                       \<comment>\<open>the updated state is a havoc of the current evaluation state\<close>
                       snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0}) \<and>
                       StateCons (snd \<omega>')
                ) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R R_out ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
proof (rule exhale_stmt_rel[OF WfConsistency])
  show "exhale_rel (rel_ext_eq R) (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt) Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
    by (rule ExhRel)
qed (insert assms, auto) 

text \<open>The output relation could be strengthened here, but this lemma is still useful in cases where the output relation
is irrelevant (such as when exhaling the postcondition, since there is no code after that)\<close>

lemma exhale_true_stmt_rel:
  shows "stmt_rel R (\<lambda>_ _. True) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale (Atomic (Pure (ELit (ViperLang.LBool True))))) \<gamma> \<gamma>"
  apply (rule stmt_rel_intro)
  using red_ast_bpl_refl
   apply blast
  apply (erule RedExhale_case)
    apply simp
  apply (erule ExhPure_case)
  by (auto elim: red_pure_exp_total_elims exh_if_total.elims)

lemma exhale_true_stmt_rel_2:
  assumes "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> R' \<omega> ns"
  shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale (Atomic (Pure (ELit (ViperLang.LBool True))))) \<gamma> \<gamma>"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" 
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (Atomic (Pure (ELit (ViperLang.lit.LBool True))))) \<omega> (RNormal \<omega>')"

  hence "\<omega> = \<omega>'"
  proof (rule RedExhale_case)
    fix \<omega>_exh \<omega>''
    assume RNormalEq: "RNormal \<omega>' = RNormal \<omega>''"
       and RedExh: "red_exhale ctxt_vpr StateCons \<omega> (Atomic (Pure (ELit (ViperLang.lit.LBool True)))) \<omega> (RNormal \<omega>_exh)"
       and HavocState:"\<omega>'' \<in> havoc_locs_state ctxt_vpr \<omega>_exh
           {loc. pnone < get_mh_total (get_total_full \<omega>) loc \<and> get_mh_total (get_total_full \<omega>_exh) loc = pnone}"

    from RedExh have "\<omega> = \<omega>_exh"
      using exhale_pure_normal_same
      by fastforce      

    with HavocState have "\<omega>'' = \<omega>"
      using havoc_locs_state_empty
      by (metis (mono_tags, lifting) empty_Collect_eq less_imp_neq)

    thus "\<omega> = \<omega>'"
      using RNormalEq
      by auto
  qed simp_all

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns') \<and> R' \<omega>' ns'"
    using assms \<open>R \<omega> ns\<close> red_ast_bpl_refl
    by fast
next
  fix \<omega> ns
  assume "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (Atomic (Pure (ELit (ViperLang.lit.LBool True))))) \<omega> RFailure"
  hence False
    apply cases
     apply (erule ExhPure_case)
      apply (metis TotalExpressions.RedLit_case ValueAndBasicState.val.inject(2) exh_if_total_failure extended_val.inject val_of_lit.simps(1))
     apply (erule TotalExpressions.RedLit_case)
     apply blast
    apply simp
    done

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
    by simp
qed

text \<open>The following lemma and the next one must have the same number and kind of premises, since currently a single 
      tactic deals with the premises.\<close>
lemma exhale_stmt_rel_inst_no_inv:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> True" \<comment>\<open>not required, but makes proof generation uniform (same number of premises for each case)\<close>
      and "exhale_rel (rel_ext_eq R) (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt) (\<lambda>_ _ _. True) ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"

      and UpdHavoc: "rel_general (uncurry (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt)) (\<lambda>\<omega> ns. R (snd \<omega>) ns) 
               (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and> 
                       snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0}) \<and>
                       StateCons (snd \<omega>')
                ) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
  using assms
  by (rule exhale_stmt_rel_inst)

lemma exhale_stmt_rel_inst_framing_inv:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRelAndConsistent: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns \<and> StateCons \<omega>"
      and InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> framing_exh ctxt_vpr StateCons A \<omega> \<omega>"
      and ExhRel: "exhale_rel (rel_ext_eq R) (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt) (framing_exh ctxt_vpr StateCons) ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
      and UpdHavoc: "rel_general (uncurry (state_rel Pr StateCons TyRep Tr' AuxPred' ctxt)) (\<lambda>\<omega> ns. (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) (snd \<omega>) ns) 
               (\<lambda>\<omega> \<omega>'. red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and> 
                       snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0}) \<and>
                       StateCons (snd \<omega>')
                ) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
  apply (rule exhale_stmt_rel_inst[OF WfConsistency _ _ ExhRel UpdHavoc])
  using assms
  by auto

lemma exhale_stmt_rel_finish:
  assumes StateRel: "state_rel_def_same Pr StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred ctxt \<omega> ns" and
          CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
          WfTyRepr: "wf_ty_repr_bpl TyRep" and
          ProgramTotal: "Pr = program_total ctxt_vpr" and
          DomainType:  "domain_type TyRep = absval_interp_total ctxt_vpr" and
          HeapWellDefSame: "heap_var Tr = heap_var_def Tr" and 
          "id_on_known_locs_name = FunMap FIdenticalOnKnownLocs" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          "StateCons \<omega>'" and
          "\<omega>' \<in> havoc_locs_state ctxt_vpr \<omega> ({loc. get_mh_total_full (\<omega>0 ) loc > 0 \<and> get_mh_total_full \<omega> loc = 0})" and
          "hvar = heap_var Tr" and
          "mvar = mask_var Tr" and
          LookupDeclExhaleHeap: "lookup_var_decl (var_context ctxt) hvar_exh = Some (TConSingle (THeapId TyRep), None)" and
          ExhaleHeapFresh: "hvar_exh \<notin> ({heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"                           
  shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Havoc hvar_exh # 
                                                   Assume (FunExp id_on_known_locs_name [] [Var hvar, Var hvar_exh, Var mvar]) # 
                                                   Assign hvar (Var hvar_exh) #
                                                   cs) str tr, cont), Normal ns)
                             ((BigBlock name cs str tr, cont), Normal ns') \<and>
               state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega>' ns'" (is "\<exists>ns'. ?red ns' \<and> ?rel ns'")
proof -
  from state_rel_heap_var_rel[OF StateRel]
  obtain hb where   LookupHeapVarTy: "lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
                    LookupHeapVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and  
                    HeapVarWellTy: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
                    HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb" and
                    HeapVprWellTy: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
      unfolding heap_var_rel_def
      by blast

  from state_rel_mask_var_rel[OF StateRel]
  obtain mb where LookupMaskVar: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding mask_var_rel_def 
    by blast

  from state_rel_field_rel[OF StateRel] 
  have "inj_on (field_translation Tr) (dom (field_translation Tr))"
    unfolding field_rel_def
    by blast 

  from this obtain hb' where *: "heap_rel (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>') hb'" and
                   **: "vbpl_absval_ty_opt TyRep (AHeap hb') = Some (THeapId TyRep, [])"
    using  construct_bpl_heap_from_vpr_heap_correct[OF WfTyRepr havoc_locs_state_well_typed_heap[OF \<open>\<omega>' \<in> _\<close>] DomainType]                
    by blast
                                          
  \<comment>\<open>We derive a heap which coincides with \<^term>\<open>hb'\<close> on the locations related to Viper locations
     and matches \<^term>\<open>hb\<close> on all other locations. This approach allows one to have strictly positive
     permissions at the Boogie level for locations that have no Viper counterpart. Alternatively,
     one could enforce in the state relation that that permission amount must be 0 for locations without
     a Viper counterpart (but then one would have to also prove that property when establishing the
     state relation). \<close>

  obtain hb'' where 
            NewHeapRel: "heap_rel (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>') hb''" and
            NewHeapWellTy: "vbpl_absval_ty_opt TyRep (AHeap hb'') = Some (THeapId TyRep, [])" and
            NewHeapProperty:
                "\<forall> loc_bpl. loc_bpl \<notin> (vpr_heap_locations_bpl (program_total ctxt_vpr) (field_translation Tr) ) \<longrightarrow> 
                                                     hb'' loc_bpl = hb loc_bpl"
    using heap_rel_stable_2_well_typed[OF * ** HeapVarWellTy]
    by blast   

  have IdOnKnownCondNormalField: "\<forall>r f t. 0 < mb (r, NormalField f t) \<longrightarrow> hb (r, NormalField f t) = hb'' (r, NormalField f t)"
  proof clarify
    fix r f t 
    assume PermPos: "0 < mb (r, (NormalField f t))"    

    show "hb (r, NormalField f t) = hb'' (r, NormalField f t)"

     \<comment>\<open>Need to put the type \<^typ>\<open>(ref \<times> 'a vb_field) set\<close> explicitly here, otherwise the proof does not work
       (most likely due to the type parameter).\<close>
    proof (cases "(r, NormalField f t) \<in> (vpr_heap_locations_bpl Pr (field_translation Tr)  :: (ref \<times> 'a vb_field) set)")
      case True
      from this obtain heap_loc where
         HeapLocProperties:
         "r = Address (fst heap_loc)"
         "declared_fields Pr (snd heap_loc) = Some t"
         "(field_translation Tr) (snd heap_loc) = Some f"
        unfolding vpr_heap_locations_bpl_def
        by blast

      hence "mb (r, (NormalField f t)) = Rep_preal (get_mh_total_full \<omega> heap_loc)"
        using MaskRel
        unfolding mask_rel_def
        by blast
      hence "get_mh_total_full \<omega> heap_loc \<noteq> pnone"
        using PermPos zero_preal.rep_eq by fastforce

      hence "get_hh_total_full \<omega> heap_loc = get_hh_total_full \<omega>' heap_loc"
        using \<open>\<omega>' \<in> _\<close> 
        unfolding havoc_locs_state_def havoc_locs_heap_def
        by fastforce

      then show ?thesis 
        using HeapRel NewHeapRel HeapLocProperties ProgramTotal
        unfolding heap_rel_def
        by simp
    next
      case False
      thus "hb (r, NormalField f t) = hb'' (r, NormalField f t)"
        using NewHeapProperty ProgramTotal
        by simp 
    qed
  qed

  have IdOnKnownCond: "\<forall>r f. 0 < mb (r, f) \<longrightarrow> hb (r, f) = hb'' (r, f)"
  proof clarify
    fix r f t 
    assume PermPos: "0 < mb (r, f)"

    show "hb (r, f) = hb'' (r, f)"
    proof (cases "is_NormalField f")
      case True
      then show ?thesis 
        using IdOnKnownCondNormalField PermPos
        by (metis is_NormalField_def)
    next
      case False
      hence "(r,f) \<notin> vpr_heap_locations_bpl (program_total ctxt_vpr) (field_translation Tr)"
        unfolding vpr_heap_locations_bpl_def
        by force
      thus ?thesis
        using NewHeapProperty PermPos
        by auto
    qed
  qed

  let ?ns1 = "update_var (var_context ctxt) ns hvar_exh (AbsV (AHeap hb''))"
  have Red1:  "red_ast_bpl P ctxt ((BigBlock name (Havoc hvar_exh # 
                                                 Assume (FunExp id_on_known_locs_name [] [Var hvar, Var hvar_exh, Var mvar]) # 
                                                 Assign hvar (Var hvar_exh) #
                                                 cs) str tr, cont), Normal ns)
                           ((BigBlock name (Assign hvar (Var hvar_exh) # cs) str tr, cont), Normal ?ns1)"
    apply (subst \<open>hvar = _\<close>)+
    apply (subst \<open>mvar = _\<close>)+
    apply (rule red_ast_bpl_identical_on_known_locs[OF CtxtWf \<open>id_on_known_locs_name = _\<close> \<open>type_interp ctxt = _\<close> LookupDeclExhaleHeap])
          apply (rule LookupHeapVar)
         apply (rule LookupMaskVar)
    using ExhaleHeapFresh
        apply blast
       apply (rule HeapVarWellTy)
      apply (rule NewHeapWellTy)
     apply simp
    apply (rule IdOnKnownCond)
    done

  have StateRel1: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ?ns1"
    using StateRel
    apply (rule state_rel_independent_var)
    using ExhaleHeapFresh
       apply blast
    using TypeInterp
      apply simp
    using LookupDeclExhaleHeap
    unfolding lookup_var_decl_def lookup_var_ty_def
     apply simp
    using NewHeapWellTy TypeInterp
    by auto  

  let ?ns2 = "update_var (var_context ctxt) ?ns1 hvar (AbsV (AHeap hb''))"
  have "red_ast_bpl P ctxt ((BigBlock name (Assign hvar (Var hvar_exh) # cs) str tr, cont), Normal ?ns1)
                           ((BigBlock name cs str tr, cont), Normal ?ns2)"      
    apply (subst \<open>hvar = _\<close>)+
    apply (rule red_ast_bpl_one_assign)
    using NewHeapWellTy TypeInterp LookupHeapVarTy
    by (auto intro: RedVar)

  moreover have "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega>' ?ns2"
  proof (rule state_rel_heap_update_2[OF StateRel1])
    show " \<omega> = \<omega> \<and> \<omega>' = \<omega>' \<and> heap_var Tr = heap_var_def Tr"
      using HeapWellDefSame
      by simp
  next
    fix x
    assume "x \<noteq> heap_var Tr"
    thus "lookup_var (var_context ctxt) ?ns1 x = lookup_var (var_context ctxt) ?ns2 x"
      apply (subst \<open>hvar = _\<close>)
      by simp
  next
    show "get_store_total \<omega> = get_store_total \<omega>'"
      using \<open>\<omega>' \<in> _\<close> havoc_locs_state_same_store
      by metis
  next
    show "get_m_total_full \<omega> = get_m_total_full \<omega>'"
      using \<open>\<omega>' \<in> _\<close> havoc_locs_state_same_mask
      by metis
  next
    show "get_trace_total \<omega> = get_trace_total \<omega>'"
      using \<open>\<omega>' \<in> _\<close> havoc_locs_state_same_trace
      by metis
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) \<omega>' ?ns2"
      using ProgramTotal
      unfolding heap_var_rel_def
      apply (subst \<open>hvar = _\<close>)+
      using LookupHeapVarTy NewHeapWellTy NewHeapRel DomainType havoc_locs_state_well_typed_heap[OF \<open>\<omega>' \<in> _\<close>] 
      by auto
  next
    fix x
    assume "map_of (snd (var_context ctxt)) x \<noteq> None"
    thus "global_state ?ns2 x = global_state ?ns1 x"
      by (metis global_state_update_local global_state_update_other option.exhaust)
  next
    show "old_global_state ?ns2 = old_global_state ?ns1"
      by (simp add: update_var_old_global_same)
  next
    from state_rel_state_well_typed[OF StateRel1] have "binder_state ?ns1 = Map.empty"
      unfolding state_well_typed_def
      by blast
      
    thus "binder_state ?ns2 = Map.empty"
      by (simp add: update_var_binder_same)
  qed (insert assms, auto)

  ultimately show "\<exists>ns'. ?red ns' \<and> ?rel ns'"
    using Red1 red_ast_bpl_transitive
    by blast
qed

lemma exhale_pure_stmt_rel_upd_havoc:
  assumes RelImp: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> R_out (snd \<omega>) ns"     
      and SuccessImp:
        "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> 
                 red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and>
                 snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0})"
      and "is_pure A"
    shows "rel_general R (\<lambda>\<omega> ns. R_out (snd \<omega>) ns)
                 Success (\<lambda>_. False) P ctxt \<gamma> \<gamma>"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and "Success \<omega> \<omega>'"
  note SuccessAux = SuccessImp[OF \<open>Success \<omega> \<omega>'\<close>]

  hence "fst \<omega> = snd \<omega>"
    using exhale_pure_normal_same \<open>is_pure A\<close>
    by blast

  with SuccessAux havoc_locs_state_empty
  have "snd \<omega>' = snd \<omega>"
    by (metis (mono_tags, lifting) Collect_empty_eq less_imp_neq)

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns') \<and> R_out (snd \<omega>') ns'"
    using red_ast_bpl_refl \<open>R \<omega> ns\<close> RelImp
    by metis        
qed (simp)

subsection \<open>Assert statement relation\<close>

lemma assert_stmt_rel:
  assumes \<comment>\<open>CaptureState: "red_ast_bpl_rel (uncurry_eq R) (uncurry Rexh) P ctxt \<gamma> \<gamma>1"\<close>
          InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      and ExhaleRel: "exhale_rel (rel_ext_eq R) Rexh Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
   \<comment>\<open>The second disjunct makes explicit that since the assert has no effect on the Viper state,
      the Boogie encoding can continue from any point that is reachable from \<^term>\<open>\<gamma>\<close>.
      The first disjunct allows the Boogie encoding to reach \<^term>\<open>\<gamma>'\<close> from \<^term>\<open>\<gamma>2\<close> (i.e., the point
      after the exhale) as long as the resulting Boogie state is in relation with the original Viper state
      before the assert is executed. The first disjunct expresses the original Viper state
      as the well-definedness state, which is correct since the exhale does not change the well-definedness
      state.\<close>
      and ResetState: "rel_general (uncurry Rexh) (\<lambda>\<omega> ns. R' (snd \<omega>) ns) 
                                   (\<lambda> \<omega>1 \<omega>2. snd \<omega>2 = fst \<omega>1 \<and>
                                             red_exhale ctxt_vpr StateCons (fst \<omega>1) A (fst \<omega>1) (RNormal (snd \<omega>1))) 
                                   (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'
                      \<or> red_ast_bpl_rel R R' P ctxt \<gamma> \<gamma>'"
                 (is "?ResetFromExhale \<or> ?ResetFromStart")
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.Assert A) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and RedStmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.Assert A) \<omega> res"
    
  show "rel_vpr_aux R' P ctxt \<gamma> \<gamma>' ns res"
  proof (rule rel_vpr_aux_intro)
    fix \<omega>'
    assume "res = RNormal \<omega>'"

    with RedStmt obtain \<omega>_exh where RedExh: "red_exhale ctxt_vpr StateCons \<omega> A \<omega> (RNormal \<omega>_exh)" and "\<omega> = \<omega>'"
      by (auto elim: RedAssertNormal_case)


    from this obtain ns_exh where RedBplExh: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns_exh)" and 
                                  "Rexh \<omega> \<omega>_exh ns_exh" 
      using exhale_rel_normal_elim[OF ExhaleRel _ InvHolds[OF \<open>R \<omega> ns\<close>]] \<open>R \<omega> ns\<close>
      by blast

    from disjE[OF ResetState]
    show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    proof (cases)
      case 1
      with rel_success_elim[OF 1] \<open>Rexh \<omega> \<omega>_exh ns_exh\<close> 
      obtain ns' where "red_ast_bpl P ctxt (\<gamma>2, Normal ns_exh) (\<gamma>', Normal ns')" and "R' \<omega> ns'"
        using RedExh
        by fastforce  
      with RedBplExh
      show ?thesis
        using \<open>\<omega> = \<omega>'\<close> red_ast_bpl_transitive
        by blast
    next
      case 2
      with \<open>R \<omega> ns\<close> show ?thesis 
        unfolding red_ast_bpl_rel_def
        using \<open>\<omega> = \<omega>'\<close>
        by force
    qed      
  next
    assume "res = RFailure"

    with RedStmt have RedExh: "red_exhale ctxt_vpr StateCons \<omega> A \<omega> RFailure"
      by (auto elim: RedAssertFailure_case)

    thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      using exhale_rel_failure_elim[OF ExhaleRel _ InvHolds[OF \<open>R \<omega> ns\<close>]] \<open>R \<omega> ns\<close>
      by (metis (no_types, opaque_lifting) snd_conv)
  qed
qed

lemma red_ast_bpl_rel_transitive_with_inv_capture_state:
  assumes Rel1: "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and Inv: "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> Q \<omega>"
      and Rel2: "red_ast_bpl_rel (\<lambda>\<omega> ns. R1 \<omega> ns \<and> Q \<omega>) (uncurry (\<lambda>\<omega>def. state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred  ctxt m h \<omega>def \<omega>def)) P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 (uncurry (\<lambda>\<omega>def. state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred  ctxt m h \<omega>def \<omega>def)) P ctxt \<gamma>0 \<gamma>2"
  using assms
  by (rule red_ast_bpl_rel_transitive_with_inv)

lemma assert_stmt_rel_inst:
  assumes InvHolds: "\<And> \<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      and ExhaleRel: " exhale_rel (rel_ext_eq (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)) 
                                  R' Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
      and ResetState: "rel_general (uncurry R')
                                          (\<lambda> \<omega> ns. state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt (snd \<omega>) ns)
                                          (\<lambda> \<omega>1 \<omega>2. snd \<omega>2 = fst \<omega>1 \<and>
                                             red_exhale ctxt_vpr StateCons (fst \<omega>1) A (fst \<omega>1) (RNormal (snd \<omega>1)))
                                          (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                    (ViperLang.Assert A) \<gamma> \<gamma>'"
  apply (rule assert_stmt_rel[where ?Q=Q])
    apply (rule InvHolds)
    apply assumption
   apply (rule ExhaleRel)
  apply (rule disjI1)
  apply (rule ResetState)
  done 

text \<open>The following lemma turns the goal into a form, which removes the information that the captured state is the well-definedness state.
      The reason for applying this is that the current tactics for \<^const>\<open>exhale_rel\<close> cannot deal with state relations where the parameters
      of \<^const>\<open>state_rel\<close> depend on the state. By making the captured state a quantified variable, one can circumvent this.
      Losing information in this particular case is usually not problematic, because one just wants to show that the captured state
      does not change. One can then later retrieve that the captured state is the well-definedness state (since one knows that 
      exhale does not change the well-definedness state).\<close>

lemma exhale_rel_capture_state_abstract:
  assumes ExhaleRel: "\<And>\<omega>def. exhale_rel (state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred ctxt m h \<omega>def)
                              (state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred  ctxt m h \<omega>def) Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  shows "exhale_rel (\<lambda>\<omega>def. (state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred ctxt m h \<omega>def \<omega>def))
                    (\<lambda>\<omega>def. (state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred ctxt m h \<omega>def \<omega>def)) Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"

  apply (rule exhale_rel_intro_2)
  using exhale_rel_elim_2[OF ExhaleRel]
  by blast

lemma assert_reset_state_pure:
  assumes Success: "\<And> \<omega> \<omega>'.  Success \<omega> \<omega>' \<Longrightarrow> snd \<omega>' = fst \<omega> \<and>
                              red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>))"
      and "is_pure A"
      and \<comment>\<open>as long as the evaluation state is the same, relation is preserved\<close>
          RelImplies: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> snd \<omega> = snd \<omega>' \<Longrightarrow>  R' \<omega>' ns" 
    shows "rel_general R R' Success (\<lambda>_. False) P ctxt \<gamma> \<gamma>" 
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and "Success \<omega> \<omega>'"

  with Success have "snd \<omega>' = fst \<omega>" and "red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>))"
    by blast+

  hence "fst \<omega> = snd \<omega>"
    using exhale_pure_normal_same \<open>is_pure A\<close>
    by blast

  hence "R' \<omega>' ns"
    using RelImplies[OF \<open>R \<omega> ns\<close>] \<open>snd \<omega>' = fst \<omega>\<close>
    by simp    

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>, Normal ns') \<and> R' \<omega>' ns'"    
    using red_ast_bpl_refl \<open>R \<omega> ns\<close>
    by blast
qed (simp)

lemma assert_stmt_rel_alt:
  assumes InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      and CaptureState: "red_ast_bpl_rel R (\<lambda> \<omega> ns. (RStore0 \<omega>) \<omega> ns) P ctxt \<gamma> \<gamma>1"
      and ExhaleRel: "\<And>\<omega>0. exhale_rel (rel_ext_eq (RStore0 \<omega>0)) (RStore \<omega>0) Q ctxt_vpr StateCons P ctxt A \<gamma>1 \<gamma>2"
      and ResetState: "\<And> \<omega>0. rel_general (uncurry (RStore \<omega>0)) (\<lambda>\<omega> ns. R' (snd \<omega>) ns) 
                                          (\<lambda> \<omega>1 \<omega>2. snd \<omega>2 = \<omega>0 \<and> red_exhale ctxt_vpr StateCons \<omega>0 A \<omega>0 (RNormal (snd \<omega>1)))
                                          (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'
                             \<or> red_ast_bpl_rel R R' P ctxt \<gamma> \<gamma>'"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.Assert A) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and RedStmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.Assert A) \<omega> res"


  with CaptureState obtain ns1 where RedBplInit: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)" and RStoreInit: "(RStore0 \<omega>) \<omega> ns1"
    unfolding red_ast_bpl_rel_def
    by auto
    
  show "rel_vpr_aux R' P ctxt \<gamma> \<gamma>' ns res"
  proof (rule rel_vpr_aux_intro)
    fix \<omega>'
    assume "res = RNormal \<omega>'"

    with RedStmt obtain \<omega>_exh where RedExh: "red_exhale ctxt_vpr StateCons \<omega> A \<omega> (RNormal \<omega>_exh)" and "\<omega> = \<omega>'"
      by (auto elim: RedAssertNormal_case)


    from this obtain ns_exh where RedBplExh: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns_exh)" and 
                                  RStore: "(RStore \<omega>) \<omega> \<omega>_exh ns_exh" 
      using exhale_rel_normal_elim[OF ExhaleRel _ InvHolds[OF \<open>R \<omega> ns\<close>]] RStoreInit red_ast_bpl_transitive[OF RedBplInit]
      by blast

    from disjE[OF ResetState[of \<omega>]]
    show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    proof (cases)
      case 1
        with RStore rel_success_elim[OF 1]
        obtain ns' where "red_ast_bpl P ctxt (\<gamma>2, Normal ns_exh) (\<gamma>', Normal ns')" and "R' \<omega> ns'"
          using RedExh
          by fastforce
    
        with RedBplExh
        show ?thesis
          using \<open>\<omega> = \<omega>'\<close> red_ast_bpl_transitive
          by blast
    next
      case 2
      then show ?thesis 
        by (metis \<open>R \<omega> ns\<close> \<open>\<omega> = \<omega>'\<close> red_ast_bpl_rel_def)
    qed
  next
    assume "res = RFailure"

    with RedStmt have RedExh: "red_exhale ctxt_vpr StateCons \<omega> A \<omega> RFailure"
      by (auto elim: RedAssertFailure_case)

    thus "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      using exhale_rel_failure_elim[OF ExhaleRel _ InvHolds[OF \<open>R \<omega> ns\<close>]] RStoreInit red_ast_bpl_transitive[OF RedBplInit]
      by (metis (no_types, opaque_lifting) snd_conv)
  qed
qed

subsection \<open>Method call relation\<close> 

fun the_var :: "ViperLang.pure_exp \<Rightarrow> ViperLang.var" where 
  "the_var (ViperLang.Var x) = x"
| "the_var _ = undefined"

lemma dom_map_upds_test:
  assumes "xs \<noteq> []" and "length xs = length ys"
  shows "dom (map_upds zs xs ys) = dom zs \<union> set xs"
  using assms
  by force

subsubsection \<open>Helper lemmas\<close>

lemma map_le_ran:
  assumes "f \<subseteq>\<^sub>m g"
  shows "ran f \<subseteq> ran g"
  using assms
  unfolding map_le_def ran_def
  by force

lemma state_rel_var_translation_remove:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns" and
          MapLe: "f' \<subseteq>\<^sub>m var_translation Tr" and
          "finite (ran f')"
        shows "state_rel Pr StateCons TyRep (Tr\<lparr> var_translation := f' \<rparr>) AuxPred ctxt \<omega> \<omega> ns"
proof (rule state_rel_store_update[OF StateRel])
  show "store_rel (type_interp ctxt) (var_context ctxt) f' \<omega> ns"
  proof (rule store_relI)
    show "inj_on f' (dom f')"
      using state_rel_var_tr_inj[OF StateRel] MapLe
      by (metis dom_map_add inj_on_Un inj_on_map_add_dom map_add_subsumed2)
  next
    fix var_vpr var_bpl
    assume "f' var_vpr = Some var_bpl"
    hence "var_translation Tr var_vpr = Some var_bpl"
      using MapLe
      unfolding map_le_def
      by force
    thus "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns var_vpr var_bpl"
      using state_rel_store_rel[OF StateRel, simplified store_rel_def]
      unfolding store_var_rel_aux_def
      by blast
  qed
next
  show "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := f'\<rparr>)) \<Longrightarrow> StateCons \<omega>"
    using state_rel_consistent StateRel
    by fastforce
next
  show "binder_state ns = Map.empty"
    using state_rel_state_well_typed[OF StateRel, simplified state_well_typed_def]
    by simp
next
  show "ran f' \<inter>
    ({heap_var Tr, heap_var_def Tr} \<union> {mask_var Tr, mask_var_def Tr} \<union> ran (field_translation Tr) \<union> range (const_repr Tr) \<union>
     dom AuxPred) = {}"
    using var_translation_disjoint[OF assms(1)] map_le_ran[OF assms(2)]
    by blast
qed (insert assms, auto)

lemma state_rel_transfer_var_tr_to_aux_pred:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns" and
          "f' \<subseteq>\<^sub>m var_translation Tr" and
          "finite (ran f')"
          "B = ran (var_translation Tr) - ran f'" 
        shows "state_rel Pr StateCons TyRep (Tr\<lparr> var_translation := f' \<rparr>) 
                 (map_upd_set AuxPred B (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))) 
                 ctxt \<omega> \<omega> ns"
proof -
  let ?Tr' = "Tr\<lparr> var_translation := f' \<rparr>"
  let ?AuxPred' = "map_upd_set AuxPred B (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"

  from assms have "state_rel Pr StateCons TyRep ?Tr' AuxPred ctxt \<omega> \<omega> ns"
    using state_rel_var_translation_remove
    by fast

  thus ?thesis
  proof (rule state_rel_new_aux_var_no_state_upd)
    have "dom ?AuxPred' = dom AuxPred \<union> B"
      by (simp add: map_upd_set_dom)

    let ?M = "({heap_var ?Tr', mask_var ?Tr', heap_var_def ?Tr',
      mask_var_def ?Tr'} \<union>
     ran (var_translation ?Tr') \<union>
     ran (field_translation ?Tr') \<union>
     range (const_repr ?Tr'))"

    note disj_lemmas = state_rel_aux_pred_disjoint[OF StateRel]
                       var_translation_disjoint[OF StateRel]

    have *: "(dom AuxPred \<union> (ran (var_translation Tr) - ran f')) \<inter> ran f' = {}"
    proof -
      have "dom AuxPred \<inter> ran f' = {}"
        using disj_lemmas \<open>f' \<subseteq>\<^sub>m _\<close>
      proof -
        have "ran f' \<subseteq> ran (var_translation Tr)"
          using \<open>f' \<subseteq>\<^sub>m _\<close> map_le_ran
          by blast

        thus ?thesis
          using disj_lemmas
          by blast
      qed
      moreover have "dom AuxPred \<inter> (ran (var_translation Tr) - ran f') = {}"
        using disj_lemmas
        by blast
      ultimately show ?thesis
        by fast
    qed

    show "dom ?AuxPred' \<inter> ?M = {}"
      apply (simp add: map_upd_set_dom)      
      apply (subst \<open>B = _\<close>)+
      apply (intro conjI)
      using disj_lemmas
              apply blast
      using disj_lemmas
             apply blast
      using disj_lemmas
            apply blast
      using disj_lemmas
           apply blast
      using disj_lemmas
          apply blast
      using disj_lemmas
         apply blast
      using disj_lemmas
        apply blast
      using disj_lemmas
       apply blast
      using disj_lemmas *
      by fast
  next
    let ?pred_fun = "(\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"
    show "aux_vars_pred_sat (var_context ctxt) ?AuxPred' ns"
      unfolding aux_vars_pred_sat_def
    proof (rule allI | rule impI)+
      fix x P
      assume SomePred: "map_upd_set AuxPred B ?pred_fun x = Some P"

      from this consider (OldSetCase) "x \<in> dom AuxPred \<and> x \<notin> B" | (NewSetCase) "x \<in> B"
        by (metis Some_Some_ifD domIff map_upd_set_lookup_2)

      thus "has_Some P (lookup_var (var_context ctxt) ns x)"
      proof cases
        case OldSetCase        
        then show ?thesis           
          using state_rel_aux_vars_pred_sat[OF StateRel]
          unfolding aux_vars_pred_sat_def
          by (metis SomePred map_upd_set_lookup_2)
      next
        case NewSetCase
        hence "P = ?pred_fun x"
          using SomePred
          by (simp add: map_upd_set_lookup_1)

        moreover have "lookup_var (var_context ctxt) ns x \<noteq> None"
        proof -
          from NewSetCase obtain x_vpr where "var_translation Tr x_vpr = Some x"
            unfolding \<open>B = _\<close> ran_def
            by blast

          thus ?thesis
            using state_rel_store_rel[OF StateRel]
            unfolding store_rel_def
            by fast
        qed
        ultimately show ?thesis
          unfolding pred_eq_def
          by force          
      qed
    qed
  qed
qed

lemma vpr_store_well_typed_append:
  assumes ArgsWellTy: "vals_well_typed A v_args (method_decl.args mdecl)" 
      and RetsWellTy: "vals_well_typed A v_rets (method_decl.rets mdecl)" 
      and LengthArgs: "length (method_decl.args mdecl) = length v_args"
      and LengthRets: "length (method_decl.rets mdecl) = length v_rets"
    shows "vpr_store_well_typed A (nth_option (method_decl.args mdecl @ rets mdecl)) (shift_and_add_list_alt Map.empty (v_args@v_rets))"
proof (unfold vpr_store_well_typed_def, (rule allI | rule impI)+)
  fix x t
  assume *: "nth_option (method_decl.args mdecl @ rets mdecl) x = Some t"
  have LengthMdeclArgsRets: "length (method_decl.args mdecl) = length v_args \<and> length (method_decl.rets mdecl) = length v_rets"
    using RedMethodCall assms
    by (fastforce dest: vals_well_typed_same_lengthD)
  with * have "x < length (v_args @ v_rets)"
    by (simp split: if_split_asm)

  hence Lookup: "shift_and_add_list_alt Map.empty (v_args @ v_rets) x = Some ((v_args @ v_rets) ! x)"
    using * shift_and_add_list_alt_lookup_1
    by metis

  show "map_option (get_type A) (shift_and_add_list_alt Map.empty (v_args @ v_rets) x) = Some t"
  proof (subst Lookup, simp)
    show "get_type A ((v_args @ v_rets) ! x) = t"
    proof (cases "x < length v_args")
      case True
      hence "(v_args @ v_rets) ! x = v_args ! x" 
        using nth_append 
        by metis
      moreover from True have "(method_decl.args mdecl @ method_decl.rets mdecl) ! x = method_decl.args mdecl ! x"
        using nth_append * LengthArgs
        by (metis LengthMdeclArgsRets)
      ultimately show ?thesis          
        using True ArgsWellTy
        unfolding vals_well_typed_def 
        by (metis "*" LengthArgs LengthRets \<open>x < length (v_args @ v_rets)\<close> length_append nth_map nth_option.elims option.inject)
    next
      case False
      thus ?thesis 
        using \<open>x < length (v_args @ v_rets)\<close> RetsWellTy ArgsWellTy
        unfolding vals_well_typed_def 
        apply simp
        by (metis (mono_tags, lifting) "*" \<open>x < length (v_args @ v_rets)\<close> length_map map_append nth_map nth_option.elims option.inject)        
    qed
  qed
qed

subsubsection \<open>General lemma\<close>

lemma method_call_stmt_rel_general:
  assumes MdeclSome: "program.methods (program_total ctxt_vpr) m = Some mdecl"
      and ArgsWfRel: "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>1"
      and RelPremises:
          "\<And> (\<omega>0 :: 'a full_total_state) ns0 v_args v_rets.  
            R \<omega>0 ns0 \<Longrightarrow>
            red_pure_exps_total ctxt_vpr StateCons (Some \<omega>0) es \<omega>0 (Some v_args) \<Longrightarrow>      
            vals_well_typed (absval_interp_total ctxt_vpr) v_args (method_decl.args mdecl) \<Longrightarrow>
            vals_well_typed (absval_interp_total ctxt_vpr) v_rets (method_decl.rets mdecl) \<Longrightarrow>
            list_all2 (\<lambda>y t. y = Some t) (map \<Lambda>_vpr ys) (rets mdecl) \<Longrightarrow>
            rel_general (\<lambda> \<omega> ns. (\<omega>,ns) = (\<omega>0,ns0)) (RExhIn (g_exh \<omega>0 ns0)) 
                        (\<lambda>\<omega> \<omega>'. \<omega>' = state_during_exhale_pre_call \<omega> v_args) (\<lambda>_.False)
                        P ctxt \<gamma>1 \<gamma>_exh_in \<and>
           \<comment>\<open> (RExhIn (g_exh \<omega>0 ns0)) (state_during_exhale_pre_call \<omega>0 v_args) ns0 \<and>\<close>
            (stmt_rel (RExhIn (g_exh \<omega>0 ns0)) (RExhOut (g_exh \<omega>0 ns0)) ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                          (Exhale (method_decl.pre mdecl)) \<gamma>_exh_in \<gamma>_exh_out) \<and>
            rel_general (RExhOut (g_exh \<omega>0 ns0)) (RInhIn (g_inh \<omega>0 ns0))
                        (\<lambda>\<omega> \<omega>'. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr 
                                                (Exhale (method_decl.pre mdecl)) 
                                                (state_during_exhale_pre_call \<omega>0 v_args)
                                                (RNormal \<omega>) \<and>
                                 \<omega>' = state_during_inhale_post_call \<omega>0 \<omega> v_args v_rets) (\<lambda>_. False)
                         P ctxt \<gamma>_exh_out \<gamma>_inh_in \<and>
            (stmt_rel (RInhIn (g_inh \<omega>0 ns0)) (RInhOut (g_inh \<omega>0 ns0)) ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                        (Inhale (method_decl.post mdecl)) \<gamma>_inh_in \<gamma>_inh_out) \<and>
            rel_general (RInhOut (g_inh \<omega>0 ns0)) R'
                                            \<comment>\<open>type annotation must match the one given above, otherwise will not match the other states\<close>
                         (\<lambda>\<omega> \<omega>'. (\<exists>\<omega>pre :: 'a full_total_state. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr 
                                          (Inhale (method_decl.post mdecl))
                                          (state_during_inhale_post_call \<omega>0 \<omega>pre v_args v_rets)
                                          (RNormal \<omega>)) \<and>
                                  \<omega>' = reset_state_after_call ys v_rets \<omega>0 \<omega>) (\<lambda>_. False)
                         P ctxt \<gamma>_inh_out \<gamma>'"
    shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda>_vpr P ctxt (MethodCall ys m es) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega>0 ns0_before_args res
  assume R0: "R \<omega>0 ns0_before_args" 

  let ?xs = "map the_var es"

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (MethodCall ys m es) \<omega>0 res"

  thus "rel_vpr_aux R' P ctxt \<gamma> \<gamma>' ns0_before_args res"
  proof (cases)
    case (RedMethodCall v_args mdecl' v_rets resPre resPost)

    from MdeclSome RedMethodCall have "mdecl = mdecl'"
      by force

    have *: "list_all2 (\<lambda>y t. y = Some t) (map \<Lambda>_vpr ys) (rets mdecl) "
      using RedMethodCall \<open>mdecl = _\<close>
      by blast            

    have ListAllArgsEvalVpr: "list_all2 (\<lambda>e v. ctxt_vpr, StateCons, Some \<omega>0 \<turnstile> \<langle>e; \<omega>0\<rangle> [\<Down>]\<^sub>t Val v) es v_args"
      using red_pure_exps_total_list_all2 RedMethodCall
      by blast

    from RedMethodCall exprs_wf_rel_normal_elim[OF ArgsWfRel] R0 obtain ns0 where 
           RedArgsBpl: "red_ast_bpl P ctxt (\<gamma>, Normal ns0_before_args) (\<gamma>1, Normal ns0)"
       and RArgs: "R \<omega>0 ns0"  
      by blast

    from RelPremises[OF RArgs] RedMethodCall \<open>mdecl = _\<close> have 
          InitStateRel: "rel_general (\<lambda> \<omega> ns. (\<omega>,ns) = (\<omega>0,ns0)) (RExhIn (g_exh \<omega>0 ns0)) 
                        (\<lambda>\<omega> \<omega>'. \<omega>' = state_during_exhale_pre_call \<omega> v_args) (\<lambda>_.False)
                        P ctxt \<gamma>1 \<gamma>_exh_in"
      and ExhalePreRel: "stmt_rel (RExhIn (g_exh \<omega>0 ns0)) (RExhOut (g_exh \<omega>0 ns0)) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale (method_decl.pre mdecl)) \<gamma>_exh_in \<gamma>_exh_out"
      and ExhOutInhInRel: "rel_general (RExhOut (g_exh \<omega>0 ns0)) (RInhIn (g_inh \<omega>0 ns0))
                                       (\<lambda>\<omega> \<omega>'.  red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr 
                                                (Exhale (method_decl.pre mdecl)) 
                                                (state_during_exhale_pre_call \<omega>0 v_args)
                                                (RNormal \<omega>) \<and>
                                        \<omega>' = state_during_inhale_post_call \<omega>0 \<omega> v_args v_rets) (\<lambda>_. False) 
                                        P ctxt \<gamma>_exh_out \<gamma>_inh_in"
      and InhalePostRel: "stmt_rel (RInhIn (g_inh \<omega>0 ns0)) (RInhOut (g_inh \<omega>0 ns0)) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale (method_decl.post mdecl)) \<gamma>_inh_in \<gamma>_inh_out"
      and ResetStateRel: "rel_general (RInhOut (g_inh \<omega>0 ns0)) R'
                         (\<lambda>\<omega> \<omega>'.
                             (\<exists>\<omega>pre :: 'a full_total_state. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl)) (state_during_inhale_post_call \<omega>0 \<omega>pre v_args v_rets) (RNormal \<omega>)) \<and>
                             \<omega>' = reset_state_after_call ys v_rets \<omega>0 \<omega>)
                         (\<lambda>_. False) P ctxt \<gamma>_inh_out \<gamma>'"
      by blast+


    from RedArgsBpl rel_success_elim[OF InitStateRel] RArgs
    obtain ns_exh_in where
           RedExhIn: "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) (\<gamma>_exh_in, Normal ns_exh_in)"
       and RExhIn: "RExhIn (g_exh \<omega>0 ns0) (state_during_exhale_pre_call \<omega>0 v_args) ns_exh_in"
      by blast      
      
    show ?thesis 
    proof (cases "resPre") \<comment>\<open>case split on exhale precondition outcome\<close>
      case RMagic
      then show ?thesis
        using RedMethodCall
        by (auto intro: rel_vpr_aux_intro)
    next
      case RFailure
      with RedMethodCall \<open>mdecl = _\<close> 
      obtain c where 
          "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) c" and
          "snd c = Failure"
        using stmt_rel_failure_elim[OF ExhalePreRel RExhIn] RedExhIn red_ast_bpl_transitive
        by blast
      moreover have "res = RFailure"
        using RFailure RedMethodCall
        by argo
      ultimately show ?thesis         
        using red_ast_bpl_transitive RedArgsBpl
        by (blast intro: rel_vpr_aux_intro) 
    next
      case (RNormal \<omega>pre)
      from RNormal RedMethodCall \<open>mdecl = _\<close>
      obtain nspre where
         RedBplPre: "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) (\<gamma>_exh_out, Normal nspre)" and
         RExhOut: "RExhOut (g_exh \<omega>0 ns0) \<omega>pre nspre"
        using stmt_rel_normal_elim[OF ExhalePreRel RExhIn] RedExhIn red_ast_bpl_transitive
        by blast

      let ?\<omega>havoc = "state_during_inhale_post_call \<omega>0 \<omega>pre v_args v_rets"

      from rel_success_elim[OF ExhOutInhInRel] RExhOut obtain nshavoc where
         "red_ast_bpl P ctxt (\<gamma>_exh_out, Normal nspre) (\<gamma>_inh_in, Normal nshavoc)" and  
         RInhIn: "RInhIn (g_inh \<omega>0 ns0) ?\<omega>havoc nshavoc"
        using \<open>red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (method_decl.pre mdecl')) (state_during_exhale_pre_call \<omega>0 v_args) resPre\<close> 
             RNormal \<open>mdecl = _\<close>
        by blast                                                                                                    

      hence RedBplHavoc: "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) (\<gamma>_inh_in, Normal nshavoc)"
        using RedBplPre red_ast_bpl_transitive
        by blast

      from RedMethodCall RNormal have 
         RedInh: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl')) ?\<omega>havoc resPost" and
         "res = map_stmt_result_total (reset_state_after_call ys v_rets \<omega>0) resPost"
        by blast+

      show ?thesis
      proof (cases resPost) \<comment>\<open>case split on inhale postcondition outcome\<close>
        case RMagic
        then show ?thesis \<comment>\<open>trivial case\<close>
          using \<open>res = _\<close>
          by (auto intro: rel_vpr_aux_intro)     
      next
        case RFailure
        with RedInh stmt_rel_failure_elim[OF InhalePostRel RInhIn] \<open>mdecl = _\<close>
        obtain c where 
            "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) c" and
            "snd c = Failure"
          using RedBplHavoc red_ast_bpl_transitive
          by blast
        moreover from RFailure \<open>res = _\<close> have "res = RFailure"
          by simp
        ultimately show ?thesis 
          using RedArgsBpl red_ast_bpl_transitive
          by (blast intro: rel_vpr_aux_intro)     
      next
        case (RNormal \<omega>post)
          with RedInh stmt_rel_normal_elim[OF InhalePostRel RInhIn] \<open>mdecl = _\<close>
          obtain nspost where 
              RedBplPost: "red_ast_bpl P ctxt (\<gamma>1, Normal ns0) (\<gamma>_inh_out, Normal nspost)" and
              RInhOut: "RInhOut (g_inh \<omega>0 ns0) \<omega>post nspost"
            using RedBplHavoc red_ast_bpl_transitive
            by blast

          let ?\<omega>reset = "reset_state_after_call ys v_rets \<omega>0 \<omega>post"

          from rel_success_elim[OF ResetStateRel RInhOut] obtain nsreset
            where 
                "red_ast_bpl P ctxt (\<gamma>_inh_out, Normal nspost) (\<gamma>', Normal nsreset)"
            and "R' (reset_state_after_call ys v_rets \<omega>0 \<omega>post) nsreset"
            using RedInh \<open>mdecl = _\<close> \<open>resPost = _\<close>
            by blast
            
          thus ?thesis
            unfolding rel_vpr_aux_def \<open>res = _\<close> \<open>resPost = _\<close>
            using RedBplPost RedArgsBpl
            by (metis exh_if_total.elims exh_if_total_normal_2 map_stmt_result_total.simps(1) red_ast_bpl_transitive stmt_result_total.distinct(5))
      qed
    qed
  next
    case RedSubExpressionFailure
    \<comment>\<open>Since the arguments are assumed to be arguments, this case cannot occur\<close>
    have SubExpEq: "sub_expressions (MethodCall ys m es) = es"
      by simp

    from RedSubExpressionFailure
    show ?thesis
      unfolding rel_vpr_aux_def
      using exprs_wf_rel_failure_elim[OF ArgsWfRel] R0
      by auto
  qed
qed

abbreviation method_before_state_pred
  where "method_before_state_pred ctxt_vpr StateCons mdecl R es v_args v_rets \<omega>0 ns0 \<equiv> 
           R \<omega>0 ns0 \<and>
            red_pure_exps_total ctxt_vpr StateCons (Some \<omega>0) es \<omega>0 (Some v_args)"

subsubsection \<open>Instantiated lemma\<close>

lemma method_call_stmt_rel_inst:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and ConsistencyDownwardMono: "mono_prop_downward_ord StateCons"
      and "Pr = program_total ctxt_vpr"
          \<comment>\<open>We need to require state consistency, otherwise framing_exh cannot be established.\<close>
      and ConsistencyEnabled: "consistent_state_rel_opt (state_rel_opt Tr)"
      and MdeclSome:  "program.methods (program_total ctxt_vpr) m = Some mdecl"
      and MethodSpecsFramed: "vpr_method_spec_correct_total ctxt_vpr StateCons mdecl"
      and MethodSpecSubset:  "no_perm_assertion (method_decl.pre mdecl) \<and>                                    
                              no_perm_assertion (method_decl.post mdecl) \<and> 
                              supported_assertion (method_decl.pre mdecl) \<and>
                              supported_assertion (method_decl.post mdecl)"
      and OnlyArgsInPre: "\<And> x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow> x < length es"
      and "rtype_interp ctxt = []"
      and DomainTyRep: "domain_type TyRep = absval_interp_total ctxt_vpr"
      and TyInterpBplEq:   "type_interp ctxt = vbpl_absval_ty TyRep"
      and StateRelConcrete: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"              
      and ArgsAreVars: "list_all (\<lambda>x. \<exists>a. x = ViperLang.Var a) es" \<comment>\<open>simplifying assumption: only variables as arguments\<close>
      and "xs = map the_var es"
      and "set xs \<subseteq> dom (var_translation Tr)"
      and XsBplEq: "map (the \<circ> var_translation Tr) xs = xs_bpl"
      and "set ys \<subseteq> dom (var_translation Tr)"
      and YsBplEq: "map (the \<circ> var_translation Tr) ys = ys_bpl"
      and "set xs_bpl \<inter> set ys_bpl = {}" \<comment>\<open>simplifying assumption: targets and arguments do not clash\<close>
      and "distinct xs" \<comment>\<open>simplifying assumption: arguments are distinct\<close>
      and "distinct ys"
             \<comment>\<open>TODO: One could probably track the following fact on declared types also via the variable relation
                      where one ensures that the declared Viper and Boogie types match for variables related by
                      the variable relation.\<close>
      and LookupDeclRetsBpl: 
                     "list_all2 (\<lambda>y_bpl t_vpr. \<exists>t_bpl. vpr_to_bpl_ty TyRep t_vpr = Some t_bpl \<and>
                                           lookup_var_decl (var_context ctxt) y_bpl = Some (t_bpl, None))
                                ys_bpl (method_decl.rets mdecl)"
          \<comment>\<open> Since the rule only deals with variables in the arguments, well-definedness holds trivially
             ExpWfRel: "exprs_wf_rel Rdef ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>def"\<close>
                   \<comment>\<open>simplifying assumption: unoptimized exhale and inhale\<close>
                        \<comment>\<open>"var_tr' = [[0..<length es] [\<mapsto>] rev xs_bpl]" and \<close>
      and "var_tr' = [[0..<length es] [\<mapsto>] xs_bpl]"
      and ExhalePreRel:
                      "\<And> fpred.                                                
                        stmt_rel 
                              (\<lambda>\<omega> ns.
                                 state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt \<omega> ns \<and>
                                 framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) \<omega> \<omega>)
                              (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt) 
                              ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                              (Exhale (method_decl.pre mdecl)) \<gamma> (BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)"
      and "cs_pre = havocs_list_bpl ys_bpl @ cs_pre_suffix"
      and "var_tr'' = Map.empty(upt 0 (length es+length ys) [\<mapsto>] (xs_bpl @ ys_bpl))"
      and InhalePostRel: 
          "\<And> fpred.  stmt_rel 
                        (\<lambda> \<omega> ns. 
                         state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt \<omega> ns \<and>
                         assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega> 
                        )
                        (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt)
                        ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                        (Inhale (method_decl.post mdecl)) (BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre) \<gamma>'"
      shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (MethodCall ys m es) \<gamma> \<gamma>'"
proof (rule method_call_stmt_rel_general[OF MdeclSome _,
      where ?g_exh="(\<lambda>\<omega>0 ns0. \<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns0 x)))" and
            ?g_inh="(\<lambda>\<omega>0 ns0. \<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns0 x)))"]; (intro conjI)?)

\<comment>\<open>Arguments are well-defined by default since we restrict them to be variables here\<close>

  show "exprs_wf_rel (rel_ext_eq R) ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>"
    unfolding exprs_wf_rel_def
  proof (rule wf_rel_intro)
    fix \<omega>def \<omega> ns
    assume "rel_ext_eq R \<omega>def \<omega> ns" and 
           "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None"

    from this obtain i where "i < length es" and 
                             "red_pure_exp_total ctxt_vpr StateCons (Some \<omega>def) (es ! i) \<omega> VFailure"
      by (metis option.distinct(1) red_exp_list_failure_Nil red_exp_list_failure_nth)

    hence False
      using ArgsAreVars
      by (smt (verit, ccfv_SIG) list_all_length var_never_fails)

    fix contra
    show contra
      using \<open>False\<close>
      by auto
  qed (auto intro: red_ast_bpl_refl)

\<comment>\<open>Initialization\<close>
  fix \<omega> :: "'a full_total_state"
  fix ns :: "'a vbpl_absval nstate"
  fix  v_args v_rets
  assume R0: "R \<omega> ns" 
     and RedArgs: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) es \<omega> (Some v_args)"
     and ArgsWellTyped: "vals_well_typed (absval_interp_total ctxt_vpr) v_args (method_decl.args mdecl)"
     and RetsWellTyped: "vals_well_typed (absval_interp_total ctxt_vpr) v_rets (rets mdecl)"
     and RetsRespectVarContext: "list_all2 (\<lambda>y t. y = Some t) (map \<Lambda>_vpr ys) (rets mdecl)"

  note MethodCallPremises = RedArgs ArgsWellTyped RetsWellTyped RetsRespectVarContext
    
  have "es = map pure_exp.Var xs"
  proof (rule nth_equalityI)
    show "length es = length (map pure_exp.Var xs)"
      using \<open>xs = _\<close>
      by simp
  next
    fix i 
    assume "i < length es"
    show "es ! i = map pure_exp.Var xs ! i"
    proof -
      have "xs ! i = the_var (es ! i)"
        using \<open>i < _\<close> \<open>xs = _\<close>
        by simp
      moreover from ArgsAreVars obtain x where
          "es ! i = pure_exp.Var x"
        using \<open>i < _\<close>                 
        by (fastforce simp: list_all_length)

      ultimately show ?thesis
        using \<open>i < length es\<close> \<open>xs = _\<close> by auto
    qed            
  qed

  have "set xs_bpl \<subseteq> ran (var_translation Tr)"
  proof 
    fix x_bpl
    assume "x_bpl \<in> set xs_bpl"

    from this obtain x_vpr where "x_vpr \<in> set xs" and "the ((var_translation Tr) x_vpr) = x_bpl"
      using XsBplEq
      by auto

    moreover with \<open>set xs \<subseteq> dom (var_translation Tr)\<close> obtain x_bpl' where "var_translation Tr x_vpr = Some x_bpl'"
      by fast

    ultimately show "x_bpl \<in> ran (var_translation Tr)"
      by (simp add: ranI)
  qed

  have "set ys_bpl \<subseteq> ran (var_translation Tr)"
  proof 
    fix x_bpl
    assume "x_bpl \<in> set ys_bpl"

    from this obtain x_vpr where "x_vpr \<in> set ys" and "the ((var_translation Tr) x_vpr) = x_bpl"
      using YsBplEq
      by auto

    moreover with \<open>set ys \<subseteq> dom (var_translation Tr)\<close> obtain x_bpl' where "var_translation Tr x_vpr = Some x_bpl'"
      by fast

    ultimately show "x_bpl \<in> ran (var_translation Tr)"
      by (simp add: ranI)
  qed

  have ListAllArgsEvalVpr: "list_all2 (\<lambda>e v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) es v_args"
    using red_pure_exps_total_list_all2 RedArgs
    by blast

  have "length es = length v_args"
    using MethodCallPremises red_pure_exps_total_Some_lengthD
    by blast

  have "length xs = length xs_bpl"
    using XsBplEq
    by auto

  have "length xs_bpl = length v_args"
    using \<open>xs = _\<close> XsBplEq
    by (metis ListAllArgsEvalVpr length_map list_all2_lengthD)    

  have "length ys = length ys_bpl"
    using YsBplEq by auto

  hence "length ys_bpl = length v_rets"
    using RetsWellTyped RetsRespectVarContext
    unfolding vals_well_typed_def
    by (metis length_map list_all2_lengthD)

  note LengthEqs = \<open>length es = length v_args\<close> \<open>length xs = length xs_bpl\<close> \<open>length xs_bpl = length v_args\<close>
                   \<open>length ys = length ys_bpl\<close> \<open>length ys_bpl = length v_rets\<close>

  have "distinct xs_bpl" and "distinct ys_bpl"
  proof -
    have "inj_on (var_translation Tr) (dom (var_translation Tr))"
    using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
    unfolding store_rel_def
    by blast

    thus "distinct ys_bpl" and "distinct xs_bpl"
      using XsBplEq YsBplEq distinct_map_the_inj_on_subset \<open>distinct xs\<close> \<open>distinct ys\<close> \<open>set xs \<subseteq> _\<close> \<open>set ys \<subseteq> _\<close> 
      by blast+
  qed

  from R0 have StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
    using StateRelConcrete
    by blast  

  hence "StateCons_t (get_total_full \<omega>)"
    using state_rel_consistent StateRel WfConsistency ConsistencyEnabled
    unfolding wf_total_consistency_def
    by blast

  have StoreSameOnArgs: "\<And>x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow>
             shift_and_add_list_alt Map.empty (v_args @ v_rets) x = 
             shift_and_add_list_alt Map.empty v_args x" (is "\<And>x. _ \<Longrightarrow> ?store_args_rets x = ?store_args x")
  proof -
    fix x 
    assume "x \<in> free_var_assertion (method_decl.pre mdecl)"
    hence *: "x < length v_args"
      using OnlyArgsInPre LengthEqs
      by auto
    hence **: "x < length (v_args @ v_rets)"
      by simp

    thus "?store_args_rets x = ?store_args x"
    proof -
      have "shift_and_add_list_alt Map.empty (v_args @ v_rets) x = Some ((v_args @ v_rets) ! x)"
        using shift_and_add_list_alt_lookup_1[OF **]
        by blast
      also have "... = Some (v_args ! x)"
        using \<open>x < length v_args\<close>
        by (simp add: nth_append)
      finally show "shift_and_add_list_alt Map.empty (v_args @ v_rets) x = shift_and_add_list_alt Map.empty v_args x"
        using shift_and_add_list_alt_lookup_1[OF \<open>x < length v_args\<close>]
        by simp
    qed
  qed

  have StoreValArgsVpr: "list_all2 (\<lambda>x v. get_store_total \<omega> x = Some v) xs v_args"
    proof -
      have "list_all2 (\<lambda>x v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>ViperLang.Var x; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) xs v_args"
      proof (rule list_all2_all_nthI)
        show "length xs = length v_args"
          using LengthEqs
          by simp
      next
        fix i
        assume "i < length xs"
       
        hence *: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>es ! i; \<omega>\<rangle> [\<Down>]\<^sub>t Val (v_args ! i)"
          using ListAllArgsEvalVpr LengthEqs
          by (simp add: list_all2_conv_all_nth)
  
        have "es ! i = pure_exp.Var (xs ! i)"
          using \<open>i < _\<close> \<open>es = _\<close>
          by auto
    
        thus "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>pure_exp.Var (xs ! i);\<omega>\<rangle> [\<Down>]\<^sub>t Val (v_args ! i)"
          using *
          by simp
      qed
      thus ?thesis
      using TotalExpressions.RedVar_case
      by (metis (mono_tags, lifting) list_all2_mono)
    qed

  have StoreRelAuxArgs: 
    "list_all2 (\<lambda> x_vpr x_bpl. store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns x_vpr x_bpl) xs xs_bpl"
  proof (rule list_all2_all_nthI)
    fix i
    assume "i < length xs"

    let ?x_vpr = "xs ! i"
    let ?x_bpl = "xs_bpl ! i"


    have "var_translation Tr (xs ! i) = Some (xs_bpl ! i)"
      using XsBplEq \<open>set xs \<subseteq> dom _\<close> \<open>i < _\<close> nth_mem
      by fastforce

    thus "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns ?x_vpr ?x_bpl"
      using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
      unfolding store_var_rel_aux_def store_rel_def
      by blast 
  next
    show "length xs = length xs_bpl"
      using XsBplEq by auto
  qed

  have ValRelArgs: "list_all2 
        (\<lambda> v_vpr x_bpl. lookup_var (var_context ctxt) ns x_bpl = Some (val_rel_vpr_bpl v_vpr) \<and>
                        (\<exists>ty_bpl. lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl \<and> 
                        type_of_val (type_interp ctxt) (val_rel_vpr_bpl v_vpr) = ty_bpl)) 
        v_args 
        xs_bpl"
  proof (rule list_all2_all_nthI)
    show "length v_args = length xs_bpl"
      by (simp add: \<open>length xs_bpl = length v_args\<close>)
  next
    fix i 
    assume "i < length v_args"

    with \<open>length xs_bpl = length v_args\<close> have
      "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns (xs ! i) (xs_bpl ! i)"
      using StoreRelAuxArgs
      by (metis list_all2_nthD2)

    thus "lookup_var (var_context ctxt) ns (xs_bpl ! i) = Some (val_rel_vpr_bpl (v_args ! i)) \<and>
       (\<exists>ty_bpl. lookup_var_ty (var_context ctxt) (xs_bpl ! i) = Some ty_bpl \<and> 
       type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! i)) = ty_bpl)"        
      using StoreValArgsVpr \<open>i < _\<close>
      unfolding store_var_rel_aux_def
      by (simp add: list_all2_conv_all_nth)
  qed

  \<comment>\<open>main proof\<close>

  let ?\<omega>0 = "state_during_exhale_pre_call \<omega> v_args"
  let ?fpred  = "(\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"
  let ?AuxPredPre = "(map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) ?fpred)"
  let ?RCallParam = "\<lambda>fpred. state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt"
  let ?RCall = "?RCallParam ?fpred"

   \<comment>\<open>We prove the first conjunct of the state relation before the exhale of the precondition\<close>
  
  have StateRelDuringCall: "?RCall ?\<omega>0 ns" 
  proof -
    from var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] have 
      *: "ran (var_translation Tr) \<inter> dom AuxPred = {}"
      by blast

    have AuxSub: "map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) ?fpred \<subseteq>\<^sub>m
          map_upd_set AuxPred (ran (var_translation Tr)) ?fpred"
      unfolding map_upd_set_def
      apply (rule map_add_le_dom_disjoint)
      using *
       apply (smt (verit) disjoint_iff_not_equal domIff)
      by (smt (verit) Diff_iff domIff map_le_def)

    have StoreRel: "store_rel (type_interp ctxt) (var_context ctxt) var_tr' ?\<omega>0 ns"
    proof (rule store_relI)
      \<comment>\<open>Could adjust state rel with an additional parameter that switches off injectivity on the variable translation.
         Then, one could support multiple arguments being the same variable. Injectivity is useful only if there
         are changes to the local Viper variables.\<close>
      show "inj_on var_tr' (dom var_tr')"
        unfolding \<open>var_tr' = _\<close>
        using inj_on_upt_distinct \<open>distinct xs_bpl\<close> LengthEqs
        by fastforce
    next
      fix x_vpr x_bpl
      assume VarTrSome: "var_tr' x_vpr = Some x_bpl" 
      with \<open>var_tr' = _\<close>
      have "x_vpr \<in> set [0..<length es]"
        by (metis Some_Some_ifD map_upds_apply_nontin)
      hence "x_vpr < length es"
        by simp
      hence "x_vpr < length v_args"
        using ListAllArgsEvalVpr
        using list_all2_lengthD by force
      with ValRelArgs
      have *:"lookup_var (var_context ctxt) ns (xs_bpl ! x_vpr) = Some (val_rel_vpr_bpl ( v_args ! x_vpr))"
        using list_all2_nthD 
        by blast
      
      have "x_bpl = xs_bpl ! x_vpr"
      proof -
        from \<open>x_vpr \<in> _\<close> have *: "x_vpr = [0..<length es] ! x_vpr"
          by simp
        thus ?thesis
          using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys = "xs_bpl"]
                LengthEqs VarTrSome \<open>x_vpr < length v_args\<close> \<open>var_tr' = _\<close> 
          by auto
      qed          

      hence "x_bpl \<in> set xs_bpl"
        using \<open>x_vpr < length v_args\<close> \<open>length xs_bpl = length v_args\<close>
        by force

      from ValRelArgs obtain \<tau>_bpl where
        XBplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some \<tau>_bpl" 
                "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! x_vpr)) = \<tau>_bpl"
        using  \<open>x_bpl = _\<close> \<open>x_vpr < length v_args\<close> list_all2_nthD by blast          

      show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>0 ns x_vpr x_bpl"
        unfolding store_var_rel_aux_def
      proof ((rule exI)+, intro conjI)
        show "get_store_total ?\<omega>0 x_vpr = Some (v_args ! x_vpr)"
          using shift_and_add_list_alt_lookup_1 \<open>x_vpr < length v_args\<close>
          by auto
      next
        from * \<open>x_bpl = _\<close> 
        show "lookup_var (var_context ctxt) ns x_bpl = Some (val_rel_vpr_bpl (v_args ! x_vpr))"
          by simp  
      next
        show "lookup_var_ty (var_context ctxt) x_bpl = Some \<tau>_bpl"
          using XBplTy
          by blast
      next
        show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! x_vpr)) = \<tau>_bpl"
          using XBplTy
          by blast
      qed
    qed      

    have "ran var_tr' = set xs_bpl"
      using map_upds_upt_ran LengthEqs
      unfolding \<open>var_tr' = _\<close>
      by force

    have "state_rel Pr StateCons TyRep (Tr \<lparr> var_translation := Map.empty \<rparr>) ?AuxPredPre ctxt \<omega> \<omega> ns"
      apply (rule state_rel_aux_pred_remove)
       apply (rule state_rel_transfer_var_tr_to_aux_pred[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]])
        apply simp
        apply simp
       apply simp
      by (rule AuxSub)        

    thus ?thesis
    proof (rule state_rel_store_update[where ?f= var_tr'])
      show "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<Longrightarrow> StateCons ?\<omega>0"
        apply (rule total_consistencyI[OF WfConsistency])
         apply (insert \<open>StateCons_t (get_total_full \<omega>)\<close>)
         apply (solves \<open>simp\<close>)
        apply simp
        by (metis option.distinct(1) option.inject)           
    next
      show "binder_state ns = Map.empty"
        using state_rel_state_well_typed[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>], simplified state_well_typed_def]
        by simp
    next
      show "store_rel (type_interp ctxt) (var_context ctxt) var_tr' ?\<omega>0 ns"
        using StoreRel
        by blast
    qed (insert  var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] \<open>set xs_bpl \<subseteq> _\<close> \<open>ran var_tr' = _\<close>,
         auto simp add: map_upd_set_lookup_2)
  qed
  
  show "rel_general (\<lambda>\<omega>1 ns1. (\<omega>1, ns1) = (\<omega>, ns)) (\<lambda>\<omega> ns. ?RCall \<omega> ns \<and> framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) \<omega> \<omega>)
        (\<lambda>\<omega> \<omega>'. \<omega>' = state_during_exhale_pre_call \<omega> v_args) (\<lambda>_. False) P ctxt \<gamma> \<gamma>"
  proof (rule rel_general_success_refl_2, simp)
    fix \<omega>_init ns_init \<omega>0
    assume RInit: "(\<omega>_init, ns_init) = (\<omega>, ns)"
       and "\<omega>0 = state_during_exhale_pre_call \<omega>_init v_args"

    \<comment>\<open>Prove various properties before showing the goal\<close> 

    have AssertionFramingInit: "framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0 ?\<omega>0"
    proof -
      let ?\<omega>0_rets_empty = "\<lparr> get_store_total = shift_and_add_list_alt Map.empty (v_args@v_rets), 
                    get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                    get_total_full = (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>"
      let ?\<omega>0_empty = "?\<omega>0\<lparr> get_total_full := (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>"
  
      have "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty"
        unfolding assertion_framing_state_def
      proof (rule allI, rule impI)+
        fix res
        assume "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty res"           
        moreover have "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (shift_and_add_list_alt Map.empty (v_args@v_rets))"
          apply (rule vpr_store_well_typed_append)
          using ArgsWellTyped RetsWellTyped
          by (auto dest: vals_well_typed_same_lengthD)
        moreover have "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full ?\<omega>0_rets_empty)"
          using state_rel_heap_var_rel[OF StateRel] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
          unfolding heap_var_rel_def
          by simp
        moreover have "is_empty_total_full ?\<omega>0_rets_empty"
          by (simp add: is_empty_total_full_def is_empty_total_def)
        ultimately show "res \<noteq> RFailure"
          using MethodSpecsFramed
          unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
          by (metis full_total_state.select_convs(1))          
      qed
  
      hence AssertionFraming_\<omega>0'_only_args: "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_empty"
     \<comment>\<open>using that return variables do not appear in precondition\<close>
        apply (rule assertion_framing_store_same_on_free_var[OF WfConsistency])
        apply (insert StoreSameOnArgs, insert MethodSpecSubset)
        by auto
  
      show ?thesis        
      proof (rule framing_exhI[OF _ _ AssertionFraming_\<omega>0'_only_args])
        show "StateCons ?\<omega>0"
          using StateRelDuringCall state_rel_consistent ConsistencyEnabled
          by fastforce
      next
        show "valid_heap_mask (get_mh_total_full ?\<omega>0)"
          using StateRelDuringCall state_rel_wf_mask_simple
          by fast
      next        
        show "?\<omega>0_empty \<oplus> ?\<omega>0 = Some ?\<omega>0"
          by (rule plus_full_total_state_zero_mask) simp_all          
      next
        show "?\<omega>0 \<succeq> ?\<omega>0"
          by (simp add: succ_refl)
      qed
    qed

    note RCallPre = conjI[OF \<open>?RCall ?\<omega>0 ns\<close> AssertionFramingInit]

    thus "?RCall \<omega>0 ns_init \<and> framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) \<omega>0 \<omega>0"
      unfolding \<open>\<omega>0 = _\<close>
      using RInit
      by blast
  qed

  show "stmt_rel (\<lambda>\<omega> ns. ?RCall \<omega> ns \<and>
                                 framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) \<omega> \<omega>)
                          ?RCall 
                          ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                         (Exhale (method_decl.pre mdecl)) \<gamma> (BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)"
    using ExhalePreRel
    by blast

  let ?\<gamma>pre = "(BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)"
  let ?\<gamma>havoc = "(BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre)"
  let ?AuxPredPostParam = "\<lambda>fpred. (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred)"  
  let ?RCallPostParam = "\<lambda>fpred. state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (?AuxPredPostParam fpred) ctxt"
  let ?RCallPost = "?RCallPostParam ?fpred"

\<comment>\<open>We next show that the havocs capture the nondeterministic assignments to the return variables\<close>
  show "rel_general
          ?RCall
          ((\<lambda> \<omega> ns. ?RCallPost \<omega> ns \<and>
                   assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega>)
          )
          (\<lambda>\<omega>_prev \<omega>'. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (method_decl.pre mdecl)) (state_during_exhale_pre_call \<omega> v_args) (RNormal \<omega>_prev) \<and>
                       \<omega>' = state_during_inhale_post_call \<omega> \<omega>_prev v_args v_rets) (\<lambda>_. False) 
         P ctxt
         ?\<gamma>pre
         ?\<gamma>havoc"
  proof (rule rel_intro)
    fix \<omega>pre nspre \<omega>havoc
    assume "?RCall \<omega>pre nspre"
       and SuccessHavoc: 
            "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (method_decl.pre mdecl)) (state_during_exhale_pre_call \<omega> v_args) (RNormal \<omega>pre) \<and>
            \<omega>havoc = state_during_inhale_post_call \<omega> \<omega>pre v_args v_rets"
    note RedExhPre = conjunct1[OF SuccessHavoc] 
    note \<omega>havocEq = conjunct2[OF SuccessHavoc]

    let ?v_rets_bpl = "map (val_rel_vpr_bpl) v_rets"
    let ?nshavoc = "update_var_list (var_context ctxt) nspre ys_bpl ?v_rets_bpl"

    show "\<exists>ns'. red_ast_bpl P ctxt (?\<gamma>pre, Normal nspre) (?\<gamma>havoc, Normal ns') \<and>
             ?RCallPost \<omega>havoc ns' \<and>
             assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega>havoc"
    proof -
     have *: "length ys_bpl = length (map val_rel_vpr_bpl v_rets)"
        proof -
            have "length ys = length ys_bpl"
              using YsBplEq by auto
            moreover have "length ys = length v_rets"
              using MethodCallPremises
              unfolding vals_well_typed_def
              by (metis length_map list_all2_lengthD)
            ultimately show ?thesis
              by simp
          qed

      have YsBplCorrectTypes: "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) 
                                     ys_bpl 
                                     (map val_rel_vpr_bpl v_rets)"
        proof (rule list_all2_all_nthI[OF *])        
          fix n
          assume "n < length ys_bpl"
          
          from this obtain t_bpl where 
            "vpr_to_bpl_ty TyRep ((rets mdecl) ! n) = Some t_bpl"
            "lookup_var_decl (var_context ctxt) (ys_bpl ! n) = Some (t_bpl, None)"
            using LookupDeclRetsBpl
            by (blast dest: list_all2_nthD)

          moreover have "get_type (absval_interp_total ctxt_vpr) (v_rets ! n) = (rets mdecl) ! n"
            using * \<open>n < _\<close> RetsWellTyped
            unfolding vals_well_typed_def
            by (metis length_map nth_map)           

          ultimately 
         show "lookup_var_decl (var_context ctxt) (ys_bpl ! n) = 
                 Some (type_of_val (type_interp ctxt) (map val_rel_vpr_bpl v_rets ! n), None)"
           apply simp
           using DomainTyRep vpr_to_bpl_val_type TyInterpBplEq 
           by (metis "*" \<open>n < length ys_bpl\<close> list_update_id list_update_same_conv map_update)
       qed

      have
        RedBplHavoc: "red_ast_bpl P ctxt (?\<gamma>pre, Normal nspre) ((BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre), Normal ?nshavoc)"
        unfolding \<open>cs_pre = _\<close>
      proof (rule red_ast_bpl_havoc_list, simp add: \<open>rtype_interp ctxt = _\<close>)   
        show "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) ys_bpl (map val_rel_vpr_bpl v_rets)"
          using YsBplCorrectTypes
          by simp
      qed

     have "ran var_tr'' = set xs_bpl \<union> set ys_bpl"
       using LengthEqs map_upds_ran_distinct
       unfolding \<open>var_tr'' = _\<close>
       by (simp add: map_upds_upt_ran)

     from \<open>?RCall \<omega>pre nspre\<close> have
       "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>var_translation := var_tr'\<rparr>)
          (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))) ctxt \<omega>pre nspre"
       apply (rule state_rel_aux_pred_remove)
       apply (rule map_upd_set_subset)
        apply blast
       using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
      by blast

     hence
      "?RCallPost \<omega>havoc ?nshavoc"
     proof (rule state_rel_store_update[where ?f=var_tr''])
       fix x
       assume "x \<notin> ran var_tr''"
       hence "x \<notin> set ys_bpl"
         using \<open>ran var_tr'' = _\<close>
         by blast

       thus "lookup_var (var_context ctxt) nspre x = 
             lookup_var (var_context ctxt) (update_var_list (var_context ctxt) nspre ys_bpl (map val_rel_vpr_bpl v_rets)) x"
         using lookup_update_var_list_other LengthEqs
         by (metis "*")
     next
       show "store_rel (type_interp ctxt) (var_context ctxt) var_tr'' \<omega>havoc ?nshavoc"
       proof (rule store_relI)
         show "inj_on var_tr'' (dom var_tr'')"
         proof -
           have *: "distinct (xs_bpl @ ys_bpl)"
             using \<open>distinct xs_bpl\<close> \<open>distinct ys_bpl\<close> \<open>set xs_bpl \<inter> set ys_bpl = {}\<close>
                   distinct_append
             by blast

           thus ?thesis
             using LengthEqs inj_on_upt_distinct[OF *]
             unfolding \<open>var_tr'' = _\<close>
             by simp
         qed        
       next
         fix var_vpr var_bpl
         assume VarTrSome: "var_tr'' var_vpr = Some var_bpl"

         with \<open>var_tr'' = _\<close>
         have "var_vpr \<in> dom [[0..<length es + length ys] [\<mapsto>] xs_bpl @ ys_bpl]"
           by (fastforce intro: domI)
         hence "var_vpr < length es + length ys"
           using map_upds_dom LengthEqs
           by simp

         hence "var_vpr = [0..<length es + length ys] ! var_vpr"
           by simp

         from VarTrSome \<open>var_tr'' = _\<close> 
         have VarBplEqNth: "var_bpl = (xs_bpl @ ys_bpl) ! var_vpr"
           using LengthEqs \<open>var_vpr < length es + length ys\<close>
                 map_upds_distinct_nth[OF distinct_upt \<open>var_vpr = _\<close>, where ?m=Map.empty and ?ys="xs_bpl @ ys_bpl"]
           by force

         have HavocStoreVprLookupAux: "get_store_total \<omega>havoc var_vpr = Some ((v_args @ v_rets) ! var_vpr)"
           unfolding \<open>\<omega>havoc = _\<close>
             apply (simp add: shift_and_add_list_alt_lookup)
             using \<open>var_vpr < _\<close> LengthEqs
             by (simp add: \<open>length ys_bpl = length v_rets\<close>)

         show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega>havoc ?nshavoc var_vpr var_bpl"
         proof (cases "var_vpr < length es")
           case True
             \<comment>\<open>Prove facts properties \<^term>\<open>var_bpl\<close>\<close>
             hence "var_bpl = xs_bpl ! var_vpr"
               using VarBplEqNth LengthEqs
               by (simp add: nth_append) 
             hence "var_bpl \<in> set xs_bpl"
               using LengthEqs True
               by simp
             hence LookupVarBplAux: "lookup_var (var_context ctxt) ?nshavoc var_bpl = lookup_var (var_context ctxt) nspre var_bpl"
               using \<open>set xs_bpl \<inter> set ys_bpl = {}\<close> lookup_update_var_list_other LengthEqs
               by (metis Int_iff empty_iff length_map)

             have "var_tr' var_vpr = Some (xs_bpl ! var_vpr)"
             proof -
               have *: "var_vpr = [0..<length es] ! var_vpr"
                 using True
                 by simp
               show ?thesis
               unfolding \<open>var_tr' = _\<close>
               using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys="xs_bpl"]
                     LengthEqs True
               by fastforce
             qed

             with state_rel_store_rel[OF \<open>?RCall \<omega>pre nspre\<close>] 
             obtain ty_bpl where
                  VarBplValRel: "lookup_var (var_context ctxt) nspre var_bpl = Some (val_rel_vpr_bpl (the (get_store_total \<omega>pre var_vpr)))" and
                  LookupTyVarBpl: "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl" and
                  TypeOfValRel:  "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (the (get_store_total \<omega>pre var_vpr))) = ty_bpl"
               using \<open>var_bpl = xs_bpl ! var_vpr\<close>
               unfolding store_rel_def
               by fastforce

             from RedExhPre have \<comment>\<open>exhale does not change the store\<close>
                 StorePreVprEq: "get_store_total \<omega>pre = shift_and_add_list_alt Map.empty v_args"
               using exhale_only_changes_total_state
               by fastforce               
                 
             hence StorePreVprEqLookup: "get_store_total \<omega>pre var_vpr = Some (v_args ! var_vpr)"
               using True LengthEqs
               by (simp add: shift_and_add_list_alt_lookup_1)

             show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega>havoc ?nshavoc var_vpr var_bpl"
               unfolding store_var_rel_aux_def
             proof ( (rule exI)+, intro conjI, rule HavocStoreVprLookupAux)
               from StorePreVprEqLookup
               show "lookup_var (var_context ctxt) ?nshavoc var_bpl =
                     Some (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr))" 
               using VarBplValRel LookupVarBplAux True LengthEqs
               by (simp add: nth_append)
             next
               show "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl"
                 by (rule LookupTyVarBpl)
             next
               show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr)) = ty_bpl"
                 using TypeOfValRel StorePreVprEqLookup LengthEqs
                 by (metis True nth_append option.sel)
             qed
         next
           case False
           hence VarVprLength: "var_vpr \<ge> length es \<and> var_vpr < length es + length ys"
             using \<open>var_vpr < _\<close>
             by simp

           hence "(xs_bpl @ ys_bpl) ! var_vpr = ys_bpl ! (var_vpr - length xs_bpl)"
             using LengthEqs
             by (simp add: nth_append)

           hence VarBplYsBplNth: "var_bpl = ys_bpl ! (var_vpr - length xs_bpl)" (is "_ = _ ! ?id_bpl")
             using \<open>var_bpl  = _\<close>
             by blast

           hence "var_bpl \<in> set ys_bpl"
             using VarVprLength LengthEqs
             by fastforce

           from VarBplYsBplNth obtain t_bpl where 
              LookupDeclVarBpl: 
                  "vpr_to_bpl_ty TyRep ((rets mdecl) ! ?id_bpl) = Some t_bpl \<and> 
                   lookup_var_decl (var_context ctxt) var_bpl = Some (t_bpl, None)"
             using list_all2_nthD[OF LookupDeclRetsBpl] VarVprLength LengthEqs
             by fastforce

           have *: "((v_args @ v_rets) ! var_vpr) = v_rets ! (var_vpr - length xs_bpl)" (is "_ = ?val_vpr")
             using LengthEqs VarVprLength
             by (simp add: nth_append)

           have "?id_bpl < length ys_bpl"
             using VarVprLength LengthEqs
             by linarith

           show ?thesis
             unfolding store_var_rel_aux_def
           proof ((rule exI)+, intro conjI, rule HavocStoreVprLookupAux)
             show "lookup_var (var_context ctxt) ?nshavoc var_bpl = Some (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr))" (is "?lhs = ?rhs")
             proof -

               have "?lhs = [ ys_bpl [\<mapsto>] (map val_rel_vpr_bpl v_rets) ] var_bpl"
                 apply (rule lookup_update_var_list_same[ OF \<open>var_bpl \<in> _\<close> ])
                 using LengthEqs
                 by simp
               also have "... = Some ((map val_rel_vpr_bpl v_rets) ! (var_vpr - length xs_bpl))"
                 apply (rule map_upds_distinct_nth)
                 using \<open>distinct ys_bpl\<close>
                    apply simp
                   apply (simp add: VarBplYsBplNth)
                 using LengthEqs VarVprLength
                  apply fastforce
                 using LengthEqs
                 by simp

               finally show ?thesis                 
                 using * VarVprLength LengthEqs nth_map
                 by fastforce                 
             qed
           next
             show "lookup_var_ty (var_context ctxt) var_bpl = Some t_bpl"
               using LookupDeclVarBpl
               by (simp add: lookup_var_decl_ty_Some)
           next         
             from YsBplCorrectTypes
             have "lookup_var_decl (var_context ctxt) (ys_bpl ! ?id_bpl) = Some (type_of_val (type_interp ctxt) (val_rel_vpr_bpl ?val_vpr), None)"
               using \<open>?id_bpl < _\<close>
               by (simp add: list_all2_conv_all_nth rev_map)

             hence "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ?val_vpr) = t_bpl" 
               using LookupDeclVarBpl VarBplYsBplNth
               by simp

             thus "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr)) = t_bpl"
               using *
               by simp
           qed
         qed
       qed
     next
       note aux_disj_thms = var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] 
              \<open>set xs_bpl \<subseteq> _\<close> \<open>set ys_bpl \<subseteq> _\<close> \<open>ran var_tr'' = _\<close>
       show "ran var_tr'' \<inter>
            ({heap_var (Tr\<lparr>var_translation := var_tr'\<rparr>), heap_var_def (Tr\<lparr>var_translation := var_tr'\<rparr>)} \<union>
             {mask_var (Tr\<lparr>var_translation := var_tr'\<rparr>), mask_var_def (Tr\<lparr>var_translation := var_tr'\<rparr>)} \<union>
             ran (field_translation (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<union>
             range (const_repr (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<union>
             dom (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl))
                   (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x))))) = {}"
         apply simp
         apply (intro conjI)

         using aux_disj_thms
             apply blast
         using aux_disj_thms
            apply blast
         using aux_disj_thms
           apply blast
         using aux_disj_thms
          apply blast
         using aux_disj_thms
         by (auto simp add: map_upd_set_dom)
     next 
       have "StateCons_t (get_total_full \<omega>pre)"
       proof -
         have "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr'\<rparr>))"
           by (simp add: ConsistencyEnabled)
         with state_rel_consistent[OF \<open>?RCall \<omega>pre nspre\<close>]  WfConsistency 
         show ?thesis
           unfolding wf_total_consistency_def
           by blast
       qed                  

       show "StateCons \<omega>havoc"
         unfolding \<open>\<omega>havoc = _\<close>
         apply (rule total_consistencyI[OF WfConsistency])
          apply (simp add: \<open>StateCons_t (get_total_full \<omega>pre)\<close>)          
         apply simp
         by (fastforce  split: if_split_asm intro: \<open>StateCons_t (get_total_full \<omega>)\<close> )         
     next
       fix x
       assume "map_of (snd (var_context ctxt)) x \<noteq> None"
       thus "global_state ?nshavoc x = global_state nspre x"
         using global_state_update_var_list_local 
         by blast
     next
       show "old_global_state ?nshavoc = old_global_state nspre"
         by (simp add: update_var_list_old_global_state_same)
     next
       show "binder_state ?nshavoc = Map.empty"
         using state_rel_state_well_typed[OF \<open>?RCall \<omega>pre nspre\<close>, simplified state_well_typed_def]
         by (simp add: update_var_list_binder_state_same)
     qed (simp_all add: \<open>\<omega>havoc = _\<close>)

     have PostFramed: "assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega>havoc"       
      proof -
        \<comment>\<open>We know that the postcondition is framed w.r.t. the precondition. More precisely, the assumption
           tells us that \<^emph>\<open>if\<close> the precondition is normally inhaled from an empty state \<^term>\<open>\<omega>_empty\<close> to reach \<^term>\<open>\<omega>inh\<close>, then the postcondition
           is framed in any well-typed state whose store is the same as \<^term>\<open>get_store_total \<omega>_empty\<close> and whose old state is given 
           by \<^term>\<open>\<omega>inh\<close>.

           We first show that we can inhale the precondition from an empty state to reach \<^term>\<open>RNormal (?\<omega>0 \<ominus> \<omega>pre)\<close>
           using the fact that the precondition was successfully exhaled from \<^term>\<open>?\<omega>0\<close> to reach \<^term>\<open>\<omega>pre\<close>.
           From this, we will then learn that the postcondition is framed in
           \<^term>\<open>\<omega>havoc \<lparr> get_trace_total := [old_label \<mapsto> get_total_full (?\<omega>0 \<ominus> \<omega>pre)] \<rparr> \<close>.
           From this we conclude the proof with a monotonicity argument (using that 
           \<^prop>\<open>get_total_full ?\<omega>0 \<succeq> get_total_full (?\<omega>0 \<ominus> \<omega>pre)\<close>)\<close>        

        let ?\<omega>0_rets =  "?\<omega>0\<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"
        let ?\<omega>0_rets_empty = "?\<omega>0\<lparr>   get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets),
                                      get_total_full := (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>"         

        let ?\<omega>pre_rets = "\<omega>pre \<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"
        from (*\<open>red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (method_decl.pre mdecl')) ?\<omega>0 resPre\<close> *)
             RedExhPre
        obtain \<omega>pre_exh_aux where
          RedExh: "red_exhale ctxt_vpr StateCons ?\<omega>0 (method_decl.pre mdecl) ?\<omega>0 (RNormal \<omega>pre_exh_aux)"
          by (cases) auto 

        hence "?\<omega>0 \<succeq> \<omega>pre_exh_aux"
          using exhale_normal_result_smaller
          by blast

        let ?\<omega>pre_exh_aux_rets = "\<omega>pre_exh_aux\<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"

        have "?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets"
        proof -
          have TraceEq: "get_trace_total ?\<omega>0_rets = get_trace_total ?\<omega>pre_exh_aux_rets"
            using exhale_only_changes_total_state_aux[OF RedExh]
            by auto

          have *: "?\<omega>0_rets \<ge> ?\<omega>pre_exh_aux_rets"
            apply (rule less_eq_full_total_stateI)
               apply simp
            using TraceEq
              apply simp
              apply simp
            using full_total_state_succ_implies_gte[OF \<open>?\<omega>0 \<succeq> \<omega>pre_exh_aux\<close>] less_eq_full_total_stateD
            apply fastforce
            by simp
          show ?thesis 
            using full_total_state_gte_implies_succ[OF *] TraceEq
            by argo
        qed

        have StoreWellTy: "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total ?\<omega>0_rets_empty)"
          apply simp
          apply (rule vpr_store_well_typed_append)
          using MethodCallPremises
          by (auto dest: vals_well_typed_same_lengthD)
        moreover have HeapWellTy: "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full ?\<omega>0_rets_empty)"
          using state_rel_heap_var_rel[OF StateRel] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
          unfolding heap_var_rel_def
          by simp
        moreover have EmptyState: "is_empty_total_full ?\<omega>0_rets_empty"
          unfolding is_empty_total_full_def is_empty_total_def
          by auto
        moreover have "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty (RNormal (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets))"
        proof -
          have RedExhRets: "red_exhale ctxt_vpr StateCons ?\<omega>0_rets (method_decl.pre mdecl) ?\<omega>0_rets (RNormal ?\<omega>pre_exh_aux_rets)"
            apply (rule exhale_same_on_free_var[OF RedExh]) \<comment>\<open>using that the return variables do not appear in the precondition\<close>
            using StoreSameOnArgs MethodSpecSubset
            by auto

          moreover have SumDefined: "?\<omega>0_rets_empty \<oplus> (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = Some (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)"
          proof -
            have "get_h_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = get_h_total_full ?\<omega>0_rets"
            using minus_full_total_state_only_mask_different
            by blast
            hence *: "get_h_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = get_h_total_full ?\<omega>0_rets_empty"
              by simp

            show ?thesis
              apply (rule plus_full_total_state_zero_mask)
               apply (simp add: minus_full_total_state_only_mask_different)
              using *
               apply simp
              by simp
          qed
          moreover have PreFramed: "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty"
            unfolding assertion_framing_state_def \<comment>\<open>using that the precondition is self-framing\<close>
          proof (rule allI | rule impI)+
            fix res
            assume "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty res"
            with StoreWellTy HeapWellTy EmptyState
            show "res \<noteq> RFailure"
              using MethodSpecsFramed
              unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
              by blast
          qed
          moreover have ValidRes: "StateCons (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) \<and> valid_heap_mask (get_mh_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets))"
          proof (rule conjI)
            let ?\<omega>minus = "?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets"
            have gt_\<omega>minus: "?\<omega>0_rets \<succeq> ?\<omega>minus"
            using \<open>?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets\<close> minus_smaller 
            by auto

            show "StateCons ?\<omega>minus"
            proof (rule mono_prop_downwardD[OF wf_total_consistency_trace_mono_downwardD[OF WfConsistency] _ gt_\<omega>minus])
              show "StateCons ?\<omega>0_rets"
                apply (rule total_consistency_store_update[OF WfConsistency])
                using state_rel_consistent StateRelDuringCall ConsistencyEnabled
                apply fastforce
                by simp_all
            qed
          
            show "valid_heap_mask (get_mh_total_full ?\<omega>minus)"
              apply (rule valid_heap_mask_downward_mono)
               apply (rule state_rel_wf_mask_simple[OF StateRelDuringCall])
              using gt_\<omega>minus full_total_state_greater_mask 
              by fastforce
          qed
          moreover have "mono_prop_downward StateCons"
            using ConsistencyDownwardMono mono_prop_downward_ord_implies_mono_prop_downward 
            by auto
          ultimately show ?thesis
            using exhale_inhale_normal MethodSpecSubset supported_assertion_no_unfolding
            by blast
        qed
        ultimately have PostFramedAuxSmaller: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)) (get_store_total ?\<omega>0_rets)"
          using MethodSpecsFramed
          unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
          by fastforce

        have PostFramedAux: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full \<omega>) (get_store_total ?\<omega>0_rets)"
        proof -
          have "(get_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)) \<le> (get_total_full \<omega>)"
            by (metis \<open>?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets\<close> full_total_state.select_convs(3) full_total_state.update_convs(1) greater_full_total_state_total_state minus_smaller total_state_greater_equiv)
          thus ?thesis
            using vpr_postcondition_framed_mono ConsistencyDownwardMono MethodSpecSubset PostFramedAuxSmaller 
                  supported_assertion_no_unfolding
            by blast            
        qed

      show ?thesis
      unfolding assertion_framing_state_def
      proof (rule allI, rule impI)+
        let ?\<phi>havoc = "get_total_full \<omega>havoc"
        let ?\<omega>havoc2 = "\<lparr> get_store_total = get_store_total ?\<omega>0_rets, 
                          get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                          get_total_full = ?\<phi>havoc \<rparr>"

          fix res
          assume "red_inhale ctxt_vpr StateCons (method_decl.post mdecl) \<omega>havoc res"
          hence "red_inhale ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>havoc2 res"
            unfolding \<open>\<omega>havoc = _\<close>
            by auto
          moreover have "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total ?\<phi>havoc)"
            using state_rel_heap_var_rel[OF \<open>?RCallPost \<omega>havoc ?nshavoc\<close>] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
            unfolding heap_var_rel_def
            by simp
          moreover have "valid_heap_mask (get_mh_total ?\<phi>havoc)"
            using \<open>?RCallPost \<omega>havoc ?nshavoc\<close> state_rel_wf_mask_simple
            by fastforce
          ultimately show "res \<noteq> RFailure"
            using PostFramedAux
            unfolding vpr_postcondition_framed_def
            using assertion_framing_state_def 
            by (metis fun_upd_same)
        qed
      qed

      note RCallPostConj = conjI[OF \<open>?RCallPost \<omega>havoc ?nshavoc\<close> PostFramed]     

      thus ?thesis
        using RedBplHavoc
        by blast
    qed
  qed simp

  show " stmt_rel
            (\<lambda>\<omega> ns. (?RCallPost \<omega> ns) \<and>
                    assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega>)
            ?RCallPost 
            ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale (method_decl.post mdecl)) (BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre) \<gamma>'"
    using InhalePostRel
    by blast

  show "rel_general
        ?RCallPost
        (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
        (\<lambda>\<omega>_prev \<omega>'.
            (\<exists>\<omega>pre. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl)) (state_during_inhale_post_call \<omega> \<omega>pre v_args v_rets) (RNormal \<omega>_prev)) \<and>
            \<omega>' = reset_state_after_call ys v_rets \<omega> \<omega>_prev)
        (\<lambda>_. False) P ctxt \<gamma>' \<gamma>'"
  proof (rule rel_general_success_refl_2)
    fix \<omega>post nspost \<omega>reset 
    assume "?RCallPost \<omega>post nspost"
       and SuccessReset:
            "(\<exists>\<omega>pre. red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl)) (state_during_inhale_post_call \<omega> \<omega>pre v_args v_rets) (RNormal \<omega>post)) \<and>
                    \<omega>reset = reset_state_after_call ys v_rets \<omega> \<omega>post"
    note RedInhPost = conjunct1[OF SuccessReset]
    note \<omega>resetEq = conjunct2[OF SuccessReset]

    have "get_store_total \<omega>post = (shift_and_add_list_alt Map.empty (v_args@v_rets))"
    using SuccessReset inhale_only_changes_mask(3)
      by (metis RedInhale_case full_total_state.select_convs(1) sub_expressions.simps(7))

    show "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega>reset nspost"
      unfolding \<open>\<omega>reset = _\<close>
    proof -
      from \<open>?RCallPost \<omega>post nspost\<close> have
        "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>var_translation := var_tr''\<rparr>) AuxPred ctxt \<omega>post nspost"
        apply (rule state_rel_aux_pred_remove)
        apply (rule map_upd_set_subset2)
        using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
        by blast

      thus "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost"
      proof (rule state_rel_store_update[where ?f="var_translation Tr"])
        show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) 
                        (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost"
        proof (rule store_relI)
          show "inj_on (var_translation Tr) (dom (var_translation Tr))"
            using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
            by (simp add: store_rel_def)
        next
          fix var_vpr var_bpl
          assume VarTrSome: "var_translation Tr var_vpr = Some var_bpl"
          show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost var_vpr var_bpl"
          proof (cases "var_vpr \<in> set ys")
            case True
            from this obtain id where "var_vpr = ys ! id" and "id < length ys"
              by (metis in_set_conv_nth)
            hence "var_bpl = ys_bpl ! id"
              using YsBplEq VarTrSome
              by auto

            have *: "(length es + id) = [0..<length es + length ys] ! (length es + id)"
              using \<open>id < _\<close> LengthEqs
              by auto

            have "var_tr'' (length es + id) = Some var_bpl"
              using \<open>id < _\<close> LengthEqs map_upds_distinct_nth[OF distinct_upt *, 
                                                             where ?m=Map.empty and ?ys="xs_bpl @ ys_bpl"]
              unfolding \<open>var_tr'' = _\<close> \<open>var_bpl = (ys_bpl ! id)\<close>
              by (smt (verit) True add.commute add_less_cancel_right diff_less diff_zero length_append length_pos_if_in_set length_rev length_upt nth_append_length_plus rev_append zero_less_Suc)

            from this obtain val_vpr ty_bpl where
              AuxStoreRel:
               "get_store_total \<omega>post (length es + id) = Some val_vpr \<and>
               lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
               lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl \<and>
               type_of_val (type_interp ctxt) (val_rel_vpr_bpl val_vpr) = ty_bpl"
              using state_rel_store_rel[OF \<open>?RCallPost \<omega>post nspost\<close>]
              unfolding store_rel_def
              by auto

            have "val_vpr = v_rets ! id"
            proof -
              have *: "(length es + id) < length (v_args @ v_rets)"
                        using \<open>id < _\<close> LengthEqs
                        by simp
              have "get_store_total \<omega>post (length es + id) = shift_and_add_list_alt Map.empty (v_args @ v_rets) (length es + id)"
                  by (simp add: \<open>get_store_total \<omega>post = _\<close>)
              also have "... = Some ((v_args @ v_rets) ! (length es + id))"
                using \<open>id < _\<close> shift_and_add_list_alt_lookup_1[OF *] 
                by blast
              also have "... = Some (v_rets ! id)"
                using LengthEqs
                by fastforce
              finally show ?thesis
                using AuxStoreRel
                by auto  
            qed
               
            show ?thesis
            unfolding store_var_rel_aux_def
            proof ((rule exI)+, intro conjI)
              show "get_store_total (reset_state_after_call ys v_rets \<omega> \<omega>post) var_vpr = Some (v_rets ! id)"
                unfolding reset_state_after_call_def
                apply simp
                using \<open>var_vpr = _\<close> \<open>distinct ys\<close> map_upds_distinct_nth \<open>id < _\<close> LengthEqs
                by metis
            next
              show "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl (v_rets ! id))"
                using AuxStoreRel \<open>val_vpr = v_rets ! id\<close>                                           
                by simp
            next
              show "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl"
                using AuxStoreRel
                by blast
            next
              show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_rets ! id)) = ty_bpl"
                using AuxStoreRel\<open>val_vpr = v_rets ! id\<close>
                by blast
            qed
          next
            case False
            \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is not a target variable and thus we need to show that
               it still contains the same value as before the call. \<close>

            hence "var_bpl \<notin> set ys_bpl"
              using map_the_inj_not_in state_rel_var_tr_inj[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                    YsBplEq VarTrSome \<open>set ys \<subseteq> _\<close>
              by fast

            have "get_store_total (reset_state_after_call ys v_rets \<omega> \<omega>post) var_vpr = 
                   get_store_total \<omega> var_vpr"
              unfolding reset_state_after_call_def
              by (simp add: False)

            moreover have "lookup_var (var_context ctxt) nspost var_bpl = 
                           lookup_var (var_context ctxt) ns var_bpl"
            proof -
              from VarTrSome obtain v_bpl where 
                LookupVarBpl: "lookup_var (var_context ctxt) ns var_bpl = Some v_bpl"
                using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                unfolding store_rel_def
                by blast                    

              show ?thesis
              proof (cases "var_vpr \<in> set xs")
                case True
                \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is an argument variable, which means the proof
                   tracked the corresponding Boogie variable in the variable translation. Thus,
                   by showing that the Viper local store did not change during the call (except
                   for target variables), we can show that the Boogie variable was not modified either.\<close>

                have "var_bpl \<in> set xs_bpl"
                proof -
                  from \<open>var_vpr \<in> set xs\<close> obtain i where
                       "i < length xs" and "xs ! i = var_vpr"
                    by (meson in_set_conv_nth)

                  thus ?thesis
                    using XsBplEq VarTrSome LengthEqs
                    by (metis comp_eq_dest_lhs nth_map nth_mem option.sel)
                qed

                from this obtain i where "i < length xs_bpl" and "var_bpl = xs_bpl ! i"
                  by (metis in_set_conv_nth)

                hence *: "i = [0..<length es+length ys] ! i"
                  using LengthEqs
                  by fastforce

                have "var_tr'' i = Some var_bpl"
                  using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys="xs_bpl@ys_bpl"] 
                        LengthEqs
                  unfolding \<open>var_tr'' = _\<close> \<open>var_bpl = _\<close>
                  using \<open>i < _\<close>
                  by (simp add: nth_append)
                                                                                        
                with state_rel_store_rel[OF \<open>?RCallPost \<omega>post nspost\<close>] obtain val_vpr where 
                  "get_store_total \<omega>post i = Some val_vpr" and
                  "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl val_vpr)"
                  unfolding store_rel_def
                  by auto

                hence "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl (v_args ! i))"
                  unfolding \<open>get_store_total \<omega>post = _\<close>
                  using \<open>i < _\<close> LengthEqs
                  by (simp add: shift_and_add_list_alt_lookup nth_append)

                moreover from ValRelArgs have
                  "lookup_var (var_context ctxt) ns var_bpl = Some (val_rel_vpr_bpl (v_args ! i))"
                  using \<open>var_bpl = _\<close>
                  by (simp add: \<open>i < length xs_bpl\<close> list_all2_conv_all_nth)

                ultimately show ?thesis
                  by simp
              next
                case False
                \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is not an argument variable or target variable.
                   Thus, the proof tracked the corresponding Boogie variable explicitly as an 
                   auxiliary variable that must still have the same value as before the call.\<close>
                
                hence "var_bpl \<notin> set xs_bpl" 
                  using map_the_inj_not_in state_rel_var_tr_inj[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                        XsBplEq VarTrSome \<open>set xs \<subseteq> _\<close>
                  by fast
                                       
                have *: "map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl))
                         ?fpred var_bpl = Some (?fpred var_bpl)"
                  apply (rule map_upd_set_lookup_1)
                  using \<open>var_bpl \<notin> set xs_bpl\<close> \<open>var_bpl \<notin> set ys_bpl\<close> VarTrSome
                        ranI
                  by fast

                thus ?thesis
                  using state_rel_aux_pred_sat_lookup[OF \<open>?RCallPost \<omega>post nspost\<close> *]
                        LookupVarBpl
                  unfolding pred_eq_def
                  by (simp add: has_Some_iff)
                qed                   
              qed
              ultimately show ?thesis
              using VarTrSome state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
              unfolding store_var_rel_aux_def store_rel_def
              by presburger                    
          qed
        qed
      next
        have "StateCons_t (get_total_full \<omega>post)"
        proof -
          have "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr''\<rparr>))"
            by (simp add: ConsistencyEnabled)

          with \<open>?RCallPost \<omega>post _\<close> state_rel_consistent WfConsistency 
          show ?thesis
          unfolding wf_total_consistency_def                
          by blast
        qed

        show "StateCons (reset_state_after_call ys v_rets \<omega> \<omega>post)"
          unfolding reset_state_after_call_def
          apply (rule total_consistencyI[OF WfConsistency])
           apply (simp add: \<open>StateCons_t (get_total_full \<omega>post)\<close>)                 
          using state_rel_consistent[OF StateRel] WfConsistency ConsistencyEnabled
          unfolding wf_total_consistency_def
          by simp
      next
        show "binder_state nspost = Map.empty"
          using state_rel_state_well_typed[OF \<open>?RCallPost \<omega>post nspost\<close>, simplified state_well_typed_def]
          by simp
      next
        show "ran (var_translation Tr) \<inter>
             ({heap_var (Tr\<lparr>var_translation := var_tr''\<rparr>), heap_var_def (Tr\<lparr>var_translation := var_tr''\<rparr>)} \<union>
              {mask_var (Tr\<lparr>var_translation := var_tr''\<rparr>), mask_var_def (Tr\<lparr>var_translation := var_tr''\<rparr>)} \<union>
              ran (field_translation (Tr\<lparr>var_translation := var_tr''\<rparr>)) \<union>
              range (const_repr (Tr\<lparr>var_translation := var_tr''\<rparr>)) \<union>
              dom AuxPred) =
             {}"
          using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
          by simp
      qed (simp_all add: reset_state_after_call_def)              
    qed
  qed (simp)
qed

subsection \<open>Scoped variable\<close>

\<comment> \<open>TODO: general rule that is independent from \<^term>\<open>state_rel\<close>\<close>

lemma scoped_var_stmt_rel:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and StateRelImp: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and DomainTyRep: "domain_type TyRep = (absval_interp_total ctxt_vpr)"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and RtypeInterpEmpty: "rtype_interp ctxt = []"
      and RedToHavocBpl: "red_ast_bpl_rel R R P ctxt \<gamma> (BigBlock name (Havoc x_bpl # cs) str tr, cont)" (is "red_ast_bpl_rel R R P ctxt \<gamma> ?\<gamma>_havoc")
      and DisjBpl: "x_bpl \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred"
      and LookupDeclNewVarBpl: "lookup_var_decl (var_context ctxt) x_bpl = Some (\<tau>_bpl, None)"
      and VprToBplTy: "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl"
      and "var_tr' = shift_and_add (var_translation Tr) x_bpl"
      and StmtRelBody:
          "stmt_rel (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) AuxPred ctxt) 
                    (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) AuxPred ctxt) 
                    ctxt_vpr StateCons (shift_and_add \<Lambda>_vpr \<tau>_vpr) P ctxt s_body (BigBlock name cs str tr, cont) \<gamma>'"
    shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Scope \<tau>_vpr s_body) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and
         RedStmtVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Scope \<tau>_vpr s_body) \<omega> res"    

  from RedStmtVpr obtain res_body v where 
        NewValTy: "get_type (absval_interp_total ctxt_vpr) v = \<tau>_vpr"
    and RedBodyVpr: "red_stmt_total ctxt_vpr StateCons (shift_and_add \<Lambda>_vpr \<tau>_vpr) s_body (shift_and_add_state_total \<omega> v) res_body"
    and ResEqUnshift: "res = map_stmt_result_total (unshift_state_total (Suc 0)) res_body"
    by (auto elim: RedScope_case)

  from \<open>R \<omega> ns\<close> RedToHavocBpl obtain ns' where 
    RedBpl1: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>_havoc, Normal ns')" and "R \<omega> ns'"
    unfolding red_ast_bpl_rel_def
    by blast

  let ?v_bpl = "val_rel_vpr_bpl v"
  let ?\<omega>_v = "shift_and_add_state_total \<omega> v"
  let ?ns'_v = "update_var (var_context ctxt) ns' x_bpl ?v_bpl"  
  let ?R' = "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt"
  let ?var_tr = "var_translation Tr"

  from vpr_to_bpl_val_type NewValTy VprToBplTy DomainTyRep 
  have TyBpl: "type_of_vbpl_val TyRep ?v_bpl = \<tau>_bpl"
    by blast

  have "red_ast_bpl P ctxt (?\<gamma>_havoc, Normal ns') ((BigBlock name cs str tr, cont), Normal ?ns'_v)"
    apply (rule red_ast_bpl_one_havoc[OF LookupDeclNewVarBpl])
    using TypeInterp TyBpl RtypeInterpEmpty
     apply force
    by simp
  with RedBpl1 have RedAstBpl2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) ((BigBlock name cs str tr, cont), Normal ?ns'_v)"
    using red_ast_bpl_transitive
    by blast

  note StateRel_ns' = StateRelImp[OF \<open>R \<omega> ns'\<close>]

  from StateRel_ns'
  have StateRelBody: "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) AuxPred ctxt ?\<omega>_v ?ns'_v"
  proof (rule state_rel_store_update, simp)
    let ?\<omega>' = "shift_and_add_state_total \<omega> v"

    from \<open>x_bpl \<notin> _\<close> have "x_bpl \<notin> ran ?var_tr"
      by blast

    show "store_rel (type_interp ctxt) (var_context ctxt) var_tr' ?\<omega>' ?ns'_v"
      unfolding shift_1_shift_and_add_total shift_1_shift_and_add \<open>var_tr' = _\<close> 
    proof (rule store_rel_add_new_var)
      show "store_rel (type_interp ctxt) (var_context ctxt) (DeBruijn.shift 1 (var_translation Tr)) (shift_state_total 1 \<omega>) ns'"
        apply (rule store_rel_shift)
        by (rule state_rel_store_rel[OF StateRel_ns'])
    next
      show "lookup_var_ty (var_context ctxt) x_bpl = Some \<tau>_bpl"
        using LookupDeclNewVarBpl
        by (simp add: lookup_var_decl_ty_Some)
    next
      show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = \<tau>_bpl"
        using TyBpl TypeInterp
        by simp
    next
      show "x_bpl \<notin> ran (DeBruijn.shift 1 (var_translation Tr))"
        using \<open>x_bpl \<notin> ran _\<close> ran_shift
        by fast       
    qed (insert DisjBpl, auto)

    show "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<Longrightarrow> StateCons (shift_and_add_state_total \<omega> v)"
      using WfConsistency state_rel_consistent[OF StateRelImp[OF \<open>R \<omega> ns'\<close>]]
      unfolding wf_total_consistency_def
      by simp

    show "\<And>x. x \<notin> ran var_tr' \<Longrightarrow>
         lookup_var (var_context ctxt) ns' x = lookup_var (var_context ctxt) ?ns'_v x"
        (is "\<And>x. _ \<Longrightarrow> ?Goal x")
      unfolding \<open>var_tr' = _\<close> shift_and_add_def
      by (metis fun_upd_same ranI update_var_other)

    show "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ?ns'_v x = global_state ns' x"
      by (metis LookupDeclNewVarBpl global_state_update_local global_state_update_other lookup_var_decl_local_2)

    show "old_global_state ?ns'_v = old_global_state ns'"
      using update_var_old_global_same by blast

    show "binder_state ?ns'_v = Map.empty"
      using state_rel_state_well_typed[OF StateRel_ns', simplified state_well_typed_def]
      by (simp add: update_var_binder_same)

    show "ran var_tr' \<inter> ({heap_var Tr, heap_var_def Tr} \<union> {mask_var Tr, mask_var_def Tr} \<union> ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred) = {}"
    proof -
      have "ran (shift_and_add (var_translation Tr) x_bpl) = ran (var_translation Tr) \<union> {x_bpl}"
        using ran_shift_and_add
        by metis
      thus ?thesis
        unfolding \<open>var_tr' = _\<close> 
        using DisjBpl var_translation_disjoint[OF StateRel_ns']
        by force
    qed
  qed (auto)

  show "rel_vpr_aux ?R' P ctxt \<gamma> \<gamma>' ns res"
  proof (rule rel_vpr_aux_intro)
    \<comment>\<open>Normal case\<close>
    fix \<omega>'
    assume "res = RNormal \<omega>'"
    with ResEqUnshift obtain \<omega>_body where 
      "res_body = RNormal \<omega>_body"
      "\<omega>' = unshift_state_total (Suc 0) \<omega>_body"
      by (blast elim: map_stmt_result_total.elims)

                        
    with RedBodyVpr stmt_rel_normal_elim[OF StmtRelBody StateRelBody]
    obtain ns_body where
     "red_ast_bpl P ctxt ((BigBlock name cs str tr, cont), Normal ?ns'_v) (\<gamma>', Normal ns_body)" and
     StateRelBodyEnd: "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>var_translation := var_tr'\<rparr>) AuxPred ctxt \<omega>_body ns_body"
      by blast
 
    moreover have "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega>' ns_body"
    proof (rule state_rel_store_update[OF StateRelBodyEnd, where ?f = ?var_tr])
      show "store_rel (type_interp ctxt) (var_context ctxt) ?var_tr \<omega>' ns_body"
      proof -
        have VarTrEq: "?var_tr = unshift_2 (Suc 0) var_tr'"
          unfolding \<open>var_tr' = _\<close> 
          using unshift_shift_and_add_id
          by metis
        show ?thesis
          unfolding \<open>\<omega>' = _\<close> VarTrEq
          apply (rule store_rel_unshift)
          using state_rel_store_rel[OF StateRelBodyEnd]
          by simp
      qed

      show "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>'" (is "?ConsOpt \<Longrightarrow> _")
      proof -
        assume ?ConsOpt
        hence "StateCons \<omega>"
          using state_rel_consistent[OF StateRel_ns']
          by simp
        thus ?thesis
          using WfConsistency RedStmtVpr \<open>res = RNormal \<omega>'\<close>
          unfolding wf_total_consistency_def
          by blast
      qed

      show "binder_state ns_body = Map.empty"
        using state_rel_state_well_typed[OF StateRelBodyEnd, simplified state_well_typed_def]
        by (simp add: update_var_binder_same)

    qed (insert \<open>\<omega>' = _\<close>, insert var_translation_disjoint[OF StateRel_ns'],  auto)

    ultimately show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> ?R' \<omega>' ns'"
      using RedAstBpl2 red_ast_bpl_transitive
      by blast
  next
    \<comment>\<open>Failure case\<close>
    assume "res = RFailure"
    with ResEqUnshift have "res_body = RFailure"
      by (blast elim: map_stmt_result_total.elims)

    with RedBodyVpr stmt_rel_failure_elim[OF StmtRelBody StateRelBody] 
    obtain \<gamma>fail where
      RedAstBplFail: "red_ast_bpl P ctxt ((BigBlock name cs str tr, cont), Normal ?ns'_v) (\<gamma>fail, Failure)"
      by auto

    show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
      apply (rule exI, rule conjI)
       apply (rule red_ast_bpl_transitive[OF RedAstBpl2 RedAstBplFail])
      by simp            
  qed
qed

schematic_goal "?Tr = 
         (Tr \<lparr> var_translation := (shift_and_add Map.empty a) \<rparr> ) \<lparr> var_translation := 
             shift_and_add (var_translation (Tr \<lparr> var_translation := (shift_and_add Map.empty a) \<rparr> )) b\<rparr>"
  by simp

schematic_goal
  "?Tr = ((Tr \<lparr> var_translation := Tr1 \<rparr> )\<lparr> var_translation := Tr2 \<rparr> ) \<lparr> var_translation := Tr3 \<rparr>"
  by simp

text \<open>The following lemma is semantically equivalent to the previous one. This lemma phrases one the premises 
      in a way that allows natural simplification of the translation record term.\<close>

lemma scoped_var_stmt_rel_simplify_tr:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and DomainTyRep: "domain_type TyRep = (absval_interp_total ctxt_vpr)"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and RtypeInterpEmpty: "rtype_interp ctxt = []"
      and StateRelImp: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and RedToHavocBpl: "red_ast_bpl_rel R R P ctxt \<gamma> (BigBlock name (Havoc x_bpl # cs) str tr, cont)" (is "red_ast_bpl_rel R R P ctxt \<gamma> ?\<gamma>_havoc")
      and DisjBpl: "x_bpl \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred"
      and LookupDeclNewVarBpl: "lookup_var_decl (var_context ctxt) x_bpl = Some (\<tau>_bpl, None)"
      and VprToBplTy: "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl"
 \<comment>\<open>The purpose of the following premise is to allow for simplification of the translation record term.
    This avoids unnecessary updates in the term (such as consescutive var_translation updates)\<close>
      and "Tr' = (Tr\<lparr> var_translation := shift_and_add (var_translation Tr) x_bpl \<rparr>)"
      and StmtRelBody:
          "stmt_rel (state_rel_def_same Pr StateCons TyRep Tr' AuxPred ctxt) 
                    (state_rel_def_same Pr StateCons TyRep Tr' AuxPred ctxt) 
                    ctxt_vpr StateCons (shift_and_add \<Lambda>_vpr \<tau>_vpr) P ctxt s_body (BigBlock name cs str tr, cont) \<gamma>'"
        shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Scope \<tau>_vpr s_body) \<gamma> \<gamma>'"
  apply (rule scoped_var_stmt_rel)
  using assms
  by auto

subsection \<open>Misc\<close>

lemma exp_rel_true_imp_1:
  assumes  "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
  shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (Binop (ELit (ViperLang.LBool True)) BImp e_vpr) e_bpl"
proof (rule exp_rel_equiv_vpr[OF _ assms])
  fix v1 StateCons \<omega> \<omega>_def_opt
  assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>Binop (ELit (ViperLang.LBool True)) BImp e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  thus "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  proof (rule RedBinop_case)
    fix v1a contra
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ELit (ViperLang.lit.LBool True);\<omega>\<rangle> [\<Down>]\<^sub>t Val v1a"
    hence "v1a = VBool True"
      by (metis TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(1))
    assume "eval_binop_lazy v1a BImp = Some v1"
    thus contra using \<open>v1a = _\<close>
      by simp
  next
    fix v1a v2
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ELit (ViperLang.lit.LBool True);\<omega>\<rangle> [\<Down>]\<^sub>t Val v1a"
    hence "v1a = VBool True"
      by (metis TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(1))
    assume "eval_binop v1a BImp v2 = BinopNormal v1"
    hence "v2 = v1"
      unfolding \<open>v1a = _\<close>
      by (rule eval_binop.elims) auto
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
    thus "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      by (simp add: \<open>v2 = v1\<close>)
  qed
qed


  
end