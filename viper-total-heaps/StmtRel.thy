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
                       vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, []) \<and>
                       R (update_hh_loc_total_full \<omega> (addr,f_vpr) v)
                         (update_var (var_context ctxt) ns h_bpl
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         ))"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
         \<gamma>
         (BigBlock name cs str tr, cont)" 
proof (rule stmt_rel_intro)
  let ?\<gamma>3="((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)"
  let ?Rext = "rel_ext_eq R"
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
  hence "?Rext \<omega> \<omega> ns" by simp

  assume RedStmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> (RNormal \<omega>')"

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) ((BigBlock name cs str tr, cont), Normal ns') \<and> R \<omega>' ns'"
  proof cases
    case (RedFieldAssign addr v ty_vpr)
    from this obtain ns1 where
      "?Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
      by auto
    from this RedFieldAssign obtain ns2 where "?Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast
    from this RedFieldAssign obtain ns3 where "?Rext \<omega> \<omega> ns3" and RedNs3: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>3, Normal ns3)" 
      using wf_rel_normal_elim[OF WriteableLocRel] red_ast_bpl_transitive
      by blast
    hence "R \<omega> ns3" by simp

    have "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl"         
      using \<open>declared_fields _ f_vpr = Some ty_vpr\<close> DeclaredFieldsSome
      by simp
 
   moreover have NewValTypeBpl: "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
     using vpr_to_bpl_val_type[OF \<open>get_type _ v = ty_vpr\<close> \<open>vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl\<close>]
           \<open>domain_type _ = _\<close>
     by simp

   moreover from RedStmt have "StateConsEnabled \<Longrightarrow> StateCons \<omega>'"
     using total_consistency_red_stmt_preserve[OF WfConsistency] Consistent[OF _ \<open>R \<omega> ns\<close>]
     by simp

   moreover from RedFieldAssign DomainTypeEq have "get_type (domain_type TyRep) v = \<tau>_vpr"
     using DeclaredFieldsSome
     by force

   ultimately obtain hb f_bpl_val
     where 
           LookupTyHeapBpl: "lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep))" and
           LookupHeapVarBpl: "lookup_var (var_context ctxt) ns3  h_bpl = Some (AbsV (AHeap hb))" and
           HeapWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
           HeapUpdWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, [])" and
           LookupFieldVarBpl: "lookup_var (var_context ctxt) ns3 f_bpl = Some (AbsV (AField f_bpl_val))" and           
           FieldTyBpl: "field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [\<tau>_field_bpl, \<tau>_bpl])" and
           "R \<omega>'
                   (update_var (var_context ctxt) ns3 h_bpl
                   (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
             )" (is "R _ ?ns_upd")
     using RFieldAssign[OF \<open>R \<omega> ns3\<close>] \<open>\<omega>' = _\<close>           
     by metis

   from RcvRel have RedRcvBpl: "red_expr_bpl ctxt rcv_bpl ns3 (AbsV (ARef (Address addr)))"
     using \<open>?Rext \<omega> \<omega> ns3\<close>  RedFieldAssign exp_rel_vpr_bpl_elim
     by (metis (mono_tags, lifting) val_rel_vpr_bpl.simps(3))

   from RhsRel have RedRhsBpl: "red_expr_bpl ctxt rhs_bpl ns3 (val_rel_vpr_bpl v)" 
     using \<open>?Rext \<omega> \<omega> ns3\<close>  RedFieldAssign exp_rel_vpr_bpl_elim
     by (metis (mono_tags, lifting))

   from HeapUpdWf have 
      RedHeapUpdBpl:
     "red_expr_bpl ctxt (heap_upd_bpl (Lang.Var h_bpl) rcv_bpl (Lang.Var f_bpl) rhs_bpl [\<tau>_field_bpl, \<tau>_bpl])
                             ns3 (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))"
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

   have "red_ast_bpl P ctxt 
           ((BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont), Normal ns3) 
           ((BigBlock name cs str tr, cont), Normal ?ns_upd)"
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (rule Semantics.RedAssign)
       apply (fastforce intro!: LookupTyHeapBpl)
     using HeapUpdWellTyBpl \<open>type_interp ctxt = _\<close>
      apply simp
     by (fastforce intro: RedHeapUpdBpl simp: \<open>h_upd_bpl = _\<close>)
    thus ?thesis
      using RedNs3 \<open>R \<omega>' ?ns_upd\<close>
      using red_ast_bpl_transitive by blast      
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
    from this obtain ns1 where
      "?Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
      by auto      
    from this RedFieldAssignFailure obtain ns2 where "?Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast

    with RedFieldAssignFailure obtain \<gamma>' where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
      using wf_rel_failure_elim[OF WriteableLocRel \<open>?Rext \<omega> \<omega> ns2\<close>] red_ast_bpl_transitive
      by (metis (no_types, opaque_lifting) ref.exhaust ref.sel snd_conv surj_pair)
    thus ?thesis
      by (meson snd_conv)
  next
    case RedSubExpressionFailure
    hence RedSubExpFailureAux: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) [rcv_vpr, rhs_vpr] \<omega> None"
      by simp
    show ?thesis
    proof (cases  "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure")
      case True
      then show ?thesis 
        using wf_rel_failure_elim[OF RcvWfRel \<open>?Rext \<omega> \<omega> ns\<close>]
        by blast
    next
      case False
      from this obtain v where "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
                               "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rhs_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
        using RedSubExpFailureAux
        by (auto elim: red_pure_exp_total_elims)
      then show ?thesis 
        using wf_rel_normal_elim[OF RcvWfRel \<open>?Rext \<omega> \<omega> ns\<close>] wf_rel_failure_elim[OF RhsWfRel] red_ast_bpl_transitive
        by blast
    qed
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
                        vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, []) \<and>
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
          WellDefSame: "heap_var Tr = heap_var_def Tr \<and> mask_var Tr = mask_var_def Tr" and 
          "id_on_known_locs_name = FunMap FIdenticalOnKnownLocs" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          "StateCons \<omega>'" and
          "\<omega>' \<in> havoc_locs_state ctxt_vpr \<omega> ({loc. get_mh_total_full (\<omega>0 ) loc > 0 \<and> get_mh_total_full \<omega> loc = 0})" and
          "hvar = heap_var Tr" and
          "mvar = mask_var Tr" and
          LookupDeclExhaleHeap: "lookup_var_decl (var_context ctxt) hvar_exh = Some (TConSingle (THeapId TyRep), None)" and
          ExhaleHeapFresh: "hvar_exh \<notin> state_rel0_disj_vars Tr AuxPred"                           
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
        apply simp
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
      using WellDefSame
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
    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>') ?ns2"
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
      and ResetState: "rel_general (uncurry Rexh) (\<lambda>\<omega> ns. R (snd \<omega>) ns) 
                                   (\<lambda> \<omega>1 \<omega>2. snd \<omega>2 = fst \<omega>1 \<and>
                                             red_exhale ctxt_vpr StateCons (fst \<omega>1) A (fst \<omega>1) (RNormal (snd \<omega>1))) 
                                   (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'
                      \<or> red_ast_bpl_rel R R P ctxt \<gamma> \<gamma>'"
                 (is "?ResetFromExhale \<or> ?ResetFromStart")
    shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.Assert A) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" and RedStmt: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.Assert A) \<omega> res"
    
  show "rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res"
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
    show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
    proof (cases)
      case 1
      with rel_success_elim[OF 1] \<open>Rexh \<omega> \<omega>_exh ns_exh\<close> 
      obtain ns' where "red_ast_bpl P ctxt (\<gamma>2, Normal ns_exh) (\<gamma>', Normal ns')" and "R \<omega> ns'"
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
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)"
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
    
    show "store_rel (type_interp ctxt) (var_context ctxt) var_tr' (get_store_total ?\<omega>') ?ns'_v"
      unfolding shift_1_shift_and_add_total shift_1_shift_and_add \<open>var_tr' = _\<close>       
    proof (simp del: One_nat_def, rule store_rel_add_new_var)      
      show "store_rel (type_interp ctxt) (var_context ctxt) (DeBruijn.shift 1 (var_translation Tr)) (DeBruijn.shift 1 (get_store_total \<omega>)) ns'"
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

    show "ran var_tr' \<inter> ({heap_var Tr, heap_var_def Tr} \<union> {mask_var Tr, mask_var_def Tr} \<union> ran (field_translation Tr) \<union> 
                          range (const_repr Tr) \<union> dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
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
      show "store_rel (type_interp ctxt) (var_context ctxt) ?var_tr (get_store_total \<omega>') ns_body"
      proof -
        have VarTrEq: "?var_tr = unshift_2 (Suc 0) var_tr'"
          unfolding \<open>var_tr' = _\<close> 
          using unshift_shift_and_add_id
          by metis
        show ?thesis
          unfolding \<open>\<omega>' = _\<close> VarTrEq          
          using store_rel_unshift state_rel_store_rel[OF StateRelBodyEnd]
          by fastforce
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
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)"
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