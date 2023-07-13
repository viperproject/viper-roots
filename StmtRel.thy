theory StmtRel
imports ExpRel ExprWfRel InhaleRel ExhaleRel TotalSemProperties TotalViper.ViperBoogieTranslationInterface Simulation
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

subsection \<open>Propagation rules\<close>

lemma stmt_rel_propagate:
          \<comment>\<open>We could weaken this assumption by adding that success or failure must occur, but until
            now we have not required this.\<close>
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"  
  using assms
  unfolding stmt_rel_def
  using rel_propagate_pre
  by metis

lemma stmt_rel_propagate_same_rel:
  assumes "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R \<omega> ns'" and
          "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using stmt_rel_propagate assms
  by blast

lemma stmt_rel_propagate_2:
  assumes "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega> ns. R1 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega> ns'"
  shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms
  unfolding stmt_rel_def
  using rel_propagate_post
  by blast
  
lemma stmt_rel_propagate_2_same_rel:
  assumes "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega> ns'"
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
          "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr StateCons P ctxt cond 
           \<gamma>1
           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)" and
     ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl" and
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
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
    apply (metis \<open>R \<omega> ns\<close> val_rel_vpr_bpl.simps(2))
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
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
      apply (insert exp_rel_vpr_bpl_elim_2[OF ExpRel])
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

subsection \<open>Local variable assignment relation\<close>

lemma assign_rel_simple:
  assumes R_def:  "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R2 \<omega> ns)" and
          VprTy: "\<Lambda>_vpr x_vpr = Some ty" and
          TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep" and
          EmptyRtype: "rtype_interp ctxt = []" and
          ExpWfRel: "expr_wf_rel R3 ctxt_vpr StateCons P ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)" 
                    (is "expr_wf_rel R3 ctxt_vpr StateCons P ctxt e_vpr \<gamma> (?b, cont)") and
          BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl" and
          TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl" and
                    \<comment>\<open>Key assignment property for R2\<close>
          RAssign:  "\<And> \<omega> ns v . R2 \<omega> ns \<Longrightarrow>
                           get_type (absval_interp_total ctxt_vpr) v = ty \<Longrightarrow>
                           type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl \<Longrightarrow>
                           R2 (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))" and
          ExpRel: "exp_rel_vpr_bpl R3 ctxt_vpr ctxt e_vpr e_bpl"
          
        shows "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
               \<gamma>
               (BigBlock name cs str tr, cont)" (is "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma> ?\<gamma>'") 
proof (cases rule: stmt_rel_intro)
\<comment>\<open>Normal case\<close>
  fix \<omega> ns \<omega>'
  assume R: "R2 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> (RNormal \<omega>')"

  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R2 \<omega>' ns'"
  proof -
    from RedVpr obtain v where RedEVpr: "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v)" and 
                                "\<omega>' = (update_var_total \<omega> x_vpr v)" and
                                vTyVpr: "get_type (absval_interp_total ctxt_vpr) v = ty"      
      apply (rule red_stmt_total.cases)
      using VprTy
      by auto

    from this obtain ns' where
        R':"R3 \<omega> \<omega> ns'" and
        RedBplWf:"red_ast_bpl P ctxt (\<gamma>, Normal ns) ((?b, cont), Normal ns')"
      using R R_def wf_rel_normal_elim[OF ExpWfRel]
      by blast

    let ?v_bpl = "val_rel_vpr_bpl v"
    have RedEBpl:"red_expr_bpl ctxt e_bpl ns' ?v_bpl"
      apply (rule exp_rel_vpr_bpl_elim_2[OF ExpRel])
      using R' RedEVpr R_def
      by fastforce

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

    moreover have "R3 \<omega>' \<omega>' ?ns''" 
      apply (subst \<open>\<omega>' = _\<close>)+
      using R_def RAssign R' vTyVpr ValBplTy 
      by auto

    ultimately show ?thesis 
      using RedBplWf R_def \<open>\<omega>' = _\<close> red_ast_bpl_def
      by (metis (mono_tags, lifting) rtranclp_trans)
  qed
next
  \<comment>\<open>Failure case\<close>
  fix \<omega> ns 
  assume "R2 \<omega> ns" and 
         RedVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> RFailure"
  
  from RedVpr show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
  case (RedSubExpressionFailure)
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by (fastforce elim: red_pure_exps_total_singleton)

  then show ?thesis 
    using  R_def \<open>R2 \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
    by blast
  qed
qed

subsection \<open>Field assignment relation\<close>

lemma field_assign_rel:
  assumes 
    HeapUpdWf: "heap_update_wf TyRep ctxt heap_upd_bpl" and
               "domain_type TyRep = absval_interp_total ctxt_vpr" and
               "type_interp ctxt = vbpl_absval_ty TyRep" and
    Rext: "Rext = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)"  and
    RcvWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1" and
    RhsWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2" and
    WriteableLocRel: "wf_rel_fieldacc get_writeable_locs Rext Rext ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)" and 
                   "h_bpl = heap_var Tr" and
    HeapUpdateBpl: "h_upd_bpl = heap_upd_bpl (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
    RcvRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rcv_vpr rcv_bpl" and
    FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    RhsRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rhs_vpr rhs_bpl" and

    \<comment>\<open>Key field assignment property for R\<close>
    RFieldAssign:  "\<And> \<omega> ns ty_vpr hb addr  f_bpl v . R \<omega> ns \<Longrightarrow>
                     declared_fields (program_total ctxt_vpr) f_vpr = Some ty_vpr \<Longrightarrow>
                     field_translation Tr f_vpr = Some f_bpl \<Longrightarrow>
                     vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl \<Longrightarrow>
                     type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl \<Longrightarrow>
                     (\<exists>hb f_bpl_val. 
                       lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep)) \<and>
                       lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
                       vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
                       lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
                       field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<and>
                       vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, []) \<and>
                       R (update_hh_loc_total_full \<omega> (addr,f_vpr) v) 
                         (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         ))"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
         \<gamma>
         (BigBlock name cs str tr, cont)" 
proof (rule stmt_rel_intro)
  let ?\<gamma>3="((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)"
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
  hence "Rext \<omega> \<omega> ns" using Rext by simp

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> (RNormal \<omega>')"

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) ((BigBlock name cs str tr, cont), Normal ns') \<and> R \<omega>' ns'"
  proof cases
    case (RedFieldAssign addr v ty_vpr)
    from this  obtain ns1 where
      "Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
      by auto
    from this RedFieldAssign obtain ns2 where "Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast
    from this RedFieldAssign obtain ns3 where "Rext \<omega> \<omega> ns3" and RedNs3: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>3, Normal ns3)" 
      using wf_rel_normal_elim[OF WriteableLocRel] red_ast_bpl_transitive
      by blast
    hence "R \<omega> ns3"
      using Rext by simp

    obtain f_bpl where
         "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl" and
         "field_translation Tr f_vpr = Some f_bpl" and 
         "e_f_bpl = Lang.Var f_bpl"
      using FieldRelSingle \<open>declared_fields _ f_vpr = Some ty_vpr\<close>
      unfolding field_rel_single_def
      using has_SomeD by force      
 
   moreover have NewValTypeBpl: "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
     using vpr_to_bpl_val_type[OF \<open>get_type _ v = ty_vpr\<close> \<open>vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl\<close>]
           \<open>domain_type _ = _\<close>
     by simp

   ultimately obtain hb f_bpl_val
     where 
           HeapLookupTyBpl: "lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
           LookupHeapVarBpl: "lookup_var (var_context ctxt) ns3 (heap_var Tr) = Some (AbsV (AHeap hb))" and
           HeapWellTyBpl:       "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
           HeapUpdWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, [])" and
           LookupFieldVarBpl: "lookup_var (var_context ctxt) ns3 f_bpl = Some (AbsV (AField f_bpl_val))" and           
           FieldTyBpl: "field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])" and
           "R \<omega>'
                   (update_var (var_context ctxt) ns3 (heap_var Tr) 
                   (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
             )" (is "R _ ?ns_upd")
     using RFieldAssign[OF \<open>R \<omega> ns3\<close> \<open>declared_fields _ f_vpr = Some ty_vpr\<close>] \<open>\<omega>' = _\<close>
     by blast

   from RcvRel have RedRcvBpl: "red_expr_bpl ctxt rcv_bpl ns3 (AbsV (ARef (Address addr)))"
     using \<open>Rext \<omega> \<omega> ns3\<close>  RedFieldAssign
     by (metis exp_rel_vpr_bpl_elim val_rel_vpr_bpl.simps(3))

   from RhsRel have RedRhsBpl: "red_expr_bpl ctxt rhs_bpl ns3 (val_rel_vpr_bpl v)" 
     using \<open>Rext \<omega> \<omega> ns3\<close>  RedFieldAssign
     by (meson  exp_rel_vpr_bpl_elim)

   from HeapUpdWf have 
      RedHeapUpdBpl:
     "red_expr_bpl ctxt (heap_upd_bpl (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])
                             ns3 (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))"
     apply (rule heap_update_wf_apply)
     using  \<open>h_bpl = _\<close> Semantics.RedVar[OF LookupHeapVarBpl]
           apply simp
          apply (rule HeapWellTyBpl)
         apply (rule RedRcvBpl)
     using \<open>e_f_bpl = _\<close> Semantics.RedVar[OF LookupFieldVarBpl]
        apply simp
       apply (rule FieldTyBpl)
      apply (rule RedRhsBpl)
     apply (simp add: NewValTypeBpl)
     done

   have "red_ast_bpl P ctxt 
           ((BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont), Normal ns3) 
           ((BigBlock name cs str tr, cont), Normal ?ns_upd)"
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (subst HOL.sym[OF \<open>h_bpl = _\<close>])
     apply (rule Semantics.RedAssign)
       apply (fastforce intro!: HeapLookupTyBpl simp: \<open>h_bpl = _\<close>)
     using HeapUpdWellTyBpl \<open>type_interp ctxt = _\<close>
      apply simp
     by (fastforce intro: RedHeapUpdBpl simp: \<open>h_upd_bpl = _\<close>)
    thus ?thesis
      using RedNs3 \<open>R \<omega>' ?ns_upd\<close>
      using red_ast_bpl_transitive by blast      
  qed
next
  fix \<omega> ns 
  assume "R \<omega> ns"
  hence "Rext \<omega> \<omega> ns" using Rext by simp
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
    case (RedFieldAssignFailure r v)
    from this obtain ns1 where
      "Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
      by auto      
    from this RedFieldAssignFailure obtain ns2 where "Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast

    with RedFieldAssignFailure obtain \<gamma>' where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
      using wf_rel_failure_elim[OF WriteableLocRel \<open>Rext \<omega> \<omega> ns2\<close>] red_ast_bpl_transitive
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
        using wf_rel_failure_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
        by blast
    next
      case False
      from this obtain v where "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
                               "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rhs_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
        using RedSubExpFailureAux
        by (auto elim: red_pure_exp_total_elims)
      then show ?thesis 
        using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>] wf_rel_failure_elim[OF RhsWfRel] red_ast_bpl_transitive
        by blast
    qed
  qed
qed

text \<open>Version of generic field assignment relation rule where state relation is instantiated\<close>

lemma field_assign_rel_inst:
  assumes 
    WfTyRep: "wf_ty_repr_bpl TyRep" and
    RStateRel: "\<And>\<omega> ns. R \<omega> ns = state_rel_def_same (program_total ctxt_vpr) TyRep Tr AuxPred ctxt \<omega> ns" and
    HeapVarDefSame: "heap_var_def Tr = heap_var Tr" and
    HeapUpdWf: "heap_update_wf TyRep ctxt heap_upd_bpl" and
               "domain_type TyRep = absval_interp_total ctxt_vpr" and
               "type_interp ctxt = vbpl_absval_ty TyRep" and
    Rext: "Rext = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)"  and
    RcvWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1" and
    RhsWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2" and
    WriteableLocRel: "wf_rel_fieldacc get_writeable_locs Rext Rext ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)" and 
                   "h_bpl = heap_var Tr" and
(*    HeapLookupTyBpl: "lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep))" and *)
    HeapUpdateBpl: "h_upd_bpl = heap_upd_bpl (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
    RcvRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rcv_vpr rcv_bpl" and
    FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    RhsRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rhs_vpr rhs_bpl"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
         \<gamma>
         (BigBlock name cs str tr, cont)" 
proof (rule field_assign_rel)
  fix \<omega> ns ty_vpr hb addr  f_bpl v
  assume "R \<omega> ns" and
         FieldLookup: "declared_fields (program_total ctxt_vpr) f_vpr = Some ty_vpr" and
         FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
         TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl" and
         NewValBplTy: "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"

  from \<open>R \<omega> ns\<close> have StateRelInst: "state_rel_def_same (program_total ctxt_vpr) TyRep Tr AuxPred ctxt \<omega> ns"
    by (simp add: RStateRel)

  have HeapLookupTyBpl: "lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep))"
    using state_rel0_heap_var_rel[OF state_rel_state_rel0[OF StateRelInst]] \<open>h_bpl = _\<close>
    unfolding heap_var_rel_def
    by blast

  let ?\<omega>' = "(update_hh_loc_total_full \<omega> (addr,f_vpr) v)"
  let ?ns' = "\<lambda>f_bpl_val. (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         )"      
  from state_rel_heap_update_2_ext[OF WfTyRep StateRelInst _ FieldLookup FieldTranslation TyTranslation NewValBplTy]
  obtain hb f_bpl_val where
    "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))"
    "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val))"
    "field_ty_fun_opt TyRep f_bpl_val = Some (TFieldId TyRep, [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])" and
    StateRelInstUpd: "state_rel_def_same (program_total ctxt_vpr) TyRep Tr AuxPred ctxt ?\<omega>'
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
qed (insert assms, auto)

subsection \<open>Inhale statement relation\<close>

lemma inhale_stmt_rel:
  assumes InhRel: "inhale_rel R Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'" and
          InvHolds: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> Q A \<omega>" 
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale A) \<gamma> \<gamma>'"
  apply (rule stmt_rel_intro)
  using inhale_rel_normal_elim[OF InhRel] inhale_rel_failure_elim[OF InhRel] InvHolds
  by (auto elim: RedInhale_case)

subsection \<open>Exhale statement relation\<close>

lemma exhale_stmt_rel:
  assumes 
          \<comment>\<open>Since the well-definedness must be differentiated from the evaluation state during the exhale,
            there is potentially a step in the Boogie program that sets this differentiation up resulting a new
            relation that tracks both states (where in the beginning both states are the same)\<close>
          R_to_Rexh: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns') \<and> Rexh \<omega> \<omega> ns'" and                   
          ExhaleRel: "exhale_rel Rexh Q ctxt_vpr StateCons P ctxt A \<gamma>1 \<gamma>2" and
          InvHolds: "\<And> \<omega> ns. Rexh \<omega> \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>" and
          \<comment>\<open>At the end of the exhale we require the Boogie program to reestablish the original relation on the 
             evaluation state\<close>
          Rexh_to_R: "\<And> \<omega>def \<omega> ns. Rexh \<omega>def \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>2, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega> ns'" and
          ExhaleState: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> \<omega>' \<in> exhale_state ctxt_vpr \<omega> (get_mh_total_full \<omega>) \<Longrightarrow>
                                 \<exists>ns'. red_ast_bpl P ctxt (\<gamma>3, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" 
  with R_to_Rexh obtain ns1 where Red1: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)" and "Rexh \<omega> \<omega> ns1"
    by blast

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> (RNormal \<omega>')"
  thus "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> (RNormal \<omega>') \<Longrightarrow>\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
  proof cases
    case (RedExhale \<omega>_exh)
    with exhale_rel_normal_elim[OF ExhaleRel \<open>Rexh \<omega> \<omega> ns1\<close>] obtain ns2 where 
      "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)" and "Rexh \<omega> \<omega>_exh ns2"
      using red_ast_bpl_transitive[OF Red1] InvHolds[OF \<open>Rexh \<omega> \<omega> ns1\<close>]
      by blast
    with Rexh_to_R obtain ns3 where 
     "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>3, Normal ns3)" and "R \<omega>_exh ns3"
      using red_ast_bpl_transitive
      by blast
    with ExhaleState RedExhale show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
      using red_ast_bpl_transitive
      by blast
  qed
next
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" 
  with R_to_Rexh obtain ns1 where Red1: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)" and "Rexh \<omega> \<omega> ns1"
    by blast

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale A) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
    case RedExhaleFailure
    with exhale_rel_failure_elim[OF ExhaleRel \<open>Rexh \<omega> \<omega> ns1\<close>] show ?thesis
      using red_ast_bpl_transitive[OF Red1] InvHolds[OF \<open>Rexh \<omega> \<omega> ns1\<close>]
      by fastforce
  qed (simp)
qed


text \<open>The following theorem is the same as exhale_stmt_rel except that Rext has been instantiated.
      It seems cumbersome to instantiate Rext properly during the proof generation (with a naive approach
      Isabelle picks a version that ignores the well-definedness state)\<close>

lemma exhale_stmt_rel_inst:
  assumes 
      "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns') \<and> (state_rel Pr TyRep Tr' AuxPred' ctxt \<omega> \<omega> ns')" and                   
      "exhale_rel (state_rel Pr TyRep Tr' AuxPred' ctxt) Q ctxt_vpr StateCons P ctxt A \<gamma>1 \<gamma>2" and
      InvHolds: "\<And> \<omega> ns. state_rel Pr TyRep Tr' AuxPred' ctxt \<omega> \<omega> ns \<Longrightarrow> Q A \<omega> \<omega>"
      "\<And> \<omega>def \<omega> ns. (state_rel Pr TyRep Tr' AuxPred' ctxt) \<omega>def \<omega> ns \<Longrightarrow> 
                      \<exists>ns'. red_ast_bpl P ctxt (\<gamma>2, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega> ns'" and
      "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> \<omega>' \<in> exhale_state ctxt_vpr \<omega> (get_mh_total_full \<omega>) \<Longrightarrow>
                             \<exists>ns'. red_ast_bpl P ctxt (\<gamma>3, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
  using assms
  by (rule exhale_stmt_rel)

lemma exhale_stmt_rel_finish:
  assumes StateRel: "state_rel_def_same Pr (TyRep :: 'a ty_repr_bpl) Tr AuxPred ctxt \<omega> ns" and
          CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
          WfTyRepr: "wf_ty_repr_bpl TyRep" and
          ProgramTotal: "Pr = program_total ctxt_vpr" and
          DomainType:  "domain_type TyRep = absval_interp_total ctxt_vpr" and
          WellDefSame: "heap_var Tr = heap_var_def Tr \<and> mask_var Tr = mask_var_def Tr" and 
          "id_on_known_locs_name = FunMap FIdenticalOnKnownLocs" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          "\<omega>' \<in> exhale_state ctxt_vpr \<omega> (get_mh_total_full \<omega>)" and
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
               state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega>' ns'" (is "\<exists>ns'. ?red ns' \<and> ?rel ns'")
proof -
  from state_rel_heap_var_rel[OF StateRel]
  obtain hb where   LookupHeapVarTy: "lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep))" and
                    LookupHeapVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and  
                    HeapVarWellTy: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
                    HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
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
    using  construct_bpl_heap_from_vpr_heap_correct[OF WfTyRepr exhale_state_well_typed_heap[OF \<open>\<omega>' \<in> _\<close>] DomainType]                
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

  have IdOnKnownCond: "\<forall>r f t. 0 < mb (r, NormalField f t) \<longrightarrow> hb (r, NormalField f t) = hb'' (r, NormalField f t)"
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

      hence "mb (r, (NormalField f t)) = real_of_rat (Rep_prat (get_mh_total_full \<omega> heap_loc))"
        using MaskRel
        unfolding mask_rel_def
        by blast
      hence "get_mh_total_full \<omega> heap_loc \<noteq> pnone"
        using PermPos zero_prat.rep_eq by fastforce

      hence "get_hh_total_full \<omega> heap_loc = get_hh_total_full \<omega>' heap_loc"
        using \<open>\<omega>' \<in> _\<close> 
        unfolding exhale_state_def havoc_undef_locs_def
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

  have StateRel1: "state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega> ?ns1"
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

  moreover have "state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega>' ?ns2"
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
      using \<open>\<omega>' \<in> _\<close> exhale_state_same_store
      by metis
  next
    show "get_m_total_full \<omega> = get_m_total_full \<omega>'"
      using \<open>\<omega>' \<in> _\<close> exhale_state_same_mask
      by metis
  next
    show "get_trace_total \<omega> = get_trace_total \<omega>'"
      using \<open>\<omega>' \<in> _\<close> exhale_state_same_trace
      by metis
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep Tr (heap_var Tr) \<omega>' ?ns2"
      using ProgramTotal
      unfolding heap_var_rel_def
      apply (subst \<open>hvar = _\<close>)+
      by (fastforce intro: LookupHeapVarTy NewHeapWellTy NewHeapRel)      
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

subsection \<open>Method call relation\<close> 

fun the_var :: "ViperLang.pure_exp \<Rightarrow> ViperLang.var" where 
  "the_var (ViperLang.Var x) = x"
| "the_var _ = undefined"

term map_upds

value "upt 0 4"

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

definition store_var_rel_aux
  where "store_var_rel_aux A \<Lambda> \<omega> ns var_vpr var_bpl \<equiv>
           (\<exists>val_vpr ty_bpl.
                             (get_store_total \<omega> var_vpr) = Some val_vpr \<and>
                              lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                              lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                              type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl )"


lemma store_relI:
  assumes "inj_on f (dom f)"
          "\<And> var_vpr var_bpl. f var_vpr = Some var_bpl \<Longrightarrow>
                        store_var_rel_aux A \<Lambda> \<omega> ns var_vpr var_bpl"
  shows "store_rel A \<Lambda> f \<omega> ns"
  using assms
  unfolding store_rel_def store_var_rel_aux_def
  by blast

lemma state_rel_var_translation_remove:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega> \<omega> ns" and
          MapLe: "f' \<subseteq>\<^sub>m var_translation Tr" and
          "finite (ran f')"
        shows "state_rel Pr TyRep (Tr\<lparr> var_translation := f' \<rparr>) AuxPred ctxt \<omega> \<omega> ns"
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
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega> \<omega> ns" and
          "f' \<subseteq>\<^sub>m var_translation Tr" and
          "finite (ran f')"
          "B = ran (var_translation Tr) - ran f'" 
        shows "state_rel Pr TyRep (Tr\<lparr> var_translation := f' \<rparr>) 
                 (map_upd_set AuxPred B (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))) 
                 ctxt \<omega> \<omega> ns"
proof -
  let ?Tr' = "Tr\<lparr> var_translation := f' \<rparr>"
  let ?AuxPred' = "map_upd_set AuxPred B (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"

  from assms have "state_rel Pr TyRep ?Tr' AuxPred ctxt \<omega> \<omega> ns"
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

subsubsection \<open>Main Lemma\<close>

lemma method_call_stmt_rel:
  assumes 
          MdeclSome:  "program.methods (program_total ctxt_vpr) m = Some mdecl" and
                      "rtype_interp ctxt = []" and
          DomainTyRep: "domain_type TyRep = absval_interp_total ctxt_vpr" and
          TyInterpBplEq:   "type_interp ctxt = vbpl_absval_ty TyRep" and
          StateRelConcrete: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega> ns" and                  
                  ArgsAreVars: "list_all (\<lambda>x. \<exists>a. x = ViperLang.Var a) es" \<comment>\<open>simplifying assumption: only variables as arguments\<close> and
                  "xs = map the_var es" and
                  "set xs \<subseteq> dom (var_translation Tr)" and
                  XsBplEq: "map (the \<circ> var_translation Tr) xs = xs_bpl" and
                  "set ys \<subseteq> dom (var_translation Tr)" and
                  YsBplEq: "map (the \<circ> var_translation Tr) ys = ys_bpl" and     
                  "set xs_bpl \<inter> set ys_bpl = {}" and \<comment>\<open>simplifying assumption: targets and arguments do not clash\<close>
                  "distinct xs" and \<comment>\<open>simplifying assumption: arguments are distinct\<close>
                  "distinct ys" and
             \<comment>\<open>TODO: One could probably track the following fact on declared types also via the variable relation
                      where one ensures that the declared Viper and Boogie types match for variables related by
                      the variable relation.\<close>
          LookupDeclRetsBpl: 
                     "list_all2 (\<lambda>y_bpl t_vpr. \<exists>t_bpl. vpr_to_bpl_ty TyRep t_vpr = Some t_bpl \<and>
                                           lookup_var_decl (var_context ctxt) y_bpl = Some (t_bpl, None))
                                ys_bpl (method_decl.rets mdecl)" and
          \<comment>\<open> Since the rule only deals with variables in the arguments, well-definedness holds trivially
             ExpWfRel: "exprs_wf_rel Rdef ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>def"\<close>
                   \<comment>\<open>simplifying assumption: unoptimized exhale and inhale\<close>
                        \<comment>\<open>"var_tr' = [[0..<length es] [\<mapsto>] rev xs_bpl]" and \<close>
                   "var_tr' = [[0..<length es] [\<mapsto>] xs_bpl]" and
          ExhalePreRel: "\<And> fpred.                                                
                        stmt_rel 
                              (state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt)
                              (state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt) 
                              ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                              (Exhale (method_decl.pre mdecl)) \<gamma> \<gamma>pre" and
                 "\<gamma>pre = (BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)" and
                 "cs_pre = havocs_list_bpl ys_bpl @ cs_pre_suffix" and
             \<comment>\<open>    "var_tr'' = Map.empty(upt 0 (length es+length ys) [\<mapsto>] rev (ys_bpl@xs_bpl))" and\<close>
               "var_tr'' = Map.empty(upt 0 (length es+length ys) [\<mapsto>] (xs_bpl @ ys_bpl))" and
          InhalePostRel:         "\<And> fpred.
                        stmt_rel (state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt)
                              (state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt)
                              ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                              (Inhale (method_decl.post mdecl)) (BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre) \<gamma>'"

  shows "stmt_rel R (state_rel_def_same Pr TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (MethodCall ys m es) \<gamma> \<gamma>'" 
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" 
  \<comment>\<open>Prove various properties before showing the goal\<close>
  hence StateRel: "state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega> ns"
    using StateRelConcrete
    by blast  

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

  \<comment>\<open>Show the goal\<close>

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (MethodCall ys m es) \<omega> res"

  thus "rel_vpr_aux (state_rel_def_same Pr TyRep Tr AuxPred ctxt) P ctxt \<gamma> \<gamma>' ns res"
  proof (cases)
    case (RedMethodCall v_args mdecl' v_rets resPre resPost)
     \<comment>\<open>All arguments evaluate normally\<close>

    from MdeclSome RedMethodCall have "mdecl = mdecl'"
      by force

    have ListAllArgsEvalVpr: "list_all2 (\<lambda>e v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) es v_args"
      using red_pure_exps_total_list_all2 RedMethodCall
      by blast

    hence "length es = length v_args"
      by (simp add: list_all2_lengthD)

    have "length xs = length xs_bpl"
      using XsBplEq
      by auto

    have "length xs_bpl = length v_args"
      using RedMethodCall \<open>xs = _\<close> XsBplEq
      by (metis ListAllArgsEvalVpr length_map list_all2_lengthD)    

    have "length ys = length ys_bpl"
      using YsBplEq by auto

    hence "length ys_bpl = length v_rets"
      using RedMethodCall
      unfolding vals_well_typed_def
      by (metis length_map list_all2_lengthD)

    note LengthEqs = \<open>length es = length v_args\<close> \<open>length xs = length xs_bpl\<close> \<open>length xs_bpl = length v_args\<close>
                     \<open>length ys = length ys_bpl\<close> \<open>length ys_bpl = length v_rets\<close>

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

    hence StoreValArgsVpr: "list_all2 (\<lambda>x v. get_store_total \<omega> x = Some v) xs v_args"
      using TotalExpressions.RedVar_case
      by (metis (mono_tags, lifting) list_all2_mono)

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

      \<comment>\<open>Show state rel with new var translation, which is required to use the exhale relation on the
         precondition\<close>

    let ?\<omega>0 = "\<lparr>get_store_total = shift_and_add_list_alt Map.empty v_args, 
                get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                get_total_full = get_total_full \<omega>\<rparr>"

    let ?fpred  = "(\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"

    note ExhalePreRelInst = ExhalePreRel
    (*note InhalePostRelInst = InhalePostRel[OF \<open>set ls = _\<close> \<open>length ls = length ?ps\<close>]*)
    let ?AuxPredPre = "(map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) ?fpred)"
    let ?RCall = "state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) ?AuxPredPre ctxt"
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
  
      have "state_rel Pr TyRep (Tr \<lparr> var_translation := Map.empty \<rparr>) ?AuxPredPre ctxt \<omega> \<omega> ns"
        apply (rule state_rel_aux_pred_remove)
         apply (rule state_rel_transfer_var_tr_to_aux_pred[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]])
          apply simp
          apply simp
         apply simp
        by (rule AuxSub)        

      thus ?thesis
        apply (rule state_rel_store_update[where ?f= var_tr'])
                 apply simp
               apply simp
              apply simp
             apply simp
        using StoreRel
         apply simp
           apply simp
          apply simp
        using state_rel_state_well_typed[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>], simplified state_well_typed_def]
        apply simp
        
        using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] 
              \<open>set xs_bpl \<subseteq> _\<close> \<open>ran var_tr' = _\<close>
        by (auto simp: map_upd_set_lookup_2)
    qed

    show ?thesis 
    proof (cases "resPre")
      case RMagic
      then show ?thesis \<comment>\<open>trivial case\<close>
        using RedMethodCall
        by (auto intro: rel_vpr_aux_intro)
    next
      case RFailure
      with RedMethodCall \<open>mdecl = _\<close> 
      obtain c where 
          "red_ast_bpl P ctxt (\<gamma>, Normal ns) c" and
          "snd c = Failure"
        using stmt_rel_failure_elim[OF ExhalePreRelInst StateRelDuringCall]
        by blast
      moreover have "res = RFailure"
        using RFailure RedMethodCall
        by argo
      ultimately show ?thesis         
        using red_ast_bpl_transitive
        by (blast intro: rel_vpr_aux_intro)                  
    next
      case (RNormal \<omega>pre)
      with RedMethodCall \<open>mdecl = _\<close>
      obtain nspre where
        RedBplPre: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>pre, Normal nspre)" and
        "?RCall \<omega>pre nspre"
        using stmt_rel_normal_elim[OF ExhalePreRelInst StateRelDuringCall]
        by blast

      let ?\<omega>havoc = "\<lparr> get_store_total = (shift_and_add_list_alt Map.empty (v_args@v_rets)), 
                       get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                       get_total_full = get_total_full \<omega>pre \<rparr>"
 
      note InhalePostRelInst = InhalePostRel

      let ?AuxPredPost = "(map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) ?fpred)"
      let ?RCallPost = "state_rel_def_same Pr TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) ?AuxPredPost ctxt"

      let ?v_rets_bpl = "map (val_rel_vpr_bpl) v_rets"

      let ?nshavoc = "update_var_list (var_context ctxt) nspre ys_bpl ?v_rets_bpl"

         have *: "length ys_bpl = length (map val_rel_vpr_bpl v_rets)"
        proof -
            have "length ys = length ys_bpl"
              using YsBplEq by auto
            moreover have "length ys = length v_rets"
              using RedMethodCall
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
            using * \<open>n < _\<close> \<open>vals_well_typed (absval_interp_total ctxt_vpr) v_rets (rets mdecl')\<close>
            unfolding vals_well_typed_def  \<open>mdecl = mdecl'\<close>
            by (metis length_map nth_map)           

          ultimately 
         show "lookup_var_decl (var_context ctxt) (ys_bpl ! n) = 
                 Some (type_of_val (type_interp ctxt) (map val_rel_vpr_bpl v_rets ! n), None)"
           apply simp
           using DomainTyRep vpr_to_bpl_val_type TyInterpBplEq 
           by (metis "*" \<open>n < length ys_bpl\<close> list_update_id list_update_same_conv map_update)
       qed

      have
        RedBplHavoc: "red_ast_bpl P ctxt (\<gamma>pre, Normal nspre) ((BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre), Normal ?nshavoc)"
        unfolding \<open>\<gamma>pre = _\<close> \<open>cs_pre = _\<close>
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
       "state_rel_def_same Pr TyRep (Tr\<lparr>var_translation := var_tr'\<rparr>)
          (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))) ctxt \<omega>pre nspre"
       apply (rule state_rel_aux_pred_remove)
       apply (rule map_upd_set_subset)
        apply blast
       using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
       by blast

     hence
      "?RCallPost ?\<omega>havoc ?nshavoc"
     proof (rule state_rel_store_update[where ?f=var_tr''])
       fix x
       assume "x \<notin> ran var_tr''"
       hence "x \<notin> set ys_bpl"
         using \<open>ran var_tr'' = _\<close>
         by blast

       thus "lookup_var (var_context ctxt) nspre x = 
             lookup_var (var_context ctxt) (update_var_list (var_context ctxt) nspre ys_bpl (map val_rel_vpr_bpl v_rets)) x"
         using lookup_update_var_list_other LengthEqs
         by (metis length_map)
     next
       show "store_rel (type_interp ctxt) (var_context ctxt) var_tr'' ?\<omega>havoc ?nshavoc"
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

         have HavocStoreVprLookupAux: "get_store_total ?\<omega>havoc var_vpr = Some ((v_args @ v_rets) ! var_vpr)"
             apply (simp add: shift_and_add_list_alt_lookup)
             using \<open>var_vpr < _\<close> LengthEqs
             by linarith

         show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>havoc ?nshavoc var_vpr var_bpl"
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

             from RedMethodCall have \<comment>\<open>exhale does not change the store\<close>
                 StorePreVprEq: "get_store_total \<omega>pre = shift_and_add_list_alt Map.empty v_args"
               using \<open>resPre = _\<close> exhale_only_changes_total_state
               by force
                 
             hence StorePreVprEqLookup: "get_store_total \<omega>pre var_vpr = Some (v_args ! var_vpr)"
               using True LengthEqs
               by (simp add: shift_and_add_list_alt_lookup_1)

             show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>havoc ?nshavoc var_vpr var_bpl"
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
     qed simp_all

      from RedMethodCall RNormal have 
         RedInh: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl')) ?\<omega>havoc resPost" and
         "res = map_stmt_result_total (reset_state_after_call ys v_rets \<omega>) resPost"
        by blast+

      show ?thesis  
      proof (cases resPost)
        case RMagic
        then show ?thesis \<comment>\<open>trivial case\<close>
          using \<open>res = _\<close>
          by (auto intro: rel_vpr_aux_intro)
      next
        case RFailure
          with RedInh stmt_rel_failure_elim[OF InhalePostRelInst \<open>?RCallPost ?\<omega>havoc ?nshavoc\<close>] \<open>mdecl = _\<close>
          obtain c where 
              "red_ast_bpl P ctxt (\<gamma>pre, Normal nspre) c" and
              "snd c = Failure"
            using RedBplHavoc red_ast_bpl_transitive
            by blast
          moreover from RFailure \<open>res = _\<close> have "res = RFailure"
            by simp
          ultimately show ?thesis 
            using RedBplPre red_ast_bpl_transitive
            by (blast intro: rel_vpr_aux_intro)
      next
        case (RNormal \<omega>post)
          with RedInh stmt_rel_normal_elim[OF InhalePostRelInst \<open>?RCallPost ?\<omega>havoc ?nshavoc\<close>] \<open>mdecl = _\<close>
          obtain nspost where 
              "red_ast_bpl P ctxt (\<gamma>pre, Normal nspre) (\<gamma>', Normal nspost)" and
              "?RCallPost \<omega>post nspost"
            using RedBplHavoc red_ast_bpl_transitive
            by blast
          hence "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal nspost)"
            using RedBplPre red_ast_bpl_transitive
            by blast

          moreover have "get_store_total \<omega>post = get_store_total ?\<omega>havoc"
          using RedMethodCall \<open>resPre = _\<close> \<open>resPost = _\<close> inhale_only_changes_mask
          by (metis RedInhale_case sub_expressions.simps(7))

          moreover from RNormal \<open>res = _\<close> have "res = RNormal (reset_state_after_call ys v_rets \<omega> \<omega>post)"
            by simp
            
          moreover have                                          
             "state_rel_def_same Pr TyRep Tr AuxPred ctxt (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost"
          proof -
            from \<open>?RCallPost \<omega>post nspost\<close> have
              "state_rel_def_same Pr TyRep (Tr\<lparr>var_translation := var_tr''\<rparr>) AuxPred ctxt \<omega>post nspost"
              apply (rule state_rel_aux_pred_remove)
              apply (rule map_upd_set_subset2)
              using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
              by blast

            thus ?thesis
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
                    using VarTrSome * state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                    unfolding store_var_rel_aux_def store_rel_def
                    by presburger                    
                qed
              qed
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
            qed (simp_all add: reset_state_after_call_def  )
              
          qed
            
          ultimately show ?thesis 
            by (blast intro: rel_vpr_aux_intro)
        qed
      qed
  next
    case RedSubExpressionFailure
    \<comment>\<open>Since the arguments are assumed to be arguments, this case cannot occur\<close>
    have SubExpEq: "sub_expressions (MethodCall ys m es) = map ViperLang.Var xs"
      by (simp add: \<open>es = _\<close>) 

    from RedSubExpressionFailure
    show ?thesis
      unfolding SubExpEq
    proof -
      assume "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) (map pure_exp.Var xs) \<omega> None"

      from this obtain i where 
        "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>pure_exp.Var (xs ! i); \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        using red_exp_list_failure_nth
        by (metis SubExpEq length_map local.RedSubExpressionFailure(2) nth_map)
        
      hence False
        by (cases) auto

      thus ?thesis
        by simp
    qed
  qed
qed

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