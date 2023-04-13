theory StmtRel
imports ExpRel ExprWfRel InhaleRel ExhaleRel TotalSemProperties TotalViper.ViperBoogieTranslationInterface Simulation
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
       ( red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_thn \<omega> (RNormal \<omega>') \<or>
       red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_els \<omega> (RNormal \<omega>'))"
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
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and>
        red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_thn \<omega> RFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and>
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
        apply (rule ValBplTy)
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
    HeapUpdWf: "heap_update_wf TyRep ctxt (heap_update Tr)" and
               "domain_type TyRep = absval_interp_total ctxt_vpr" and
               "type_interp ctxt = vbpl_absval_ty TyRep" and
    Rext: "Rext = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)"  and
    RcvWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1" and
    RhsWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2" and
    WriteableLocRel: "wf_rel_fieldacc get_writeable_locs Rext Rext ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)" and 
                   "h_bpl = heap_var Tr" and
    HeapUpdateBpl: "h_upd_bpl = heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
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
     "red_expr_bpl ctxt (heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])
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
    HeapUpdWf: "heap_update_wf TyRep ctxt (heap_update Tr)" and
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
    HeapUpdateBpl: "h_upd_bpl = heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
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
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Inhale A) \<gamma> \<gamma>'"
  apply (rule stmt_rel_intro)
  using inhale_rel_normal_elim[OF assms] inhale_rel_failure_elim[OF assms]
  by (auto elim: RedInhale_case)

subsection \<open>Exhale statement relation\<close>

lemma exhale_stmt_rel:
  assumes 
          \<comment>\<open>Since the well-definedness must be differentiated from the evaluation state during the exhale,
            there is potentially a step in the Boogie program that sets this differentiation up resulting a new
            relation that tracks both states (where in the beginning both states are the same)\<close>
          R_to_Rexh: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns') \<and> Rexh \<omega> \<omega> ns'" and                   
          ExhaleRel: "exhale_rel Rexh ctxt_vpr StateCons P ctxt A \<gamma>1 \<gamma>2" and
          \<comment>\<open>At the end of the exhale we require the Boogie program to reestablish the original relation on the 
             evaluation state\<close>
          Rexh_to_R: "\<And> \<omega>def \<omega> ns. Rexh \<omega>def \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>2, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega> ns'" and
          ExhaleState: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> \<omega>' \<in> exhale_state \<omega> (get_mh_total_full \<omega>) \<Longrightarrow>
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
      using red_ast_bpl_transitive[OF Red1]
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
      using red_ast_bpl_transitive[OF Red1]
      by fastforce
  qed (simp)
qed


text \<open>The following theorem is the same as exhale_stmt_rel except that Rext has been instantiated.
      It seems cumbersome to instantiate Rext properly during the proof generation (with a naive approach
      Isabelle picks a version that ignores the well-definedness state)\<close>

lemma exhale_stmt_rel_inst:
  assumes 
      "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns') \<and> (state_rel Pr TyRep Tr AuxPred ctxt \<omega> \<omega> ns')" and                   
      "exhale_rel (state_rel Pr TyRep Tr AuxPred ctxt) ctxt_vpr StateCons P ctxt A \<gamma>1 \<gamma>2" and
      "\<And> \<omega>def \<omega> ns. (state_rel Pr TyRep Tr AuxPred ctxt) \<omega>def \<omega> ns \<Longrightarrow> 
                      \<exists>ns'. red_ast_bpl P ctxt (\<gamma>2, Normal ns) (\<gamma>3, Normal ns') \<and> R \<omega> ns'" and
      "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> \<omega>' \<in> exhale_state \<omega> (get_mh_total_full \<omega>) \<Longrightarrow>
                             \<exists>ns'. red_ast_bpl P ctxt (\<gamma>3, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
  using assms 
  by (rule exhale_stmt_rel)

lemma exhale_stmt_rel_finish:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
          WfTyRepr: "wf_ty_repr_bpl TyRep" and
          "id_on_known_locs_name = FunMap FIdenticalOnKnownLocs" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          "\<omega>' \<in> exhale_state \<omega> (get_mh_total_full \<omega>)" and
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
               state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega>' ns'" (is "\<exists>ns'. ?red ns' \<and> ?rel ns'")
proof -
 (* "vbpl_absval_ty_opt TyRep (AHeap h_new) = Some ((THeapId TyRep) ,[])" *)
  from state_rel_heap_var_rel[OF StateRel]
  obtain hb where LookupHeapVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and  
                    HeapVarWellTy: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
                    HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
      unfolding heap_var_rel_def
      by blast

    from state_rel_mask_var_rel[OF StateRel]
    obtain mb where LookupMaskVar: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
                    "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
      unfolding mask_var_rel_def 
      by blast

    obtain hb' where HeapRel': "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>') hb'" and
                     NewHeapWellTy: "vbpl_absval_ty_opt TyRep (AHeap hb') = Some (THeapId TyRep, [])"
      using WfTyRepr construct_bpl_heap_from_vpr_heap_correct by blast

    have IdOnKnownCond: "\<forall>r f t. 0 < mb (r, NormalField f t) \<longrightarrow> hb (r, NormalField f t) = hb' (r, NormalField f t)"
    proof clarify
      fix r f t 
      assume "0 < mb (r, NormalField f t)"

    let ?ns1 = "(update_var (var_context ctxt) ns hvar_exh (AbsV (AHeap hb')))"
    have "red_ast_bpl P ctxt ((BigBlock name (Havoc hvar_exh # 
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




subsection \<open>Misc\<close>

lemma init_state:
  assumes "R0 \<omega> ns" and
          "is_empty_total \<omega>" 
  shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name cs str tr,cont), Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'"
  oops

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