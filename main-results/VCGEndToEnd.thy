theory VCGEndToEnd
imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal TotalViper.TraceIndepProperty
begin

subsection \<open>Helper\<close>

fun valid_front_end_cmd :: "cmd \<Rightarrow> bool"
  where
    "valid_front_end_cmd (Cseq C1 C2) \<longleftrightarrow> valid_front_end_cmd C1 \<and> valid_front_end_cmd C2"
  | "valid_front_end_cmd ({P1} C1 {P2} || {Q1} C2 {Q2})  \<longleftrightarrow> valid_a2t_assert P1 \<and> valid_a2t_assert P2
                                                          \<and> valid_a2t_assert Q1 \<and> valid_a2t_assert Q2 \<and>
                                                            valid_front_end_cmd C1 \<and> valid_front_end_cmd C2"
  | "valid_front_end_cmd (Cif B C1 C2) \<longleftrightarrow> valid_front_end_cmd C1 \<and> valid_front_end_cmd C2"
  | "valid_front_end_cmd (Cwhile B I C)    \<longleftrightarrow> valid_a2t_assert I \<and> valid_front_end_cmd C"
  | "valid_front_end_cmd _    = True"

lemma valid_a2t_exp_translate_exp: "valid_a2t_exp (translate_exp e)"
  by (induction e) auto

lemma valid_a2t_bexp_translate_exp: "valid_a2t_exp (translate_bexp e)"
  apply (induction e)
  using valid_a2t_exp_translate_exp
  by auto

lemma vald_a2t_stmt_n_havoc: "valid_a2t_stmt (n_havoc xs)"
  by (induction xs) auto
  
lemma valid_a2t_stmt_translate_syn:
  assumes "valid_front_end_cmd C"
  shows "valid_a2t_stmt (fst (translate_syn  C)) \<and> (\<forall>aux \<in> snd (translate_syn C). valid_a2t_stmt aux)"
  using assms
  apply (induction C)
  apply (simp_all add: valid_a2t_exp_translate_exp 
                      syntactic_translate_heap_loc_def
                      syntactic_translate_addr_def
                      Let_def 
                      vald_a2t_stmt_n_havoc
                      valid_a2t_bexp_translate_exp)
    apply fastforce
   apply blast
  apply blast
  done

subsection \<open>Main\<close>

definition vpr_program_from_method_decl :: "method_decl \<Rightarrow> program"
  where "vpr_program_from_method_decl m = 
           \<lparr> methods = [''m'' \<mapsto> m], predicates = Map.empty, funs = Map.empty, declared_fields = [field_val \<mapsto> TInt], domains = 0 \<rparr>"

definition default_ctxt :: "('a \<Rightarrow> abs_type) \<Rightarrow> method_decl \<Rightarrow> 'a total_context"
  where "default_ctxt d m = \<lparr> program_total = vpr_program_from_method_decl m, fun_interp_total = Map.empty, absval_interp_total = d \<rparr>"

abbreviation true_syn_assertion 
  where "true_syn_assertion \<equiv> (Atomic (Pure (ELit (LBool True))))"

lemma custom_context_tcfe_eq:
  "custom_context (tcfe \<Delta> tys) =
   sem_fields i1 (declared_fields (program_total (default_ctxt d mdecl)))"
  unfolding type_ctxt_front_end_def
         default_ctxt_def vpr_program_from_method_decl_def type_ctxt_heap_def
  apply simp
  apply (rule ext)
  apply (case_tac "f = field_val")
  by (simp_all add: sem_fields_def vints_def)

lemma no_trace_atrue:
  assumes "\<omega> \<in> atrue \<Delta> tys"
  shows "get_trace |\<omega>| = (\<lambda>x. None)"
  using assms unfolding atrue_def no_trace_def
  by (simp add: core_charact_equi(3))


lemma no_assert_assume_havoc_list:
  "ConcreteSemantics.no_assert_assume (ConcreteSemantics.havoc_list l)"
  by (induct l) simp_all

lemma valid_then_no_assume_assert:
  "ConcreteSemantics.no_assert_assume (fst (translate \<Delta> tys C))"
  by (induct C) (simp_all add: Let_def no_assert_assume_havoc_list)

lemma valid_then_no_assume_assert_snd:
  assumes "Cv \<in> snd (translate \<Delta> tys C)"
  shows "ConcreteSemantics.no_assert_assume Cv"
  using assms
  apply (induct C) apply (simp_all add: Let_def)
  by (elim disjE; simp_all add: Let_def valid_then_no_assume_assert no_assert_assume_havoc_list)+

lemma mono_custom_holds:
  "ConcreteSemantics.mono_custom \<Gamma>"
proof -
  have "\<And>C \<omega> \<omega>' S. \<omega>' \<succeq> \<omega> \<Longrightarrow> red_custom_stmt \<Gamma> C \<omega> S \<Longrightarrow> wf_custom_stmt \<Gamma> C \<Longrightarrow> (\<exists>S'. red_custom_stmt \<Gamma> C \<omega>' S' \<and> S' \<ggreater> S)"
  proof -
    fix C \<omega> \<omega>' S
    show "red_custom_stmt \<Gamma> C \<omega> S \<Longrightarrow> \<omega>' \<succeq> \<omega> \<Longrightarrow> wf_custom_stmt \<Gamma> C  \<Longrightarrow> (\<exists>S'. red_custom_stmt \<Gamma> C \<omega>' S' \<and> S' \<ggreater> S)"
    proof (induct rule: red_custom_stmt.induct)
      case (RedFieldAssign r \<omega> hl e v f \<Delta> ty)
      moreover have "red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega>' {update_heap_val \<omega>' (hl, f) v}"
        apply (rule red_custom_stmt.RedFieldAssign)
        using wf_expE[of r \<omega>' \<omega> hl]
        using calculation(1) calculation(6) calculation(7) apply fastforce
        apply (meson calculation(2) calculation(6) calculation(7) wf_custom_stmt.simps wf_expE)
        using calculation(3) calculation(6) larger_mask_full apply blast
        using RedFieldAssign by simp_all
      moreover have "update_heap_val \<omega>' (hl, f) v \<succeq> update_heap_val \<omega> (hl, f) v"
        apply (intro greater_prodI vstate_greater_charact1 greaterI)
         apply (metis calculation(6) fstI greater_charact set_state_def succ_refl)
          apply (simp add: calculation(6) greater_Ag greater_state_has_greater_parts(2) set_state_def)
         apply (metis calculation(6) get_state_def get_state_set_state get_vh_vm_set_value(2) greaterE greater_state_has_greater_parts(3) vstate_greater_charact)
        apply (case_tac "(hl, f) = l")
        unfolding set_value_def
         apply simp_all
         apply (metis fun_upd_same get_state_def get_state_set_state get_vh_vm_set_value(1) set_value.abs_eq succ_refl)
        by (metis (no_types, lifting) calculation(6) fun_upd_apply get_state_def get_state_set_state get_vh_Some_greater get_vh_vm_set_value(1) option_greater_iff set_value.abs_eq succ_refl)
      then show "\<exists>S'. red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega>' S' \<and> S' \<ggreater> {update_heap_val \<omega> (hl, f) v}"
        by (meson calculation(8) greater_set_singleton)
    qed
  qed
  then show ?thesis unfolding ConcreteSemantics.mono_custom_def by blast
qed

lemma stabilize_core_initial_state:
  assumes "typed (tcfe \<Delta> tys) \<omega>"
      and "get_trace |\<omega>| = (\<lambda>x. None)"
    shows "stabilize |\<omega>| \<in> initial_vcg_states_equi (t2a_ctxt (default_ctxt (interp.domains \<Delta>) mdecl) (nth_option tys))"
proof -
  have fst_tcfes_eq: "fst (tcfes tys) = nth_option tys"
    unfolding type_ctxt_front_end_syntactic_def by auto
  show ?thesis
    unfolding initial_vcg_states_equi_def apply simp
    apply (rule conjI)
     defer
    apply (rule conjI)
      defer
    apply (simp add: core_charact_equi(2) core_structure(1) zero_mask_def)
    unfolding t2a_ctxt_def TypedEqui.typed_def TypedEqui.typed_store_def
     apply simp
     apply (rule conjI)
    apply (metis abs_type_context.simps(1) assms(1) default_ctxt_def fst_tcfes_eq make_context_semantic_def make_context_semantic_type_ctxt total_context.simps(3) type_ctxt_front_end_def typed_then_store_typed)
    unfolding sem_fields_def absval_interp_total_def
     apply simp
     apply (metis TypedEqui.typed_core TypedEqui.typed_def TypedEqui.typed_state_axioms assms(1) custom_context_tcfe_eq sem_fields_def typed_state.typed_state_then_stabilize_typed)
    using assms(2) by simp
qed

theorem sound_syntactic_translation_VCG:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"
      and ValidFrontendCmd: "valid_front_end_cmd C"
      and ValidPrePost: "valid_a2t_assert Ps \<and> valid_a2t_assert Qs"

      and AbsTypeWf: "abs_type_wf (interp.domains \<Delta>)"
      and InterpFunsPredsEmpty: "interp.funs \<Delta> = (\<lambda> _ _ _. None) \<and> interp.predicates \<Delta> = Map.empty"

      and "mdecl = (triple_as_method_decl tys Ps (fst (translate_syn C)) Qs)"
      and MethodCorrect: "vpr_method_correct_total (default_ctxt (domains \<Delta>) mdecl) (\<lambda>_ :: int full_total_state. True) mdecl"     
      and AuxiliaryMethodsCorrectAndTyped:
        "\<And> stmtAux. stmtAux \<in> snd (translate_syn C) \<Longrightarrow> 
             let mdeclAux = triple_as_method_decl tys 
                              true_syn_assertion stmtAux true_syn_assertion 
             in
             vpr_method_correct_total (default_ctxt (domains \<Delta>) mdeclAux) (\<lambda>_ :: int full_total_state. True) mdeclAux \<and>
             stmt_typing (program_total (default_ctxt (domains \<Delta>) mdeclAux)) (nth_option tys) stmtAux"
 
      and MainViperTyped: 
            "stmt_typing (program_total (default_ctxt (domains \<Delta>) mdecl)) (nth_option tys)
                   (stmt.Seq (stmt.Seq (stmt.Inhale Ps) (fst (translate_syn C))) (stmt.Exhale Qs))"

      and "P = make_semantic_assertion_gen False \<Delta> (tcfes tys) Ps"
      and "Q = make_semantic_assertion_gen False \<Delta> (tcfes tys) Qs"     
    shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"

proof (rule sound_translation[OF assms(1-3)])

  have wf_fst: "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))"
    using assms(1) assms(2) wf_stmt_implies_wf_translation by blast

  have wf_snd: "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
    using assms(1) assms(2) wf_stmt_implies_wf_translation_snd by blast

  have tcfe_eq: "variables (tcfe \<Delta> tys) = nth_option (map (set_from_type (domains \<Delta>)) tys)"
    unfolding type_ctxt_front_end_def type_ctxt_store_def by auto
  have fst_tcfes_eq: "fst (tcfes tys) = nth_option tys"
    unfolding type_ctxt_front_end_syntactic_def by auto


  let ?Ctr_main = "(fst (translate_syn C))"
  let ?ctxt = "(default_ctxt (domains \<Delta>) mdecl) :: int total_context"
  let ?\<Lambda> = "nth_option tys"
  let ?Ctr_mainV = "(stmt.Seq (stmt.Seq (stmt.Inhale Ps) ?Ctr_main) (stmt.Exhale Qs))"

  show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) (abs_stmt.Inhale P ;; fst (translate \<Delta> tys C) ;; abs_stmt.Exhale Q)"
  proof -

    have A1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) ?Ctr_mainV)"
      apply (rule VCG_to_verifies_set)
      using MethodCorrect
      unfolding \<open>mdecl = _\<close>
          apply blast
         apply simp
      using MainViperTyped
      unfolding \<open>mdecl = _\<close>
        apply blast
      using valid_a2t_stmt_translate_syn[OF ValidFrontendCmd] ValidPrePost
      apply fast
      by (simp_all add: default_ctxt_def AbsTypeWf)

    have "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)) (compile False \<Delta> (tcfes tys) ?Ctr_mainV)"
    proof -
      have "tcfe \<Delta> tys = t2a_ctxt ?ctxt (nth_option tys)"
        unfolding t2a_ctxt_def
        apply (rule abs_type_context.equality, simp_all)
         apply (simp add: sem_store_def)
         apply (fastforce simp add: tcfe_eq default_ctxt_def)    
        using custom_context_tcfe_eq
        by blast
      moreover have "tcfes tys = (nth_option tys, declared_fields (program_total ?ctxt))"        
        unfolding type_ctxt_front_end_syntactic_def        
        apply clarify
        apply (rule conjI)
        using fst_tcfes_eq
        unfolding type_ctxt_front_end_syntactic_def
         apply simp
        apply (simp add: default_ctxt_def vpr_program_from_method_decl_def)
        apply (rule ext)
        apply (case_tac "f = field_val")
        by (simp_all add: if_split)
      moreover have "\<Delta> = (ctxt_to_interp ?ctxt)"
        apply (simp add: default_ctxt_def ctxt_to_interp_def)
        apply (rule interp.equality)
        by (simp_all add: InterpFunsPredsEmpty)        
      ultimately show ?thesis
        using A1
        by metis
    qed

    hence r: "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
              (abs_stmt.Inhale P ;; compile False \<Delta> (tcfes tys) ?Ctr_main ;; abs_stmt.Exhale Q)"
      using \<open>P = _\<close> \<open>Q = _\<close>
      by simp


    show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) (abs_stmt.Inhale P ;; fst (translate \<Delta> tys C) ;; abs_stmt.Exhale Q)"
      apply (rule ConcreteSemantics.verifies_setI)
      apply (rule ConcreteSemantics.monotonicity_verifiesE)
           apply (simp_all; intro conjI)
             apply (simp_all add: assms(3) assms(12) wf_fst)
      using assms(12) assms(3) apply blast
         defer
         defer
         defer
         apply (subgoal_tac "\<omega> \<succeq> stabilize |\<omega>| ")
          apply assumption
         apply (metis already_stable core_stabilize_mono(2) max_projection_prop_pure_core mpp_smaller)
        defer
        defer
      apply (rule verifies_more_verifies)
         apply (rule verifies_more_seq)+
             apply (rule verifies_more_refl)
      apply (rule translation_refinement_syntactic_semantic(1)[OF assms(2) assms(1) wf_fst wf_snd])
            apply (simp_all add: assms)
      using assms(12) assms(3) apply blast
        apply (rule verifies_more_refl)
      using wf_fst assms(12) assms(3) apply argo
    proof -
      fix \<omega> assume asm0: "\<omega> \<in> atrue \<Delta> tys" "sep_algebra_class.stable \<omega>" "typed (tcfe \<Delta> tys) \<omega>"
      moreover have "stabilize |\<omega>| \<in> initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)"
        apply (rule stabilize_core_initial_state)
        apply (simp add: calculation(3))
        using calculation(1) no_trace_atrue by blast
    then show "ConcreteSemantics.verifies (tcfe \<Delta> tys)
          (abs_stmt.Inhale (make_semantic_assertion_untyped \<Delta> (tcfes tys) Ps) ;; compile False \<Delta> (tcfes tys) (fst (translate_syn C)) ;;
           abs_stmt.Exhale (make_semantic_assertion_untyped \<Delta> (tcfes tys) Qs))
          (stabilize |\<omega>| )"
        by (metis ConcreteSemantics.verifies_set_def TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed assms(12) assms(13) calculation(3) r stabilize_is_stable)
      
      show "typed (tcfe \<Delta> tys) (stabilize |\<omega>| )"
        using TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed calculation(3) by blast
      show "ConcreteSemantics.no_assert_assume (fst (translate \<Delta> tys C))"
        using valid_then_no_assume_assert by blast
      show "ConcreteSemantics.mono_custom (tcfe \<Delta> tys)"
        by (simp add: mono_custom_holds)
    qed
  qed

  fix Cv
  
  assume "Cv \<in> snd (translate \<Delta> tys C)"

  have "verifies_more_set (tcfe \<Delta> tys) (snd (translate \<Delta> tys C)) (compile False \<Delta> (tcfes tys) ` snd (translate_syn C))"
    apply (rule translation_refinement_syntactic_semantic(2)[OF assms(2) assms(1)])
    using wf_fst wf_snd by force+
  then obtain Cv_syn where ver_more: "Cv_syn \<in> snd (translate_syn C)" "verifies_more (tcfe \<Delta> tys) Cv (compile False \<Delta> (tcfes tys) Cv_syn)"
    using \<open>Cv \<in> snd (translate \<Delta> tys C)\<close> assms(1) assms(2) translation_refinement_snd wf_fst wf_snd by blast


  let ?mdeclAux = "triple_as_method_decl tys 
                              true_syn_assertion Cv_syn true_syn_assertion"
  let ?ctxt = "(default_ctxt (domains \<Delta>) ?mdeclAux) :: int total_context"

  have TypingAux: "stmt_typing (program_total (default_ctxt (interp.domains \<Delta>) (triple_as_method_decl tys true_syn_assertion Cv_syn true_syn_assertion)))
     (nth_option tys) (stmt.Seq (stmt.Seq (stmt.Inhale true_syn_assertion) Cv_syn) (stmt.Exhale true_syn_assertion))"
    using AuxiliaryMethodsCorrectAndTyped[OF \<open>Cv_syn \<in> _\<close>, simplified Let_def]    
    by (auto intro!: stmt_typing.intros
                        assertion_typing.intros atomic_assertion_typing.intros pure_exp_typing.intros)


  show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"
  proof -
    have ver1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) 
               (stmt.Seq (stmt.Seq (stmt.Inhale true_syn_assertion) Cv_syn) (stmt.Exhale true_syn_assertion)))"
      apply (rule VCG_to_verifies_set)
      using AuxiliaryMethodsCorrectAndTyped[OF \<open>Cv_syn \<in> _\<close>]
      unfolding \<open>mdecl = _\<close> Let_def  
         apply blast
        apply simp
        apply (rule TypingAux)
       using valid_a2t_stmt_translate_syn[OF ValidFrontendCmd] \<open>Cv_syn \<in> _\<close> ValidPrePost
       apply force
       by (simp_all add: default_ctxt_def AbsTypeWf ValidPrePost)

   moreover have A1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) Cv_syn)"
     apply (rule ConcreteSemantics.inhale_c_exhale_verifies_simplifies[where
         ?A="make_semantic_assertion_untyped (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) true_syn_assertion" and
         ?B="make_semantic_assertion_untyped (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) true_syn_assertion"])
      defer
     using ver1 apply simp
     unfolding make_semantic_assertion_gen_def apply simp
     unfolding ctxt_to_interp_def red_pure_assert_def corely_def emp_core_def apply simp
     by (metis core_is_pure pure_def red_pure_red_pure_exps.RedLit val_of_lit.simps(1))


    hence "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)) (compile False \<Delta> (tcfes tys) Cv_syn)"
    proof -
      \<comment>\<open>these proofs are duplicated from above\<close>
      have "tcfe \<Delta> tys = t2a_ctxt ?ctxt (nth_option tys)"
        unfolding t2a_ctxt_def
        apply (rule abs_type_context.equality, simp_all)
         apply (simp add: sem_store_def)
         apply (fastforce simp add: tcfe_eq default_ctxt_def)    
        using custom_context_tcfe_eq
        by blast      
      moreover have "tcfes tys = (nth_option tys, declared_fields (program_total ?ctxt))"
        unfolding type_ctxt_front_end_syntactic_def        
        apply clarify
        apply (rule conjI)
        using fst_tcfes_eq
        unfolding type_ctxt_front_end_syntactic_def
         apply simp
        apply (simp add: default_ctxt_def vpr_program_from_method_decl_def)
        apply (rule ext)
        apply (case_tac "f = field_val")
        by (simp_all add: if_split)    
      moreover have "\<Delta> = (ctxt_to_interp ?ctxt)"
        apply (simp add: default_ctxt_def ctxt_to_interp_def)
        apply (rule interp.equality)
        by (simp_all add: InterpFunsPredsEmpty)        
      ultimately show ?thesis
        using A1
        by argo        
    qed


    show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"
      apply (rule ConcreteSemantics.verifies_setI)
      apply (rule ConcreteSemantics.monotonicity_verifiesE)
      using \<open>Cv \<in> snd (translate \<Delta> tys C)\<close> wf_snd apply blast
      using mono_custom_holds apply blast
      using valid_then_no_assume_assert_snd
      using \<open>Cv \<in> snd (translate \<Delta> tys C)\<close> apply blast
        apply (rule verifies_more_verifies[OF ver_more(2)])
      defer
          defer
          defer
      defer
         apply (subgoal_tac "\<omega> \<succeq> stabilize |\<omega>|")
           apply assumption
          apply (metis already_stable core_stabilize_mono(2) max_projection_prop_pure_core mpp_smaller)
         apply simp_all
       apply (subgoal_tac "stabilize |\<omega>| \<in> initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)")
      apply (meson ConcreteSemantics.verifies_set_def TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed \<open>ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (initial_vcg_states_equi (t2a_ctxt (default_ctxt (interp.domains \<Delta>) (triple_as_method_decl tys true_syn_assertion Cv_syn true_syn_assertion)) (nth_option tys))) (compile False \<Delta> (tcfes tys) Cv_syn)\<close> stabilize_is_stable)
      apply (rule stabilize_core_initial_state)
        apply simp_all
      using no_trace_atrue apply fastforce
      using TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed by blast
  qed
qed

end