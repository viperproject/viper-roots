theory VCGEndToEnd
imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal TotalViper.TraceIndepProperty
begin

section \<open>Theorem VCG back-end to ViperCore operational semantics\<close>

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

definition triple_as_method_decl :: "vtyp list \<Rightarrow> ViperLang.assertion \<Rightarrow> stmt \<Rightarrow> ViperLang.assertion \<Rightarrow> method_decl"
  where "triple_as_method_decl tys P C Q \<equiv> \<lparr> method_decl.args = [], 
                                         rets = tys, 
                                         pre = Atomic (Pure (ELit (LBool True))), 
                                         post = Atomic (Pure (ELit (LBool True))), 
                                         body = Some (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))\<rparr>"


definition vpr_program_from_method_decl :: "method_decl \<Rightarrow> program"
  where "vpr_program_from_method_decl m = 
           \<lparr> methods = [''m'' \<mapsto> m], predicates = Map.empty, funs = Map.empty, declared_fields = [field_val \<mapsto> TInt], domains = 0 \<rparr>"

definition default_ctxt :: "('a \<Rightarrow> abs_type) \<Rightarrow> method_decl \<Rightarrow> 'a total_context"
  where "default_ctxt d m = \<lparr> program_total = vpr_program_from_method_decl m, fun_interp_total = Map.empty, absval_interp_total = d \<rparr>"

definition is_initial_vcg_state
  where "is_initial_vcg_state ctxt \<Lambda> \<omega> \<equiv> 
             total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>) \<and>
             is_empty_total_full \<omega> \<and>
             (\<forall>x t. \<Lambda> x = Some t \<longrightarrow> (\<exists>v. get_store_total \<omega> x = Some v \<and> get_type (absval_interp_total ctxt) v = t))"

lemma vpr_method_correct_totalE: 
  assumes "vpr_method_correct_total ctxt R mdecl"
      and "vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total \<omega>)"
      and "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>)"
      and "is_empty_total_full \<omega>"
      and "red_inhale ctxt R (method_decl.pre mdecl) \<omega> rpre"
      and "rpre \<noteq> RFailure \<Longrightarrow> rpre = RNormal \<omega>pre"
      and "method_decl.body mdecl = Some mbody"      
      and Rec: "vpr_postcondition_framed ctxt R (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>) \<Longrightarrow>                 
                vpr_method_body_correct ctxt R mdecl \<omega>pre \<Longrightarrow> P"
    shows "P"
   using assms
   unfolding vpr_method_correct_total_def vpr_method_correct_total_aux_def
   by blast

lemma valid_a2t_exp_to_core:
  assumes "valid_a2t_exp e"
  shows "exp_in_core_subset e"
  using assms
  by (induction e) simp_all

lemma valid_a2t_atomic_assert_todo:
  assumes "valid_a2t_atomic_assert atm"
  shows "atomic_assert_in_core_subset atm"
  using assms
proof (induction atm)
  case (Acc e f e_p)
  then show ?case
    by (cases e_p) (simp_all add: valid_a2t_exp_to_core)
qed (simp_all add: valid_a2t_exp_to_core)
  
lemma valid_a2t_assert_to_core:
  assumes "valid_a2t_assert A"
  shows "assertion_in_core_subset A"
  using assms
  by (induction A)
     (simp_all add: valid_a2t_atomic_assert_todo valid_a2t_exp_to_core)

lemma valid_a2t_stmt_to_core:
  assumes "valid_a2t_stmt C"
  shows "stmt_in_core_subset C"
  using assms
  apply (induction C)
  by (simp_all add: valid_a2t_assert_to_core valid_a2t_exp_to_core)

lemma vpr_method_correct_red_stmt_total_set_ok:
  assumes MethodCorrect:
          "vpr_method_correct_total (ctxt :: 'a total_context) (\<lambda>_. True) (triple_as_method_decl tys P C Q)"
      and "\<Lambda> = nth_option tys"
      and ValidStmt: "valid_a2t_stmt C \<and> valid_a2t_assert P \<and> valid_a2t_assert Q"
    shows "red_stmt_total_set_ok ctxt (\<lambda>_. True) \<Lambda> ((stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))) {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
  unfolding red_stmt_total_set_ok_def
proof (rule allI, rule impI, rule notI, simp)
  fix \<omega> :: "'a full_total_state"
  assume Init: "is_initial_vcg_state ctxt \<Lambda> \<omega>"
     and Red: "red_stmt_total ctxt (\<lambda>_. True) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)) \<omega> RFailure"

  let ?mdecl = "triple_as_method_decl tys P C Q"

  show False
  proof (rule vpr_method_correct_totalE[OF MethodCorrect])
    from Init[simplified is_initial_vcg_state_def]
    show "vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args (triple_as_method_decl tys P C Q) @ rets (triple_as_method_decl tys P C Q)))
     (get_store_total \<omega>)"
      unfolding triple_as_method_decl_def vpr_store_well_typed_def \<open>\<Lambda> = _\<close>
      by simp
  next
    show "red_inhale ctxt (\<lambda>_. True) (method_decl.pre (triple_as_method_decl tys P C Q)) \<omega> (RNormal \<omega>)"
      unfolding triple_as_method_decl_def
      apply simp
      apply (rule inh_pure_normal)
      using RedLit
      by (metis val_of_lit.simps(1))
  next
    assume BodyCorrect: "vpr_method_body_correct ctxt (\<lambda>_. True) (triple_as_method_decl tys P C Q) \<omega>"

    show False
    proof (rule BodyCorrect[simplified vpr_method_body_correct_def, THEN allE[where ?x=RFailure], THEN impE], assumption,
           simp add: triple_as_method_decl_def)
      show "red_stmt_total ctxt (\<lambda>_. True) (nth_option tys) (stmt.Seq (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)) (stmt.Exhale (Atomic (Pure (ELit (LBool True))))))
     (\<omega>\<lparr>get_trace_total := [old_label \<mapsto> get_total_full \<omega>]\<rparr>) RFailure"
      proof (rule RedSeqFailureOrMagic)
        have InSubset: "stmt_in_core_subset (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
          apply (rule valid_a2t_stmt_to_core)
          using ValidStmt
          by simp

        show "red_stmt_total ctxt (\<lambda>_. True) (nth_option tys) (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))
     (\<omega>\<lparr>get_trace_total := [old_label \<mapsto> get_total_full \<omega>]\<rparr>) RFailure"
          using red_stmt_trace_indep[OF Red InSubset]
          unfolding \<open>\<Lambda> = _\<close> 
          by auto
      qed (simp)
    qed simp
  qed  (insert Init[simplified is_initial_vcg_state_def], auto simp: triple_as_method_decl_def)
qed


definition initial_vcg_states_equi where 
      "initial_vcg_states_equi \<Delta> \<equiv> {\<omega> :: int equi_state. stable \<omega> \<and> 
                                    typed \<Delta> \<omega> \<and> 
                                    get_trace \<omega> = Map.empty \<and> (\<forall>l. get_m \<omega> l = 0)
                                  }"

corollary VCG_to_verifies_set :                             
  assumes MethodCorrect: "vpr_method_correct_total ctxt (\<lambda>_ :: int full_total_state. True) (triple_as_method_decl tys P C Q)"
      and "\<Lambda> = nth_option tys"
      and Typed: "stmt_typing (program_total ctxt) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
      and ValidBodyPrePost: "valid_a2t_stmt C \<and> valid_a2t_assert P \<and> valid_a2t_assert Q"
      and AbsTypeWf: "abs_type_wf (absval_interp_total ctxt)"
    shows "ConcreteSemantics.verifies_set (t2a_ctxt ctxt \<Lambda>) (initial_vcg_states_equi (t2a_ctxt ctxt \<Lambda>))
            (compile False (ctxt_to_interp ctxt) (\<Lambda>, declared_fields (program_total ctxt)) 
               (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)))"  
proof (rule abstract_refines_total_verifies_set[OF _ Typed])
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>"
  hence "stable \<omega>" and "typed (t2a_ctxt ctxt \<Lambda>) \<omega>" and "get_trace \<omega> = Map.empty" and 
        EmptyMask: "\<forall>l. get_m \<omega> l = 0"
    unfolding initial_vcg_states_equi_def
    by auto

  from MethodCorrect \<open>\<Lambda> = _\<close>
  have "red_stmt_total_set_ok ctxt (\<lambda>_. True) \<Lambda> 
          ((stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))) {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
    using vpr_method_correct_red_stmt_total_set_ok ValidBodyPrePost
    by blast
    
  moreover have "a2t_states ctxt \<omega> \<subseteq> {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
  proof 
    fix \<omega>t
    assume "\<omega>t \<in> a2t_states ctxt \<omega>"

    show "\<omega>t \<in> {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"      
    proof 
      show "is_initial_vcg_state ctxt \<Lambda> \<omega>t"
        unfolding is_initial_vcg_state_def
      proof (intro conjI)
        from \<open>typed ?\<Delta> \<omega>\<close> have StoreTyped: 
          "well_typed_heap (custom_context (t2a_ctxt ctxt \<Lambda>)) (snd (get_abs_state \<omega>))"
          unfolding TypedEqui.typed_def well_typed_def
          by simp

        thus "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>t)"
          using \<open>\<omega>t \<in> _\<close>
          unfolding t2a_ctxt_def
          by (simp add: heap_typing_total_heap_well_typed snd_get_abs_state)
      next
        show "is_empty_total_full \<omega>t"          
          unfolding is_empty_total_full_def is_empty_total_def zero_mask_def
          apply (rule conjI)
          using EmptyMask \<open>\<omega>t \<in>  _\<close> 
           apply fastforce
          using a2t_states_mp_empty[OF \<open>\<omega>t \<in>  _\<close> ]
          unfolding zero_mask_def
          by simp
      next
        from \<open>typed ?\<Delta> \<omega>\<close> have StoreTyped: "store_typed (variables ?\<Delta>) (get_store \<omega>)"
          unfolding TypedEqui.typed_def TypedEqui.typed_store_def
          by blast

        show "\<forall>x t. \<Lambda> x = Some t \<longrightarrow> (\<exists>v. get_store_total \<omega>t x = Some v \<and> get_type (absval_interp_total ctxt) v = t)"
          using StoreTyped[simplified store_typed_def] t2a_ctxt_def sem_store_def
          by (smt (verit, ccfv_SIG) StoreTyped \<open>\<omega>t \<in> a2t_states ctxt \<omega>\<close> get_store_a2t_states sem_vtyp_to_get_type store_typed_lookup t2a_ctxt_variables)
      qed
    qed
  qed

  ultimately show
    "red_stmt_total_set_ok ctxt (\<lambda>_. True) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)) (a2t_states ctxt \<omega>)"  
    using red_stmt_total_set_ok_mono 
    by blast
next 
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>" 
     and TypedState: "typed (t2a_ctxt ctxt \<Lambda>) \<omega>"

  show "abs_state_typing ctxt \<Lambda> \<omega>"
    unfolding abs_state_typing_def
  proof (intro conjI)
    from TypedState have "store_typed (variables (t2a_ctxt ctxt \<Lambda>)) (get_store \<omega>)"
      unfolding TypedEqui.typed_def TypedEqui.typed_store_def
      by blast

    thus "store_typing ctxt \<Lambda> (get_store \<omega>)"
      by (simp add: store_typing_def t2a_ctxt_def)
  next
    from TypedState have HeapTyped: "well_typed_heap (custom_context (t2a_ctxt ctxt \<Lambda>)) (snd (get_abs_state \<omega>))"
      unfolding TypedEqui.typed_def well_typed_def
      by blast
    thus "well_typed_heap (sem_fields (absval_interp_total ctxt) (declared_fields (program_total ctxt))) (get_state \<omega>)"
      by (simp add: snd_get_abs_state t2a_ctxt_def)
  next
    show "partial_trace_typing ctxt (get_trace \<omega>)"
      using \<open>\<omega> \<in> _\<close>
      by (simp add: partial_trace_typing_def initial_vcg_states_equi_def)
  qed
next
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>"

  thus "a2t_state_wf ctxt (get_trace \<omega>)"
    unfolding a2t_state_wf_def initial_vcg_states_equi_def
    by (simp add: AbsTypeWf)
next
  show "valid_a2t_stmt (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
    by (simp add: ValidBodyPrePost)
qed 

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
    using assms(2) by blast
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
      using no_trace_atrue apply blast
      using TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed by blast
  qed
qed

end