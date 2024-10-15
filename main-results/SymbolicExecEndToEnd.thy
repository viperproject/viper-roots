theory SymbolicExecEndToEnd
imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstract.SymbolicExecSound
begin

section \<open>Theorem Symbolic Exec back-end to Frontend operational semantics\<close>

abbreviation true_syn_assertion
  where "true_syn_assertion \<equiv> (Atomic (Pure (ELit (LBool True))))"

theorem sound_syntactic_translation_symexec:
  fixes \<Delta> :: "('a, _) interp"
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"
      and "\<Delta> = def_interp"
      and "stmt_typing (fields_to_prog (snd (tcfes tys)))
            (nth_option tys)
            (stmt.Seq (stmt.Seq (stmt.Inhale Ps) (fst (translate_syn C))) (stmt.Exhale Qs))"

      and "sinit tys (snd (tcfes tys)) (\<lambda> \<sigma> :: 'a sym_state. sproduce \<sigma> Ps (\<lambda> \<sigma>.
           sexec \<sigma> (fst (translate_syn C)) (\<lambda> \<sigma>.
           sconsume \<sigma> Qs (\<lambda> \<sigma>. sym_stabilize \<sigma> (\<lambda> _. True)))))"

      and "\<And>Cv. Cv \<in> snd (translate_syn C) \<Longrightarrow>
            stmt_typing (fields_to_prog (snd (tcfes tys))) (nth_option tys) Cv \<and>
            sinit tys (snd (tcfes tys)) (\<lambda> \<sigma> :: 'a sym_state. sexec \<sigma> Cv (\<lambda> _. True))"

      and "P = make_semantic_assertion_gen False \<Delta> (tcfes tys) Ps"
      and "Q = make_semantic_assertion_gen False \<Delta> (tcfes tys) Qs"
    shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
proof (rule sound_syntactic_translation[OF assms(1-3)])

  let ?Ctr_main = "(fst (translate_syn C))"
  let ?\<Lambda> = "nth_option tys"
  let ?F = "(\<lambda>f. if f = field_val then Some TInt else None)"
  let ?Ctr_mainV = "(stmt.Seq (stmt.Seq (stmt.Inhale Ps) ?Ctr_main) (stmt.Exhale Qs))"

  have tcfe_s2a_eq: "(tcfe def_interp tys) = s2a_ctxt ?F ?\<Lambda>"
    apply (simp add:s2a_ctxt_def type_ctxt_front_end_def sem_store_def sem_fields_def)
    by (rule conjI; rule ext; simp add:type_ctxt_store_def type_ctxt_heap_def vints_def)


  show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys)
    (abs_stmt.Inhale P ;; compile False \<Delta> (tcfes tys) ?Ctr_main ;; abs_stmt.Exhale Q)"
  proof -
    have A1: "ConcreteSemantics.verifies_set (s2a_ctxt ?F ?\<Lambda>) (atrue \<Delta> tys)
               (compile False def_interp (?\<Lambda>, ?F) ?Ctr_mainV)"
      apply (rule sinit_sexec_verifies_set)
      using assms by (simp_all add:type_ctxt_front_end_syntactic_def atrue_def no_trace_def)

    show ?thesis
      using A1 assms(4,8,9) by (simp add:tcfe_s2a_eq type_ctxt_front_end_syntactic_def)
  qed

  fix Cv assume HCv: "Cv \<in> compile False \<Delta> (tcfes tys) ` snd (translate_syn C)"

  obtain Cvv where HCvv: "Cvv \<in> snd (translate_syn C)" "Cv = compile False \<Delta> (tcfes tys) Cvv"
    using HCv by blast

  show "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"
    using HCvv apply (simp add:tcfe_s2a_eq assms(4) type_ctxt_front_end_syntactic_def)
    apply (rule sinit_sexec_verifies_set)
      using assms by (auto simp add:type_ctxt_front_end_syntactic_def atrue_def no_trace_def)
  qed


end