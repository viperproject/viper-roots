theory PaperResults
  imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal VCGEndToEnd
  ViperAbstract.SymbolicExecSound  
begin


section \<open>Summary of the Results from the Paper\<close>

text \<open>This file contains the formal results mentioned the paper. It is organized in the same order
and with the same structure as the paper.
\<^item> You can use the panel "Sidekick" on the right to see and navigate the structure of the file, via sections and subsections.
\<^item> You can ctrl+click on terms to jump to their definition.
\<^item> After jumping to another location, you can come back to the previous location by clicking the
  green left arrow, on the right side of the menu above.\<close>


subsection \<open>2: Key Ideas\<close>

subsubsection \<open>2.1: A Core Language for SL-Based IVLs\<close>

text \<open>The syntax of CoreIVL (Figure 1) is defined in the file AbstractSemantics.thy as
the type \<^typ>\<open>('a, 'v, 'c) abs_stmt\<close> (<-- you can ctrl+click on the name \<open>abs_stmt\<close> to jump to its definition).
                              
\<open>'a\<close>, \<open>'v\<close>, and \<open>'c\<close> are type parameters:
\<^item> \<open>'a\<close>: Type of state (IDF algebra...)
\<^item> \<open>'v\<close>: Type of values for local variables
\<^item> \<open>'c\<close>: Type of custom statements\<close>


subsubsection \<open>2.3: Operational Semantics and Back-End Verifiers\<close>

context semantics
begin

text \<open>Figure 3 (a): In the file AbstractSemantics.thy, ...
\<^term>\<open>red_stmt\<close>
signature: \<^term>\<open>red_stmt \<Delta> C \<omega> S\<close>
represents \<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close>.
\<close>

text \<open>Definition 1: C is correct for \<open>\<omega>\<close> iff
\<^term>\<open>verifies \<Delta> C \<omega>\<close>
\<close>

text \<open>TODO: Why do we define valid, but we don't have it?\<close>

definition valid where
  "valid \<Delta> C \<longleftrightarrow> (\<forall>\<omega>. verifies \<Delta> C \<omega>)"

subsubsection \<open>2.4: Axiomatic Semantics\<close>

text \<open>Axiomatic semantics:
\<^item> \<^term>\<open>SL_proof \<Delta> P C Q\<close>
\<^item> \<^term>\<open>\<Delta> \<turnstile> [P] C [Q]\<close>\<close>


text \<open>Theorem 2: Operational-to-Axiomatic Soundness\<close>

text \<open>General theorem\<close>
theorem operational_to_axiomatic_soundness_general:
  assumes "verifies_set \<Delta> A C"
      and "wf_abs_stmt \<Delta> C"
      and "self_framing A"
      and "semi_typed \<Delta> A"
    shows "\<exists>B. \<Delta> \<turnstile> [A] C [B]"
  using assms Viper_implies_SL_proof by simp

definition atrue_typed where
  "atrue_typed \<Delta> = { \<omega>. typed \<Delta> (stabilize \<omega>)}"

lemma good_atrue_typed:
  "semi_typed \<Delta> (atrue_typed \<Delta>)"
  "self_framing (atrue_typed \<Delta>)"
  unfolding semi_typed_def atrue_typed_def apply blast
  apply (rule self_framingI)
  by (simp add: already_stable)

text \<open>Actual theorem 2\<close>
corollary operational_to_axiomatic_soundness:
  assumes "wf_abs_stmt \<Delta> C"
      and "valid \<Delta> C"
    shows "\<exists>B. \<Delta> \<turnstile> [atrue_typed \<Delta>] C [B]"
  using assms good_atrue_typed operational_to_axiomatic_soundness_general 
  unfolding valid_def verifies_set_def by blast


lemma wf_abs_stmt_havoc_list:
  assumes "set l \<subseteq> dom (variables \<Delta>)"
  shows "wf_abs_stmt \<Delta> (havoc_list l)"
  using assms by (induct l) simp_all

lemma entailment_1:
  assumes "entails_typed \<Delta> R F"
      and "entails A (R \<otimes> P)"
    shows "entails_typed \<Delta> A (P \<otimes> F)"
proof (rule entails_typedI)
  fix \<omega>
  assume asm0: "\<omega> \<in> A" "local.typed \<Delta> \<omega>"
  then obtain r p where "Some \<omega> = r \<oplus> p" "r \<in> R" "p \<in> P"
    by (meson assms(2) entails_def in_mono in_starE)
  then have "r \<in> F"
    by (metis asm0(2) assms(1) commutative entails_typed_def greater_equiv typed_smaller)
  then show "\<omega> \<in> P \<otimes> F"
    by (simp add: \<open>Some \<omega> = r \<oplus> p\<close> \<open>p \<in> P\<close> add_set_commm in_starI)
qed


lemma entailment_2:
  "entails_typed \<Delta> (Q \<otimes> F) (F \<otimes> Set.filter (local.typed \<Delta> \<circ> stabilize) Q)"
  apply (rule entails_typedI)
  apply (erule in_starE)
  by (smt (verit, best) commutative comp_eq_dest_lhs greater_def member_filter typed_smaller typed_state.typed_state_then_stabilize_typed typed_state_axioms x_elem_set_product)


text \<open>Lemma 1\<close>
lemma exhale_havoc_inhale:
  assumes context_well_formed: "wrC C \<subseteq> dom (variables \<Delta>) \<and> finite_context \<Delta>"

  assumes "self_framing P"
      and "self_framing Q"
      and "\<Delta> \<turnstile> [A] Exhale P;; havoc_list (wrL C);; Inhale Q [B]"
      and "SomeSL \<Delta> P C Q"
      and FrameRule: "\<And>P Q F. self_framing P \<Longrightarrow> self_framing F \<Longrightarrow>
                    SomeSL \<Delta> P C Q \<Longrightarrow> free_vars \<Delta> F \<inter> wrC C = {} \<Longrightarrow> SomeSL \<Delta> (P \<otimes> F) C (Q \<otimes> F)"
      and ConsequenceRule: "\<And>P Q P' Q'. SomeSL \<Delta> P C Q \<Longrightarrow> entails_typed \<Delta> P' P \<Longrightarrow> entails_typed \<Delta> Q Q' \<Longrightarrow> SomeSL \<Delta> P' C Q'"
    shows "SomeSL \<Delta> A C B"

  apply (rule SL_proof_Seq_elim[OF assms(4)])
  apply (erule SL_proof_Seq_elim)
  apply (drule SL_proof_Havoc_list_elim)
  using context_well_formed wf_abs_stmt_havoc_list wrL_wrC_same apply blast
  using context_well_formed apply force
  apply (erule SL_proof_Inhale_elim)
  apply (erule SL_proof_Exhale_elim)
  subgoal for F R
    apply (rule ConsequenceRule)
      apply (rule FrameRule[of P F Q])
         apply (simp_all add: assms)
    using wrL_wrC_same apply auto[1]
    using entailment_1 apply blast
    using entailment_2 by blast
  done


subsection \<open>3: Semantics\<close>

subsubsection \<open>3.1: An Algebra for Separation Logic and Implicit Dynamic Frames\<close>

text \<open>See file: SepAlgebraDef.thy. Definition 3.
Layered:
\<^item> \<^class>\<open>pcm\<close>: Accepts a type and binary operation \<^term>\<open>a \<oplus> b\<close>, first 3 axioms.
\<^item> \<^class>\<open>pcm_with_core\<close>: Adds core \<^term>\<open>|x|\<close>, and next 5 axioms.
\<^item> \<^class>\<open>sep_algebra\<close>: Adds \<^term>\<open>stable\<close> and \<^term>\<open>stabilize\<close>, last 5 axioms.\<close>

text \<open>Instantiations:
For combinators, see file SepAlgebra.thy.
State model \<open>\<Sigma>\<^sub>I\<^sub>D\<^sub>F\<close> defined in file EquiViper.thy. Actually our state is much more complex.
\<close>

text \<open>State model for CoreIVL:
\<^typ>\<open>('v, 'a) abs_state\<close>, where
\<^item> \<open>'v\<close> is the type of values for local variables, and
\<^item> \<open>'a\<close> is the type of states (IDF algebra).\<close>


text \<open>Definition 4:
\<^item> P is self-framing: \<^term>\<open>self_framing P\<close>                 
\<^item> The state \<omega> frames the assertion P: \<^term>\<open>rel_stable_assertion \<omega> P\<close>
  \<^item> see \<^term>\<open>wf_assertion A\<close>
(* TODO: Explain why it's the same *)
\<^item> The assertion B frames the assertion P: \<^term>\<open>framed_by B P\<close>
\<^item> The assertion P frames the expression e: \<^term>\<open>framed_by_exp P e\<close>
\<close>

lemma wf_assertion_add:
  assumes "wf_assertion P"
  shows "wf_assertion ({\<omega>} \<otimes> P)"
  apply (rule wf_assertionI)
  apply (erule in_starE)
  apply simp
proof -
  fix x' x b assume asm0: "pure_larger x' x" "b \<in> P" "Some x = \<omega> \<oplus> b"
  then obtain p where "pure p" "Some x' = x \<oplus> p"
    unfolding pure_larger_def by blast
  then obtain b' where "Some b' = b \<oplus> p"
    using asm0(3) compatible_smaller greater_equiv by blast
  then have "b' \<in> P"
    using \<open>pure p\<close> asm0(2) assms pure_larger_def typed_state.wf_assertionE typed_state_axioms by blast
  moreover have "Some x' = \<omega> \<oplus> b'"
    using \<open>Some b' = b \<oplus> p\<close> \<open>Some x' = x \<oplus> p\<close> asm0(3) asso1 by force
  ultimately show "x' \<in> {\<omega>} \<otimes> P"
    unfolding add_set_def by blast
qed

text \<open>The following lemma shows that the definition in the paper and \<^term>\<open>rel_stable_assertion \<omega> P\<close>
agree for well-formed assertions (i.e., all relevant assertions).\<close>

lemma rel_stable_assertion_same_as_in_paper:
  assumes "wf_assertion P"
  shows "rel_stable_assertion \<omega> P \<longleftrightarrow> self_framing ({\<omega>} \<otimes> P)"
  unfolding rel_stable_assertion_def self_framing_def
  apply (rule)
  apply (meson Stable_def assms in_Stabilize subsetD wf_assertion_add wf_assertion_stabilize)
  using StableI by blast



subsubsection \<open>3.2: Operational Semantics\<close>


text \<open>Figure 7: In the file AbstractSemantics.thy, ...
\<^term>\<open>red_stmt\<close>
signature: \<^term>\<open>red_stmt \<Delta> C \<omega> S\<close>
represents \<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close>.\<close>

subsubsection \<open>3.3: Axiomatic Semantics\<close>

text \<open>Axiomatic semantics:
\<^item> \<^term>\<open>SL_proof \<Delta> P C Q\<close>
\<^item> \<^term>\<open>\<Delta> \<turnstile> [P] C [Q]\<close>\<close>

text \<open>Lemma 2\<close>

lemma lemma_2_from_operational_to_axiomatic_semantics:
  fixes S :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>l \<omega>. (l, \<omega>) \<in> \<Omega> \<Longrightarrow> stable \<omega> \<and> typed \<Delta> \<omega> \<and> red_stmt \<Delta> C \<omega> (S (l, \<omega>))"
      and "wf_abs_stmt \<Delta> C"
    shows "\<Delta> \<turnstile> [Stabilize (snd ` \<Omega>)] C [Stabilize (\<Union>\<omega>\<in>\<Omega>. S \<omega>)]"
  apply (rule Viper_implies_SL_proof_aux)
  using assms(1) apply force
  using assms(2) apply simp
  unfolding wf_set_def wf_state_def using assms(1) by auto


text \<open>Completeness\<close>


theorem completeness:
  assumes "wf_abs_stmt \<Delta> C"
      and "typed \<Delta> \<omega>"

  assumes "\<Delta> \<turnstile> [P] C [Q]"
      and "\<omega> \<in> P"
      and "stable \<omega>"
    shows "\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> Q"
  using assms SL_proof_implies_Viper by blast

end

subsubsection \<open>3.4: ViperCore: Instantiating CoreIVL with Viper\<close>

text \<open>See the file Instantiation.thy.
(1) State: \<^typ>\<open>'a equi_state\<close>
(2) Custom statements:
  \<^item> \<^typ>\<open>'a custom\<close>
  \<^item> \<^term>\<open>FieldAssign e1 f e2\<close>
(3) Semantics of custom statements:
  \<^item> Operational: \<^term>\<open>red_custom_stmt \<Delta> (FieldAssign e1 f e2) \<omega> S\<close>
  \<^item> Axiomatic: \<^term>\<open>SL_Custom \<Delta> P (FieldAssign e1 f e2) Q\<close>
\<close>


subsection \<open>4: Back-End Soundness\<close>



subsubsection \<open>4.1: Symbolic Execution\<close>


theorem sinit_sexec_verifies_set :
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  assumes "sinit tys F (\<lambda> \<sigma> :: 'a sym_state. sexec \<sigma> C Q)"
  (* TODO: replace with nth_option from TotalUtil? *)
  assumes "\<Lambda> = (\<lambda> v. if v < length tys then Some (tys ! v) else None)"
  assumes "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> get_trace \<omega> = Map.empty"
  shows "ConcreteSemantics.verifies_set (s2a_ctxt F \<Lambda>) (A :: 'a equi_state set) (compile False def_interp (\<Lambda>, F) C)"
  apply (rule sexec_verifies_set[where Q=Q]; (rule assms)?)
  using assms apply -
  subgoal for \<omega>
    apply (erule (1) sinit_sound[where \<omega>=\<omega>])
    by (auto simp add:TypedEqui.typed_def TypedEqui.typed_store_def s2a_ctxt_def)
  done

(* TODO! See with Gaurav, and Michael? *)

subsubsection \<open>4.2: Verification Condition Generation\<close>

(* TODO! See with Gaurav *)





subsection \<open>5: Front-End Soundness\<close>

subsubsection \<open>5.1: An IDF-Based Concurrent Separation Logic\<close>

text \<open>ParImp defined in the file simple-frontend/ParImp.thy.
\<^item> Syntax:
  \<^item> Commands: \<^typ>\<open>cmd\<close>
  \<^item> Arithmetic expressions: \<^typ>\<open>exp\<close>
  \<^item> Boolean expressions: \<^typ>\<open>bexp\<close>
\<^item> Small-step semantics: \<^term>\<open>red C \<sigma> C' \<sigma>'\<close>, or equivalently, \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>\<close>

Program logic (Figure 9) defined in the file simple-frontend/CSL_IDF.thy:
\<^term>\<open>CSL_syn \<Delta> P C Q\<close> or \<^term>\<open>\<Delta> \<turnstile>CSL [P] C [Q]\<close>
\<close>



(*
TODO:
Maybe explain the following:
1. Entailment is typed in consequence rule
| RuleConsTyped: "\<lbrakk>\<Delta> \<turnstile>CSL [P] C [Q]; ConcreteSemantics.entails_typed \<Delta> P' P; ConcreteSemantics.entails_typed \<Delta> Q Q'\<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile>CSL [P'] C [Q']"

2. Those rules are convenient

| RuleStabilizeTyped: "\<Delta> \<turnstile>CSL [P] C [Q] \<Longrightarrow> \<Delta> \<turnstile>CSL [Stabilize P] C [Stabilize Q]"
| RuleInhalify: "\<Delta> \<turnstile>CSL [P] C [Q] \<Longrightarrow> \<Delta> \<turnstile>CSL [P] C [Set.filter (typed \<Delta> \<circ> stabilize) Q]"

*)



theorem soundness_CSL:
  assumes "tcfe tys \<turnstile>CSL [P] C [Q]"
      and "well_typed_cmd tys C"
      and "TypedEqui.finite_context \<Delta>"
    shows "CSL (tcfe tys) P C Q"
  using assms CSL_sound by simp

text \<open>Theorem 8: Adequacy\<close>

theorem adequacy_CSL:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "tcfe tys \<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
      and "well_typed_cmd tys C"
      and "TypedEqui.typed_store (tcfe tys) (fst \<sigma>)"
      and "heap_typed type_ctxt_heap (snd \<sigma>)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  using assms adequacy by blast




subsubsection \<open>5.2: A Sound Front-End Translation\<close>

text \<open>Translation: Figure 10.
Defined in the file simple-frontend/SyntacticTranslation.thy.
For historical reasons, we first do a "semantic" translation (into CoreIVL), in simple-frontend/FrontEndTranslation.thy,
and then show that verification of the syntactic translation into ViperCore implies verification of the semantic translation.

\<^term>\<open>translate_syn \<Delta> F C\<close>
(* TODO: Explain F *)\<close>


text \<open>Theorem 9: Soundness of the front-end translation\<close>

lemma denot_mono:
  assumes "a \<succeq> b"
      and "Some (VInt (edenot e (get_store b))) = Some v"
    shows "Some (VInt (edenot e (get_store a))) = Some v"
  using assms
  apply (induct e)
    apply simp_all
  apply (simp add: greater_charact)
  by (simp add: greater_charact)

lemma wf_exp_semantify[simp]:
  "wf_exp (semantify_exp x2)"
  unfolding semantify_exp_def
  apply (rule wf_expI)
   apply simp
  using denot_mono by fast


lemma typed_exp_semantify_vints[simp]:
  "TypedEqui.typed_exp vints (semantify_exp x2)"
  unfolding TypedEqui.typed_exp_def semantify_exp_def
  by (simp add: vints_def)


lemma wf_exp_semantify_heap_loc[simp]:
  "wf_exp (semantify_heap_loc r)"
  unfolding semantify_heap_loc_def
  apply (rule wf_expI)
   apply simp_all
  apply (simp add: core_charact_equi(2) core_structure(2))
  by (smt (z3) get_address_simp get_vh_Some_greater greater_cover_store option.discI option.sel some_eq_imp)


lemma semantify_heap_loc_typed[simp]:
  "TypedEqui.typed_exp vints (semantify_heap_loc r)"
  unfolding semantify_heap_loc_def TypedEqui.typed_exp_def vints_def
  apply simp
  by force

lemma wf_exp_semantify_addr[simp]:
  "wf_exp (semantify_addr x1)"
  unfolding semantify_addr_def
  apply (rule wf_expI)
  apply simp_all
  by (metis (mono_tags, lifting) Eps_cong greater_charact_equi simplify_if_some_none)

lemma type_ctxt_field_val[simp]:
  "type_ctxt_heap field_val = Some vints"
  unfolding type_ctxt_heap_def by auto

lemma in_dom_type_ctxt_store:
  assumes "x1 < length tys"
    shows "x1 \<in> dom (type_ctxt_store tys)"
  using assms unfolding type_ctxt_store_def by auto

lemma wf_assertion_stabilize[simp]:
  "TypedEqui.wf_assertion (Stabilize A)"
  apply (rule TypedEqui.wf_assertionI)
  by (simp add: pure_larger_stabilize_same)

lemma wf_exp_semantify_bexp[simp]:
  "wf_exp (semantify_bexp b)"
  unfolding semantify_bexp_def
  apply (rule wf_expI)
  apply simp
  by (metis greater_charact)

lemma well_typed_cmd_all_written_vars_def:
  assumes "well_typed_cmd tys C"
  shows "set (wrL C) \<subseteq> dom (type_ctxt_store tys)"
  using assms
  apply (induct C)
  unfolding type_ctxt_store_def
           apply simp_all
  by force+

lemma assertion_while_or_par_wf:
  assumes "well_typed_cmd tys C1 \<and> well_typed_cmd tys C2"
    shows "set (wrL C1 @ wrL C2) \<subseteq> dom (type_ctxt_store tys)"
  by (simp add: assms well_typed_cmd_all_written_vars_def)

(*
lemma wf_assertion_par:
  assumes "self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1)"
      and "self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2)"
      and "self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1)"
      and "self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2)"
      and "wf_stmt tys \<Gamma> C1"
      and "wf_stmt tys \<Gamma> C2"
      and "well_typed_cmd tys C1 \<and> well_typed_cmd tys C2"
      
    ConcreteSemantics.wf_abs_stmt \<lparr>variables = type_ctxt_store tys, custom_context = type_ctxt_heap\<rparr> (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2)) \<and>
    TypedEqui.wf_assertion (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1 \<otimes> make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2)
*)

lemma wf_stmt_implies_wf_translation:
  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"
  shows "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))"
  using assms
  apply (induct C)
           apply (simp_all add: type_ctxt_front_end_def type_ctxt_store_def)
  apply (simp add: in_dom_type_ctxt_store)
  apply (simp add: Let_def)
  apply (rule conjI)
  apply (metis self_framing_eq test_self_framing typed_self_framing_star wf_assertion_stabilize)
   apply (rule conjI)
    apply (metis ConcreteSemantics.wf_abs_stmt_havoc_list abs_type_context.select_convs(1) assertion_while_or_par_wf)
  apply (metis self_framing_eq typed_self_framing_star wf_assertion_stabilize)
   apply (rule conjI)
   apply (metis self_framing_eq test_self_framing wf_assertion_stabilize)
   apply (rule conjI)
  apply (simp add: ConcreteSemantics.wf_abs_stmt_havoc_list well_typed_cmd_all_written_vars_def)
  by (metis self_framing_eq self_framing_inter wf_assertion_stabilize)




lemma wf_stmt_implies_wf_translation_snd:
  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"
      and "Cv \<in> snd (translate tys \<Gamma> C)"
    shows "ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
  using assms
  apply (induct C)
           apply (simp_all add: type_ctxt_front_end_def type_ctxt_store_def Let_def)
     apply metis
    apply (erule disjE)
     apply simp
  apply (rule conjI)
      apply (metis self_framing_eq wf_assertion_stabilize)
     apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
    apply (erule disjE)
     apply simp
  apply (rule conjI)
      apply (metis self_framing_eq wf_assertion_stabilize)
     apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
    apply (erule disjE)
     apply blast+
    apply (erule disjE)
  apply simp
   apply (rule conjI)+
  apply (metis self_framing_eq self_framing_inter wf_assertion_stabilize)
  apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
  by blast


theorem sound_front_end_translation:

(* Well formedness *)

  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"

      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"

      and "ConcreteSemantics.verifies_set (FrontEndTranslation.tcfe tys) (atrue tys)
     (abs_stmt.Inhale P ;; compile False \<Gamma> (tcfes tys) (fst (translate_syn \<Gamma> (tcfes tys) C)) ;; abs_stmt.Exhale Q)"
      and "\<And>Cv. Cv \<in> compile False \<Gamma> (tcfes tys) ` snd (translate_syn \<Gamma> (tcfes tys) C) \<Longrightarrow> ConcreteSemantics.verifies_set (FrontEndTranslation.tcfe tys) (atrue tys) Cv"

shows "tcfe tys \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  apply (rule sound_syntactic_translation[of _ \<Gamma>])
        apply (simp_all add: assms)
  apply (simp add: assms(2) assms(1) wf_stmt_implies_wf_translation)
  using assms(1) assms(2) wf_stmt_implies_wf_translation_snd by blast





text \<open>Lemma 3: What we call "convertible" is the following:
Not really, quite a few differences. Maybe we should make lemma and convertible in paper closer to here?
\<close>

(* Concrete for CSL *)
definition convertible where
  "convertible tys \<Gamma> C \<longleftrightarrow> (\<forall>P Q.
  (proof_obligations_valid tys (snd (translate tys \<Gamma> C)) \<and> ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q)
  \<longrightarrow> tcfe tys \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV])"

lemma lemma_3_inhale_translation_exhale:
  assumes "convertible tys \<Gamma> C"
      and "ConcreteSemantics.SL_proof (tcfe tys) P (Inhale A;; fst (translate tys \<Gamma> C);; Exhale B) Q"
      and "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
    shows "tcfe tys \<turnstile>CSL [P \<otimes> inhalify tys A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
  using invariant_translate_inhale_exhale_get_proof assms unfolding convertible_def invariant_translate_def
  by presburger

(* TODO: Explain discrepancy with inhalify? *)

context semantics
begin

text \<open>Lemma 4\<close>
lemma lemma_4_exhale_havoc_inhale:
  assumes context_well_formed: "wrC C \<subseteq> dom (variables \<Delta>) \<and> finite_context \<Delta>"

  assumes "self_framing P"
      and "self_framing Q"
      and "\<Delta> \<turnstile> [A] Exhale P;; havoc_list (wrL C);; Inhale Q [B]"
      and "SomeSL \<Delta> P C Q"
      and FrameRule: "\<And>P Q F. self_framing P \<Longrightarrow> self_framing F \<Longrightarrow>
                    SomeSL \<Delta> P C Q \<Longrightarrow> free_vars \<Delta> F \<inter> wrC C = {} \<Longrightarrow> SomeSL \<Delta> (P \<otimes> F) C (Q \<otimes> F)"
      and ConsequenceRule: "\<And>P Q P' Q'. SomeSL \<Delta> P C Q \<Longrightarrow> entails_typed \<Delta> P' P \<Longrightarrow> entails_typed \<Delta> Q Q' \<Longrightarrow> SomeSL \<Delta> P' C Q'"
    shows "SomeSL \<Delta> A C B"
  using local.exhale_havoc_inhale[of C \<Delta> P Q A B SomeSL] assms by blast

end




(*
TODO: Nice e2e theorems?
*)

end