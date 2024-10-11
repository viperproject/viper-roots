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
  assumes "\<Delta> \<turnstile>CSL [P] C [Q]"
      and "well_typed_cmd \<Delta> C"
      and "TypedEqui.finite_context \<Delta>"
    shows "CSL \<Delta> P C Q"
  using assms CSL_sound by simp

text \<open>Theorem 8: Adequacy\<close>

theorem adequacy_CSL:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "\<Delta> \<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
      and "well_typed_cmd \<Delta> C"
      and "TypedEqui.typed_store \<Delta> (fst \<sigma>)"
      and "heap_typed type_ctxt_heap (snd \<sigma>)"
      and "TypedEqui.finite_context \<Delta>"
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

theorem sound_front_end_translation:

(* Well formedness *)
  assumes "wf_stmt \<Delta> tcfes C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"
      and "typed_stmt C" (* TODO: Unify the two notions of typing *)

(* Verification *)
      and "ConcreteSemantics.verifies_set tcfe atrue (abs_stmt.Inhale P ;; compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)) ;; abs_stmt.Exhale Q)"
      and "\<And>Cv. Cv \<in> compile False \<Delta> tcfes ` (snd (translate_syn \<Delta> tcfes C)) \<Longrightarrow> ConcreteSemantics.verifies_set tcfe atrue Cv"

shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  using assms sound_syntactic_translation by blast


(* TODO: Show simpler modular result, this one is end-to-end more complex corollary *)



text \<open>Lemma 3: What we call "convertible" is the following:
Not really, quite a few differences. Maybe we should make lemma and convertible in paper closer to here?
\<close>

(* Concrete for CSL *)
definition convertible where
  "convertible \<Gamma> C \<longleftrightarrow> (\<forall>P Q.
  (proof_obligations_valid (snd (translate \<Gamma> C)) \<and> ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C)) Q)
  \<longrightarrow> tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV])"

lemma lemma_3_inhale_translation_exhale:
  assumes "convertible \<Gamma> C"
      and "ConcreteSemantics.SL_proof tcfe P (Inhale A;; fst (translate \<Gamma> C);; Exhale B) Q"
      and "proof_obligations_valid (snd (translate \<Gamma> C))"
    shows "tcfe \<turnstile>CSL [P \<otimes> inhalify A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
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