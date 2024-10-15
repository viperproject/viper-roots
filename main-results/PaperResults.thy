theory PaperResults
  imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal VCGEndToEnd
  ViperAbstract.SymbolicExecSound  
begin


section \<open>Getting Started Guide for Exploration of the Isabelle Formalisation\<close>

text \<open>
Follow the instructions in the README for the artifact, which
shows how to identify that Isabelle has checked all files correctly that are loaded when this file
\<open>PaperResults.thy\<close> is opened.

Once Isabelle has successfully checked all files, continue here.

The following Isabelle theory file contains references to all the formalised results explicitly
mentioned in the paper. The theory file is structured using Isabelle sections and subsections,
which match those from the paper. Within each subsection we structured the different parts that we 
show via Isabelle paragraphs (there is one Isabelle paragraph per bullet point at the lowest level 
in the artifact README). You can use the "Sidekick" view on the right side of the Isabelle IDE to quickly 
jump to a section, subsection, or paragraph.

The following Isabelle theory file contains references to all the formalised results explicitly
mentioned in the paper. The theory file is structured using Isabelle sections and subsections,
which match those from the paper. Within each subsection we structured the different parts that we 
show via Isabelle paragraphs (there is one Isabelle paragraph per bullet point at the lowest level 
in the artifact README). You can use the "Sidekick" view on the right side of the Isabelle IDE to quickly 
jump to a section, subsection, or paragraph.

In the Isabelle IDE, you can ctrl-and-click on defined names, which takes you to the Isabelle source 
where the name is defined (for example, a standard definition or an Isabelle function). 
Whenever you jump somewhere via ctrl-and-clicking (for example, by jumping to a section or a definition),
you can use the two green arrow buttons at the top of the Isabelle IDE to jump back (or forward) to the 
previous position.

In this document, we make use of Isabelle's documentation features, which itself can contain Isabelle
elements (and are checked via Isabelle), to walk you through the formalisation of the definitions and 
rules in the paper. In particular, we use the following Isabelle document elements:

  \<^item> types (for example, \<^typ>\<open>('a, 'v, 'c) abs_stmt\<close>)
     --> you can click on defined names in types (i.e. \<open>abs_stmt\<close> in the example)
  \<^item> defined names (for example, \<^const>\<open>semantics.red_stmt\<close> --> you can click on defined names)
  \<^item> terms (for example, \<^term>\<open>semantics.red_stmt \<Delta>\<close>)
    --> you can click on defined names in terms (i.e. \<open>semantics.red_stmt\<close> in the example)
  \<^item> propositions (for example, \<^prop>\<open>red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>); these are just 
    boolean terms
    --> you can click on defined names in proposition (i.e. \<open>red_stmt_total\<close> and \<open>True\<close> in the example)
\<close>

section \<open>2: Key Ideas\<close>

subsection \<open>2.1: A Core Language for SL-Based IVLs\<close>

paragraph \<open>Figure 1\<close>
text \<open>The syntax of CoreIVL (Figure 1) is defined in the file AbstractSemantics.thy as
the type \<^typ>\<open>('a, 'v, 'c) abs_stmt\<close> (<-- you can ctrl+click on the name \<open>abs_stmt\<close> to jump to its definition,
as mentioned above).
                              
\<open>'a\<close>, \<open>'v\<close>, and \<open>'c\<close> are type parameters:
\<^item> \<open>'a\<close>: Type of state (IDF algebra...)
\<^item> \<open>'v\<close>: Type of values for local variables
\<^item> \<open>'c\<close>: Type of custom statements\<close>


subsection \<open>2.3: Operational Semantics and Back-End Verifiers\<close>

context semantics
begin

paragraph \<open>Figure 3 a)\<close> 
text\<open> 
In the file AbstractSemantics.thy, \<^const>\<open>red_stmt\<close> defines the operational semantics of CoreIVL,
which contains the rules in Figure 3 a). 
\<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close> in the paper is represented by \<^prop>\<open>red_stmt \<Delta> C \<omega> S\<close>.
\<close>

paragraph \<open>Definition 1\<close>
text\<open>C is correct for \<open>\<omega>\<close> iff \<^term>\<open>verifies \<Delta> C \<omega>\<close>\<close>

text \<open>TODO: Why do we define valid, but we don't have it?\<close>

definition valid where
  "valid \<Delta> C \<longleftrightarrow> (\<forall>\<omega>. verifies \<Delta> C \<omega>)"

subsection \<open>2.4: Axiomatic Semantics\<close>

paragraph \<open>Triple \<open>\<Delta> \<turnstile> [P] C [Q]\<close> and Figure 3b)\<close>
text \<open>
In the file AbstractSemantics.thy, \<^const>\<open>SL_proof\<close> defines the axiomatic semantics of CoreIVL,
which contains the rules in Figure 3 b).
\<open>\<Delta> \<turnstile> [P] C [Q]\<close> in the paper is represented by \<^prop>\<open>\<Delta> \<turnstile> [P] C [Q]\<close> (which is syntactic sugar for 
\<^prop>\<open>SL_proof \<Delta> P C Q\<close>)
\<close>

paragraph \<open>Theorem 2: Operational-to-Axiomatic Soundness\<close>

text \<open>The following is a general version of theorem 2:\<close>

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

text \<open>The following is theorem 2 as presented in the paper:\<close>

corollary operational_to_axiomatic_soundness:
  assumes "wf_abs_stmt \<Delta> C" \<comment>\<open>C is well-typed\<close>
      and "valid \<Delta> C"
    shows "\<exists>B. \<Delta> \<turnstile> [atrue_typed \<Delta>] C [B]"
  using assms good_atrue_typed operational_to_axiomatic_soundness_general 
  unfolding valid_def verifies_set_def by blast


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


paragraph \<open>Lemma 1 (Exhale-inhale)\<close>
text \<open>The following shows lemma 1 from the paper:\<close>
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


section \<open>3: Semantics\<close>

subsection \<open>3.1: An Algebra for Separation Logic and Implicit Dynamic Frames\<close>

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



subsection \<open>3.2: Operational Semantics\<close>


text \<open>Figure 7: In the file AbstractSemantics.thy, ...
\<^term>\<open>red_stmt\<close>
signature: \<^term>\<open>red_stmt \<Delta> C \<omega> S\<close>
represents \<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close>.\<close>

subsection \<open>3.3: Axiomatic Semantics\<close>

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

subsection \<open>3.4: ViperCore: Instantiating CoreIVL with Viper\<close>

text \<open>See the file Instantiation.thy.
(1) State: \<^typ>\<open>'a equi_state\<close>
(2) Custom statements:
  \<^item> \<^typ>\<open>'a custom\<close>
  \<^item> \<^term>\<open>FieldAssign e1 f e2\<close>
(3) Semantics of custom statements:
  \<^item> Operational: \<^term>\<open>red_custom_stmt \<Delta> (FieldAssign e1 f e2) \<omega> S\<close>
  \<^item> Axiomatic: \<^term>\<open>SL_Custom \<Delta> P (FieldAssign e1 f e2) Q\<close>
\<close>


section \<open>4: Back-End Soundness\<close>



subsection \<open>4.1: Symbolic Execution\<close>


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

subsection \<open>4.2: Verification Condition Generation\<close>

(* TODO! See with Gaurav *)





section \<open>5: Front-End Soundness\<close>

subsection \<open>5.1: An IDF-Based Concurrent Separation Logic\<close>

text \<open>ParImp defined in the file simple-frontend/ParImp.thy.
\<^item> Syntax:
  \<^item> Commands: \<^typ>\<open>cmd\<close>
  \<^item> Arithmetic expressions: \<^typ>\<open>exp\<close>
  \<^item> Boolean expressions: \<^typ>\<open>bexp\<close>
\<^item> Small-step semantics: \<^term>\<open>red C \<sigma> C' \<sigma>'\<close>, or equivalently, \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>\<close>

Program logic (Figure 9) defined in the file simple-frontend/CSL_IDF.thy:
\<^term>\<open>CSL_syn \<Delta> P C Q\<close> or \<^term>\<open>\<Delta> \<turnstile>CSL [P] C [Q]\<close>
\<close>





theorem soundness_CSL:
  assumes "tcfe \<Delta> tys \<turnstile>CSL [P] C [Q]"
      and "well_typed_cmd tys C"
    shows "CSL (tcfe \<Delta> tys) P C Q"
  using assms CSL_sound by blast

text \<open>Theorem 8: Adequacy\<close>


(* TODO: Make adequacy work with "\<otimes> atrue" for real e2e theorem? *)
theorem adequacy_CSL:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "tcfe \<Delta> tys \<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
      and "well_typed_cmd tys C"
      and "TypedEqui.typed_store (tcfe \<Delta> tys) (fst \<sigma>)"
      and "heap_typed type_ctxt_heap (snd \<sigma>)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  using assms adequacy by blast




subsection \<open>5.2: A Sound Front-End Translation\<close>

text \<open>Translation: Figure 10.
Defined in the file simple-frontend/SyntacticTranslation.thy.
For historical reasons, we first do a "semantic" translation (into CoreIVL), in simple-frontend/thy,
and then show that verification of the syntactic translation into ViperCore implies verification of the semantic translation.

\<^term>\<open>translate_syn C\<close>
\<close>


text \<open>Theorem 9: Soundness of the front-end translation\<close>


theorem sound_front_end_translation:

(* Well formedness *)

  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"

      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"

      and "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys)
     (abs_stmt.Inhale P ;; compile False \<Delta> (tcfes tys) (fst (translate_syn C)) ;; abs_stmt.Exhale Q)"
      and "\<And>Cv. Cv \<in> compile False \<Delta> (tcfes tys) ` snd (translate_syn C) \<Longrightarrow> ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"

shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  by (rule sound_syntactic_translation) (simp_all add: assms)




text \<open>Lemma 3: What we call "convertible" is the following:
Not really, quite a few differences. Maybe we should make lemma and convertible in paper closer to here?
\<close>

(* Concrete for CSL *)
definition convertible where
  "convertible \<Delta> tys C \<longleftrightarrow> (\<forall>P Q.
  (proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C)) \<and> ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q)
  \<longrightarrow> tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys])"

lemma lemma_3_inhale_translation_exhale:
  assumes "convertible \<Delta> tys C"
      and "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Inhale A;; fst (translate \<Delta> tys C);; Exhale B) Q"
      and "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
    shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [Q \<otimes> B \<otimes> atrue \<Delta> tys]"
  using invariant_translate_inhale_exhale_get_proof assms unfolding convertible_def invariant_translate_def
  by meson

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





theorem VCG_e2e_sound:
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
  using assms sound_syntactic_translation_VCG
  by blast



(*
TODO: Nice e2e theorems?
*)

end