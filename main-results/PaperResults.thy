theory PaperResults
  imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal VCGEndToEnd
  ViperAbstract.SymbolicExecSound  
begin


section \<open>Getting Started Guide for Exploration of the Isabelle Formalisation\<close>

text \<open>TODO: make sure text here is in sync with README\<close>

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
  \<^item> type classes (for example, \<^class>\<open>sep_algebra\<close> --> you can click on defined names in type classes)
  \<^item> defined names (for example, \<^const>\<open>red_stmt_total\<close> --> you can click on defined names)
  \<^item> terms (for example, \<^term>\<open>red_stmt_total ctxt\<close>)
    --> you can click on defined names in terms (i.e. \<open>red_stmt_total ctxt\<close> in the example)
  \<^item> propositions (for example, \<^prop>\<open>red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>); these are just 
    boolean terms
    --> you can click on defined names in proposition (i.e. \<open>red_stmt_total\<close> and \<open>True\<close> in the example)
  \<^item> proved lemmas (for example, @{thm VCG_to_verifies_set})
    --> you can click on the lemma names (i.e. \<open>VCG_to_verifies_set\<close> in the example)

We also provide links to files in some cases such as @{file "../vipersemabstract/Instantiation.thy"}
(which you can also ctrl-click on).
\<close>

section \<open>2: Key Ideas\<close>

subsection \<open>2.1: A Core Language for SL-Based IVLs\<close>

paragraph \<open>Figure 1\<close>
text \<open>The syntax of CoreIVL (Figure 1) is defined as the type \<^typ>\<open>('a, 'v, 'c) abs_stmt\<close> 
(<-- you can ctrl+click on the name \<open>abs_stmt\<close> to jump to its definition, as mentioned above).
                              
\<open>'a\<close>, \<open>'v\<close>, and \<open>'c\<close> are type parameters:
\<^item> \<open>'a\<close>: Type of state (IDF algebra...)
\<^item> \<open>'v\<close>: Type of values for local variables
\<^item> \<open>'c\<close>: Type of custom statements\<close>


subsection \<open>2.3: Operational Semantics and Back-End Verifiers\<close>

context semantics
begin

paragraph \<open>Figure 3 a)\<close> 
text\<open> 
\<^const>\<open>red_stmt\<close> defines the operational semantics of CoreIVL, which contains the rules in Figure 3 a). 
\<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close> in the paper is represented by \<^prop>\<open>red_stmt \<Delta> C \<omega> S\<close>.
\<close>

paragraph \<open>Definition 1\<close>
text\<open>C is correct for \<open>\<omega>\<close> iff \<^term>\<open>verifies \<Delta> C \<omega>\<close>\<close>

text \<open>TODO:
- Use valid later?
- Restrict it to well-formed states?\<close>


definition valid where
  "valid \<Delta> C \<longleftrightarrow> (\<forall>\<omega>. verifies \<Delta> C \<omega>)"

subsection \<open>2.4: Axiomatic Semantics\<close>

paragraph \<open>Triple \<open>\<Delta> \<turnstile> [P] C [Q]\<close> and Figure 3b)\<close>
text \<open>
\<^const>\<open>SL_proof\<close> defines the axiomatic semantics of CoreIVL,
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

text \<open>The following is theorem 2 as presented in the paper:\<close>

corollary operational_to_axiomatic_soundness:
  assumes "wf_abs_stmt \<Delta> C" \<comment>\<open>C is well-typed\<close>
      and "valid \<Delta> C"
    shows "\<exists>B. \<Delta> \<turnstile> [atrue_typed \<Delta>] C [B]"
  using assms good_atrue_typed operational_to_axiomatic_soundness_general 
  unfolding valid_def verifies_set_def by blast


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

paragraph \<open>Definition 3 (IDF algebra) and Figure 5\<close>
text \<open>IDF algebras are formalized via type type class \<^class>\<open>sep_algebra\<close>. 
This type class is defined via other type classes. To see all the axioms listed in Figure 5, one must
inspect all of the type classes.
More concretely, \<^class>\<open>sep_algebra\<close> is defined in terms of type classes \<^class>\<open>pcm_with_core\<close>, which
is defined in terms of \<^class>\<open>pcm\<close>. The following gives a brief description of what each type class
contributes and which axioms shown in Figure 5 it contains:

\<^item> \<^class>\<open>pcm\<close>: Accepts a type and binary operation \<^term>\<open>a \<oplus> b\<close> and contains the first 3 axioms (top row) 
  in Figure 5 (note that here, the associativity axiom in Figure 5 is split into two axioms)
\<^item> \<^class>\<open>pcm_with_core\<close>: Adds core \<^term>\<open>|x|\<close>, and contains the next 5 axioms in Figure 5 (second row
  and first axiom in third row).
\<^item> \<^class>\<open>sep_algebra\<close>: Adds \<^term>\<open>stable\<close> and \<^term>\<open>stabilize\<close>, and contains the last 5 axioms. in 
  Figure 5 (all axioms in Figure 5 that contain \<open>stabilize\<close>)\<close>

paragraph\<open>Instantiations\<close>
text \<open>Our concrete IDF state model \<Sigma>_IDF is defined in \<^typ>\<open>'a virtual_state\<close>, which is a subset type
of \<^typ>\<open>'a pre_virtual_state\<close> (restricting permissions to be at most 1 and requiring that nonzero 
permission for a heap location \<open>loc\<close> implies that the partial heap defines a value for \<open>loc\<close>.

We prove that \<^typ>\<open>'a virtual_state\<close> forms an IDF algebra in the file
 @{file "../vipersemabstract/EquiSemAuxLemma.thy"} 
(look for the line "instantiation virtual_state :: (type) sep_algebra").

TODO is there more to say here?
\<close>

paragraph \<open>State model for CoreIVL\<close>
text \<open>The state model for CoreIVL is given by \<^typ>\<open>('v, 'a) abs_state\<close>, where
\<^item> \<open>'v\<close> is the type of values for local variables, and
\<^item> \<open>'a\<close> is the type of states (IDF algebra).\<close>

paragraph\<open>Definition 4\<close>
text \<open>Definition 4:
\<^item> P is self-framing: \<^term>\<open>self_framing P\<close>                 
\<^item> The state \<omega> frames the assertion P: \<^term>\<open>rel_stable_assertion \<omega> P\<close>
  \<^item> see \<^term>\<open>wf_assertion A\<close>
\<^item> The assertion B frames the assertion P: \<^term>\<open>framed_by B P\<close>
\<^item> The assertion P frames the expression e: \<^term>\<open>framed_by_exp P e\<close>
\<close>

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


paragraph \<open>Figure 6\<close>
text \<open>
\<^const>\<open>red_stmt\<close> defines the operational semantics of CoreIVL, which contains the rules in Figure 6. 
\<open>\<langle>C, \<omega>\<rangle> \<rightarrow>\<^sub>\<Delta> S\<close> in the paper is represented by \<^prop>\<open>red_stmt \<Delta> C \<omega> S\<close>.
\<close>

subsection \<open>3.3: Axiomatic Semantics\<close>

paragraph \<open>Triple \<open>\<Delta> \<turnstile> [P] C [Q]\<close> and Figure 7\<close>
text \<open>
\<^const>\<open>SL_proof\<close> defines the axiomatic semantics of CoreIVL,
which contains the rules in Figure 7.
\<open>\<Delta> \<turnstile> [P] C [Q]\<close> in the paper is represented by \<^prop>\<open>\<Delta> \<turnstile> [P] C [Q]\<close> (which is syntactic sugar for 
\<^prop>\<open>SL_proof \<Delta> P C Q\<close>)
\<close>

paragraph \<open>Lemma 2\<close>
text\<open>Lemma 2 is given by:\<close>

lemma lemma_2_from_operational_to_axiomatic_semantics:
  fixes S :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>l \<omega>. (l, \<omega>) \<in> \<Omega> \<Longrightarrow> stable \<omega> \<and> typed \<Delta> \<omega> \<and> red_stmt \<Delta> C \<omega> (S (l, \<omega>))"
      and "wf_abs_stmt \<Delta> C"
    shows "\<Delta> \<turnstile> [Stabilize (snd ` \<Omega>)] C [Stabilize (\<Union>\<omega>\<in>\<Omega>. S \<omega>)]"
  apply (rule Viper_implies_SL_proof_aux)
  using assms(1) apply force
  using assms(2) apply simp
  unfolding wf_set_def wf_state_def using assms(1) by auto


paragraph \<open>Theorem 5: Completeness\<close>
text\<open>Theorem 5 is given by the following.
Note that we require C to be well-formed, i.e., \<^term>\<open>wf_abs_stmt \<Delta> C\<close>
TODO: Explain what it checks:
- Assertions are well-formed (cannot become false because of more info (pure state))
- Expressions are well-formed (cannot change value because of more info)
- Expressions and variables for assignment are well-typed
- Havoced variables are defined
: (TODO: first assumption \<^prop>\<open>wf_abs_stmt \<Delta> C\<close> not mentioned in paper)\<close>

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

text \<open>The four components that we need for our ViperCore instantiation are given by:

\<^item> (1) IDF algebra instance:
    Our ViperCore IDF algebra instance is given by \<^typ>\<open>'a virtual_state\<close> (\<Sigma>_IDF in the paper),
    which we discuss above as part of Section 3.1.
    TODO where do we mention \<^typ>\<open>'a equi_state\<close>?
\<^item> (2) Custom statements:
  We define our custom statements in \<^typ>\<open>'a custom\<close>, which just includes field assignments
  \<^term>\<open>FieldAssign e1 f e2\<close>.
\<^item> (3) Semantics of custom statements:
  \<^item> Operational semantics: \<^term>\<open>red_custom_stmt \<Delta> (FieldAssign e1 f e2) \<omega> S\<close>
  \<^item> Axiomatic semantics: \<^term>\<open>SL_Custom \<Delta> P (FieldAssign e1 f e2) Q\<close>
\<^item> (4) Proofs that the semantics in (3) are compatible with our framework
  TODO: where is this located?
\<close>


section \<open>4: Back-End Soundness\<close>



subsection \<open>4.1: Symbolic Execution\<close>

\<comment>\<open>TODO: Michael\<close>

theorem sinit_sexec_verifies_set :
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  assumes "sinit tys F (\<lambda> \<sigma> :: 'a sym_state. sexec \<sigma> C Q)"
  assumes "\<Lambda> = nth_option tys"
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

paragraph \<open>Formalization of Viper's VCG (VCGSem)\<close>
text \<open>The formalization of Viper's VCG (which is not a contribution of this paper, but is part of 
reference 43 in our paper submission) in the paper is presented via the judgement \<open>\<langle>C, \<sigma>\<^sub>t\<rangle> \<rightarrow>_VCG r\<close>.
In Isabelle,  \<open>\<langle>C, \<sigma>\<^sub>t\<rangle> \<rightarrow>_VCG r\<close> is given by \<^prop>\<open>red_stmt_total ctxt (\<lambda>_.True) \<Lambda> C \<sigma>\<^sub>t r\<close> 
(\<^term>\<open>ctxt\<close> and \<^term>\<open>\<Lambda>\<close> provide context information that we ignored for the sake of presentation in
the paper.
\<close>

paragraph \<open>Theorem 7 (VCGSem)\<close>
text \<open>Theorem 7 is given by:\<close>
theorem abstract_refines_total_verifies_set :
  assumes A1: "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> (\<forall> \<sigma>\<^sub>t. \<sigma>\<^sub>t \<in> (a2t_states ctxt \<omega>)  \<longrightarrow> \<not> red_stmt_total ctxt (\<lambda>_. True) \<Lambda> C \<sigma>\<^sub>t RFailure)"
  assumes A2: "stmt_typing (program_total ctxt) \<Lambda> C"
  assumes A3: "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> typed (t2a_ctxt ctxt \<Lambda>) \<omega> \<Longrightarrow> abs_state_typing ctxt \<Lambda> \<omega>"
  assumes A4: "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> a2t_state_wf ctxt (get_trace \<omega>)"
  assumes A5: "valid_a2t_stmt C"
  shows "ConcreteSemantics.verifies_set (t2a_ctxt ctxt \<Lambda>) A
     (compile False (ctxt_to_interp ctxt) (\<Lambda>, declared_fields (program_total ctxt)) C)"
  using assms  
  apply (simp add:ConcreteSemantics.verifies_set_def)
  using abstract_refines_total_verifies[simplified red_stmt_total_set_ok_def]
  by blast

text \<open>One difference to the paper is that here we consider a more general version of Theorem 7 that 
is parametric in an initial set of states \<^term>\<open>A\<close>. 
Assumption A1 corresponds to \<open>\<not>(\<langle>C, \<sigma>\<^sub>t\<rangle> \<rightarrow>_VCG F)\<close> for all states \<open>\<sigma>\<^sub>t\<close> related to \<^term>\<open>\<omega>\<close> in the paper
(\<^term>\<open>a2t_states ctxt \<omega>\<close> provides the set of VCGSem states related to \<^term>\<open>\<omega>\<close>).
Assumptions A2 and A3 make sure that the Viper statement \<^term>\<open>C\<close> and the Viper state \<^term>\<open>\<omega>\<close> are 
well-typed; we omitted these in the paper for the sake of presentation.
Assumption A5 restricts the Viper statement \<^term>\<open>C\<close> to be in the Viper subset that we consider in the paper
(our formalization provides syntax for the entire Viper subset, so we need such an additional assumption
that restricts the syntax).
\<close>

paragraph \<open>Using Theorem 7 to connect to a Viper method\<close>
text \<open>The VCG back-end operates on Viper methods that contain Viper statements and not on Viper statements.
It is straightforward to use Theorem 7 in order to obtain a lemma that instead assumes the correctness of 
a Viper method w.r.t. VCGSem.
Such a lemma could then be used to directly connect to the formal results that have been shown
for Viper's VCG back-end (which shows the correctness of all Viper methods in a Viper program. w.r.t. VCGSem).

We did not show such a lemma in the paper, but we have proved such a lemma.
If you are interested, such a lemma can be inspected here @{thm [source] VCG_to_verifies_set} 
(you can ctrl-click on \<open>VCG_to_verifies_set\<close>, the target has some explanations). 
In particular, this lemma instantiates the initial set of states \<^term>\<open>A\<close> in the above formalization 
of Theorem 7 and proves assumptions A3 and A4 above for that instantiation.
\<close>



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
For historical reasons, we first do a "semantic" translation (into CoreIVL), in simple-frontend/FrontEndTranslation.thy,
and then show that verification of the syntactic translation into ViperCore implies verification of the semantic translation.

\<^term>\<open>translate_syn C\<close>
\<close>


text \<open>Theorem 9: Soundness of the front-end translation\<close>


theorem sound_front_end_translation:

  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"

      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"

      and "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys)
     (abs_stmt.Inhale P ;; compile False \<Delta> (tcfes tys) (fst (translate_syn C)) ;; abs_stmt.Exhale Q)"
      and "\<And>Cv. Cv \<in> compile False \<Delta> (tcfes tys) ` snd (translate_syn C) \<Longrightarrow> ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"

shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  by (rule sound_syntactic_translation) (simp_all add: assms)




text \<open>Lemma 3: What we call "convertible" is the following:
TODO:
- Explain "\<otimes> atrue \<Delta> tys"
- Explain "inhalify \<Delta> tys A" instead of A
\<close>

definition convertible where
  "convertible \<Delta> tys C \<longleftrightarrow> (\<forall>P Q.
  (proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))
  \<and> ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q)
  \<longrightarrow> tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys])"

lemma lemma_3_inhale_translation_exhale:
  assumes "convertible \<Delta> tys C"
      and "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Inhale A;; fst (translate \<Delta> tys C);; Exhale B) Q"
      and "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
    shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [Q \<otimes> B \<otimes> atrue \<Delta> tys]"
  using invariant_translate_inhale_exhale_get_proof assms unfolding convertible_def invariant_translate_def
  by meson

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



section \<open>End-to-end Theorems\<close>

(*
TODO:
- Combine e2e Carbon with adequacy?
- e2e theorem for symbolic execution?
*)


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




end