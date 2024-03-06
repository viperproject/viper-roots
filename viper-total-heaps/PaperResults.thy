theory PaperResults
imports ViperBoogieEndToEnd StmtRelML PaperResultsSupport
begin

section \<open>Getting Started Guide for Exploration of the Isabelle Formalisation\<close>

text \<open>
The following Isabelle theory file contains references to all the formalised results explicitly mentioned in
the paper. The theory file is structured using Isabelle sections and subsections, which match those from 
the paper. You can use the "Sidekick" view on the right side of the Isabelle IDE to quickly jump to a 
section or subsection. 

When you first load this file, Isabelle will load and check all Isabelle files in the formalisation for the paper.
This takes several minutes to finish. You can see the progress by clicking on the \<open>Theories\<close> panel on 
the right. Make sure that the checkbox \<open>Continuous checking\<close> at the top of the \<open>Theories\<close> panel is selected,
which should already be the case by default (otherwise Isabelle won't check the files).
Wait until Isabelle finished checking all files (keep the current file open, otherwise Isabelle won't 
continue with certain files). If the bars for all files on the right are fully white except the current
 \<open>PaperResult\<close> one, then it is finished. There should be no red bars in the files of the theory panel (this would 
indicate that Isabelle was not able to check a file).

In the Isabelle IDE, you can ctrl-and-click on defined names, which takes you to the Isabelle source 
where the constant is defined (for example, a standard definition or an Isabelle function). 
Whenever you jump somewhere via ctrl-and-clicking (for example, by jumping to a section or a definition),
you can use the two green arrow buttons at the top of the Isabelle IDE to jump back (or forward) to the 
previous position.

In this document, we make use of Isabelle's documentation features, which itself can contain Isabelle
elements (and are checked via Isabelle), to walk you through the formalisation of the definitions and 
rules in the paper. In particular, we use the following Isabelle document elements:

  \<^item> types (for example, \<^typ>\<open>ViperLang.stmt\<close>)
     --> you can click on defined names in types (i.e. \<open>ViperLang.stmt\<close> in the example)
  \<^item> defined names (for example, \<^const>\<open>red_stmt_total\<close> --> you can click on defined names)
  \<^item> terms (for example, \<^term>\<open>red_stmt_total ctxt\<close>)
    --> you can click on defined names in terms (i.e. \<open>red_stmt_total\<close> in the example)
  \<^item> propositions (for example, \<^prop>\<open>red_stmt_total ctxt R \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>); these are just boolean terms
    --> you can click on defined names in proposition (i.e. \<open>red_stmt_total\<close> in the example)
  \<^item> Standard ML terms (for example, \<^ML>\<open>stmt_rel_tac\<close>) and types (for example, \<^ML_type>\<open>'a stmt_rel_hint\<close>);
      we use Standard ML to define custom Isabelle tactics.
    --> you can click on the ML definitions in ML terms and types 
        (i.e., \<open>stmt_rel_tac\<close> and \<open>stmt_rel_hint\<close> in the examples)

Make sure that you can click on the sections and subsections in this file (via Isabelle's sidekick on the
right) and the document elements shown above in the bullet list.
Make sure that doing so brings you to the source of the clicked element.

Make sure that you can use the green back arrow to jump back to this point in the document after clicking
on an element.

Note that you can also double-click on specific files via the \<open>Theories\<close> panel on the right to open them
or open a specific active file by clicking on the bar with the current file name and downwards arrow at the top 
of the Isabelle GUI (below the green arrows).

To refer to specific lemmas proved in our Isabelle formalisation, we use Isabelle's \<open>lemmas\<close> keyword. 

For example:
\<close>

lemmas example_for_rule = RedExhale RedExhaleFailure

lemmas example_for_a_proved_theorem = exhale_inhale_normal

\<comment>\<open>You can ctrl-click on the lemmas \<open>RedExhale\<close>, \<open>RedExhaleFailure\<close> and \<open>exhale_inhale_normal\<close>.
  You can also inspect the lemmas by clicking anywhere right after the \<open>lemmas\<close> keyword
  and then looking at the resulting Isabelle statement in the \<open>Output\<close> panel at the bottom of the Isabelle GUI.
  Note that if multiple lemmas are listed (such as for \<open>example_for_rule\<close>), then the \<open>Output\<close> panel
  shows both lemmas.
  Make sure that you can do both of these things (ctrl-clicking and inspecting lemma in \<open>Output\<close> panel) 
  for these three lemmas.

  In general, we recommend ctrl-clicking to get to the source, where we have often provided names 
  for the premises (sometimes we refer to these names explicitly) and is easier to read.

  This marks the end of the Getting Started Guide for the Isabelle formalisation. The next section
  starts with the Step-By-Step Instructions (ordered via Isabelle sections and subsections that match 
  those in the paper as mentioned above).
\<close>

section \<open>2 Viper and Boogie: Background and Semantics (Start of Step-by-Step Instructions)\<close>

subsection \<open>2.1 The Viper and Boogie languages\<close>

text \<open>The Viper AST for statements is defined in \<^typ>\<open>ViperLang.stmt\<close>.
      The Boogie AST for statements is defined in \<^typ>\<open>Ast.bigblock\<close>\<close>

text \<open>Both formalised ASTs includes a larger subset than presented in the paper (for example,
      loops for Viper and Boogie). For the artifact, only the subset mentioned in the paper is relevant. 
      Some of our definitions in the formalisations are generalised to also work for features outside
      the subset. These generalisations are not relevant here and throughout this file, we will make clear 
      which parts are relevant.\<close>

subsection \<open>2.2: Boogie Semantics\<close>

paragraph \<open>Outcomes\<close>
text \<open>Boogie outcomes are defined in \<^typ>\<open>'a state\<close> and Boogie states are defined in \<^typ>\<open>'a nstate\<close>.
      \<^typ>\<open>'a nstate\<close> defines the mapping of variables to values via different mappings (local variable mapping,
      global variable mapping etc.); the details are not essential here.\<close>

paragraph \<open>Semantics for Boogie statements\<close>
text \<open>The single step execution of a Boogie statement is expressed via \<^const>\<open>red_bigblock_small\<close>, which 
      makes sure that at most one simple command is executed in each step.
      A lot of the semantics was taken directly \<comment>\<open>TODO\<close>.
      
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> (\<gamma>, N(\<sigma>\<^sub>b)) \<rightarrow>\<^sub>b\<^sup>* (\<gamma>', r\<^sub>b)\<close> in the paper (expressing a finite Boogie execution taking
      0 or more steps) corresponds to \<^prop>\<open>red_ast_bpl P ctxt (\<gamma>, Normal \<sigma>\<^sub>b) (\<gamma>',r\<^sub>b)\<close> in the formalisation,
      where \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>.
\<close>

subsection \<open>2.3 Viper Semantics\<close>

paragraph \<open>Outcomes\<close>
text \<open>Viper outcomes are defined in \<^typ>\<open>'a stmt_result_total\<close>.
      Viper states are defined via the record type \<^typ>\<open>'a full_total_state\<close>. The type parameter
      \<^typ>\<open>'a\<close> is not relevant for the Viper subset in the paper.

      Given a Viper state \<^term>\<open>\<sigma>\<^sub>v :: 'a full_total_state\<close>, its components are:
        \<^item> the store: \<^term>\<open>get_store_total \<sigma>\<^sub>v\<close>
        \<^item> the heap: \<^term>\<open>get_hh_total_full \<sigma>\<^sub>v\<close> 
        \<^item> the permission mask: \<^term>\<open>get_mh_total_full \<sigma>\<^sub>v\<close>

      The state has more components, which are not relevant for features outside of the Viper subset 
      presented in the paper.
\<close>

paragraph \<open>Semantics for Viper statements\<close> 
text \<open>The big-step judgement for Viper statements is defined via \<^const>\<open>red_stmt_total\<close>.     
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> \<langle>s, \<sigma>\<^sub>v\<rangle> \<rightarrow> r\<^sub>v\<close> in the paper (the execution of statement \<open>s\<close>
      in state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>red_stmt_total ctxt R \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close> in the formalisation,
      where the Viper context \<^term>\<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>ctxt\<close> and \<^term>\<open>\<Lambda>\<close>

      The parameter \<^term>\<open>R\<close> is not required for the Viper subset in the paper. In our generated proofs, 
      it is always instantiated as \<^term>\<open>\<lambda>_. True\<close>.
\<close>

paragraph \<open>Viper expression evaluation\<close>
text \<open>The expression evaluation is defined via \<^const>\<open>red_pure_exp_total\<close>.
      The notation \<open>\<langle>e, \<sigma>\<^sub>v\<rangle> \<Down> V(v)\<close> in the paper (expression evaluation of expression \<open>e\<close> to value \<open>v\<close> 
      in state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>ctxt, R, Some(\<sigma>\<^sub>v) \<turnstile> \<langle>e; \<sigma>\<^sub>v\<rangle> [\<Down>]\<^sub>t Val v\<close> in the formalisation (here,
      we defined special notation in Isabelle for \<^const>\<open>red_pure_exp_total\<close>). 
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> \<langle>e, \<sigma>\<^sub>v\<rangle> \<Down> <lightning_symbol>\<close> in the paper(expression \<open>e\<close> is ill-defined in \<open>\<sigma>\<^sub>v\<close>) 
      corresponds to \<^prop>\<open>ctxt, R, Some(\<sigma>\<^sub>v) \<turnstile> \<langle>e; \<sigma>\<^sub>v\<rangle> [\<Down>]\<^sub>t VFailure\<close>.

      As for the statement reduction, \<^term>\<open>R\<close> is not required for the Viper subset in the paper and is always
      instantiated as \<^term>\<open>\<lambda>_. True\<close> in our generated proofs. \<^term>\<open>ctxt\<close> is the same as for the statement reduction
      but is redundant for the expression evaluation for the Viper subset in the paper and thus was 
      omitted in the presentation.      

      One difference to the paper, is that the expression evaluation in the formalisation takes two 
      Viper states as input instead of just one. Having two states is only required for Viper features
      outside of the subset of the paper and that's why in the paper we present the evaluation just with one 
      state to ease the presentation.
       
      In almost all cases of the semantics formalisation, these two states are chosen to be the same one and thus 
      directly correspond to the paper. The only case where the two states differ is during \<open>remcheck\<close> operations, 
      where one state is instantiated to be the \<^emph>\<open>reduction state\<close> and the other the \<^emph>\<open>expression evaluation state\<close>
      (introduced on lines 312-317 in the paper). The expression evaluation checks whether there
      is nonzero permission to fields in the expression evaluation state (as in the paper), but 
      the other lookups (e.g. heap, store) are performed in the reduction state. This is done, because 
      there is a Viper feature outside of the subset in the paper that allows looking up the current 
      permission in the \<^emph>\<open>reduction state\<close> during a \<open>remcheck\<close> operation. Since in the subset of the paper,
      the expressions allow only looking up heap values and store values, instantiating both states to be the
      expression evaluation state leads to the same result and thus directly corresponds to the paper
      (because the reduction and expression evaluate state differ only on the permission mask).
\<close>

paragraph \<open>Exhale semantics\<close>

text \<open>The rule (EXH-SUCC) is given by:\<close>

lemmas EXH_SUCC = RedExhale \<comment>\<open>Note: you can ctrl-click on \<open>RedExhale\<close> to jump to the rule\<close>

text \<open>TODO: discuss why nonDetSelect is the same as \<^const>\<open>havoc_locs_state\<close>\<close>

text \<open>The rule (EXH-FAIL) is given by:\<close>

lemmas EXH_FAIL = RedExhaleFailure

text \<open>The \<open>remcheck\<close> reduction is defined in \<^const>\<open>red_exhale\<close>.
      The notation \<open>\<sigma>0\<^sub>v \<turnstile> \<langle>A, \<sigma>\<^sub>v\<rangle> \<rightarrow>\<^sub>r\<^sub>c r\<^sub>v\<close> (remcheck reduction of assertion \<open>A\<close> in expression evaluation
      state \<open>\<sigma>0\<^sub>v\<close> and reduction state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>red_exhale ctxt R \<sigma>0\<^sub>v A \<sigma>\<^sub>v r\<^sub>v\<close> \<close>

text \<open>The rule (RC-SEP) is given by:\<close>

lemmas RC_SEP = ExhStarNormal

text \<open>The rule (RC-ACC) is given by:\<close>
                     
lemmas RC_ACC = ExhAcc

paragraph \<open>Inhale semantics\<close>

text \<open>The statement reduction rule for \<open>inhale\<close> is given by:\<close>

lemmas red_inhale = RedInhale

text \<open>This rule is defined via a helper definition \<^const>\<open>red_inhale\<close>.\<close>


section \<open>3 A Forward Simulation Methodology For Front-End Translations\<close>

subsection \<open>3.2 One Simulation Judgement to Rule Them All\<close>

text \<open>The generic forward simulation judgement \<open>sim\<close> in the paper is defined in \<^const>\<open>rel_general\<close>.
      The notation \<open>sim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, Succ, Fail, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> corresponds to
      \<^prop>\<open>rel_general R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Succ Fail P ctxt \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>, where the Boogie context \<open>\<Gamma>\<^sub>b\<close> captures both
      \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>.\<close>

paragraph \<open>Three common instantiations of \<open>sim\<close>\<close>
text \<open>For the three common instantiations shown at the bottom of figure 4, in the formalisation,
      the Boogie context \<open>\<Gamma>\<^sub>b\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>, and \<^term>\<open>StateCons\<close> corresponds 
      to parameter \<^term>\<open>R\<close> discussed above for the statement and expression reduction and is always
      instantiated to be \<^term>\<open>\<lambda>_.True\<close> in our generated proofs.

      The \<^emph>\<open>statement simulation\<close> is defined in \<^const>\<open>stmt_rel\<close>. 
      The notation \<open>stmSim\<^sub>\<Gamma>\<^sub>v,\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, s, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
      \<^prop>\<open>stmt_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons \<Lambda> P ctxt s \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.
      The Viper context \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>ctxt_vpr\<close> and \<^term>\<open>\<Lambda>\<close>.

      The \<^emph>\<open>expression well-definedness simulation\<close> is defined in \<^const>\<open>exprs_wf_rel_2\<close>.
      The notation \<open>wfSim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, es, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to
      \<^prop>\<open>exprs_wf_rel_2 R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.
      \<^term>\<open>ctxt_vpr\<close> is not relevant here for subset presented in the paper.
     
      Since the expression evaluation takes two states as input in the formalisation (see above),
      \<^term>\<open>R\<^sub>i\<^sub>n\<close> and \<^term>\<open>R\<^sub>o\<^sub>u\<^sub>t\<close> also are defined in terms of both states. For convenience, they are both 
      in curried form and thus the instantiation via \<^const>\<open>rel_general\<close> uncurries them.
     
      For convenience, we usually work with \<^const>\<open>exprs_wf_rel\<close>, where the input and output
      state relation are the same, which is sufficient for our use case. That is, we have:
\<close>

lemma exprs_wf_rel_with_2_equiv: 
  "exprs_wf_rel_2 R R ctxt_vpr StateCons P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t \<longleftrightarrow>
   exprs_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t"
  by (simp add: exprs_wf_rel_2_def exprs_wf_rel_def)    

text \<open>The \<^emph>\<open>remcheck simulation\<close> is defined in \<^const>\<open>exhale_rel0\<close>. The notation
      \<open>rcSim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
      \<^prop>\<open>exhale_rel0 R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.
      \<^term>\<open>ctxt_vpr\<close> is not relevant here for subset presented in the paper.
      For convenience, \<^term>\<open>R\<^sub>i\<^sub>n\<close> and \<^term>\<open>R\<^sub>o\<^sub>u\<^sub>t\<close> are curried, and thus the instantiation via
      \<^const>\<open>rel_general\<close> uncurries them.

     In our formalisation, we always directly work with a remcheck simulation that additionally takes
     a predicate \<open>Q\<close> on assertions as a parameter as described in Section 3.5 of the paper.
     The notation \<open>rcSim\<^sub>\<Gamma>\<^sub>b\<^sup>Q(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper (Figure 7) corresponds to 
     \<^prop>\<open>exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.
    
     \<^const>\<open>exhale_rel\<close> is directly defined in terms of the generic simulation judgement, but the following
     lemma shows that this is equivalent to defining \<^const>\<open>exhale_rel\<close> in terms \<^const>\<open>exhale_rel0\<close>
     as we do in the paper for the sake of presentation:
\<close>

lemma exhale_rel_exhale_rel0_inst_equiv: 
  "exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>' \<longleftrightarrow>
   exhale_rel0 (\<lambda>\<omega>def \<omega> ns. R\<^sub>i\<^sub>n \<omega>def \<omega> ns \<and> Q A \<omega>def \<omega>) R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  unfolding exhale_rel_def exhale_rel0_def
  by simp

subsection \<open>3.3 Instantiation-Independent Rules\<close>

text \<open>The generic composition rule COMP (Figure 5) is given by:\<close>

lemmas COMP_paper = rel_general_comp

text \<open>The sequential composition rule SEQ-SIM (Figure 5) is given by:\<close>

lemmas SEQ_SIM = stmt_rel_seq \<comment>\<open>Note that the proof uses the generic composition rule\<close>

text \<open>Additional rules derived from the generic composition rule are:\<close>

lemmas COMP_derived = 
  exhale_rel_star \<comment>\<open>remcheck A1*A2\<close>
  inhale_rel_star \<comment>\<open>inhale A1*A2\<close>

text \<open>The propagation rule BPROP (Figure 5) is given by:\<close>

\<comment>\<open>TODO: prove bSim in terms of rel_general\<close>

subsection \<open>3.4 Examples: Generic Decomposition in Action\<close>

text \<open>The rule EXH-SIM (Figure 6) is given by:\<close>

lemmas EXH_SIM = exhale0_stmt_rel

\<comment>\<open>TODO: maybe show havocLocs corresponds to nonDet definition\<close>

text \<open>As discussed above in section 3.3, instead of working with \<open>rcInv\<close> we always work with 
     \<open>rcInvSim\<close> (see Figure 7), which takes an additional predicate \<open>Q\<close> on assertions.
     The EXH-SIM rule generalised to \<open>rcInvSim\<close> is given by:\<close>

lemmas EXH_SIM_rcInvSim = exhale_stmt_rel \<comment>\<open>the rule for EXH-SIM is proved via this rule\<close>

\<comment>\<open>TODO: second example appendix B --> put it here or later?\<close>
 
subsection \<open>3.5 Injecting Non-Local Hypotheses into Simulation Proofs\<close>

text \<open>As also mentioned above in section 3.3., the notation \<open>rcSimInv\<^sub>\<Gamma>\<^sub>b\<^sup>Q(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> 
      in the paper (Figure 7) corresponds to \<^prop>\<open>exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.

      The rule RSEP-SIM is given by: \<^theory>\<open>TotalViper.ViperBoogieEndToEnd\<close> 
      @{thm exhale_rel0_def}

      Test: @{thm [source] exhale_rel0_def}
      Test2: @{thm [source] exhale_rel0_def exhale_rel_star stmt_rel_seq}
      Test3: @{thm exhale_rel0_def exhale_rel_star stmt_rel_seq}    
\<close>

lemmas RSEP_SIM = exhale_rel_star


section \<open>4 Putting the Methodology to Work\<close>

subsection \<open>4.1 State Relation\<close>

text \<open>The state relation is defined in \<^const>\<open>state_rel0\<close>.
      The notation \<open>R\<^sub>\<Gamma>\<^sub>b\<^sup>T\<^sup>r\<^sup>,\<^sup>A\<^sup>v((\<sigma>0\<^sub>v,\<sigma>\<^sub>v), \<sigma>\<^sub>b)\<close> in the paper corresponds to
      \<^prop>\<open>state_rel0 Pr (\<lambda>_.True) A \<Lambda> TyRep Tr Av \<sigma>0\<^sub>v \<sigma>\<^sub>v ns\<close>
      where \<open>\<Gamma>\<^sub>b\<close> captures both \<^term>\<open>A\<close> and \<^term>\<open>\<Lambda>\<close>, \<open>Pr\<close> is the Viper program representation and is left
      implicit in the paper.

      The presented conjuncts in the paper are represented as follows in the definition of \<^const>\<open>state_rel0\<close>:
      
      \<^item> State consistency: The conjunct \<open>consistent(\<sigma>\<^sub>v)\<close> corresponds to \<^term>\<open>wf_mask_simple (get_mh_total_full \<sigma>\<^sub>v)\<close>.
      \<^item> Field relation: The conjunct \<open>fieldRel\<^sub>\<Gamma>\<^sub>b(field(Tr), \<sigma>\<^sub>b)\<close> corresponds to
                        \<^term>\<open>field_rel Pr \<Lambda> (field_translation Tr) \<sigma>\<^sub>b\<close>.
      \<^item> Auxiliary variable constraints: The conjunct \<open>\<forall>x,P. AV(x) = P \<longrightarrow> P(\<sigma>\<^sub>b(x))\<close> corresponds to
                        \<^term>\<open>aux_vars_pred_sat \<Lambda> AuxPred \<sigma>\<^sub>b\<close>
      \<^item> Store relation: The conjunct \<open>stRel\<^sub>\<Gamma>\<^sub>b(var(Tr), \<sigma>\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to 
                        \<^term>\<open>store_rel A \<Lambda> (var_translation Tr) \<sigma>\<^sub>v \<sigma>\<^sub>b\<close>
      \<^item> Heap and permission mask relation: The conjunct \<open>hmRel\<^sub>\<Gamma>\<^sub>b(HM(Tr), \<sigma>\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to
          \<^term>\<open>heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) \<sigma>\<^sub>v \<sigma>\<^sub>b \<and>
               mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) \<sigma>\<^sub>v \<sigma>\<^sub>b\<close>
          The conjunct \<open>hmRel\<^sub>\<Gamma>\<^sub>b(HM\<^sup>0(Tr), \<sigma>0\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to
          \<^term>\<open>heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) \<sigma>0\<^sub>v \<sigma>\<^sub>b \<and>
               mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) \<sigma>0\<^sub>v \<sigma>\<^sub>b\<close>
\<close>

subsection \<open>4.2 Non-Locality\<close>

text \<open>The predicate \<open>Q\<^sub>p\<^sub>r\<^sub>e\<close> is defined in \<^const>\<open>framing_exh\<close>. 
      The notation \<open>Q\<^sub>p\<^sub>r\<^sub>e(A, \<sigma>0\<^sub>v, \<sigma>\<^sub>v)\<close> corresponds to \<^prop>\<open>framing_exh ctxt_vpr (\<lambda>_.True) A \<sigma>0\<^sub>v \<sigma>\<^sub>v\<close>.
      The extra parameter \<^term>\<open>ctxt_vpr\<close> (the Viper context) is not relevant for the subset presented 
      in the paper in this case.

      Lemma 4.1 is shown by:
\<close>

lemmas lemma_4_1 = exhale_inhale_normal

text \<open>The parameter \<^term>\<open>StateCons\<close> is redundant for the subset presented in the paper and is always
      instantiated to be \<^term>\<open>\<lambda>_.True\<close> in our proofs.
      The premise \<^term>\<open>no_perm_assertion A \<and> no_unfolding_assertion A\<close> restricts the assertion \<^term>\<open>A\<close>
      to be within the subset presented in the paper.

      The premise \<open>\<not> \<langle>A, \<sigma>i\<^sub>v\<rangle> \<rightarrow>\<^sub>i\<^sub>n\<^sub>h F\<close> in the paper corresponds to
      \<^prop>\<open>assertion_framing_state ctxt StateCons A \<omega>_inh\<close>.                 
\<close>

subsection \<open>4.3 Proof Automation\<close>

text \<open>Our custom tactic to prove the forward simulation of Viper statements is defined in \<^ML>\<open>stmt_rel_tac\<close>
      directly in Standard ML programming language, which is Isabelle's implementation language.
     \<^ML>\<open>stmt_rel_tac\<close> invokes other tactics such as, for example, the simulation of 
     \<open>remcheck\<close> operations defined in \<^ML>\<open>exhale_rel_aux_tac\<close>.

     \<^ML>\<open>stmt_rel_tac\<close> is parametric in the hints and tactic for the primitive statements. The type 
     signature makes this explicit via the argument types \<^ML_type>\<open>('a, 'i, 'e) stmt_rel_info\<close> (a record
     that includes the primitive statement tactic) and \<^ML_type>\<open>'a stmt_rel_hint\<close> (for the hints).
     In our proofs, we instantiate 'a to be \<^ML_type>\<open>atomic_rel_hint\<close> and define the tactic for the 
     primitive statements to be \<^ML>\<open>atomic_rel_inst_tac\<close>.

     Our tactics apply the rules proved for the different constructs. In some cases, we derive instantiated
     versions of these rules upfront, which makes the tactics easier to write. For example, \<^ML>\<open>stmt_rel_tac\<close>
     applies the lemma @{thm stmt_rel_seq_same_rel} for the sequential composition, which is the same as
     the sequential composition rule SEQ-SIM shown in Figure 5, except that the input and output relation
     are fixed to be the same.
     \<comment>\<open>TODO: which parts of 4.3 should be reflected here?\<close>
\<close>

subsection \<open>4.4 Background Theory and Polymorphic Maps\<close>

paragraph \<open>Boogie procedure correctness (top of Figure 8)\<close>
text\<open>The correctness of a Boogie procedure is defined in \<^const>\<open>proc_is_correct\<close>. The final parameter of 
the definition abstracts over the type of a procedure body and its associated operational semantics,
which allows reusing the same definition for Boogie abstract syntax trees and control-flow graphs.

The notation \<open>Correct\<^sub>b\<^sup>G(p)\<close> in the paper corresponds to 

\<^prop>\<open>\<forall>T. proc_is_correct T fun_decls constants unique_consts global_vars axioms p Ast.proc_body_satisfies_spec\<close>

where the universally quantified \<^term>\<open>T\<close> corresponds to the type interpretation. The global declarations \<^term>\<open>G\<close> 
captures \<^term>\<open>fun_decls\<close> (function declarations), \<^term>\<open>constants\<close> (constant declarations),
\<^term>\<open>unique_consts\<close> (subset of constant declarations that are marked as unique),
\<^term>\<open>global_vars\<close> (global variable declarations) and \<^term>\<open>axioms\<close> (axioms).
The final argument \<^const>\<open>Ast.proc_body_satisfies_spec\<close> concretely specifies when a body represented by a 
Boogie AST has no failing executions. \<^const>\<open>Ast.proc_body_satisfies_spec\<close> also takes the procedure pre- 
and postcondition into account, which are not relevant for the paper, since the Viper-to-Boogie 
translation does not emit any pre- and postconditions in the Boogie program.
\<close>

paragraph \<open>Polymorphic maps\<close>
text \<open>The type \<^typ>\<open>'a vbpl_absval\<close> defines our instantiation of the uninterpreted Boogie types
generated by the Viper-to-Boogie translation. In this type definition, \<open>HType\<close> is instantiated via
\<^term>\<open>AHeap h\<close>, where \<^term>\<open>h\<close> is a partial mapping (represented by a function that maps to the option type;
note that \<^typ>\<open>'a \<rightharpoonup> 'b\<close> is syntactic sugar for \<^typ>\<open>'a \<Rightarrow> 'b option\<close>) as presented in the paper. 
The function \<^const>\<open>vbpl_absval_ty_opt\<close> is the main building block for constructing the corresponding
type interpretation for the Viper-to-Boogie translation (i.e. mapping values of type
\<^typ>\<open>'a vbpl_absval\<close> to Boogie types).

The instantiations for the \<open>upd\<close> and \<open>read\<close> functions of \<open>HType\<close> are provided by \<^const>\<open>store_heap\<close>
and \<^const>\<open>select_heap\<close>, respectively.
\<close>

subsection \<open>4.5 Generating A Proof of the Final Theorem\<close>

paragraph \<open>Correctness of a Viper method (Figure 8 at the bottom)\<close>
text \<open>The correctness of a Viper method is defined in \<^const>\<open>vpr_method_correct_paper\<close>.
The notation \<open>Correct\<^sub>v\<^sup>F\<^sup>,\<^sup>M(m)\<close> corresponds to \<^prop>\<open>vpr_method_correct_paper ctxt_vpr m\<close>
where F,M capture \<^term>\<open>ctxt_vpr\<close>. 

In our generated proofs, we use a more general version of the correctness of a Viper method
(defined in \<^const>\<open>vpr_method_correct_total\<close>) that is applicable to a larger subset of Viper than
supported by the paper, where correctness of a method is expressed via 
\<^prop>\<open>vpr_method_correct_total ctxt_vpr (\<lambda>_.True) m\<close>. 

The following lemma shows that the more general version implies the version of the paper for Viper 
methods that lie withing the Viper subset presented in the paper:
\<close>

lemmas general_method_correctness_stronger = method_correctness_stronger_than_paper

text \<open>Thus, our generated proofs prove the method correctness for each method as presented
      in the paper.\<close>

paragraph \<open>Main helper lemma to prove final theorem\<close>

text \<open>To generate proofs for \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> (Figure 9, bottom), we use a generic helper lemma 
      that we prove once and for all and that reflects the strategy for \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> as
      described in Section 4.5 of  of the paper (starting at line 809 of the paper).
      This generic helper lemmas is given by:\<close> 

lemmas generic_helper_lemma_final_theorem = end_to_end_vpr_method_correct_partial

text \<open>The lemma has lots of assumptions that are not relevant here (we prove the assumptions when we generate
the proofs). There are three relevant assumptions directly mentioned in the paper:
  \<^item> Assumption with name \<open>Boogie_correct\<close>: 
    This expresses correctness of the Boogie procedures (corresponds to the left-hand side \<open>Correct\<^sub>b\<^sup>G(p)\<close>
    of \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close>)
  \<^item> Assumption with name \<open>VprMethodRel\<close> (defined via \<^const>\<open>method_rel\<close>): 
    This assumption corresponds to the forward simulation statement on lines 818-820 in the paper. 
    Note that the definition of \<^const>\<open>method_rel\<close> is more general than forward simulation shown in the paper. 
    In particular, the conjunct \<^const>\<open>post_framing_rel\<close> is used to show the well-formedness of the method postcondition
    (which we explicitly ignore in the paper as mentioned in line 810 of the paper).
    Moreover, note that \<^const>\<open>method_rel\<close> includes a left-hand side \<^const>\<open>vpr_all_method_spec_correct_total\<close>,
    which states each method specification in the program is well-formed (this directly corresponds
    to \<open>\<forall>m' \<in> M. SpecWf(m')\<close> in the definition \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> in the paper (Figure 9 bottom).
  \<^item> Assumption with name \<open>InitialStateRel\<close>:
    This assumption requires one to choose an initial Boogie state that is related to the initial
    Viper state as mentioned on lines 826-827 in the paper.
\<close>

section \<open>Appendix\<close>

subsection \<open>A Inhale Semantics\<close>

text \<open>TODO\<close>

subsection \<open>B Another Simulation Rule Example\<close>

text \<open>TODO\<close>

end

