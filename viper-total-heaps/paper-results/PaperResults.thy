theory PaperResults
imports TotalViper.ViperBoogieEndToEnd TotalViper.StmtRelML PaperResultsSupport
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

In the Isabelle IDE, you can ctrl-and-click on defined names, which takes you to the Isabelle source 
where the name is defined (for example, a standard definition or an Isabelle function). 
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
  \<^item> propositions (for example, \<^prop>\<open>red_stmt_total ctxt (\<lambda>_. True) \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>); these are just 
    boolean terms
    --> you can click on defined names in proposition (i.e. \<open>red_stmt_total\<close> and \<open>True\<close> in the example)
  \<^item> Standard ML terms (for example, \<^ML>\<open>stmt_rel_tac\<close>) and types (for example, \<^ML_type>\<open>'a stmt_rel_hint\<close>);
      we use Standard ML to define custom Isabelle tactics.
    --> you can click on the ML definitions in ML terms and types 
        (i.e., \<open>stmt_rel_tac\<close> and \<open>stmt_rel_hint\<close> in the examples)

Make sure that you can click on the sections and subsections in this file (via Isabelle's sidekick on the
right) and the document elements shown above in the bullet list.
Make sure that doing so brings you to the source of the clicked element.

Make sure that you can use the green back arrow to jump back to this point in the document after 
clicking on an element.

Note that you can also double-click on specific files via the \<open>Theories\<close> panel on the right to 
open them or open a specific active file by clicking on the bar with the current file name and 
downwards arrow at the top of the Isabelle GUI (below the green arrows).

To refer to specific rules and lemmas in our Isabelle formalisation, we use Isabelle's \<open>lemmas\<close> keyword. 

For example:
\<close>

lemmas example_for_rule = RedExhale RedExhaleFailure

lemmas example_for_a_proved_theorem = exhale_inhale_normal

text \<open>
  You can ctrl-click on the lemmas \<open>RedExhale\<close>, \<open>RedExhaleFailure\<close> and \<open>exhale_inhale_normal\<close>.
  You can also inspect the lemmas by clicking anywhere right after the \<open>lemmas\<close> keyword
  and then looking at the resulting Isabelle statement in the \<open>Output\<close> panel at the bottom of the 
  Isabelle GUI (make sure that \<open>Proof state\<close> is selected in the \<open>Output panel\<close>, which should be the
  case by default). 
  Note that if multiple lemmas are listed (such as for \<open>example_for_rule\<close>), then 
  the \<open>Output\<close> panel shows both lemmas.
  Make sure that you can do both of these things (ctrl-clicking and inspecting lemma in the \<open>Output\<close> panel) 
  for these three lemmas.

  In general, we recommend ctrl-clicking to get to the source, where we have often provided names 
  for the premises (sometimes we refer to these names explicitly), and the source is easier to read.

  This marks the end of the Getting Started Guide for the Isabelle formalisation. The next section
  in this document starts with the Step-By-Step Instructions for the Isabelle formalisation
  (ordered via Isabelle sections and subsections that match those in the paper as mentioned above).
\<close>

section \<open>2 Viper and Boogie: Background and Semantics (Start of Step-by-Step Instructions)\<close>

subsection \<open>2.1 The Viper and Boogie languages\<close>

paragraph\<open>Figure 1\<close>
text \<open>The components in Figure 1 are defined in (note that the formalisation contains a larger subset 
      than in Figure 1 as we discuss right after the following list):

      Viper:
      \<^item> Viper expressions (\<open>VExpr\<close> in Figure 1) are defined in \<^typ>\<open>ViperLang.pure_exp\<close>
      \<^item> Viper assertions (\<open>VAssert\<close> in Figure 1) are defined in \<^typ>\<open>assertion\<close>. Note that 
       \<^typ>\<open>assertion\<close> is formalised via the composite assertions \<^typ>\<open>('p, 'a) assert\<close>,
        which is parametric in the expressions \<^typ>\<open>'p\<close> and primitive assertions \<^typ>\<open>'a\<close>. \<^typ>\<open>assertion\<close> 
        is a type synonym for \<^typ>\<open>(pure_exp, pure_exp atomic_assert) assert\<close>.
        Note that \<^term>\<open>Acc e f (PureExp ep)\<close> denotes the accessibilty predicate \<open>acc(e.f, ep)\<close> in 
        the paper and \<^term>\<open>A && B\<close> denotes the separating conjunction \<open>A * B\<close> in the paper.
      \<^item> Viper statements (\<open>VStmt\<close> in Figure 1) are defined in \<^typ>\<open>ViperLang.stmt\<close>.

      Boogie (note that when ctrl-clicking Boogie elements, the Isabelle source is red and you can't explore
      further; this is because we have preloaded the Boogie theories as we discuss in Section 2.2 below):
      \<^item> Boogie expressions (\<open>BExpr\<close> in Figure 1) are defined in \<^typ>\<open>Lang.expr\<close>
      \<^item> Boogie simple command (\<open>BSimpleCmd\<close> in Figure 1) are defined in \<^typ>\<open>Lang.cmd\<close>
      \<^item> Boogie if statements (\<open>BIfOpt\<close> in Figure 1) are defined in \<^term>\<open>ParsedIf\<close>.
        Note that \<^term>\<open>ParsedIf (Some(b)) s1 s2\<close> corresponds to \<open>if(b) { s1 } else { s1 }\<close> in
        the paper and \<^term>\<open>ParsedIf None s1 s2\<close> corresponds to \<open>if(*) { s1 } else { s2 }\<close> in the 
        paper (the latter is a nondeterministic if-statement). Note that the empty case \<open>\<epsilon>\<close> is handled 
        via statement blocks in the formalisation.
      \<^item> Boogie statement blocks (\<open>BStmtBlock\<close> in Figure 1) are defined in \<^typ>\<open>Ast.bigblock\<close>.
        \<open>BStmt\<close> is expressed as \<^typ>\<open>Ast.bigblock list\<close>. Note that, in the formalisation, statement 
        blocks also include gotos, which we do not consider in the paper.    

      Both formalised ASTs include a larger subset than presented in the paper (for example,
      loops for Viper and Boogie). For the artifact, only the subset mentioned in the paper is 
      relevant. For Viper, \<^prop>\<open>stmt_in_paper_subset s\<close> defines when a Viper statement is in the 
      paper subset. It is defined via the functions \<^const>\<open>stmt_in_paper_subset_no_rec\<close>,
      \<^const>\<open>assert_in_paper_subset_no_rec\<close>, \<^const>\<open>atomic_assert_in_paper_subset\<close>, and
      \<^const>\<open>exp_in_paper_subset_no_rec\<close>. These functions indicate which statement, assertion, primitive
      assertion (accessibility predicates or Boolean expression), and expression constructors are
      in the paper subset.
      
      Some of our definitions in the formalisations are generalised to also work for features outside
      the subset presented in the paper. These generalisations are not relevant here. Throughout this 
      file, we will make clear which parts are relevant.
\<close>

subsection \<open>2.2: Boogie Semantics\<close>

text \<open>The Boogie formalisation is taken from an extension of the CAV21 paper
 \<open>Formally Validating a Practical Verification Condition Generator\<close>, which is being developed 
in \<open>https://github.com/gauravpartha/foundational_boogie/\<close>.

We have preloaded the formalisation of the Boogie semantics in the GUI.
You can see this by clicking on \<open>Theories\<close> in Isabelle GUI's side panel on the right and seeing that
\<open>Boogie_Lang\<close>  has been selected as the main Isabelle session at the top (right below \<open>Purge\<close> and
\<open>Continuous checking\<close>). 
The advantage is that whenever you load the GUI, Isabelle does not need to recheck these files,
thus speeding up the GUI set-up process. A disadvantage is that the Boogie formalisation files are 
"locked", which means that when you jump to the definitions in the Boogie formalisation, then the 
file will have a red shade and you can't further explore the file other than just reading the file
(for example, you can't ctrl-click on definitions in a Boogie formalisation file). The same is true 
for many standard Isabelle sessions, which are by default preloaded by the Isabelle GUI.

We believe that since the Boogie formalisation is not part of the artifact that is
to be evaluated, it is not crucial to explore the Boogie formalisation via ctrl-clicking in the GUI. 
However, if you wish to explore the Boogie formalisation via the GUI, then you can change the main 
Isabelle session from \<open>Boogie_Lang\<close> to \<open>HOL\<close>. After restarting Isabelle and loading \<open>PaperResults.thy\<close>, 
Isabelle will load all files again including those from the Boogie formalisation, which you will then 
be able to explore.\<close>

paragraph \<open>Outcomes and states\<close>
text \<open>Boogie outcomes are defined in \<^typ>\<open>'a state\<close> and Boogie states are defined in \<^typ>\<open>'a nstate\<close>.
      \<^typ>\<open>'a nstate\<close> defines the mapping of variables to values via different mappings 
      (local variable mapping, global variable mapping etc.); the details are not relevant here.\<close>

paragraph \<open>The judgement expressing a finite Boogie execution\<close>
text \<open>The single step execution of a Boogie statement is expressed via \<^const>\<open>red_bigblock_small\<close>,
      which  makes sure that at most one simple command is executed in each step.
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> (\<gamma>, N(\<sigma>\<^sub>b)) \<rightarrow>\<^sub>b\<^sup>* (\<gamma>', r\<^sub>b)\<close> in the paper (expressing a finite Boogie execution 
      taking 0 or more steps) corresponds to \<^prop>\<open>red_ast_bpl P ctxt (\<gamma>, Normal \<sigma>\<^sub>b) (\<gamma>',r\<^sub>b)\<close> in 
      the formalisation
      (reflexive-transitive closure of \<^const>\<open>red_bigblock_small\<close>),
      where \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>. Program points (i.e. \<^term>\<open>\<gamma>\<close> and \<^term>\<open>\<gamma>'\<close> 
      in the example) are expressed via the product type \<^typ>\<open>bigblock * cont\<close> where \<^typ>\<open>bigblock\<close>
      is a statement block and \<^typ>\<open>cont\<close> is a continuation.

      Note that we have defined \<^const>\<open>red_bigblock_small\<close> ourselves. This definition directly builds on
      \<^const>\<open>red_bigblock\<close>, which is defined in the existing Boogie semantics. The only difference 
      between the two is that our version \<^const>\<open>red_bigblock_small\<close> reduces a single simple command 
      in one step, while the version \<^const>\<open>red_bigblock\<close> in the existing Boogie semantics reduces 
      the list of simple commands at the beginning of a statement block in a single step. Reducing a 
      single simple command per step is more natural for the proof connecting to the Viper program.

      Note that both definitions use the semantics for simple commands (asserts, assumes, assignments, 
      and havocs) defined in \<^const>\<open>red_cmd\<close> from the existing Boogie formalisation.

      As we will show later in this file, we use the same Boogie procedure correctness definition 
      as the existing Boogie formalisation, which is expressed in terms of \<^const>\<open>red_bigblock\<close>.
      So, in the end, our semantics defined via \<^const>\<open>red_bigblock_small\<close> just serves as a 
      stepping stone to complete the proof, and the final theorem just uses the existing Boogie 
      semantics.
\<close>

subsection \<open>2.3 Viper Semantics\<close>

paragraph \<open>Outcomes and states\<close>
text \<open>Viper outcomes are defined in \<^typ>\<open>'a stmt_result_total\<close>.
      Viper states are defined via the record type \<^typ>\<open>'a full_total_state\<close>. The type parameter
      \<^typ>\<open>'a\<close> is not relevant for the Viper subset in the paper.

      Given a Viper state \<^term>\<open>\<sigma>\<^sub>v :: 'a full_total_state\<close>, its main components are:
        \<^item> the store: \<^term>\<open>get_store_total \<sigma>\<^sub>v\<close>
        \<^item> the heap: \<^term>\<open>get_hh_total_full \<sigma>\<^sub>v\<close> 
        \<^item> the permission mask: \<^term>\<open>get_mh_total_full \<sigma>\<^sub>v\<close>

      The state has more components, which are not relevant for features outside of the Viper subset 
      presented in the paper.
\<close>

paragraph \<open>The judgement for Viper statement execution\<close> 
text \<open>The big-step judgement for Viper statements is defined via \<^const>\<open>red_stmt_total\<close>.     
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> \<langle>s, \<sigma>\<^sub>v\<rangle> \<rightarrow> r\<^sub>v\<close> in the paper (the execution of statement \<open>s\<close>
      in state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>red_stmt_total ctxt (\<lambda>_.True) \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close> in the 
      formalisation, where the Viper context \<^term>\<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>ctxt\<close> and \<^term>\<open>\<Lambda>\<close>.

      We instantiate the parameter \<^term>\<open>R\<close> in \<^term>\<open>red_stmt_total ctxt R \<Lambda> \<sigma>\<^sub>v \<omega> r\<^sub>v\<close> always with 
      \<^term>\<open>\<lambda>_. True\<close> for the subset in the paper. The parameter exists because of Viper features 
      outside of the subset in the paper. This parameter also shows up in other definitions and for 
      the subset in the paper it is always instantiated with \<^term>\<open>\<lambda>_. True\<close>.
\<close>

paragraph \<open>The judgement for Viper expression evaluation\<close>
text \<open>The expression evaluation is defined via \<^const>\<open>red_pure_exp_total\<close>.
      The notation \<open>\<langle>e, \<sigma>\<^sub>v\<rangle> \<Down> V(v)\<close> in the paper (expression evaluation of expression \<open>e\<close> to value \<open>v\<close> 
      in state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>ctxt, (\<lambda>_. True), Some(\<sigma>\<^sub>v) \<turnstile> \<langle>e; \<sigma>\<^sub>v\<rangle> [\<Down>]\<^sub>t Val v\<close> in the 
      formalisation (here, we use special notation in Isabelle for \<^const>\<open>red_pure_exp_total\<close>). 
      The notation \<open>\<langle>e, \<sigma>\<^sub>v\<rangle> \<Down> <lightning_symbol>\<close> in the paper (expression \<open>e\<close> is ill-defined in \<open>\<sigma>\<^sub>v\<close>) 
      corresponds to \<^prop>\<open>ctxt, (\<lambda>_. True), Some(\<sigma>\<^sub>v) \<turnstile> \<langle>e; \<sigma>\<^sub>v\<rangle> [\<Down>]\<^sub>t VFailure\<close>.       

      \<^term>\<open>ctxt\<close> is the same as for the statement reduction but is redundant for the expression 
      evaluation for the Viper subset in the paper and thus was omitted in the presentation.

      One difference to the paper is that the expression evaluation in the formalisation takes two 
      Viper states as input instead of just one. Having two states is only required for Viper features
      outside of the subset of the paper and that's why in the paper we present the evaluation 
      just with one state to ease the presentation.
       
      In almost all cases of the semantics formalisation, these two states are chosen to be the same 
      one and thus directly correspond to the paper. The only case where the two states differ is 
      during \<open>remcheck\<close> operations, where one state is instantiated to be the \<^emph>\<open>reduction state\<close> and 
      the other the \<^emph>\<open>expression evaluation state\<close> (these states are introduced in the paper). The 
      formalised expression evaluation checks whether there is nonzero permission to fields in the 
      expression evaluation state (as in the paper), but the other lookups (e.g. heap, store) are 
      performed in the reduction state. In the paper subset, expressions can only look up values in 
      the heap and store (but not the permission mask), thus expression lookups in the reduction 
      state and expression evaluation state are the same (since the two states differ only on the 
      permission mask). As a result, only one state is required for the subset of the paper in the
      expression evaluation (namely the expression evaluation state).
\<close>

paragraph \<open>The judgement for \<open>remcheck\<close> reduction and Figure 2\<close>

text \<open>The \<open>remcheck\<close> reduction is defined in \<^const>\<open>red_exhale\<close>.
      The notation \<open>\<sigma>0\<^sub>v \<turnstile> \<langle>A, \<sigma>\<^sub>v\<rangle> \<rightarrow>\<^sub>r\<^sub>c r\<^sub>v\<close> (remcheck reduction of assertion \<open>A\<close> in expression evaluation
      state \<open>\<sigma>0\<^sub>v\<close> and reduction state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^prop>\<open>red_exhale ctxt (\<lambda>_.True) \<sigma>0\<^sub>v A \<sigma>\<^sub>v r\<^sub>v\<close>.
      The parameter \<^term>\<open>ctxt\<close> is not relevant for the paper subset.\<close>

text \<open>The rule (EXH-SUCC) is given by (Figure 2):\<close>

lemmas EXH_SUCC = RedExhale \<comment>\<open>Recall: you can ctrl-click on lemmas such as \<open>RedExhale\<close> to jump to the rule\<close>

text \<open>Note that the premise \<open>nonDet \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'\<close> in the paper is expressed via
  \<^prop>\<open>\<sigma>\<^sub>v' \<in> havoc_locs_state ctxt \<sigma>\<^sub>v'' {loc. get_mh_total_full \<sigma>\<^sub>v loc > 0 \<and> get_mh_total_full \<sigma>\<^sub>v'' loc = 0}\<close>
  in the formalisation.
  The following lemma shows that the two are equivalent (where \<open>nonDet \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'\<close> is formalised
  via \<^prop>\<open>non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'\<close>; \<^term>\<open>ctxt\<close> is used to express a typing property
  on heaps that we omitted from the paper for the sake of presentation):
\<close>

lemmas non_det_select_havoc_locs = non_det_select_havoc_locs_equivalence

text \<open>The rule (EXH-FAIL) is given by (Figure 2):\<close>

lemmas EXH_FAIL = RedExhaleFailure

text \<open>The rule (RC-SEP) is given by (Figure 2):\<close>

lemmas RC_SEP = ExhStarNormal

text \<open>The rule (RC-ACC) is given by (Figure 2):\<close>
                     
lemmas RC_ACC = ExhAcc

text \<open>Note that the term 

\<^term>\<open>( exh_if_total (p \<ge> 0 \<and> (if r = Null then p = 0 else pgte (mh (a,f)) (Abs_preal p)))
                     (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((mh (a,f)) - (Abs_preal p)))
      )\<close>

in the formalisation corresponds to \<open>if exhAccSucc(r, p, \<sigma>\<^sub>v) then N(\<sigma>\<^sub>v\<^sup>R) else F\<close> in the paper (where \<open>\<sigma>\<^sub>v\<^sup>R\<close> 
corresponds to \<^term>\<open>if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((mh (a,f)) - (Abs_preal p))\<close>).

The formalisation uses this term directly in the conclusion instead of introducing a separate 
variable \<open>r\<^sub>v\<close> with an additional premise as the paper does.
\<close>

section \<open>3 A Forward Simulation Methodology For Front-End Translations\<close>


subsection \<open>3.2 One Simulation Judgement to Rule Them All\<close>

paragraph \<open>The generic simulation judgement \<open>sim\<close> (Figure 4 top)\<close>
text \<open>The generic forward simulation judgement \<open>sim\<close> in the paper is defined in \<^const>\<open>rel_general\<close>.
      The notation \<open>sim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, Succ, Fail, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to
      \<^prop>\<open>rel_general R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Succ Fail P ctxt \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>, where the Boogie context \<open>\<Gamma>\<^sub>b\<close> captures both
      \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>.\<close>

paragraph \<open>Three common instantiations of \<open>sim\<close> (Figure 4 bottom)\<close>
text \<open>For the three common instantiations shown at the bottom of figure 4, in the formalisation,
      the Boogie context \<open>\<Gamma>\<^sub>b\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>, and \<^term>\<open>StateCons\<close> corresponds 
      to parameter \<^term>\<open>R\<close> discussed above for the statement reduction and is always
      instantiated to be \<^term>\<open>\<lambda>_.True\<close> in our generated proofs.

      The \<^emph>\<open>statement simulation\<close> is defined in \<^const>\<open>stmt_rel\<close>. 
      The notation \<open>stmSim\<^sub>\<Gamma>\<^sub>v,\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, s, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
      \<^prop>\<open>stmt_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr (\<lambda>_.True) \<Lambda> P ctxt s \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.
      The Viper context \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>ctxt_vpr\<close> and \<^term>\<open>\<Lambda>\<close>.

      The \<^emph>\<open>expression well-definedness simulation\<close> is defined in \<^const>\<open>exprs_wf_rel_2\<close>.
      The notation \<open>wfSim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, es, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to
      \<^prop>\<open>exprs_wf_rel_2 R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr (\<lambda>_.True) P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.
      \<^term>\<open>ctxt_vpr\<close> is not relevant here for the subset presented in the paper.
     
      Since the expression evaluation takes two states as input in the formalisation (see above),
      \<^term>\<open>R\<^sub>i\<^sub>n\<close> and \<^term>\<open>R\<^sub>o\<^sub>u\<^sub>t\<close> also are defined in terms of both states. For convenience, they are 
      both in curried form and thus the instantiation via \<^const>\<open>rel_general\<close> uncurries them.
     
      For convenience, we usually work with \<^const>\<open>exprs_wf_rel\<close>, where the input and output
      state relation are the same, which is sufficient for our use case. That is, we have:
\<close>

lemma exprs_wf_rel_with_2_equiv: 
  "exprs_wf_rel_2 R R ctxt_vpr StateCons P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t \<longleftrightarrow>
   exprs_wf_rel R ctxt_vpr StateCons P ctxt e_vpr \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t"
  by (simp add: exprs_wf_rel_2_def exprs_wf_rel_def)    

text \<open>The \<^emph>\<open>remcheck simulation\<close> is defined via \<^const>\<open>exhale_rel0\<close>. The notation
      \<open>rcSim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
      \<^prop>\<open>exhale_rel0 R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.
      \<^term>\<open>ctxt_vpr\<close> is not relevant here for the subset presented in the paper.
      For convenience, \<^term>\<open>R\<^sub>i\<^sub>n\<close> and \<^term>\<open>R\<^sub>o\<^sub>u\<^sub>t\<close> are curried, and thus the instantiation via
      \<^const>\<open>rel_general\<close> uncurries them.

      In our formalisation, we always directly work with a remcheck simulation that additionally 
      takes a predicate \<open>Q\<close> on assertions as a parameter as described in Section 3.5 of the paper.
      The notation \<open>rcInvSim\<^sub>\<Gamma>\<^sub>b\<^sup>Q(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper (Figure 7) corresponds to 
      \<^prop>\<open>exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.
    
      \<^const>\<open>exhale_rel\<close> is directly defined in terms of the generic simulation judgement, 
      but the following lemma shows that this is equivalent to defining \<^const>\<open>exhale_rel\<close> in 
      terms \<^const>\<open>exhale_rel0\<close> as we do in the paper for the sake of presentation:
\<close>

lemma exhale_rel_exhale_rel0_inst_equiv: 
  "exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>' \<longleftrightarrow>
   exhale_rel0 (\<lambda>\<omega>def \<omega> ns. R\<^sub>i\<^sub>n \<omega>def \<omega> ns \<and> Q A \<omega>def \<omega>) R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  unfolding exhale_rel_def exhale_rel0_def
  by simp

subsection \<open>3.3 Instantiation-Independent Rules\<close>

paragraph \<open>The rules shown in Figure 5\<close>

text \<open>The generic composition rule COMP (Figure 5) is given by:\<close>

lemmas COMP_paper = rel_general_comp

text \<open>The sequential composition rule SEQ-SIM (Figure 5) is given by:\<close>

lemmas SEQ_SIM = stmt_rel_seq \<comment>\<open>Note that the proof uses the generic composition rule\<close>

text \<open>Additional rules derived from the generic composition rule are:\<close>

lemmas COMP_derived = 
  exhale_rel_star \<comment>\<open>remcheck A1*A2\<close>
  inhale_rel_star \<comment>\<open>inhale A1*A2\<close>

text \<open>The propagation rule BPROP (Figure 5) is given by:\<close>

lemmas BPROP = brop_paper

text \<open>Here, \<open>bSim\<^sub>\<Gamma>\<^sub>b(R, R', \<gamma>, \<gamma>')\<close> in the paper is defined by \<^term>\<open>bsim R R' P ctxt \<gamma> \<gamma>'\<close>.
In the main parts of our formalisation, we use \<^term>\<open>red_ast_bpl_rel R R\<^sub>1 P ctxt \<gamma> \<gamma>'\<close> instead,
which is not defined directly via the generic simulation judgement (for historical reasons). The
following lemma shows that the two definitions are equivalent:
\<close>

lemmas bsim_red_ast_bpl_rel_equiv = bsim_red_ast_bpl_rel

text \<open>Our formalisation uses various versions of propagation rules (using \<^const>\<open>red_ast_bpl_rel\<close>), 
which follow the same structure as the rule BPROP in the paper (some of them are stronger rules).
Examples include:\<close>

lemmas propagation_rule_examples = 
   rel_propagate_pre rel_propagate_post \<comment>\<open>generic versions\<close>
   stmt_rel_propagate stmt_rel_propagate_2 \<comment>\<open>propagation rules derived for the statement relation\<close>
   exhale_rel_propagate_pre exhale_rel_propagate_post \<comment>\<open>propagation rules derived for \<open>remcheck\<close> relation\<close>   

subsection \<open>3.4 Examples: Generic Decomposition in Action\<close>

paragraph \<open>The rule EXH-SIM (Figure 6) is given by:\<close>
                       
lemmas EXH_SIM = exhale0_stmt_rel

text \<open>As discussed above for section 2.3 (the semantics of \<open>exhale\<close>), we use
\<^const>\<open>havoc_locs_state\<close> to express the nondeterministic heap assignment, 
while the paper uses \<open>nonDet\<close>. As we show there, the two formulations are equivalent.
The first two premises in the lemma (WfConsistency, Consistent) are irrelevant for the paper, since
\<^term>\<open>StateCons\<close> is always instantiated to be \<^term>\<open>\<lambda>_. True\<close> for the subset in the paper, and thus
these two premises are trivially satisfied.

As discussed above in section 3.2, instead of working with \<open>rcSim\<close> we always work with
\<open>rcInvSim\<close> (see Figure 7), which takes an additional predicate \<open>Q\<close> on assertions.
The EXH-SIM rule generalised to \<open>rcInvSim\<close> is given by:\<close>

lemmas EXH_SIM_rcInvSim = exhale_stmt_rel
 
subsection \<open>3.5 Injecting Non-Local Hypotheses into Simulation Proofs\<close>

paragraph \<open>Figure 7\<close>
text \<open>As also mentioned above in section 3.2, the notation \<open>rcInvSim\<^sub>\<Gamma>\<^sub>b\<^sup>Q(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> 
      in the paper (Figure 7) corresponds to
      \<^prop>\<open>exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr (\<lambda>_.True) P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>
      and the following lemma shows that the definition given for \<open>rcInvSim\<close> is equivalent to the one
      we give for \<^const>\<open>exhale_rel\<close>
\<close>

lemmas rcSimInv_paper =  exhale_rel_exhale_rel0_inst_equiv

text\<open>The rule RSEP-SIM (Figure 7) is given by:\<close>

lemmas RSEP_SIM = exhale_rel_star

text \<open>The two premises Invariant1 and Invariant2 in the formalisation correspond together to the
      last premise of RSEP-SIM in the paper.\<close>


section \<open>4 Putting the Methodology to Work\<close>

subsection \<open>4.1 State Relation\<close>

paragraph \<open>State Relation\<close>
text \<open>The state relation is defined in \<^const>\<open>state_rel0\<close>.
      The notation \<open>SR\<^sub>\<Gamma>\<^sub>b\<^sup>T\<^sup>r\<^sup>,\<^sup>A\<^sup>v((\<sigma>0\<^sub>v,\<sigma>\<^sub>v), \<sigma>\<^sub>b)\<close> in the paper corresponds to
      \<^prop>\<open>state_rel0 Pr (\<lambda>_.True) A \<Lambda> TyRep Tr Av \<sigma>0\<^sub>v \<sigma>\<^sub>v \<sigma>\<^sub>b\<close>
      where \<open>\<Gamma>\<^sub>b\<close> captures both \<^term>\<open>A\<close> and \<^term>\<open>\<Lambda>\<close>.
      \<^term>\<open>Pr\<close> is the Viper program representation and is left implicit in the paper.
      \<^term>\<open>TyRep\<close> provides information on how Viper types are represented in Boogie. We omit
      \<^term>\<open>TyRep\<close> in the paper, since for the subset in the paper, we always instantiate it the same
      way, namely using \<^term>\<open>ty_repr_basic I\<close> (where \<^term>\<open>I\<close> is irrelevant for the subset of the 
      paper).

      The presented conjuncts in the paper are represented as follows 
      in the definition of \<^const>\<open>state_rel0\<close>:
                                                                                       
      \<^item> State consistency: The conjunct \<open>consistent(\<sigma>\<^sub>v)\<close> corresponds to
                           \<^term>\<open>wf_mask_simple (get_mh_total_full \<sigma>\<^sub>v)\<close>.
      \<^item> Field relation: The conjunct \<open>fieldRel\<^sub>\<Gamma>\<^sub>b(field(Tr), \<sigma>\<^sub>b)\<close> corresponds to     
                        \<^term>\<open>field_rel Pr \<Lambda> (field_translation Tr) \<sigma>\<^sub>b\<close>.
      \<^item> Auxiliary variable constraints: The conjunct \<open>\<forall>x,P. AV(x) = P \<longrightarrow> P(\<sigma>\<^sub>b(x))\<close> corresponds to
                        \<^term>\<open>aux_vars_pred_sat \<Lambda> AuxPred \<sigma>\<^sub>b\<close>
      \<^item> Store relation: The conjunct \<open>stRel\<^sub>\<Gamma>\<^sub>b(var(Tr), \<sigma>\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to 
                        \<^term>\<open>store_rel A \<Lambda> (var_translation Tr) \<sigma>\<^sub>v \<sigma>\<^sub>b\<close>
      \<^item> Heap and permission mask relation: The conjunct \<open>hmRel\<^sub>\<Gamma>\<^sub>b(H(Tr), M(Tr), \<sigma>\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to
          \<^term>\<open>heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<sigma>\<^sub>v) \<sigma>\<^sub>b \<and>
               mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<sigma>\<^sub>v) \<sigma>\<^sub>b\<close>
          The conjunct \<open>hmRel\<^sub>\<Gamma>\<^sub>b(H\<^sup>0(Tr), M\<^sup>0(Tr), \<sigma>0\<^sub>v, \<sigma>\<^sub>b)\<close> corresponds to
          \<^term>\<open>heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<sigma>0\<^sub>v) \<sigma>\<^sub>b \<and>
               mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (getm_mh_total_full \<sigma>0\<^sub>v) \<sigma>\<^sub>b\<close>
\<close>

subsection \<open>4.2 Non-Locality\<close>

paragraph\<open>Definition \<open>Q\<^sub>p\<^sub>r\<^sub>e\<close>\<close>
text \<open>The predicate \<open>Q\<^sub>p\<^sub>r\<^sub>e\<close> is defined in \<^const>\<open>framing_exh\<close>. 
      The notation \<open>Q\<^sub>p\<^sub>r\<^sub>e(A, \<sigma>0\<^sub>v, \<sigma>\<^sub>v)\<close> corresponds to \<^prop>\<open>framing_exh ctxt_vpr (\<lambda>_.True) A \<sigma>0\<^sub>v \<sigma>\<^sub>v\<close>.
      The extra parameter \<^term>\<open>ctxt_vpr\<close> (the Viper context) is not relevant for the subset 
      presented in the paper in this case.
      The conjunct  \<open>\<not> \<langle>A, \<sigma>i\<^sub>v\<rangle> \<rightarrow>\<^sub>i\<^sub>n\<^sub>h F\<close> in the paper corresponds to
      \<^prop>\<open>assertion_framing_state ctxt (\<lambda>_.True) A \<sigma>i\<^sub>v\<close>.
\<close>

paragraph\<open>Lemma 4.1\<close>      
text\<open>Lemma 4.1 is shown by:\<close>
lemmas lemma_4_1 = exhale_inhale_normal

text \<open>The parameter \<^term>\<open>StateCons\<close> is is always instantiated to be \<^term>\<open>\<lambda>_.True\<close> for the paper subset.
      The premise \<^prop>\<open>mono_prop_downward (\<lambda>_.True)\<close> is trivially true.
      The premise \<^term>\<open>no_perm_assertion A \<and> no_unfolding_assertion A\<close> restricts the assertion \<^term>\<open>A\<close>
      to be within the subset presented in the paper.

      The premise \<open>\<not> \<langle>A, \<sigma>i\<^sub>v\<rangle> \<rightarrow>\<^sub>i\<^sub>n\<^sub>h F\<close> in the paper corresponds to
      \<^prop>\<open>assertion_framing_state ctxt (\<lambda>_.True) A \<sigma>i\<^sub>v\<close>.

      The conclusion \<open>\<langle>A, \<sigma>i\<^sub>v\<rangle> \<rightarrow>\<^sub>i\<^sub>n\<^sub>h N(\<sigma>s\<^sub>v)\<close> in the paper corresponds to
      \<^prop>\<open>red_inhale ctxt (\<lambda>_.True) A \<sigma>i\<^sub>v (RNormal \<sigma>s\<^sub>v)\<close> (reduction of \<open>inhale A\<close> from state
      \<^term>\<open>\<sigma>i\<^sub>v\<close> that results in outcome \<^term>\<open>(RNormal \<sigma>s\<^sub>v)\<close>.
\<close>

subsection \<open>4.3 Proof Automation\<close>

paragraph\<open>The Isabelle tactic to prove forward simulations\<close>
text \<open>Our custom tactic to prove the forward simulation of Viper statements is defined in
      \<^ML>\<open>stmt_rel_tac\<close> directly in the Standard ML programming language, which is Isabelle's 
     implementation language. \<^ML>\<open>stmt_rel_tac\<close> invokes other custom tactics such as, for example, 
     a tactic for the simulation of \<open>remcheck\<close> operations defined in \<^ML>\<open>exhale_rel_aux_tac\<close>.

     \<^ML>\<open>stmt_rel_tac\<close> is parametric in the hints and the tactic for the \<^emph>\<open>primitive\<close> statements. 
     The type signature makes this explicit via the argument types \<^ML_type>\<open>('a, 'i, 'e) stmt_rel_info\<close> 
     (a record that includes the primitive statement tactic) and \<^ML_type>\<open>'a stmt_rel_hint\<close> (for the hints).
     In our proofs, we instantiate 'a to be \<^ML_type>\<open>atomic_rel_hint\<close> primitive statement hints and 
     define the tactic for the primitive statements to be \<^ML>\<open>atomic_rel_inst_tac\<close>.

     Our tactics apply rules proved for the different constructs. In some cases, we derive 
     instantiated versions of these rules upfront, which makes the tactics easier to write. 
     For example, \<^ML>\<open>stmt_rel_tac\<close> applies the lemma @{thm [source] stmt_rel_seq_same_rel} 
     (you can ctrl-click on \<open>stmt_rel_seq_same_rel\<close>) for the sequential composition, which is 
     the same as the sequential composition rule SEQ-SIM shown in Figure 5, except that the input 
     and output relation are fixed to be the same.
\<close>

subsection \<open>4.4 Background Theory and Polymorphic Maps\<close>

paragraph \<open>Boogie procedure correctness definition (top of Figure 9)\<close>
text\<open>The correctness of a Boogie procedure is defined in \<^const>\<open>proc_is_correct\<close>. This definition
was taken from an extension of the CAV21 paper \<open>Formally Validating a Practical Verification 
Condition Generator\<close>, which is developed in an open source repository. The details of the Boogie
semantics are not part of this artifact. Nevertheless, we explain the Boogie correctness definition
at a high level. 

The final parameter of the \<^const>\<open>proc_is_correct\<close> definition abstracts over the type
of a procedure body and its associated operational semantics, which allows reusing the same definition 
for Boogie abstract syntax trees and control-flow graphs.

The notation \<open>Correct\<^sub>b\<^sup>G(p)\<close> in the paper corresponds to 

\<^prop>\<open>\<forall>T. proc_is_correct T fun_decls constants unique_consts global_vars axioms p Ast.proc_body_satisfies_spec\<close>

where the universally quantified \<^term>\<open>T\<close> corresponds to the type interpretation. The global 
declarations \<open>G\<close> capture \<^term>\<open>fun_decls\<close> (function declarations), \<^term>\<open>constants\<close> (constant 
declarations),\<^term>\<open>unique_consts\<close> (subset of constant declarations that are marked as unique),
\<^term>\<open>global_vars\<close> (global variable declarations) and \<^term>\<open>axioms\<close> (axioms).
The final argument \<^const>\<open>Ast.proc_body_satisfies_spec\<close> concretely specifies when a body represented 
by a Boogie AST has no failing executions. \<^const>\<open>Ast.proc_body_satisfies_spec\<close> also takes the 
procedure pre- and postcondition into account, which are not relevant for the paper, since the 
Viper-to-Boogie translation does not emit any pre- and postconditions in the Boogie program.

(Note that once you click on \<^const>\<open>proc_is_correct\<close> you can't ctrl-click further in the source, since the
Boogie formalisation is preloaded; see the comments on Section 2.2 regarding this if you want to be 
able to explore the files.) 

\<^const>\<open>Ast.proc_body_satisfies_spec\<close> expresses a finite Boogie execution that takes 0 or more steps 
via \<^term>\<open>rtranclp (red_bigblock A [] \<Lambda> \<Gamma> [] ast)\<close> (the empty lists \<^term>\<open>[]\<close> reflect our instantiation
for the corresponding parameters)  while for the Boogie semantics discussed in Section 2.2 above and most of the
formalisation we use \<^term>\<open>red_ast_bpl ast (create_ctxt_bpl A \<Lambda> \<Gamma>)\<close>. We discussed the difference 
between \<^term>\<open>red_ast_bpl\<close> (defined via \<^term>\<open>red_bigblock_small\<close>) and \<^term>\<open>red_bigblock\<close> in  
Section 2.2 above: 
The only difference between the two is that \<^term>\<open>red_bigblock\<close> reduces the simple commands at 
the beginning of a statement block in a single step, while \<^term>\<open>red_bigblock_small\<close> reduces each 
simple command separately (one step each). 
We formally bridge the gap between these two definitions whenever we need to directly deal with the 
correctness of a Boogie procedure (e.g. when proving the final theorem).
\<close>

paragraph \<open>Instantiation of \<open>HType\<close>\<close>
text \<open>The type \<^typ>\<open>'a vbpl_absval\<close> defines our instantiation of the uninterpreted Boogie types
generated by the Viper-to-Boogie translation. In this type definition, \<open>HType\<close> is instantiated via
\<^term>\<open>AHeap h\<close>, where \<^term>\<open>h\<close> is a partial mapping (represented by a function that maps to the option 
type; note that \<^typ>\<open>'a \<rightharpoonup> 'b\<close> is syntactic sugar for \<^typ>\<open>'a \<Rightarrow> 'b option\<close>) as presented in the paper. 
The function \<^const>\<open>vbpl_absval_ty_opt\<close> is the main building block for constructing the corresponding
type interpretation for the Viper-to-Boogie translation (i.e. mapping values of type
\<^typ>\<open>'a vbpl_absval\<close> to Boogie types).
                                                                                             
The instantiations for the \<open>upd\<close> and \<open>read\<close> functions of \<open>HType\<close> are provided by \<^const>\<open>store_heap\<close>
and \<^const>\<open>select_heap\<close>, respectively.
\<close>

subsection \<open>4.5 Generating A Proof of the Final Theorem\<close>

paragraph \<open>Correctness of a Viper method (Figure 9 at the bottom)\<close>
text \<open>The correctness of a Viper method is defined in \<^const>\<open>vpr_method_correct_paper\<close>.
The notation \<open>Correct\<^sub>v\<^sup>F\<^sup>,\<^sup>M(m)\<close> corresponds to \<^prop>\<open>vpr_method_correct_paper ctxt_vpr m\<close>
where F,M capture \<^term>\<open>ctxt_vpr\<close>. 

In our generated proofs, we use a more general version for the correctness of a Viper method
(defined in \<^const>\<open>vpr_method_correct_total\<close>) that is applicable to a larger subset of Viper than
supported by the paper, where the correctness of a method is expressed via 
\<^prop>\<open>vpr_method_correct_total ctxt_vpr (\<lambda>_.True) m\<close>.

The following lemma shows that the more general version implies the version of the paper for Viper 
methods that are within the Viper subset presented in the paper:
\<close>

lemmas general_method_correctness_stronger = method_correctness_stronger_than_paper

text \<open>Thus, our generated proofs prove the method correctness for each method as presented
      in the paper.\<close>

paragraph \<open>Helper lemma to prove \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close>\<close>

text \<open>To generate proofs for \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> (Figure 10, bottom), we use a generic helper lemma 
      that we prove once and for all and that reflects the strategy for \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> as
      described in Section 4.5 of the paper.
      This generic helper lemmas is given by:\<close> 

lemmas generic_helper_lemma_final_theorem = end_to_end_vpr_method_correct_partial

text \<open>The lemma has lots of assumptions that are not relevant here (we prove the assumptions when 
we generate the proofs). There are three relevant assumptions directly mentioned in the paper:
  \<^item> Assumption with name \<open>Boogie_correct\<close>: 
    This expresses correctness of the Boogie procedures (corresponds to the left-hand side 
    \<open>Correct\<^sub>b\<^sup>G(p)\<close> of \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close>)
  \<^item> Assumption with name \<open>VprMethodRel\<close> (defined via \<^const>\<open>method_rel\<close>): 
    This assumption corresponds to the forward simulation statement shown at the end of Section 4.5 in 
    the paper. Note that \<^const>\<open>method_rel\<close> is more general than the forward simulation shown in the 
    paper. In particular, the conjunct \<^const>\<open>post_framing_rel\<close> is used to show the well-formedness 
    of the method postcondition (which we ignore in the paper for the sake of presentation). 
    Moreover, note that \<^const>\<open>method_rel\<close> includes a left-hand side
    \<^const>\<open>vpr_all_method_spec_correct_total\<close>, which states that each method specification in the program 
    is well-formed (this directly corresponds to \<open>\<forall>m' \<in> M. SpecWf(m')\<close> in the definition of
    \<open>Rel\<^sup>G\<^sub>F\<^sub>,\<^sub>M(m,p)\<close> in the paper in Figure 10).
  \<^item> Assumption with name \<open>InitialStateRel\<close>:
    This assumption requires one to choose an initial Boogie state that is related to the initial
    Viper state.
\<close>

section \<open>Appendix\<close>

subsection \<open>A Inhale Semantics\<close>

text \<open>The rule (INH) (Figure 11) is given by:\<close>

lemmas INH_paper = RedInhale

text \<open>Here \<open>\<langle>A, \<sigma>\<^sub>v\<rangle> \<longrightarrow>\<^sub>i\<^sub>n\<^sub>h r\<^sub>v\<close> in the paper is given by \<^term>\<open>red_inhale ctxt (\<lambda>_.True) A \<sigma>\<^sub>v r\<^sub>v\<close>. The 
parameter \<^term>\<open>ctxt\<close> is not relevant for the subset of the paper.\<close>

text \<open>The rule (INH-ACC) (Figure 11) is given by:\<close>

lemmas INH_ACC_paper = InhAcc

text \<open>In the formalisation of INH-ACC, the premises are written slightly differently than in the paper.

The term
\<^term>\<open>W' = (if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r,f) (Some (Abs_preal p)))\<close>

ensures that \<^term>\<open>W'\<close> is equal to the singleton set \<open>{ addperm(\<sigma>\<^sub>v, r, f, p) }\<close> if adding \<open>p\<close> permission to heap location
\<open>(r,f)\<close> does not exceed 1 permission and otherwise \<^term>\<open>W'\<close> is empty.
(\<open>addperm(\<sigma>\<^sub>v, r, f, p)\<close> is also used in Figure 11 of the paper to represent the state \<open>\<sigma>\<^sub>v\<close> where \<open>p\<close> 
permission is added to the heap location \<open>(r,f)\<close>).

This definition of \<^term>\<open>W'\<close> together with the premise
 \<^prop>\<open>th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' res\<close> in the formalisation capture
 the third, fourth, and fifth premises of rule INH-ACC in the paper. In particular, 
 \<^prop>\<open>th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' res\<close> ensures that
  \<^item> \<^term>\<open>res\<close> is a failure state if \<^term>\<open>p \<ge> 0\<close> does not hold (third premise in paper)
  \<^item> \<^term>\<open>res\<close> is a normal state given by \<open>addperm(\<sigma>\<^sub>v, r, f, p)\<close> if (1) \<^term>\<open>p \<ge> 0\<close> holds and 
    (2) \<^term>\<open>W'\<close> is nonempty  (which can only be the case if adding \<^term>\<open>p\<close> to the permission for \<^term>\<open>(r,f)\<close> 
    does not exceed 1 if \<^term>\<open>r \<noteq> Null\<close>) and (3) \<^term>\<open>p > 0 \<longrightarrow> r \<noteq> Null\<close> holds.
  \<^item> \<^term>\<open>res\<close> is a magic state in the other cases 
\<close>


text \<open>The rule (INH-SEP-S) (Figure 11) is given by:\<close>

lemmas INH_SEP_S_paper = InhStarNormal

text \<open>The rule (INH-SEP-F) (Figure 11) is given by:\<close>

lemmas INH_SEP_F_paper = InhStarFailureMagic

text \<open>Note that this lemma also capture the case for the magic outcome.\<close>

subsection \<open>B Another Simulation Rule Example\<close>

text \<open>The rule (RACC-SIM) (Figure 12) is given by:\<close>

lemmas RACC_SIM_paper = exhale_rel_field_acc

text \<open>Note that the formalisation directly uses the \<open>remcheck\<close> simulation relation with the additional 
predicate \<open>Q\<close> (\<open>rcInvSim\<close> in Figure 7). If one sets \<open>Q\<close> to be the trivial predicate
\<^term>\<open>\<lambda>_ _ _. True\<close>, then the formalisation corresponds to the rule using \<open>rcSim\<close>.

Also note that the paper uses a universal quantifier on a Viper state in the first premise for RACC-SIM,
while there is no such universal quantifier in the formalisation. The reason is that, as we discussed above
in Section 3.2, the expression well-definedness simulation (\<open>wfSim\<close> in the paper) has state relations
in the formalisation that take two Viper states as input, while in the paper the state relations only
take one Viper state as input (due to the expression evaluation being more general in the formalisation,
which is not relevant for the paper subset). 

The universal quantifier in the paper bridges the gap from a state relation with two Viper states
(for \<open>rcSim\<close>) to a state relation with one Viper state (for \<open>wfSim\<close>). More specifically, the universal
quantifier states that only the expression evaluation state is relevant for \<open>wfSim\<close>, which is indeed 
the case for the paper subset. 

The formalisation does not need to bridge this gap, since in the formalisation both \<open>rcSim\<close> and \<open>wfSim\<close> 
use state relations that take two Viper state as inputs.
\<close>

end

