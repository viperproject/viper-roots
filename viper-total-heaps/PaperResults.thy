theory PaperResults
imports ViperBoogieEndToEnd
begin

text \<open>The following Isabelle theory file contains references to all the formalised results explicitly mentioned in
the paper. The Isabelle sections and subsections match those from the paper except if mentioned otherwise.
In the Isabelle IDE, you can ctrl-and-click on the original definitions (highlighted in black everywhere
except for constants where it has the same orange color as this text). Clickable definitions in the
Isabelle documentation (i.e., within text \<open>...\<close> annotations) can be contained in
  \<^item> types (for example, \<^typ>\<open>ViperLang.stmt\<close>)
  \<^item> constants (for example, \<^const>\<open>red_stmt_total\<close>; note that here the clickable constant is in orange)
  \<^item> terms (for example, \<^term>\<open>red_stmt_total ctxt\<close>)
  \<^item> propositions (for example, \<^prop>\<open>red_stmt_total ctxt R \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>); these are just boolean terms

To refer to specific rules or proved theorems, we use Isabelle's \<open>lemmas\<close> keyword. For example:
\<close>

lemmas example_for_rule = RedExhale RedExhaleFailure
 \<comment>\<open>you can ctrl-click on the rules \<open>RedExhale\<close> and \<open>RedExhaleFailure\<close>\<close>

lemmas example_for_a_proved_theorem = exhale_inhale_normal
\<comment>\<open>you can ctrl-click on the proved theorem \<open>exhale_inhale_normal\<close>\<close>

text \<open>Whenever a ctrl-click takes you to another theory, you can use the green arrow buttons at the top 
      of the Isabelle IDE to jump back (or forward) to the previous position.
      You can also use the "Sidekick" view on the right side of the Isabelle IDE to quickly jump to a section or 
      subsection.\<close>

section \<open>2 Viper and Boogie: Background and Semantics\<close>

subsection \<open>2.1 The Viper and Boogie languages\<close>

text \<open>The Viper AST for statements is defined in \<^typ>\<open>ViperLang.stmt\<close>.
      The Boogie AST for statements is defined in \<^typ>\<open>Ast.bigblock\<close>\<close>

text \<open>Both formalised ASTs includes a larger subset than presented in the paper (for example,
      loops for Viper and Boogie). For the artifact, only the subset mentioned in the paper is relevant. 
      Some of our definitions in the formalisations are generalised to also work for features outside
      the subset. These generalisations are not relevant here and throughout this file, we will make clear 
      which parts are relevant.\<close>

subsection \<open>2.2: Boogie Semantics\<close>

text \<open> \<^item> Statement single step reduction is defined via \<^const>\<open>red_bigblock_small\<close>
       \<^item> Statement multistep reduction is defined via \<^const>\<open>red_ast_bpl\<close>

  The notation \<open>\<Gamma>\<^sub>v \<turnstile> (\<gamma>, N(\<sigma>\<^sub>b)) \<rightarrow>\<^sub>b\<^sup>* (\<gamma>', r\<^sub>b)\<close> in the paper (expressing a finite Boogie execution taking
  0 or more steps) corresponds to \<^prop>\<open>red_ast_bpl P ctxt (\<gamma>,N(\<sigma>\<^sub>b)) (\<gamma>',r\<^sub>b)\<close> in the formalisation,
  where \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>.
 \<close>

subsection \<open>2.3 Viper Semantics\<close>

paragraph \<open>Viper states\<close>
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
      but is redundant for the Viper subset in the paper and thus was omitted in the presentation.      

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
      the Boogie context \<open>\<Gamma>\<^sub>b\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>, the Viper context \<open>\<Gamma>\<^sub>v\<close> captures 
      both \<^term>\<open>ctxt_vpr\<close> and \<^term>\<open>\<Lambda>\<close>, and \<^term>\<open>StateCons\<close> corresponds to parameter \<^term>\<open>R\<close> discussed
      above for the statement and expression reduction and is always instantiated to be \<^term>\<open>\<lambda>_.True\<close>
      in our generated proofs.\<close>

text \<open>The statement simulation is defined in \<^const>\<open>stmt_rel\<close>. The notation
     \<open>stmSim\<^sub>\<Gamma>\<^sub>v,\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, s, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
     \<^prop>\<open>stmt_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons \<Lambda> P ctxt s \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.\<close>

text \<open>The remcheck simulation is defined in \<^const>\<open>exhale_rel0\<close>. The notation
     \<open>rcSim\<^sub>\<Gamma>\<^sub>b(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper corresponds to 
      \<^prop>\<open>exhale_rel0 R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close> in the formalisation.
     For convenience reasons, \<^term>\<open>R\<^sub>i\<^sub>n\<close> and \<^term>\<open>R\<^sub>o\<^sub>u\<^sub>t\<close> are curried, and thus the instantiation via
     \<^const>\<open>rel_general\<close> uncurries them.
     In our formalisation, we always directly work with a remcheck simulation that additionally takes
     a predicate \<open>Q\<close> on assertions as a parameter as described in Section 3.5 of the paper.
     The notation \<open>rcSim\<^sub>\<Gamma>\<^sub>b\<^sup>Q(R\<^sub>i\<^sub>n, R\<^sub>o\<^sub>u\<^sub>t, A, \<gamma>\<^sub>i\<^sub>n, \<gamma>\<^sub>o\<^sub>u\<^sub>t)\<close> in the paper (Figure 7) corresponds to 
     \<^prop>\<open>exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr StateCons P ctxt A \<gamma>\<^sub>i\<^sub>n \<gamma>\<^sub>o\<^sub>u\<^sub>t\<close>.
    
     \<^const>\<open>exhale_rel\<close> is directly defined in terms of the generic simulation judgement, but the following
     lemma shows that this is equivalent to defining \<^const>\<open>exhale_rel\<close> in terms \<^const>\<open>exhale_rel0\<close>
     as we do in the paper for the sake of presentation:
\<close>

lemma exhale_rel_exhale_rel0_inst_equiv: 
  "exhale_rel R\<^sub>i\<^sub>n R\<^sub>o\<^sub>u\<^sub>t Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>' \<longleftrightarrow>
   exhale_rel0 (\<lambda>\<omega>def \<omega> ns. R\<^sub>i\<^sub>n \<omega>def \<omega> ns \<and> Q A \<omega>def \<omega>) R\<^sub>o\<^sub>u\<^sub>t ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  unfolding exhale_rel_def exhale_rel0_def
  by simp



end

