theory PaperResults
imports ViperBoogieEndToEnd
begin

text \<open>The following Isabelle theory file contains references to all the results explicitly mentioned in
the paper. The Isabelle sections and subsections match those from the paper except if mentioned otherwise.
In the Isabelle IDE, you can ctrl-and-click on the original definitions (highlighted in black everywhere
except for constants where it has the same orange color as this text). Clickable definitions in the
Isabelle documentation (i.e., within text \<open>...\<close> annotations) can be contained in
  \<^item> types (for example, \<^typ>\<open>ViperLang.stmt\<close>)
  \<^item> terms (for example, \<^term>\<open>red_stmt_total ctxt R \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close>)
  \<^item> constants (for example, \<^const>\<open>red_stmt_total\<close>; notice that here the clickable constant is in orange)
\<close>

section \<open>2: "Viper and Boogie: Background and Semantics"\<close>

subsection \<open>2.1: The Viper and Boogie languages\<close>

text \<open>The Viper AST for statements is defined in \<^typ>\<open>ViperLang.stmt\<close>.\<close>

text \<open>The Boogie AST for statements is defined in \<^typ>\<open>Ast.bigblock\<close>\<close>

text \<open>Both formalised ASTs includes a larger subset than presented in the paper (for example,
      loops for Viper and Boogie). For the artifact, only the subset mentioned in the paper is relevant. 
      Some of our definitions in the formalisations are generalised to also work for features outside
      the subset. These generalisations are not relevant here and throughout this file, we will make clear 
      which parts are relevant.\<close>

subsection \<open>2.2: Boogie Semantics\<close>

text \<open> \<^item> Statement single step reduction is defined via \<^const>\<open>red_bigblock_small\<close>
       \<^item> Statement multistep reduction is defined via \<^const>\<open>red_ast_bpl\<close>

  The notation \<open>\<Gamma>\<^sub>v \<turnstile> (\<gamma>, N(\<sigma>\<^sub>b)) \<rightarrow>\<^sub>b\<^sup>* (\<gamma>', r\<^sub>b)\<close> in the paper (expressing a finite Boogie execution taking
  0 or more steps) corresponds to \<^term>\<open>red_ast_bpl P ctxt (\<gamma>,N(\<sigma>\<^sub>b)) (\<gamma>',r\<^sub>b)\<close> in the formalisation,
  where \<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>P\<close> and \<^term>\<open>ctxt\<close>.
 \<close>

subsection \<open>2.3: Viper Semantics\<close>

paragraph \<open>Semantics for Viper statements\<close> 
text \<open>The big-step judgement for Viper statements is defined via \<^const>\<open>red_stmt_total\<close>.     
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> \<langle>s, \<sigma>\<^sub>v\<rangle> \<rightarrow> r\<^sub>v\<close> in the paper (the execution of statement \<open>s\<close>
      in state \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^term>\<open>red_stmt_total ctxt R \<Lambda> s \<sigma>\<^sub>v r\<^sub>v\<close> in the formalisation,
      where \<^term>\<open>\<Gamma>\<^sub>v\<close> captures both \<^term>\<open>ctxt\<close> and \<^term>\<open>\<Lambda>\<close>

      The parameter \<^term>\<open>R\<close> is not relevant for the Viper subset in the paper. In our proofs, 
      it is always instantiated to be \<open>\<lambda>_. True\<close>.
\<close>

paragraph \<open>Viper expression evaluation\<close>
text \<open>The expression evaluation is defined via \<^const>\<open>red_pure_exp_total\<close>.
      The notation \<open>\<Gamma>\<^sub>v \<turnstile> \<langle>e, \<sigma>\<^sub>v\<rangle> \<Down> V(v)\<close> in the paper (expression evaluation of expression \<open>e\<close> in state 
      \<open>\<sigma>\<^sub>v\<close>) corresponds to \<^term>\<open>ctxt, R, Some(\<sigma>\<^sub>v) \<turnstile> \<langle>e; \<sigma>\<^sub>v\<rangle> [\<Down>]\<^sub>t Val v\<close> in the formalisation (here,
      we have special notation for \<^const>\<open>red_pure_exp_total\<close>). 

      As for the statements, the \<^term>\<open>R\<close> is not relevant for the Viper subset in the paper.
      \<close>



text \<open>\<close>

end

