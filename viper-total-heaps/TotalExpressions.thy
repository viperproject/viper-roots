section \<open>Expression evaluation, well-definedness, inhale, total heap consistency\<close>

theory TotalExpressions
imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState TotalViperState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil TotalStateUtil
begin

subsection \<open>Heap-dependent function interpretation\<close>

type_synonym 'a heapfun_repr = "'a val list \<Rightarrow> 'a full_total_state \<rightharpoonup> 'a extended_val"
type_synonym 'a interp = "function_ident \<rightharpoonup> 'a heapfun_repr"

text \<open>\<^typ>\<open>'a heapfun_repr\<close> provides a semantic representation of heap-dependent functions. The possible outcomes
for \<^term>\<open>(f::'a heapfun_repr) vs \<omega>\<close> are 
\<^item> \<^term>\<open>None\<close>: There is a typing issue (e.g., \<^term>\<open>vs\<close> does not have the correct length or not the correct types)
\<^item> \<^term>\<open>Some VFailure\<close>: There is no typing issue, but the function applied to arguments \<^term>\<open>vs\<close> 
                       in state \<^term>\<open>\<omega>\<close> is ill-defined (i.e., \<^term>\<open>f\<close>'s  precondition is violated for arguments \<^term>\<open>vs\<close> 
                       in state \<^term>\<open>\<omega>\<close>).
\<^item> \<^term>\<open>Some (Val v)\<close>: There is no typing issue and the function call is well-defined. The resulting value is \<^term>\<open>v\<close>.
\<close>

subsection\<open>General auxiliary definitions\<close>

datatype 'a stmt_result_total = RMagic | RFailure | RNormal "'a full_total_state"

fun map_stmt_result_total :: "('a full_total_state \<Rightarrow> 'b full_total_state) \<Rightarrow> 'a stmt_result_total \<Rightarrow> 'b stmt_result_total"
  where
    "map_stmt_result_total f (RNormal \<omega>) = (RNormal (f \<omega>))"
  | "map_stmt_result_total f RMagic = RMagic"
  | "map_stmt_result_total f RFailure = RFailure"

inductive th_result_rel :: "bool \<Rightarrow> bool \<Rightarrow> ('a full_total_state) set \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"  where
  THResultNormal: "\<lbrakk> \<omega> \<in> W \<rbrakk> \<Longrightarrow> th_result_rel True True W (RNormal \<omega>)"
| THResultMagic: "th_result_rel True False W RMagic"
| THResultFailure: "th_result_rel False b W RFailure"

text \<open>\<^const>\<open>th_result_rel\<close> is an auxiliary relation that is useful to express a state in terms of 
conditions. \<^term>\<open>th_result_rel bSuccess bFeasible W res\<close> is used in the following way:

  \<^item> \<^term>\<open>bSuccess\<close> expresses when \<^term>\<open>res\<close> is not a failing state 
  \<^item> If \<^term>\<open>bSuccess\<close> holds (i.e., \<^term>\<open>res\<close> not a failing state), then 
    \<^term>\<open>bFeasible\<close> expresses when res is a normal state.
  \<^item> W expresses the set of possible normal states for \<^term>\<open>res\<close> if both \<^term>\<open>bSuccess\<close> and 
    \<^term>\<open>bFeasible\<close> hold.
\<close>

inductive_cases THResultNormal_case: "th_result_rel True True W (RNormal \<omega>)"
thm THResultNormal_case

lemma THResultNormal_alt: "\<lbrakk> \<omega> \<in> W; A; B\<rbrakk> \<Longrightarrow> th_result_rel A B W (RNormal \<omega>)"
  by (cases A; cases B) (auto intro: THResultNormal)

lemma th_result_rel_normal: 
  assumes "th_result_rel a b W (RNormal \<omega>)"
  shows "a \<and> b \<and> \<omega> \<in> W"
  using assms
  by (cases) auto

text \<open>\<^typ>\<open>'a stmt_result_total\<close> expresses the possible states for statements. \<close>


lemma th_result_rel_failure: 
  assumes "th_result_rel False b W res"
  shows "res = RFailure"
  using assms
  by (cases) auto

lemma th_result_rel_failure_2: 
  assumes "th_result_rel a b W RFailure"
  shows "\<not>a"
  using assms
  by (cases) auto

lemma th_result_rel_magic: 
  assumes "th_result_rel True False W res"
  shows "res = RMagic"
  using assms
  by (cases) auto

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {lh |lh. pgt (get_mh_total_full \<omega> lh) pnone}"

definition get_writeable_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_writeable_locs \<omega> = {lh |lh. (get_mh_total_full \<omega> lh) = pwrite}"

text \<open>If the evaluation of a subexpression fails, then the evaluation of the entire expression (or
atomic assertion) fails.
To avoid writing separate rules for every subexpression, we define auxiliary functions that capture
the direct subexpressions, which are evaluated in the same state as the parent expression.

Such auxiliary functions are also defined in the more abstract semantics (e.g., EquiSem). However, 
there are at least two differences to those functions:

 \<^item> In the semantics expressed here, the body of an \<^const>\<open>Unfolding\<close> expression must be evaluated in
   a separate state. In a more abstract semantics, this may not be the case.
 \<^item> In the semantics expressed here, the auxiliary subexpression functions return a list of expressions
   reflecting the order in which the expressions should be evaluated (instead of using a set). This
   leads to differences for ill-typed expressions.
\<close>

fun sub_pure_exp_total :: "pure_exp \<Rightarrow> pure_exp list" where
  "sub_pure_exp_total (Unop _ e) = [e]"
\<comment>\<open>the second expression of a binary expression might not be evaluated due to lazy binary operators\<close>
| "sub_pure_exp_total (Binop e _ _) = [e]"
| "sub_pure_exp_total (FieldAcc e _) = [e]"
| "sub_pure_exp_total (Let e _) = [e]"
| "sub_pure_exp_total (Perm e _) = [e]"
| "sub_pure_exp_total (CondExp e _ _) = [e]"
| "sub_pure_exp_total (PermPred _ exps) = exps"
| "sub_pure_exp_total (FunApp _ exps) = exps"
| "sub_pure_exp_total (Unfolding _ exps e) = exps"
| "sub_pure_exp_total _ = []"

fun sub_expressions_exp_or_wildcard :: "pure_exp exp_or_wildcard \<Rightarrow> pure_exp list" where
  "sub_expressions_exp_or_wildcard (PureExp e) = [e]"
| "sub_expressions_exp_or_wildcard Wildcard = []"

fun sub_expressions_atomic :: "pure_exp atomic_assert \<Rightarrow> pure_exp list" where
  "sub_expressions_atomic (Pure e) = [e]"
| "sub_expressions_atomic (Acc x f p) = x # sub_expressions_exp_or_wildcard p"
| "sub_expressions_atomic (AccPredicate P exps p) = exps @ sub_expressions_exp_or_wildcard p"

fun direct_sub_expressions_assertion :: "assertion \<Rightarrow> pure_exp list" where
  "direct_sub_expressions_assertion (Atomic A) = sub_expressions_atomic A"
| "direct_sub_expressions_assertion (Imp e A) = [e]"
| "direct_sub_expressions_assertion (CondAssert e A B) = [e]"
| "direct_sub_expressions_assertion _ = []"

subsection\<open>Auxiliary inhale definitions\<close>

text \<open>Construct the set of states that can be reached after inhaling a field permission.
      \<^term>\<open>R\<close> expresses when a state is consistent. If \<^term>\<open>p_opt = Some q\<close> then precisely \<^term>\<open>q\<close> 
      permission is added and otherwise the added permission is just required to be positive without
      any further constraints (useful to model adding wildcard permission).\<close>

definition inhale_perm_single :: "('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single R \<omega> lh p_opt =
      {\<omega>'| \<omega>' q. R \<omega>' \<and>
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mh_total_full \<omega> lh) q) \<and> \<comment>\<open>There can be at most 1 field permission\<close>
               \<omega>' = update_mh_loc_total_full \<omega> lh (padd (get_mh_total_full \<omega> lh) q)
       }"

lemma inhale_perm_single_nonempty:
  assumes "inhale_perm_single R \<omega> lh (Some p) \<noteq> {}"
  shows "inhale_perm_single R \<omega> lh (Some p) = {update_mh_loc_total_full \<omega> lh (padd (get_mh_total_full \<omega> lh) p)}"
  using assms
  unfolding inhale_perm_single_def
  by fastforce  

lemma inhale_perm_single_elem:
  assumes "\<omega>' = update_mh_loc_total_full \<omega> lh (padd (get_mh_total_full \<omega> lh) q)" and
          "R \<omega>'" and
          "option_fold ((=) q) (q \<noteq> pnone) p_opt" and
          "pgte pwrite (padd (get_mh_total_full \<omega> lh) q)"
        shows "\<omega>' \<in> inhale_perm_single R \<omega> lh p_opt"
  using assms
  unfolding inhale_perm_single_def
  by blast

text \<open>Construct the set of states that can be reached after inhaling a predicate permission.
      \<^term>\<open>p_opt\<close> plays the same role as in \<^const>\<open>inhale_perm_single\<close>\<close>

definition inhale_perm_single_pred :: "('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single_pred R \<omega> lp p_opt = 
      {\<omega>'| \<omega>' q. R \<omega>' \<and>  
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               \<omega>' = update_mp_loc_total_full \<omega> lp (padd (get_mp_total_full \<omega> lp) q)
       }"

lemma inhale_perm_single_pred_elem:
  assumes "\<omega>' = update_mp_loc_total_full \<omega> lp (padd (get_mp_total_full \<omega> lp) q)" and
          "R \<omega>'" and
          "option_fold ((=) q) (q \<noteq> pnone) p_opt"
        shows "\<omega>' \<in> inhale_perm_single_pred R \<omega> lp p_opt"
  using assms
  unfolding inhale_perm_single_pred_def
  by blast

subsection\<open>Main definitions for evaluation,  well-definedness, and inhale\<close>

record 'a total_context =
  program_total :: program
  fun_interp_total :: "'a interp"
  absval_interp_total :: "'a \<Rightarrow> abs_type"

text \<open>Expression evaluation, well-definedness of expressions and inhale are defined in a mutually
inductive way. The reason is that well-definedness uses inhale to express the well-definedness of 
unfolding expressions and inhale fails if some subexpression is not well-defined. Expression evaluation
itself without well-definedness checks could be defined independently. However, since expression evaluation
and well-definedness follow similar rules for many connectives, we decided to express them in the same
relation, where one uses one of the parameters to distinguish expression evaluation from well-definedness.

As part of this mutually inductive definition, we also define a relation that captures unfolding a
single a predicate in a state (via an inhale). This relation is used to define the well-definedness
of unfolding expressions.

Expression evaluation either results in a value or in a failure. Failure occurs if some operation is 
not defined (e.g., division by 0 and null dereference). Importantly, expression evaluation is defined
for all field accesses (with a non-null receiver), since the heap is total. 
Well-definedness is defined the same as expression evaluation, except that failure also occurs if
a field is accessed for which no permission is held in the mask.

All three relations (evaluation, well-definedness, inhale) take a unary relation \<^term>\<open>R\<close> on states 
as input.This relation represents when a state is consistent. Inhale progresses after adding new 
permission only if the resulting state is consistent.
\<close>

inductive red_pure_exp_total :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state option \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a extended_val \<Rightarrow> bool"
  ("_, _, _ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t _)" [51,51,51,0,51,51] 81) and
   red_pure_exps_total :: "'a total_context \<Rightarrow>  ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state option \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> (('a val) list) option \<Rightarrow> bool" and
   red_inhale :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool" and
   unfold_rel :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool"
  for ctxt :: "'a total_context" and R :: "'a full_total_state \<Rightarrow> bool"
  where

\<comment>\<open>Pure expression evaluation and well-definedness of pure expressions\<close>

\<comment>\<open>Atomic expressions\<close>
  RedLit: "ctxt, R, \<omega>_def \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l)"
| RedVar: "\<lbrakk> (get_store_total \<omega>) n = Some v \<rbrakk> \<Longrightarrow> ctxt, R, \<omega>_def \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedResult: "\<lbrakk> get_store_total \<omega> 0 = Some v \<rbrakk> \<Longrightarrow> ctxt, R, \<omega>_def \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

\<comment>\<open>Binop and Unop\<close>
| RedBinopLazy: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>\<Longrightarrow> 
    ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"                                                                        
| RedBinop: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; 
     ctxt, R, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; 
     eval_binop_lazy v1 bop = None; 
     eval_binop v1 bop v2 = BinopNormal v \<rbrakk> \<Longrightarrow> 
  ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinopRightFailure: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1; 
     ctxt, R, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure; 
     eval_binop_lazy v1 bop = None;
     \<comment>\<open>The following premise makes sure in this case that the binary operation does not reduce if
       e1 evaluates to a value that renders the binary operation ill-typed\<close>
     (\<exists> v2. eval_binop v1 bop v2 \<noteq> BinopTypeFailure)\<rbrakk> \<Longrightarrow> 
   ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopOpFailure: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1; 
     ctxt, R, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2; 
     eval_binop v1 bop v2 = BinopOpFailure; 
     eval_binop_lazy v1 bop = None \<rbrakk> \<Longrightarrow> 
  ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" \<comment>\<open>happens for division by 0, modulo 0\<close>

| RedUnop: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v; 
     eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow> 
  ctxt, R, \<omega>_def \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"

\<comment>\<open>Cond\<close>
| RedCondExpTrue: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) ; 
    ctxt, R, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow> 
    ctxt, R, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFalse: 
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) ; 
     ctxt, R, \<omega>_def \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow> 
   ctxt, R, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"

\<comment>\<open>Old\<close>
| RedOld: 
   "\<lbrakk> get_trace_total \<omega> l = Some \<phi> ; 
     \<omega>_def' = map_option (\<lambda>\<omega>_def_val. \<omega>_def_val\<lparr> get_total_full := \<phi> \<rparr>) \<omega>_def;                   
     ctxt, R, \<omega>_def' \<turnstile> \<langle>e; \<omega>\<lparr> get_total_full := \<phi> \<rparr>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow> 
     ctxt, R, \<omega>_def \<turnstile> \<langle>Old l e; \<omega>\<rangle> [\<Down>]\<^sub>t v"
 | RedOldFailure: 
   "\<lbrakk> get_trace_total \<omega> l = None \<rbrakk> \<Longrightarrow> 
    ctxt, R, \<omega>_def \<turnstile> \<langle>Old l e ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 

\<comment>\<open>Heap lookup\<close>
| RedField: 
   "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); 
      get_hh_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow> 
      ctxt, R, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t (if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) \<omega>_def) then Val v else VFailure)"
| RedFieldNullFailure:
   "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
       ctxt, R, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

\<comment>\<open>Permission introspection\<close>
| RedPermNull:
    "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
     ctxt, R, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
| RedPerm: 
   "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
      get_mh_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow> 
      ctxt, R, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal v))"

\<comment>\<open>Unfolding\<close> 
| RedUnfolding: "\<lbrakk> ctxt, R, None \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>   
     ctxt, R, None \<turnstile> \<langle>Unfolding p es ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v"
| RedUnfoldingDefNoPred:
   "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>_def) es \<omega> (Some vs);
     ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     \<not> (pgte (get_mp_total_full \<omega>_def (pred_id,vs)) pwrite) \<rbrakk> \<Longrightarrow> \<comment>\<open>insufficient perrmision\<close>
     ctxt, R, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedUnfoldingDef: 
   "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>_def) es \<omega> (Some vs);
     unfold_rel ctxt R p vs pwrite (get_total_full \<omega>_def) \<phi>'; 
     \<omega>'_def = \<omega>_def \<lparr> get_total_full := \<phi>' \<rparr>;
     ctxt, R, (Some \<omega>'_def) \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow>   
     ctxt, R, (Some \<omega>_def) \<turnstile> \<langle>Unfolding p es ubody ; \<omega>\<rangle> [\<Down>]\<^sub>t v"

\<comment>\<open>Important: \<^const>\<open>sub_pure_exp_total\<close> should not include the body of an unfolding\<close>
| RedSubFailure: 
   "\<lbrakk> (sub_pure_exp_total e') \<noteq> [];
     red_pure_exps_total ctxt R \<omega>_def (sub_pure_exp_total e') \<omega> None \<rbrakk> \<Longrightarrow> 
     ctxt, R, \<omega>_def \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

\<comment>\<open>List of expressions\<close>
| RedExpListCons:
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v; 
     red_pure_exps_total ctxt R \<omega>_def es \<omega> res;
     res' = map_option (\<lambda>vs. (v#vs)) res \<rbrakk> \<Longrightarrow>
     red_pure_exps_total ctxt R \<omega>_def (e#es) \<omega> res'"
| RedExpListFailure:
  "\<lbrakk> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
     red_pure_exps_total ctxt R \<omega>_def (e#es) \<omega> None"
| RedExpListNil:
  "red_pure_exps_total ctxt R \<omega>_def Nil \<omega> (Some Nil)"

\<comment>\<open>Atomic inhale\<close>
| InhAcc: 
    "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
       ctxt, R, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       W' = (if r = Null then {\<omega>} else inhale_perm_single R \<omega> (the_address r,f) (Some (Abs_preal p)));
       th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' res \<rbrakk> \<Longrightarrow>
       red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
| InhAccPred:
    "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
       ctxt, R, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);      
       W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) (Some (Abs_preal p));
       th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' res \<rbrakk> \<Longrightarrow>       
       red_inhale ctxt R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res"
| InhAccWildcard: 
    "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       W' = inhale_perm_single R \<omega> (the_address r,f) None;
       th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<rbrakk> \<Longrightarrow>
       red_inhale ctxt R (Atomic (Acc e_r f Wildcard)) \<omega> res"
| InhAccPredWildcard: 
    "\<lbrakk> red_pure_exps_total ctxt R (Some \<omega>) e_args \<omega> (Some v_args);
       W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) None;
       th_result_rel True (W' \<noteq> {}) W' res \<rbrakk> \<Longrightarrow>
       red_inhale ctxt R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res"
| InhPure: 
    "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
      red_inhale ctxt R (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"

\<comment>\<open>Connectives inhale\<close>
| InhStarNormal: 
   "\<lbrakk> red_inhale ctxt R A \<omega> (RNormal \<omega>''); 
      red_inhale ctxt R B \<omega>'' res\<rbrakk> \<Longrightarrow>
      red_inhale ctxt R (A && B) \<omega> res"
| InhStarFailureMagic:
   "\<lbrakk> red_inhale ctxt R A \<omega> resA; 
      resA = RFailure \<or> resA = RMagic \<rbrakk> \<Longrightarrow>
      red_inhale ctxt R (A && B) \<omega> resA"
| InhImpTrue:
 "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)); 
    red_inhale ctxt R A \<omega> res \<rbrakk> \<Longrightarrow>
    red_inhale ctxt R (Imp e A) \<omega> res"
| InhImpFalse:
 "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
    red_inhale ctxt R (Imp e A) \<omega> (RNormal \<omega>)"
| InhCondAssertTrue:
 "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)); 
    red_inhale ctxt R A \<omega> res \<rbrakk> \<Longrightarrow>
    red_inhale ctxt R (CondAssert e A B) \<omega> res"
| InhCondAssertFalse:
 "\<lbrakk> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
    red_inhale ctxt R B \<omega> res \<rbrakk> \<Longrightarrow> 
    red_inhale ctxt R (CondAssert e A B) \<omega> res"

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this result in failure.\<close>
| InhSubExpFailure: 
    "\<lbrakk> (direct_sub_expressions_assertion A) \<noteq> [];
       red_pure_exps_total ctxt R (Some \<omega>) (direct_sub_expressions_assertion A) \<omega> None \<rbrakk> \<Longrightarrow> 
       red_inhale ctxt R A \<omega> RFailure"

\<comment>\<open>unfold_rel\<close>
| UnfoldRelStep: 
    "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     m = get_mp_total \<phi>;
     pgte (m (pred_id,vs)) q;
     q \<noteq> pnone;
     m' = m( (pred_id,vs) := (m (pred_id,vs)) - q );
     \<omega> = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = update_mp_total \<phi> m' \<rparr>;
     red_inhale ctxt R (syntactic_mult (Rep_preal q) pred_body) \<omega> (RNormal \<omega>') \<rbrakk> \<Longrightarrow> 
     unfold_rel ctxt R pred_id vs q \<phi> (get_total_full \<omega>')"

lemmas red_exp_inhale_unfold_inducts = red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.inducts

subsection \<open>Elimination and introduction rules\<close>

lemmas red_exp_inhale_unfold_intros = red_pure_exp_total_red_pure_exps_total_red_inhale_unfold_rel.intros

subsubsection \<open>Expression evaluation and well-definedness\<close>

lemma RedField_no_def_normalI:
  assumes "ctxt, R, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v" 
    shows "ctxt, R, None \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (None :: ('a full_total_state) option)) then Val v else VFailure)"

  have "ctxt, R, None \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    by simp
qed

lemma RedField_def_normalI:
  assumes "ctxt, R, Some \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v"  
      and "(a,f) \<in> get_valid_locs \<omega>_def"
    shows "ctxt, R, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (Some \<omega>_def)) then Val v else VFailure)"

  have "ctxt, R, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    using assms
    by simp
qed

lemma RedField_def_failureI:
  assumes "ctxt, R, Some \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
      and "get_hh_total_full \<omega> (a, f) = v"  
      and "(a,f) \<notin> get_valid_locs \<omega>_def"
    shows "ctxt, R, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
proof -
  let ?res = "(if (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) (Some \<omega>_def)) then Val v else VFailure)"

  have "ctxt, R, Some \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t ?res"
    apply (rule RedField)
    using assms
    by auto

  thus ?thesis
    using assms
    by simp
qed

inductive_cases RedVar_case: "Pr, ctxt, \<omega>_def \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

lemma RedLit_case:
  assumes 
    "Pr, ctxt, \<omega>_def \<turnstile> \<langle>ELit l; \<omega>\<rangle> [\<Down>]\<^sub>t v" and
    "v = Val (val_of_lit l) \<Longrightarrow> P" 
  shows P
  using assms
  by (cases) auto

lemma RedFieldNormal_case:
  assumes "Pr, ctxt, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
          "\<And>a. Pr, ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<Longrightarrow>
           (if_Some (\<lambda>res. (a,f) \<in> get_valid_locs res) \<omega>_def) \<Longrightarrow>
           get_hh_total_full \<omega> (a, f) = v \<Longrightarrow>
             P"
        shows P
  using assms
  by cases (metis extended_val.distinct(1) extended_val.inject)

inductive_cases RedUnop_case: "ctxt, R, \<omega>_def \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
inductive_cases RedBinop_case: "ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
inductive_cases RedFunApp_case: "ctxt, R, \<omega>_def \<turnstile> \<langle>FunApp fname es; \<omega>\<rangle> [\<Down>]\<^sub>t res"

inductive_cases RedExpList_case: "red_pure_exps_total Pr ctxt LH es \<omega> (Some vs)"
inductive_cases RedExpListFailure_case: "red_pure_exps_total Pr ctxt LH es \<omega> None"
inductive_cases RedExpListGeneral_case: "red_pure_exps_total Pr ctxt LH es \<omega> res"

lemma red_exp_list_normal_elim: 
  assumes
     "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs)" and
     "(\<And>vs_hd vs_tl e_hd es_tl.       
        es = e_hd # es_tl \<Longrightarrow>
        vs = vs_hd # vs_tl \<Longrightarrow>
        ctxt, R, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t Val vs_hd \<Longrightarrow> red_pure_exps_total ctxt R \<omega>_def es_tl \<omega> (Some vs_tl) \<Longrightarrow> P)" and 
     "es = [] \<Longrightarrow> vs = [] \<Longrightarrow> P"
   shows "P"
  using assms
proof cases
  case (RedExpListCons e v es' res)
  from this obtain vs' where "res = Some vs'" and "vs = v#vs'"
    by (metis map_option_eq_Some)
  with RedExpListCons assms(2)[OF \<open>es = e#es'\<close> \<open>vs = _\<close> ]  show ?thesis
    by blast
next
  case RedExpListNil
  then show ?thesis using assms by auto
qed

lemma red_exp_list_failure_Nil:
  assumes "red_pure_exps_total ctxt_vpr StateCons \<omega>_def [] \<omega> res"
  shows "res = Some []"
  using assms
  by cases

lemma red_exp_list_failure_elim:
  assumes
     "red_pure_exps_total ctxt R \<omega>_def es \<omega> None" and
     "(\<And>v e_hd es_tl.
        es = e_hd # es_tl \<Longrightarrow>
        ctxt, R, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<Longrightarrow> 
        es_tl \<noteq> [] \<Longrightarrow>
        red_pure_exps_total ctxt R \<omega>_def es_tl \<omega> None \<Longrightarrow> P)" and
     "(\<And>e_hd es_tl.
        es = e_hd # es_tl \<Longrightarrow>
        ctxt, R, \<omega>_def \<turnstile> \<langle>e_hd;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P)"
   shows "P"
  using assms    
  by (cases) (auto elim: RedExpListFailure_case)

lemma red_exp_list_failure_nth:
  assumes "red_pure_exps_total ctxt R \<omega>_def es \<omega> None" and 
          "es \<noteq> []"
  shows "\<exists>i. i < length es \<and> ctxt, R, \<omega>_def \<turnstile> \<langle>es ! i;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  using assms
proof (induction es)
  case Nil
  then show ?case by simp \<comment>\<open>contradiction\<close>
next
  case (Cons a es)
  thus ?case 
    by (fastforce elim: red_exp_list_failure_elim dest!: Cons.IH)  
qed

inductive_cases RedPerm_case: "ctxt, R, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

lemma red_pure_exps_total_singleton:
  assumes "red_pure_exps_total ctxt R \<omega>_def [e] \<omega> res" and
          "\<And>v. res = Some [v] \<and> (ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<Longrightarrow> P" and
          "res = None \<Longrightarrow> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P"
  shows P
  apply (rule RedExpListGeneral_case[OF assms(1)])
  using RedExpListGeneral_case assms(2) apply blast
   apply (simp add: assms(3))
  apply simp
  done

lemmas red_pure_exp_total_elims = 
  RedLit_case RedVar_case
  RedUnop_case RedBinop_case RedFunApp_case  
  red_exp_list_normal_elim red_exp_list_failure_elim

lemma red_pure_exps_total_append_failure:
  assumes "red_pure_exps_total ctxt R \<omega>_def es \<omega> None"
  shows "red_pure_exps_total ctxt R \<omega>_def (es@es') \<omega> None"
  using assms
proof (induction es)
  case Nil
  then show ?case 
    using red_exp_list_failure_Nil
    by blast    
next
  case (Cons e es)
  then show ?case 
    by (auto elim: red_exp_list_failure_elim intro: red_exp_inhale_unfold_intros)
qed

lemma red_pure_exps_total_append_failure_2:
  assumes "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs)"
      and "red_pure_exps_total ctxt R \<omega>_def es' \<omega> None"
    shows "red_pure_exps_total ctxt R \<omega>_def (es@es') \<omega> None"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  from this obtain v vs_tl where 
     "vs = v#vs_tl" and
     RedE: "ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
     "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs_tl)"
  by (auto elim: red_pure_exp_total_elims)
      
  then have "red_pure_exps_total ctxt R \<omega>_def (es @ es') \<omega> None"
    using Cons
    by blast

  thus ?case
    using RedE
    by (auto intro: red_exp_inhale_unfold_intros) 
qed

subsubsection \<open>Inhale\<close>

lemma inh_imp_failure:
  assumes "ctxt, R, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt R (Imp e A) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="Imp e A"] RedExpListFailure
  by fastforce

lemma inh_cond_assert_failure:
  assumes "ctxt, R, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "red_inhale ctxt R (CondAssert e A B) \<omega> RFailure"
  using assms InhSubExpFailure[where ?A="CondAssert e A B"] RedExpListFailure
  by fastforce

lemma inh_pure_normal:
  assumes "ctxt, R, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
  shows "red_inhale ctxt R (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using assms InhPure
  by force

lemma inh_pure_magic:
  assumes "ctxt, R, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  shows "red_inhale ctxt R (Atomic (Pure e)) \<omega> RMagic"
  using assms InhPure
  by force

lemmas red_inhale_intros = 
  InhAcc 
  InhAccPred 
  InhAccWildcard 
  InhAccPredWildcard 
  inh_pure_normal
  inh_pure_magic
  InhStarNormal 
  InhStarFailureMagic
  InhImpTrue
  InhImpFalse 
  InhCondAssertTrue
  InhCondAssertFalse
  InhSubExpFailure

inductive_cases InhStar_case: "red_inhale ctxt R (A && B) \<omega> res"
inductive_cases InhImp_case: "red_inhale ctxt R (Imp e A) \<omega> res"
inductive_cases InhPure_case: "red_inhale ctxt R (Atomic (Pure e)) \<omega> res"
thm InhPure_case

lemmas red_inhale_elims = 
  InhStar_case
  InhImp_case
  InhPure_case

subsection \<open>Helper lemmas\<close>

lemma red_pure_exps_total_list_all2:
  assumes "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs)"
  shows "list_all2 (\<lambda>e v. red_pure_exp_total ctxt R  \<omega>_def e \<omega> (Val v)) es vs"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case 
    by (auto elim: red_pure_exp_total_elims)
next
  case (Cons e es)
  from this obtain vs_hd vs_tail where 
     "vs = vs_hd # vs_tail" and
     "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val vs_hd" and
     "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs_tail)"
     by (auto elim: red_exp_list_normal_elim)
  with Cons.IH show ?case
    by blast
qed

lemma red_pure_exps_total_Some_lengthD: 
  assumes "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some v_args)"
  shows "length es = length v_args"
proof -
  from red_pure_exps_total_list_all2[OF assms]
  show ?thesis
    by (simp add: list_all2_lengthD)
qed

lemma list_all2_red_pure_exps_total:
  assumes "list_all2 (\<lambda>e v. red_pure_exp_total ctxt R \<omega>_def e \<omega> (Val v)) es vs"
  shows "red_pure_exps_total ctxt R \<omega>_def es \<omega> (Some vs)"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case 
    by (auto intro: red_exp_inhale_unfold_intros)
next
  case (Cons e es)
  from this obtain vs_hd vs_tail where 
     "vs = vs_hd # vs_tail" and
     "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val vs_hd" and
     "list_all2 (\<lambda>e v. ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) es vs_tail"
    by (metis (no_types, lifting) list_all2_Cons1)
  with Cons.IH show ?case
    unfolding \<open>vs = _\<close>
    using option.simps(9) red_pure_exps_total.simps 
    by fastforce
qed

subsection \<open>Total heap consistency\<close>

definition unfold_rel_general :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool"
  where "unfold_rel_general ctxt R \<omega> \<omega>' \<equiv> \<exists> pred_id vs q. unfold_rel ctxt R pred_id vs q \<omega> \<omega>'"

definition unfold_rel_multi :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow>'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool"
  where "unfold_rel_multi ctxt R  \<equiv> rtranclp (unfold_rel_general ctxt R)"

text \<open>Expression evaluation as a function. Using this function makes sense, when it is known that 
e is well-defined and is deterministic (for example, if e is the body of a predicate).\<close>

fun red_pure_exp_total_fun :: "'a total_context \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a val"
  where "red_pure_exp_total_fun ctxt e \<omega> = (SOME v. ctxt, (\<lambda>_. True), None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"

fun red_pure_exps_total_fun :: "'a total_context \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> ('a val) list"
  where "red_pure_exps_total_fun ctxt es \<omega> = (SOME vs. red_pure_exps_total ctxt (\<lambda>_. True)  None es \<omega> (Some vs))"

(* TODO: duplicate? *)
fun extract_address_from_val :: "'a val \<Rightarrow> address"
  where 
    "extract_address_from_val (VRef (Address a)) = a"
  | "extract_address_from_val _ = undefined"

(* TODO: duplicate? *)
fun extract_perm_from_val :: "'a val \<Rightarrow> real"
  where 
    "extract_perm_from_val (VPerm r) = r"
  | "extract_perm_from_val _ = undefined"

fun is_positive_permission :: "'a total_context \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where 
    "is_positive_permission ctxt Wildcard \<omega> = True"
  | "is_positive_permission ctxt (PureExp e) \<omega> = (extract_perm_from_val (red_pure_exp_total_fun ctxt e \<omega>) > 0)"


fun assertion_heap_snapshot :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> heap_loc set"
  where 
   "assertion_heap_snapshot ctxt (Atomic (Pure e)) \<omega> = {}"
 | "assertion_heap_snapshot ctxt (Atomic (Acc e f e_p)) \<omega> = 
             (if is_positive_permission ctxt e_p \<omega> then 
                  {(extract_address_from_val (red_pure_exp_total_fun ctxt e \<omega>), f)} 
              else {})"
 | "assertion_heap_snapshot ctxt (Atomic (AccPredicate pred_id e_args e_p)) \<omega> = 
             (if is_positive_permission ctxt e_p \<omega> then
                fst (get_hp_total_full \<omega> (pred_id, red_pure_exps_total_fun ctxt e_args \<omega>))
              else {})"
 | "assertion_heap_snapshot ctxt (Imp e A) \<omega> =
             (if red_pure_exp_total_fun ctxt e \<omega> = VBool True then 
                 assertion_heap_snapshot ctxt A \<omega> 
              else {})"
 | "assertion_heap_snapshot ctxt (A && B) \<omega> = assertion_heap_snapshot ctxt A \<omega> \<union> assertion_heap_snapshot ctxt B \<omega>"      
 | "assertion_heap_snapshot ctxt _ \<omega> = undefined" (* wands and quantified permissions not supported *)

fun assertion_predicate_snapshot :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc set"
  where 
   "assertion_predicate_snapshot ctxt (Atomic (Pure e)) \<omega> = {}"
 | "assertion_predicate_snapshot ctxt (Atomic (Acc e f e_p)) \<omega> = {}"
 | "assertion_predicate_snapshot ctxt (Atomic (AccPredicate pred_id e_args e_p)) \<omega> = 
             (if is_positive_permission ctxt e_p \<omega> then
                {(pred_id, red_pure_exps_total_fun ctxt e_args \<omega>)} \<union> 
                snd (get_hp_total_full \<omega> (pred_id, red_pure_exps_total_fun ctxt e_args \<omega>))
              else {})"
 | "assertion_predicate_snapshot ctxt (Imp e A) \<omega> =
             (if red_pure_exp_total_fun ctxt e \<omega> = VBool True then 
                 assertion_predicate_snapshot ctxt A \<omega> 
              else {})"
 | "assertion_predicate_snapshot ctxt (A && B) \<omega> = assertion_predicate_snapshot ctxt A \<omega> \<union> assertion_predicate_snapshot ctxt B \<omega>"      
 | "assertion_predicate_snapshot ctxt _ \<omega> = undefined" (* wands and quantified permissions not supported *)


(* TODO: Should the state track the predicate heap explicitly? *)
definition pheap_consistent :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
 "pheap_consistent ctxt \<omega> \<equiv> 
    \<forall> pred_id vs pred_decl. 
         (pgt (get_mp_total_full \<omega> (pred_id,vs)) pnone \<and> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl) \<longrightarrow>
          option_fold (\<lambda> pred_body. get_hp_total_full \<omega> (pred_id, vs) = 
                        (assertion_heap_snapshot ctxt pred_body (update_store_total \<omega> (nth_option vs)), assertion_predicate_snapshot ctxt pred_body (update_store_total \<omega> (nth_option vs))) )
                      True
                      (ViperLang.predicate_decl.body pred_decl)"

\<comment>\<open>alternative with pheap:
inductive total_heap_consistent :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  for ctxt :: "'a total_context"
  where 
  \<comment>\<open>If a state does contain any permission to non-abstract predicates, then the state is trivially consistent.\<close>
  ConsistentNoPred: 
  " \<lbrakk> \<And> pred_id vs. option_fold (\<lambda>decl. ViperLang.predicate_decl.body decl) None (ViperLang.predicates (program_total ctxt) pred_id) \<noteq> None \<Longrightarrow>
                    get_mp_total_full \<omega> (pred_id,vs) = pnone \<rbrakk> \<Longrightarrow> 
                    total_heap_consistent ctxt \<omega>"
  \<comment>\<open>If a state contains permission to a non-abstract predicate, then the state is consistent if some such non-abstract predicate
     can be completely unfolded to reach another consistent state\<close>
| UnfoldStep: "\<lbrakk> option_fold (\<lambda>decl. ViperLang.predicate_decl.body decl) None (ViperLang.predicates (program_total ctxt) pred_id) \<noteq> None;
                 q = (get_mp_total_full \<omega> (pred_id,vs));
                 pgt p pnone;
                 \<exists>\<omega>'. unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<omega> \<omega>' \<and> total_heap_consistent ctxt \<omega>';
                 pheap_consistent ctxt \<omega> \<rbrakk> \<Longrightarrow>
                 total_heap_consistent ctxt \<omega>"
\<close>

inductive total_heap_consistent_wrt_mask :: "'a total_context \<Rightarrow> preal mask \<times> 'a predicate_mask \<Rightarrow> 'a total_state \<Rightarrow> bool"
  for ctxt :: "'a total_context" and m :: "preal mask \<times> 'a predicate_mask"
  where 
  \<comment>\<open>If a state does contain any permission to non-abstract predicates, then the state is trivially consistent.\<close>
  ConsistentNoPred: 
  " \<lbrakk> get_m_total_full \<omega> = m;
      valid_heap_mask (fst m);
      \<And> pred_id vs. option_fold (\<lambda>decl. ViperLang.predicate_decl.body decl) None (ViperLang.predicates (program_total ctxt) pred_id) \<noteq> None \<Longrightarrow>
                    get_mp_total \<phi> (pred_id,vs) = pnone \<rbrakk> \<Longrightarrow> 
      total_heap_consistent_wrt_mask ctxt m \<phi>"
  \<comment>\<open>If a state contains permission to a non-abstract predicate, then the state is consistent if some such non-abstract predicate
     can be completely unfolded to reach another consistent state\<close>
| UnfoldStep: 
   "\<lbrakk> option_fold (\<lambda>decl. ViperLang.predicate_decl.body decl) None (ViperLang.predicates (program_total ctxt) pred_id) \<noteq> None;
      q = (get_mp_total \<phi> (pred_id,vs));
      pgt q pnone;
      \<exists>\<phi>'. unfold_rel ctxt (\<lambda>_. True) pred_id vs q \<phi> \<phi>' \<and> total_heap_consistent_wrt_mask ctxt m \<phi>'
      \<comment>\<open>ignore predicate heaps for now \<^term>\<open>pheap_consistent ctxt \<omega>\<close>\<close> 
    \<rbrakk> \<Longrightarrow>
    total_heap_consistent_wrt_mask ctxt m \<phi>"

definition total_heap_consistent :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "total_heap_consistent ctxt \<omega> \<equiv> (\<exists>m. total_heap_consistent_wrt_mask ctxt m (get_total_full \<omega>)) \<and>
                                         (\<forall>l \<phi>. get_trace_total \<omega> l = Some \<phi> \<longrightarrow> (\<exists>m. total_heap_consistent_wrt_mask ctxt m \<phi>))"

abbreviation red_inhale_th_cons :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a stmt_result_total \<Rightarrow> bool"
  where "red_inhale_th_cons ctxt A \<omega> res \<equiv> red_inhale ctxt (total_heap_consistent ctxt) A \<omega> res"

text \<open>\<^const>\<open>red_inhale_th_cons\<close> only takes transitions to total heap consistent states whenever some 
permission is inhaled\<close>

definition assertion_framing_state :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
    "assertion_framing_state ctxt StateCons A \<omega> \<equiv> 
      \<forall> res. red_inhale ctxt StateCons A \<omega> res \<longrightarrow> res \<noteq> RFailure"

definition assertion_self_framing_store :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a store \<Rightarrow> bool"
  where
    "assertion_self_framing_store ctxt StateCons A \<sigma> \<equiv> 
      \<forall> \<omega>. assertion_framing_state ctxt StateCons A (update_store_total \<omega> \<sigma>)"

lemma assertion_framing_star: 
  assumes "assertion_framing_state ctxt StateCons (A1 && A2) \<omega>" 
  shows "assertion_framing_state ctxt StateCons A1 \<omega> \<and> 
        (\<forall> \<omega>'. red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>') \<longrightarrow> assertion_framing_state ctxt StateCons A2 \<omega>')" (is "?Goal1 \<and> ?Goal2")
proof 
  show "assertion_framing_state ctxt StateCons A1 \<omega>"
    unfolding assertion_framing_state_def
  proof (rule allI | rule impI)+
    fix res
    assume "red_inhale ctxt StateCons A1 \<omega> res"

    thus "res \<noteq> RFailure"
      using assms InhStarFailureMagic assertion_framing_state_def
      by blast
  qed
next
  show ?Goal2
  proof (rule allI | rule impI)+
    fix \<omega>' 
    assume InhA1: "red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>')"
    show "assertion_framing_state ctxt StateCons A2 \<omega>'"
      unfolding assertion_framing_state_def
      using InhA1 InhStarNormal assertion_framing_state_def assms by blast
  qed
qed

lemma assertion_framing_imp: 
  assumes "assertion_framing_state ctxt StateCons (Imp e A) \<omega>"
     and "ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"  
   shows "assertion_framing_state ctxt StateCons A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhImpTrue)

lemma assertion_framing_cond_assert_true:
  assumes "assertion_framing_state ctxt StateCons (CondAssert e A B) \<omega>"
      and "ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"
    shows "assertion_framing_state ctxt StateCons A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertTrue)

lemma assertion_framing_cond_assert_false:
  assumes "assertion_framing_state ctxt StateCons (CondAssert e A B) \<omega>"
      and "ctxt, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool False))"
    shows "assertion_framing_state ctxt StateCons B \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertFalse)

end