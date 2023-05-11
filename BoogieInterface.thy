theory BoogieInterface
imports Boogie_Lang.Ast
begin

subsection \<open>Expressions\<close>

record 'a econtext_bpl_general =
  type_interp :: "'a  absval_ty_fun"
  var_context :: var_context
  fun_interp :: "'a fun_interp"

abbreviation create_ctxt_bpl :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> 'a econtext_bpl_general"
  where "create_ctxt_bpl A \<Lambda> \<Gamma> \<equiv> \<lparr>type_interp=A, var_context=\<Lambda>,fun_interp=\<Gamma>\<rparr>"

abbreviation red_expr_bpl :: "'a econtext_bpl_general \<Rightarrow> expr \<Rightarrow> 'a nstate \<Rightarrow> 'a val \<Rightarrow> bool"
  where "red_expr_bpl ctxt e ns v \<equiv> type_interp ctxt, var_context ctxt, fun_interp ctxt, [] \<turnstile> \<langle>e, ns\<rangle> \<Down> v"   

subsection \<open>Ast\<close>

type_synonym ast_bpl = Ast.ast

text \<open>AST transitive closure relation. We make sure simple commands step take one step at a time\<close>

abbreviation empty_bigblock :: "string option \<Rightarrow> bigblock"
  where "empty_bigblock name \<equiv> BigBlock name [] None None"

fun is_empty_bigblock :: "bigblock \<Rightarrow> bool"
  where 
    "is_empty_bigblock (BigBlock _ [] None None) = True"
  | "is_empty_bigblock _ = False"

abbreviation if_bigblock :: "string option \<Rightarrow> expr option \<Rightarrow> bigblock list \<Rightarrow> bigblock list \<Rightarrow> bigblock"
  where 
    "if_bigblock name_opt cond_opt thn_list els_list \<equiv> 
       BigBlock name_opt [] (Some (ParsedIf cond_opt thn_list els_list)) None"

type_synonym 'a vast_config_general = "(bigblock * cont) * 'a state"

text \<open>
 We define a single step relation on big blocks based on \<^const>\<open>red_bigblock\<close>, where only a single 
simple command reduces in a single step (contrary to \<^const>\<open>red_bigblock\<close>, where all simple commands 
of the same big block reduce in a single step).
\<close>
inductive red_bigblock_small :: "ast \<Rightarrow> 'a econtext_bpl_general \<Rightarrow> 'a vast_config_general \<Rightarrow> 'a vast_config_general \<Rightarrow> bool"
  for P ctxt
  where 
    RedBigBlockSmallSimpleCmd [intro]: 
      "\<lbrakk> (type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), [] \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s' \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt (((BigBlock name (c#cs) str tr), cont), s) (((BigBlock name cs str tr), cont), s')"
   | RedBigBlockSmallNoSimpleCmdOneStep [intro]: 
    "\<lbrakk> red_bigblock (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) [] P (BigBlock name [] str tr, cont, s) (b', cont', s') \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt ((BigBlock name [] str tr, cont), s) ((b', cont'), s')"

abbreviation red_bigblock_small_multi :: "ast \<Rightarrow> 'a econtext_bpl_general \<Rightarrow> 'a vast_config_general \<Rightarrow> 'a vast_config_general \<Rightarrow> bool"
  where "red_bigblock_small_multi P ctxt \<equiv> rtranclp (red_bigblock_small P ctxt)"

text \<open>We order the arguments of an AST config such that the syntactic part (bigblock + continuation) is the 
first element s.t. one can easily construct an AST configuration from the syntactic part and the state\<close>                                                                                                                                 

definition red_ast_bpl :: "ast \<Rightarrow> 'a econtext_bpl_general \<Rightarrow>'a vast_config_general \<Rightarrow> 'a vast_config_general \<Rightarrow> bool"
  where "red_ast_bpl ctxt \<equiv> red_bigblock_small_multi ctxt"

lemma red_ast_bpl_refl: "red_ast_bpl P ctxt \<gamma> \<gamma>"
  by (simp add: red_ast_bpl_def)

lemma red_ast_bpl_transitive:
  assumes "red_ast_bpl P ctxt \<gamma>1 \<gamma>2" and
          "red_ast_bpl P ctxt \<gamma>2 \<gamma>3"
  shows "red_ast_bpl P ctxt \<gamma>1 \<gamma>3"
  using assms 
  unfolding red_ast_bpl_def
  by fastforce

lemma red_ast_bpl_one_simple_cmd:
  assumes "(type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), [] \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s'"
  shows "red_ast_bpl P ctxt ((BigBlock name (c#cs) str tr, cont), s) ((BigBlock name cs str tr, cont), s')"
  using assms
  unfolding red_ast_bpl_def
  by blast

lemma red_ast_bpl_one_step_empty_simple_cmd:
  assumes "(type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), [], P \<turnstile> 
             \<langle>(BigBlock name [] str tr, cont, s)\<rangle> \<longrightarrow> (b', cont', s')"
  shows "red_ast_bpl P ctxt ((BigBlock name [] str tr, cont), s) ((b', cont'), s')"
  using assms
  unfolding red_ast_bpl_def
  by blast
 
lemma red_ast_bpl_empty_block: "red_ast_bpl P ctxt ((BigBlock name [] None None, KSeq b cont), Normal ns) ((b, cont), Normal ns)"
  unfolding red_ast_bpl_def
  by (fastforce intro: RedSkip)

lemma red_ast_bpl_empty_block_2: 
  assumes "is_empty_bigblock empty_block"
  shows "red_ast_bpl P ctxt ((empty_block, KSeq b cont), Normal ns) ((b, cont), Normal ns)"
  using assms red_ast_bpl_empty_block
  by (metis is_empty_bigblock.elims(2))

lemma red_ast_bpl_empty_else:
  assumes CondFalse: "red_expr_bpl ctxt cond_bpl ns (BoolV False)" and
          EmptyElse: "is_empty_bigblock empty_else_block"
  shows "red_ast_bpl P ctxt ((if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont), Normal ns) 
                            ((next, cont), Normal ns)"
proof -
  from EmptyElse obtain name where "empty_else_block = empty_bigblock name"
    by (auto elim: is_empty_bigblock.elims)
  show ?thesis    
    apply (rule red_ast_bpl_transitive)
     apply (fastforce intro!: red_ast_bpl_one_step_empty_simple_cmd RedParsedIfFalse simp: CondFalse \<open>empty_else_block = _\<close>)
    by (fastforce intro!: red_ast_bpl_one_step_empty_simple_cmd RedSkip)
qed 

subsection \<open>Reducing Boogie programs while preserving a property\<close>

lemma red_ast_bpl_propagate_rel:
  assumes "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1)" and
          "R1 \<omega> ns1" and
          "R1 \<omega> ns1 \<Longrightarrow> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2) \<and> R2 \<omega> ns2"
        shows "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>2, Normal ns2) \<and> R2 \<omega> ns2"
  using assms
  unfolding red_ast_bpl_def
  by auto

lemma red_ast_bpl_propagate_same_rel:
    assumes "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1)" and
          "R \<omega> ns1" and
          "R \<omega> ns1 \<Longrightarrow> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2) \<and> R \<omega> ns2"
        shows "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>2, Normal ns2) \<and> R \<omega> ns2"
  using assms
  unfolding red_ast_bpl_def
  by auto

\<comment>\<open>TODO: Should use a definition for \<^term>\<open>\<exists>ns1. red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1) \<and> Q1 ns1\<close>\<close>

lemma red_ast_bpl_propagate_transitive:
  assumes "\<exists>ns1. red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1) \<and> Q1 ns1" and
          "\<And>ns1. Q1 ns1 \<Longrightarrow> \<exists>ns2. red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2) \<and> Q2 ns2"
        shows "\<exists>ns2. red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>2, Normal ns2) \<and> Q2 ns2"
  using assms red_ast_bpl_transitive by blast

subsection \<open>Single step lemmas for concrete simple commands\<close>

lemma red_ast_bpl_one_assert:
  assumes "red_expr_bpl ctxt e ns (BoolV b)" and
          "s' = (if b then Normal ns else Failure)" 
  shows "red_ast_bpl P ctxt ((BigBlock name (Assert e#cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), s')"
  apply (rule red_ast_bpl_one_simple_cmd)
  using assms
  by (auto intro: RedAssertOk RedAssertFail)

lemma red_ast_bpl_one_assume:
  assumes "red_expr_bpl ctxt e ns (BoolV b)" and
          "s' = (if b then Normal ns else Magic)"
  shows "red_ast_bpl P ctxt ((BigBlock name (Assume e#cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), s')"
  apply (rule red_ast_bpl_one_simple_cmd)
  using assms
  by (auto intro: RedAssumeOk RedAssumeMagic)

lemma red_ast_bpl_one_assign:
  assumes "lookup_var_ty (var_context ctxt) x = Some ty" and
          "red_expr_bpl ctxt e ns v" and
          "type_of_val (type_interp ctxt) v = instantiate [] ty"
  shows "red_ast_bpl P ctxt ((BigBlock name (Assign x e#cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), Normal (update_var (var_context ctxt) ns x v))"
  apply (rule red_ast_bpl_one_simple_cmd)
  using assms
  by (auto intro: RedAssign)

lemma red_ast_bpl_havoc_assume:
assumes "lookup_var_decl (var_context ctxt) x = Some (ty,w)" and
        "type_of_val (type_interp ctxt) v = instantiate [] ty" and
        "\<And>cond. w = Some cond \<Longrightarrow> red_expr_bpl ctxt cond (update_var (var_context ctxt) ns x v) (BoolV True)" and
        "red_expr_bpl ctxt e (update_var (var_context ctxt) ns x v) (BoolV True)"
shows "red_ast_bpl P ctxt ((BigBlock name (Havoc x # Assume e # cs) str tr, cont), Normal ns) 
                            ((BigBlock name cs str tr, cont) , Normal (update_var (var_context ctxt) ns x v))"
  apply (rule red_ast_bpl_transitive)
   apply (rule red_ast_bpl_one_simple_cmd)
  using assms
   apply (fastforce intro: RedHavocNormal)
   apply (rule red_ast_bpl_one_simple_cmd)
  using assms(4) RedAssumeOk
  by blast

subsection \<open>Misc\<close>

lemma proc_is_correct_elim:
  assumes 
     "proc_is_correct A fun_decls constants global_vars axioms proc proc_body_satisfies_spec_general" and
     "proc_body proc = Some (locals, p_body)" and
     "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)" and
     "\<forall>v. closed ((type_of_val A) v)" and
     "fun_interp_wf A fun_decls \<Gamma>" and
     "(list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc)" and
     "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
     "state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc))" and
     "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
shows 
  "(proc_body_satisfies_spec_general 
                                        A [] (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc) (proc_checked_posts proc) p_body
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> )"
  using assms
  by fastforce

lemma closed_wf_ty_eq: "closed \<tau> = wf_ty 0 \<tau>"
proof (induction \<tau>)
  case (TCon tid args)
  show ?case 
  proof 
    assume "wf_ty 0 (TCon tid args)"
    hence "list_all (wf_ty 0) args"
      by simp
    hence "list_all closed args"
      using TCon.IH list_all_cong
      by blast
    thus "closed (TCon tid args)"
      by simp
  next
    assume "closed (TCon tid args)"
    hence "list_all closed args"
      by simp
    hence "list_all (wf_ty 0) args"
      using TCon.IH list_all_cong
      by blast
    thus "wf_ty 0 (TCon tid args)"
      by simp
  qed
qed auto

lemma closed_wf_ty_fun_eq: "closed = wf_ty 0"
  using closed_wf_ty_eq
  by presburger

end