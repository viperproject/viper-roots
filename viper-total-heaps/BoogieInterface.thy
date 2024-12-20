theory BoogieInterface
imports Boogie_Lang.Ast TotalUtil
begin

subsection \<open>Expressions\<close>

record 'a econtext_bpl_general =
  type_interp :: "'a  absval_ty_fun"
  var_context :: var_context
  fun_interp :: "'a fun_interp"
  rtype_interp :: "rtype_env"

abbreviation create_ctxt_bpl :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> 'a econtext_bpl_general"
  where "create_ctxt_bpl A \<Lambda> \<Gamma> \<equiv> \<lparr>type_interp=A, var_context=\<Lambda>,fun_interp=\<Gamma>,rtype_interp=[]\<rparr>"

abbreviation red_expr_bpl :: "'a econtext_bpl_general \<Rightarrow> expr \<Rightarrow> 'a nstate \<Rightarrow> 'a val \<Rightarrow> bool"
  where "red_expr_bpl ctxt e ns v \<equiv> type_interp ctxt, var_context ctxt, fun_interp ctxt, rtype_interp ctxt \<turnstile> \<langle>e, ns\<rangle> \<Down> v"   

subsubsection \<open>Type Safety Lemmas\<close>

corollary type_safety_top_level_two_expressions_same_type:
  assumes Wf_\<Gamma>:"fun_interp_wf A F \<Gamma>" and
          Wf_F:"list_all (wf_fdecl \<circ> snd) F" and
          Wf_\<Lambda>: "\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow> wf_ty 0 \<tau>" and
          "state_well_typed A \<Lambda> [] n_s" and
          "wf_expr 0 e1 \<and> wf_expr 0 e2" and
          "F, (lookup_var_ty \<Lambda>, Map.empty) \<turnstile> e1 : \<tau>" and
          "F, (lookup_var_ty \<Lambda>, Map.empty) \<turnstile> e2 : \<tau>"
        shows "\<exists>v1 v2. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1) \<and> (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2) \<and> type_of_val A v1 = type_of_val A v2"
proof -
  let ?\<Delta> = "(lookup_var_ty \<Lambda>, Map.empty)"
  have "\<exists>v. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate [] \<tau>" 
    apply (rule type_safety_top_level)
    using assms
    by auto
  moreover have "\<exists>v. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate [] \<tau>"
    apply (rule type_safety_top_level)
    using assms
    by auto
  ultimately show ?thesis
    by metis
qed

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
      "\<lbrakk> (type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), (rtype_interp ctxt) \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s' \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt (((BigBlock name (c#cs) str tr), cont), s) (((BigBlock name cs str tr), cont), s')"
   | RedBigBlockSmallNoSimpleCmdOneStep [intro]: 
    "\<lbrakk> red_bigblock (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) (rtype_interp ctxt) P (BigBlock name [] str tr, cont, s) (b', cont', s') \<rbrakk> \<Longrightarrow>
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
  assumes "(type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), rtype_interp ctxt \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s'"
  shows "red_ast_bpl P ctxt ((BigBlock name (c#cs) str tr, cont), s) ((BigBlock name cs str tr, cont), s')"
  using assms
  unfolding red_ast_bpl_def
  by blast

lemma red_ast_bpl_one_step_empty_simple_cmd:
  assumes "(type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), rtype_interp ctxt, P \<turnstile> 
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

lemma red_ast_bpl_if_nondet_then:
  shows "red_ast_bpl P ctxt ((if_bigblock name None (thn_hd # thn_tl) els, KSeq next cont), Normal ns) 
                            ((thn_hd, convert_list_to_cont thn_tl (KSeq next cont)), Normal ns)"
  apply (rule red_ast_bpl_one_step_empty_simple_cmd)
  apply (rule RedParsedIfTrue)
  by simp

lemma red_ast_bpl_if_nondet_else:
  shows "red_ast_bpl P ctxt ((if_bigblock name None thn (els_hd # els_tl), KSeq next cont), Normal ns) 
                            ((els_hd, convert_list_to_cont els_tl (KSeq next cont)), Normal ns)"
  apply (rule red_ast_bpl_one_step_empty_simple_cmd)
  apply (rule RedParsedIfFalse)
  by simp

subsection \<open>Reducing Boogie programs while preserving a property\<close>

definition red_ast_bpl_rel 
  where "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1 \<equiv>
          \<forall> \<omega> ns. R0 \<omega> ns \<longrightarrow> (\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns')"

lemma red_ast_bpl_relI:
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'"
  shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
  using assms
  unfolding red_ast_bpl_rel_def
  by blast

lemma red_ast_bpl_rel_weaken_input: 
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> R0' \<omega> ns"
      and "red_ast_bpl_rel R0' R1 P ctxt \<gamma>0 \<gamma>1"
  shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
  using assms
  unfolding red_ast_bpl_rel_def
  by blast

lemma red_ast_bpl_rel_strengthen_output:
  assumes "red_ast_bpl_rel R0 R1' P ctxt \<gamma>0 \<gamma>1"
      and "\<And> \<omega> ns. R1' \<omega> ns \<Longrightarrow> R1 \<omega> ns"
    shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
  using assms
  unfolding red_ast_bpl_rel_def
  by blast  

lemma red_ast_bpl_rel_strengthen_output_2:
  assumes "red_ast_bpl_rel R0 R1' P ctxt \<gamma>0 \<gamma>1"
      and "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> Q \<omega>"
      and "\<And> \<omega> ns. Q \<omega> \<and> R1' \<omega> ns \<Longrightarrow> R1 \<omega> ns"
    shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
  using assms
  by (metis red_ast_bpl_rel_def)

lemma red_ast_bpl_rel_input_implies_output:
  assumes "\<And>\<omega> ns. R1 \<omega> ns \<Longrightarrow> R2 \<omega> ns"
  shows "red_ast_bpl_rel R1 R2 P ctxt \<gamma> \<gamma>"  
  using assms red_ast_bpl_refl
  unfolding red_ast_bpl_rel_def 
  by blast

lemma red_ast_bpl_rel_input_eq_output:
  assumes "\<And>\<omega> ns. R1 \<omega> ns \<longleftrightarrow> R2 \<omega> ns"
  shows "red_ast_bpl_rel R1 R2 P ctxt \<gamma> \<gamma>"  
  using assms red_ast_bpl_refl
  unfolding red_ast_bpl_rel_def 
  by blast

lemma red_ast_bpl_rel_refl:
  shows "red_ast_bpl_rel R R P ctxt \<gamma> \<gamma>"  
  using red_ast_bpl_refl
  unfolding red_ast_bpl_rel_def
  by blast  

lemma red_ast_bpl_rel_transitive:
  assumes "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and "red_ast_bpl_rel R1 R2 P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R2 P ctxt \<gamma>0 \<gamma>2"
  using assms red_ast_bpl_transitive
  unfolding red_ast_bpl_rel_def
  by blast

lemma red_ast_bpl_rel_transitive_2:
  assumes "red_ast_bpl_rel R0 R0 P ctxt \<gamma>0 \<gamma>1"
      and "red_ast_bpl_rel R0 R1 P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>2"
  using assms red_ast_bpl_rel_transitive
  by blast

lemma red_ast_bpl_rel_transitive_3:
  assumes "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and "red_ast_bpl_rel R1 R1 P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>2"
  using assms red_ast_bpl_rel_transitive
  by blast

lemma red_ast_bpl_rel_transitive_with_inv:
  assumes Rel1: "red_ast_bpl_rel R0 R1 P ctxt \<gamma>0 \<gamma>1"
      and Inv: "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> Q \<omega>"
      and Rel2: "red_ast_bpl_rel (\<lambda>\<omega> ns. R1 \<omega> ns \<and> Q \<omega>) R2 P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R2 P ctxt \<gamma>0 \<gamma>2"
proof (rule red_ast_bpl_relI)
  fix \<omega> ns
  assume "R0 \<omega> ns"
  with Rel1 obtain ns1 where "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1) \<and> R1 \<omega> ns1" 
    unfolding red_ast_bpl_rel_def
    by blast

  with Rel2 show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega> ns'"
    unfolding red_ast_bpl_rel_def
    using Inv[OF \<open>R0 \<omega> ns\<close>] red_ast_bpl_transitive 
    by blast
qed

lemma red_ast_bpl_rel_one_simple_cmd:
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow>
                \<exists>ns'. ( (type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), rtype_interp ctxt \<turnstile> \<langle>c, Normal ns\<rangle> \<rightarrow> (Normal ns')) \<and>
                R1 \<omega> ns'"
  shows "red_ast_bpl_rel R0 R1 P ctxt (BigBlock name (c#cs) str tr, cont) (BigBlock name cs str tr, cont)"
  using assms
  unfolding red_ast_bpl_rel_def red_ast_bpl_def
  by blast

lemma red_ast_bpl_rel_empty_block: "red_ast_bpl_rel R R P ctxt (BigBlock name [] None None, KSeq b cont) (b, cont)"
  unfolding red_ast_bpl_rel_def red_ast_bpl_def
  by (fastforce intro: RedSkip)  

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

lemma red_ast_bpl_rel_if_nondet_then:
  shows "red_ast_bpl_rel R R P ctxt (if_bigblock name None (thn_hd # thn_tl) els, KSeq next cont) 
                                      (thn_hd, convert_list_to_cont thn_tl (KSeq next cont))"
  unfolding red_ast_bpl_rel_def
  using red_ast_bpl_if_nondet_then
  by blast

lemma red_ast_bpl_rel_if_nondet_else:
  shows "red_ast_bpl_rel R R P ctxt (if_bigblock name None thn (els_hd # els_tl), KSeq next cont) 
                            (els_hd, convert_list_to_cont els_tl (KSeq next cont))"
  unfolding red_ast_bpl_rel_def
  using red_ast_bpl_if_nondet_else
  by blast

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
          "type_of_val (type_interp ctxt) v = instantiate (rtype_interp ctxt) ty"
  shows "red_ast_bpl P ctxt ((BigBlock name (Assign x e#cs) str tr, cont), Normal ns) ((BigBlock name cs str tr, cont), Normal (update_var (var_context ctxt) ns x v))"
  apply (rule red_ast_bpl_one_simple_cmd)
  using assms
  by (auto intro: RedAssign)

lemma red_ast_bpl_one_havoc:
assumes "lookup_var_decl (var_context ctxt) x = Some (ty,w)" and
        "type_of_val (type_interp ctxt) v = instantiate (rtype_interp ctxt) ty" and
        "\<And>cond. w = Some cond \<Longrightarrow> red_expr_bpl ctxt cond (update_var (var_context ctxt) ns x v) (BoolV True)"
shows "red_ast_bpl P ctxt ((BigBlock name (Havoc x # cs) str tr, cont), Normal ns) 
                            ((BigBlock name cs str tr, cont) , Normal (update_var (var_context ctxt) ns x v))"
   apply (rule red_ast_bpl_one_simple_cmd)
  using assms
  by (fastforce intro: RedHavocNormal)

lemma red_ast_bpl_havoc_assume:
assumes "lookup_var_decl (var_context ctxt) x = Some (ty,w)" and
        "type_of_val (type_interp ctxt) v = instantiate (rtype_interp ctxt) ty" and
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

subsection \<open>map_upds\<close>

subsection \<open>Lifting from single elements to lists of elements\<close>

definition update_var_list 
  where "update_var_list \<Lambda> ns xs vs \<equiv> foldl (\<lambda> ns0 x_v. (update_var \<Lambda> ns0 (fst x_v) (snd x_v))) ns (zip xs vs)"

lemma update_var_list_Cons [simp]:
  "update_var_list \<Lambda> ns (x#xs) (v#vs) = update_var_list \<Lambda> (update_var \<Lambda> ns x v) xs vs"
  unfolding update_var_list_def
  by simp

lemma update_var_list_Nil [simp]:
  "update_var_list \<Lambda> ns [] vs = ns"
  by (simp add: update_var_list_def)

lemma update_var_list_Nil2 [simp]:
  "update_var_list \<Lambda> ns xs [] = ns"
  by (simp add: update_var_list_def)

lemma lookup_update_var_list_other:
  assumes "x \<notin> set xs" and "length xs = length vs"
  shows "lookup_var \<Lambda> (update_var_list \<Lambda> ns xs vs) x = lookup_var \<Lambda> ns x"
  using assms
proof (induction xs arbitrary: vs ns)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a xs)
  from this obtain vs_hd vs_tl where 
    "vs = vs_hd # vs_tl" and "length xs = length vs_tl"
    by (metis length_Suc_conv)

  hence "lookup_var \<Lambda> (update_var_list \<Lambda> ns (a # xs) vs) x = 
        lookup_var \<Lambda> (update_var_list \<Lambda> (update_var \<Lambda> ns a vs_hd) xs vs_tl) x"
    by simp
  hence "... = lookup_var \<Lambda> (update_var \<Lambda> ns a vs_hd) x"
    using Cons \<open>vs = _\<close> \<open>length xs = _\<close>
    by simp
    
  thus ?case 
    using update_var_other Cons
    by (simp add: \<open>vs = vs_hd # vs_tl\<close>)
qed

lemma lookup_update_var_list_same:
  assumes "x \<in> set xs" and "length xs = length vs"      
  shows "lookup_var \<Lambda> (update_var_list \<Lambda> ns xs vs) x = [xs [\<mapsto>] vs] x"
  using assms
proof (induction xs arbitrary: ns vs)
  case Nil
  then show ?case
    by simp \<comment>\<open>contradiction\<close>
next
  case (Cons a xs)
  from this obtain vs_hd vs_tl where 
    "vs = vs_hd # vs_tl" and "length xs = length vs_tl"
    by (metis length_Suc_conv)

  hence *: "lookup_var \<Lambda> (update_var_list \<Lambda> ns (a # xs) vs) x = 
         lookup_var \<Lambda> (update_var_list \<Lambda> (update_var \<Lambda> ns a vs_hd) xs vs_tl) x"
    by simp

  show ?case 
  proof (cases "x \<in> set xs")
    case True
    with Cons.IH * \<open>length xs  =_\<close>
    have IHFact: "lookup_var \<Lambda> (update_var_list \<Lambda> ns (a # xs) vs) x =
           [xs [\<mapsto>] vs_tl] x"
      by simp

    thus ?thesis
      using True map_upds_Cons_lookup_tail \<open>length xs = length vs_tl\<close> \<open>vs = _\<close>
      by metis
  next
    case False
    hence "x = a"
      using Cons
      by simp

    from False * lookup_update_var_list_other 
    have "lookup_var \<Lambda> (update_var_list \<Lambda> ns (a # xs) vs) x = lookup_var \<Lambda> (update_var \<Lambda> ns a vs_hd) x"
      using \<open>length xs = length vs_tl\<close>
      by metis

    also have "... = Some vs_hd"
      using \<open>x = a\<close>
      by simp

    finally show ?thesis 
      using False
      unfolding \<open>vs = _\<close> \<open>x = a\<close> 
      by simp
  qed
qed

lemma global_state_update_var_list_local:
  assumes "map_of (snd \<Lambda>) x = Some \<tau>"
  shows  "global_state (update_var_list \<Lambda> ns xs vs) x = global_state ns x"
proof (induction xs arbitrary: vs ns)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  note ConsOuter = Cons
  show ?case
  proof (cases vs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons vs_hd vs_tl)
    hence "global_state (update_var_list \<Lambda> ns (a # xs) vs) x =
           global_state (update_var_list \<Lambda> (update_var \<Lambda> ns a vs_hd) xs vs_tl) x"
      by simp
    also have "... = global_state (update_var \<Lambda> ns a vs_hd) x"
      using ConsOuter
      by simp
              
    finally show ?thesis 
      using assms
      by (metis global_state_update_local global_state_update_other)                       
  qed    
qed

lemma update_var_list_binder_state_same:
  shows  "binder_state (update_var_list \<Lambda> ns xs vs) = binder_state ns"
proof (induction xs arbitrary: vs ns)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  thus ?case
    by (cases vs) (auto simp add: update_var_binder_same)   
qed

lemma update_var_list_old_global_state_same:
  shows  "old_global_state (update_var_list \<Lambda> ns xs vs) = old_global_state ns"
proof (induction xs arbitrary: vs ns)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  thus ?case
  by (cases vs) (auto simp add: update_var_old_global_same)   
qed

fun havocs_list_bpl :: "vname list \<Rightarrow> cmd list" where 
  "havocs_list_bpl [] = []"
| "havocs_list_bpl (x#xs) = Lang.Havoc x # havocs_list_bpl xs"

lemma red_ast_bpl_havoc_list:
  assumes  RtypeEmpty: "rtype_interp ctxt = []" and
           "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) xs vs"
shows "red_ast_bpl P ctxt ((BigBlock name (havocs_list_bpl xs @ cs) str tr, cont), Normal ns)
                          ((BigBlock name cs str tr, cont), Normal (update_var_list (var_context ctxt) ns xs vs))"
  using assms(2)
proof (induction xs arbitrary: vs ns)
  case Nil
  then show ?case 
    using red_ast_bpl_refl
    by (fastforce simp: update_var_list_def)
next
  case (Cons xs_hd xs_tl)
  let ?b = "(BigBlock name cs str tr, cont)"
  let ?\<Lambda> = "var_context ctxt"

  from Cons.prems obtain vs_hd vs_tl where
        "vs = vs_hd # vs_tl" and
        LookupXsHd: "lookup_var_decl (var_context ctxt) xs_hd = Some (type_of_val (type_interp ctxt) vs_hd, None)" and
        LookupXsTl: "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) xs_tl vs_tl"
    by (auto simp: list_all2_Cons1)

  let ?ns' = "update_var (var_context ctxt) ns xs_hd vs_hd"

  have RedHd: "red_ast_bpl P ctxt ((BigBlock name (havocs_list_bpl (xs_hd # xs_tl) @ cs) str tr, cont), Normal ns)
        ((BigBlock name (havocs_list_bpl xs_tl @ cs) str tr, cont), Normal ?ns')"
    apply simp
    apply (rule red_ast_bpl_one_havoc)
      apply (rule LookupXsHd)
     apply (simp add: RtypeEmpty)
    by simp

  have "red_ast_bpl P ctxt ((BigBlock name (havocs_list_bpl xs_tl @ cs) str tr, cont), Normal ?ns')
                                    ((BigBlock name cs str tr, cont), Normal (update_var_list (var_context ctxt) ?ns' xs_tl vs_tl))"
    using Cons.IH[OF LookupXsTl]
    by simp
  hence "red_ast_bpl P ctxt ((BigBlock name (havocs_list_bpl xs_tl @ cs) str tr, cont), Normal ?ns')
                            ((BigBlock name cs str tr, cont), Normal (update_var_list (var_context ctxt) ns (xs_hd#xs_tl) (vs_hd#vs_tl)))"
    unfolding update_var_list_def
    by auto

  thus ?case 
    using RedHd red_ast_bpl_transitive \<open>vs = _\<close>
    by blast    
qed

subsection \<open>Misc\<close>

lemma proc_is_correct_elim:
  assumes 
     "proc_is_correct A fun_decls constants unique_consts global_vars axioms proc proc_body_satisfies_spec_general" and
     "proc_body proc = Some (locals, p_body)" and
     "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)" and
     "\<forall>v. closed ((type_of_val A) v)" and
     "fun_interp_wf A fun_decls \<Gamma>" and
     "(list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc)" and
     "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
     "state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc))" and
     "unique_constants_distinct gs unique_consts" and
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

lemma closed_instantiate: "closed \<tau> \<Longrightarrow> instantiate ts \<tau> = \<tau>"
proof (induction \<tau>)
  case (TVar x)
  then show ?case by simp
next
  case (TPrim x)
  then show ?case by simp
next
  case (TCon x1a x2a)
  then show ?case 
    by (metis closed.simps(3) in_set_conv_nth instantiate.simps(3) list_all_length map_idI)
qed

lemma closed_map_instantiate: "list_all closed ts \<Longrightarrow> map (instantiate ts') ts = ts"
  apply (induction ts)
   apply simp
  apply (simp add: closed_instantiate)
  done

lemma instantiate_idem: 
  assumes "list_all closed ts"
  shows "instantiate ts (instantiate ts t) = (instantiate ts t)"
proof (induction t)
  case (TVar x)  
  then show ?case 
  proof clarsimp
    assume "x < length ts"
    hence "closed (ts ! x)"
      using assms
      by (simp add: list_all_length)
    thus "instantiate ts (ts ! x) = ts ! x"
      using closed_instantiate
      by auto
  qed
qed auto

end