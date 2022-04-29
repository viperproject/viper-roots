theory ViperBoogieBasicRel
imports TotalExpressions Boogie_Lang.Semantics ViperBoogieInstantiation
begin

type_synonym viper_expr = ViperLang.pure_exp
type_synonym boogie_expr = Lang.expr

type_synonym 'a vpr_val = "'a ValueAndBasicState.val" \<comment>\<open>Viper values with abstract carrier \<^typ>\<open>'a\<close>\<close>
typ "'a bpl_val" \<comment>\<open>Boogie values with abstract carrier \<^typ>\<open>'a\<close>\<close>
typ "'a vbpl_val" \<comment>\<open>Boogie values with abstract carrier instantiated for Viper (i.e., abstract carrier \<^typ>\<open>'a vbpl_absval\<close>\<close>
                                             
type_synonym 'a bpl_heap_ty = "ref \<Rightarrow> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"
type_synonym 'a bpl_mask_ty = "ref \<Rightarrow> 'a vb_field \<Rightarrow> real"

record tr_vpr_bpl =
  heap_var :: Lang.vname
  mask_var :: Lang.vname
  mask_read :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" \<comment>\<open>arguments: mask, receiver, field\<close>
  heap_read :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field\<close>
  field_translation :: "field_ident \<rightharpoonup> Lang.vname"
  fun_translation :: "ViperLang.function_ident \<rightharpoonup> Lang.fname"
  var_translation :: "ViperLang.var \<rightharpoonup> Lang.vname" \<comment>\<open>local Boogie variables\<close>
  lit_translation :: "ViperLang.lit \<Rightarrow> expr"
 (*TODO: bound vars*)
(*  result_var :: "string" *)

subsection \<open>Value relation\<close>

fun val_rel_vpr_bpl :: "'a vpr_val \<Rightarrow> 'a vbpl_val"
  where
    "val_rel_vpr_bpl (VInt i) = (IntV i)"
  | "val_rel_vpr_bpl (VBool b) = (BoolV b)"
  | "val_rel_vpr_bpl (VRef r) = (AbsV (ARef r))"
  | "val_rel_vpr_bpl (VAbs a) = (AbsV (ADomainVal a))"
  | "val_rel_vpr_bpl (VPerm r) = (RealV (real_of_rat r))"


subsection \<open>State relationship\<close>

definition heap_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a total_heap \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_rel Pr tr_field h hb \<equiv> 
    \<forall> l :: heap_loc. if_Some 
                       (\<lambda>field_vty. has_Some (\<lambda>res. val_rel_vpr_bpl (h l) = res) (hb (Address (fst l)) (NormalField (the (tr_field (snd l))) field_vty)))
                       (declared_fields Pr (snd l))"

definition mask_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> mask \<Rightarrow> 'a bpl_mask_ty \<Rightarrow> bool"
  where "mask_rel Pr tr_field m mb \<equiv> 
    (\<forall> l :: heap_loc. if_Some 
                       (\<lambda>field_vty. real_of_rat (Rep_prat (m l)) = (mb (Address (fst l)) (NormalField (the (tr_field (snd l))) field_vty)))
                       (declared_fields Pr (snd l))) \<and>
    (\<forall>f t. mb Null (NormalField f t) = 0)"

text \<open>\<^const>\<open>heap_rel\<close> and \<^const>\<open>mask_rel\<close> depend on the program, since the Viper type of a Viper field is required (currently)
      to identify the corresponding Boogie field\<close>

(* TODO 
definition predicate_heap_rel :: "ViperLang.program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "predicate_heap_rel Pr A h hb \<equiv> 
    \<forall> pred_id :: predicate_ident. \<forall> tys :: vtyp list. map_option (predicate_decl.args) (ViperLang.predicates Pr pred_id) = Some tys \<longrightarrow>
        (\<forall>vs. map (get_type A) vs = tys \<longrightarrow> True) "
*)

(* TODO: lift to predicates *)
definition state_rel_vpr_bpl :: "ViperLang.program \<Rightarrow> var_context \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "state_rel_vpr_bpl Pr \<Lambda> T \<omega> ns \<equiv>
           (\<forall> var_vpr var_bpl. var_translation T var_vpr = Some var_bpl \<longrightarrow> 
              (\<exists>val_vpr. ((get_store_total \<omega>) var_vpr) = Some val_vpr \<and>
                                (lookup_var \<Lambda> ns var_bpl) = Some (val_rel_vpr_bpl val_vpr))) \<and>
           (\<exists>hb. lookup_var \<Lambda> ns (heap_var T) = Some (AbsV (AHeap hb)) \<and> heap_rel Pr (field_translation T) (get_hh_total_full \<omega>) hb) \<and>
           (\<exists>mb. lookup_var \<Lambda> ns (mask_var T) = Some (AbsV (AMask mb)) \<and> mask_rel Pr (field_translation T) (get_mh_total_full \<omega>) mb) \<and>
           (\<forall>f f_vty. declared_fields Pr f = Some f_vty \<longrightarrow> 
             has_Some (\<lambda>f_bpl. lookup_var \<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (field_translation T f))"

subsection\<open>function relation\<close>

(* TODO: maybe make parametric *)
abbreviation eval_heap_dep_bpl_fun :: "('a vbpl_absval) Semantics.fun_repr \<Rightarrow> ('a vbpl_val) list \<Rightarrow> 'a vbpl_val \<rightharpoonup> 'a vbpl_val"
  where "eval_heap_dep_bpl_fun f_bpl vs heap \<equiv> f_bpl [] (heap#vs)"

definition fun_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a TotalExpressions.heapfun_repr \<Rightarrow> ('a vbpl_absval) Semantics.fun_repr \<Rightarrow> bool"
  where "fun_rel Pr tr_field f_vpr f_bpl \<equiv> 
           (\<forall>vs \<omega> v_vpr. f_vpr vs \<omega> = Some (Val v_vpr) \<longrightarrow>
              (\<forall> h_bpl. heap_rel Pr tr_field (get_hh_total_full \<omega>) h_bpl \<longrightarrow>
                has_Some (\<lambda>v_bpl. val_rel_vpr_bpl v_vpr = v_bpl) (eval_heap_dep_bpl_fun f_bpl ((map val_rel_vpr_bpl) vs) (AbsV (AHeap h_bpl)))))"

definition fun_interp_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (ViperLang.function_ident \<rightharpoonup> Lang.fname) \<Rightarrow> 'a TotalExpressions.interp \<Rightarrow> ('a vbpl_absval) Semantics.fun_interp \<Rightarrow> bool"
  where 
    "fun_interp_rel Pr tr_field tr_fun \<Delta> \<Gamma> \<equiv> (\<forall>fid f_vpr. \<Delta> fid = Some f_vpr \<longrightarrow>
                                 (\<forall>fid_bpl. tr_fun fid = Some fid_bpl \<longrightarrow>
                                   has_Some (\<lambda>f_bpl. fun_rel Pr tr_field f_vpr f_bpl) (\<Gamma> fid_bpl)))"

subsection \<open>expression relation\<close>

record 'a context_bpl =
  type_interp :: "('a vbpl_absval) absval_ty_fun"
  var_context :: var_context
  fun_interp :: "('a vbpl_absval) fun_interp"

abbreviation create_ctxt_bpl :: "('a vbpl_absval) absval_ty_fun \<Rightarrow> var_context \<Rightarrow> ('a vbpl_absval) fun_interp \<Rightarrow> 'a context_bpl"
  where "create_ctxt_bpl A \<Lambda> \<Gamma> \<equiv> \<lparr>type_interp=A, var_context=\<Lambda>,fun_interp=\<Gamma>\<rparr>"

abbreviation red_expr_bpl :: "'a context_bpl \<Rightarrow> expr \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> 'a vbpl_val \<Rightarrow> bool"
  where "red_expr_bpl ctxt e ns v \<equiv> type_interp ctxt,var_context ctxt, fun_interp ctxt,[] \<turnstile> \<langle>e, ns\<rangle> \<Down> v"

definition exp_rel_vpr_bpl :: 
   "ViperLang.program \<Rightarrow> 'a interp \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a context_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "exp_rel_vpr_bpl Pr \<Delta> T Tr ctxt e_vpr e_bpl \<omega> ns \<equiv> 
             \<exists>v1 v2. (Pr, \<Delta>, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<and> 
             (red_expr_bpl ctxt e_bpl ns v2) \<and> (val_rel_vpr_bpl v1 = v2)"


subsection \<open>syntactic relations\<close>

fun unop_rel :: "ViperLang.unop \<Rightarrow> Lang.unop"
  where 
    "unop_rel ViperLang.Minus = Lang.UMinus"
  | "unop_rel ViperLang.Not = Lang.Not"

lemma unop_rel_correct: 
  assumes 
    "eval_unop uop_vpr v_vpr = BinopNormal v_vpr'" and
    "unop_rel uop_vpr = uop_bpl"
  shows "unop_eval_val uop_bpl (val_rel_vpr_bpl v_vpr) = Some (val_rel_vpr_bpl v_vpr')  "
  apply (insert assms)
  by (erule eval_unop.elims) (auto simp: of_rat_minus)   

fun binop_rel :: "ViperLang.binop \<Rightarrow> Lang.binop"
  where 
    "binop_rel ViperLang.Add = Lang.Add"
  | "binop_rel ViperLang.Sub = Lang.Sub"
  | "binop_rel ViperLang.Mult = Lang.Mul"
  | "binop_rel ViperLang.IntDiv = Lang.Div"
  | "binop_rel ViperLang.PermDiv = Lang.RealDiv"
  | "binop_rel ViperLang.Mod = Lang.Mod"
  | "binop_rel ViperLang.Eq = Lang.Eq"
  | "binop_rel ViperLang.Neq = Lang.Neq"
  | "binop_rel ViperLang.Gt = Lang.Gt"
  | "binop_rel ViperLang.Gte = Lang.Ge"
  | "binop_rel ViperLang.Lt = Lang.Lt"
  | "binop_rel ViperLang.Lte = Lang.Le"
  | "binop_rel ViperLang.Or = Lang.Or"
  | "binop_rel ViperLang.BImp = Lang.Imp"
  | "binop_rel ViperLang.And = Lang.And"

lemma binop_lazy_rel_correct:
  assumes "eval_binop_lazy v_vpr bop_vpr = Some v'_vpr" and
          "binop_rel bop_vpr = bop_bpl" and
          "binop_eval_val bop_bpl (val_rel_vpr_bpl v_vpr) v_bpl \<noteq> None"
  shows   "binop_eval_val bop_bpl (val_rel_vpr_bpl v_vpr) v_bpl = Some (val_rel_vpr_bpl v'_vpr)"
  using assms
  apply (cases rule: eval_binop_lazy.elims)
  apply simp_all
  by (cases v_bpl; (rename_tac lit, case_tac lit, auto))+

lemma binop_nonlazy_rel_correct:
  assumes "eval_binop v1_vpr bop_vpr v2_vpr = BinopNormal v_vpr" and
          "binop_rel bop_vpr = bop_bpl" and
           \<comment>\<open>need to update Viper semantics or change relation to deal with integer division and modulo\<close>
          "bop_vpr \<noteq> IntDiv \<and> bop_vpr \<noteq> ViperLang.Mod" 
  shows   "binop_eval_val bop_bpl (val_rel_vpr_bpl v1_vpr) (val_rel_vpr_bpl v2_vpr) = Some (val_rel_vpr_bpl v_vpr)"
  using assms
  apply (cases rule: eval_binop.elims)
                      apply simp_all
    apply (cases bop_vpr)
                  apply simp_all
     \<comment>\<open>real division of two integers\<close>
    apply (unfold smt_real_div_def)
    apply (metis (mono_tags, hide_lams) Fract_of_int_quotient binop_result.distinct(5) binop_result.inject of_int_0_eq_iff of_rat_divide of_rat_of_int_eq val_rel_vpr_bpl.simps(5))
   
   \<comment>\<open>operator betweeen two reals\<close>
   apply (cases bop_vpr)
                 apply (simp_all add: of_rat_add of_rat_diff of_rat_mult smt_real_div_def of_rat_less of_rat_less_eq)
   apply (metis binop_result.distinct(5) binop_result.inject of_rat_divide val_rel_vpr_bpl.simps(5))

\<comment>\<open>operator between two booleans\<close>
  apply (cases bop_vpr) 
                apply simp_all
  done 

  
(*
datatype pure_exp =
  ELit lit
  | Var var
  | Unop unop pure_exp
  | Binop pure_exp binop pure_exp
  | CondExp pure_exp pure_exp pure_exp (*TODO, not yet supported in Boogie formalization*)
  | FieldAcc pure_exp field_ident
  | Old label pure_exp (*TODO*)

  | Perm pure_exp field_ident
  | PermPred predicate_ident "pure_exp list" (*TODO*)

  | FunApp function_ident "pure_exp list" 
  | Result (* Only for functions *) (*TODO*)

  | Unfolding predicate_ident "pure_exp list" pure_exp (*TODO*)

  | Let pure_exp pure_exp (*TODO*)
  | PExists vtyp pure_exp (*TODO*)
  | is_pforall: PForall vtyp pure_exp (*TODO*)
*)

inductive syn_exp_rel :: "ViperLang.program \<Rightarrow> tr_vpr_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> bool"
  for Pr :: ViperLang.program and Tr :: tr_vpr_bpl
  where
    \<comment>\<open>The only global variables in the Boogie encoding are Heap and Mask, which do not have a variable 
       counter part in Viper.\<close>
       VarRel: 
       "\<lbrakk> var_translation Tr x = Some y \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Tr (ViperLang.Var x) (Lang.Var y)"
     | LitRel: 
       "\<lbrakk> lit_translation Tr lit = e_bpl \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Tr (ViperLang.ELit lit) e_bpl"
     | FieldAccRel:
       "\<lbrakk> e_bpl = heap_read Tr (Lang.Var (heap_var Tr)) e_rcv_bpl e_f_bpl; 
          syn_exp_rel Pr Tr e e_rcv_bpl;
          (field_translation Tr f) = Some f_tr;
          e_f_bpl = Lang.Var f_tr;
          declared_fields Pr f \<noteq> None \<rbrakk> \<Longrightarrow>
         syn_exp_rel Pr Tr (FieldAcc e f) e_bpl" \<comment>\<open>maybe \<^term>\<open>declared_fields Pr f \<noteq> None\<close> should be handled via \<^const>\<open>wf_pure_exp\<close> \<close>
     | UnopRel:
       "\<lbrakk> unop_rel uop = uopb; 
          syn_exp_rel Pr Tr e e_bpl \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Tr (ViperLang.Unop uop e) (Lang.UnOp uopb e_bpl)"
     | BinopRel:
        "\<lbrakk> binop_rel bop = bopb;
           bop \<noteq> IntDiv \<and> bop \<noteq> ViperLang.Mod; 
           syn_exp_rel Pr Tr e1 e1_bpl; 
           syn_exp_rel Pr Tr e2 e2_bpl \<rbrakk> \<Longrightarrow>
           syn_exp_rel Pr Tr (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
     | PermRel:
         "\<lbrakk> e_bpl = mask_read Tr (Lang.Var (mask_var Tr)) rcv_bpl f_bpl; 
           syn_exp_rel Pr Tr e rcv_bpl;
           (field_translation Tr f) = Some f_tr;
           f_bpl = Lang.Var f_tr;
           declared_fields Pr f \<noteq> None \<rbrakk> \<Longrightarrow>
           syn_exp_rel Pr Tr (Perm e f) e_bpl" \<comment>\<open>maybe \<^term>\<open>declared_fields Pr f \<noteq> None\<close> should be handled via \<^const>\<open>wf_pure_exp\<close> \<close>
     | FunAppRel: \<comment>\<open>maybe should abstract over how function calls are encoded\<close>
       "\<lbrakk> es_bpl = e_heap#e_args_bpl; 
          fun_translation Tr f = Some f_bpl;
          list_all2 (\<lambda>e_vpr e_bpl. syn_exp_rel Pr Tr e_vpr e_bpl) es e_args_bpl;          
          e_heap = Lang.Var (heap_var Tr) \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Tr (FunApp f es) (FunExp f_bpl [] es_bpl)"

lemma var_context_aux:
  assumes "x \<in> set (map fst (snd \<Lambda>))"
  shows "lookup_var \<Lambda> ns x = local_state ns x"
proof -
  from assms obtain y where "map_of (snd \<Lambda>) x = Some y"
    by (metis domIff dom_map_of_2 not_Some_eq)
  thus ?thesis
    unfolding lookup_var_def
    by simp
qed

definition lit_translation_rel :: "'a context_bpl => ('a vbpl_absval) nstate \<Rightarrow> (ViperLang.lit \<Rightarrow> Lang.expr) \<Rightarrow> bool"
  where "lit_translation_rel ctxt ns litT \<equiv> (\<forall>lit e. litT lit = e \<longrightarrow> red_expr_bpl ctxt e ns (val_rel_vpr_bpl (val_of_lit lit)))"

definition heap_read_wf :: "'a context_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "heap_read_wf ctxt hread \<equiv> \<forall> e_heap e_rcv e_f h r f ns v. 
         ( (red_expr_bpl ctxt e_heap ns (AbsV (AHeap h)) \<and> 
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> h r f = Some v) \<longrightarrow>
            red_expr_bpl ctxt (hread e_heap e_rcv e_f) ns v ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (hread e_heap e_rcv e_f) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

definition mask_read_wf :: "'a context_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "mask_read_wf ctxt mread \<equiv> \<forall> e_mask e_rcv e_f m r f ns v. 
         ( (red_expr_bpl ctxt e_mask ns (AbsV (AMask m)) \<and> 
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> m r f = v) \<longrightarrow>
            red_expr_bpl ctxt (mread e_mask e_rcv e_f) ns (RealV v) ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (mread e_mask e_rcv e_f) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"


lemma bg_expr_list_red_iff:
\<comment>\<open>Taken from Benjamin's BoogieWrapper.thy: TODO proper merge\<close>
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], s\<rangle> [\<Down>] v) = (v = [])"
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e0#es, s\<rangle> [\<Down>] v)
    = (\<exists>v0 vs. v = v0#vs \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e0, s\<rangle> \<Down> v0) \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs))"
  by ((rule iffI, (erule red_exprs.cases, assumption, simp), (simp, rule RedExpListNil)),
      (rule iffI, (erule red_exprs.cases, simp, simp), (clarsimp, rule RedExpListCons; simp)))

lemma bg_expr_list_red_all2:
\<comment>\<open>Taken from Benjamin's BoogieWrapper.thy: TODO proper merge\<close>
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) = list_all2 (\<lambda>e v. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v) es vs"
  by (induct es arbitrary:vs; simp add:bg_expr_list_red_iff list_all2_Cons1)

lemma heap_read_wf_apply:
  assumes "heap_read_wf ctxt hread" and
          "h r f = Some v" and
          "red_expr_bpl ctxt e_heap ns (AbsV (AHeap h))"and 
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))"
  shows "red_expr_bpl ctxt (hread e_heap e_rcv e_f) ns v"
  using assms
  unfolding heap_read_wf_def
  by blast

lemma syn_exp_rel_correct:
  assumes 
          "syn_exp_rel Pr Tr e_vpr e_bpl" and 
          "Pr, \<Delta>, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and

         \<comment>\<open>Need Boogie expression to reduce because Viper has lazy binary operators but Boogie does not.
           Thus, the Viper reduction on its own cannot be used to construct a Boogie reduction.\<close>
          "\<exists>v. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e_bpl ns v" and

          StateRel:"state_rel_vpr_bpl Pr \<Lambda> Tr \<omega> ns" and 
          FInterpRel: "fun_interp_rel Pr (field_translation Tr) (fun_translation Tr) \<Delta> \<Gamma>" and
          LitTrRel:"lit_translation_rel (create_ctxt_bpl A \<Lambda> \<Gamma>) ns (lit_translation Tr)"  and
          HeapReadWf: "heap_read_wf (create_ctxt_bpl A \<Lambda> \<Gamma>) (heap_read Tr)" and
          MaskReadWf: "mask_read_wf (create_ctxt_bpl A \<Lambda> \<Gamma>) (mask_read Tr)"
        shows "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e_bpl ns (val_rel_vpr_bpl v1)"
  using assms(1-3)
proof(induction arbitrary: v1)
  case (VarRel x y)
  hence "get_store_total \<omega> x = Some v1"
    by (auto elim: TotalExpressions.RedVar_case)
  with StateRel \<open>var_translation Tr x = Some y\<close> show ?case
    unfolding state_rel_vpr_bpl_def
    by (metis context_bpl.select_convs(2) option.inject red_expr_red_exprs.RedVar)
next
  case (LitRel lit e_bpl)
  hence "v1 = val_of_lit lit"
    by (auto elim: TotalExpressions.RedLit_case)
  hence "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e_bpl ns (val_rel_vpr_bpl v1)"
    using LitRel LitTrRel
    unfolding lit_translation_rel_def
    by auto
  thus ?case by simp
next
  case (FieldAccRel e_bpl e_rcv_bpl e_f_bpl e f f_tr)
  from FieldAccRel.prems obtain a where "Pr, \<Delta>, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))" and HeapVal:"get_hh_total_full \<omega> (a,f) = v1" 
    using RedFieldNormal_case
    by blast
  hence LookupRcv:"A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef (Address a))"
    using FieldAccRel.IH FieldAccRel.prems \<open>e_bpl = _\<close> HeapReadWf
    unfolding heap_read_wf_def
    by (metis context_bpl.select_convs(1) context_bpl.select_convs(2) context_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))    
  from \<open>declared_fields Pr f \<noteq> None\<close> StateRel obtain vty where 
      FieldTy:"declared_fields Pr f = Some vty" and
      LookupField:"lookup_var \<Lambda> ns f_tr = Some (AbsV (AField (NormalField f_tr vty)))"
    unfolding state_rel_vpr_bpl_def
    using FieldAccRel.hyps(3) by fastforce
  from StateRel obtain h_bpl where
     LookupHeap:"lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap h_bpl))" and 
     HeapRel:"heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) h_bpl"
    unfolding state_rel_vpr_bpl_def
    by blast  
  from HeapRel have
    "has_Some ((=) (val_rel_vpr_bpl (get_hh_total_full \<omega> (a,f))))
            (h_bpl (Address a) (NormalField f_tr vty))"
    unfolding heap_rel_def
    using FieldTy \<open>field_translation Tr f = Some f_tr\<close>
    by (metis option.pred_inject(2) option.sel fst_conv snd_conv)
  hence HeapValBpl:"h_bpl (Address a) (NormalField f_tr vty) = Some (val_rel_vpr_bpl v1)"
    using HeapVal
    by (metis (full_types) has_Some_iff)
  show ?case 
    apply (subst \<open>e_bpl =_ \<close>)
    apply (rule heap_read_wf_apply[OF HeapReadWf])
       apply (rule HeapValBpl)
    by (auto intro: LookupHeap LookupRcv LookupField RedVar simp: \<open>e_f_bpl = expr.Var f_tr\<close>)
next
  case (UnopRel uop uopb e e_bpl)  
  then show ?case 
    by (auto elim!: TotalExpressions.RedUnop_case intro: Semantics.RedUnOp unop_rel_correct)
next
  case (BinopRel bop bopb e1 e1_bpl e2 e2_bpl)
  from this obtain w2 where 
        Red1:"\<exists>a. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e1_bpl ns a" and 
        Red2:"red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e2_bpl ns w2"
    by auto
  show ?case    
  proof (rule RedBinop_case[OF \<open>Pr, \<Delta>, None \<turnstile> \<langle>Binop e1 bop e2; _\<rangle> [\<Down>]\<^sub>t _\<close>])    
    \<comment>\<open>lazy binop case\<close>
    fix v1'
    assume a:"Pr, \<Delta>, None \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and eval_lazy:"eval_binop_lazy v1' bop = Some v1"
    hence Red3:"red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e1_bpl ns (val_rel_vpr_bpl v1')"
      using BinopRel.IH(1) Red1
      by auto
    thus ?thesis
      using binop_lazy_rel_correct[OF eval_lazy \<open>binop_rel _ = _\<close>] Red2
      by (metis (no_types, hide_lams) BinopRel.prems(2) RedBinOp_case expr_eval_determ(1) option.distinct(1) option.sel)
  next    
    \<comment>\<open>nonlazy binop case\<close>
    fix v1' v2'
    assume "Pr, \<Delta>, None \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and 
           "Pr, \<Delta>, None \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2'" and 
           "eval_binop v1' bop v2' = BinopNormal v1"
    thus ?thesis
      using BinopRel.IH Red1 Red2 \<open>binop_rel _ = _\<close> \<open>bop \<noteq> IntDiv \<and> bop \<noteq> ViperLang.binop.Mod\<close> binop_nonlazy_rel_correct      
      by (blast intro: RedBinOp)
  qed
next
  case (PermRel e_bpl e_rcv_bpl f_bpl e f f_tr)
  from PermRel.prems obtain r where "Pr, \<Delta>, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" 
    using RedPerm_case
    by blast  

  from \<open>declared_fields Pr f \<noteq> None\<close> StateRel obtain vty where 
      FieldTy:"declared_fields Pr f = Some vty" and
      LookupField:"lookup_var \<Lambda> ns f_tr = Some (AbsV (AField (NormalField f_tr vty)))"
    unfolding state_rel_vpr_bpl_def
    using PermRel by fastforce
  from StateRel obtain m_bpl where
     LookupMask:"lookup_var \<Lambda> ns (mask_var Tr) = Some (AbsV (AMask m_bpl))" and 
     MaskRel:"mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) m_bpl"
    unfolding state_rel_vpr_bpl_def
    by blast

  show ?case
  proof (rule RedPerm_case)
    show "Pr, \<Delta>, None \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      by (auto intro: PermRel)
  next
    assume "v1 = VPerm 0"
    assume "Pr, \<Delta>, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null)"
    hence "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef Null)"
      using PermRel.IH PermRel.prems \<open>e_bpl = _\<close> MaskReadWf
      unfolding mask_read_wf_def
      by (metis context_bpl.select_convs(1) context_bpl.select_convs(2) context_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))
    with LookupField LookupMask MaskRel MaskReadWf \<open>e_bpl = _\<close> PermRel.hyps \<open>v1 = _\<close>
    show ?case
      unfolding mask_rel_def mask_read_wf_def
      by (metis context_bpl.select_convs(1) context_bpl.select_convs(2) context_bpl.select_convs(3) of_rat_0 red_expr_red_exprs.RedVar val_rel_vpr_bpl.simps(5))
  next
    fix a
    assume "v1 = VPerm (Rep_prat (fst (snd (Rep_total_state (snd (snd \<omega>)))) (a, f)))"
    hence HeapVal:"v1 = VPerm (Rep_prat (get_mh_total_full \<omega> (a,f)))"
      by simp
    assume "Pr, \<Delta>, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    hence "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef (Address a))"
      using PermRel.IH PermRel.prems \<open>e_bpl = _\<close> MaskReadWf
      unfolding mask_read_wf_def
      by (metis context_bpl.select_convs(1) context_bpl.select_convs(2) context_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))

    with LookupMask LookupField MaskReadWf \<open>e_bpl = _\<close> MaskRel
    show ?case
      unfolding mask_read_wf_def mask_rel_def
      by (simp add: FieldTy HeapVal PermRel.hyps(3) PermRel.hyps(4) if_Some_iff red_expr_red_exprs.RedVar)
  qed
next
  case (FunAppRel es_bpl e_heap e_args_bpl f f_bpl es)
  from \<open>Pr, \<Delta>, None \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1\<close>
  obtain vs f_interp_vpr where     
      args_vpr: "list_all2 (\<lambda>e v. red_pure_exp_total Pr \<Delta> None e \<omega> (Val v)) es vs" and
                "\<Delta> f = Some f_interp_vpr" and
                "f_interp_vpr vs \<omega> = Some (Val v1)"
    by (blast elim: red_pure_exp_total_elims)
 
  from this obtain vs_bpl where BplArgsRed:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) es_bpl vs_bpl"
    using \<open>\<exists>a. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (FunExp f_bpl [] es_bpl) ns a\<close>    
    by (auto simp: bg_expr_list_red_all2)
  have "length es = length e_args_bpl" using FunAppRel.IH
    by (simp add: List.list_all2_conv_all_nth)
 have "length es = length vs" using args_vpr
      by (simp add: List.list_all2_conv_all_nth)

  have "list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns (val_rel_vpr_bpl v)) e_args_bpl vs"  
  proof (rule List.list_all2_all_nthI)
    show "length e_args_bpl = length vs"
      using \<open>length es = length e_args_bpl\<close> \<open>length es = length vs\<close>
      by simp
  next
    fix n
    assume "n < length e_args_bpl"
    hence "n < length es" using \<open>length es = length e_args_bpl\<close>
      by simp

    hence IHReq1:"Pr, \<Delta>, None \<turnstile> \<langle>es ! n;\<omega>\<rangle> [\<Down>]\<^sub>t Val (vs ! n)"
      using args_vpr
      by (metis list_all2_conv_all_nth)

    have "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (es_bpl ! (Suc n)) ns (vs_bpl ! (Suc n))"
      using BplArgsRed \<open>n < length e_args_bpl\<close>    
      by (auto simp: \<open>es_bpl = _\<close> list_all2_conv_all_nth)
    hence IHReq2: "\<exists>v. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (e_args_bpl ! n) ns v"
      by (auto simp: \<open>es_bpl = _\<close>)

    from IHReq1 IHReq2 FunAppRel.IH      
    show "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_args_bpl ! n,ns\<rangle> \<Down> val_rel_vpr_bpl (vs ! n)"
      by (auto simp: \<open>n < length e_args_bpl\<close> list_all2_conv_all_nth)
  qed      

  hence *:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) e_args_bpl (map val_rel_vpr_bpl vs)"
    by (simp add: list.rel_map(2))

  from StateRel obtain h_bpl where
     LookupHeap:"lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap h_bpl))" and 
     HeapRel:"heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) h_bpl"
    unfolding state_rel_vpr_bpl_def
    by blast

  from LookupHeap have "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (Var (heap_var Tr)) ns (AbsV (AHeap h_bpl))"
    by (auto intro: Semantics.RedVar)
  with * have A:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) ((Var (heap_var Tr))#e_args_bpl) ((AbsV (AHeap h_bpl))#(map val_rel_vpr_bpl vs))"
    by simp

  obtain f_interp_bpl where
       "\<Gamma> f_bpl = Some f_interp_bpl" and
       "fun_rel Pr (field_translation Tr) f_interp_vpr f_interp_bpl"
    using FInterpRel \<open>fun_translation Tr f = Some f_bpl\<close> \<open>\<Delta> f = Some f_interp_vpr\<close>
    unfolding fun_interp_rel_def
    by (metis has_Some_iff)

  hence **:"(eval_heap_dep_bpl_fun f_interp_bpl (map val_rel_vpr_bpl vs) (AbsV (AHeap h_bpl))) = Some (val_rel_vpr_bpl v1)"
    using \<open>f_interp_vpr vs \<omega> = Some (Val v1)\<close> HeapRel
    unfolding fun_rel_def 
    apply (simp add: has_Some_iff)
    by (metis prod.collapse)    
  show ?case
    apply (rule RedFunOp)
      apply (simp add: \<open>\<Gamma> f_bpl = Some f_interp_bpl\<close>)     
     apply (simp add: bg_expr_list_red_all2)
     apply (subst \<open>es_bpl = _\<close>)
    apply (subst \<open>e_heap = _\<close>)    
     apply (rule A)
    using **
    by simp
qed


end