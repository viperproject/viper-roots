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
  mask_read :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field\<close>
  heap_read :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field\<close>
  field_translation :: "field_ident \<rightharpoonup> field_ident"
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

definition heap_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> field_ident) \<Rightarrow> 'a total_heap \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "heap_rel Pr tr_field h hb \<equiv> 
    \<forall> l :: heap_loc. if_Some 
                       (\<lambda>field_vty. option_fold (\<lambda>res. val_rel_vpr_bpl (h l) = res) False (hb (Address (fst l)) (NormalField (the (tr_field (snd l))) field_vty)))
                       (declared_fields Pr (snd l))"

definition mask_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> field_ident) \<Rightarrow> mask \<Rightarrow> 'a bpl_mask_ty \<Rightarrow> bool"
  where "mask_rel Pr tr_field m mb \<equiv> 
    \<forall> l :: heap_loc. if_Some 
                       (\<lambda>field_vty. real_of_rat (Rep_prat (m l)) = (mb (Address (fst l)) (NormalField (the (tr_field (snd l))) field_vty)))
                       (declared_fields Pr (snd l))"

text \<open>\<^const>\<open>heap_rel\<close> and \<^const>\<open>mask_rel\<close> depend on the program, since the Viper type of a Viper field is required (currently)
      to identify the corresponding Boogie field\<close>

(* TODO 
definition predicate_heap_rel :: "ViperLang.program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "predicate_heap_rel Pr A h hb \<equiv> 
    \<forall> pred_id :: predicate_ident. \<forall> tys :: vtyp list. map_option (predicate_decl.args) (ViperLang.predicates Pr pred_id) = Some tys \<longrightarrow>
        (\<forall>vs. map (get_type A) vs = tys \<longrightarrow> True) "
*)

(* TODO: lift to predicates *)
definition state_rel_vpr_bpl :: "ViperLang.program \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "state_rel_vpr_bpl Pr T \<omega> ns \<equiv>
           (\<forall> var_vpr var_bpl. var_translation T var_vpr = Some var_bpl \<longrightarrow> 
              (\<exists>val_vpr val_bpl. ((get_store_total \<omega>) var_vpr) = Some val_vpr \<and>
                                ((local_state ns) var_vpr) = Some val_bpl \<and>
                                val_rel_vpr_bpl val_vpr = val_bpl)) \<and>
           (\<exists>hb. (global_state ns) (heap_var T) = Some (AbsV (AHeap hb)) \<and> heap_rel Pr (field_translation T) (get_hh_total_full \<omega>) hb) \<and>
           (\<exists>mb. (global_state ns) (mask_var T) = Some (AbsV (AMask mb)) \<and> mask_rel Pr (field_translation T) (get_mh_total_full \<omega>) mb)"

subsection\<open>function relation\<close>

(* TODO: maybe make parametric *)
abbreviation eval_heap_dep_bpl_fun :: "('a vbpl_absval) Semantics.fun_repr \<Rightarrow> ('a vbpl_val) list \<Rightarrow> 'a vbpl_val \<rightharpoonup> 'a vbpl_val"
  where "eval_heap_dep_bpl_fun f_bpl vs heap \<equiv> f_bpl [] (heap#vs)"

definition fun_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> field_ident) \<Rightarrow> 'a TotalExpressions.heapfun_repr \<Rightarrow> ('a vbpl_absval) Semantics.fun_repr \<Rightarrow> bool"
  where "fun_rel Pr tr_field f_vpr f_bpl \<equiv> 
           (\<forall>vs \<omega> v_vpr. f_vpr vs \<omega> = Some (Val v_vpr) \<longrightarrow>
              (\<forall> h_bpl. heap_rel Pr tr_field (get_hh_total_full \<omega>) h_bpl \<longrightarrow>
                has_Some (\<lambda>v_bpl. val_rel_vpr_bpl v_vpr = v_bpl) (eval_heap_dep_bpl_fun f_bpl ((map val_rel_vpr_bpl) vs) (AbsV (AHeap h_bpl)))))"

definition fun_interp_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> field_ident) \<Rightarrow> (ViperLang.function_ident \<Rightarrow> Lang.fname) \<Rightarrow> 'a TotalExpressions.interp \<Rightarrow> ('a vbpl_absval) Semantics.fun_interp \<Rightarrow> bool"
  where 
    "fun_interp_rel Pr tr_field f_tr \<Delta> \<Gamma> \<equiv> (\<forall>fid f_vpr. \<Delta> fid \<noteq> Some f_vpr \<longrightarrow>
                                 has_Some (\<lambda>f_bpl. fun_rel Pr tr_field f_vpr f_bpl) (\<Gamma> (f_tr fid)))"

subsection \<open>expression relation\<close>

record 'a context_bpl =
  get_var_context :: var_context
  get_fun_interp :: "('a vbpl_absval) fun_interp"
  get_type_interp :: "('a vbpl_absval) absval_ty_fun"

definition exp_rel_vpr_bpl :: 
   "ViperLang.program \<Rightarrow> 'a interp \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a context_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "exp_rel_vpr_bpl Pr \<Delta> T Tr ctxt e_vpr e_bpl \<omega> ns \<equiv> 
             \<exists>v1 v2. (Pr, \<Delta>, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<and> 
             ((get_type_interp) ctxt,(get_var_context) ctxt, (get_fun_interp) ctxt,[] \<turnstile> \<langle>e_bpl, ns\<rangle> \<Down> v2) \<and> (val_rel_vpr_bpl v1 = v2)"


subsection \<open>syntactic relations\<close>

fun unop_rel :: "ViperLang.unop \<Rightarrow> Lang.unop"
  where 
    "unop_rel ViperLang.Minus = Lang.UMinus"
  | "unop_rel ViperLang.Not = Lang.Not"

fun binop_rel :: "ViperLang.binop \<Rightarrow> Lang.binop"
  where 
    "binop_rel ViperLang.Add = Lang.Add"
  | "binop_rel ViperLang.Sub = Lang.Sub"
  | "binop_rel ViperLang.Mult = Lang.Mul"
  | "binop_rel ViperLang.IntDiv = Lang.Div"
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
(* TODO: PermDiv case *)

(*
datatype pure_exp =
  ELit lit
  | Var var
  | Unop unop pure_exp
  | Binop pure_exp binop pure_exp
  | CondExp pure_exp pure_exp pure_exp
  | FieldAcc pure_exp field_ident
  | Old label pure_exp

  | Perm pure_exp field_ident
  | PermPred predicate_ident "pure_exp list"

  | FunApp function_ident "pure_exp list"
  | Result (* Only for functions *)

\<comment>\<open>unfolding P(l) in e\<close>
  | Unfolding predicate_ident "pure_exp list" pure_exp

  | Let pure_exp pure_exp
  | PExists vtyp pure_exp
  | is_pforall: PForall vtyp pure_exp
*)

inductive syn_exp_rel :: "tr_vpr_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> bool"
  for Tr :: tr_vpr_bpl
  where
    \<comment>\<open>The only global variables in the Boogie encoding are Heap and Mask, which do not have a variable 
       counter part in Viper.\<close>
       VarRel: 
       "\<lbrakk> var_translation Tr x = Some y \<rbrakk> \<Longrightarrow>
          syn_exp_rel Tr (ViperLang.Var x) (Lang.Var y)"
     | LitRel: 
       "\<lbrakk> lit_translation Tr lit = e_bpl \<rbrakk> \<Longrightarrow>
          syn_exp_rel Tr (ViperLang.ELit lit) e_bpl"
     | FieldAccRel:
       "\<lbrakk> e_bpl = heap_read Tr (Lang.Var (heap_var Tr)) rcv_bpl f_bpl \<rbrakk> \<Longrightarrow>
         syn_exp_rel Tr (FieldAcc e f) e_bpl"
     | UnopRel:
       "\<lbrakk> unop_rel uop = uopb; syn_exp_rel Tr e e_bpl \<rbrakk> \<Longrightarrow>
           syn_exp_rel Tr (ViperLang.Unop uop e) (Lang.UnOp uopb e_bpl)"
     | BinopRel:
        "\<lbrakk> binop_rel bop = bopb; syn_exp_rel Tr e1 e1_bpl; syn_exp_rel Tr e2 e2_bpl \<rbrakk> \<Longrightarrow>
           syn_exp_rel Tr (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
     | FieldRel:
        "syn_exp_rel Tr (Perm e f) e_bpl"
     | FunAppRel:
       "\<lbrakk> es_bpl = e_heap#e_args_bpl; 
          list_all2 (\<lambda>e_vpr e_bpl. syn_exp_rel Tr e_vpr e_bpl) es e_args_bpl;
          e_heap = Lang.Var (heap_var Tr) \<rbrakk> \<Longrightarrow>
          syn_exp_rel Tr (FunApp f es) (FunExp f_bpl ts es_bpl)"

end