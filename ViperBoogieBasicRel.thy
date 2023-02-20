section \<open>Semantic relationship between basic Viper and Boogie constructs\<close>
theory ViperBoogieBasicRel
imports TotalExpressions TotalSemantics ViperBoogieAbsValueInst Boogie_Lang.Ast "HOL-Library.Disjoint_Sets"
begin

text \<open>
  In this section, we provide definitions that semantically relate Viper and Boogie constructs.
\<close>

type_synonym viper_expr = ViperLang.pure_exp
type_synonym boogie_expr = Lang.expr

type_synonym 'a vpr_val = "'a ValueAndBasicState.val" \<comment>\<open>Viper values with abstract carrier \<^typ>\<open>'a\<close>\<close>
typ "'a bpl_val" \<comment>\<open>Boogie values with abstract carrier \<^typ>\<open>'a\<close>\<close>
typ "'a vbpl_val" \<comment>\<open>Boogie values with abstract carrier instantiated for Viper (i.e., 
abstract carrier \<^typ>\<open>'a vbpl_absval\<close>\<close>
                                             
type_synonym 'a bpl_heap_ty = "ref \<Rightarrow> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"
type_synonym 'a bpl_mask_ty = "ref \<Rightarrow> 'a vb_field \<Rightarrow> real"

datatype boogie_const =      
       CNoPerm
     | CWritePerm
     | CNull 
     | CZeroMask

definition total_context_trivial :: "'a total_context"
  where "total_context_trivial \<equiv> \<lparr> program_total = Pr_trivial, fun_interp_total=f_None, absval_interp_total=(\<lambda>_.''dummy'')  \<rparr>"

text \<open>The following record abstracts over elements in the Boogie encoding that are used to represent
Viper counterparts.\<close>

record tr_vpr_bpl =
  heap_var :: Lang.vname
  mask_var :: Lang.vname
  mask_read :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: mask, receiver, field, field type arguments\<close>
  heap_read :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field, field type arguments\<close>
  field_translation :: "field_ident \<rightharpoonup> Lang.vname"
  fun_translation :: "ViperLang.function_ident \<rightharpoonup> Lang.fname"
  var_translation :: "ViperLang.var \<rightharpoonup> Lang.vname" \<comment>\<open>local Boogie variables\<close>
  const_repr :: "boogie_const \<Rightarrow> Lang.vname"
  
 (*TODO: bound vars*)
(*  result_var :: "string" *)

text \<open>
Some parts here are irrelevant for the semantic relationship. For example, \<^const>\<open>mask_read\<close>
and \<^const>\<open>heap_read\<close> abstract over how the mask and heap read accesses are encoded as Boogie 
expressions. Other parts are required for the semantic relationship. For example \<^const>\<open>field_translation\<close>
indicates the related pairs of Viper field names and corresponding Boogie constants
\<close>

subsection \<open>Value relation\<close>

fun val_rel_vpr_bpl :: "'a vpr_val \<Rightarrow> 'a vbpl_val"
  where
    "val_rel_vpr_bpl (VInt i) = (IntV i)"
  | "val_rel_vpr_bpl (VBool b) = (BoolV b)"
  | "val_rel_vpr_bpl (VRef r) = (AbsV (ARef r))"
  | "val_rel_vpr_bpl (VAbs a) = (AbsV (ADomainVal a))"
  | "val_rel_vpr_bpl (VPerm r) = (RealV (real_of_rat r))"


subsection \<open>expression relation\<close>

record 'a econtext_bpl =
  type_interp :: "('a vbpl_absval) absval_ty_fun"
  var_context :: var_context
  fun_interp :: "('a vbpl_absval) fun_interp"

abbreviation create_ctxt_bpl :: "('a vbpl_absval) absval_ty_fun \<Rightarrow> var_context \<Rightarrow> ('a vbpl_absval) fun_interp \<Rightarrow> 'a econtext_bpl"
  where "create_ctxt_bpl A \<Lambda> \<Gamma> \<equiv> \<lparr>type_interp=A, var_context=\<Lambda>,fun_interp=\<Gamma>\<rparr>"

abbreviation red_expr_bpl :: "'a econtext_bpl \<Rightarrow> expr \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> 'a vbpl_val \<Rightarrow> bool"
  where "red_expr_bpl ctxt e ns v \<equiv> type_interp ctxt, var_context ctxt, fun_interp ctxt, [] \<turnstile> \<langle>e, ns\<rangle> \<Down> v"       

definition exp_rel_vb_single ::
  "'a total_context \<Rightarrow> 'a econtext_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "exp_rel_vb_single ctxt_vpr ctxt e_vpr e_bpl \<omega> ns \<equiv> 
      (\<forall>v1 StateCons \<omega>_def_opt. (ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<longrightarrow>
               (\<exists>v2. (red_expr_bpl ctxt e_bpl ns v2) \<and> (val_rel_vpr_bpl v1 = v2)))"

text \<open>Expression relation: Here, the well-definedness state is not fixed in the expression evaluation, 
because we only care about the case where the expression successfully evaluates to a value.\<close>
definition exp_rel_vpr_bpl :: 
   "('a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> 'a econtext_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> bool"
   where "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl \<equiv> 
           \<forall> \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<longrightarrow> exp_rel_vb_single ctxt_vpr ctxt e_vpr e_bpl \<omega> ns"


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

(* TODO: lift to predicates *)
(* TODO 
definition predicate_heap_rel :: "ViperLang.program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a bpl_heap_ty \<Rightarrow> bool"
  where "predicate_heap_rel Pr A h hb \<equiv> 
    \<forall> pred_id :: predicate_ident. \<forall> tys :: vtyp list. map_option (predicate_decl.args) (ViperLang.predicates Pr pred_id) = Some tys \<longrightarrow>
        (\<forall>vs. map (get_type A) vs = tys \<longrightarrow> True) "
*)

definition heap_read_wf :: "'a ty_repr_bpl \<Rightarrow> 'a econtext_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "heap_read_wf T ctxt hread \<equiv> \<forall> e_heap e_rcv e_f h r f ns v field_tcon ty_args. 
         ( (red_expr_bpl ctxt e_heap ns (AbsV (AHeap h)) \<and>
           vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[]) \<and>
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> h r f = Some v \<and>
          field_ty_fun_opt T f = Some (field_tcon, ty_args) ) \<longrightarrow>
            red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

definition mask_read_wf :: "'a ty_repr_bpl \<Rightarrow> 'a econtext_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "mask_read_wf T ctxt mread \<equiv> \<forall> e_mask e_rcv e_f m r f ns v field_tcon ty_args.
         ( (red_expr_bpl ctxt e_mask ns (AbsV (AMask m)) \<and> 
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> m r f = v \<and>
          field_ty_fun_opt T f = Some (field_tcon, ty_args)) \<longrightarrow>
            red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns (RealV v) ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

definition heap_var_rel :: "ViperLang.program \<Rightarrow>  var_context \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> vname \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "heap_var_rel Pr \<Lambda> TyRep T hvar \<omega> ns \<equiv>
                 (\<exists>hb. lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
                 lookup_var_ty \<Lambda> hvar = Some (TConSingle (THeapId TyRep)) \<and>
                 vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[]) \<and>
                 heap_rel Pr (field_translation T) (get_hh_total_full \<omega>) hb)"

definition mask_var_rel :: "ViperLang.program \<Rightarrow>  var_context \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> vname \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "mask_var_rel Pr \<Lambda> TyRep T mvar \<omega> ns \<equiv>
                 (\<exists>mb. lookup_var \<Lambda> ns mvar = Some (AbsV (AMask mb)) \<and> 
                 lookup_var_ty \<Lambda> mvar = Some (TConSingle (TMaskId TyRep)) \<and> 
             \<comment>\<open>Since all Boogie masks \<^term>\<open>mb\<close> have the correct type, we don't add a typing constraint 
               (in contrast to Boogie heaps).\<close>                 
                       mask_rel Pr (field_translation T) (get_mh_total_full \<omega>) mb)"

lemma heap_var_rel_stable:
  assumes "heap_var_rel Pr \<Lambda> TyRep T hvar \<omega> ns" and
          "get_hh_total_full \<omega> = get_hh_total_full \<omega>'" and
          "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"
        shows "heap_var_rel Pr \<Lambda> TyRep T hvar \<omega>' ns'"
  using assms
  unfolding heap_var_rel_def
  by auto

lemma mask_var_rel_stable:
  assumes "mask_var_rel Pr \<Lambda> TyRep T mvar \<omega>' ns"
          "get_mh_total_full \<omega> = get_mh_total_full \<omega>'"
          "lookup_var \<Lambda> ns mvar = lookup_var \<Lambda> ns' mvar"
        shows "mask_var_rel Pr \<Lambda> TyRep T mvar \<omega> ns'"
  using assms
  unfolding mask_var_rel_def
  by auto
                           
abbreviation zero_mask_bpl :: "ref \<Rightarrow> 'a vb_field \<Rightarrow> real"
  where "zero_mask_bpl \<equiv> \<lambda>r f. 0"

lemma zero_mask_rel:
  shows "mask_rel Pr F zero_mask zero_mask_bpl"
  unfolding  mask_rel_def
  by (auto intro: if_SomeI simp: pnone.rep_eq zero_mask_def)

lemma zero_mask_rel_2:
  assumes "is_empty_total \<omega>"
  shows "mask_rel Pr F (get_mh_total_full \<omega>) zero_mask_bpl"
  using assms
  unfolding is_empty_total_def 
  by (simp add: zero_mask_rel)

fun boogie_const_val :: "boogie_const => ('a vbpl_val)"
  where
    "boogie_const_val CNoPerm = RealV 0"
  | "boogie_const_val CWritePerm = RealV 1"
  | "boogie_const_val CNull = AbsV (ARef Null)"
  | "boogie_const_val CZeroMask = AbsV (AMask zero_mask_bpl)"

definition boogie_const_rel :: "(boogie_const \<Rightarrow> vname) \<Rightarrow> var_context \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "boogie_const_rel C \<Lambda> ns \<equiv> 
           \<forall>const. lookup_var \<Lambda> ns (C const) = Some (boogie_const_val const)"

lemma boogie_const_rel_lookup:
  assumes "boogie_const_rel C \<Lambda> ns"           
  shows "lookup_var \<Lambda> ns (C const) = Some (boogie_const_val const)"
  using assms
  unfolding boogie_const_rel_def
  by auto

lemma boogie_const_rel_lookup_2:
  assumes "boogie_const_rel C \<Lambda> ns" and
          "c = C const" and
          "v = boogie_const_val const"
  shows "lookup_var \<Lambda> ns c = Some (boogie_const_val const)"
  using assms boogie_const_rel_lookup
  by simp

lemma boogie_const_rel_stable:
  assumes "boogie_const_rel C \<Lambda> ns" and
          "\<And>x. x \<in> range C \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
        shows "boogie_const_rel C \<Lambda> ns'"
  using assms
  unfolding boogie_const_rel_def
  by simp

fun lit_vpr_to_expr_bpl :: "(boogie_const \<Rightarrow> Lang.vname) \<Rightarrow> ViperLang.lit \<Rightarrow> boogie_expr"
  where
    "lit_vpr_to_expr_bpl C (ViperLang.LInt i) = Lit (Lang.LInt i)"
  | "lit_vpr_to_expr_bpl C (ViperLang.LBool i) = Lit (Lang.LBool i)"
  | "lit_vpr_to_expr_bpl C ViperLang.NoPerm = Var (C CNoPerm)"
  | "lit_vpr_to_expr_bpl C ViperLang.WritePerm = Var (C CWritePerm)"
  | "lit_vpr_to_expr_bpl C ViperLang.LNull = Var (C CNull)"

definition lit_translation_rel :: "'a econtext_bpl => ('a vbpl_absval) nstate \<Rightarrow> (ViperLang.lit \<Rightarrow> Lang.expr) \<Rightarrow> bool"
  where "lit_translation_rel ctxt ns litT \<equiv> (\<forall>lit e. litT lit = e \<longrightarrow> red_expr_bpl ctxt e ns (val_rel_vpr_bpl (val_of_lit lit)))"

lemma boogie_const_lit_rel:
  assumes "boogie_const_rel C (var_context ctxt) ns"
  shows "lit_translation_rel ctxt ns (lit_vpr_to_expr_bpl C)"
  unfolding lit_translation_rel_def
  apply ((rule allI | rule impI)+)
  apply (erule lit_vpr_to_expr_bpl.elims)
      apply (insert assms)
      apply (unfold boogie_const_rel_def)
  by (auto intro: RedVar RedLit)

definition disjoint_list :: " ('a set) list \<Rightarrow> bool"
  where "disjoint_list xs = (\<forall>i j. 0 \<le> i \<and> i < length xs \<and> 0 \<le> j \<and> j < length xs \<and> i \<noteq> j \<longrightarrow> disjnt (xs ! i) (xs ! j))"

definition store_rel :: "('a vbpl_absval) absval_ty_fun \<Rightarrow> var_context \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "store_rel A \<Lambda> Tr \<omega> ns \<equiv> 
          inj_on (var_translation Tr) (dom (var_translation Tr)) \<and>
          (\<forall> var_vpr var_bpl. var_translation Tr var_vpr = Some var_bpl \<longrightarrow> 
                        (\<exists>val_vpr ty_bpl.
                                     (get_store_total \<omega> var_vpr) = Some val_vpr \<and>
                                      lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                                      lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                                      type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl ))"

lemma store_rel_var_rel:
  assumes "store_rel A \<Lambda> Tr \<omega> ns" and
          "var_translation Tr var_vpr = Some var_bpl"
  shows "\<exists>val_vpr ty_bpl. ((get_store_total \<omega>) var_vpr) = Some val_vpr \<and>
                     lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                     lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                     type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl"
  using assms
  unfolding store_rel_def
  by auto

lemma store_rel_var_rel_2:
  assumes "store_rel A \<Lambda> Tr \<omega> ns" and
          "var_translation Tr var_vpr = Some var_bpl"
  shows "\<exists>val_vpr. ((get_store_total \<omega>) var_vpr) = Some val_vpr \<and>
                     lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr)"
  using assms store_rel_var_rel
  by blast
 
lemma store_rel_stable:
  assumes "store_rel A \<Lambda> Tr \<omega> ns" and
          "\<And>x. x \<in> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"          
        shows "store_rel A \<Lambda> Tr \<omega> ns'"
  using assms
  unfolding store_rel_def
  by (simp add: ranI)

lemma store_rel_var_tr_inj:
  assumes "store_rel A \<Lambda> Tr \<omega> ns"
  shows "inj_on (var_translation Tr) (dom (var_translation Tr))"
  using assms
  by (simp add: store_rel_def)

lemma store_rel_update:
  assumes 
       StoreRel: "store_rel A \<Lambda> Tr \<omega> ns" and 
       "v' = val_rel_vpr_bpl v" and
       VarTrX: "var_translation Tr x_vpr = Some x_bpl" and
       TyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
              "type_of_val A v' = ty"
   shows
       "store_rel A \<Lambda> Tr (update_var_total \<omega> x_vpr v) (update_var \<Lambda> ns x_bpl v')"
  unfolding store_rel_def
proof (rule conjI, insert StoreRel, fastforce simp: store_rel_def, (rule allI | rule impI)+)
  fix var_vpr var_bpl
  assume VarTr: "var_translation Tr var_vpr = Some var_bpl"
  show "\<exists>val_vpr ty_bpl.          
          get_store_total (update_var_total \<omega> x_vpr v) var_vpr = Some val_vpr \<and>
          lookup_var \<Lambda> (update_var \<Lambda> ns x_bpl v') var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
          lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
          type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl"
  proof (cases "var_vpr = x_vpr")
    case True
    show ?thesis 
      using VarTrX VarTr TyBpl
      by (fastforce simp: \<open>var_vpr = _\<close> \<open>v' = _\<close>  )
  next
    case False
    hence "x_bpl \<noteq> var_bpl" using store_rel_var_tr_inj[OF StoreRel] VarTr VarTrX
      by (metis domI inj_onD)
    with \<open>var_vpr \<noteq> x_vpr\<close> VarTr StoreRel obtain v_vpr ty_bpl where 
      "get_store_total (update_var_total \<omega> x_vpr v) var_vpr = Some v_vpr" and
      "lookup_var \<Lambda> (update_var \<Lambda> ns x_bpl v') var_bpl = Some (val_rel_vpr_bpl v_vpr)"
      "lookup_var_ty \<Lambda> var_bpl = Some ty_bpl" and
      "type_of_val A (val_rel_vpr_bpl v_vpr) = ty_bpl"
      unfolding store_rel_def
      by fastforce      
    then show ?thesis 
      by simp      
  qed
qed

definition field_rel :: "ViperLang.program \<Rightarrow> var_context \<Rightarrow> tr_vpr_bpl \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "field_rel Pr \<Lambda> Tr ns \<equiv> 
        (\<forall>f f_vty. declared_fields Pr f = Some f_vty \<longrightarrow> 
             has_Some (\<lambda>f_bpl. lookup_var \<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (field_translation Tr f))"

lemma field_rel_stable:
  assumes "field_rel Pr \<Lambda> Tr ns" and
          "\<And>x. x \<in> ran (field_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"          
        shows "field_rel Pr \<Lambda> Tr ns'"
  using assms
  unfolding field_rel_def
  by (metis (no_types, lifting) has_Some_mono_strong ranI)

definition state_rel0 :: "ViperLang.program \<Rightarrow> 
                          ('a vbpl_absval) absval_ty_fun \<Rightarrow> 
                          var_context \<Rightarrow> 
                          'a ty_repr_bpl \<Rightarrow> 
                          tr_vpr_bpl \<Rightarrow> 
                          'a full_total_state \<Rightarrow> 
                          ('a vbpl_absval) nstate \<Rightarrow> 
                          bool"
  where "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns \<equiv> 
         \<comment>\<open>Store relation (only Viper variables, auxiliaries are not included)\<close>
           store_rel A \<Lambda> Tr \<omega> ns \<and>           
          \<comment>\<open>Disjointness condition for variables tracked by the relation\<close>
           (disjoint_list [{heap_var Tr},
                      {mask_var Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr))]) \<and>
          \<comment>\<open>heap and mask relation\<close>
           heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega> ns \<and>
           mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega> ns \<and>
          \<comment>\<open>field relation\<close>
           field_rel Pr \<Lambda> Tr ns \<and>
          \<comment>\<open>Boogie constants relation\<close>
           boogie_const_rel (const_repr Tr) \<Lambda> ns \<and>
           \<comment>\<open>well-typedness of the Boogie state is used to show well-typedness of 
              Boogie expressions\<close>
           state_well_typed A \<Lambda> [] ns" 

lemma state_rel0_store_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns"
  shows "store_rel A \<Lambda> Tr \<omega> ns"
  using assms
  by (simp add: state_rel0_def)

lemma state_rel0_heap_var_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns"
  shows "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega> ns"
  using assms
  by (simp add: state_rel0_def)

lemma state_rel0_mask_var_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns"
  shows "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega> ns"
  using assms
  by (simp add: state_rel0_def)

lemma state_rel0_field_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns"
  shows "field_rel Pr \<Lambda> Tr ns"
  using assms
  by (simp add: state_rel0_def)

lemma state_rel0_boogie_const:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns" 
  shows "boogie_const_rel (const_repr Tr) \<Lambda> ns"
  using assms
  unfolding state_rel0_def
  by simp

lemma state_rel0_state_well_typed:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns" 
  shows "state_well_typed A \<Lambda> [] ns"
  using assms
  unfolding state_rel0_def
  by simp

lemma state_rel0_disj_mask_store:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns"
  shows "mask_var Tr \<notin> ran (var_translation Tr)"
proof -
    from assms have Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]"
      by (simp add: state_rel0_def)
    thus "mask_var Tr \<notin> ran (var_translation Tr)"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=1])
      apply (erule allE[where ?x=2])
      by simp      
qed

definition state_rel
  where "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>_def \<omega> ns \<equiv> 
          mask_var_rel Pr (var_context ctxt) TyRep Tr wd_mask_var \<omega> ns \<and>
          state_rel0 Pr (type_interp ctxt) (var_context ctxt) TyRep Tr \<omega> ns"

definition state_rel_empty
  where "state_rel_empty R \<omega> ns \<equiv> is_empty_total \<omega> \<and> R \<omega> ns"

lemma state_rel_state_rel0:
  assumes "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>_def \<omega> ns"
  shows "state_rel0 Pr (type_interp ctxt) (var_context ctxt) TyRep Tr \<omega> ns"
  using assms
  by (simp add: state_rel_def)

lemma state_rel_boogie_const:
  assumes "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>_def \<omega> ns" 
  shows "boogie_const_rel (const_repr Tr) (var_context ctxt) ns"
  using assms
  unfolding state_rel_def state_rel0_def
  by simp

lemmas state_rel_well_state_well_typed = state_rel0_state_well_typed[OF state_rel_state_rel0]

lemma lookup_disj_aux:
  assumes "\<And>x. x \<notin> M \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "disjnt M S"
        shows "\<And>x. x \<in> S \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
  using assms
  by (meson disjnt_iff)

lemma lookup_disj_aux_2:
  assumes "\<And>x. x \<noteq> y \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "y \<notin> S"
        shows "\<And>x. x \<in> S \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
  using assms
  by fastforce

lemma state_well_typed_upd_1:
  assumes StateWt: "state_well_typed A \<Lambda> \<Omega> ns" and 
          LookupTyEq: 
               "\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> 
                (\<exists>v1.  lookup_var \<Lambda> ns' x = Some v1 \<and>
                         type_of_val A v1 = instantiate \<Omega> t)" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
        shows "state_well_typed A \<Lambda> \<Omega> ns'"
  unfolding state_well_typed_def
proof (intro conjI)
  show "state_typ_wf A \<Omega> (local_state ns') (snd \<Lambda>)"
    unfolding state_typ_wf_def
  proof (rule allI | rule impI)+
    fix x t
    assume LookupTyLocal: "lookup_vdecls_ty (snd \<Lambda>) x = Some t"
    hence "lookup_var_ty \<Lambda> x = Some t"
      by (simp add: lookup_vdecls_ty_local_3)


    with LookupTyEq obtain v where
      "lookup_var \<Lambda> ns' x = Some v"  
      "type_of_val A v = instantiate \<Omega> t"
      by auto

    moreover with LookupTyLocal have "local_state ns' x = Some v"
      by (metis lookup_var_local lookup_vdecls_ty_map_of prod.exhaust_sel)


    ultimately show "map_option (type_of_val A) (local_state ns' x) = Some (instantiate \<Omega> t)"
      by simp
  qed
next
  show "state_typ_wf A \<Omega> (global_state ns') (fst \<Lambda>)"
    unfolding state_typ_wf_def
  proof (rule allI | rule impI)+
    fix x t
    assume LookupTyGlobal: "lookup_vdecls_ty (fst \<Lambda>) x = Some t"

    show "map_option (type_of_val A) (global_state ns' x) = Some (instantiate \<Omega> t)"
    proof (cases "map_of (snd \<Lambda>) x = None")
      case True
      with LookupTyGlobal have "lookup_var_ty \<Lambda> x = Some t"
        by (simp add: lookup_vdecls_ty_global_4)
      with LookupTyEq obtain v where
        "lookup_var \<Lambda> ns' x = Some v"  
        "type_of_val A v = instantiate \<Omega> t"
        by auto
      moreover with LookupTyGlobal have "global_state ns' x = Some v"
        by (metis True lookup_var_global surjective_pairing)
      ultimately show ?thesis
        by simp
    next
      case False
      hence "global_state ns' x = global_state ns x" using ShadowedGlobalsEq
        by auto
      then show ?thesis 
        using StateWt LookupTyGlobal
        unfolding state_well_typed_def state_typ_wf_def
        by auto
    qed
  qed
next
  show "state_typ_wf A \<Omega> (old_global_state ns') (fst \<Lambda>)"
    using StateWt OldStateEq
    unfolding state_well_typed_def
    by simp
next
  show "binder_state ns' = Map.empty"
    using StateWt BinderEmpty
    unfolding state_well_typed_def
    by simp
qed

lemma state_well_typed_upd_2:
  assumes  StateWt: "state_well_typed A \<Lambda> \<Omega> ns" and
          "\<And>t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> type_of_val A v = instantiate \<Omega> t"
        shows "state_well_typed A \<Lambda> \<Omega> (update_var \<Lambda> ns x v)"
  apply (rule state_well_typed_upd_1[OF StateWt])
  using StateWt 
    apply (simp add: assms(2) state_well_typed_lookup)
   apply (metis global_state_update_local global_state_update_other option.exhaust)
   apply (simp add: update_var_old_global_same)
  by (metis StateWt state_well_typed_def update_var_binder_same)
                   
lemma state_rel0_mask_update:
  assumes StateRel: "state_rel0 Pr (vbpl_absval_ty TyRep) \<Lambda> TyRep Tr \<omega> ns" and
          OnlyMaskAffected: "(\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
          MaskRel: "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega> ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
 shows "state_rel0 Pr (vbpl_absval_ty TyRep) \<Lambda> TyRep Tr \<omega> ns'"
proof -

  from StateRel have Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]"
    by (simp add: state_rel0_def)

  hence D1:"heap_var Tr \<noteq> mask_var Tr"
    unfolding disjoint_list_def
    by fastforce

  from Disj have D2: "mask_var Tr \<notin> ran (var_translation Tr)"
    unfolding disjoint_list_def
    apply (rule allE[where ?x= 1])
    apply (erule allE[where ?x= 2])
    by simp

  from Disj have D3: "mask_var Tr \<notin> ran (field_translation Tr)"
    unfolding disjoint_list_def
    apply (rule allE[where ?x= 1])
    apply (erule allE[where ?x= 3])
    by simp

  from Disj have D4: "mask_var Tr \<notin> range (const_repr Tr)"
    unfolding disjoint_list_def
    apply (rule allE[where ?x= 1])
    apply (erule allE[where ?x= 4])
    by simp

  have StateWt: "state_well_typed (vbpl_absval_ty TyRep) \<Lambda> [] ns"
    using state_rel0_state_well_typed[OF StateRel]
    by simp

  have LookupAux:
         "\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> \<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> 
                                                     type_of_val (vbpl_absval_ty TyRep) v1 = instantiate [] t"
  proof -
    fix x t 
    assume LookupTy: "lookup_var_ty \<Lambda> x = Some t"
    show "\<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> type_of_val (vbpl_absval_ty TyRep) v1 = instantiate [] t"
    proof (cases "x = mask_var Tr")
      case True      
      hence "t = TConSingle (TMaskId TyRep)"        
        by (metis LookupTy MaskRel mask_var_rel_def option.inject)
      obtain mb where LookupX: "lookup_var \<Lambda> ns' x = Some (AbsV (AMask mb))"
        using MaskRel
        apply (simp add: \<open>x = _\<close>)
        using mask_var_rel_def by blast        
      thus ?thesis
        by (simp add: \<open>t = _\<close>)                
    next
      case False
      hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" 
        using OnlyMaskAffected by simp    
      then show ?thesis using StateWt LookupTy
        by (metis state_well_typed_lookup)
    qed
  qed


  have StateWtUpd: "state_well_typed (vbpl_absval_ty TyRep) \<Lambda> [] ns'"
    apply (rule state_well_typed_upd_1[OF state_rel0_state_well_typed[OF StateRel]])
    apply (erule LookupAux)
    using ShadowedGlobalsEq OldStateEq BinderEmpty
    by auto

  show ?thesis
    unfolding state_rel0_def
    apply (intro conjI)
         apply (rule store_rel_stable)
    using StateRel 
          apply (fastforce simp: state_rel0_def)
    using lookup_disj_aux_2[OF _ D2] OnlyMaskAffected
         apply blast
    using StateRel 
        apply (fastforce simp: state_rel0_def)
       apply (rule heap_var_rel_stable)
    using StateRel 
         apply (fastforce simp: state_rel0_def)
        apply simp
    using D1 OnlyMaskAffected
        apply fastforce
      apply (rule MaskRel)
     apply (rule field_rel_stable)
    using StateRel 
      apply (fastforce simp: state_rel0_def)
    using lookup_disj_aux_2[OF _ D3]OnlyMaskAffected
     apply blast
    apply (rule boogie_const_rel_stable)
    using StateRel 
     apply (fastforce simp: state_rel0_def)
    using lookup_disj_aux_2[OF _ D4] OnlyMaskAffected
     apply blast
    apply (rule StateWtUpd)
    done
qed

lemma state_rel_mask_update:
  assumes StateRel: "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>_def \<omega> ns" and
          OnlyMaskAffected: "(\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ns' x)" and
          MaskRel : "mask_var_rel Pr (var_context ctxt) TyRep Tr (mask_var Tr) \<omega> ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty" and
          TypeInterp: "type_interp ctxt = (vbpl_absval_ty TyRep)"
        shows "state_rel Pr TyRep Tr ctxt (mask_var Tr) \<omega>_def \<omega> ns'"    
  using assms
  unfolding state_rel_def
  by (auto intro: state_rel0_mask_update)

lemma state_rel_mask_update_2:
  assumes StateRel: "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega> \<omega> ns" and 
          WdEq: "wd_mask_var = mask_var Tr" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) m'" and
          Eq: "mvar = mask_var Tr"
           "\<Lambda> = (var_context ctxt)" and
        TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
        shows "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega> \<omega> (update_var \<Lambda> ns mvar (AbsV (AMask m')))" 
                (is "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega> \<omega> ?ns'")
  apply (subst WdEq)
  apply (rule state_rel_mask_update)
    apply (rule StateRel)
   apply (metis update_var_other Eq )
  apply (unfold mask_var_rel_def)
  apply (rule exI[where ?x=m'])
      using MaskRel
      apply (simp add: Eq)
      using StateRel
          apply (metis WdEq mask_var_rel_def state_rel_def)
         apply (metis assms(5) global_state_update_local global_state_update_other option.exhaust)
        apply (simp add: update_var_old_global_same)
      using state_rel0_state_well_typed[OF state_rel_state_rel0[OF StateRel]]
      unfolding state_well_typed_def
      apply (simp add: update_var_binder_same)
      by (simp add: TypeInterp)

lemma state_rel0_store_update:
  assumes StateRel: "state_rel0 Pr A \<Lambda> TyRep Tr \<omega> ns" and
     OnlyStoreAffectedVpr: 
           "get_h_total_full \<omega> = get_h_total_full \<omega>'" 
           "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
     OnlyStoreAffectedBpl: "(\<And>x. x \<notin> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
     StoreRel: "store_rel A \<Lambda> Tr \<omega>' ns'" and
     ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
     OldStateEq: "old_global_state ns' = old_global_state ns" and
     BinderEmpty: "binder_state ns' = Map.empty"
   shows "state_rel0 Pr A \<Lambda> TyRep Tr \<omega>' ns'"
  unfolding state_rel0_def
  apply (intro conjI)
       apply (rule StoreRel)
  using StateRel 
      apply (simp add: state_rel0_def)
     apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel]])
  using OnlyStoreAffectedVpr apply simp
  subgoal
  proof -
    from StateRel have Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]"
      by (simp add: state_rel0_def)
    hence "heap_var Tr \<notin> ran (var_translation Tr)"
      unfolding disjoint_list_def
      by fastforce
    thus ?thesis
      using OnlyStoreAffectedBpl
      by blast
  qed
    apply (rule mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel]])
  using OnlyStoreAffectedVpr apply simp
  subgoal
  proof -
    have "mask_var Tr \<notin> ran (var_translation Tr)"
      by (simp add: state_rel0_disj_mask_store[OF StateRel])
    thus ?thesis
      using OnlyStoreAffectedBpl
      by blast
  qed
   apply (rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
   subgoal for x
   proof -
     assume FieldElem: "x \<in> ran (field_translation Tr)"
    from StateRel have Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]"
      by (simp add: state_rel0_def)
    hence "disjnt (ran (var_translation Tr)) (ran (field_translation Tr))"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=2])
      apply (erule allE[where ?x=3])
      by simp
    thus ?thesis
      using OnlyStoreAffectedBpl FieldElem lookup_disj_aux by blast
  qed
  apply (rule boogie_const_rel_stable[OF state_rel0_boogie_const[OF StateRel]])
  subgoal for x
  proof -
    assume ConstElem: "x \<in> range (const_repr Tr)"
    from StateRel have Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]"
      by (simp add: state_rel0_def)
    hence "disjnt (ran (var_translation Tr)) (range (const_repr Tr))"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=2])
      apply (erule allE[where ?x=4])
      by simp
    thus ?thesis
      using OnlyStoreAffectedBpl ConstElem lookup_disj_aux by blast
  qed
  subgoal
  proof -
    have StateWt: "state_well_typed A \<Lambda> [] ns"
      by (rule state_rel0_state_well_typed[OF StateRel])
    have LookupAux: 
          "\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> 
              \<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> type_of_val A v1 = instantiate [] t"
        (is "\<And>x t. ?P x t \<Longrightarrow> ?Q x t")
    proof -
      fix x t 
      assume LookupTy:"lookup_var_ty \<Lambda> x = Some t"
      show "?Q x t"
      proof (cases "x \<in> ran (var_translation Tr)")
        case True
        from this obtain x_vpr where "var_translation Tr x_vpr = Some x"          
          by (auto simp add: ran_def)          
        with LookupTy obtain v where
          "lookup_var \<Lambda> ns' x = Some v" and 
          "type_of_val A v = t"
          using store_rel_var_rel[OF StoreRel]
          by fastforce          
        then show ?thesis
          by simp        
      next
        case False
        hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
          using OnlyStoreAffectedBpl
          by simp
        then show ?thesis using StateWt LookupTy
          by (metis state_well_typed_lookup)
      qed
    qed


    show "state_well_typed A \<Lambda> [] ns'"
      apply (rule state_well_typed_upd_1)
          apply (rule state_rel0_state_well_typed[OF StateRel])
      apply (erule LookupAux)
      using ShadowedGlobalsEq OldStateEq BinderEmpty      
      by auto
  qed
  done

lemma state_rel_store_update:
  assumes StateRel: "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega> \<omega> ns" and
          WdEq: "wd_mask_var = mask_var Tr" and
          VarCtxt: "var_context ctxt = \<Lambda>" and
     OnlyStoreAffectedVpr: 
           "get_h_total_full \<omega> = get_h_total_full \<omega>'" 
           "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
     OnlyStoreAffectedBpl: "(\<And>x. x \<notin> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
     ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
     OldStateEq: "old_global_state ns' = old_global_state ns" and
     BinderEmpty: "binder_state ns' = Map.empty" and
     StoreRel: "store_rel (type_interp ctxt) \<Lambda> Tr \<omega>' ns'"
   shows "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>' \<omega>' ns'"  
  unfolding state_rel_def
  apply (subst WdEq)
  apply (rule conjI)
   apply (rule mask_var_rel_stable)
     apply (rule state_rel0_mask_var_rel[OF state_rel_state_rel0[OF StateRel]])
  using OnlyStoreAffectedVpr apply simp
  using state_rel0_disj_mask_store[OF state_rel_state_rel0[OF StateRel]] OnlyStoreAffectedBpl
   apply (simp add: VarCtxt)
  using assms
  by (auto intro: state_rel0_store_update[OF state_rel_state_rel0[OF StateRel]])

lemma state_rel_store_update_2:
  assumes 
         StateRel: "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega> \<omega> ns" and
          WdEq: "wd_mask_var = mask_var Tr" and
         VarCtxt: "\<Lambda> = var_context ctxt" and
         VarTr: "var_translation Tr x_vpr = Some x_bpl" and
         "v' = val_rel_vpr_bpl v" and
      TyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
              "type_of_val (type_interp ctxt) v' = ty"
       shows "state_rel Pr TyRep Tr ctxt wd_mask_var (update_var_total \<omega> x_vpr v) (update_var_total \<omega> x_vpr v) (update_var \<Lambda> ns x_bpl v')"  
  apply (rule state_rel_store_update[OF StateRel])
  using assms ranI state_rel0_store_rel[OF state_rel_state_rel0[OF StateRel]]
       apply (simp add: WdEq)
      apply (simp add: VarCtxt)
     apply simp
    apply simp
  using VarCtxt VarTr ranI apply fastforce
     apply (metis VarCtxt global_state_update_local global_state_update_other option.exhaust)
    apply (simp add: update_var_old_global_same)
   using state_rel0_state_well_typed[OF state_rel_state_rel0[OF StateRel]]
   unfolding state_well_typed_def
    apply (simp add: update_var_binder_same)   
   using state_rel0_store_rel[OF state_rel_state_rel0[OF StateRel]] assms store_rel_update
   by blast

subsection\<open>function relation\<close>

(* TODO: maybe make parametric *)
definition eval_heap_dep_bpl_fun :: "('a vbpl_absval) Semantics.fun_repr \<Rightarrow> ('a vbpl_val) list \<Rightarrow> 'a vbpl_val \<rightharpoonup> 'a vbpl_val"
  where "eval_heap_dep_bpl_fun f_bpl vs heap \<equiv> f_bpl [] (heap#vs)"
\<comment>\<open>If define \<^const>\<open>eval_heap_dep_bpl_fun\<close> as an abbreviation, then also terms like "state [] [heap,mask]" 
   will be displayed using the abbreviation in proof goals.\<close>

definition fun_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a TotalExpressions.heapfun_repr \<Rightarrow> ('a vbpl_absval) Semantics.fun_repr \<Rightarrow> bool"
  where "fun_rel Pr tr_field f_vpr f_bpl \<equiv> 
           (\<forall>vs \<omega> v_vpr. f_vpr vs \<omega> = Some (Val v_vpr) \<longrightarrow>
              (\<forall> h_bpl. heap_rel Pr tr_field (get_hh_total_full \<omega>) h_bpl \<longrightarrow>
                has_Some (\<lambda>v_bpl. val_rel_vpr_bpl v_vpr = v_bpl) (eval_heap_dep_bpl_fun f_bpl ((map val_rel_vpr_bpl) vs) (AbsV (AHeap h_bpl)))))"

definition fun_interp_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (ViperLang.function_ident \<rightharpoonup> Lang.fname) \<Rightarrow> 'a TotalExpressions.total_context \<Rightarrow> ('a vbpl_absval) Semantics.fun_interp \<Rightarrow> bool"
  where 
    "fun_interp_rel Pr tr_field tr_fun ctxt_vpr \<Gamma> \<equiv> (\<forall>fid f_vpr. fun_interp_total ctxt_vpr fid = Some f_vpr \<longrightarrow>
                                 (\<forall>fid_bpl. tr_fun fid = Some fid_bpl \<longrightarrow>
                                   has_Some (\<lambda>f_bpl. fun_rel Pr tr_field f_vpr f_bpl) (\<Gamma> fid_bpl)))"

definition tr_wf 
  where "tr_wf Pr ctxt_vpr ctxt tyrep Tr  \<equiv> 
           fun_interp_rel Pr (field_translation Tr) (fun_translation Tr) ctxt_vpr (fun_interp ctxt) \<and>
           heap_read_wf tyrep ctxt (heap_read Tr) \<and>
           mask_read_wf tyrep ctxt (mask_read Tr)"

fun block_from_config :: "'a ast_config \<Rightarrow> bigblock"
  where "block_from_config c = fst c"

fun cont_from_config :: "'a ast_config \<Rightarrow> cont"
  where "cont_from_config c = fst (snd c)"

fun state_from_config :: "'a ast_config \<Rightarrow> 'a state"
  where "state_from_config c = snd (snd c)"

subsection \<open>Boogie AST\<close>

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

type_synonym 'a vast_config = "(bigblock * cont) * ('a vbpl_absval) state"

text \<open>
 We define a single step relation on big blocks based on \<^const>\<open>red_bigblock\<close>, where only a single 
simple command reduces in a single step (contrary to \<^const>\<open>red_bigblock\<close>, where all simple commands 
of the same big block reduce in a single step).
\<close>
inductive red_bigblock_small :: "ast \<Rightarrow> 'a econtext_bpl \<Rightarrow> 'a vast_config \<Rightarrow> 'a vast_config \<Rightarrow> bool"
  for P ctxt
  where 
    RedBigBlockSmallSimpleCmd [intro]: 
      "\<lbrakk> (type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), [] \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s' \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt (((BigBlock name (c#cs) str tr), cont), s) (((BigBlock name cs str tr), cont), s')"
   | RedBigBlockSmallNoSimpleCmdOneStep [intro]: 
    "\<lbrakk> red_bigblock (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) [] P (BigBlock name [] str tr, cont, s) (b', cont', s') \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt ((BigBlock name [] str tr, cont), s) ((b', cont'), s')"

abbreviation red_bigblock_small_multi :: "ast \<Rightarrow> 'a econtext_bpl \<Rightarrow> 'a vast_config \<Rightarrow> 'a vast_config \<Rightarrow> bool"
  where "red_bigblock_small_multi P ctxt \<equiv> rtranclp (red_bigblock_small P ctxt)"

text \<open>We order the arguments of an AST config such that the syntactic part (bigblock + continuation) is the 
first element s.t. one can easily construct an AST configuration from the syntactic part and the state\<close>                                                                                                                                 

definition red_ast_bpl :: "ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>'a vast_config \<Rightarrow> 'a vast_config \<Rightarrow> bool"
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

type_synonym viper_stmt = ViperLang.stmt

subsection \<open>syntactic relations\<close>

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
  assumes "heap_read_wf T ctxt hread" and
          "h r f = Some v" and
          "red_expr_bpl ctxt e_heap ns (AbsV (AHeap h))" and 
          "vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[])" and
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  shows "red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v"
  using assms
  unfolding heap_read_wf_def
  by blast

lemma mask_read_wf_apply:
  assumes "mask_read_wf T ctxt mread" and
          "m r f = p" and
          "red_expr_bpl ctxt e_mask ns (AbsV (AMask m))"and 
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  shows "red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns (RealV p)"
  using assms
  unfolding mask_read_wf_def
  by blast

end