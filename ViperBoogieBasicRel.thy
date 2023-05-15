section \<open>Semantic relationship between basic Viper and Boogie constructs\<close>
theory ViperBoogieBasicRel
imports TotalExpressions TotalSemantics ViperBoogieAbsValueInst BoogieInterface "HOL-Library.Disjoint_Sets" 
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
                                             
type_synonym 'a bpl_heap_ty = "ref \<times> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"
type_synonym 'a bpl_mask_ty = "ref \<times> 'a vb_field \<Rightarrow> real"

datatype boogie_const =      
       CNoPerm
     | CWritePerm
     | CNull     
     | CZeroMask
     | CKnownFoldedZeroMask
     | CEmptyFrame     

definition total_context_trivial :: "program \<Rightarrow> 'a total_context"
  where "total_context_trivial Pr \<equiv> \<lparr> program_total = Pr, fun_interp_total=f_None, absval_interp_total=(\<lambda>_.''dummy'')  \<rparr>"

text \<open>The following record abstracts over elements in the Boogie encoding that are used to represent
Viper counterparts.\<close>

record tr_vpr_bpl =
  heap_var :: Lang.vname
  mask_var :: Lang.vname
  heap_var_def :: Lang.vname
  mask_var_def :: Lang.vname
  mask_read :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: mask, receiver, field, field type arguments\<close>
  mask_update :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: mask, receiver, field, new value, field type arguments\<close>
  heap_read :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field, field type arguments\<close>
  heap_update :: "boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr" \<comment>\<open>arguments: heap, receiver, field, new value, field type arguments\<close>
  field_translation :: "field_ident \<rightharpoonup> Lang.vname"
  fun_translation :: "ViperLang.function_ident \<rightharpoonup> Lang.fname"
  var_translation :: "ViperLang.var \<rightharpoonup> Lang.vname" \<comment>\<open>local Boogie variables\<close>
  const_repr :: "boogie_const \<Rightarrow> Lang.vname"
  
 (*TODO: bound vars*)
(*  result_var :: "string" *)

lemma tr_def_field_translation:
  assumes "tr = tr_def" and
          "field_translation tr_def = F"
        shows "field_translation tr = F"
  using assms by simp

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

\<comment> \<open>TODO: rename econtext_bpl to indicate Viper instantation\<close>
type_synonym 'a econtext_bpl = "('a vbpl_absval) econtext_bpl_general"

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
    \<forall> l field_ty_vpr field_bpl. declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
                                tr_field (snd l) = Some field_bpl \<longrightarrow>
                                hb (Address (fst l), NormalField field_bpl field_ty_vpr) = Some (val_rel_vpr_bpl (h l))"

lemma heap_rel_intro:
  assumes "\<And>l field_ty_vpr field_bpl. 
             declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
             tr_field (snd l) = Some field_bpl \<Longrightarrow> 
             hb (Address (fst l), NormalField field_bpl field_ty_vpr) = Some (val_rel_vpr_bpl (h l))"
  shows "heap_rel Pr tr_field h hb"
  using assms
  unfolding heap_rel_def 
  by blast

lemma heap_rel_elim:
  assumes "heap_rel Pr tr_field h hb" and
          "(\<And>l field_ty_vpr field_bpl. 
                declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
                tr_field (snd l) = Some field_bpl \<Longrightarrow> 
                hb (Address (fst l), NormalField field_bpl field_ty_vpr) = Some (val_rel_vpr_bpl (h l))) \<Longrightarrow> 
                P"
        shows P
  using assms
  unfolding heap_rel_def
  by blast
                                               
definition vpr_heap_locations_bpl :: "program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (ref \<times> 'a vb_field) set"
  where "vpr_heap_locations_bpl Pr tr_field \<equiv> 
            { (a_bpl,f_bpl). (\<exists>field_bpl heap_loc field_ty_vpr. 
                               a_bpl = Address (fst heap_loc) \<and>
                               f_bpl = NormalField field_bpl field_ty_vpr \<and>
                               declared_fields Pr (snd heap_loc) = Some field_ty_vpr \<and> 
                               tr_field (snd heap_loc) = Some field_bpl) }"

lemma heap_rel_stable:
  assumes "heap_rel Pr tr_field h hb"
  shows "\<And> hb'. (\<forall> loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field. hb loc_bpl = hb' loc_bpl) \<Longrightarrow> heap_rel Pr tr_field h hb'"
  using assms
  unfolding heap_rel_def vpr_heap_locations_bpl_def
  by (metis (mono_tags, lifting) case_prodI mem_Collect_eq)  

lemma split_fun_aux:
  shows "\<exists> hb'. (\<forall> loc_bpl. P loc_bpl \<longrightarrow> hb' loc_bpl = hb0 loc_bpl) \<and>
                (\<forall> loc_bpl. \<not> P loc_bpl \<longrightarrow> hb' loc_bpl = hb1 loc_bpl)"
proof -
  let ?hb' = "\<lambda>loc_bpl. if P loc_bpl then hb0 loc_bpl else hb1 loc_bpl"
  show ?thesis
    apply (rule exI[where ?x="?hb'"])
    by auto
qed

lemma heap_rel_stable_2:
  assumes "heap_rel Pr tr_field h hb0"
  shows "\<exists> hb'. heap_rel Pr tr_field h hb' \<and>
                (\<forall> loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field. hb' loc_bpl = hb0 loc_bpl) \<and>
                (\<forall> loc_bpl. loc_bpl \<notin> vpr_heap_locations_bpl Pr tr_field \<longrightarrow> hb' loc_bpl = hb1 loc_bpl)"
  using split_fun_aux[where ?P = "\<lambda>loc_bpl. loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field"]
        heap_rel_stable[OF assms] 
  by (metis (full_types))

lemma heap_rel_stable_2_well_typed:
  assumes "heap_rel Pr tr_field h hb0" and
        Heap0WellTy: "vbpl_absval_ty_opt TyRep (AHeap hb0) = Some (THeapId TyRep, [])" and
        Heap1WellTy:  "vbpl_absval_ty_opt TyRep (AHeap hb1) = Some (THeapId TyRep, [])"
shows "\<exists> hb'. heap_rel Pr tr_field h hb' \<and>
              vbpl_absval_ty_opt TyRep (AHeap hb') = Some (THeapId TyRep, []) \<and>
                (\<forall> loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field. hb' loc_bpl = hb0 loc_bpl) \<and>
                (\<forall> loc_bpl. loc_bpl \<notin> vpr_heap_locations_bpl Pr tr_field \<longrightarrow> hb' loc_bpl = hb1 loc_bpl)"
proof -
  from split_fun_aux[where ?P = "\<lambda>loc_bpl. loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field"] obtain hb'
    where HeapProperties:
          "(\<forall>loc_bpl. loc_bpl \<in> vpr_heap_locations_bpl Pr tr_field \<longrightarrow> hb' loc_bpl = hb0 loc_bpl)"
          "(\<forall>loc_bpl. loc_bpl \<notin> vpr_heap_locations_bpl Pr tr_field \<longrightarrow> hb' loc_bpl = hb1 loc_bpl)"
    by blast

  hence "heap_rel Pr tr_field h hb'"
    using heap_rel_stable[OF assms(1)] 
    by metis

  moreover have "vbpl_absval_ty_opt TyRep (AHeap hb') = Some (THeapId TyRep, [])"
  proof (rule heap_bpl_well_typed)
    fix r f fieldKind t v
    assume FieldTy: "field_ty_fun_opt TyRep f = Some (TFieldId TyRep, [fieldKind, t])" and
           "hb' (r, f) = Some v"

    thus "type_of_vbpl_val TyRep v = t"
    proof (cases "(r,f) \<in> vpr_heap_locations_bpl Pr tr_field")
      case True
      hence "hb0 (r,f) = Some v"
        using HeapProperties \<open>hb' (r, f) = Some v\<close>
        by simp
      with True show ?thesis
        using Heap0WellTy FieldTy          
        by (metis heap_bpl_well_typed_elim)
    next
      case False
      hence "hb1 (r,f) = Some v"
        using HeapProperties \<open>hb' (r, f) = Some v\<close>
        by simp
      with False show ?thesis
        using Heap1WellTy FieldTy          
        by (metis heap_bpl_well_typed_elim)
    qed
  qed

  ultimately show ?thesis
    using HeapProperties
    by blast
qed

definition mask_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> mask \<Rightarrow> 'a bpl_mask_ty \<Rightarrow> bool"
  where "mask_rel Pr tr_field m mb \<equiv> 
    (\<forall> l field_ty_vpr field_bpl. declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
                      tr_field (snd l) = Some field_bpl \<longrightarrow>
                      mb (Address (fst l), NormalField field_bpl field_ty_vpr) = real_of_rat (Rep_prat (m l)))
 \<and>  (\<forall>f t. mb (Null, NormalField f t) = 0)"

lemma mask_rel_intro:
  assumes "\<And>l field_ty_vpr field_bpl. 
             declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
             tr_field (snd l) = Some field_bpl \<Longrightarrow> 
             mb (Address (fst l), NormalField field_bpl field_ty_vpr) = real_of_rat (Rep_prat (m l))" and
          "\<And> f t. mb (Null, NormalField f t) = 0"
  shows "mask_rel Pr tr_field m mb"
  using assms
  unfolding mask_rel_def 
  by blast

lemma mask_rel_elim:
  assumes "mask_rel Pr tr_field m mb" and
          "(\<And>l field_ty_vpr field_bpl. 
                declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
                tr_field (snd l) = Some field_bpl \<Longrightarrow> 
                mb (Address (fst l), NormalField field_bpl field_ty_vpr) = real_of_rat (Rep_prat (m l))) \<Longrightarrow> 
                P"
        shows P
  using assms
  unfolding mask_rel_def
  by blast

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
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> h (r, f) = Some v \<and>
          field_ty_fun_opt T f = Some (field_tcon, ty_args) ) \<longrightarrow>
            red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

lemma heap_read_wf_apply:
  assumes "heap_read_wf T ctxt hread" and
          "h (r, f) = Some v" and
          "red_expr_bpl ctxt e_heap ns (AbsV (AHeap h))" and 
          "vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[])" and
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  shows "red_expr_bpl ctxt (hread e_heap e_rcv e_f ty_args) ns v"
  using assms
  unfolding heap_read_wf_def
  by blast

definition heap_update_wf :: "'a ty_repr_bpl \<Rightarrow> 'a econtext_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "heap_update_wf T ctxt hupdate \<equiv> \<forall> e_heap e_rcv e_f e_new_val h r f ns new_val field_tcon ty_args. 
         ( (red_expr_bpl ctxt e_heap ns (AbsV (AHeap h)) \<and>
            vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[]) \<and>
            red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
            red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and>          
            field_ty_fun_opt T f = Some (field_tcon, ty_args) \<and>
            red_expr_bpl ctxt e_new_val ns new_val \<and>
            type_of_vbpl_val T new_val = ty_args ! 1 ) \<longrightarrow>
            red_expr_bpl ctxt (hupdate e_heap e_rcv e_f e_new_val ty_args) ns (AbsV (AHeap (h((r,f) \<mapsto> new_val ))))
         ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (hupdate e_heap e_rcv e_f e_new_val ty_args) ns v) \<longrightarrow>
           (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) \<and>
            (\<exists>v. red_expr_bpl ctxt e_new_val ns v) )"

lemma heap_update_wf_apply:
  assumes "heap_update_wf T ctxt hupdate" and
          "red_expr_bpl ctxt e_heap ns (AbsV (AHeap h))" and
          "vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[])" and
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and 
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)" and 
          "red_expr_bpl ctxt e_new_val ns new_val" and
          "type_of_vbpl_val T new_val = ty_args ! 1"
  shows "red_expr_bpl ctxt (hupdate e_heap e_rcv e_f e_new_val ty_args) ns (AbsV (AHeap (h((r,f) \<mapsto> new_val ))))"
  using assms
  unfolding heap_update_wf_def
  by blast

definition mask_read_wf :: "'a ty_repr_bpl \<Rightarrow> 'a econtext_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "mask_read_wf T ctxt mread \<equiv> \<forall> e_mask e_rcv e_f m r f ns v field_tcon ty_args.
         ( (red_expr_bpl ctxt e_mask ns (AbsV (AMask m)) \<and> 
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and> m (r, f) = v \<and>
          field_ty_fun_opt T f = Some (field_tcon, ty_args)) \<longrightarrow>
            red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns (RealV v) ) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

lemma mask_read_wf_apply:
  assumes "mask_read_wf T ctxt mread" and
          "m (r, f) = p" and
          "red_expr_bpl ctxt e_mask ns (AbsV (AMask m))"and 
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  shows "red_expr_bpl ctxt (mread e_mask e_rcv e_f ty_args) ns (RealV p)"
  using assms
  unfolding mask_read_wf_def
  by blast

definition mask_update_wf :: "'a ty_repr_bpl \<Rightarrow> 'a econtext_bpl \<Rightarrow> (boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> boogie_expr) \<Rightarrow> bool"
  where 
    "mask_update_wf T ctxt mupdate \<equiv> \<forall> e_mask e_rcv e_f e_p m r f p ns field_tcon ty_args.
         ( (red_expr_bpl ctxt e_mask ns (AbsV (AMask m)) \<and> 
          red_expr_bpl ctxt e_rcv ns (AbsV (ARef r)) \<and>
          red_expr_bpl ctxt e_f ns (AbsV (AField f)) \<and>
          red_expr_bpl ctxt e_p ns (RealV p)  \<and>
          field_ty_fun_opt T f = Some (field_tcon, ty_args)) \<longrightarrow>
            red_expr_bpl ctxt (mupdate e_mask e_rcv e_f e_p ty_args) ns (AbsV (AMask (m((r,f) := p))))) \<and>
         ( (\<exists>v. red_expr_bpl ctxt (mupdate e_mask e_rcv e_f e_p ty_args) ns v) \<longrightarrow>
             (\<exists>v. red_expr_bpl ctxt e_rcv ns v) \<and> (\<exists>v. red_expr_bpl ctxt e_f ns v) )"

lemma mask_update_wf_apply:
  assumes "mask_update_wf T ctxt mupdate" and       
          "red_expr_bpl ctxt e_mask ns (AbsV (AMask m))"and 
          "red_expr_bpl ctxt e_rcv ns (AbsV (ARef r))" and
          "red_expr_bpl ctxt e_f ns (AbsV (AField f))" and      
          "red_expr_bpl ctxt e_new_perm ns (RealV p)" and
          "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  shows "red_expr_bpl ctxt (mupdate e_mask e_rcv e_f e_new_perm ty_args) ns (AbsV (AMask (m( (r,f) := p ))))"
  using assms
  unfolding mask_update_wf_def
  by blast

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
  assumes "heap_var_rel Pr \<Lambda> TyRep Tr hvar \<omega> ns" and
          "get_hh_total_full \<omega> = get_hh_total_full \<omega>'" and
          "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar" and
          "field_translation Tr = field_translation Tr'"
        shows "heap_var_rel Pr \<Lambda> TyRep Tr' hvar \<omega>' ns'"
  using assms
  unfolding heap_var_rel_def
  by auto

lemma mask_var_rel_stable:
  assumes "mask_var_rel Pr \<Lambda> TyRep Tr mvar \<omega>' ns"
          "get_mh_total_full \<omega> = get_mh_total_full \<omega>'"
          "lookup_var \<Lambda> ns mvar = lookup_var \<Lambda> ns' mvar" and
          "field_translation Tr = field_translation Tr'"
        shows "mask_var_rel Pr \<Lambda> TyRep Tr' mvar \<omega> ns'"
  using assms
  unfolding mask_var_rel_def
  by auto
                           
abbreviation zero_mask_bpl :: "ref \<times> 'a vb_field \<Rightarrow> real"
  where "zero_mask_bpl \<equiv> \<lambda> _. 0"

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
  | "boogie_const_val CKnownFoldedZeroMask = AbsV (AKnownFoldedMask (\<lambda> _. False))"
  | "boogie_const_val CEmptyFrame = AbsV (AFrame EmptyFrame)"

fun boogie_const_ty :: "'a ty_repr_bpl \<Rightarrow> boogie_const => bpl_ty"
  where
    "boogie_const_ty T CNoPerm = TPrim TReal"
  | "boogie_const_ty T CWritePerm = TPrim TReal"
  | "boogie_const_ty T CNull = TConSingle (TRefId T)"
  | "boogie_const_ty T CZeroMask = TConSingle (TMaskId T)"
  | "boogie_const_ty T CKnownFoldedZeroMask = TConSingle (TKnownFoldedMaskId T)"
  | "boogie_const_ty T CEmptyFrame = TConSingle (TFrameFragmentId T)"


lemma boogie_const_val_well_ty: "type_of_vbpl_val T (boogie_const_val c) = boogie_const_ty T c"  
  by (cases c) auto

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
  assumes "store_rel A \<Lambda> Tr \<omega> ns"
          "get_store_total \<omega> = get_store_total \<omega>'"
          "\<And>x. x \<in> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "var_translation Tr = var_translation Tr'"
        shows "store_rel A \<Lambda> Tr' \<omega>' ns'"
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
        (inj_on (field_translation Tr) (dom (field_translation Tr))) \<and>
        (\<forall>f f_vty. declared_fields Pr f = Some f_vty \<longrightarrow> 
             has_Some (\<lambda>f_bpl. lookup_var \<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (field_translation Tr f))"

lemma field_rel_stable:
  assumes "field_rel Pr \<Lambda> Tr ns" and
          "\<And>x. x \<in> ran (field_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "field_translation Tr = field_translation Tr'"
        shows "field_rel Pr \<Lambda> Tr' ns'"
  using assms
  unfolding field_rel_def
  by (metis (no_types, lifting) has_Some_mono_strong ranI)

type_synonym 'a aux_vars_pred = "Lang.vname \<rightharpoonup> ('a vbpl_val \<Rightarrow> bool)"

definition aux_vars_pred_sat :: "var_context \<Rightarrow> 'a aux_vars_pred \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "aux_vars_pred_sat \<Lambda> AuxPred ns = (\<forall> x P. AuxPred x = Some P \<longrightarrow> has_Some (\<lambda>v. P v) (lookup_var \<Lambda> ns x))"

lemma aux_vars_pred_sat_stable:
  assumes  "aux_vars_pred_sat \<Lambda> AuxPred ns"
           "\<And>x. x \<in> dom AuxPred \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
         shows "aux_vars_pred_sat \<Lambda> AuxPred ns'"
  using assms
  unfolding aux_vars_pred_sat_def
  by (simp add: domI)

lemma aux_vars_pred_sat_update:
  assumes "aux_vars_pred_sat (var_context ctxt) AuxPred ns" and
          "P aux_val"
  shows "aux_vars_pred_sat (var_context ctxt) (AuxPred(aux_var \<mapsto> P)) 
                                               (update_var (var_context ctxt) ns aux_var aux_val)"
  unfolding aux_vars_pred_sat_def
proof (rule allI | rule impI)+
  fix x p
  assume "(AuxPred(aux_var \<mapsto> P)) x = Some p"
  show "has_Some p (lookup_var (var_context ctxt) (update_var (var_context ctxt) ns aux_var aux_val) x)"
  proof (cases "aux_var = x")
    case True
    then show ?thesis 
      using \<open>P aux_val\<close> \<open>(AuxPred(aux_var \<mapsto> P)) x = Some p\<close> by auto
  next
    case False
    then show ?thesis
      using  \<open>(AuxPred(aux_var \<mapsto> P)) x = Some p\<close>
      by (metis assms(1) aux_vars_pred_sat_def map_upd_Some_unfold update_var_other)
  qed
qed


definition state_rel0 :: "ViperLang.program \<Rightarrow> 
                          ('a vbpl_absval) absval_ty_fun \<Rightarrow> 
                          var_context \<Rightarrow> 
                          'a ty_repr_bpl \<Rightarrow> 
                          tr_vpr_bpl \<Rightarrow> 
                          'a aux_vars_pred \<Rightarrow> 
                          'a full_total_state \<Rightarrow>                   
                          'a full_total_state \<Rightarrow>
                          ('a vbpl_absval) nstate \<Rightarrow> 
                          bool"
  where "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns \<equiv> 
         \<comment>\<open>field permissions can be at most one\<close>
            wf_mask_simple (get_mh_total_full \<omega>def) \<and>
            wf_mask_simple (get_mh_total_full \<omega>) \<and>
         \<comment>\<open>type interpretation must be the expected one\<close>
           (A = vbpl_absval_ty TyRep) \<and>
         \<comment>\<open>Store relation (only Viper variables, auxiliaries are not included)\<close>
           store_rel A \<Lambda> Tr \<omega> ns \<and>           
          \<comment>\<open>Disjointness condition for variables tracked by the relation\<close>
           (disjoint_list [{heap_var Tr, heap_var_def Tr},
                      {mask_var Tr, mask_var_def Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr)),
                      dom AuxPred]) \<and>
          \<comment>\<open>well-def state and evaluation state differ only on mask\<close>
           (
             get_store_total \<omega>def = get_store_total \<omega> \<and>
             get_trace_total \<omega>def = get_trace_total \<omega> \<and>
             get_h_total_full \<omega>def = get_h_total_full \<omega>
           ) \<and>
          \<comment>\<open>heap and mask relation for evaluation state\<close>
           heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega> ns \<and>
           mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega> ns \<and> 
          \<comment>\<open>heap and mask relation for well-definedness state\<close>
           heap_var_rel Pr \<Lambda> TyRep Tr (heap_var_def Tr) \<omega>def ns \<and>
           mask_var_rel Pr \<Lambda> TyRep Tr (mask_var_def Tr) \<omega>def ns \<and>      
          \<comment>\<open>field relation\<close>
           field_rel Pr \<Lambda> Tr ns \<and>
          \<comment>\<open>Boogie constants relation\<close>
           boogie_const_rel (const_repr Tr) \<Lambda> ns \<and>
           \<comment>\<open>Boogie state is well-typed (used to show well-typedness of Boogie expressions)\<close>
           state_well_typed A \<Lambda> [] ns \<and>
           \<comment>\<open>auxiliary variable constraints are satisfied\<close>
           aux_vars_pred_sat \<Lambda> AuxPred ns"

definition state_rel
  where "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<equiv> 
          state_rel0 Pr (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"

abbreviation state_rel_def_same
  where "state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega> ns \<equiv> state_rel Pr TyRep Tr AuxPred ctxt \<omega> \<omega> ns"

definition state_rel_empty
  where "state_rel_empty R \<omega> ns \<equiv> is_empty_total \<omega> \<and> R \<omega> ns"

subsection \<open>Tactics\<close>

text \<open>This tactic enumerates all options for the integer quantifier in the generated premise from 0 
      to 5. Note that the tactic uses \<open>rename_tac\<close> and there the tactic may fail if certain variable
      names are in the goal.\<close>
method disjoint_list_subset_tac uses DisjointListAssm  = 
(rule disjoint_list_subset[OF DisjointListAssm],
  simp,
  simp,

  rename_tac i0,
  case_tac i0,
  simp,

  rename_tac i1,
  case_tac i1,
  simp,
  
  rename_tac i2,
  case_tac i2,
  simp      ,
  
  rename_tac i3,
  case_tac i3,
  simp,
  
  rename_tac i4,
  case_tac i4,
  simp,
  
  rename_tac i5,
  case_tac i5,
  simp,
  
  blast)

subsection \<open>State relationship properties\<close>

abbreviation state_rel_ext
  where "state_rel_ext R \<omega>def \<omega> ns \<equiv> R \<omega> ns \<and> \<omega>def = \<omega>"

lemma state_rel_state_rel0:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  shows "state_rel0 Pr (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"
  using assms
  by (simp add: state_rel_def)

lemma state_rel0_wf_mask_simple:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "wf_mask_simple (get_mh_total_full \<omega>)"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_wf_mask_simple = state_rel0_wf_mask_simple[OF state_rel_state_rel0]

lemma state_rel0_wf_mask_def_simple:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "wf_mask_simple (get_mh_total_full \<omega>def)"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_wf_mask_def_simple = state_rel0_wf_mask_def_simple[OF state_rel_state_rel0]

lemma state_rel0_type_interp:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "A = vbpl_absval_ty TyRep"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_type_interp = state_rel0_type_interp[OF state_rel_state_rel0]

lemma state_rel0_store_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "store_rel A \<Lambda> Tr \<omega> ns"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_store_rel = state_rel0_store_rel[OF state_rel_state_rel0]

lemma state_rel0_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "(disjoint_list [{heap_var Tr, heap_var_def Tr},
                      {mask_var Tr, mask_var_def Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr)),
                      dom AuxPred])"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_disjoint = state_rel0_disjoint[OF state_rel_state_rel0]

lemma heap_var_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          "hvar = heap_var_def Tr \<or> hvar = heap_var Tr"
  shows "hvar \<noteq> mask_var Tr \<and> hvar \<noteq> mask_var_def Tr \<and> hvar \<notin> ran (var_translation Tr) \<and>
         hvar \<notin> ran (field_translation Tr) \<and> hvar \<notin> range (const_repr Tr) \<and>
         hvar \<notin> dom AuxPred"
  apply (intro conjI)
  using state_rel0_disjoint[OF assms(1)] assms(2)
  apply (unfold disjoint_list_def)
       apply (erule allE[where ?x=0])
       apply (erule allE[where ?x=1])
       apply force

    apply (erule allE[where ?x=0])
       apply (erule allE[where ?x=1])
      apply force

    apply (erule allE[where ?x=0])
       apply (erule allE[where ?x=2])
     apply force

    apply (erule allE[where ?x=0])
       apply (erule allE[where ?x=3])
    apply force

    apply (erule allE[where ?x=0])
   apply (erule allE[where ?x=4])
   apply simp
   apply meson

    apply (erule allE[where ?x=0])
  apply (erule allE[where ?x=5])
  apply force
  done
(*
lemma heap_var_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var Tr \<noteq> mask_var Tr \<and> heap_var Tr \<noteq> mask_var_def Tr \<and> heap_var Tr \<notin> ran (var_translation Tr) \<and>
         heap_var Tr \<notin> ran (field_translation Tr) \<and> heap_var Tr \<notin> range (const_repr Tr) \<and>
         heap_var Tr \<notin> dom AuxPred"
  using heap_var_disjoint_aux[OF assms]
  by presburger

lemma heap_var_def_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var_def Tr \<noteq> mask_var Tr \<and> heap_var Tr \<noteq> mask_var_def Tr \<and> heap_var_def Tr \<notin> ran (var_translation Tr) \<and>
         heap_var_def Tr \<notin> ran (field_translation Tr) \<and> heap_var_def Tr \<notin> range (const_repr Tr) \<and>
         heap_var_def Tr \<notin> dom AuxPred"
  using heap_var_disjoint_aux[OF assms]
  by presburger
*)

lemma mask_var_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          "mvar = mask_var_def Tr \<or> mvar = mask_var Tr"
  shows "mvar \<noteq> heap_var Tr \<and> mvar \<noteq> heap_var_def Tr \<and> mvar \<notin> ran (var_translation Tr) \<and>
         mvar \<notin> ran (field_translation Tr) \<and> mvar \<notin> range (const_repr Tr) \<and>
         mvar \<notin> dom AuxPred"
  apply (intro conjI)
  using state_rel0_disjoint[OF assms(1)] assms(2)
  apply (unfold disjoint_list_def)
       apply (erule allE[where ?x=1])
       apply (erule allE[where ?x=0])
       apply force

    apply (erule allE[where ?x=1])
       apply (erule allE[where ?x=0])
      apply force

    apply (erule allE[where ?x=1])
       apply (erule allE[where ?x=2])
     apply force

    apply (erule allE[where ?x=1])
       apply (erule allE[where ?x=3])
    apply force

    apply (erule allE[where ?x=1])
   apply (erule allE[where ?x=4])
   apply simp
   apply meson

    apply (erule allE[where ?x=1])
  apply (erule allE[where ?x=5])
  apply force
  done

(*
lemma mask_var_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var Tr \<noteq> heap_var Tr \<and> mask_var Tr \<noteq> heap_var_def Tr \<and> mask_var Tr \<notin> ran (var_translation Tr) \<and>
         mask_var Tr \<notin> ran (field_translation Tr) \<and> mask_var Tr \<notin> range (const_repr Tr) \<and>
         mask_var Tr \<notin> dom AuxPred"
  using mask_var_disjoint_aux[OF assms]
  by presburger

lemma mask_var_def_disjoint:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_def Tr \<noteq> heap_var Tr \<and> mask_var_def Tr \<noteq> heap_var_def Tr \<and> mask_var_def Tr \<notin> ran (var_translation Tr) \<and>
         mask_var_def Tr \<notin> ran (field_translation Tr) \<and> mask_var_def Tr \<notin> range (const_repr Tr) \<and>
         mask_var_def Tr \<notin> dom AuxPred"
  using mask_var_disjoint_aux[OF assms]
  by presburger
*)

lemma state_rel0_heap_var_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega> ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_heap_var_rel = state_rel0_heap_var_rel[OF state_rel_state_rel0]

lemma state_rel0_heap_var_def_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var_def Tr) \<omega>def ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_heap_var_def_rel = state_rel0_heap_var_def_rel[OF state_rel_state_rel0]

lemma state_rel0_mask_var_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega> ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_mask_var_rel = state_rel0_mask_var_rel[OF state_rel_state_rel0]

lemma state_rel0_mask_var_def_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var_def Tr) \<omega>def ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_mask_var_def_rel = state_rel0_mask_var_def_rel[OF state_rel_state_rel0]

lemma state_rel0_field_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "field_rel Pr \<Lambda> Tr ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_field_rel = state_rel0_field_rel[OF state_rel_state_rel0]

lemma state_rel0_boogie_const_rel:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "boogie_const_rel (const_repr Tr) \<Lambda> ns"
  using assms
  unfolding state_rel0_def
  by simp

lemmas state_rel_boogie_const_rel = state_rel0_boogie_const_rel[OF state_rel_state_rel0]

lemma state_rel_boogie_const_rel_2:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "C = const_repr Tr"
  shows "boogie_const_rel C (var_context ctxt) ns"
  using assms
  unfolding state_rel_def state_rel0_def
  by simp

lemma state_rel0_state_well_typed:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "state_well_typed A \<Lambda> [] ns"
  using assms
  unfolding state_rel0_def
  by blast

lemmas state_rel_state_well_typed = state_rel0_state_well_typed[OF state_rel_state_rel0]

lemma state_rel0_disj_mask_store:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var Tr \<notin> ran (var_translation Tr)"
proof -
    from assms have Disj: "disjoint_list [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred]"
      by (simp add: state_rel0_def)
    thus "mask_var Tr \<notin> ran (var_translation Tr)"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=1])
      apply (erule allE[where ?x=2])
      by simp      
  qed

lemmas state_rel_disj_mask_store = state_rel0_disj_mask_store[OF state_rel_state_rel0]

lemma state_rel0_disj_mask_def_store:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_def Tr \<notin> ran (var_translation Tr)"
proof -
  from assms have Disj: "disjoint_list [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred]"
    by (simp add: state_rel0_def)
  thus "mask_var_def Tr \<notin> ran (var_translation Tr)"
    unfolding disjoint_list_def
    apply (rule allE[where ?x=1])
    apply (erule allE[where ?x=2])
    by simp
qed

lemmas state_rel_disj_mask_def_store = state_rel0_disj_mask_def_store[OF state_rel_state_rel0]

lemma state_rel0_aux_vars_pred_sat:
  assumes "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "aux_vars_pred_sat \<Lambda> AuxPred ns"
  using assms
  unfolding state_rel0_def
  by blast

lemmas state_rel_aux_vars_pred_sat = state_rel0_aux_vars_pred_sat[OF state_rel_state_rel0]

lemma state_rel_obtain_mask:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  obtains mb 
  where "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
        "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
        "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
  using state_rel0_mask_var_rel[OF state_rel_state_rel0[OF StateRel]]
  unfolding mask_var_rel_def
  by blast

lemma state_rel_aux_pred_sat_lookup:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
  shows "has_Some P  (lookup_var (var_context ctxt) ns aux_var)"
  using assms state_rel_aux_vars_pred_sat
  unfolding state_rel_def aux_vars_pred_sat_def
  by blast

lemma state_rel_aux_pred_sat_lookup_2:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
  shows "\<exists>v. lookup_var (var_context ctxt) ns aux_var = Some v \<and> P v"
  using assms state_rel_aux_vars_pred_sat has_Some_iff state_rel_aux_pred_sat_lookup
  unfolding state_rel_def
  by fastforce

lemma state_rel_aux_pred_sat_lookup_2_elim:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
        obtains v where "lookup_var (var_context ctxt) ns aux_var = Some v" and "P v"
  using assms state_rel_aux_pred_sat_lookup_2
  by blast

lemma state_rel_aux_pred_sat_lookup_3:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some (pred_eq v)"
  shows "lookup_var (var_context ctxt) ns aux_var = Some v"
  using state_rel_aux_pred_sat_lookup_2[OF assms]
  by (simp add: pred_eq_def)

lemma state_rel_aux_pred_sat_lookup_3_elim:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some (pred_eq v)"
  shows "lookup_var (var_context ctxt) ns aux_var = Some v"
  using state_rel_aux_pred_sat_lookup_2[OF assms]
  by (simp add: pred_eq_def)

lemma state_rel_aux_pred_weaken:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "dom AuxPred' \<subseteq> dom AuxPred" and
          WeakerPred: "\<And>x P' P v. AuxPred x = Some P \<Longrightarrow> AuxPred' x = Some P' \<Longrightarrow> P v \<Longrightarrow> P' v"
        shows "state_rel Pr TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
  note StateRel0 = state_rel_state_rel0[OF StateRel]

  show "aux_vars_pred_sat (var_context ctxt) AuxPred' ns"
  unfolding aux_vars_pred_sat_def
  proof (rule allI | rule impI)+
    fix x P'
    assume "AuxPred' x = Some P'"
    moreover from this obtain P where "AuxPred x = Some P"
      using \<open>dom _ \<subseteq> dom _\<close>
      by blast

    ultimately show "has_Some P' (lookup_var (var_context ctxt) ns x)"
      using state_rel0_aux_vars_pred_sat[OF StateRel0] WeakerPred
      unfolding aux_vars_pred_sat_def
      by (metis has_Some_iff)
  qed   

  (* TODO: adjust the tactic disjoint_list_subset_tac such that it can be applied here *)
  show "disjoint_list
     [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr),
      dom AuxPred']" (is "disjoint_list ?A'")

  proof (rule disjoint_list_subset[OF state_rel0_disjoint[OF StateRel0]], simp)
    fix i j
    assume "0 \<le> i" and
           "i < length
                [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr),
                 dom AuxPred]" (is "i < length ?A")
    show "?A' ! i \<subseteq> ?A ! i"            
      apply (cases i)
       apply simp
      apply (rename_tac i1)
      apply (case_tac i1)
       apply simp
      apply (rename_tac i2)
      apply (case_tac i2)
      apply simp
      apply (rename_tac i3)
      apply (case_tac i3)
       apply simp
      apply (rename_tac i4)
      apply (case_tac i4)
       apply simp
      apply (rename_tac i5)
      apply (case_tac i5)
       apply simp
       apply (simp add: \<open>dom _ \<subseteq> dom _\<close>)
      apply (simp add: \<open>i < _\<close>)
      done
  qed 
qed (insert StateRel, unfold state_rel_def state_rel0_def, auto)

lemma state_rel_aux_pred_remove:
  assumes "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred' \<subseteq>\<^sub>m AuxPred"
        shows "state_rel Pr TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
      apply (rule state_rel_aux_pred_weaken[OF assms(1)])
       apply (rule map_le_implies_dom_le[OF assms(2)])
    using \<open>AuxPred' \<subseteq>\<^sub>m AuxPred\<close>
    by (metis (no_types, lifting) dom_fun_upd fun_upd_triv insertCI map_le_def option.distinct(1) option.sel)

lemma lookup_disj_aux:
  assumes "\<And>x. x \<notin> M \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "disjnt M S" and
          "x \<in> S"
        shows "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
  using assms
  by (meson disjnt_iff)

lemma lookup_disj_aux_2:
  assumes "\<And>x. x \<noteq> y \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          "y \<notin> S" and
          "x \<in> S"
        shows "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
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

lemma state_rel0_store_update:
  assumes StateRel: "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>'" and
     OnlyStoreAffectedVpr: 
           "get_h_total_full \<omega> = get_h_total_full \<omega>'" 
           "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
     OnlyStoreAffectedBpl: "(\<And>x. x \<notin> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
     StoreRel: "store_rel A \<Lambda> Tr \<omega>' ns'" and
     ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
     OldStateEq: "old_global_state ns' = old_global_state ns" and
     BinderEmpty: "binder_state ns' = Map.empty"
   shows "state_rel0 Pr A \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'"
  unfolding state_rel0_def
proof (intro conjI)
  show "wf_mask_simple (get_mh_total_full \<omega>def')"
    using state_rel0_wf_mask_simple[OF StateRel] OnlyStoreAffectedVpr WellDefSame    
    by fastforce

  show "wf_mask_simple (get_mh_total_full \<omega>')"
    using state_rel0_wf_mask_simple[OF StateRel] OnlyStoreAffectedVpr    
    by fastforce

  show "store_rel A \<Lambda> Tr \<omega>' ns'"
    by (rule StoreRel)

  show "disjoint_list
     [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred]"
    using StateRel
    by (simp add: state_rel0_def)

  show "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega>' ns'"
  proof -
    have "lookup_var \<Lambda> ns (heap_var Tr) = lookup_var \<Lambda> ns' (heap_var Tr)"
    proof -
      from state_rel0_disjoint[OF StateRel]
      have "heap_var Tr \<notin> ran (var_translation Tr)"
        unfolding disjoint_list_def
        by fastforce
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
    using heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel]] OnlyStoreAffectedVpr
    by auto
   qed

  show "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var_def Tr) \<omega>def' ns'"
  proof -   
    have "lookup_var \<Lambda> ns (heap_var_def Tr) = lookup_var \<Lambda> ns' (heap_var_def Tr)"
    proof -
      from heap_var_disjoint[OF StateRel]
      have "heap_var_def Tr \<notin> ran (var_translation Tr)"
        by blast        
        
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis    
    using heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel]] OnlyStoreAffectedVpr WellDefSame
    by simp
  qed

  show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega>' ns'"
  proof -  
    have "lookup_var \<Lambda> ns (mask_var Tr) = lookup_var \<Lambda> ns' (mask_var Tr)"
    proof -
      have "mask_var Tr \<notin> ran (var_translation Tr)"
        by (simp add: state_rel0_disj_mask_store[OF StateRel])
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
    using  mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel]] OnlyStoreAffectedVpr
    by auto
  qed 

  show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var_def Tr) \<omega>def' ns'"
  proof -  
    have "lookup_var \<Lambda> ns (mask_var_def Tr) = lookup_var \<Lambda> ns' (mask_var_def Tr)"
    proof -
      have "mask_var_def Tr \<notin> ran (var_translation Tr)"
        by (simp add: state_rel0_disj_mask_def_store[OF StateRel])
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
      using mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel]] OnlyStoreAffectedVpr WellDefSame
      by auto    
  qed 

  show "field_rel Pr \<Lambda> Tr ns'"
  proof (rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
    fix x
     assume FieldElem: "x \<in> ran (field_translation Tr)"
     from state_rel0_disjoint[OF StateRel] have
        "disjnt (ran (var_translation Tr)) (ran (field_translation Tr))"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=2])
      apply (erule allE[where ?x=3])
      by simp
    thus "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
      using OnlyStoreAffectedBpl FieldElem lookup_disj_aux by blast
  qed (simp)

  show "boogie_const_rel (const_repr Tr) \<Lambda> ns'"
  proof (rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
    fix x
    assume ConstElem: "x \<in> range (const_repr Tr)"
    from state_rel0_disjoint[OF StateRel] have
      "disjnt (ran (var_translation Tr)) (range (const_repr Tr))"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=2])
      apply (erule allE[where ?x=4])
      by simp
    thus "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
      using OnlyStoreAffectedBpl ConstElem lookup_disj_aux by blast
  qed

  show "state_well_typed A \<Lambda> [] ns'"
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

  show "aux_vars_pred_sat \<Lambda> AuxPred ns'"
  proof -
    from state_rel0_disjoint[OF StateRel]
    have "disjnt (ran (var_translation Tr)) (dom  AuxPred)"
      unfolding disjoint_list_def
      apply (rule allE[where ?x=2])
      apply (erule allE[where ?x=5])
      by simp
    thus "aux_vars_pred_sat \<Lambda> AuxPred ns'"
      using state_rel0_aux_vars_pred_sat[OF StateRel] OnlyStoreAffectedBpl
      unfolding aux_vars_pred_sat_def
      by (metis disjnt_iff domI)  
  qed
qed (insert StateRel, insert WellDefSame, unfold state_rel0_def, auto)

lemma state_rel_store_update:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          VarCtxt: "var_context ctxt = \<Lambda>" and
          WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>'" and
     OnlyStoreAffectedVpr: 
           "get_h_total_full \<omega> = get_h_total_full \<omega>'" 
           "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
     OnlyStoreAffectedBpl: "(\<And>x. x \<notin> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
     ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
     OldStateEq: "old_global_state ns' = old_global_state ns" and
     BinderEmpty: "binder_state ns' = Map.empty" and
     StoreRel: "store_rel (type_interp ctxt) \<Lambda> Tr \<omega>' ns'"
   shows "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def' \<omega>' ns'"  
  unfolding state_rel_def
  using assms
  by (auto intro!: state_rel0_store_update[OF state_rel_state_rel0[OF StateRel]])

lemma state_rel_store_update_2:
  assumes 
         StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>'" and
         VarCtxt: "\<Lambda> = var_context ctxt" and
         VarTr: "var_translation Tr x_vpr = Some x_bpl" and
         "v' = val_rel_vpr_bpl v" and
      TyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
              "type_of_val (type_interp ctxt) v' = ty"
       shows "state_rel Pr TyRep Tr AuxPred ctxt (update_var_total \<omega>def x_vpr v) (update_var_total \<omega> x_vpr v) (update_var \<Lambda> ns x_bpl v')"  
  apply (rule state_rel_store_update[OF StateRel])
       apply simp
         apply (simp add: VarCtxt)
         apply (simp add: WellDefSame)
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

lemma state_rel_new_auxvar:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     AuxVarFresh: "aux_var \<notin> 
                      ({heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"  and   
           "P aux_val" and
                 "type_interp ctxt = vbpl_absval_ty TyRep" and
     LookupTy: "lookup_var_ty (var_context ctxt) aux_var = Some \<tau>"
               "type_of_val (type_interp ctxt) aux_val = \<tau>"
   shows "state_rel Pr TyRep Tr (AuxPred(aux_var \<mapsto> P)) ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"  
proof -
  note StateRel0 = state_rel_state_rel0[OF StateRel]

  show ?thesis
    unfolding state_rel_def state_rel0_def
  proof (intro conjI)
    show "store_rel (type_interp ctxt) (var_context ctxt) Tr \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"
      using store_rel_stable[OF state_rel0_store_rel[OF StateRel0]] AuxVarFresh
      by fastforce
  next
    from state_rel0_disjoint[OF StateRel0]
    have *:"disjoint_list 
       ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]@
       [ dom AuxPred])"
      by simp

    show "disjoint_list
     [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr),
      dom (AuxPred(aux_var \<mapsto> P))]"
      using AuxVarFresh disjoint_list_add[OF *]
      by auto
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep Tr (heap_var Tr) \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"
      using heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel0]] AuxVarFresh
      by simp
  next
    show "mask_var_rel Pr (var_context ctxt) TyRep Tr (mask_var Tr) \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"
      using mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel0]] AuxVarFresh
      by auto
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep Tr (heap_var_def Tr) \<omega>def (update_var (var_context ctxt) ns aux_var aux_val)"
      using heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel0]] AuxVarFresh
      by simp
  next
    show "mask_var_rel Pr (var_context ctxt) TyRep Tr (mask_var_def Tr) \<omega>def (update_var (var_context ctxt) ns aux_var aux_val)"
      using mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel0]] AuxVarFresh
      by auto
  next
    show "field_rel Pr (var_context ctxt) Tr (update_var (var_context ctxt) ns aux_var aux_val)"
      using field_rel_stable[OF state_rel0_field_rel[OF StateRel0]] AuxVarFresh
      by fastforce
  next
    show "boogie_const_rel (const_repr Tr) (var_context ctxt) (update_var (var_context ctxt) ns aux_var aux_val)"
      using boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel0]] AuxVarFresh
      by fastforce
  next
    show "aux_vars_pred_sat (var_context ctxt) (AuxPred(aux_var \<mapsto> P)) 
                                               (update_var (var_context ctxt) ns aux_var aux_val)"  
      using aux_vars_pred_sat_update state_rel0_aux_vars_pred_sat[OF StateRel0] \<open>P aux_val\<close>
      by blast
  next
    show "state_well_typed (type_interp ctxt) (var_context ctxt) [] (update_var (var_context ctxt) ns aux_var aux_val)"
      using LookupTy state_rel0_state_well_typed[OF StateRel0]
      by (metis instantiate_nil update_var_state_wt)
  next
    show "wf_mask_simple (get_mh_total_full \<omega>)"
      using StateRel0 state_rel0_wf_mask_simple by blast
  next
    show "type_interp ctxt = vbpl_absval_ty TyRep"
      by (simp add: \<open>type_interp ctxt = _\<close>)
  qed (insert StateRel0, unfold state_rel0_def, auto)
qed

lemma state_rel_independent_var:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     AuxVarFresh: "aux_var \<notin> 
                      ({heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"  and   
     TypeInterp:       "type_interp ctxt = vbpl_absval_ty TyRep" and
     LookupTy: "lookup_var_ty (var_context ctxt) aux_var = Some \<tau>"
               "type_of_val (type_interp ctxt) aux_val = \<tau>"
             shows "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"

proof -
  have StateRelUpd: "state_rel Pr TyRep Tr (AuxPred(aux_var \<mapsto> pred_eq aux_val)) ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"    
    by (rule state_rel_new_auxvar[OF StateRel AuxVarFresh pred_eq_refl TypeInterp LookupTy])

  from AuxVarFresh have "aux_var \<notin> dom AuxPred"
    by blast
  show ?thesis
    apply (rule state_rel_aux_pred_remove[OF StateRelUpd])
    using \<open>aux_var \<notin> dom AuxPred\<close>
    by (metis fun_upd_None_if_notin_dom map_le_imp_upd_le upd_None_map_le)
qed 
                   
lemma state_rel0_heap_update:
  assumes  
     StateRel: "state_rel0 Pr TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
               "TyInterp = vbpl_absval_ty TyRep" and
          WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>' \<and> heap_var Tr = heap_var_def Tr" and
          OnlyHeapAffected: "(\<And>x. x \<noteq> heap_var Tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
          OnlyHeapAffectedVpr: "get_store_total \<omega> = get_store_total \<omega>'" 
                               "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
          HeapRel: "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega>' ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
  shows "state_rel0 Pr TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'"  
  unfolding state_rel0_def
  proof (intro conjI)
    show "wf_mask_simple (get_mh_total_full \<omega>def')"
      using state_rel0_wf_mask_def_simple[OF StateRel] OnlyHeapAffectedVpr WellDefSame
      by simp
  next
    show "wf_mask_simple (get_mh_total_full \<omega>')"
      using state_rel0_wf_mask_simple[OF StateRel] OnlyHeapAffectedVpr
      by simp
  next
    show "store_rel TyInterp \<Lambda> Tr \<omega>' ns'"
    proof (rule store_rel_stable[OF state_rel0_store_rel[OF StateRel]])
      show "get_store_total \<omega> = get_store_total \<omega>'"
        using OnlyHeapAffectedVpr
        by simp
    next
      fix x
      assume "x \<in> ran (var_translation Tr)"
      show "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
        apply (rule lookup_disj_aux_2[OF _ _ \<open>x \<in> _\<close>])
         apply (erule OnlyHeapAffected)
        using heap_var_disjoint[OF StateRel]
        by blast
    qed simp
  next  
    show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega>' ns'"
      apply (rule mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel]])
      using OnlyHeapAffectedVpr
       apply simp
      using mask_var_disjoint[OF StateRel] OnlyHeapAffected
       apply force
      by simp
  next
    show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var_def Tr) \<omega>def' ns'"
          apply (rule mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel]])
      using OnlyHeapAffectedVpr WellDefSame
       apply simp
      using mask_var_disjoint[OF StateRel] OnlyHeapAffected
       apply force
      by simp
  next
    show "field_rel Pr \<Lambda> Tr ns'"
    proof (rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
      fix x
      assume "x \<in> ran (field_translation Tr)"
      show "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
        apply (rule lookup_disj_aux_2[OF _ _ \<open>x \<in> _\<close>])
         apply (erule OnlyHeapAffected)
        using heap_var_disjoint[OF StateRel]
        by blast
    qed (simp)
  next
    show "boogie_const_rel (const_repr Tr) \<Lambda> ns'"     
    proof (rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
      fix x
      assume "x \<in> range (const_repr Tr)"
      show "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
        apply (rule lookup_disj_aux_2[OF _ _ \<open>x \<in> _\<close>])
         apply (erule OnlyHeapAffected)
        using heap_var_disjoint[OF StateRel]
        by blast
    qed
  next
    have LookupAux:
           "\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> \<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> 
                                                       type_of_val TyInterp v1 = instantiate [] t"
    proof -
      fix x t 
      assume LookupTy: "lookup_var_ty \<Lambda> x = Some t"
      show "\<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> type_of_val TyInterp v1 = instantiate [] t"
      proof (cases "x = heap_var Tr")
        case True      
        hence "t = TConSingle (THeapId TyRep)"   
          by (metis LookupTy HeapRel heap_var_rel_def option.sel)
        obtain hb where LookupX: "lookup_var \<Lambda> ns' x = Some (AbsV (AHeap hb))" and
                         "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
          using HeapRel heap_var_rel_def \<open>x = _\<close>
          by blast  
        thus ?thesis
          using \<open>t = _\<close> \<open>TyInterp = _\<close>
          by auto        
      next
        case False
        hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" 
          using OnlyHeapAffected by simp    
        then show ?thesis using state_rel0_state_well_typed[OF StateRel] LookupTy \<open>TyInterp = _\<close>
          by (metis state_well_typed_lookup)
      qed
    qed
  
    show "state_well_typed TyInterp \<Lambda> [] ns'"
      apply (rule state_well_typed_upd_1[OF state_rel0_state_well_typed[OF StateRel]])
      apply (erule LookupAux)
      using ShadowedGlobalsEq OldStateEq BinderEmpty
      by auto
  next
    from heap_var_disjoint[OF StateRel] have "heap_var Tr \<notin> dom AuxPred"
      by blast
  
    thus "aux_vars_pred_sat \<Lambda> AuxPred ns'"
    using state_rel0_aux_vars_pred_sat[OF StateRel] OnlyHeapAffected
    unfolding aux_vars_pred_sat_def
    by (metis domI)
  qed (insert assms, unfold state_rel0_def, auto)

lemma state_rel_heap_update:
  assumes  
     StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>' \<and> heap_var Tr = heap_var_def Tr" and
          OnlyHeapAffected: "(\<And>x. x \<noteq> heap_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ns' x)" and
          OnlyHeapAffectedVpr: "get_store_total \<omega> = get_store_total \<omega>'" 
                               "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
          HeapRel: "heap_var_rel Pr (var_context ctxt) TyRep Tr (heap_var Tr) \<omega>' ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty" and
          TypeInterp: "type_interp ctxt = (vbpl_absval_ty TyRep)"

shows "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def' \<omega>' ns'"  
  unfolding state_rel_def
  apply (rule state_rel0_heap_update[OF state_rel_state_rel0[OF StateRel]])
  using assms
  unfolding state_rel_def
  by auto

lemma heap_var_rel_update:
  assumes 
     WfTyRep: "wf_ty_repr_bpl TyRep" and
     HeapVarRel: "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega> ns" and
     LookupHeapVar: "lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
               "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     VBplTy:   "type_of_val (vbpl_absval_ty TyRep) (val_rel_vpr_bpl v_vpr) = ty_bpl" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     FieldTranslationInj: "inj_on (field_translation Tr) (dom (field_translation Tr))"
  shows "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr)
     (update_var \<Lambda> ns (heap_var Tr) (AbsV (AHeap (heap_bpl_upd_normal_field hb (Address addr) f_bpl ty_vpr (val_rel_vpr_bpl v_vpr)))))"
      (is "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) ?\<omega>' ?ns'")
proof -
  from HeapVarRel and LookupHeapVar have
   HeapRelFacts:
   "lookup_var_ty \<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))" 
   "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
   "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
    unfolding heap_var_rel_def
    by auto

  show ?thesis
  unfolding heap_var_rel_def
  proof (rule exI, intro conjI)
    let ?hb' = "hb( (Address addr, NormalField f_bpl ty_vpr) \<mapsto> val_rel_vpr_bpl v_vpr)"
    show "lookup_var \<Lambda> ?ns' (heap_var Tr) = Some (AbsV (AHeap ?hb'))"
      by (simp add: heap_bpl_upd_normal_field_def)
  next
    show "lookup_var_ty \<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))"
      using HeapVarRel
      unfolding heap_var_rel_def
      by auto
  next
    let ?hb' = "hb( (Address addr, NormalField f_bpl ty_vpr) \<mapsto> val_rel_vpr_bpl v_vpr)"
    show "vbpl_absval_ty_opt TyRep (AHeap ?hb') = Some (THeapId TyRep, [])"
      apply (rule heap_upd_ty_preserved[OF HeapRelFacts(2)])
       apply (fastforce intro: \<open>vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl\<close>)
      by (rule VBplTy)      
  next
    have HeapRel:"heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
       using HeapVarRel LookupHeapVar
       unfolding heap_var_rel_def
       by auto
    have AuxUpdateHeap:"\<And>l. l \<noteq> (addr, f_vpr) \<Longrightarrow> get_hh_total_full (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr) l = 
                                                   get_hh_total_full \<omega> l"
      by (metis update_hh_loc_total_full_lookup_2)
     
  
    let ?hb' = "hb( (Address addr, NormalField f_bpl ty_vpr) \<mapsto> val_rel_vpr_bpl v_vpr)"
    show "ViperBoogieBasicRel.heap_rel Pr (field_translation Tr) (get_hh_total_full ?\<omega>') ?hb'"    
    proof (rule heap_rel_intro)
      fix l :: heap_loc
      fix  field_ty_vpr field_bpl
      assume FieldLookupL: "declared_fields Pr (snd l) = Some field_ty_vpr" and
             FieldTranslationL: "field_translation Tr (snd l) = Some field_bpl"
      show "?hb' (Address (fst l),  NormalField field_bpl field_ty_vpr) = 
               Some (val_rel_vpr_bpl (get_hh_total_full ?\<omega>' l))"
      proof (cases "l = (addr, f_vpr)")
        case True
        then show ?thesis 
          using FieldLookup FieldTranslation FieldLookupL FieldTranslationL 
          by (simp add: update_hh_loc_total_lookup_1)
      next
        case False
        hence "(hb( (Address addr, NormalField f_bpl ty_vpr) \<mapsto> val_rel_vpr_bpl v_vpr)) (Address (fst l), NormalField field_bpl field_ty_vpr)
                  = hb (Address (fst l), NormalField field_bpl field_ty_vpr) "
          using FieldTranslation FieldLookup FieldTranslationInj FieldLookupL FieldTranslationL
          by (metis (no_types, lifting) Pair_inject domI fun_upd_other inj_on_contraD prod.exhaust_sel ref.inject vb_field.inject(1))     
        thus ?thesis 
          by (metis AuxUpdateHeap False FieldLookupL FieldTranslationL HeapRel ViperBoogieBasicRel.heap_rel_def)
      qed
    qed
  qed
qed

lemma state_rel_heap_update_2:
  assumes  
     WfTyRep: "wf_ty_repr_bpl TyRep" and
     StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>' \<and> heap_var Tr = heap_var_def Tr" and
     LookupHeap:  "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     BplType:  "type_of_vbpl_val TyRep (val_rel_vpr_bpl v_vpr) = ty_bpl"
   shows "state_rel Pr TyRep Tr AuxPred ctxt 
      (update_hh_loc_total_full \<omega>def (addr, f_vpr) v_vpr)
      (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr)
      (update_var (var_context ctxt) ns (heap_var Tr) (AbsV (AHeap (heap_bpl_upd_normal_field hb (Address addr) f_bpl ty_vpr (val_rel_vpr_bpl v_vpr)))))"
         (is "state_rel Pr TyRep Tr AuxPred ctxt ?\<omega>def' ?\<omega>' ?ns'")
proof (rule state_rel_heap_update[OF StateRel])
  show "\<And>x. x \<noteq> heap_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ?ns' x"
    by simp
next
  show "get_store_total \<omega> = get_store_total ?\<omega>'"
    by simp
next
  show "get_m_total_full \<omega> = get_m_total_full ?\<omega>'"
    by (meson get_m_total_full_aux)
next
  show "heap_var_rel Pr (var_context ctxt) TyRep Tr (heap_var Tr) ?\<omega>' ?ns'"
    apply (rule heap_var_rel_update[OF WfTyRep])
    using state_rel_state_rel0[OF StateRel] assms
    unfolding state_rel0_def field_rel_def
    by auto
next
  show "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ?ns' x = global_state ns x"
    by (metis global_state_update_local global_state_update_other option.exhaust)
next
  show "old_global_state ?ns' = old_global_state ns"
    by (simp add: update_var_old_global_same)
next
  show "binder_state ?ns' = Map.empty"
    by (metis StateRel state_rel_state_well_typed state_well_typed_def update_var_binder_same)
next
  show "type_interp ctxt = vbpl_absval_ty TyRep"
    using StateRel
    by (meson state_rel0_type_interp state_rel_state_rel0)    
qed (insert assms, auto)

lemma state_rel_heap_update_2_ext:
  assumes  
     WfTyRep: "wf_ty_repr_bpl TyRep" and
     StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>' \<and> heap_var Tr = heap_var_def Tr" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     BplType:  "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = ty_bpl"
   shows "\<exists>hb f_bpl_val.
    lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
    lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
    field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), ty_bpl]) \<and>
    state_rel Pr TyRep Tr AuxPred ctxt
      (update_hh_loc_total_full \<omega>def (addr, f_vpr) v)
      (update_hh_loc_total_full \<omega> (addr, f_vpr) v)
       (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         )"
proof -
  from StateRel obtain hb where LookupHeapVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))"
    unfolding state_rel_def state_rel0_def heap_var_rel_def
    by blast

  have
    LookupFieldVar: "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField (NormalField f_bpl ty_vpr)))" 
    using FieldLookup FieldTranslation TyTranslation
          state_rel0_field_rel[OF state_rel_state_rel0[OF StateRel]]
    unfolding field_rel_def
    by fastforce
  hence FieldTy: "field_ty_fun_opt TyRep (NormalField f_bpl ty_vpr) = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), ty_bpl])"
    using TyTranslation
    by simp

  let ?\<omega>def' = "update_hh_loc_total_full \<omega>def (addr, f_vpr) v"
  let ?\<omega>' = "update_hh_loc_total_full \<omega> (addr, f_vpr) v"
  from state_rel_heap_update_2[OF WfTyRep StateRel]
  have "state_rel Pr TyRep Tr AuxPred ctxt 
        ?\<omega>def'
        ?\<omega>' 
        (update_var (var_context ctxt) ns (heap_var Tr) (AbsV (AHeap (heap_bpl_upd_normal_field hb (Address addr) f_bpl ty_vpr (val_rel_vpr_bpl v)))))"
    using assms LookupHeapVar
    by fast
   
  thus  ?thesis
    using LookupHeapVar LookupFieldVar FieldTy 
    unfolding heap_bpl_upd_normal_field_def
    by auto
qed

lemma state_rel0_mask_update:
  assumes StateRel: "state_rel0 Pr (vbpl_absval_ty TyRep) \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
                  \<comment>\<open>The following assumption only allows updating both the well-definedness and 
                     evaluation mask (in case the tracked Boogie variables are the same) or 
                     just the evaluation mask. For unfolding expressions, we will need to weaken this
                     assumption to also allow updating just the well-definedness mask.
                     \<close>                    
          WellDefSame: "mask_var Tr = mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>'"
                       "mask_var Tr \<noteq> mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>def"  and
          OnlyMaskAffected: "\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          OnlyMaskAffectedVpr: "get_store_total \<omega> = get_store_total \<omega>'" 
                               "get_trace_total \<omega> = get_trace_total \<omega>'"
                               "get_h_total_full \<omega> = get_h_total_full \<omega>'" and
          WfMaskSimple: "wf_mask_simple (get_mh_total_full \<omega>')" and
          MaskVarRel: "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega>' ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
 shows "state_rel0 Pr (vbpl_absval_ty TyRep) \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'"  
  unfolding state_rel0_def
  proof (intro conjI)
    show "wf_mask_simple (get_mh_total_full \<omega>')"
      by (rule WfMaskSimple)
  next
    show "wf_mask_simple (get_mh_total_full \<omega>def')"
      using WellDefSame WfMaskSimple state_rel0_wf_mask_def_simple[OF StateRel]
      by fast
  next
    show "store_rel (vbpl_absval_ty TyRep) \<Lambda> Tr \<omega>' ns'"
      apply (rule store_rel_stable[OF state_rel0_store_rel[OF StateRel]])
      using OnlyMaskAffectedVpr
       apply simp
      using OnlyMaskAffected mask_var_disjoint[OF StateRel]
      by (meson OnlyMaskAffected) simp
  next
    show "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var Tr) \<omega>' ns'"
      apply (rule heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel]])
      using OnlyMaskAffectedVpr
       apply simp
      using OnlyMaskAffected heap_var_disjoint[OF StateRel]
       apply presburger 
      by simp
  next
    have HeapSame: "get_h_total_full \<omega> = get_h_total_full \<omega>def"
      using StateRel
      unfolding state_rel0_def
      by argo

    show "heap_var_rel Pr \<Lambda> TyRep Tr (heap_var_def Tr) \<omega>def' ns'"          
    proof (cases "mask_var Tr = mask_var_def Tr")
      case True
      hence "\<omega>def' = \<omega>'"
        using WellDefSame by blast            
      show ?thesis 
        apply (rule heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel]])
        using \<open>\<omega>def' = \<omega>'\<close> HeapSame \<open>get_h_total_full \<omega> = get_h_total_full \<omega>'\<close> 
         apply force
        using OnlyMaskAffected heap_var_disjoint[OF StateRel]
         apply presburger 
        by simp
    next
      case False
      hence "\<omega>def' = \<omega>def"
        using WellDefSame
        by blast

      show ?thesis 
        apply (rule heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel]])
        using \<open>\<omega>def' = \<omega>def\<close>
         apply simp
        using OnlyMaskAffected heap_var_disjoint[OF StateRel]
         apply presburger    
        by simp
    qed
  next
    show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var Tr) \<omega>' ns'"
      by (rule MaskVarRel)
  next
    show "mask_var_rel Pr \<Lambda> TyRep Tr (mask_var_def Tr) \<omega>def' ns'"
    proof (cases "mask_var Tr = mask_var_def Tr")
      case True
      then show ?thesis
        using MaskVarRel WellDefSame
        by simp
    next
      case False
      show ?thesis   
        apply (rule mask_var_rel_stable)
        apply (rule state_rel0_mask_var_def_rel[OF StateRel])
        using WellDefSame False
         apply fast
        using False OnlyMaskAffected
         apply presburger
        by simp
    qed
  next
    show "field_rel Pr \<Lambda> Tr ns'"
      apply (rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
      using mask_var_disjoint[OF StateRel] OnlyMaskAffected
       apply meson
      by simp
  next
    show "boogie_const_rel (const_repr Tr) \<Lambda> ns'"
      apply (rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
      using OnlyMaskAffected mask_var_disjoint[OF StateRel]
      by meson
  next
    show "aux_vars_pred_sat \<Lambda> AuxPred ns'"
      apply (rule aux_vars_pred_sat_stable[OF state_rel0_aux_vars_pred_sat[OF StateRel]])
      using mask_var_disjoint[OF StateRel] OnlyMaskAffected
      by meson
  next
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
          by (metis LookupTy MaskVarRel mask_var_rel_def option.inject)
        obtain mb where LookupX: "lookup_var \<Lambda> ns' x = Some (AbsV (AMask mb))"
          using MaskVarRel
          apply (simp add: \<open>x = _\<close>)
          using mask_var_rel_def by blast        
        thus ?thesis
          by (simp add: \<open>t = _\<close>)                
      next
        case False
        hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" 
          using OnlyMaskAffected by simp    
        then show ?thesis using state_rel0_state_well_typed[OF StateRel] LookupTy
          by (metis state_well_typed_lookup)
      qed
    qed
  
    show "state_well_typed (vbpl_absval_ty TyRep) \<Lambda> [] ns'"
      apply (rule state_well_typed_upd_1[OF state_rel0_state_well_typed[OF StateRel]])
      apply (erule LookupAux)
      using ShadowedGlobalsEq OldStateEq BinderEmpty
      by auto
  qed (insert assms, unfold state_rel0_def, auto)

lemma state_rel_mask_update:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          WellDefSame: "mask_var Tr = mask_var_def Tr \<and> \<omega>def = \<omega>" and
          OnlyMaskAffected: "\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ns' x" and
          MaskRel: "mask_var_rel Pr (var_context ctxt) TyRep Tr (mask_var Tr) \<omega> ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty" and
          TypeInterp: "type_interp ctxt = (vbpl_absval_ty TyRep)"
        shows "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns'"
  unfolding state_rel_def
  using assms state_rel0_wf_mask_simple[OF state_rel_state_rel0[OF StateRel]]
  unfolding state_rel_def
  by (auto intro: state_rel0_mask_update)

lemma state_rel_mask_update_2:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and 
          WellDefSame: "mask_var Tr = mask_var_def Tr \<and> \<omega>def = \<omega>" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) m'" and
          Eq: "mvar = mask_var Tr"
           "\<Lambda> = (var_context ctxt)" and
        TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
        shows "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> (update_var \<Lambda> ns mvar (AbsV (AMask m')))" 
                (is "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ?ns'")
  apply (rule state_rel_mask_update[OF StateRel WellDefSame])
   apply (metis update_var_other Eq )
  apply (unfold mask_var_rel_def)
  apply (rule exI[where ?x=m'])
  using MaskRel Eq
  apply (meson StateRel state_rel_obtain_mask update_var_same)
      apply (simp add: Eq)
      using StateRel
         apply (metis assms(4) global_state_update_local global_state_update_other)
        apply (simp add: update_var_old_global_same)
      using state_rel0_state_well_typed[OF state_rel_state_rel0[OF StateRel]]
      unfolding state_well_typed_def
      apply (simp add: update_var_binder_same)
      by (simp add: TypeInterp)

lemma state_rel_mask_update_3:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and 
                    "\<Lambda> = (var_context ctxt)" and
          WellDefSame: "mask_var Tr = mask_var_def Tr \<Longrightarrow> \<omega>def' = update_mh_loc_total_full \<omega> (addr, f_vpr) p"
                       "mask_var Tr \<noteq> mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>def"  and
        TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
        LookupMask: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
                    "pgte pwrite p" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
                    "p_bpl = real_of_rat (Rep_prat p)"
                  shows "state_rel Pr TyRep Tr AuxPred ctxt 
                      \<omega>def'
                      (update_mh_loc_total_full \<omega> (addr, f_vpr) p) 
                      (update_var \<Lambda> ns (mask_var Tr) (AbsV (AMask (mask_bpl_upd_normal_field mb (Address addr) f_bpl ty_vpr p_bpl))))"
            (is "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def' ?\<omega>' ?ns'")
  unfolding state_rel_def TypeInterp
proof (rule state_rel0_mask_update)
  show "state_rel0 Pr (vbpl_absval_ty TyRep) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"
    using assms state_rel_state_rel0[OF StateRel]
    by auto
next
  show "\<And>x. x \<noteq> mask_var Tr \<Longrightarrow>
         lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ?ns' x"
    by (simp add: \<open>\<Lambda> = _\<close>)
next
  show "get_store_total \<omega> = get_store_total ?\<omega>'"
    by simp
next
  show "get_h_total_full \<omega> = get_h_total_full ?\<omega>'"
    by (meson get_h_total_full_aux)
next
  have WfMask: "wf_mask_simple (get_mh_total_full \<omega>)"
    using state_rel_state_rel0[OF StateRel]  state_rel0_wf_mask_simple
    by fast

  show "wf_mask_simple (get_mh_total_full ?\<omega>')" 
    unfolding wf_mask_simple_def
  proof (rule allI)
    fix hl
    show "pgte pwrite (get_mh_total_full ?\<omega>' hl)"
    proof (cases "hl = (addr, f_vpr)")
      case True
      hence "get_mh_total_full ?\<omega>' hl = p"
        using update_mh_loc_total_full_lookup_1
        by metis
      then show ?thesis 
        using \<open>pgte pwrite p\<close>
        by argo
    next
      case False       
      hence "get_mh_total_full ?\<omega>' hl = get_mh_total_full \<omega> hl"
        using update_mh_loc_total_full_lookup_2
        by metis
      thus ?thesis 
        using WfMask
        unfolding wf_mask_simple_def
        by presburger        
    qed
  qed
next
  let ?mb'="mask_bpl_upd_normal_field mb (Address addr) f_bpl ty_vpr (real_of_rat (Rep_prat p))"

  have MaskRel0:"mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    using LookupMask state_rel0_mask_var_rel[OF state_rel_state_rel0[OF StateRel]]
    unfolding mask_var_rel_def
    by auto

  have FieldTrInj: "(inj_on (field_translation Tr) (dom (field_translation Tr)))"
    using state_rel0_field_rel[OF state_rel_state_rel0[OF StateRel]]
    unfolding field_rel_def
    by simp

  have "mask_rel Pr (field_translation Tr) (get_mh_total_full ?\<omega>') ?mb'"
    unfolding mask_rel_def
   
  proof (rule conjI, (rule allI | rule impI)+)
    fix l::heap_loc
    fix field_ty_vpr field_bpl
    assume FieldLookup2: "declared_fields Pr (snd l) = Some field_ty_vpr"
    assume FieldTranslation2: "field_translation Tr (snd l) = Some field_bpl"
    show "?mb' (Address (fst l), NormalField field_bpl field_ty_vpr) =
        real_of_rat (Rep_prat (get_mh_total_full ?\<omega>' l))"
    proof (cases "l = (addr, f_vpr)")
      case True
      then show ?thesis 
        using FieldLookup FieldLookup2 FieldTranslation FieldTranslation2
        unfolding mask_bpl_upd_normal_field_def
        by (metis fst_eqD fun_upd_same option.inject snd_conv update_mh_loc_total_full_lookup_1)
    next
      case False
      hence "get_mh_total_full ?\<omega>' l = get_mh_total_full \<omega> l"
        using update_mh_loc_total_full_lookup_2
        by metis
      have "(Address addr, NormalField f_bpl ty_vpr) \<noteq> (Address (fst l), NormalField field_bpl field_ty_vpr)"
        using \<open>l \<noteq> _\<close> FieldTranslation FieldTranslation2 FieldTrInj
        by (metis Pair_inject domIff inj_onD option.simps(3) prod.exhaust_sel ref.inject vb_field.inject(1))

      hence "?mb' (Address (fst l), NormalField field_bpl field_ty_vpr) = mb (Address (fst l), NormalField field_bpl field_ty_vpr)"
        unfolding mask_bpl_upd_normal_field_def
        by auto

      thus ?thesis
        using MaskRel0 \<open>get_mh_total_full ?\<omega>' l = get_mh_total_full \<omega> l\<close> FieldLookup2 FieldTranslation2
        unfolding mask_rel_def
        by presburger 
    qed
  next
    show "\<forall>f t. ?mb' (Null, NormalField f t) = 0"
      unfolding mask_bpl_upd_normal_field_def
      using MaskRel0
      unfolding mask_rel_def
      by auto
  qed

  thus "mask_var_rel Pr (var_context ctxt) TyRep Tr (mask_var Tr) ?\<omega>' ?ns'"
    using state_rel0_mask_var_rel[OF state_rel_state_rel0[OF StateRel]]
    unfolding mask_var_rel_def
    using \<open>\<Lambda> = _\<close> update_var_same \<open>p_bpl = _\<close> by blast
next
  show "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow>
         global_state ?ns' x = global_state ns x"
    by (metis \<open>\<Lambda> = _\<close> global_state_update_local global_state_update_other option.exhaust)
next
  show "old_global_state ?ns' = old_global_state ns"
    by (simp add: update_var_old_global_same)
next
  show "binder_state ?ns' = Map.empty"
    by (metis StateRel state_rel_state_well_typed state_well_typed_def update_var_binder_same)
qed (insert assms, auto)


lemma state_rel_set_def_to_eval:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  shows "state_rel Pr TyRep (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>) AuxPred ctxt \<omega> \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
  show "disjoint_list
     [{heap_var (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>), heap_var_def (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>)},
      {mask_var (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>), mask_var_def (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>)},
      ran (var_translation (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>)),
      ran (field_translation (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>)),
      range (const_repr (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>)), dom AuxPred]"
    by (disjoint_list_subset_tac DisjointListAssm: state_rel_disjoint[OF StateRel])
qed (insert StateRel,
     unfold state_rel_def state_rel0_def, 
     insert store_rel_stable[OF state_rel_store_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_rel[OF StateRel]],
     insert mask_var_rel_stable[OF state_rel_mask_var_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF StateRel]],
     insert field_rel_stable[OF state_rel_field_rel[OF StateRel]],
     insert boogie_const_rel_stable[OF state_rel_boogie_const_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF StateRel]],
     auto)

lemma state_rel_mask_var_def_update:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and  
   MaskVarRel: "mask_var_rel Pr (var_context ctxt) TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) mvar_def' \<omega>def ns" and
          VarFresh: "mvar_def' \<notin> ({heap_var Tr, heap_var_def Tr, mask_var Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)" 
        shows "state_rel Pr TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
    from state_rel_disjoint[OF StateRel]
    have *:"disjoint_list 
       ([{heap_var Tr, heap_var_def Tr}]@[{mask_var Tr, mask_var_def Tr},ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr),
       dom AuxPred])"
      by simp

    have **: " \<forall>A\<in>set ([{heap_var Tr, heap_var_def Tr}] @ [ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred]). mvar_def' \<notin> A"
      using VarFresh
      by simp
    hence DisjList: "disjoint_list
     [{heap_var Tr, heap_var_def Tr},
      {mask_var Tr, mask_var_def Tr, mvar_def'},
      ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr), dom AuxPred]"
      using disjoint_list_add[OF * **]
      by (simp add: insert_commute)
      
    have "disjoint_list
     [{heap_var Tr, heap_var_def Tr},
      {mask_var Tr, mvar_def'},
      ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr), dom AuxPred]"
      by (disjoint_list_subset_tac DisjointListAssm: DisjList)

    thus "disjoint_list
     [{heap_var (Tr\<lparr>mask_var_def := mvar_def'\<rparr>), heap_var_def (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)},
      {mask_var (Tr\<lparr>mask_var_def := mvar_def'\<rparr>), mask_var_def (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)}, ran (var_translation (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)),
      ran (field_translation (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)), range (const_repr (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)), dom AuxPred]"
      by auto
next
  show "mask_var_rel Pr (var_context ctxt) TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) (mask_var_def (Tr\<lparr>mask_var_def := mvar_def'\<rparr>)) \<omega>def ns"
    using MaskVarRel
    by simp
qed (insert StateRel,
     unfold state_rel_def state_rel0_def, 
     insert store_rel_stable[OF state_rel_store_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_rel[OF StateRel]],
     insert mask_var_rel_stable[OF state_rel_mask_var_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF StateRel]],
     insert field_rel_stable[OF state_rel_field_rel[OF StateRel]],
     insert boogie_const_rel_stable[OF state_rel_boogie_const_rel[OF StateRel]],
     auto)   

lemma state_rel_heap_var_def_update:
  assumes StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          HeapVarRel: "heap_var_rel Pr (var_context ctxt) TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) hvar_def' \<omega>def ns" and
          VarFresh: "hvar_def' \<notin> ({heap_var Tr, mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"
        shows "state_rel Pr TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
    from state_rel_disjoint[OF StateRel]
    have *:"disjoint_list 
       ([]@[{heap_var Tr, heap_var_def Tr},{mask_var Tr, mask_var_def Tr},ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr),
       dom AuxPred])"
      by simp

    have **: " \<forall>A\<in>set ([]@[{mask_var Tr, mask_var_def Tr},ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr), dom AuxPred]). hvar_def' \<notin> A"
      using VarFresh
      by simp

    hence DisjList: "disjoint_list
     [{heap_var Tr, heap_var_def Tr, hvar_def'},
      {mask_var Tr, mask_var_def Tr},
      ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr), dom AuxPred]"
      using disjoint_list_add[OF * **]
      by (simp add: insert_commute)
      
    have "disjoint_list
     [{heap_var Tr, hvar_def'},
      {mask_var Tr, mask_var_def Tr},
      ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr), dom AuxPred]"
      by (disjoint_list_subset_tac DisjointListAssm: DisjList)

    thus "disjoint_list
     [{heap_var (Tr\<lparr>heap_var_def := hvar_def'\<rparr>), heap_var_def (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)},
      {mask_var (Tr\<lparr>heap_var_def := hvar_def'\<rparr>), mask_var_def (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)}, ran (var_translation (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)),
      ran (field_translation (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)), range (const_repr (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)), dom AuxPred]"
      by auto
next
  show "heap_var_rel Pr (var_context ctxt) TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) (heap_var_def (Tr\<lparr>heap_var_def := hvar_def'\<rparr>)) \<omega>def ns"
    using HeapVarRel
    by fastforce
qed (insert StateRel,
     unfold state_rel_def state_rel0_def, 
     insert store_rel_stable[OF state_rel_store_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_rel[OF StateRel]],
     insert heap_var_rel_stable[OF state_rel_heap_var_def_rel[OF StateRel]],
     insert mask_var_rel_stable[OF state_rel_mask_var_rel[OF StateRel]],
     insert mask_var_rel_stable[OF state_rel_mask_var_def_rel[OF StateRel]],
     insert field_rel_stable[OF state_rel_field_rel[OF StateRel]],
     insert boogie_const_rel_stable[OF state_rel_boogie_const_rel[OF StateRel]],
     auto)

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

type_synonym 'a vast_config = "('a vbpl_absval) vast_config_general"

type_synonym viper_stmt = ViperLang.stmt

subsection \<open>Auxiliary definitions for simulation\<close>

definition rel_vpr_aux
  where "rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res \<equiv>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                   (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                   (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure))"

lemma rel_vpr_aux_intro:
  assumes "\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow>
           (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and
          "res = RFailure \<Longrightarrow> (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
        shows "rel_vpr_aux R P ctxt \<gamma> \<gamma>' ns res"
  using assms
  unfolding rel_vpr_aux_def
  by blast

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

subsection \<open>Well formedness of type relation\<close>

definition type_interp_rel_wf :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a vbpl_absval) absval_ty_fun  \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> bool"
  where "type_interp_rel_wf A_vpr A_bpl Trep \<equiv> 
    \<forall>v ty_vpr ty_bpl. get_type A_vpr v = ty_vpr \<longrightarrow>
                      vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl \<longrightarrow>
                      type_of_val A_bpl (val_rel_vpr_bpl v) = ty_bpl"

lemma type_interp_rel_wf_vbpl: 
  assumes "A_vpr = domain_type Trep"
    shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain tid where "domain_translation Trep (A_vpr a) = Some tid" and "ty_bpl = TCon tid []"
      by fastforce
    hence "vbpl_absval_ty Trep (ADomainVal a) = (tid, [])" using \<open>A_vpr = domain_type Trep\<close>
      by simp
    hence "type_of_vbpl_val Trep (AbsV (ADomainVal a)) = ty_bpl" using \<open>ty_bpl = _\<close>
      by simp
    thus ?thesis using VAbs
      by simp     
  qed (insert * **, auto)
qed

lemma type_interp_rel_wf_vbpl_no_domains:
  assumes "\<And> d. domain_translation Trep d = None"
  shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    fix contra
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain d where "domain_translation Trep (A_vpr a) = Some d"
      by fastforce
    with assms show contra 
      by simp
  qed (insert * **, auto)
qed

lemma vpr_to_bpl_val_type:
  assumes "get_type A v = ty_vpr" and
          "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl" and
          "domain_type TyRep = A"
  shows "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
proof (cases v)
  case (VAbs x5)
  then show ?thesis 
    using assms
    using type_interp_rel_wf_def type_interp_rel_wf_vbpl by blast
qed (insert assms, auto)

subsection \<open>Misc\<close>

definition field_rel_single :: "program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> char list \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  where "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl  \<equiv> 
           has_Some (\<lambda>f_tr. e_f_bpl = Lang.Var f_tr) (field_translation Tr f_vpr) \<and>
           has_Some (\<lambda>\<tau>_vpr. vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl) (declared_fields Pr f_vpr)"

lemma field_rel_single_intro:
  assumes "declared_fields Pr f_vpr = Some \<tau>_vpr" and
          "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl" and
          "field_translation Tr f_vpr = Some f_bpl" and
          "e_f_bpl = Lang.Var f_bpl"
        shows "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl"
  using assms
  unfolding field_rel_single_def
  by auto

lemma field_rel_single_elim:
  assumes
     "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl"
     "\<And> \<tau>_vpr f_bpl. 
      field_translation Tr f_vpr = Some f_bpl \<Longrightarrow>
      e_f_bpl = Lang.Var f_bpl \<Longrightarrow>
      declared_fields Pr f_vpr = Some \<tau>_vpr \<Longrightarrow>
      vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl \<Longrightarrow>
       P"
   shows P
  using assms
  unfolding field_rel_single_def
  by (meson has_Some_iff)
   
end