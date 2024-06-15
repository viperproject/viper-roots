section \<open>Relation between basic Viper and Boogie states\<close>
theory ViperBoogieBasicRel
imports TotalExpressions TotalSemantics ViperBoogieAbsValueInst BoogieInterface "HOL-Library.Disjoint_Sets" 
begin

text \<open>This section defines the relation between Viper and Boogie states, and proves some properties 
      of the relation.\<close>

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
     \<comment>\<open>the following constants are not required in the proof generation subset 
     | CKnownFoldedZeroMask
     | CEmptyFrame    \<close>

text \<open>The following records tracks options controlling whether certain parts of the state relation should
      or should not be enforced.\<close>

record state_rel_options = 
  consistent_state_rel_opt :: bool

definition default_state_rel_options :: state_rel_options
  where "default_state_rel_options \<equiv> \<lparr> consistent_state_rel_opt = True \<rparr>"

type_synonym label_hm_repr_bpl = "(label \<rightharpoonup> Lang.vname) \<times> (label \<rightharpoonup> Lang.vname)"

text \<open>The following record abstracts over elements in the Boogie encoding that are used to represent
Viper counterparts.\<close>

record tr_vpr_bpl =
  heap_var :: Lang.vname
  mask_var :: Lang.vname
  heap_var_def :: Lang.vname
  mask_var_def :: Lang.vname
  field_translation :: "field_ident \<rightharpoonup> Lang.vname"
  fun_translation :: "ViperLang.function_ident \<rightharpoonup> Lang.fname"
  var_translation :: "ViperLang.var \<rightharpoonup> Lang.vname" \<comment>\<open>local Boogie variables\<close>
  const_repr :: "boogie_const \<Rightarrow> Lang.vname"
  \<comment>\<open>mapping from labels (identifying labeled states) to their r Boogie heap and mask variables\<close>
  label_hm_translation :: label_hm_repr_bpl 
  state_rel_opt :: state_rel_options
  
 (*TODO: bound vars*)
(*  result_var :: "string" *)

lemma tr_def_field_translation:
  assumes "tr = tr_def" and
          "field_translation tr_def = F"
        shows "field_translation tr = F"
  using assms by simp

subsection \<open>Value relation\<close>

fun val_rel_vpr_bpl :: "'a vpr_val \<Rightarrow> 'a vbpl_val"
  where
    "val_rel_vpr_bpl (VInt i) = (IntV i)"
  | "val_rel_vpr_bpl (VBool b) = (BoolV b)"
  | "val_rel_vpr_bpl (VRef r) = (AbsV (ARef r))"
  | "val_rel_vpr_bpl (VAbs a) = (AbsV (ADomainVal a))"
  | "val_rel_vpr_bpl (VPerm p) = (RealV p)"

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

definition mask_rel :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> preal mask \<Rightarrow> 'a bpl_mask_ty \<Rightarrow> bool"
  where "mask_rel Pr tr_field m mb \<equiv> 
    (\<forall> l field_ty_vpr field_bpl. declared_fields Pr (snd l) = Some field_ty_vpr \<longrightarrow>
                      tr_field (snd l) = Some field_bpl \<longrightarrow>
                      mb (Address (fst l), NormalField field_bpl field_ty_vpr) = Rep_preal (m l))
 \<and>  (\<forall>f t. mb (Null, NormalField f t) = 0)
 \<and>  (\<forall>r f. mb (r,f) \<ge> 0 \<and> (is_bounded_field_bpl f \<longrightarrow> mb (r,f) \<le> 1))" 

lemma mask_rel_intro:
  assumes "\<And>l field_ty_vpr field_bpl. 
             declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
             tr_field (snd l) = Some field_bpl \<Longrightarrow> 
             mb (Address (fst l), NormalField field_bpl field_ty_vpr) = Rep_preal (m l)" and
          "\<And> f t. mb (Null, NormalField f t) = 0" and
          "\<And>r f. mb (r,f) \<ge> 0 \<and> (is_bounded_field_bpl f \<longrightarrow> mb (r,f) \<le> 1)"
  shows "mask_rel Pr tr_field m mb"
  using assms
  unfolding mask_rel_def 
  by blast

lemma mask_rel_elim:
  assumes "mask_rel Pr tr_field m mb" and
          "(\<And>l field_ty_vpr field_bpl. 
                declared_fields Pr (snd l) = Some field_ty_vpr \<Longrightarrow>
                tr_field (snd l) = Some field_bpl \<Longrightarrow> 
                mb (Address (fst l), NormalField field_bpl field_ty_vpr) = Rep_preal (m l)) \<Longrightarrow> 
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

definition heap_var_rel :: "ViperLang.program \<Rightarrow>  var_context \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> vname \<Rightarrow> 'a total_heap \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "heap_var_rel Pr \<Lambda> TyRep FieldTr hvar hv ns \<equiv>
                 (\<exists>hb. lookup_var \<Lambda> ns hvar = Some (AbsV (AHeap hb)) \<and>
                 lookup_var_ty \<Lambda> hvar = Some (TConSingle (THeapId TyRep)) \<and>
                 vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[]) \<and>
                 heap_rel Pr FieldTr hv hb) \<and>
                 total_heap_well_typed Pr (domain_type TyRep) hv"

definition mask_var_rel :: "ViperLang.program \<Rightarrow>  var_context \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> vname \<Rightarrow> preal mask \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where
    "mask_var_rel Pr \<Lambda> TyRep FieldTr mvar mv ns \<equiv>
                 (\<exists>mb. lookup_var \<Lambda> ns mvar = Some (AbsV (AMask mb)) \<and> 
                 lookup_var_ty \<Lambda> mvar = Some (TConSingle (TMaskId TyRep)) \<and> 
             \<comment>\<open>Since all Boogie masks \<^term>\<open>mb\<close> have the correct type, we don't add a typing constraint 
               (in contrast to Boogie heaps).\<close>                 
                 mask_rel Pr FieldTr mv mb)"

lemma heap_var_rel_stable:
  assumes "heap_var_rel Pr \<Lambda> TyRep FieldTr hvar hv ns" and
          "hv = hv'"
          "lookup_var \<Lambda> ns hvar = lookup_var \<Lambda> ns' hvar"        
        shows "heap_var_rel Pr \<Lambda> TyRep FieldTr hvar hv' ns'"
  using assms
  unfolding heap_var_rel_def
  by auto

lemma mask_var_rel_stable:
  assumes "mask_var_rel Pr \<Lambda> TyRep FieldTr mvar mv ns"
          "mv = mv'"
          "lookup_var \<Lambda> ns mvar = lookup_var \<Lambda> ns' mvar"
        shows "mask_var_rel Pr \<Lambda> TyRep FieldTr mvar mv' ns'"
  using assms
  unfolding mask_var_rel_def
  by auto
                           
abbreviation zero_mask_bpl :: "ref \<times> 'a vb_field \<Rightarrow> real"
  where "zero_mask_bpl \<equiv> \<lambda> _. 0"

lemma zero_mask_rel:
  shows "mask_rel Pr F zero_mask zero_mask_bpl"
  unfolding  mask_rel_def
  by (auto intro: if_SomeI simp: zero_preal.rep_eq zero_mask_def)

lemma zero_mask_rel_2:
  assumes "is_empty_total_full \<omega>"
  shows "mask_rel Pr F (get_mh_total_full \<omega>) zero_mask_bpl"
  using assms
  unfolding is_empty_total_full_def is_empty_total_def
  by (simp add: zero_mask_rel)

fun boogie_const_val :: "boogie_const => ('a vbpl_val)"
  where
    "boogie_const_val CNoPerm = RealV 0"
  | "boogie_const_val CWritePerm = RealV 1"
  | "boogie_const_val CNull = AbsV (ARef Null)"
  | "boogie_const_val CZeroMask = AbsV (AMask zero_mask_bpl)"
 \<comment>\<open> | "boogie_const_val CKnownFoldedZeroMask = AbsV (AKnownFoldedMask (\<lambda> _. False))"
    | "boogie_const_val CEmptyFrame = AbsV (AFrame EmptyFrame)" \<close>

fun boogie_const_ty :: "'a ty_repr_bpl \<Rightarrow> boogie_const => bpl_ty"
  where
    "boogie_const_ty T CNoPerm = TPrim TReal"
  | "boogie_const_ty T CWritePerm = TPrim TReal"
  | "boogie_const_ty T CNull = TConSingle (TRefId T)"
  | "boogie_const_ty T CZeroMask = TConSingle (TMaskId T)"
\<comment>\<open>  | "boogie_const_ty T CKnownFoldedZeroMask = TConSingle (TKnownFoldedMaskId T)"
  | "boogie_const_ty T CEmptyFrame = TConSingle (TFrameFragmentId T)"\<close>


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

fun lit_vpr_to_expr_bpl :: "(boogie_const \<Rightarrow> Lang.vname) \<Rightarrow> ViperLang.lit \<rightharpoonup> boogie_expr"
  where
    "lit_vpr_to_expr_bpl C (ViperLang.LInt i) = Some (Lit (Lang.LInt i))"
  | "lit_vpr_to_expr_bpl C (ViperLang.LBool i) = Some (Lit (Lang.LBool i))"
  | "lit_vpr_to_expr_bpl C (ViperLang.LPerm p) = (if p = 0 then Some (Var (C CNoPerm))
                                                  else (if p = 1 then Some (Var (C CWritePerm)) else None))"
  | "lit_vpr_to_expr_bpl C ViperLang.LNull = Some (Var (C CNull))"

definition lit_translation_rel :: "'a econtext_bpl => ('a vbpl_absval) nstate \<Rightarrow> (ViperLang.lit \<rightharpoonup> Lang.expr) \<Rightarrow> bool"
  where "lit_translation_rel ctxt ns litT \<equiv> (\<forall>lit e. litT lit = Some e \<longrightarrow> red_expr_bpl ctxt e ns (val_rel_vpr_bpl (val_of_lit lit)))"

lemma boogie_const_lit_rel:
  assumes "boogie_const_rel C (var_context ctxt) ns"
  shows "lit_translation_rel ctxt ns (lit_vpr_to_expr_bpl C)"
  unfolding lit_translation_rel_def
  apply ((rule allI | rule impI)+)
  apply (erule lit_vpr_to_expr_bpl.elims)
     apply (insert assms)
     apply (unfold boogie_const_rel_def)
  by (auto intro: RedVar RedLit split: if_split_asm)
 
definition store_rel :: "('a vbpl_absval) absval_ty_fun \<Rightarrow> var_context \<Rightarrow> (ViperLang.var \<rightharpoonup> Lang.vname) \<Rightarrow> 'a store \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "store_rel A \<Lambda> var_rel st ns \<equiv> 
          inj_on var_rel (dom var_rel) \<and>
          (\<forall> var_vpr var_bpl. var_rel var_vpr = Some var_bpl \<longrightarrow> 
                        (\<exists>val_vpr ty_bpl.
                                     (st var_vpr) = Some val_vpr \<and>
                                      lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                                      lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                                      type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl ))"

lemma store_rel_var_rel:
  assumes "store_rel A \<Lambda> var_tr st ns" and
          "var_tr var_vpr = Some var_bpl"
  shows "\<exists>val_vpr ty_bpl. st var_vpr = Some val_vpr \<and>
                     lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                     lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                     type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl"
  using assms
  unfolding store_rel_def
  by auto

lemma store_rel_var_rel_2:
  assumes "store_rel A \<Lambda> var_tr st ns"
      and "var_tr var_vpr = Some var_bpl"
  shows "\<exists>val_vpr. st var_vpr = Some val_vpr \<and>
                   lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr)"
  using assms store_rel_var_rel
  by blast
 
lemma store_rel_stable:
  assumes "store_rel A \<Lambda> var_tr st ns"
      and "st = st'"
      and "\<And>x. x \<in> ran var_tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
    shows "store_rel A \<Lambda> var_tr st' ns'"
  using assms
  unfolding store_rel_def
  by (simp add: ranI)

lemma store_rel_var_tr_inj:
  assumes "store_rel A \<Lambda> var_tr \<omega> ns"
  shows "inj_on var_tr (dom var_tr)"
  using assms
  by (simp add: store_rel_def)

definition field_rel :: "ViperLang.program \<Rightarrow> var_context \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname) \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "field_rel Pr \<Lambda> fd_tr ns \<equiv> 
        (inj_on fd_tr (dom fd_tr)) \<and>
        (\<forall>f f_vty. declared_fields Pr f = Some f_vty \<longrightarrow> 
             has_Some (\<lambda>f_bpl. lookup_var \<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (fd_tr f))"

lemma field_rel_stable:
  assumes "field_rel Pr \<Lambda> fd_tr ns" and
          "\<And>x. x \<in> ran fd_tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
        shows "field_rel Pr \<Lambda> fd_tr ns'"
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

lemma aux_vars_pred_sat_weaken:
  assumes AuxVarsPredSat: "aux_vars_pred_sat (var_context ctxt) AuxPred ns"
      and "dom AuxPred' \<subseteq> dom AuxPred"
      and WeakerPred: "\<And>x P' P v. AuxPred x = Some P \<Longrightarrow> AuxPred' x = Some P' \<Longrightarrow> P v \<Longrightarrow> P' v"
    shows "aux_vars_pred_sat (var_context ctxt) AuxPred' ns"
  unfolding aux_vars_pred_sat_def
  proof (rule allI | rule impI)+
    fix x P'
    assume "AuxPred' x = Some P'"
    moreover from this obtain P where "AuxPred x = Some P"
      using \<open>dom _ \<subseteq> dom _\<close>
      by blast

    ultimately show "has_Some P' (lookup_var (var_context ctxt) ns x)"
      using AuxVarsPredSat WeakerPred
      unfolding aux_vars_pred_sat_def
      by (metis has_Some_iff)
  qed  

definition label_rel :: "(vname \<Rightarrow> 'a total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool)  \<Rightarrow> (label \<rightharpoonup> vname) \<Rightarrow> 'a total_trace \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "label_rel P LabelMap t ns \<equiv> 
             (\<forall> lbl h. LabelMap lbl = Some h \<longrightarrow> (\<exists>\<phi>. t lbl = Some \<phi> \<and> P h \<phi> ns))"

definition label_hm_rel :: "ViperLang.program \<Rightarrow>  var_context \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> label_hm_repr_bpl \<Rightarrow> 'a total_trace \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "label_hm_rel Pr \<Lambda> TyRep FieldTr LabelMap t ns \<equiv>
             label_rel (\<lambda>h \<phi>. heap_var_rel Pr \<Lambda> TyRep FieldTr h (get_hh_total \<phi>)) (fst LabelMap) t ns
          \<and>  label_rel (\<lambda>m \<phi>. mask_var_rel Pr \<Lambda> TyRep FieldTr m (get_mh_total \<phi>)) (snd LabelMap) t ns
          \<and>  (\<forall> lbl \<phi>. t lbl = Some \<phi> \<longrightarrow> wf_mask_simple (get_mh_total \<phi>))"

lemma label_hm_rel_empty:
  \<comment>\<open>We need to assume that all members of the trace are well-formed\<close>
  assumes "\<forall>lbl \<phi>. t lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
    shows "label_hm_rel Pr \<Lambda> TyRep FieldTr (Map.empty, Map.empty) t ns"
  by (simp add: assms label_hm_rel_def label_rel_def)
  
definition vars_label_hm_tr :: "label_hm_repr_bpl \<Rightarrow> vname set"
  where "vars_label_hm_tr LabelMap \<equiv> (ran (fst LabelMap)) \<union> (ran (snd LabelMap))"

definition active_labels_hm_tr :: "label_hm_repr_bpl \<Rightarrow> label set"
  where "active_labels_hm_tr LabelMap = dom (fst LabelMap) \<union> dom (snd LabelMap)"

lemma label_hm_rel_stable:
  assumes "label_hm_rel Pr \<Lambda> TyRep FieldTr LabelMap t ns"
      and "t = t'"
      and "\<And> x. x \<in> vars_label_hm_tr LabelMap \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
    shows  "label_hm_rel Pr \<Lambda> TyRep FieldTr LabelMap t' ns'"
  using assms heap_var_rel_stable mask_var_rel_stable
  unfolding label_hm_rel_def vars_label_hm_tr_def label_rel_def
  by (metis (no_types, lifting) UnCI ranI)

abbreviation state_rel0_disj_list
  where "state_rel0_disj_list Tr AuxPred \<equiv> [{heap_var Tr, heap_var_def Tr},
                      {mask_var Tr, mask_var_def Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr)),
                      dom AuxPred,
                      vars_label_hm_tr (label_hm_translation Tr)]"

abbreviation state_rel0_disj_vars
  where "state_rel0_disj_vars Tr AuxPred \<equiv> \<Union> (set (state_rel0_disj_list Tr AuxPred))"


definition state_rel0 :: "ViperLang.program \<Rightarrow> 
                          ('a full_total_state \<Rightarrow> bool) \<Rightarrow>
                          ('a vbpl_absval) absval_ty_fun \<Rightarrow> 
                          var_context \<Rightarrow> 
                          'a ty_repr_bpl \<Rightarrow> 
                          tr_vpr_bpl \<Rightarrow> 
                          'a aux_vars_pred \<Rightarrow> 
                          'a full_total_state \<Rightarrow>                   
                          'a full_total_state \<Rightarrow>
                          ('a vbpl_absval) nstate \<Rightarrow> 
                          bool"
  where "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns \<equiv> 
         \<comment>\<open>field permissions can be at most one\<close>
            wf_mask_simple (get_mh_total_full \<omega>def) \<and>
            wf_mask_simple (get_mh_total_full \<omega>) \<and>
         \<comment>\<open>The state consistency predicate must hold if the option is set. The reason for having an
            option here is because there are cases where one wants to prove the state relation w.r.t.
            some consistent Viper state via multiple intermediate Viper states that may not be 
            consistent (in such a case one can temporarily disable the state consistency)\<close> 
            ((consistent_state_rel_opt (state_rel_opt Tr)) \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>) \<and>
         \<comment>\<open>type interpretation must be the expected one\<close>
           (A = vbpl_absval_ty TyRep) \<and>
         \<comment>\<open>Store relation (only Viper variables, auxiliaries are not included)\<close>
           store_rel A \<Lambda> (var_translation Tr) (get_store_total \<omega>) ns \<and>           
          \<comment>\<open>Disjointness condition for variables tracked by the relation\<close>
           disjoint_list (state_rel0_disj_list Tr AuxPred) \<and>
          \<comment>\<open>well-def state and evaluation state differ only on mask\<close>
           (
             get_store_total \<omega>def = get_store_total \<omega> \<and>
             get_trace_total \<omega>def = get_trace_total \<omega> \<and>
             get_h_total_full \<omega>def = get_h_total_full \<omega>
           ) \<and>
          \<comment>\<open>heap and mask relation for evaluation state\<close>
           heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>) ns \<and>
           mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>) ns \<and> 
          \<comment>\<open>heap and mask relation for well-definedness state\<close>
           heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def) ns \<and>
           mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def) ns \<and>      
          \<comment>\<open>field relation\<close>
           field_rel Pr \<Lambda> (field_translation Tr) ns \<and>
          \<comment>\<open>Boogie constants relation\<close>
           boogie_const_rel (const_repr Tr) \<Lambda> ns \<and>
           \<comment>\<open>Boogie state is well-typed (used to show well-typedness of Boogie expressions)\<close>
           state_well_typed A \<Lambda> [] ns \<and>
           \<comment>\<open>auxiliary variable constraints are satisfied\<close>
           aux_vars_pred_sat \<Lambda> AuxPred ns \<and>
           \<comment>\<open>Labeled states are captured. Note that for the general case one will have to 
             generalize this conjunct to depend on the Boogie state, since whether a labeled
             state is active in general is expressed via Boolean Boogie variable.\<close>
           label_hm_rel Pr \<Lambda> TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"

definition state_rel
  where "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<equiv> 
          state_rel0 Pr StateCons (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"

abbreviation state_rel_def_same
  where "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns \<equiv> state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns"

definition state_rel_empty
  where "state_rel_empty R \<omega> ns \<equiv> is_empty_total_full \<omega> \<and> R \<omega> ns"

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

  rename_tac i6,
  case_tac i6,
  simp,
  
  blast)

subsection \<open>Store relationship properties\<close>

definition store_var_rel_aux
  where "store_var_rel_aux A \<Lambda> st ns var_vpr var_bpl \<equiv>
           (\<exists>val_vpr ty_bpl.
                              st var_vpr = Some val_vpr \<and>
                              lookup_var \<Lambda> ns var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                              lookup_var_ty \<Lambda> var_bpl = Some ty_bpl \<and>
                              type_of_val A (val_rel_vpr_bpl val_vpr) = ty_bpl )"


lemma store_relI:
  assumes "inj_on f (dom f)"
          "\<And> var_vpr var_bpl. f var_vpr = Some var_bpl \<Longrightarrow>
                        store_var_rel_aux A \<Lambda> st ns var_vpr var_bpl"
  shows "store_rel A \<Lambda> f st ns"
  using assms
  unfolding store_rel_def store_var_rel_aux_def
  by blast

lemma store_rel_add_new_var:
  assumes StoreRel: "store_rel A \<Lambda> var_tr st ns"
      and "v' = val_rel_vpr_bpl v"
      and "var_tr' = var_tr(x_vpr \<mapsto> x_bpl)"
      and LookupVarTyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
      and TypeOfValBpl: "type_of_val A v' = ty"
      and "x_bpl \<notin> ran var_tr"
    shows "store_rel A \<Lambda> var_tr' (st(x_vpr \<mapsto> v)) (update_var \<Lambda> ns x_bpl v')"
proof (rule store_relI)
  show "inj_on var_tr' (dom var_tr')"
    unfolding inj_on_def
  proof clarify
    fix x0 x1 y0 y1
    assume InjAssms: "var_tr' x0 = Some y0" "var_tr' x1 = Some y1" "var_tr' x0 = var_tr' x1"
    thus "x0 = x1"
    proof (cases "x_vpr \<notin> {x0,x1}")
      case True
      then show ?thesis 
        using store_rel_var_tr_inj[OF StoreRel] InjAssms
        unfolding \<open>var_tr' = _\<close>
        by (simp add: domI inj_on_def)
    next
      case False
      hence "y0 = x_bpl \<and> y1 = x_bpl"
        using InjAssms
        unfolding \<open>var_tr' = _\<close>
        by auto
      hence "x0 = x_vpr \<and> x1 = x_vpr"
        using InjAssms \<open>x_bpl \<notin> ran var_tr\<close>
        unfolding \<open>var_tr' = _\<close>
        by (meson map_upd_Some_unfold ranI)
      thus ?thesis
        by simp
    qed
  qed
next
  fix var_vpr var_bpl
  assume "var_tr' var_vpr = Some var_bpl"
  let ?st' = "st(x_vpr \<mapsto> v)"
  let ?ns' = "update_var \<Lambda> ns x_bpl v'"

  show "store_var_rel_aux A \<Lambda> ?st' ?ns' var_vpr var_bpl"
  proof (cases "var_vpr = x_vpr")
    case True
    moreover from this have "var_bpl = x_bpl"
      using \<open>var_tr' var_vpr = Some var_bpl\<close>
      unfolding \<open>var_tr' = _\<close>
      by simp
    ultimately show ?thesis
      unfolding store_var_rel_aux_def
      using LookupVarTyBpl TypeOfValBpl \<open>v' = _\<close>
      by auto
  next
    case False
    moreover from this have "var_bpl \<noteq> x_bpl"
      using \<open>var_tr' var_vpr = Some var_bpl\<close>
            assms ranI by force

    moreover from \<open>var_vpr \<noteq> x_vpr\<close> have "var_tr var_vpr = Some var_bpl"
      using \<open>var_tr' var_vpr = Some var_bpl\<close>
      by (simp add: \<open>var_tr' = _\<close>)

    ultimately show ?thesis 
      unfolding store_var_rel_aux_def
      using StoreRel[simplified store_rel_def] \<open>var_vpr \<noteq> x_vpr\<close>
      by auto
  qed
qed

lemma store_rel_update:
  assumes 
       StoreRel: "store_rel A \<Lambda> var_tr st ns" and 
       "v' = val_rel_vpr_bpl v" and
       VarTrX: "var_tr x_vpr = Some x_bpl" and
       TyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
              "type_of_val A v' = ty"
   shows
       "store_rel A \<Lambda> var_tr (st(x_vpr \<mapsto> v)) (update_var \<Lambda> ns x_bpl v')"
  unfolding store_rel_def
proof (rule conjI, insert StoreRel, fastforce simp: store_rel_def, (rule allI | rule impI)+)
  fix var_vpr var_bpl
  assume VarTr: "var_tr var_vpr = Some var_bpl"
  show "\<exists>val_vpr ty_bpl.          
          (st(x_vpr \<mapsto> v)) var_vpr = Some val_vpr \<and>
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
      "(st(x_vpr \<mapsto> v)) var_vpr = Some v_vpr" and
      "lookup_var \<Lambda> (update_var \<Lambda> ns x_bpl v') var_bpl = Some (val_rel_vpr_bpl v_vpr)"
      "lookup_var_ty \<Lambda> var_bpl = Some ty_bpl" and
      "type_of_val A (val_rel_vpr_bpl v_vpr) = ty_bpl"
      unfolding store_rel_def
      by fastforce      
    then show ?thesis 
      by simp      
  qed
qed

text \<open>The following lemma shows when the store relation is preserved if one renames or deletes
      Viper variables. The function \<^term>\<open>f\<close> specifies whether a variable is renamed (i.e., if
      \<^term>\<open>i\<close> is in the domain of \<^term>\<open>f\<close>, then \<^term>\<open>i\<close> is renamed to \<^term>\<open>the (f i)\<close> and otherwise 
      the variable is deleted.\<close>

lemma store_rel_update_vpr_rename_or_delete:
  assumes StoreRel: "store_rel A \<Lambda> var_tr st ns"   
      and "inj_on f (dom f)"
      and InsideDomEq: "\<And>i. i \<in> dom f \<Longrightarrow> var_tr' i = var_tr (the (f i))"
      and OutsideDomEq: "\<And>i. i \<notin> dom f \<Longrightarrow> var_tr' i = None"
      and InsideDomStore: "\<And>i y. f i = Some y \<Longrightarrow> y \<in> dom var_tr \<Longrightarrow> st' i = st (the (f i))"
    shows "store_rel A \<Lambda> var_tr' st' ns"
proof (rule store_relI)
  show "inj_on var_tr' (dom var_tr')"
    using assms
    by (smt (verit) domIff inj_onD inj_onI option.expand store_rel_var_tr_inj)
next
  fix var_vpr var_bpl
  assume "var_tr' var_vpr = Some var_bpl"

  from this obtain var_vpr' where "f var_vpr = Some var_vpr'"
    using InsideDomEq OutsideDomEq
    by fastforce
  from this have "var_tr var_vpr' = Some var_bpl"
    using InsideDomEq \<open>var_tr' var_vpr = Some var_bpl\<close>
    by fastforce        

  thus "store_var_rel_aux A \<Lambda> st' ns var_vpr var_bpl "
    unfolding store_var_rel_aux_def
    using StoreRel[simplified store_rel_def] InsideDomStore \<open>f var_vpr = Some _\<close>
    by (simp add: domI)
qed  

lemma store_rel_unshift:
  assumes "store_rel A \<Lambda> var_tr st ns"
  shows "store_rel A \<Lambda> (unshift_2 n var_tr) (unshift_2 n st) ns"
  apply (rule store_rel_update_vpr_rename_or_delete[where ?f = "\<lambda>x. Some (x+n)", OF assms])
     apply (metis (mono_tags, lifting) add_right_cancel injD inj_Some inj_onI)
  by (auto simp: unshift_2_def)

lemma store_rel_shift:
  assumes "store_rel A \<Lambda> var_tr st ns"
  shows "store_rel A \<Lambda> (DeBruijn.shift n var_tr) (DeBruijn.shift n st) ns"
  apply (rule store_rel_update_vpr_rename_or_delete[where ?f = "\<lambda>x. if x < n then None else Some (x-n)", OF assms])
     apply (fastforce simp: inj_on_def split: if_split_asm)
    apply (fastforce simp: DeBruijn.shift_def split: if_split_asm)
   apply (fastforce simp: DeBruijn.shift_def split: if_split_asm )
  by (fastforce simp add: DeBruijn.shift_def split: if_split_asm)

subsection \<open>State relationship properties\<close>

abbreviation state_rel_ext :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                               'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool"
  where "state_rel_ext R \<omega>def \<omega> ns \<equiv> R \<omega> ns \<and> \<omega>def = \<omega>"

lemma state_rel_state_rel0:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  shows "state_rel0 Pr StateCons (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"
  using assms
  by (simp add: state_rel_def)

lemma state_rel0_state_rel:
  assumes "state_rel0 Pr StateCons (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  using assms
  by (simp add: state_rel_def)

lemma state_rel0_wf_mask_simple:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "wf_mask_simple (get_mh_total_full \<omega>)"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_wf_mask_simple = state_rel0_wf_mask_simple[OF state_rel_state_rel0]

lemma state_rel0_consistent:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
      and "consistent_state_rel_opt (state_rel_opt Tr)"
  shows "StateCons \<omega>def \<and> StateCons \<omega>"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_consistent = state_rel0_consistent[OF state_rel_state_rel0]

lemma state_rel0_wf_mask_def_simple:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "wf_mask_simple (get_mh_total_full \<omega>def)"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_wf_mask_def_simple = state_rel0_wf_mask_def_simple[OF state_rel_state_rel0]

lemma state_rel0_type_interp:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "A = vbpl_absval_ty TyRep"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_type_interp = state_rel0_type_interp[OF state_rel_state_rel0]

lemma state_rel0_store_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "store_rel A \<Lambda> (var_translation Tr) (get_store_total \<omega>) ns"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_store_rel = state_rel0_store_rel[OF state_rel_state_rel0]

lemmas state_rel_var_rel = store_rel_var_rel_2[OF state_rel_store_rel]

lemma state_rel_var_tr_inj:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  shows "inj_on (var_translation Tr) (dom (var_translation Tr))"
  using state_rel_store_rel[OF assms]
  unfolding store_rel_def
  by blast

lemma state_rel0_disjoint:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "disjoint_list (state_rel0_disj_list Tr AuxPred)"
  using assms        
  unfolding state_rel0_def
  by blast

lemmas state_rel_disjoint = state_rel0_disjoint[OF state_rel_state_rel0]

lemma heap_var_disjoint:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          "hvar = heap_var_def Tr \<or> hvar = heap_var Tr"
  shows "hvar \<noteq> mask_var Tr \<and> hvar \<noteq> mask_var_def Tr \<and> hvar \<notin> ran (var_translation Tr) \<and>
         hvar \<notin> ran (field_translation Tr) \<and> hvar \<notin> range (const_repr Tr) \<and>
         hvar \<notin> dom AuxPred \<and>
         hvar \<notin> vars_label_hm_tr (label_hm_translation Tr)"
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

  apply (erule allE[where ?x=0])
  apply (erule allE[where ?x=6])
  apply force
  done

lemmas state_rel_heap_var_disjoint = heap_var_disjoint[OF state_rel_state_rel0]

lemma mask_var_disjoint:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          "mvar = mask_var_def Tr \<or> mvar = mask_var Tr"
  shows "mvar \<noteq> heap_var Tr \<and> mvar \<noteq> heap_var_def Tr \<and> mvar \<notin> ran (var_translation Tr) \<and>
         mvar \<notin> ran (field_translation Tr) \<and> mvar \<notin> range (const_repr Tr) \<and>
         mvar \<notin> dom AuxPred \<and>
         mvar \<notin> vars_label_hm_tr (label_hm_translation Tr)"
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

  apply (erule allE[where ?x=1])
  apply (erule allE[where ?x=6])
  apply force
  done

lemmas state_rel_mask_var_disjoint = mask_var_disjoint[OF state_rel_state_rel0]

lemma set_inter_union_conj: "A \<inter> B = {} \<and> A \<inter> C = {} \<Longrightarrow> A \<inter> (B \<union> C) = {}"
  by auto

lemma var_translation_disjoint0:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "ran (var_translation Tr) \<inter> ( {heap_var Tr, heap_var_def Tr} \<union>
                                      {mask_var Tr, mask_var_def Tr} \<union>
                                       ran (field_translation Tr) \<union>
                                       range (const_repr Tr) \<union>
                                       dom AuxPred \<union>
                                       vars_label_hm_tr (label_hm_translation Tr)) = {}"

  apply (rule set_inter_union_conj, rule conjI)+
  using state_rel0_disjoint[OF assms(1)]
    apply (unfold disjoint_list_def)

       apply (erule allE[where ?x=0])
     apply (erule allE[where ?x=2])
     apply simp

       apply (erule allE[where ?x=1])
     apply (erule allE[where ?x=2])
    apply simp

       apply (erule allE[where ?x=3])
     apply (erule allE[where ?x=2])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=4])
   apply (erule allE[where ?x=2])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=5])
   apply (erule allE[where ?x=2])
   apply (simp add: disjnt_def inf_commute)

  apply (erule allE[where ?x=6])
  apply (erule allE[where ?x=2])
  apply (simp add: disjnt_def inf_commute)
  done

lemmas var_translation_disjoint = var_translation_disjoint0[OF state_rel_state_rel0]

lemma state_rel0_aux_pred_disjoint:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "dom AuxPred \<inter> ( {heap_var Tr, heap_var_def Tr} \<union>
                                      {mask_var Tr, mask_var_def Tr} \<union>
                                       ran (var_translation Tr) \<union>
                                       ran (field_translation Tr) \<union>
                                       range (const_repr Tr) \<union>
                                       vars_label_hm_tr (label_hm_translation Tr)) = {}"
  apply (rule set_inter_union_conj, rule conjI)+
  using state_rel0_disjoint[OF assms(1)]
    apply (unfold disjoint_list_def)

       apply (erule allE[where ?x=0])
     apply (erule allE[where ?x=5])
     apply simp

       apply (erule allE[where ?x=1])
     apply (erule allE[where ?x=5])
    apply simp

       apply (erule allE[where ?x=2])
     apply (erule allE[where ?x=5])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=3])
   apply (erule allE[where ?x=5])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=4])
   apply (erule allE[where ?x=5])
   apply (simp add: disjnt_def inf_commute)

  apply (erule allE[where ?x=6])
  apply (erule allE[where ?x=5])
  apply (simp add: disjnt_def inf_commute)
  done

lemmas state_rel_aux_pred_disjoint = state_rel0_aux_pred_disjoint[OF state_rel_state_rel0]

lemma state_rel0_eval_welldef_eq:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "get_store_total \<omega>def = get_store_total \<omega> \<and>
         get_trace_total \<omega>def = get_trace_total \<omega> \<and>
         get_h_total_full \<omega>def = get_h_total_full \<omega>"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_eval_welldef_eq = state_rel0_eval_welldef_eq[OF state_rel_state_rel0]

lemma state_rel0_heap_var_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>) ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_heap_var_rel = state_rel0_heap_var_rel[OF state_rel_state_rel0]

lemma state_rel0_heap_var_def_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def) ns"
  using assms
  by (fastforce simp add: state_rel0_def)

lemmas state_rel_heap_var_def_rel = state_rel0_heap_var_def_rel[OF state_rel_state_rel0]

lemma state_rel0_mask_var_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>) ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_mask_var_rel = state_rel0_mask_var_rel[OF state_rel_state_rel0]

lemma state_rel0_mask_var_def_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def) ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_mask_var_def_rel = state_rel0_mask_var_def_rel[OF state_rel_state_rel0]

lemma state_rel0_field_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "field_rel Pr \<Lambda> (field_translation Tr) ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_field_rel = state_rel0_field_rel[OF state_rel_state_rel0]

lemma state_rel0_boogie_const_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "boogie_const_rel (const_repr Tr) \<Lambda> ns"
  using assms
  unfolding state_rel0_def
  by simp

lemmas state_rel_boogie_const_rel = state_rel0_boogie_const_rel[OF state_rel_state_rel0]

lemmas state_rel_lit_rel = boogie_const_lit_rel[OF state_rel_boogie_const_rel]

lemma state_rel_boogie_const_rel_2:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "C = const_repr Tr"
  shows "boogie_const_rel C (var_context ctxt) ns"
  using assms
  unfolding state_rel_def state_rel0_def
  by simp

lemma state_rel0_state_well_typed:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "state_well_typed A \<Lambda> [] ns"
  using assms
  unfolding state_rel0_def
  by blast

lemmas state_rel_state_well_typed = state_rel0_state_well_typed[OF state_rel_state_rel0]

text \<open>Once quantifiers are supported, the state relation will have to be adjusted such that non-empty
 binder states are possible.\<close>

lemma state_rel0_binder_empty:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" 
  shows "binder_state ns = Map.empty"
  using state_rel0_state_well_typed[OF assms, simplified state_well_typed_def]
  by simp

lemmas state_rel_binder_empty = state_rel0_binder_empty[OF state_rel_state_rel0]

lemma state_rel0_aux_vars_pred_sat:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "aux_vars_pred_sat \<Lambda> AuxPred ns"
  using assms
  unfolding state_rel0_def
  by blast

lemmas state_rel_aux_vars_pred_sat = state_rel0_aux_vars_pred_sat[OF state_rel_state_rel0]

lemma state_rel_obtain_mask:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  obtains mb 
  where "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
        "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
        "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
  using state_rel0_mask_var_rel[OF state_rel_state_rel0[OF StateRel]]
  unfolding mask_var_rel_def
  by blast

lemma state_rel_aux_pred_sat_lookup:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
  shows "has_Some P  (lookup_var (var_context ctxt) ns aux_var)"
  using assms state_rel_aux_vars_pred_sat
  unfolding state_rel_def aux_vars_pred_sat_def
  by blast

lemma state_rel_aux_pred_sat_lookup_2:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
  shows "\<exists>v. lookup_var (var_context ctxt) ns aux_var = Some v \<and> P v"
  using assms state_rel_aux_vars_pred_sat has_Some_iff state_rel_aux_pred_sat_lookup
  unfolding state_rel_def
  by fastforce

lemma state_rel_aux_pred_sat_lookup_2_elim:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some P"
        obtains v where "lookup_var (var_context ctxt) ns aux_var = Some v" and "P v"
  using assms state_rel_aux_pred_sat_lookup_2
  by blast

lemma state_rel_aux_pred_sat_lookup_3:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some (pred_eq v)"
  shows "lookup_var (var_context ctxt) ns aux_var = Some v"
  using state_rel_aux_pred_sat_lookup_2[OF assms]
  by (simp add: pred_eq_def)

lemma state_rel_aux_pred_sat_lookup_3_elim:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "AuxPred aux_var = Some (pred_eq v)"
  shows "lookup_var (var_context ctxt) ns aux_var = Some v"
  using state_rel_aux_pred_sat_lookup_2[OF assms]
  by (simp add: pred_eq_def)

lemma state_rel_aux_pred_weaken:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          "dom AuxPred' \<subseteq> dom AuxPred" and
          WeakerPred: "\<And>x P' P v. AuxPred x = Some P \<Longrightarrow> AuxPred' x = Some P' \<Longrightarrow> P v \<Longrightarrow> P' v"
        shows "state_rel Pr StateCons TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
  note StateRel0 = state_rel_state_rel0[OF StateRel]

  show "aux_vars_pred_sat (var_context ctxt) AuxPred' ns"
    using aux_vars_pred_sat_weaken[OF state_rel0_aux_vars_pred_sat[OF StateRel0]] \<open>dom _ \<subseteq> dom _\<close> WeakerPred
    by blast

  (* TODO: adjust the tactic disjoint_list_subset_tac such that it can be applied here *)
  show "disjoint_list (state_rel0_disj_list Tr AuxPred')" (is "disjoint_list ?A'")

  proof (rule disjoint_list_subset[OF state_rel0_disjoint[OF StateRel0]], simp)
    fix i j
    assume "0 \<le> i" and
           "i < length
                (state_rel0_disj_list Tr AuxPred)" (is "i < length ?A")
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
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and "AuxPred' \<subseteq>\<^sub>m AuxPred"
    shows "state_rel Pr StateCons TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
  apply (rule state_rel_aux_pred_weaken[OF assms(1)])
   apply (rule map_le_implies_dom_le[OF assms(2)])
  using \<open>AuxPred' \<subseteq>\<^sub>m AuxPred\<close>
  by (metis (no_types, lifting) dom_fun_upd fun_upd_triv insertCI map_le_def option.distinct(1) option.sel)

lemma state_rel0_label_hm_rel:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "label_hm_rel Pr \<Lambda> TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
  using assms
  by (simp add: state_rel0_def)

lemmas state_rel_label_hm_rel = state_rel0_label_hm_rel[OF state_rel_state_rel0]
                                   
lemma state_rel0_label_hm_disjoint:
  assumes "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
  shows "vars_label_hm_tr (label_hm_translation Tr) \<inter> ( {heap_var Tr, heap_var_def Tr} \<union>
                                      {mask_var Tr, mask_var_def Tr} \<union>
                                       ran (var_translation Tr) \<union>
                                       ran (field_translation Tr) \<union>
                                       range (const_repr Tr) \<union>
                                       dom AuxPred) = {}"
  apply (rule set_inter_union_conj, rule conjI)+
  using state_rel0_disjoint[OF assms(1)]
    apply (unfold disjoint_list_def)

       apply (erule allE[where ?x=0])
     apply (erule allE[where ?x=6])
     apply simp

       apply (erule allE[where ?x=1])
     apply (erule allE[where ?x=6])
    apply simp

       apply (erule allE[where ?x=2])
     apply (erule allE[where ?x=6])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=3])
   apply (erule allE[where ?x=6])
    apply (simp add: disjnt_def inf_commute)

       apply (erule allE[where ?x=4])
   apply (erule allE[where ?x=6])
   apply (simp add: disjnt_def inf_commute)

  apply (erule allE[where ?x=5])
  apply (erule allE[where ?x=6])
  apply (simp add: disjnt_def inf_commute)
  done

lemmas state_rel_label_hm_disjoint = state_rel0_label_hm_disjoint[OF state_rel_state_rel0]

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
  assumes StateRel: "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
      and "Tr' = Tr\<lparr>var_translation := f\<rparr>"
      and WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>'"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr') \<Longrightarrow> StateCons \<omega>'"
      and OnlyStoreAffectedVpr: 
           "get_total_full \<omega> = get_total_full \<omega>' \<and> get_trace_total \<omega> = get_trace_total \<omega>'"
      and OnlyStoreAffectedBpl: "\<And>x. x \<notin> ran f \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
      and StoreRel: "store_rel A \<Lambda> f (get_store_total \<omega>') ns'"
      and ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x"
      and OldStateEq: "old_global_state ns' = old_global_state ns"
      and BinderEmpty: "binder_state ns' = Map.empty"
      and RanVarTrDisj:    "ran f \<inter> ( {heap_var Tr, heap_var_def Tr} \<union>
                                      {mask_var Tr, mask_var_def Tr} \<union>
                                       ran (field_translation Tr) \<union>
                                       range (const_repr Tr) \<union>
                                       dom AuxPred \<union>
                                       vars_label_hm_tr (label_hm_translation Tr)) = {}"
    shows "state_rel0 Pr StateCons A \<Lambda> TyRep Tr' AuxPred \<omega>def' \<omega>' ns'"
  unfolding state_rel0_def
proof (intro conjI)
  show "wf_mask_simple (get_mh_total_full \<omega>def')"
    using state_rel0_wf_mask_simple[OF StateRel] OnlyStoreAffectedVpr WellDefSame    
    by fastforce

  show "wf_mask_simple (get_mh_total_full \<omega>')"
    using state_rel0_wf_mask_simple[OF StateRel] OnlyStoreAffectedVpr    
    by fastforce

  show "store_rel A \<Lambda> (var_translation Tr') (get_store_total \<omega>') ns'"
    using StoreRel \<open>Tr' = _\<close>
    by simp

  show "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
  proof -
    from state_rel0_disjoint[OF StateRel]
    have "disjoint_list
          ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}]@
           (ran (var_translation Tr) # [ran (field_translation Tr), range (const_repr Tr), dom AuxPred,
             vars_label_hm_tr (label_hm_translation Tr)]))" (is "disjoint_list (?xs@(?M#?ys))")
      by simp
    hence "disjoint_list (?xs@ran f#?ys)"
      apply (rule disjoint_list_replace_set)
      using RanVarTrDisj
      unfolding disjnt_def
      by fastforce
    thus ?thesis
      by (simp add: \<open>Tr' = _\<close>)
  qed

  show "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>') ns'"
  proof -
    have "lookup_var \<Lambda> ns (heap_var Tr) = lookup_var \<Lambda> ns' (heap_var Tr)"
    proof -
      from RanVarTrDisj
      have "heap_var Tr \<notin> ran f"
        by fastforce
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
    using heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel]] OnlyStoreAffectedVpr
    by (auto simp: \<open>Tr' = _\<close>)
  qed

  show "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full \<omega>def') ns'"
  proof -   
    have "lookup_var \<Lambda> ns (heap_var_def Tr) = lookup_var \<Lambda> ns' (heap_var_def Tr)"
    proof -
      from RanVarTrDisj
      have "heap_var_def Tr \<notin> ran f"
        by blast        
        
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis    
    using heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel]] OnlyStoreAffectedVpr WellDefSame
    by (simp add: \<open>Tr' = _\<close>)
  qed

  show "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr') (mask_var Tr') (get_mh_total_full \<omega>') ns'"
  proof -  
    have "lookup_var \<Lambda> ns (mask_var Tr) = lookup_var \<Lambda> ns' (mask_var Tr)"
    proof -
      from RanVarTrDisj
      have "mask_var Tr \<notin> ran f"
        by blast
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
    using  mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel]] OnlyStoreAffectedVpr
    by (auto simp: \<open>Tr' = _\<close>)
  qed 

  show "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr') (mask_var_def Tr') (get_mh_total_full \<omega>def') ns'"
  proof -  
    have "lookup_var \<Lambda> ns (mask_var_def Tr) = lookup_var \<Lambda> ns' (mask_var_def Tr)"
    proof -
      from RanVarTrDisj
      have "mask_var_def Tr \<notin> ran f"
        by blast
      thus ?thesis
        using OnlyStoreAffectedBpl
        by blast
    qed
    thus ?thesis
      using mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel]] OnlyStoreAffectedVpr WellDefSame
      by (auto simp: \<open>Tr' = _\<close>)
  qed 

  show "field_rel Pr \<Lambda> (field_translation Tr') ns'"
  proof (simp add: \<open>Tr' = _\<close>, rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
    fix x
     assume FieldElem: "x \<in> ran (field_translation Tr)"
     from RanVarTrDisj have
        "ran (field_translation Tr) \<inter> (ran f) = {}"
       by blast
      
    thus "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
      using OnlyStoreAffectedBpl FieldElem by blast
  qed

  show "boogie_const_rel (const_repr Tr') \<Lambda> ns'"
  proof (simp add: \<open>Tr' = _\<close>, rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
    fix x
    assume ConstElem: "x \<in> range (const_repr Tr)"
    from RanVarTrDisj have
      "ran f \<inter> range (const_repr Tr) = {}"
      by blast
    thus "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
      using OnlyStoreAffectedBpl ConstElem by blast
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
      proof (cases "x \<in> ran (var_translation Tr')")
        case True
        from this obtain x_vpr where "var_translation Tr' x_vpr = Some x"          
          by (auto simp add: ran_def)          
        with LookupTy obtain v where
          "lookup_var \<Lambda> ns' x = Some v" and 
          "type_of_val A v = t"
          using store_rel_var_rel[OF StoreRel] \<open>Tr' = _\<close>
          by force                    
        then show ?thesis
          by simp        
      next
        case False
        hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"
          using OnlyStoreAffectedBpl \<open>Tr' = _\<close>
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
    from RanVarTrDisj
    have "ran f \<inter> dom  AuxPred = {}"
      by fast
      
    thus "aux_vars_pred_sat \<Lambda> AuxPred ns'"
      using state_rel0_aux_vars_pred_sat[OF StateRel] OnlyStoreAffectedBpl
      unfolding aux_vars_pred_sat_def
      by fastforce
  qed

  show "label_hm_rel Pr \<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total \<omega>') ns'"
    apply (simp add: \<open>Tr' = _\<close>)
    apply (rule label_hm_rel_stable[OF state_rel0_label_hm_rel[OF StateRel]])
       apply (simp add: OnlyStoreAffectedVpr)
      using OnlyStoreAffectedBpl RanVarTrDisj
      by blast
qed (insert StateRel WellDefSame Consistent, unfold state_rel0_def, auto)

lemmas state_rel_store_update = state_rel0_state_rel[OF state_rel0_store_update[OF state_rel_state_rel0]]

lemma state_rel0_store_update_same_tr:
  assumes StateRel: "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
      and WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>'"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>'"
      and OnlyStoreAffectedVpr: 
           "get_total_full \<omega> = get_total_full \<omega>' \<and> get_trace_total \<omega> = get_trace_total \<omega>'"
      and OnlyStoreAffectedBpl: "(\<And>x. x \<notin> ran (var_translation Tr) \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)"
      and StoreRel: "store_rel A \<Lambda> (var_translation Tr) (get_store_total \<omega>') ns'"
      and ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x"
      and OldStateEq: "old_global_state ns' = old_global_state ns"
      and BinderEmpty: "binder_state ns' = Map.empty"
   shows "state_rel0 Pr StateCons A \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'"
  apply (rule state_rel0_store_update[where ?Tr = Tr and ?f = "(var_translation Tr)", OF StateRel])
  using assms apply simp_all
  using var_translation_disjoint0[OF StateRel]
  by simp

lemmas state_rel_store_update_same_tr = state_rel0_state_rel[OF state_rel0_store_update_same_tr[OF state_rel_state_rel0]]

lemma state_rel_store_update_2:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and WellDefSame: "\<omega>def = \<omega>"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_var_total \<omega> x_vpr v)"
      and  VarCtxt: "\<Lambda> = var_context ctxt"
      and VarTr: "var_translation Tr x_vpr = Some x_bpl"
      and "v' = val_rel_vpr_bpl v"
      and TyBpl: "lookup_var_ty \<Lambda> x_bpl = Some ty"
              "type_of_val (type_interp ctxt) v' = ty"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt (update_var_total \<omega>def x_vpr v) (update_var_total \<omega> x_vpr v) (update_var \<Lambda> ns x_bpl v')"
  apply (rule state_rel_store_update_same_tr[OF StateRel _ Consistent])
         apply (simp add: WellDefSame)
        apply simp
       apply simp
      using VarCtxt VarTr ranI 
      apply fastforce
      using state_rel0_store_rel[OF state_rel_state_rel0[OF StateRel]] assms store_rel_update
     apply fastforce
    apply (metis VarCtxt global_state_update_local global_state_update_other option.exhaust)
   apply (simp add: update_var_old_global_same)
  using state_rel0_state_well_typed[OF state_rel_state_rel0[OF StateRel]]
  unfolding state_well_typed_def
  apply (simp add: update_var_binder_same)
  done

lemma state_rel_new_auxvar:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and AuxVarFresh: "aux_var \<notin> state_rel0_disj_vars Tr AuxPred"
     (*AuxVarFresh: "aux_var \<notin> 
                      ({heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union>
                      vars_label_hm_tr (label_hm_translation Tr))"  and   *)          
      and "P aux_val"
      and "type_interp ctxt = vbpl_absval_ty TyRep"
      and LookupTy: "lookup_var_ty (var_context ctxt) aux_var = Some \<tau>"
               "type_of_val (type_interp ctxt) aux_val = \<tau>"
   shows "state_rel Pr StateCons TyRep Tr (AuxPred(aux_var \<mapsto> P)) ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"  
proof -
  note StateRel0 = state_rel_state_rel0[OF StateRel]

  show ?thesis
    unfolding state_rel_def state_rel0_def
  proof (intro conjI)
    show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) (get_store_total \<omega>) (update_var (var_context ctxt) ns aux_var aux_val)"
      using store_rel_stable[OF state_rel0_store_rel[OF StateRel0]] AuxVarFresh
      by fastforce
  next
    from state_rel0_disjoint[OF StateRel0] thm disjoint_list_add
    have *:"disjoint_list 
       ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr), range (const_repr Tr)]@
       (dom AuxPred # [vars_label_hm_tr (label_hm_translation Tr)]))"
      by simp

    show "disjoint_list (state_rel0_disj_list Tr (AuxPred(aux_var \<mapsto> P)))"
      using AuxVarFresh disjoint_list_add[OF *]
      by auto
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>) (update_var (var_context ctxt) ns aux_var aux_val)"
      using heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel0]] AuxVarFresh
      by simp
  next
    show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>) (update_var (var_context ctxt) ns aux_var aux_val)"
      using mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel0]] AuxVarFresh
      by auto
  next
    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def) (update_var (var_context ctxt) ns aux_var aux_val)"
      using heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel0]] AuxVarFresh
      by simp
  next
    show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def) (update_var (var_context ctxt) ns aux_var aux_val)"
      using mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel0]] AuxVarFresh
      by auto
  next
    show "field_rel Pr (var_context ctxt) (field_translation Tr) (update_var (var_context ctxt) ns aux_var aux_val)"
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
  next
    show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) 
                          (get_trace_total \<omega>) (update_var (var_context ctxt) ns aux_var aux_val)"
      using label_hm_rel_stable[OF state_rel0_label_hm_rel[OF StateRel0]] AuxVarFresh
      by fastforce      
  qed (insert StateRel0, unfold state_rel0_def, auto)
qed

lemma state_rel_independent_var:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and AuxVarFresh: "aux_var \<notin> state_rel0_disj_vars Tr AuxPred"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and LookupTy: "lookup_var_ty (var_context ctxt) aux_var = Some \<tau>"
      and AuxValTy: "type_of_val (type_interp ctxt) aux_val = \<tau>"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"
proof -
  have StateRelUpd: "state_rel Pr StateCons TyRep Tr (AuxPred(aux_var \<mapsto> pred_eq aux_val)) ctxt \<omega>def \<omega> (update_var (var_context ctxt) ns aux_var aux_val)"   
    by (rule state_rel_new_auxvar[OF StateRel AuxVarFresh pred_eq_refl TypeInterp LookupTy AuxValTy])

  from AuxVarFresh have "aux_var \<notin> dom AuxPred"
    by simp
  show ?thesis
    apply (rule state_rel_aux_pred_remove[OF StateRelUpd])
    using \<open>aux_var \<notin> dom AuxPred\<close>
    by (metis fun_upd_None_if_notin_dom map_le_imp_upd_le upd_None_map_le)
qed 

lemma state_rel_new_aux_var_no_state_upd:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     AuxVarFresh: "dom AuxPred' \<inter> 
                      ({heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      vars_label_hm_tr (label_hm_translation Tr)) = {}"  and   
           "aux_vars_pred_sat (var_context ctxt) AuxPred' ns"
         shows "state_rel Pr StateCons TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
  have "disjoint_list
     ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr)] @ ((dom AuxPred') # [vars_label_hm_tr (label_hm_translation Tr)]))"
    apply (rule disjoint_list_replace_set)
    using state_rel_disjoint[OF StateRel]
     apply simp
    apply (simp add: disjnt_def)
    using AuxVarFresh
    by auto

  thus "disjoint_list (state_rel0_disj_list Tr AuxPred')"
    by simp
qed (insert assms state_rel_state_rel0[OF StateRel], unfold state_rel0_def, auto)


subsubsection \<open>Heap update\<close>

lemma state_rel0_heap_update:
  assumes StateRel: "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns"
      and TyInterp: "ns \<noteq> ns' \<Longrightarrow> TyInterp = vbpl_absval_ty TyRep"
      and "Tr' = Tr\<lparr> heap_var := hvar', heap_var_def := hvar_def' \<rparr>"
      and Disj: "{hvar', hvar_def'} \<inter>
                      ({mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
      and UpdStates: "\<omega>def' = update_h_total_full \<omega>def hh' hp'" 
                     "\<omega>' = update_h_total_full \<omega> hh' hp'"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>def' \<and> StateCons \<omega>'"
      and OnlyHeapAffected: "(\<And>x. x \<notin> {hvar', hvar_def'} \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)"
      and HeapRel: "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) hvar' (get_hh_total_full \<omega>') ns'"
      and HeapRelDef: "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) hvar_def' (get_hh_total_full \<omega>def') ns'"
      and ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x"
      and OldStateEq: "old_global_state ns' = old_global_state ns"
      and BinderEmpty: "binder_state ns' = Map.empty"
    shows "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr' AuxPred \<omega>def' \<omega>' ns'"
  unfolding state_rel0_def
  proof (intro conjI)
    show "wf_mask_simple (get_mh_total_full \<omega>def')"
      using state_rel0_wf_mask_def_simple[OF StateRel] \<open>\<omega>def' = _\<close>
      by simp     
  next
    show "wf_mask_simple (get_mh_total_full \<omega>')"
      using state_rel0_wf_mask_simple[OF StateRel] \<open>\<omega>' = _\<close>
      by simp
  next
    show "store_rel TyInterp \<Lambda> (var_translation Tr') (get_store_total \<omega>') ns'"
    proof (simp add: \<open>Tr' = _\<close>, rule store_rel_stable[OF state_rel0_store_rel[OF StateRel]])
      show "get_store_total \<omega> = get_store_total \<omega>'"  
        using \<open>\<omega>' = _\<close>
        by simp
    next
      fix x
      assume "x \<in> ran (var_translation Tr)"
      thus  "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"        
        using OnlyHeapAffected Disj
        by blast      
    qed
  next  
    have "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>') ns'"      
      apply (rule mask_var_rel_stable[OF state_rel0_mask_var_rel[OF StateRel]])
      using \<open>\<omega>' = _\<close>
       apply simp
      using OnlyHeapAffected Disj
      by force      
    thus "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr') (mask_var Tr') (get_mh_total_full \<omega>') ns'"
      by (simp add: \<open>Tr' = _\<close>)
  next
    have "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def') ns'"
          apply (rule mask_var_rel_stable[OF state_rel0_mask_var_def_rel[OF StateRel]])
      using \<open>\<omega>def' = _\<close>
       apply simp
      using mask_var_disjoint[OF StateRel] OnlyHeapAffected Disj
      by force
    thus "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr') (mask_var_def Tr') (get_mh_total_full \<omega>def') ns'"
      by (simp add: \<open>Tr' = _\<close>)
  next
    show "field_rel Pr \<Lambda> (field_translation Tr') ns'"
      apply (simp add: \<open>Tr' = _\<close>, rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
      using OnlyHeapAffected Disj
      by blast
  next
    have "boogie_const_rel (const_repr Tr) \<Lambda> ns'"     
      apply (rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
      using Disj OnlyHeapAffected
      by blast
    thus "boogie_const_rel (const_repr Tr') \<Lambda> ns'"
      by (simp add: \<open>Tr' = _\<close>)
  next
    have LookupAux:
           "ns \<noteq> ns' \<Longrightarrow> (\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> \<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> 
                                                       type_of_val TyInterp v1 = instantiate [] t)"
    proof -
      assume "ns \<noteq> ns'"
      fix x t 
      assume LookupTy: "lookup_var_ty \<Lambda> x = Some t"
      show "\<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> type_of_val TyInterp v1 = instantiate [] t"
      proof (cases "x \<in> {hvar', hvar_def'}")
        case True   
        
        hence "t = TConSingle (THeapId TyRep)" 
          apply (cases "x = hvar'")
          using HeapRel HeapRelDef LookupTy
          unfolding heap_var_rel_def 
          by fastforce+
          
        obtain hb where LookupX: "lookup_var \<Lambda> ns' x = Some (AbsV (AHeap hb))" and
                         "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
          using HeapRel HeapRelDef heap_var_rel_def \<open>x \<in> _\<close>
          by blast  
        thus ?thesis
          using \<open>t = _\<close> TyInterp[OF \<open>ns \<noteq> ns'\<close>]
          by auto        
      next
        case False
        hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" 
          using OnlyHeapAffected by simp    
        then show ?thesis using state_rel0_state_well_typed[OF StateRel] LookupTy TyInterp[OF \<open>ns \<noteq> ns'\<close>]
          by (metis state_well_typed_lookup)
      qed
    qed
  
    show "state_well_typed TyInterp \<Lambda> [] ns'"
    proof (cases "ns = ns'")
      case True
      then show ?thesis 
        using state_rel0_state_well_typed[OF StateRel]
        by simp
    next
      case False
      show ?thesis
      apply (rule state_well_typed_upd_1[OF state_rel0_state_well_typed[OF StateRel]])
      apply (rule LookupAux[OF \<open>ns \<noteq> ns'\<close>])
      using ShadowedGlobalsEq OldStateEq BinderEmpty
      by auto
  qed
next 
    show "aux_vars_pred_sat \<Lambda> AuxPred ns'"
    using state_rel0_aux_vars_pred_sat[OF StateRel] OnlyHeapAffected Disj
    unfolding aux_vars_pred_sat_def
    by (smt (verit, ccfv_threshold) Int_Un_distrib Int_commute Int_insert_left_if0 Int_insert_right_if1 Un_commute Un_empty_left Un_insert_right Un_left_commute domI dom_restrict inf_sup_aci(8) insert_absorb insert_commute insert_not_empty)
    (*old proof before changes: by (metis Un_iff domIff option.distinct(1))*)
next
  have DisjAux: "disjoint_list
       ([] @
         ( ({heap_var Tr, heap_var_def Tr} \<union> {hvar', hvar_def'}) #
         [ {mask_var Tr, mask_var_def Tr}, 
          ran (var_translation Tr), 
          ran (field_translation Tr),
          range (const_repr Tr),
          dom AuxPred,
          vars_label_hm_tr (label_hm_translation Tr)]))"
    apply (rule disjoint_list_add_set)
    using state_rel0_disjoint[OF StateRel]
      apply simp
    using Disj
    by fastforce+

  thus "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
    apply (rule disjoint_list_subset_list_all2)
    by (simp add: \<open>Tr' = _\<close>)
next
  show "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>') ns'"
    using HeapRel \<open>Tr' = _\<close> 
    unfolding heap_var_rel_def
    by auto    
next
  show "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full \<omega>def') ns'"
    using HeapRelDef \<open>Tr' = _\<close> 
    unfolding heap_var_rel_def
    by auto
next
  show "label_hm_rel Pr \<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total \<omega>') ns'"
    apply (simp add: \<open>Tr' = _\<close>)
    apply (rule label_hm_rel_stable[OF state_rel0_label_hm_rel[OF StateRel]])
     apply (simp add: UpdStates)
    using OnlyHeapAffected Disj
    by blast
qed (insert assms, unfold state_rel0_def, simp_all add: \<open>Tr' = _\<close>)

lemmas state_rel_heap_update = 
  state_rel0_state_rel[OF state_rel0_heap_update[OF state_rel_state_rel0]]

lemma state_rel0_heap_update_2:
  assumes                                
    StateRel: "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
    TyInterp:     "TyInterp = vbpl_absval_ty TyRep" and
    WellDefSame: "\<omega>def = \<omega> \<and> \<omega>def' = \<omega>' \<and> heap_var Tr = heap_var_def Tr" and
    Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>'" and
    OnlyHeapAffected: "(\<And>x. x \<noteq> heap_var Tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x)" and
    OnlyHeapAffectedVpr: "get_store_total \<omega> = get_store_total \<omega>'" 
                         "get_m_total_full \<omega> = get_m_total_full \<omega>'"
                         "get_trace_total \<omega> = get_trace_total \<omega>'" and
    HeapRel: "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>') ns'" and
    ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
    OldStateEq: "old_global_state ns' = old_global_state ns" and
    BinderEmpty: "binder_state ns' = Map.empty"
        shows "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'"  
proof (rule state_rel0_heap_update[OF StateRel TyInterp])
  show "Tr = Tr\<lparr>heap_var := heap_var Tr, heap_var_def := heap_var_def Tr\<rparr>"
    by auto
next
  show "{heap_var Tr, heap_var_def Tr} \<inter>
    ({mask_var Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union> range (const_repr Tr) \<union>
     dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
    using heap_var_disjoint[OF StateRel]
    by simp
next
  show "\<omega>def' = update_h_total_full \<omega>def (get_hh_total_full \<omega>def') (get_hp_total_full \<omega>def')"
    apply (rule full_total_state.equality)
       apply (simp add: OnlyHeapAffectedVpr WellDefSame)
    apply (simp add: OnlyHeapAffectedVpr WellDefSame)
     apply (simp add: WellDefSame)
    using OnlyHeapAffectedVpr
    by auto
next
  show "\<omega>' = update_h_total_full \<omega> (get_hh_total_full \<omega>def') (get_hp_total_full \<omega>def')"
    apply (rule full_total_state.equality)
       apply (simp add: OnlyHeapAffectedVpr WellDefSame)
      apply (simp add: OnlyHeapAffectedVpr WellDefSame)
    using OnlyHeapAffectedVpr WellDefSame
    by auto
qed (insert assms, auto)

lemmas state_rel_heap_update_2 =
  state_rel0_state_rel[OF state_rel0_heap_update_2[OF state_rel_state_rel0]]

lemma heap_var_rel_update:
  assumes 
     WfTyRep: "wf_ty_repr_bpl TyRep" and
     HeapVarRel: "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) hv ns" and
     LookupHeapVar: "lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
               "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     VVprTy:   "get_type (domain_type TyRep) v_vpr = ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     FieldTranslationInj: "inj_on (field_translation Tr) (dom (field_translation Tr))"
  shows "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var Tr) (hv((addr,f_vpr) := v_vpr))
     (update_var \<Lambda> ns (heap_var Tr) (AbsV (AHeap (heap_bpl_upd_normal_field hb (Address addr) f_bpl ty_vpr (val_rel_vpr_bpl v_vpr)))))"
      (is "heap_var_rel Pr \<Lambda> TyRep _ (heap_var Tr) ?hv' ?ns'")
proof -
  from HeapVarRel and LookupHeapVar have
   HeapRelFacts:
   "lookup_var_ty \<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))" 
   "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
   "heap_rel Pr (field_translation Tr) hv hb"
   "total_heap_well_typed Pr (domain_type TyRep) hv"
    unfolding heap_var_rel_def
    by auto
  let ?hb' = "hb( (Address addr, NormalField f_bpl ty_vpr) \<mapsto> val_rel_vpr_bpl v_vpr)"

  have VBplTy: "type_of_val (vbpl_absval_ty TyRep) (val_rel_vpr_bpl v_vpr) = ty_bpl"
    using VVprTy vpr_to_bpl_val_type \<open>vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl\<close>
    by blast

  show ?thesis
  unfolding heap_var_rel_def
  proof (intro conjI, rule exI, intro conjI)
    show "lookup_var \<Lambda> ?ns' (heap_var Tr) = Some (AbsV (AHeap ?hb'))"
      by (simp add: heap_bpl_upd_normal_field_def)
  next
    show "lookup_var_ty \<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))"
      using HeapVarRel
      unfolding heap_var_rel_def
      by auto
  next
    show "vbpl_absval_ty_opt TyRep (AHeap ?hb') = Some (THeapId TyRep, [])"
      apply (rule heap_upd_ty_preserved[OF HeapRelFacts(2)])
       apply (fastforce intro: \<open>vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl\<close>)
      by (rule VBplTy)      
  next
    have HeapRel:"heap_rel Pr (field_translation Tr) hv hb"
       using HeapVarRel LookupHeapVar
       unfolding heap_var_rel_def
       by auto
    have AuxUpdateHeap:"\<And>l. l \<noteq> (addr, f_vpr) \<Longrightarrow> ?hv' l = 
                                                   hv l"
      by simp     
  
    show "ViperBoogieBasicRel.heap_rel Pr (field_translation Tr) ?hv' ?hb'"    
    proof (rule heap_rel_intro)
      fix l :: heap_loc
      fix  field_ty_vpr field_bpl
      assume FieldLookupL: "declared_fields Pr (snd l) = Some field_ty_vpr" and
             FieldTranslationL: "field_translation Tr (snd l) = Some field_bpl"
      show "?hb' (Address (fst l),  NormalField field_bpl field_ty_vpr) = 
               Some (val_rel_vpr_bpl (?hv' l))"
      proof (cases "l = (addr, f_vpr)")
        case True
        then show ?thesis 
          using FieldLookup FieldTranslation FieldLookupL FieldTranslationL 
          by simp
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
  next
    show "total_heap_well_typed Pr (domain_type TyRep) ?hv'"
      unfolding total_heap_well_typed_def
    proof (rule allI | rule impI)+
      fix loc :: heap_loc
      fix  \<tau>
      assume *: "declared_fields Pr (snd loc) = Some \<tau>"
      show "has_type (domain_type TyRep) \<tau> (?hv' loc) "
      proof (cases "loc = (addr, f_vpr)")
        case True
        then show ?thesis 
          using * has_type_get_type VVprTy FieldLookup
          by auto
      next
        case False
        then show ?thesis 
          using HeapRelFacts *
          unfolding total_heap_well_typed_def          
          by fastforce
      qed
    qed
  qed
qed

lemma state_rel_heap_update_3:
  assumes  
     WfTyRep: "wf_ty_repr_bpl TyRep" and
     StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     WellDefSame: "\<omega>def = \<omega> \<and> heap_var Tr = heap_var_def Tr" and
     Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_hh_loc_total_full \<omega>def (addr, f_vpr) v_vpr) \<and> StateCons (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr)" and
     LookupHeap:  "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     VVprTy: "get_type (domain_type TyRep) v_vpr = ty_vpr" 
   shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt 
      (update_hh_loc_total_full \<omega>def (addr, f_vpr) v_vpr)
      (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr)
      (update_var (var_context ctxt) ns (heap_var Tr) (AbsV (AHeap (heap_bpl_upd_normal_field hb (Address addr) f_bpl ty_vpr (val_rel_vpr_bpl v_vpr)))))"
         (is "state_rel Pr StateCons TyRep Tr AuxPred ctxt ?\<omega>def' ?\<omega>' ?ns'")
proof (rule state_rel_heap_update_2[OF StateRel])
  show "\<And>x. x \<noteq> heap_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ?ns' x"
    by simp
next
  show "get_store_total \<omega> = get_store_total ?\<omega>'"
    by simp
next
  show "get_m_total_full \<omega> = get_m_total_full ?\<omega>'"
    by simp
next
  show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full ?\<omega>') ?ns'"
    apply simp
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
     StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
     WellDefSame: "\<omega>def = \<omega> \<and> heap_var Tr = heap_var_def Tr" and
     Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_hh_loc_total_full \<omega>def (addr, f_vpr) v)"
                 "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_hh_loc_total_full \<omega> (addr, f_vpr) v)" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
     VVprTy: "get_type (domain_type TyRep) v = ty_vpr" 
   shows "\<exists>hb f_bpl_val.
    lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
    lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
    field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), ty_bpl]) \<and>
    state_rel Pr StateCons TyRep Tr AuxPred ctxt
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
  from state_rel_heap_update_3[OF WfTyRep StateRel]
  have "state_rel Pr StateCons TyRep Tr AuxPred ctxt 
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

lemma state_rel_heap_var_update:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and HeapVarRel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar' (get_hh_total_full \<omega>) ns"
      and VarFresh: "hvar' \<notin> ({mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union>
                      vars_label_hm_tr (label_hm_translation Tr))"
    shows "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
proof (rule state_rel_heap_update[OF StateRel, where ?hvar' = hvar'])
  show "\<omega> = update_h_total_full \<omega> (get_hh_total_full \<omega>) (get_hp_total_full \<omega>)"
    by simp
next
  from VarFresh heap_var_disjoint[OF state_rel_state_rel0[OF StateRel]]
  show "{hvar', heap_var_def Tr} \<inter>
    ({mask_var Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
     range (const_repr Tr) \<union>
     dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
    by blast
qed (insert HeapVarRel, insert state_rel_binder_empty[OF StateRel], insert state_rel_state_rel0[OF StateRel, simplified state_rel0_def], auto)    

lemma state_rel_heap_var_def_update:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and HeapVarRel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar_def' (get_hh_total_full \<omega>def) ns"
      and VarFresh: "hvar_def' \<notin> ({mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union>
                      vars_label_hm_tr (label_hm_translation Tr))"
    shows "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
proof (rule state_rel_heap_update[OF StateRel, where ?hvar_def' = hvar_def'])
  show "\<omega>def = update_h_total_full \<omega>def (get_hh_total_full \<omega>def) (get_hp_total_full \<omega>def)"
    by simp
next
  from VarFresh heap_var_disjoint[OF state_rel_state_rel0[OF StateRel]]
  show "{heap_var Tr, hvar_def'} \<inter>
    ({mask_var Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
     range (const_repr Tr) \<union>
     dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
    by blast
qed (insert HeapVarRel, insert state_rel_binder_empty[OF StateRel], insert state_rel_state_rel0[OF StateRel, simplified state_rel0_def], simp_all)    

subsubsection \<open>Mask update\<close>

lemma state_rel0_mask_update:
  assumes StateRel: "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          TyInterp: "ns \<noteq> ns' \<Longrightarrow> TyInterp = vbpl_absval_ty TyRep" and
                    "Tr' = Tr\<lparr>mask_var := mvar', mask_var_def := mvar_def'\<rparr>" and
          Disj: "{mvar', mvar_def'} \<inter>
                            ({heap_var Tr, heap_var_def Tr} \<union>
                            (ran (var_translation Tr)) \<union>
                            (ran (field_translation Tr)) \<union>
                            (range (const_repr Tr)) \<union>
                            dom AuxPred \<union>
                            vars_label_hm_tr (label_hm_translation Tr)) = {}" and
          UpdStates: "\<omega>' = update_m_total_full \<omega> mh' mp'" 
             "get_store_total \<omega>def' = get_store_total \<omega>' \<and>
              get_trace_total \<omega>def' = get_trace_total \<omega>' \<and>
              get_h_total_full \<omega>def' = get_h_total_full \<omega>'" and   

          OnlyMaskAffected: "\<And>x. x \<notin> {mvar', mvar_def'} \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          WfMaskSimple: "wf_mask_simple mh'" 
                        "wf_mask_simple (get_mh_total_full \<omega>def')" and
          Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>' \<and> StateCons \<omega>def'" and 
          MaskVarRel: "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) mvar' (get_mh_total_full \<omega>') ns'" 
                      "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) mvar_def' (get_mh_total_full \<omega>def') ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
        shows "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr' AuxPred \<omega>def' \<omega>' ns'"
  unfolding state_rel0_def
proof (intro conjI)
  show "store_rel TyInterp \<Lambda> (var_translation Tr') (get_store_total \<omega>') ns'"
  proof (simp add: \<open>Tr' = _\<close>, rule store_rel_stable[OF state_rel0_store_rel[OF StateRel]])
    show "get_store_total \<omega> = get_store_total \<omega>'"  
      using \<open>\<omega>' = _\<close>
      by simp
  next
    fix x
    assume "x \<in> ran (var_translation Tr)"
    thus  "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x"        
      using OnlyMaskAffected Disj
      by blast      
  qed
next
  show "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>') ns'"
    using Disj OnlyMaskAffected heap_var_rel_stable[OF state_rel0_heap_var_rel[OF StateRel]]
    by (fastforce simp: \<open>Tr' = _\<close> \<open>\<omega>' = _\<close>)
next
  have HeapVarRelDef: "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def') ns'"
    apply (rule heap_var_rel_stable[OF state_rel0_heap_var_def_rel[OF StateRel]])
    using UpdStates StateRel
    unfolding state_rel0_def
      apply simp
    using Disj OnlyMaskAffected
    by blast
  thus "heap_var_rel Pr \<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full \<omega>def') ns'"
    by (simp add: \<open>Tr' = _\<close>)
next
  show "field_rel Pr \<Lambda> (field_translation Tr') ns'"
    apply (simp add: \<open>Tr' = _\<close>, rule field_rel_stable[OF state_rel0_field_rel[OF StateRel]])
    using OnlyMaskAffected Disj
    by blast
next
  have "boogie_const_rel (const_repr Tr) \<Lambda> ns'"     
    apply (rule boogie_const_rel_stable[OF state_rel0_boogie_const_rel[OF StateRel]])
    using Disj OnlyMaskAffected
    by blast
  thus "boogie_const_rel (const_repr Tr') \<Lambda> ns'"
    by (simp add: \<open>Tr' = _\<close>)
next
  have LookupAux:
         "ns \<noteq> ns' \<Longrightarrow> (\<And>x t. lookup_var_ty \<Lambda> x = Some t \<Longrightarrow> \<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> 
                                                     type_of_val TyInterp v1 = instantiate [] t)"
  proof -
    assume "ns \<noteq> ns'"
    fix x t 
    assume LookupTy: "lookup_var_ty \<Lambda> x = Some t"
    show "\<exists>v1. lookup_var \<Lambda> ns' x = Some v1 \<and> type_of_val TyInterp v1 = instantiate [] t"
    proof (cases "x \<in> {mvar', mvar_def'}")
      case True            
      thus ?thesis
        using TyInterp[OF \<open>ns \<noteq> ns'\<close>] MaskVarRel LookupTy True
        unfolding mask_var_rel_def
        by fastforce          
    next
      case False
      hence "lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" 
        using OnlyMaskAffected by simp    
      then show ?thesis using state_rel0_state_well_typed[OF StateRel] LookupTy TyInterp[OF \<open>ns \<noteq> ns'\<close>]
        by (metis state_well_typed_lookup)
    qed
  qed

  show "state_well_typed TyInterp \<Lambda> [] ns'"
  proof (cases "ns = ns'")
    case True
    then show ?thesis 
      using state_rel0_state_well_typed[OF StateRel]
      by simp
  next
    case False
    show ?thesis
    apply (rule state_well_typed_upd_1[OF state_rel0_state_well_typed[OF StateRel]])
         apply (rule LookupAux[OF \<open>ns \<noteq> ns'\<close>])
    using ShadowedGlobalsEq OldStateEq BinderEmpty
    by auto
  qed
next
  show "aux_vars_pred_sat \<Lambda> AuxPred ns'"
  using state_rel0_aux_vars_pred_sat[OF StateRel] OnlyMaskAffected Disj
  unfolding aux_vars_pred_sat_def
  by (smt (verit, ccfv_threshold) Int_Un_distrib Int_commute Int_insert_left_if0 Int_insert_right_if1 Un_commute Un_empty_left Un_insert_right Un_left_commute domI dom_restrict inf_sup_aci(8) insert_absorb insert_commute insert_not_empty)
next
  have DisjAux: "disjoint_list
       (
         [{heap_var Tr, heap_var_def Tr}]@
          (
            ({mask_var Tr, mask_var_def Tr} \<union> {mvar', mvar_def'})# 
              [ran (var_translation Tr), 
              ran (field_translation Tr),
              range (const_repr Tr),
              dom AuxPred,
              vars_label_hm_tr (label_hm_translation Tr)]
          )
       )"
    apply (rule disjoint_list_add_set)
    using state_rel0_disjoint[OF StateRel]
      apply simp
    using Disj
    by fastforce

  thus "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
    apply (rule disjoint_list_subset_list_all2)
    by (simp add: \<open>Tr' = _\<close>)
next
  show "label_hm_rel Pr \<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total \<omega>') ns'"
    apply (simp add: \<open>Tr' = _\<close>)
    apply (rule label_hm_rel_stable[OF state_rel0_label_hm_rel[OF StateRel]])
     apply (simp add: UpdStates)
    using OnlyMaskAffected Disj
    by blast    
qed (insert assms, unfold mask_var_rel_def, unfold state_rel0_def, auto simp: \<open>Tr' = _\<close>)

lemmas state_rel_mask_update_wip =
  state_rel0_state_rel[OF state_rel0_mask_update[OF state_rel_state_rel0]]

lemma state_rel0_mask_update_2:
  assumes StateRel: "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def \<omega> ns" and
          TyInterp: "TyInterp = vbpl_absval_ty TyRep" and
                  \<comment>\<open>The following assumption only allows updating both the well-definedness and 
                     evaluation mask (in case the tracked Boogie variables are the same) or 
                     just the evaluation mask. If want to also allow updating just the well-definedness mask
                     consider \<open>TODO\<close>.
                     \<close>                    
          WellDefSame: "mask_var Tr = mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>'"
                       "mask_var Tr \<noteq> mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>def"  and
          OnlyMaskAffected: "\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda> ns' x" and
          OnlyMaskAffectedVpr: "get_store_total \<omega> = get_store_total \<omega>'" 
                               "get_trace_total \<omega> = get_trace_total \<omega>'"
                               "get_h_total_full \<omega> = get_h_total_full \<omega>'" and
          WfMaskSimple: "wf_mask_simple (get_mh_total_full \<omega>')" and
          Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>'" and
          MaskVarRel: "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>') ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd \<Lambda>) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty"
        shows "state_rel0 Pr StateCons TyInterp \<Lambda> TyRep Tr AuxPred \<omega>def' \<omega>' ns'" 

proof -
  have "\<omega>' = update_m_total_full \<omega> (get_mh_total_full \<omega>') (get_mp_total_full \<omega>')"
    using OnlyMaskAffectedVpr
    by simp        

  show ?thesis
  proof (cases "mask_var Tr = mask_var_def Tr")
    case True
    hence "\<omega>def' = update_m_total_full \<omega> (get_mh_total_full \<omega>') (get_mp_total_full \<omega>')"
      using WellDefSame \<open>\<omega>' = _\<close>
      by presburger

    have MaskVarRelDef: "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def') ns'"
      using MaskVarRel \<open>\<omega>def' = _\<close> True
      unfolding mask_var_rel_def 
      by simp
            
    show ?thesis 
      apply (rule state_rel0_mask_update[OF StateRel TyInterp, where ?mvar' = "mask_var Tr" and ?mvar_def' = "mask_var_def Tr"])
              apply simp
              apply (simp add:  mask_var_disjoint[OF StateRel])
               apply (rule \<open>\<omega>' = _\<close>)
      using \<open>\<omega>' = _\<close> \<open>\<omega>def' = _\<close>
              apply simp
      using OnlyMaskAffected
             apply simp
      using WfMaskSimple 
            apply simp
      using WfMaskSimple  \<open>\<omega>def' = _\<close>
             apply simp
      using Consistent state_rel0_consistent[OF StateRel] WellDefSame
           apply blast      
          apply (rule MaskVarRel)
         apply (rule MaskVarRelDef)
        apply (meson ShadowedGlobalsEq)
      using assms
      by auto      
  next
    case False
    hence "\<omega>def' = \<omega>def"
      using WellDefSame
      by simp

    hence *: "get_store_total \<omega>def' = get_store_total \<omega>' \<and> get_trace_total \<omega>def' = get_trace_total \<omega>' \<and> get_h_total_full \<omega>def' = get_h_total_full \<omega>'"
      using StateRel \<open>\<omega>' = _\<close> OnlyMaskAffectedVpr 
      unfolding state_rel0_def
      by presburger 
     
    have MaskVarRelDef: "mask_var_rel Pr \<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def') ns'"
      using state_rel0_mask_var_def_rel[OF StateRel]
      by (metis False OnlyMaskAffected \<open>\<omega>def' = \<omega>def\<close> mask_var_rel_stable)
      
    show ?thesis 
      apply (rule state_rel0_mask_update[OF StateRel TyInterp, where ?mvar' = "mask_var Tr" and ?mvar_def' = "mask_var_def Tr"])
              apply simp
              apply (simp add:  mask_var_disjoint[OF StateRel])
               apply (rule \<open>\<omega>' = _\<close>)
              apply (rule *)
      using OnlyMaskAffected
             apply simp
            apply (rule WfMaskSimple)
      using \<open>\<omega>def' = _\<close> state_rel0_wf_mask_def_simple[OF StateRel]
             apply blast
      using Consistent state_rel0_consistent[OF StateRel] WellDefSame
           apply blast
          apply (rule MaskVarRel)
         apply (rule MaskVarRelDef)
      using assms
      by auto
  qed
qed

lemmas state_rel_mask_update_2 = state_rel0_state_rel[OF state_rel0_mask_update_2[OF state_rel_state_rel0]]

lemma state_rel_mask_update_2b:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          WellDefSame: "mask_var Tr = mask_var_def Tr \<and> \<omega>def = \<omega>" and
          OnlyMaskAffected: "\<And>x. x \<noteq> mask_var Tr \<Longrightarrow> lookup_var (var_context ctxt) ns x = lookup_var (var_context ctxt) ns' x" and
          MaskRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>) ns'" and
          ShadowedGlobalsEq: "\<And>x. map_of (snd (var_context ctxt)) x \<noteq> None \<Longrightarrow> global_state ns' x = global_state ns x" and
          OldStateEq: "old_global_state ns' = old_global_state ns" and
          BinderEmpty: "binder_state ns' = Map.empty" and
          TypeInterp: "type_interp ctxt = (vbpl_absval_ty TyRep)"
        shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns'"
  unfolding state_rel_def
  using assms state_rel0_wf_mask_simple[OF state_rel_state_rel0[OF StateRel]] state_rel0_consistent[OF state_rel_state_rel0[OF StateRel]]
  unfolding state_rel_def
  by (auto intro: state_rel0_mask_update_2)

lemma state_rel_mask_update_3:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and 
          WellDefSame: "mask_var Tr = mask_var_def Tr \<and> \<omega>def = \<omega>" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) m'" and
          Eq: "mvar = mask_var Tr"
           "\<Lambda> = (var_context ctxt)" and
        TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
        shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> (update_var \<Lambda> ns mvar (AbsV (AMask m')))" 
                (is "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ?ns'")
  apply (rule state_rel_mask_update_2b[OF StateRel WellDefSame])
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

lemma state_rel_mask_update_4:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and 
                    "\<Lambda> = (var_context ctxt)" and
          WellDefSame: "mask_var Tr = mask_var_def Tr \<Longrightarrow> \<omega>def' = update_mh_loc_total_full \<omega> (addr, f_vpr) p"
                       "mask_var Tr \<noteq> mask_var_def Tr \<Longrightarrow> \<omega>def' = \<omega>def"  and
        Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_mh_loc_total_full \<omega> (addr, f_vpr) p)" and
        TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
        LookupMask: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
                    "pgte pwrite p" and
     FieldLookup: "declared_fields Pr f_vpr = Some ty_vpr" and
     FieldTranslation: "field_translation Tr f_vpr = Some f_bpl" and
     TyTranslation: "vpr_to_bpl_ty TyRep ty_vpr = Some ty_bpl" and
                    "p_bpl = Rep_preal p"
                  shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt 
                      \<omega>def'
                      (update_mh_loc_total_full \<omega> (addr, f_vpr) p) 
                      (update_var \<Lambda> ns (mask_var Tr) (AbsV (AMask (mask_bpl_upd_normal_field mb (Address addr) f_bpl ty_vpr p_bpl))))"
            (is "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def' ?\<omega>' ?ns'")
  unfolding state_rel_def TypeInterp
proof (rule state_rel0_mask_update_2)
  show "state_rel0 Pr StateCons (vbpl_absval_ty TyRep) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns"
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
    by simp
next
  have WfMask: "wf_mask_simple (get_mh_total_full \<omega>)"
    using state_rel_state_rel0[OF StateRel]  state_rel0_wf_mask_simple
    by fast

  show "wf_mask_simple (get_mh_total_full ?\<omega>')" 
    unfolding wf_mask_simple_def
  proof (rule allI)
    fix hl
    show "pwrite \<ge> get_mh_total_full ?\<omega>' hl"
    proof (cases "hl = (addr, f_vpr)")
      case True
      hence "get_mh_total_full ?\<omega>' hl = p"
        by simp
      then show ?thesis 
        using \<open>pgte pwrite p\<close>
        by (metis PosReal.pgte.rep_eq less_eq_preal.rep_eq)
    next
      case False       
      hence "get_mh_total_full ?\<omega>' hl = get_mh_total_full \<omega> hl"
        by simp
      thus ?thesis 
        using WfMask
        unfolding wf_mask_simple_def
        by presburger        
    qed
  qed
next
  let ?mb'="mask_bpl_upd_normal_field mb (Address addr) f_bpl ty_vpr (Rep_preal p)"

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
   
  proof (intro conjI, (rule allI | rule impI)+)
    fix l::heap_loc
    fix field_ty_vpr field_bpl
    assume FieldLookup2: "declared_fields Pr (snd l) = Some field_ty_vpr"
    assume FieldTranslation2: "field_translation Tr (snd l) = Some field_bpl"
    show "?mb' (Address (fst l), NormalField field_bpl field_ty_vpr) = Rep_preal (get_mh_total_full ?\<omega>' l)"
    proof (cases "l = (addr, f_vpr)")
      case True
      then show ?thesis 
        using FieldLookup FieldLookup2 FieldTranslation FieldTranslation2
        unfolding mask_bpl_upd_normal_field_def
        by simp
    next
      case False
      hence "get_mh_total_full ?\<omega>' l = get_mh_total_full \<omega> l"
        by simp
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
  next
    show "\<forall>r f. 0 \<le> ?mb' (r, f) \<and>
          (is_bounded_field_bpl f \<longrightarrow> ?mb' (r, f) \<le> 1)" (is "\<forall>r f. ?MaskBplGoal r f")
    proof (rule allI)+
      fix r f
      show "?MaskBplGoal r f"
      proof (cases "(r,f) = (Address addr, NormalField f_bpl ty_vpr)")
        case True
        then show ?thesis 
          using \<open>pgte pwrite p\<close> one_prat.rep_eq pgte.rep_eq prat_non_negative one_preal.rep_eq
          unfolding mask_bpl_upd_normal_field_def
          by auto
      next
        case False
        then show ?thesis 
          unfolding mask_bpl_upd_normal_field_def
          using MaskRel0
          unfolding mask_rel_def
          by auto
      qed
    qed
  qed

  thus "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full ?\<omega>') ?ns'"
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
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  shows "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>) AuxPred ctxt \<omega> \<omega> ns"
  unfolding state_rel_def state_rel0_def
proof (intro conjI)
  show "disjoint_list (state_rel0_disj_list (Tr\<lparr>mask_var_def := mask_var Tr, heap_var_def := heap_var Tr\<rparr>) AuxPred)"
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

lemma state_rel_mask_var_update:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and MaskVarRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar' (get_mh_total_full \<omega>) ns"
      and VarFresh: "mvar' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union>
                      vars_label_hm_tr (label_hm_translation Tr))" 
    shows "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
proof (rule state_rel_mask_update_wip[OF StateRel, where ?mvar' = mvar'])      
  show "\<omega> = update_m_total_full \<omega> (get_mh_total_full \<omega>) (get_mp_total_full \<omega>)"
    by simp
next  
  from VarFresh mask_var_disjoint[OF state_rel_state_rel0[OF StateRel]]
  show "{mvar', mask_var_def Tr} \<inter> 
          ({heap_var Tr, heap_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
           range (const_repr Tr) \<union> dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
    by auto
next
  show "binder_state ns = Map.empty"
    using state_rel_state_well_typed[OF StateRel, simplified state_well_typed_def]
    by blast   
qed (insert MaskVarRel, insert state_rel_state_rel0[OF StateRel, simplified state_rel0_def], simp_all)    

lemma state_rel_mask_var_def_update:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and MaskVarRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar_def' (get_mh_total_full \<omega>def) ns"
      and VarFresh: "mvar_def' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union> 
                      vars_label_hm_tr (label_hm_translation Tr))" 
    shows "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns"
proof (rule state_rel_mask_update_wip[OF StateRel, where ?mvar_def' = "mvar_def'"])      
  show "\<omega> = update_m_total_full \<omega> (get_mh_total_full \<omega>) (get_mp_total_full \<omega>)"
    by simp
next  
  from VarFresh mask_var_disjoint[OF state_rel_state_rel0[OF StateRel]]
  show "{mask_var Tr, mvar_def'} \<inter> 
          ({heap_var Tr, heap_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union> 
           range (const_repr Tr) \<union> dom AuxPred \<union> vars_label_hm_tr (label_hm_translation Tr)) = {}"
    by auto
next
  show "binder_state ns = Map.empty"
    using state_rel_state_well_typed[OF StateRel, simplified state_well_typed_def]
    by blast   
qed (insert MaskVarRel, insert state_rel_state_rel0[OF StateRel, simplified state_rel0_def], simp_all)    

subsubsection \<open>Labeled state adjustments\<close>

lemma state_rel_label_mask_update:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t" 
      and StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns"
      and "\<omega>' = update_trace_label_total \<omega> lbl (get_total_full \<omega>)"
      and "label_tr = label_hm_translation Tr"     
      and HeapLabelStable: "\<And>h. fst label_tr lbl = Some h \<Longrightarrow> get_trace_total \<omega> lbl = Some (get_total_full \<omega>)"
      and "Tr' = (Tr \<lparr> label_hm_translation := (fst label_tr, (snd label_tr)(lbl \<mapsto> m)) \<rparr>)"  
      and MaskVarRel: "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) m (get_mh_total_full \<omega>) ns" 
      and Disj: "m \<notin> {heap_var Tr, heap_var_def Tr, mask_var Tr, mask_var_def Tr} \<union> ran (var_translation Tr)
                       \<union> ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred"
    shows "state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>' \<omega>' ns"
  unfolding state_rel_def state_rel0_def
  unfolding \<open>Tr' = _\<close> \<open>\<omega>' = _\<close>
proof(simp, intro conjI)
  show "consistent_state_rel_opt (state_rel_opt Tr) \<longrightarrow>
    StateCons (\<omega>\<lparr>get_trace_total := get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)\<rparr>)"
    using WfConsistency state_rel_consistent[OF StateRel]
    unfolding wf_total_consistency_def
    by auto
next
  have SubAux: "vars_label_hm_tr (fst label_tr, (snd label_tr)(lbl \<mapsto> m)) \<subseteq> vars_label_hm_tr label_tr \<union> {m}"   
    unfolding vars_label_hm_tr_def ran_def
    by auto

  have "disjoint_list
         ([{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr),
           ran (field_translation Tr), range (const_repr Tr), dom AuxPred]@
          [vars_label_hm_tr label_tr \<union> {m}])"
    apply (rule disjoint_list_add)
    using state_rel_disjoint[OF StateRel] 
    unfolding \<open>label_tr = _\<close>
     apply simp
    using Disj
    by fastforce
    
  thus "disjoint_list
       [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr),
        ran (field_translation Tr), range (const_repr Tr), dom AuxPred,
        vars_label_hm_tr (fst label_tr, snd label_tr(lbl \<mapsto> m))]"
    apply (rule disjoint_list_subset_list_all2)
    using SubAux
    by simp_all
next
  note StateRelLabel = state_rel_label_hm_rel[OF StateRel, simplified label_hm_rel_def label_rel_def]
  
  show "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (fst label_tr, snd label_tr(lbl \<mapsto> m))
                        (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) ns"
    unfolding label_hm_rel_def
  proof (intro conjI)
    show "label_rel (\<lambda>h \<phi>. heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) h (get_hh_total \<phi>))
     (fst (fst label_tr, snd label_tr(lbl \<mapsto> m))) (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) ns"
      unfolding label_rel_def
    proof (intro allI, intro impI)
      fix lbla h
      assume "fst (fst label_tr, snd label_tr(lbl \<mapsto> m)) lbla = Some h"
      thus "\<exists>\<phi>. (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) lbla = Some \<phi> \<and>
            heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) h (get_hh_total \<phi>) ns"
        using HeapLabelStable StateRelLabel \<open>label_tr = _\<close>
        by fastforce
    qed
    show "label_rel (\<lambda>m \<phi>. mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) m (get_mh_total \<phi>))
     (snd (fst label_tr, snd label_tr(lbl \<mapsto> m))) (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) ns"
      unfolding label_rel_def
    proof (intro allI, intro impI)
      fix lbla h
      assume "snd (fst label_tr, snd label_tr(lbl \<mapsto> m)) lbla = Some h"
      thus "\<exists>\<phi>. (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) lbla = Some \<phi> \<and>
            mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) h (get_mh_total \<phi>) ns"
        using MaskVarRel StateRelLabel \<open>label_tr = _\<close>
        by fastforce
    qed
    show "\<forall>lbla \<phi>. (get_trace_total \<omega>(lbl \<mapsto> get_total_full \<omega>)) lbla = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
      by (metis StateRel StateRelLabel get_mh_total_full.simps map_upd_Some_unfold state_rel_wf_mask_def_simple)
  qed    
qed(insert StateRel[simplified state_rel_def state_rel0_def], auto)              


subsection \<open>Adjust state relation options\<close>

abbreviation disable_consistent_state_rel_opt :: "tr_vpr_bpl \<Rightarrow> tr_vpr_bpl"
  where "disable_consistent_state_rel_opt Tr \<equiv> Tr \<lparr> state_rel_opt := (state_rel_opt Tr) \<lparr> consistent_state_rel_opt := False \<rparr> \<rparr>"

abbreviation enable_consistent_state_rel_opt :: "tr_vpr_bpl \<Rightarrow> tr_vpr_bpl"
  where "enable_consistent_state_rel_opt Tr \<equiv> Tr \<lparr> state_rel_opt := (state_rel_opt Tr) \<lparr> consistent_state_rel_opt := True \<rparr> \<rparr>"

lemma state_rel_disable_consistency:
  assumes  "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"       
  shows "state_rel Pr StateCons TyRep (disable_consistent_state_rel_opt Tr) AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
  by (insert assms[simplified state_rel_def state_rel0_def]) auto

lemma state_rel_enable_consistency:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" 
      and "StateCons \<omega> \<and> StateCons \<omega>def"       
    shows "state_rel Pr StateCons TyRep (enable_consistent_state_rel_opt Tr) AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
  by (insert assms[simplified state_rel_def state_rel0_def]) auto

lemma state_rel_enable_consistency_2:
  assumes "state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ns" 
      and "Tr' = (disable_consistent_state_rel_opt Tr)"
      and "StateCons \<omega> \<and> StateCons \<omega>def"       
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  unfolding state_rel_def state_rel0_def
  by (insert assms[simplified state_rel_def state_rel0_def]) auto
  

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
           fun_interp_rel Pr (field_translation Tr) (fun_translation Tr) ctxt_vpr (fun_interp ctxt)"

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
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], s\<rangle> [\<Down>] v) = (v = [])"
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e0#es, s\<rangle> [\<Down>] v)
    = (\<exists>v0 vs. v = v0#vs \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e0, s\<rangle> \<Down> v0) \<and> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs))"
  by ((rule iffI, (erule red_exprs.cases, assumption, simp), (simp, rule RedExpListNil)),
      (rule iffI, (erule red_exprs.cases, simp, simp), (clarsimp, rule RedExpListCons; simp)))

lemma bg_expr_list_red_all2:
  "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) = list_all2 (\<lambda>e v. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v) es vs"
  by (induct es arbitrary:vs; simp add:bg_expr_list_red_iff list_all2_Cons1)

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