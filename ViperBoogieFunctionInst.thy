section \<open>Instantiation of Boogie functions used in Viper encoding\<close>

text \<open>A Boogie program is correct for all interpretations of the declared Boogie functions that 
satisfy certain criteria (well-typed, satisfy axioms, etc...). This theory provides one such 
instantiation for the Boogie functions used in Viper-generated Boogie programs. Note that this does
not include Boogie functions that are Viper-program-dependent (e.g., to model specific Viper functions
or specific Viper predicates).\<close>
theory ViperBoogieFunctionInst
imports ViperBoogieBasicRel
begin

subsection \<open>General\<close>

datatype fun_enum_bpl = 
     FGoodState
     | FReadHeap 
     | FReadMask
     | FHasPerm

text \<open>\<^typ>\<open>fun_enum_bpl\<close> enumerates the functions required for the encoding\<close>

type_synonym 'a sem_fun_bpl = "bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"

type_synonym fdecl_ty_bpl = "(nat \<times> ty list \<times> ty)"

definition values_respect_fdecl 
  where "values_respect_fdecl ts vs A fdecl \<equiv> 
           length ts = fst fdecl \<and> 
           list_all closed ts \<and> 
           map (type_of_val A) vs = map (instantiate ts) (fst (snd fdecl))"

subsection \<open>Good state assumption\<close>

abbreviation good_state_decl :: "'a ty_repr_bpl \<Rightarrow> fdecl_ty_bpl"
  where "good_state_decl T \<equiv> (0,[TConSingle (THeapId T), TConSingle (TMaskId T)],(TPrim TBool))"

fun good_state :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a sem_fun_bpl"
  where
    "good_state Pr F ts vs =
      (case (ts, vs) of 
           ([], [AbsV (AHeap h), AbsV (AMask m)]) \<Rightarrow> 
             Some (BoolV (\<exists> \<omega> :: 'a full_total_state. 
                                 \<comment>\<open>TODO: predicates \<longrightarrow> need state consistency\<close>
                                 heap_rel Pr F (get_hh_total_full \<omega>) h \<and> 
                                 mask_rel Pr F (get_mh_total_full \<omega>) m))
        | _ \<Rightarrow> None)"

lemma good_state_Some_true:
  assumes "heap_rel Pr F (get_hh_total_full \<omega>) hb" and
          "mask_rel Pr F (get_mh_total_full \<omega>) mb"
  shows "good_state Pr F [] [AbsV (AHeap hb), AbsV (AMask mb)] = Some (BoolV True)"
  using assms
  apply simp
  apply (rule exI[where ?x="\<omega>"])
  by simp

subsection \<open>Functions for polymorphic map instantiations\<close>

fun arg_types_of_field :: "'a ty_repr_bpl \<Rightarrow> 'a vb_field \<rightharpoonup> bpl_ty \<times> bpl_ty"
  where
    "arg_types_of_field T f = 
      ( case field_ty_fun_opt T f of
          Some (tid, [t1,t2]) \<Rightarrow> Some (t1,t2)
       | _ \<Rightarrow> None )"

subsubsection \<open>Heap\<close>

text \<open>select function for the heap: readHeap<A, B>(h: HeapType, r: Ref, f: (Field A B)): B\<close>

definition select_heap_aux :: "'a ty_repr_bpl \<Rightarrow> bpl_ty \<Rightarrow> 'a heap_repr \<Rightarrow> ref \<Rightarrow> 'a vb_field \<Rightarrow> 'a vbpl_val"
  where 
    "select_heap_aux T ret_ty h r f = 
       option_fold id (SOME v. type_of_val (vbpl_absval_ty T) v = ret_ty) (h (r, f))"

(* This function was used before lifting of a function to only reduce if the argument types are 
correct was defined separately.
fun select_heap_old :: "'a ty_repr_bpl \<Rightarrow> 'a bpl_fun"
  where 
    "select_heap_old T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             if (if_Some (\<lambda>res. res  = (t1, t2) \<and> vbpl_absval_ty_opt T (AHeap h) = Some ((THeapId T) ,[])) (arg_types_of_field T f))
             then Some (select_heap_aux T t2 h r f)
             else None
         | _ \<Rightarrow> None)"
*)

fun select_heap :: "'a ty_repr_bpl \<Rightarrow> 'a sem_fun_bpl"
  where 
    "select_heap T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
                Some (select_heap_aux T t2 h r f)
         | _ \<Rightarrow> None)"

text \<open>store function for the heap: updHeap<A, B>(h: HeapType, r: Ref, f: (Field A B), y: B): HeapType\<close>

fun store_heap :: "'a sem_fun_bpl"
  where
    "store_heap ts vs = 
       (case (ts, vs) of 
          ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f), v]) \<Rightarrow>
            Some (AbsV (  AHeap (h((r,f) \<mapsto> v))  ))
        | _ \<Rightarrow> None)"

subsubsection \<open>Mask\<close>

text \<open>select function for the heap: readMask<A, B>(m: MaskType, r: Ref, f: (Field A B)): Perm\<close>
fun select_mask :: "'a sem_fun_bpl"
  where 
    "select_mask ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (RealV (m (r, f)))
        | _ \<Rightarrow> None)"

lemma select_mask_some: 
  assumes "select_mask ts vs = Some t"
  shows "\<exists>t1 t2 m r f. ts = [t1, t2] \<and> vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]"
  using assms
  by (simp split: list.split_asm val.split_asm vbpl_absval.split_asm)

lemma select_mask_none:
  assumes "\<nexists>t1 t2 m r f. ts = [t1, t2] \<and> vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]"
  shows "select_mask ts vs = None"
  using assms select_mask_some option.exhaust_sel 
  by blast

text \<open>function for checking whether there is nonzero permission in mask\<close>

fun has_perm_in_mask :: "'a sem_fun_bpl"
  where 
    "has_perm_in_mask ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (BoolV (m (r, f) > 0))
        | _ \<Rightarrow> None)"

lemma has_perm_in_mask_some: 
  assumes "has_perm_in_mask ts vs = Some t"
  shows "\<exists>t1 t2 m r f. ts = [t1, t2] \<and> vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]"
  using assms
  by (simp split: list.split_asm val.split_asm vbpl_absval.split_asm)

lemma has_perm_in_mask_none:
  assumes "\<nexists>t1 t2 m r f. ts = [t1, t2] \<and> vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]"
  shows "has_perm_in_mask ts vs = None"
  using assms has_perm_in_mask_some option.exhaust_sel
  by blast

fun real_from_val :: "'a val \<Rightarrow> real"
  where
    "real_from_val (RealV r) = r"
  | "real_from_val _ = undefined"

lemma has_perm_in_mask_select_mask: 
  "has_perm_in_mask ts vs = map_option (\<lambda>v. BoolV ((real_from_val v) > 0)) (select_mask ts vs)"
proof (cases "\<exists> t1 t2 m r f. ts = [t1,t2] \<and> vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]")
  case True
  then show ?thesis 
    by force
next
  case False
  then show ?thesis
    using has_perm_in_mask_none select_mask_none
    by (metis option.map_disc_iff)
qed


subsubsection \<open>Knownfolded Mask\<close>

text \<open>select function for the knownfolded mask: readPMask<A, B>(pm: PMaskType, r: Ref, f: (Field A B)): bool\<close>

fun select_knownfolded_mask :: "'a ty_repr_bpl \<Rightarrow> 'a sem_fun_bpl"
  where 
    "select_knownfolded_mask T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AKnownFoldedMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (BoolV (m (r, f)))
        | _ \<Rightarrow> None)"

text \<open>store function for the knownfolded mask: updPMask<A, B>(PMaskType: PMaskType, obj: Ref, f_1: (Field A B), y: bool): PMaskType\<close>

fun store_knownfolded_mask :: "'a ty_repr_bpl \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "store_knownfolded_mask T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AKnownFoldedMask m), AbsV (ARef r), AbsV (AField f), BoolV b]) \<Rightarrow> 
             Some (AbsV (AKnownFoldedMask (m((r,f) := b))))
        | _ \<Rightarrow> None)"

subsection \<open>Global function map\<close>

text \<open>Transforms a Boogie function f into a function that only reduces to f if the input types are 
correct w.r.t. the function declaration. This function enables defining f to just guarantee
a correct return type if the argument types are correct and then lifts f to a function that satisfies
all the required typing constraints.\<close>

definition lift_fun_bpl :: "('a vbpl_absval) absval_ty_fun \<Rightarrow> fdecl_ty_bpl \<Rightarrow> 'a sem_fun_bpl \<Rightarrow> 'a sem_fun_bpl"
  where
    "lift_fun_bpl A fdecl f ts vs = 
       (if (length ts = fst fdecl \<and> 
           list_all closed ts \<and> 
           map (type_of_val A) vs = map (instantiate ts) (fst (snd fdecl)))
       then 
           f ts vs
       else
           None)"

lemma lift_fun_decl_well_typed:
  assumes "fdecl = (n_ty_params, args_ty, ret_ty)" and
          "length ts = n_ty_params" and
          "list_all closed ts" and
          "map (type_of_val A) vs = map (instantiate ts) args_ty" and
          "f ts vs = res"
        shows "lift_fun_bpl A fdecl f ts vs = res"
  using assms
  by (simp add: lift_fun_bpl_def)

text \<open>TODO: this is currently not modular. Ideally, different modules would define these interpretations
independently. Could achieve this by separating different functions.\<close>

fun fun_interp_vpr_bpl_aux :: "ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 
                                fun_enum_bpl \<Rightarrow> 'a sem_fun_bpl  \<times> fdecl_ty_bpl"
  where
    "fun_interp_vpr_bpl_aux Pr T F FGoodState = 
       (good_state Pr F, (0,[TConSingle (THeapId T), TConSingle (TMaskId T)],(TPrim TBool)))"
  | "fun_interp_vpr_bpl_aux Pr T F FReadHeap = 
       (select_heap T, (2,[TConSingle (THeapId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TVar 1)))"
  | "fun_interp_vpr_bpl_aux Pr T F FReadMask =
       (select_mask, (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TReal)))"
  | "fun_interp_vpr_bpl_aux Pr T F FHasPerm =
       (has_perm_in_mask, (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TReal)))"

fun fun_interp_vpr_bpl :: " ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 
                                fun_enum_bpl \<Rightarrow> 'a sem_fun_bpl"
  where 
    "fun_interp_vpr_bpl Pr T F fid = 
          (let (f,fdecl) = fun_interp_vpr_bpl_aux Pr T F fid in lift_fun_bpl (vbpl_absval_ty T) fdecl f)"

definition fun_interp_vpr_bpl_wf :: "ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (fun_enum_bpl \<Rightarrow> fname) \<Rightarrow>
                                      ('a vbpl_absval) fun_interp \<Rightarrow> bool"
  where 
   "fun_interp_vpr_bpl_wf Pr T FieldMap FunMap \<Gamma> = 
         (\<forall>fid. \<Gamma> (FunMap fid) = Some (fun_interp_vpr_bpl Pr T FieldMap fid))"

definition ctxt_wf :: "ViperLang.program \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (fun_enum_bpl \<Rightarrow> fname) \<Rightarrow> 'a econtext_bpl \<Rightarrow>  bool"
  where "ctxt_wf Pr T FieldMap FunMap ctxt \<equiv> fun_interp_vpr_bpl_wf Pr T FieldMap FunMap (fun_interp ctxt)"

lemma ctxt_wf_fun_interp:
  assumes "ctxt_wf Pr T FieldMap FunMap ctxt"
  shows "(fun_interp ctxt) (FunMap fid) = Some (fun_interp_vpr_bpl Pr T FieldMap fid)"
  using assms
  unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
  by fast

lemma assume_state_normal:
  assumes CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
          FieldTr: "field_translation Tr = F" and
          StateRel: "state_rel Pr TyRep Tr ctxt wd_mask_var \<omega>_def \<omega> ns" and 
          Heq: "heap_var Tr = h" and
          Meq: "mask_var Tr = m" and
          StateName: "FunMap FGoodState = state_name"
        shows "red_expr_bpl ctxt (FunExp state_name [] [Var h, Var m]) ns (BoolV True)"
proof  -
  let ?\<Gamma> = "fun_interp ctxt"
  let ?f = "good_state Pr (field_translation Tr)"
  let ?fdecl = "(0,[((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool))"

  from StateRel obtain hb where
       HLookup: "lookup_var (var_context ctxt) ns h = Some (AbsV (AHeap hb))" and
       "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])" and
       Hrel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
    unfolding state_rel_def state_rel0_def heap_var_rel_def
    using Heq
    by blast

  hence Hty:"type_of_vbpl_val TyRep (AbsV (AHeap hb)) = TConSingle (THeapId TyRep)"
    by simp

  from StateRel obtain mb where
       MLookup:"lookup_var (var_context ctxt) ns m = Some (AbsV (AMask mb))" and                
       Mrel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding state_rel_def state_rel0_def heap_var_rel_def mask_var_rel_def
    using Meq
    by blast

  hence Mty: "type_of_vbpl_val TyRep (AbsV (AMask mb)) = TConSingle (TMaskId TyRep)"
    by simp

  show ?thesis
    apply rule
    using CtxtWf
    unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
    using StateName
      apply blast
     apply rule
      apply rule
      apply (rule HLookup)
     apply rule
    apply rule
      apply (rule MLookup)
     apply rule    
    apply simp
    apply (rule lift_fun_decl_well_typed)
         apply simp
        apply simp
      apply simp
    using Hty Mty
     apply (simp del: vbpl_absval_ty_opt.simps)    
    using Hrel Mrel good_state_Some_true FieldTr
    by blast
qed


end