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
     | FGoodMask
     | FReadHeap
     | FUpdateHeap
     | FReadMask
     | FUpdateMask
     | FReadKnownFoldedMask
     | FUpdateKnownFoldedMask
     | FHasPerm
     | FIdenticalOnKnownLocs

text \<open>\<^typ>\<open>fun_enum_bpl\<close> enumerates the functions required for the encoding\<close>

type_synonym 'a sem_fun_bpl = "bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"

type_synonym fdecl_ty_bpl = "(nat \<times> ty list \<times> ty)"

definition values_respect_fdecl 
  where "values_respect_fdecl ts vs A fdecl \<equiv> 
           length ts = fst fdecl \<and> 
           list_all closed ts \<and> 
           map (type_of_val A) vs = map (instantiate ts) (fst (snd fdecl))"

text \<open>The following function transforms a Boogie function f into a function that only reduces to f 
if the input types are correct w.r.t. the function declaration. This function enables defining f to 
just guarantee a correct return type if the argument types are correct and then lifts f to a function
that satisfies all the required typing constraints.\<close>

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

lemma lift_fun_decl_fun_interp_single_wf_1:
  assumes "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) f"
  shows "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty)  (lift_fun_bpl A (n_ty_params, args_ty, ret_ty) f)"
  using assms
  by (simp add: lift_fun_decl_well_typed)

lemma lift_fun_decl_fun_interp_single_wf_1_eq:
  assumes "fd = fd'"
          "fun_interp_single_wf A fd f"
        shows "fun_interp_single_wf A fd (lift_fun_bpl A fd' f)"
  apply (cases fd)
  using assms lift_fun_decl_fun_interp_single_wf_1
  by blast

lemma lift_fun_decl_fun_interp_single_wf_2:
  assumes "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) f"
  shows "fun_interp_single_wf_2 A (n_ty_params, args_ty, ret_ty) (lift_fun_bpl A (n_ty_params, args_ty, ret_ty) f)"
  using assms
  apply (unfold lift_fun_bpl_def)
  apply simp
  using map_eq_imp_length_eq 
  by fastforce

lemma lift_fun_decl_fun_interp_single_wf_2_eq:
  assumes "fd = fd'"
          "fun_interp_single_wf A fd f"
        shows "fun_interp_single_wf_2 A fd (lift_fun_bpl A fd' f)"
  apply (cases fd)
  using assms lift_fun_decl_fun_interp_single_wf_2
  by blast  

lemma lift_fun_decl_fun_interp_single_wf_eq:
  assumes "fd = fd'"
          "fun_interp_single_wf A fd' f"
        shows "fun_interp_single_wf A fd (lift_fun_bpl A fd' f) \<and> fun_interp_single_wf_2 A fd (lift_fun_bpl A fd' f)"
  using assms lift_fun_decl_fun_interp_single_wf_1_eq lift_fun_decl_fun_interp_single_wf_2_eq
  by meson

lemma fun_interp_single_wf_intro:
  assumes "\<And> ts vs. length ts = n_ty_params \<Longrightarrow> 
                     list_all closed ts \<Longrightarrow>
                     length vs = length args_ty \<Longrightarrow>
                     map (type_of_val A) vs = (map (instantiate ts) args_ty) \<Longrightarrow>
                     \<exists>v. f ts vs = Some v \<and> type_of_val A v = instantiate ts ret_ty"
shows "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) f "
  using assms
  by simp

subsection \<open>Good state and good mask\<close>

fun good_state :: "ViperLang.program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a sem_fun_bpl"
  where
    "good_state Pr F ts vs =
      (case (ts, vs) of 
           ([], [AbsV (AHeap h), AbsV (AMask m)]) \<Rightarrow> 
             Some (BoolV (\<exists> \<omega> :: 'a full_total_state. 
                                 \<comment>\<open>TODO: predicates \<longrightarrow> need state consistency\<close>
                                 wf_mask_simple (get_mh_total_full \<omega>) \<and>
                                 heap_rel Pr F (get_hh_total_full \<omega>) h \<and> 
                                 mask_rel Pr F (get_mh_total_full \<omega>) m))
        | _ \<Rightarrow> None)"

lemma good_state_Some_true:
  assumes "wf_mask_simple (get_mh_total_full (\<omega> :: 'a full_total_state))" and 
          "heap_rel Pr F (get_hh_total_full \<omega>) hb" and
          "mask_rel Pr F (get_mh_total_full \<omega>) mb"
  shows "good_state Pr F [] [AbsV (AHeap hb), AbsV (AMask mb)] = Some (BoolV True)"
  using assms
  apply simp
  apply (rule exI[where ?x="\<omega>"])
  by simp

lemma good_state_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf (vbpl_absval_ty T) (0,[TConSingle (THeapId T), TConSingle (TMaskId T)],(TPrim TBool)) (good_state Pr F)"
proof (rule fun_interp_single_wf_intro)
  fix ts vs
  assume "length ts = 0" and 
 ArgsTy: "map (type_of_val (vbpl_absval_ty T)) vs = map (instantiate ts) [TConSingle (THeapId T), TConSingle (TMaskId T)]"

  hence "ts = []" by blast

  from ArgsTy obtain h m where
    "vs = [AbsV (AHeap h), AbsV (AMask m)]" 
    using all_inversion_type_of_vbpl_val[OF WfTyRepr]
    by force

  show "\<exists>v. good_state Pr F ts vs = Some v \<and> type_of_vbpl_val T v = instantiate ts (TPrim prim_ty.TBool)"
    by (simp add: \<open>ts = _\<close> \<open>vs = _\<close>)
qed

fun good_mask :: "'a sem_fun_bpl"
  where 
    "good_mask ts vs =
      (case (ts, vs) of 
           ([], [AbsV (AMask m)]) \<Rightarrow> 
             Some (BoolV ((\<forall> loc. m loc \<ge> 0) \<and> (\<forall> r f t. m (r, (NormalField f t)) \<le> 1)))
        | _ \<Rightarrow> None)"

lemma good_mask_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf (vbpl_absval_ty T) (0,[TConSingle (TMaskId T)],(TPrim TBool)) good_mask"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] deconstruct_list_length_2 VCExprHelper.treal_realv split: val.split vbpl_absval.split)

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

fun select_heap :: "'a ty_repr_bpl \<Rightarrow> 'a sem_fun_bpl"
  where 
    "select_heap T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
                Some (select_heap_aux T t2 h r f)
         | _ \<Rightarrow> None)"


lemma select_heap_aux_well_typed:
  assumes WfTyRepr: "wf_ty_repr_bpl T" and
          "closed ret_ty"  and
          HeapTy: "type_of_vbpl_val T (AbsV (AHeap h)) = TConSingle (THeapId T)" and
          FieldTy: "field_ty_fun_opt T f = Some (TFieldId T, [fieldKind, ret_ty])"
  shows "type_of_vbpl_val T (select_heap_aux T ret_ty h r f) = ret_ty"
proof (cases "h (r,f)")
  case None
  with closed_types_inhabited[OF \<open>closed _\<close>] show ?thesis
    unfolding select_heap_aux_def
    apply simp
    by (meson \<open>closed _\<close> closed_types_inhabited someI_ex)
next
  case (Some v)
  from HeapTy have "vbpl_absval_ty_opt T (AHeap h) = Some (THeapId T, [])"
    using tdummyid_fresh[OF WfTyRepr]                                                                                    
    by (metis (no_types, lifting) Pair_inject UnI1 prod.collapse range_eqI ty.inject(3) type_of_val.simps(2) vbpl_absval_ty_not_dummy)

  with Some FieldTy have "type_of_vbpl_val T v = ret_ty"
    using heap_bpl_well_typed_elim
    by meson

  thus ?thesis
    unfolding select_heap_aux_def Some
    by simp
qed

lemma select_heap_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf (vbpl_absval_ty T) (2,[TConSingle (THeapId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TVar 1))
                                                 (select_heap T)"
proof (rule fun_interp_single_wf_intro)
  fix ts vs
  assume "length ts = 2" and closed: "list_all closed ts" and
 ArgsTy: "map (type_of_vbpl_val T) vs = map (instantiate ts) [TConSingle (THeapId T), TConSingle (TRefId T), TCon (TFieldId T) [TVar 0, TVar 1]]"

  from this obtain t1 t2 where "ts = [t1, t2]"
    using deconstruct_list_length_2
    by fast

  from ArgsTy obtain h r f where
    "vs = [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f)]" 
    by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr])

  with ArgsTy have HeapTy: "type_of_vbpl_val T (AbsV (AHeap h)) = TConSingle (THeapId T)" 
    by simp

  from \<open>vs = _\<close> ArgsTy have "type_of_vbpl_val T (AbsV (AField f)) = TCon (TFieldId T) [t1, t2]"
    using \<open>ts = _\<close>
    by simp

  hence FieldTy: "field_ty_fun_opt T f = Some (TFieldId T, [t1, t2])"
  using tdummyid_fresh[OF WfTyRepr]                                                                                    
  by (metis list.distinct(1) prod.exhaust_sel snd_conv ty.inject(3) type_of_val.simps(2) vbpl_absval_ty_not_dummy vbpl_absval_ty_opt.simps(2))

  thus "\<exists>v. select_heap T ts vs = Some v \<and> type_of_vbpl_val T v = instantiate ts (TVar 1)"
    using \<open>vs = _\<close> \<open>ts = _\<close> select_heap_aux_well_typed[OF WfTyRepr _ HeapTy FieldTy] closed
    by auto
qed

text \<open>store function for the heap: updHeap<A, B>(h: HeapType, r: Ref, f: (Field A B), y: B): HeapType\<close>
      
fun store_heap :: "'a sem_fun_bpl"
  where
    "store_heap ts vs = 
       (case (ts, vs) of 
          ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f), v]) \<Rightarrow>
            Some (AbsV (  AHeap (h((r,f) \<mapsto> v))  ))
        | _ \<Rightarrow> None)"

lemma store_heap_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf (vbpl_absval_ty T) (2,[TConSingle (THeapId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)]), TVar 1], TConSingle (THeapId T))
                                                 store_heap"
proof (rule fun_interp_single_wf_intro)
  fix ts vs
  assume "length ts = 2" and closed: "list_all closed ts" and
 ArgsTy: "map (type_of_vbpl_val T) vs = map (instantiate ts) [TConSingle (THeapId T), TConSingle (TRefId T), TCon (TFieldId T) [TVar 0, TVar 1], TVar 1]"

  from this obtain t1 t2 where "ts = [t1, t2]"
    using deconstruct_list_length_2
    by fast

  from ArgsTy obtain h r f v where
    "vs = [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f), v]" 
    by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr])

  with ArgsTy have 
   HeapTy: "type_of_vbpl_val T (AbsV (AHeap h)) = TConSingle (THeapId T)" 
       and "type_of_vbpl_val T (AbsV (AField f)) = TCon (TFieldId T) [t1, t2]"
       and NewValTy: "type_of_vbpl_val T v = t2"
    using \<open>ts = _\<close>
    by auto

  hence FieldTy: "field_ty_fun_opt T f = Some (TFieldId T, [t1, t2])"
  using tdummyid_fresh[OF WfTyRepr]                                                                                    
  by (metis list.distinct(1) prod.exhaust_sel snd_conv ty.inject(3) type_of_val.simps(2) vbpl_absval_ty_not_dummy vbpl_absval_ty_opt.simps(2))

  from HeapTy have HeapTyOpt: "vbpl_absval_ty_opt T (AHeap h) = Some (THeapId T, [])"
    using tdummyid_fresh[OF WfTyRepr] 
    by (metis (no_types, lifting) Pair_inject UnI1 prod.exhaust_sel range_eqI ty.inject(3) type_of_val.simps(2) vbpl_absval_ty_not_dummy)

  thus " \<exists>v. store_heap ts vs = Some v \<and> type_of_vbpl_val T v = instantiate ts (TConSingle (THeapId T))"
    using \<open>vs = _\<close> \<open>ts = _\<close> closed heap_upd_ty_preserved[OF HeapTyOpt FieldTy NewValTy]
    by simp
qed

subsubsection \<open>Mask\<close>

text \<open>select function for the mask: readMask<A, B>(m: MaskType, r: Ref, f: (Field A B)): Perm\<close>

fun select_mask :: "'a sem_fun_bpl"
  where 
    "select_mask ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (RealV (m (r, f)))
        | _ \<Rightarrow> None)"

lemma select_mask_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TReal)) 
              select_mask"
proof (rule fun_interp_single_wf_intro)
  fix ts vs
  assume "length ts = 2" and 
  ArgsTy: "map (type_of_val (vbpl_absval_ty T)) vs = 
           map (instantiate ts) [TConSingle (TMaskId T), TConSingle (TRefId T), TCon (TFieldId T) [(TVar 0),(TVar 1)]]"

  from this obtain t1 t2 where "ts = [t1, t2]"
    using deconstruct_list_length_2 by blast

  from ArgsTy obtain m r f where
    "vs = [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]"
    using all_inversion_type_of_vbpl_val[OF WfTyRepr]
    by force
    
  show  "\<exists>v. select_mask ts vs = Some v \<and> type_of_vbpl_val T v = instantiate ts (TPrim TReal) "
    by (simp add: \<open>ts = _\<close> \<open>vs = _\<close>)
qed

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

text \<open>store function for the mask: updMask<A, B>(h: MaskType, r: Ref, f: (Field A B), y: Perm): Perm\<close>

fun store_mask :: "'a sem_fun_bpl"
  where
    "store_mask ts vs = 
       (case (ts, vs) of 
          ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f), RealV p]) \<Rightarrow>
            Some (AbsV (  AMask (m((r,f) := p))  ))
        | _ \<Rightarrow> None)"

lemma store_mask_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)]), TPrim TReal], (TConSingle (TMaskId T)))
              store_mask"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] deconstruct_list_length_2 VCExprHelper.treal_realv split: val.split vbpl_absval.split)

text \<open>function for checking whether there is nonzero permission in mask\<close>

fun has_perm_in_mask :: "'a sem_fun_bpl"
  where 
    "has_perm_in_mask ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (BoolV (m (r, f) > 0))
        | _ \<Rightarrow> None)"

lemma has_direct_perm_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (2,[TConSingle (TMaskId T), TConSingle (TRefId T), (TCon (TFieldId T) [(TVar 0),(TVar 1)])], (TPrim TBool))
              has_perm_in_mask"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] deconstruct_list_length_2 VCExprHelper.treal_realv split: val.split vbpl_absval.split)

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

lemma select_knownfolded_mask_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (2,[TConSingle (TKnownFoldedMaskId T), TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TBool))
              (select_knownfolded_mask T)"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] deconstruct_list_length_2 lit_inversion_type_of_val split: val.split vbpl_absval.split)

text \<open>store function for the knownfolded mask: updPMask<A, B>(PMaskType: PMaskType, obj: Ref, f_1: (Field A B), y: bool): PMaskType\<close>

fun store_knownfolded_mask :: "bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "store_knownfolded_mask ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AKnownFoldedMask m), AbsV (ARef r), AbsV (AField f), BoolV b]) \<Rightarrow> 
             Some (AbsV (AKnownFoldedMask (m((r,f) := b))))
        | _ \<Rightarrow> None)"

lemma store_knownfolded_mask_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (2,[TConSingle (TKnownFoldedMaskId T), TConSingle (TRefId T), (TCon (TFieldId T) [(TVar 0),(TVar 1)]),(TPrim TBool)], TConSingle (TKnownFoldedMaskId T))
              store_knownfolded_mask"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] deconstruct_list_length_2 lit_inversion_type_of_val split: val.split vbpl_absval.split)

subsubsection \<open>Identical on known locations\<close>

fun identical_on_known_locs ::  "'a sem_fun_bpl"
  where 
    "identical_on_known_locs ts vs = 
      (case (ts, vs) of 
         ([], [AbsV (AHeap h), AbsV (AHeap h_exhale), AbsV (AMask m)]) \<Rightarrow>
           Some (BoolV (\<forall>r f t. m (r, NormalField f t) > 0 \<longrightarrow> h (r, NormalField f t) = h_exhale (r, NormalField f t)))
       | _ \<Rightarrow> None)"

lemma identical_on_known_locs_fun_interp_single_wf:
  assumes WfTyRepr: "wf_ty_repr_bpl T"
  shows "fun_interp_single_wf 
              (vbpl_absval_ty T) 
              (0,[TConSingle (THeapId T), TConSingle (THeapId T), TConSingle (TMaskId T)], (TPrim TBool))
              identical_on_known_locs"
  apply (rule fun_interp_single_wf_intro)
  by (clarsimp dest!: all_inversion_type_of_vbpl_val[OF WfTyRepr] split: val.split vbpl_absval.split)

subsection \<open>Global function map\<close>

text \<open>TODO: this is currently not modular. Ideally, different modules would define these interpretations
independently. Could achieve this by separating different functions.\<close>

fun fun_interp_vpr_bpl_aux :: "ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 
                                fun_enum_bpl \<Rightarrow> 'a sem_fun_bpl  \<times> fdecl_ty_bpl"
  where
    "fun_interp_vpr_bpl_aux Pr T F FGoodState = 
       (good_state Pr F, (0,[TConSingle (THeapId T), TConSingle (TMaskId T)],(TPrim TBool)))"
  | "fun_interp_vpr_bpl_aux Pr T F FGoodMask = 
       (good_mask, (0,[TConSingle (TMaskId T)],(TPrim TBool)))"
  | "fun_interp_vpr_bpl_aux Pr T F FReadHeap = 
       (select_heap T, (2,[TConSingle (THeapId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TVar 1)))"
  | "fun_interp_vpr_bpl_aux Pr T F FUpdateHeap = 
       (store_heap, (2,[TConSingle (THeapId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)]), TVar 1], TConSingle (THeapId T)))"
  | "fun_interp_vpr_bpl_aux Pr T F FReadMask =
       (select_mask, (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TReal)))"
  | "fun_interp_vpr_bpl_aux Pr T F FUpdateMask =
       (store_mask, (2,[TConSingle (TMaskId T),TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)]), TPrim TReal], TConSingle (TMaskId T)))"
  | "fun_interp_vpr_bpl_aux Pr T F FReadKnownFoldedMask  =
       (select_knownfolded_mask T, (2,[TConSingle (TKnownFoldedMaskId T), TConSingle (TRefId T),(TCon (TFieldId T) [(TVar 0),(TVar 1)])],(TPrim TBool)))"
  | "fun_interp_vpr_bpl_aux Pr T F FUpdateKnownFoldedMask =
       (store_knownfolded_mask, (2,[TConSingle (TKnownFoldedMaskId T), TConSingle (TRefId T), (TCon (TFieldId T) [(TVar 0),(TVar 1)]),(TPrim TBool)], TConSingle (TKnownFoldedMaskId T)))"
  | "fun_interp_vpr_bpl_aux Pr T F FHasPerm =
       (has_perm_in_mask, (2,[TConSingle (TMaskId T), TConSingle (TRefId T), (TCon (TFieldId T) [(TVar 0),(TVar 1)])], (TPrim TBool)))"
  | "fun_interp_vpr_bpl_aux Pr T F FIdenticalOnKnownLocs =
       (identical_on_known_locs, (0,[TConSingle (THeapId T), TConSingle (THeapId T), TConSingle (TMaskId T)], (TPrim TBool)))"

fun fun_interp_vpr_bpl :: " ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 
                                fun_enum_bpl \<Rightarrow> 'a sem_fun_bpl"
  where 
    "fun_interp_vpr_bpl Pr T F fid = 
          (let (f,fdecl) = fun_interp_vpr_bpl_aux Pr T F fid in lift_fun_bpl (vbpl_absval_ty T) fdecl f)"

fun fun_interp_vpr_bpl_concrete :: "ViperLang.program \<Rightarrow>  'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (fun_enum_bpl \<Rightarrow> fname) \<Rightarrow> ('a vbpl_absval) fun_interp"
  where "fun_interp_vpr_bpl_concrete Pr T FieldMap FunMap fun_name = 
         (if (\<exists>fid. FunMap fid = fun_name) then
           Some (fun_interp_vpr_bpl Pr T FieldMap (SOME fid. FunMap fid = fun_name))
         else
           None)"

definition fun_interp_vpr_bpl_wf :: "ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> (fun_enum_bpl \<Rightarrow> fname) \<Rightarrow>
                                      ('a vbpl_absval) fun_interp \<Rightarrow> bool"
  where 
   "fun_interp_vpr_bpl_wf Pr T FieldMap FunMap \<Gamma> = 
         (\<forall>fid. \<Gamma> (FunMap fid) = Some (fun_interp_vpr_bpl Pr T FieldMap fid))"

lemma fun_interp_vpr_bpl_concrete_wf:
  assumes "inj FunMap"
  shows "fun_interp_vpr_bpl_wf Pr T FieldMap FunMap (fun_interp_vpr_bpl_concrete Pr T FieldMap FunMap)"
  unfolding fun_interp_vpr_bpl_wf_def
proof (rule allI)
  fix fid

  have "\<exists>fid'. FunMap fid' = FunMap fid"
    by blast

  moreover have "fid = (SOME fid'. FunMap fid' = FunMap fid)"
    using \<open>inj FunMap\<close>
    by (metis inv_def inv_f_f)

  thus "fun_interp_vpr_bpl_concrete Pr T FieldMap FunMap (FunMap fid) = Some (fun_interp_vpr_bpl Pr T FieldMap fid)"
    by auto
qed

lemma fun_interp_vpr_bpl_concrete_lookup:
  assumes "inj FunMap" and
          "FunMap fid = fname"
        shows "fun_interp_vpr_bpl_concrete Pr T FieldMap FunMap fname = Some (fun_interp_vpr_bpl Pr T FieldMap fid)"
  using fun_interp_vpr_bpl_concrete_wf[OF assms(1)] assms(2)
  unfolding fun_interp_vpr_bpl_wf_def
  by blast


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
          StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and 
          FieldTr: "field_translation Tr = F" and
          Heq: "heap_var Tr = h" and
          Meq: "mask_var Tr = m" and
          StateName: "FunMap FGoodState = state_name"
        shows "red_expr_bpl ctxt (FunExp state_name [] [Var h, Var m]) ns (BoolV True)"
proof  -
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
     apply simp
    using Hrel Mrel good_state_Some_true FieldTr state_rel0_wf_mask_simple[OF state_rel_state_rel0[OF StateRel]]
    by blast
qed

lemma red_ast_bpl_identical_on_known_locs:
  assumes CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
          "id_on_known_locs_name = FunMap FIdenticalOnKnownLocs" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          LookupDeclExhaleHeap: "lookup_var_decl (var_context ctxt) hvar_exh = Some (TConSingle (THeapId TyRep), None)" and
          LookupHeapVar: "lookup_var (var_context ctxt) ns hvar = Some (AbsV (AHeap h))" and
          LookupMaskVar: "lookup_var (var_context ctxt) ns mvar = Some (AbsV (AMask m))" and 
          ExhaleHeapFresh: "hvar_exh \<notin> {hvar , mvar}" and
          HeapTy: "vbpl_absval_ty_opt TyRep (AHeap h) = Some ((THeapId TyRep) ,[])" and
          NewHeapTy: "vbpl_absval_ty_opt TyRep (AHeap h_new) = Some ((THeapId TyRep) ,[])" and
          MaskTy: "vbpl_absval_ty_opt TyRep (AMask m) = Some ((TMaskId TyRep), [])" and
          IdenticalOnKnownCond: "(\<forall>r f t. m (r, NormalField f t) > 0 \<longrightarrow> h (r, NormalField f t) = h_new (r, NormalField f t))"
        shows "red_ast_bpl P ctxt 
                                   ((BigBlock name (Havoc hvar_exh # 
                                                    Assume (FunExp id_on_known_locs_name [] [Var hvar, Var hvar_exh, Var mvar]) #                                                    
                                                    cs) str tr,
                                     cont),
                                     Normal ns)
                                   ((BigBlock name cs str tr, cont), 
                                       Normal (update_var (var_context ctxt) ns hvar_exh (AbsV (AHeap h_new))))"
proof (rule red_ast_bpl_havoc_assume[OF LookupDeclExhaleHeap])
  show "red_expr_bpl ctxt (FunExp id_on_known_locs_name [] [expr.Var hvar, expr.Var hvar_exh, expr.Var mvar])
                          (update_var (var_context ctxt) ns hvar_exh (AbsV (AHeap h_new))) (BoolV True)"
    apply (subst \<open>id_on_known_locs_name = _\<close>)
    apply (rule RedFunOp)
      apply (rule ctxt_wf_fun_interp[OF CtxtWf])

    using ExhaleHeapFresh
    apply (fastforce intro: RedExpListCons RedExpListNil RedVar LookupHeapVar LookupMaskVar)
    apply simp
    apply (rule lift_fun_decl_well_typed)
        apply simp
       apply simp
      apply simp
    using TypeInterp HeapTy NewHeapTy MaskTy
     apply simp
    apply (simp add: IdenticalOnKnownCond)
    done
qed (insert assms, auto)


end