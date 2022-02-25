section \<open>Viper Instantiation of Boogie Abstract Values\<close>

theory ViperBoogieInstantiation
imports Viper.ViperLang Viper.ValueAndBasicState Boogie_Lang.Semantics HOL.Real TotalUtil Boogie_Lang.VCExprHelper
begin

type_synonym 'a vpr_val = "'a ValueAndBasicState.val"
type_synonym 'a bpl_val = "'a Semantics.val"

type_synonym vpr_ty = ViperLang.vtyp
type_synonym bpl_ty = Lang.ty

type_synonym viper_prog = "ViperLang.program"

subsection \<open>Abstract values datatype\<close>

\<comment>\<open>implementation detail\<close>
datatype 'a vb_field = 
     NormalField field_ident vpr_ty
   | PredSnapshotField "'a predicate_loc" 
   | PredKnownFoldedField "'a predicate_loc"
   | DummyField bpl_ty bpl_ty \<comment>\<open>used to make sure that every field type \<open>Field A B\<close> is inhabited\<close>

\<comment>\<open>implementation detail\<close>
codatatype 'a frame_fragment = EmptyFrame | LiftFrame 'a | CombineFrame "'a frame_fragment" "'a frame_fragment"

datatype 'a vbpl_absval = 
    ARef ref
  | ADomainVal 'a
\<comment>\<open>implementation detail\<close>
  | AField "'a vb_field"
  | AHeap "ref \<Rightarrow> 'a vb_field \<rightharpoonup> ('a vbpl_absval) bpl_val"
  | AMask "ref \<Rightarrow> 'a vb_field \<Rightarrow> real"                      
  | AKnownFoldedMask "ref \<Rightarrow> 'a vb_field \<Rightarrow> bool"         
  | AFrame  "(('a vbpl_absval) bpl_val) frame_fragment"
  | ADummy tcon_id "bpl_ty list" 

text \<open>The reason for including \<^const>\<open>ADummy\<close> is that the Boogie interface requires that every type 
is inhabited. We will need to make sure that \<^term>\<open>ADummy tcon_id ts\<close> is mapped to \<^term>\<open>TCon tcon_id ts\<close> 
only if \<^term>\<open>TCon tcon_id ts\<close> is not a meaningful type (e.g., not the heap type)\<close>

type_synonym 'a vbpl_val = "('a vbpl_absval) bpl_val"

type_synonym 'a heap_repr = "ref \<Rightarrow> 'a vb_field \<rightharpoonup> 'a vbpl_val"

subsection \<open>Translation interface\<close>

datatype tcon_enum = TCRef | TCField | TCHeap | TCMask | TCKnownFoldedMask | TCFrameFragment | TCNormalField

record 'a vpr_bpl_translation =
  tcon_id_repr :: "tcon_enum \<Rightarrow> tcon_id"
  pred_snap_field_type :: "predicate_ident \<rightharpoonup> bpl_ty"
  pred_knownfolded_field_type :: "predicate_ident \<rightharpoonup> bpl_ty"
  domain_translation :: "abs_type \<rightharpoonup> tcon_id \<times> ty list" \<comment>\<open>we assume domains without type parameters\<close>
  domain_type :: "'a \<Rightarrow> abs_type"

definition wf_vpr_bpl_translation :: "'a vpr_bpl_translation \<Rightarrow> bool"
  where "wf_vpr_bpl_translation T \<equiv>
               (\<forall> vt bt. domain_translation T vt = Some bt \<longrightarrow> list_all closed (snd bt)) \<and>
               (\<forall> pid bt. pred_snap_field_type T pid = Some bt \<longrightarrow> closed bt) \<and>
               (\<forall> pid bt. pred_knownfolded_field_type T pid = Some bt \<longrightarrow> closed bt)"

abbreviation "TRefId T \<equiv> (tcon_id_repr T) TCRef"
abbreviation "TFieldId T \<equiv> (tcon_id_repr T) TCField"
abbreviation "THeapId T \<equiv> (tcon_id_repr T) TCHeap"
abbreviation "TMaskId T \<equiv> (tcon_id_repr T) TCMask"
abbreviation "TKnownFoldedMaskId T \<equiv> (tcon_id_repr T) TCKnownFoldedMask"
abbreviation "TFrameFragmentId T \<equiv> (tcon_id_repr T) TCFrameFragment"
abbreviation "TNormalFieldId T \<equiv> (tcon_id_repr T) TCNormalField"

text \<open>For the dummy type, we just pick some identifier that is different from all the ones used by 
      the translation\<close>
definition TDummyId :: "'a vpr_bpl_translation \<Rightarrow> tcon_id"
  where "TDummyId T \<equiv> (SOME v. v \<notin> range (tcon_id_repr T))"

abbreviation TConSingle :: "tcon_id \<Rightarrow> bpl_ty"
  where "TConSingle tid \<equiv> TCon tid []"

lemma "closed (TConSingle tid)"
  by simp

subsection \<open>Type interpretation\<close>

fun vpr_to_bpl_ty :: "'a vpr_bpl_translation \<Rightarrow> vpr_ty \<rightharpoonup> bpl_ty"
  where 
    "vpr_to_bpl_ty T ViperLang.TInt = Some (Lang.TPrim Lang.TInt)"
  | "vpr_to_bpl_ty T ViperLang.TBool = Some( Lang.TPrim Lang.TBool)"  
  | "vpr_to_bpl_ty T ViperLang.TPerm = Some (Lang.TPrim Lang.TInt)" (* TODO: Real type in Boogie *)
  | "vpr_to_bpl_ty T ViperLang.TRef = Some (TConSingle (TRefId T))"
  | "vpr_to_bpl_ty T (ViperLang.TAbs t) = map_option (\<lambda>tc. TCon (fst tc) (snd tc)) (domain_translation T t)"

fun field_ty_fun_opt :: "'a vpr_bpl_translation \<Rightarrow> 'a vb_field \<rightharpoonup> (tcon_id \<times> ty list)"
  where 
    "field_ty_fun_opt T (NormalField field_id vty) = map_option (\<lambda>t.(TFieldId T, [TConSingle (TNormalFieldId T), t])) (vpr_to_bpl_ty T vty)"
  | "field_ty_fun_opt T (PredSnapshotField pred_loc) = 
       map_option (\<lambda>p. (TFieldId T, [p, TConSingle (TFrameFragmentId T)])) (pred_snap_field_type T (fst pred_loc))"
  | "field_ty_fun_opt T (PredKnownFoldedField pred_loc) = 
       map_option (\<lambda>p. (TFieldId T, [p, TConSingle (TFrameFragmentId T)])) (pred_knownfolded_field_type T (fst pred_loc))"
  | "field_ty_fun_opt T (DummyField t1 t2) =
       Some_if (closed t1 \<and> closed t2) (TFieldId T, [t1, t2])"

lemma field_ty_fun_opt_closed: "wf_vpr_bpl_translation T \<Longrightarrow> 
                                field_ty_fun_opt T f = Some res \<Longrightarrow>  
                                list_all closed (snd res)"  
  apply (cases f)
     apply (rename_tac vty)
     apply (case_tac vty)
  by (auto split: if_split_asm simp: wf_vpr_bpl_translation_def)

fun tcon_to_bplty :: "(tcon_id \<times> bpl_ty list) \<Rightarrow> bpl_ty"
  where "tcon_to_bplty tc = TCon (fst tc) (snd tc)"

definition heap_rel :: "('a vbpl_absval \<times> 'a vbpl_absval) set"
  where "heap_rel = {(y, (AHeap h)) | h r f y v. h r f = Some v \<and> y \<in> set_val v}"

lemma wf_heap_rel: "wf heap_rel"
  unfolding wf_def
  apply (rule)+
  apply (unfold heap_rel_def)
  apply (rule vbpl_absval.induct)
  by auto (metis UNIV_I image_eqI vbpl_absval.inject(4))

primrec ty_inhabitant :: "tcon_enum \<rightharpoonup> (nat \<times> (Lang.ty list \<Rightarrow> 'a vbpl_absval))" 
  where
    "ty_inhabitant TCRef      = Some (0, \<lambda>_.  ARef undefined)"
  | "ty_inhabitant TCField    = Some (2, \<lambda>ts. AField (DummyField (hd ts) (hd (tl ts))))"
  | "ty_inhabitant TCHeap     = Some (0, \<lambda>_. AHeap (\<lambda> _ _. None))"
  | "ty_inhabitant TCMask     = Some (0, \<lambda>_. AMask (\<lambda> _ _. 0))"
  | "ty_inhabitant TCKnownFoldedMask = Some (0, \<lambda>_. AKnownFoldedMask (\<lambda> _ _. False))"
  | "ty_inhabitant TCFrameFragment = Some (0, \<lambda>_. AFrame EmptyFrame)"
  | "ty_inhabitant TCNormalField = None"

text\<open>The \<open>NormalField\<close> type is used only to construct field types and thus, we do not need to provide
an inhabitant that is not a dummy value.\<close>

definition is_inhabited :: "'a vpr_bpl_translation \<Rightarrow> tcon_id \<Rightarrow> nat \<Rightarrow> bool"
  where 
    "is_inhabited T tid n = 
      (\<exists> tc_enum :: tcon_enum. \<exists> res :: (nat \<times> (Lang.ty list \<Rightarrow> 'a vbpl_absval)). 
         (tcon_id_repr T) tc_enum = tid \<and> ty_inhabitant tc_enum = Some res \<and> n = fst res)"


function (sequential) vbpl_absval_ty_opt :: "'a vpr_bpl_translation \<Rightarrow> 'a vbpl_absval \<rightharpoonup> (tcon_id \<times> bpl_ty list)"
  where 
   "vbpl_absval_ty_opt T (ARef r) = Some (TRefId T, [])"
 | "vbpl_absval_ty_opt T (AField vb_field) = (field_ty_fun_opt T vb_field)"
 | "vbpl_absval_ty_opt T (ADomainVal v) = domain_translation T (domain_type T v)"
 | "vbpl_absval_ty_opt T (AHeap h) = 
      Some_if 
          (\<forall>r::ref. \<forall> f :: 'a vb_field. \<forall>fieldKind t :: bpl_ty. \<forall> v :: 'a vbpl_val. 
             h r f = Some v \<and> field_ty_fun_opt T f = Some (TFieldId T, [fieldKind, t]) \<longrightarrow> 
             (case v of LitV lit \<Rightarrow> TPrim (type_of_lit lit) = t | 
                        AbsV absv \<Rightarrow> map_option tcon_to_bplty (vbpl_absval_ty_opt T absv) = Some t)
          ) 
          (THeapId T, [])"
 | "vbpl_absval_ty_opt T (AMask m) = Some (TMaskId T, [])"
 | "vbpl_absval_ty_opt T (AKnownFoldedMask pm) = Some (TKnownFoldedMaskId T, [])"
 | "vbpl_absval_ty_opt T (AFrame f) = Some (TFrameFragmentId T, [])"
 | "vbpl_absval_ty_opt T (ADummy tid ts) = 
     Some_if (\<not> is_inhabited T tid (length ts) \<and> list_all closed ts) (tid, ts)"
  by (pat_completeness) auto
termination
  apply (relation "inv_image heap_rel snd")
   apply (rule wf_inv_image)
   apply (rule wf_heap_rel)
  apply (unfold heap_rel_def)
  by fastforce

fun vbpl_absval_ty :: "'a vpr_bpl_translation \<Rightarrow> 'a vbpl_absval \<Rightarrow> (tcon_id \<times> bpl_ty list)"
  where
    "vbpl_absval_ty T a = option_fold id (TDummyId T, []) (vbpl_absval_ty_opt T a)"

text\<open> \<^const>\<open>vbpl_absval_ty\<close> is the type interpretation for the Boogie abstract value instantiation 
      used for Viper.\<close>

subsection \<open>Properties of type interpretation\<close>

lemma vbpl_absval_ty_opt_closed:
  assumes "wf_vpr_bpl_translation T" and
          "vbpl_absval_ty_opt T v = Some res"
  shows   "list_all closed (snd res)"
  apply (cases res)
  apply (insert assms)
  by (cases v) (auto split: if_split_asm simp: wf_vpr_bpl_translation_def dest: field_ty_fun_opt_closed[OF assms(1)])

lemma vbpl_absval_ty_closed: 
  assumes "wf_vpr_bpl_translation T"
  shows "closed (tcon_to_bplty (vbpl_absval_ty T v))" 
  by (cases "(vbpl_absval_ty_opt T v)") (auto dest: vbpl_absval_ty_opt_closed[OF assms])

lemma deconstruct_list_length_2:
  assumes "length xs = 2"
  shows "\<exists> x1 x2. xs = [x1,x2]"
proof (cases xs)
  case (Cons y ys)
  show ?thesis
  proof (cases ys)
    case Nil
    then show ?thesis using Cons assms by simp
  next
    case (Cons z zs)
    then show ?thesis using \<open>xs = y # ys\<close> Cons assms by simp
  qed  
qed (insert assms; simp)

lemma ty_inhabitant_well_typed:
  assumes TyInh:"ty_inhabitant tc_enum = Some (n,f)" and
          "n = length ts" and
          Closed:"list_all closed ts"
  shows "vbpl_absval_ty_opt T (f ts) = Some (tcon_id_repr T tc_enum, ts)"
proof (cases tc_enum)
  case TCField
  hence "n = 2" and "f = (\<lambda>ts. AField (DummyField (hd ts) (hd (tl ts))))" (is "(f = ?f)")
    using TyInh \<open>n = length ts\<close>
    by auto
  moreover from \<open>n = 2\<close> \<open>n = length ts\<close> have "ts = [(hd ts), (hd (tl ts))]"
    using deconstruct_list_length_2
    by fastforce
  ultimately show ?thesis
    using Closed TCField
    by (metis (mono_tags, lifting) field_ty_fun_opt.simps(4) list.pred_inject(2) vbpl_absval_ty_opt.simps(2))
qed (insert assms, auto)

theorem is_inhabited_correct:
  assumes Inh:"is_inhabited T tid n" and "n = length ts" and "list_all closed ts"
  shows "\<exists>v. vbpl_absval_ty_opt T v = Some (tid, ts)"
  using assms ty_inhabitant_well_typed
  unfolding is_inhabited_def
  by (metis prod.exhaust_sel)

abbreviation type_of_vbpl_val :: "'a vpr_bpl_translation \<Rightarrow> 'a vbpl_val \<Rightarrow> bpl_ty"
  where "type_of_vbpl_val T \<equiv> type_of_val (vbpl_absval_ty T)"

theorem closed_types_inhabited:
  assumes "closed t"
  shows "\<exists>v. type_of_vbpl_val T v = t"
proof (cases t)
case (TVar x1)
  then show ?thesis using assms by simp
next
  case (TPrim tprim)
  show ?thesis 
    apply (cases tprim) 
     apply (metis TPrim type_of_lit.simps(1) type_of_val.simps(1))
    apply (metis TPrim type_of_lit.simps(2) type_of_val.simps(1))
    done
next
  case (TCon tid ts)
  hence Closed:"list_all closed ts" using \<open>closed t\<close>
    by simp
  show ?thesis
  proof (cases "is_inhabited T tid (length ts)")
    case True
    from is_inhabited_correct[OF True _ Closed] obtain absv where
      TyV:"vbpl_absval_ty_opt T absv = Some (tid, ts)"
      by auto
    show ?thesis
      by (rule exI[where ?x="AbsV absv"]) (auto simp: TyV TCon)         
  next
    case False
    show ?thesis
      apply  (rule exI[where ?x="AbsV (ADummy tid ts)"])
      using False \<open>closed t\<close> TCon
      by auto
  qed
qed

subsection \<open>Functions for map instantiations\<close>

fun arg_types_of_field :: "'a vpr_bpl_translation \<Rightarrow> 'a vb_field \<rightharpoonup> bpl_ty \<times> bpl_ty"
  where
    "arg_types_of_field T f = 
      ( case field_ty_fun_opt T f of
          Some (tid, [t1,t2]) \<Rightarrow> Some (t1,t2)
       | _ \<Rightarrow> None )"

subsubsection \<open>Heap\<close>

text \<open>select function for the heap: readHeap<A, B>(h: HeapType, r: Ref, f: (Field A B)): B\<close>

definition select_heap_aux :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty \<Rightarrow> 'a heap_repr \<Rightarrow> ref \<Rightarrow> 'a vb_field \<Rightarrow> 'a vbpl_val"
  where 
    "select_heap_aux T ret_ty h r f = 
       option_fold id (SOME v. type_of_val (vbpl_absval_ty T) v = ret_ty) (h r f)"

fun select_heap :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "select_heap T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             if (if_Some (arg_types_of_field T f) (\<lambda>res. res  = (t1, t2) \<and> (vbpl_absval_ty_opt T (AHeap h)) = Some ((THeapId T) ,[])))
             then Some (select_heap_aux T t2 h r f)
             else None
         | _ \<Rightarrow> None)"

text \<open>store function for the heap: updHeap<A, B>(h: HeapType, r: Ref, f: (Field A B), y: B): HeapType\<close>

fun store_heap :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where
    "store_heap T ts vs = 
       (case (ts, vs) of 
          ([t1, t2], [AbsV (AHeap h), AbsV (ARef r), AbsV (AField f), v]) \<Rightarrow>
             if (if_Some (arg_types_of_field T f) (\<lambda>res. res = (t1, t2) \<and> (vbpl_absval_ty_opt T (AHeap h)) = Some ((THeapId T) ,[])))
             then Some (AbsV (  AHeap (h( r := (h r)(f \<mapsto> v) ))  ))
             else None
        | _ \<Rightarrow> None)"

subsubsection \<open>Mask\<close>

text \<open>select function for the heap: readMask<A, B>(m: MaskType, r: Ref, f: (Field A B)): Perm\<close>
(* todo need to add reals 
fun select_mask :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "select_mask T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (RealV (m r f))
        | _ \<Rightarrow> None)"
*)

subsubsection \<open>Knownfolded Mask\<close>

text \<open>select function for the knownfolded mask: readPMask<A, B>(pm: PMaskType, r: Ref, f: (Field A B)): bool\<close>

fun select_mask :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "select_mask T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AKnownFoldedMask m), AbsV (ARef r), AbsV (AField f)]) \<Rightarrow> 
             Some (BoolV (m r f))
        | _ \<Rightarrow> None)"

text \<open>store function for the knownfolded mask: updPMask<A, B>(PMaskType: PMaskType, obj: Ref, f_1: (Field A B), y: bool): PMaskType\<close>

fun store_mask :: "'a vpr_bpl_translation \<Rightarrow> bpl_ty list \<Rightarrow> 'a vbpl_val list \<rightharpoonup> 'a vbpl_val"
  where 
    "store_mask T ts vs = 
        (case (ts, vs) of 
           ([t1, t2], [AbsV (AKnownFoldedMask m), AbsV (ARef r), AbsV (AField f), BoolV b]) \<Rightarrow> 
             Some (AbsV (AKnownFoldedMask (m(r := (m r)(f := b)))))
        | _ \<Rightarrow> None)"

end