theory ViperBoogieTranslationInterface
  imports ViperBoogieBasicRel ViperBoogieFunctionInst
begin

text \<open>concrete function declarations\<close>
definition fdecls
  where
    "fdecls  = [(''state'',0,[((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool)),(''succHeap'',0,[((TCon ''HeapType'') []),((TCon ''HeapType'') [])],(TPrim TBool)),(''succHeapTrans'',0,[((TCon ''HeapType'') []),((TCon ''HeapType'') [])],(TPrim TBool)),(''IdenticalOnKnownLocations'',0,[((TCon ''HeapType'') []),((TCon ''HeapType'') []),((TCon ''MaskType'') [])],(TPrim TBool)),(''readHeap'',2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TVar 1)),(''updHeap'',2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TVar 1)],((TCon ''HeapType'') [])),(''IsPredicateField'',2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''IsWandField'',2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''getPredicateId'',2,[((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TInt)),(''PredicateMaskField'',1,[((TCon ''Field'') [(TVar 0),((TCon ''FrameType'') [])])],((TCon ''Field'') [(TVar 0),((TCon ''PMaskType'') [])])),(''WandMaskField'',1,[((TCon ''Field'') [(TVar 0),((TCon ''FrameType'') [])])],((TCon ''Field'') [(TVar 0),((TCon ''PMaskType'') [])])),(''Perm'',0,[(TPrim TReal),(TPrim TReal)],(TPrim TReal)),(''readMask'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TReal)),(''updMask'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TPrim TReal)],((TCon ''MaskType'') [])),(''readPMask'',2,[((TCon ''PMaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''updPMask'',2,[((TCon ''PMaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TPrim TBool)],((TCon ''PMaskType'') [])),(''GoodMask'',0,[((TCon ''MaskType'') [])],(TPrim TBool)),(''HasDirectPerm'',2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TBool)),(''sumMask'',0,[((TCon ''MaskType'') []),((TCon ''MaskType'') []),((TCon ''MaskType'') [])],(TPrim TBool)),(''FrameFragment'',1,[(TVar 0)],((TCon ''FrameType'') [])),(''ConditionalFrame'',0,[(TPrim TReal),((TCon ''FrameType'') [])],((TCon ''FrameType'') [])),(''dummyFunction'',1,[(TVar 0)],(TPrim TBool)),(''CombineFrames'',0,[((TCon ''FrameType'') []),((TCon ''FrameType'') [])],((TCon ''FrameType'') [])),(''InsidePredicate'',2,[((TCon ''Field'') [(TVar 0),((TCon ''FrameType'') [])]),((TCon ''FrameType'') []),((TCon ''Field'') [(TVar 1),((TCon ''FrameType'') [])]),((TCon ''FrameType'') [])],(TPrim TBool))]"

lemma mfun_readHeap:
shows "((map_of fdecls ''readHeap'') = (Some (2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TVar 1))))"
by (simp add:fdecls_def)

lemma mfun_updHeap:
shows "((map_of fdecls ''updHeap'') = (Some (2,[((TCon ''HeapType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TVar 1)],((TCon ''HeapType'') []))))"
by (simp add:fdecls_def)

lemma mfun_readMask:
shows "((map_of fdecls ''readMask'') = (Some (2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)])],(TPrim TReal))))"
by (simp add:fdecls_def)

lemma mfun_updMask:
shows "((map_of fdecls ''updMask'') = (Some (2,[((TCon ''MaskType'') []),((TCon ''Ref'') []),((TCon ''Field'') [(TVar 0),(TVar 1)]),(TPrim TReal)],((TCon ''MaskType'') []))))"
  by (simp add:fdecls_def)


subsection \<open>Boogie translation representation instantiation\<close>

type_synonym fun_repr_bpl = "fun_enum_bpl \<Rightarrow> fname"

definition read_heap_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "read_heap_concrete F h rcv f ts \<equiv> FunExp (F FReadHeap) ts [h, rcv, f]"

definition read_mask_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "read_mask_concrete F h rcv f ts \<equiv> FunExp (F FReadMask) ts [h, rcv, f]"

lemma field_ty_fun_two_params:
  assumes "field_ty_fun_opt T f = Some (field_tcon, ty_args)"
  obtains t1 t2
  where "ty_args = [t1, t2]"
  apply (insert assms)
  apply (cases f)
     apply fastforce+
  apply simp
  by (metis Pair_inject option.distinct(1) option.inject)

lemma field_ty_fun_opt_num_args:
     "field_ty_fun_opt T f = Some res \<Longrightarrow> length (snd res) = 2"
  apply (erule field_ty_fun_opt.elims)
     apply (simp_all add: map_option_case split: option.split_asm split: if_split_asm)
  done

lemma vpr_to_bpl_ty_closed:
  assumes   "wf_ty_repr_bpl TyRep" and
            "vpr_to_bpl_ty TyRep vty = Some t" 
          shows "closed t"
  apply (rule vpr_to_bpl_ty.elims[OF assms(2)])
  using assms(1)
  unfolding wf_ty_repr_bpl_def
  by (auto simp: map_option_case split:option.split_asm)  

lemma field_ty_fun_opt_closed_args: 
  assumes "wf_ty_repr_bpl TyRep" and
          "field_ty_fun_opt TyRep f = Some res"
  shows  "list_all closed (snd res)"
  apply (rule field_ty_fun_opt.elims[OF assms(2)])
  using assms(1) wf_ty_repr_bpl_def
       apply (simp_all add: map_option_case vpr_to_bpl_ty_closed split: option.split_asm split: if_split_asm)
   apply blast+
  done

lemma field_ty_fun_opt_tcon:
  assumes "field_ty_fun_opt TyRep f = Some res"
  shows "fst res = TFieldId TyRep"
  using assms
  by (rule field_ty_fun_opt.elims)
     (simp_all add: map_option_case vpr_to_bpl_ty_closed split: option.split_asm split: if_split_asm)     

lemma instantiate_nil_id: "instantiate [] = id"
  by auto

lemma map_instantiate_nil: "map (instantiate []) ts = ts"
  by (simp add: List.List.list.map_id instantiate_nil_id)

lemma heap_wf_concrete:
  assumes 
    TyRepWf: "wf_ty_repr_bpl TyRep" and
    CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" 
  shows "heap_read_wf TyRep ctxt (read_heap_concrete FunMap)"
  unfolding heap_read_wf_def
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (unfold read_heap_concrete_def)
  apply (rule RedFunOp)
       using CtxtWf
    unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
       apply blast
      apply ((rule RedExpListCons, blast)+, rule RedExpListNil)
     apply (simp del: vbpl_absval_ty_opt.simps)
     apply (rule lift_fun_decl_well_typed)
         apply simp       
    using field_ty_fun_two_params
        apply fastforce    
    using field_ty_fun_opt_closed_args[OF TyRepWf] 
       apply (fastforce simp: map_instantiate_nil)
      apply (simp only: map_instantiate_nil)    
      apply simp
    using field_ty_fun_two_params field_ty_fun_opt_tcon
    apply (metis fst_eqD length_0_conv length_Suc_conv lessI list.distinct(1) nth_Cons_0 nth_Cons_Suc)
     apply (rule field_ty_fun_two_params)
    apply blast
     apply (simp only: map_instantiate_nil)
  by (auto elim: cons_exp_elim simp: select_heap_aux_def)

lemma mask_read_wf_concrete:
  assumes 
    TyRepWf: "wf_ty_repr_bpl TyRep" and
    CtxtWf: "ctxt_wf Pr TyRep F fun_repr ctxt" 
  shows "mask_read_wf TyRep ctxt (read_mask_concrete fun_repr)"   
  unfolding mask_read_wf_def
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (unfold read_mask_concrete_def)
  apply (rule RedFunOp)
       using CtxtWf
    unfolding ctxt_wf_def fun_interp_vpr_bpl_wf_def
       apply blast
      apply ((rule RedExpListCons, blast)+, rule RedExpListNil)
     apply (simp del: vbpl_absval_ty_opt.simps)
     apply (rule lift_fun_decl_well_typed)
         apply simp       
    using field_ty_fun_two_params
        apply fastforce    
    using field_ty_fun_opt_closed_args[OF TyRepWf] 
       apply (fastforce simp: map_instantiate_nil)
      apply (simp only: map_instantiate_nil)    
      apply simp
    using field_ty_fun_two_params field_ty_fun_opt_tcon
    apply (metis fst_eqD length_0_conv length_Suc_conv lessI list.distinct(1) nth_Cons_0 nth_Cons_Suc)
     apply (rule field_ty_fun_two_params)
    apply blast
     apply (simp only: map_instantiate_nil)
  by (auto elim: cons_exp_elim)

subsection \<open>Translation interface\<close>

text \<open>Showcase a concrete translation example\<close>

fun field_translation_example :: "ViperLang.function_ident \<rightharpoonup> Lang.vname"
  where "field_translation_example _ = None"

fun fun_translation_example :: "ViperLang.function_ident \<rightharpoonup> Lang.fname"
  where "fun_translation_example _ = None"

definition var_translation_example_list :: "(ViperLang.var \<times> Lang.vname) list"
  where 
    "var_translation_example_list = [(0,5)]"

definition var_translation_example :: "ViperLang.var \<rightharpoonup> Lang.vname"
  where
    "var_translation_example \<equiv> map_of var_translation_example_list"

fun fun_repr_concrete :: fun_repr_bpl 
  where 
    "fun_repr_concrete FReadHeap = ''readHeap''"
  | "fun_repr_concrete FReadMask = ''readMask''"
  | "fun_repr_concrete FGoodState = ''state''"
  | "fun_repr_concrete FHasPerm = ''hasDirectPerm''"

(*
definition tr_vpr_bpl_example :: "fun_repr_bpl \<Rightarrow> tr_vpr_bpl"
  where "tr_vpr_bpl_example F \<equiv>
      \<lparr> heap_var = 0,
       mask_var = 1,
       mask_read = (read_mask_concrete F),
      heap_read = (read_heap_concrete F),
      field_translation = field_translation_example,
      fun_translation = fun_translation_example,
      var_translation = var_translation_example \<rparr>"
*)

method ctxt_wf_fun_tac for f :: fun_enum_bpl = (unfold ctxt_wf_def, erule allE[where ?x=f], simp)

(* TODO
lemma ctxt_wf_read_heap:
   "ctxt_wf ctxt ty_repr F \<Longrightarrow> fun_interp ctxt (F FReadHeap) = Some (select_heap ty_repr)"
  by (ctxt_wf_fun_tac FReadHeap)

lemma ctxt_wf_read_mask:
   "ctxt_wf ctxt ty_repr F \<Longrightarrow> fun_interp ctxt (F FReadMask) = Some (select_mask ty_repr)"
  by (ctxt_wf_fun_tac FReadMask)
*)

(*
lemma tr_wf_concrete: 
  assumes CtxtWf: "ctxt_wf ctxt ty_repr F"
  shows "tr_wf Pr \<Delta> ctxt ty_repr (tr_vpr_bpl_example F)"
  unfolding tr_wf_def tr_vpr_bpl_example_def
  apply (intro conjI)
    apply (simp add: fun_interp_rel_def)  
   apply (simp, rule heap_read_wf_concrete)
   apply (rule ctxt_wf_read_heap[OF CtxtWf])
   apply (simp, rule mask_read_wf_concrete)
  apply (rule ctxt_wf_read_mask[OF CtxtWf])
  done
*)

subsection \<open>Boogie Type representation instantiation\<close>

fun tcon_enum_to_id :: "tcon_enum \<Rightarrow> tcon_id"
  where
    "tcon_enum_to_id TCRef = ''ref''"
  | "tcon_enum_to_id TCField = ''Field''"
  | "tcon_enum_to_id TCHeap = ''HeapType''"
  | "tcon_enum_to_id TCMask = ''MaskType''"
  | "tcon_enum_to_id TCKnownFoldedMask = ''PMaskType''"
  | "tcon_enum_to_id TCFrameFragment = ''FrameFragment''"
  | "tcon_enum_to_id TCNormalField = ''NormalField''"

text \<open>Type representation instantiation without predicates and domains\<close>

definition ty_repr_basic :: "'a ty_repr_bpl"
  where "ty_repr_basic = 
     \<lparr>  tcon_id_repr = tcon_enum_to_id,
        pred_snap_field_type = (\<lambda>_. None),
        pred_knownfolded_field_type = (\<lambda>_. None),
        domain_translation = (\<lambda>_. None),
        domain_type = (\<lambda>_. ''placeholder'')  \<rparr>"

lemma wf_ty_repr_basic: "wf_ty_repr_bpl ty_repr_basic"
  unfolding wf_ty_repr_bpl_def
  apply (intro conjI)
    apply clarify
  using ty_repr_basic_def
    apply (metis option.discI ty_repr_bpl.select_convs(4))
  using ty_repr_basic_def
   apply (metis option.discI ty_repr_bpl.select_convs(2))
  using ty_repr_basic_def
  apply (metis option.discI ty_repr_bpl.select_convs(3))
  done


subsection \<open>Helper definitions\<close>

text \<open>Since currently Carbon always generates the same constants and global variables in the same order,
one can use the following variable name mapping for the constants.\<close>

fun const_repr_basic :: "boogie_const \<Rightarrow> vname"
  where 
    "const_repr_basic CNoPerm = 3"
  | "const_repr_basic CWritePerm = 4"
  | "const_repr_basic CNull = 0"
  | "const_repr_basic CZeroMask = 1"


end