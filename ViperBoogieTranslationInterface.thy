theory ViperBoogieTranslationInterface
  imports ViperBoogieBasicRel ViperBoogieFunctionInst
begin

subsection \<open>Boogie translation representation instantiation\<close>

type_synonym fun_repr_bpl = "fun_enum_bpl \<Rightarrow> fname"

definition read_heap_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "read_heap_concrete F h rcv f ts \<equiv> FunExp (F FReadHeap) ts [h, rcv, f]"

definition update_heap_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "update_heap_concrete F h rcv f v ts \<equiv> FunExp (F FUpdateHeap) ts [h, rcv, f, v]"

definition read_mask_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "read_mask_concrete F h rcv f ts \<equiv> FunExp (F FReadMask) ts [h, rcv, f]"

definition update_mask_concrete :: "fun_repr_bpl \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> boogie_expr \<Rightarrow> Lang.ty list \<Rightarrow> expr"
  where "update_mask_concrete F m rcv f p ts \<equiv> FunExp (F FUpdateMask) ts [m, rcv, f, p]"

lemma vpr_to_bpl_ty_closed:
  assumes   "wf_ty_repr_bpl TyRep" and
            "vpr_to_bpl_ty TyRep vty = Some t" 
          shows "closed t"
  apply (rule vpr_to_bpl_ty.elims[OF assms(2)])
  using assms(1)
  unfolding wf_ty_repr_bpl_def
  by (auto simp: map_option_case split:option.split_asm) 

lemma instantiate_nil_id: "instantiate [] = id"
  by auto

lemma map_instantiate_nil: "map (instantiate []) ts = ts"
  by (simp add: List.List.list.map_id instantiate_nil_id)


method red_fun_op_bpl_tac1 uses CtxtWf =
    (rule RedFunOp,
     insert CtxtWf,
     unfold ctxt_wf_def fun_interp_vpr_bpl_wf_def,
     blast,
     ((rule RedExpListCons, blast)+, rule RedExpListNil),
     (simp del: vbpl_absval_ty_opt.simps),
     (rule lift_fun_decl_well_typed),
     simp,
     insert field_ty_fun_two_params,
     fastforce)

lemma heap_wf_concrete:
  assumes 
    CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
    TyRepWf: "wf_ty_repr_bpl TyRep"
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

lemma heap_update_wf_concrete:
  assumes 
    CtxtWf: "ctxt_wf Pr TyRep F FunMap ctxt" and
    TyRepWf: "wf_ty_repr_bpl TyRep"
  shows "heap_update_wf TyRep ctxt (update_heap_concrete FunMap)"
  unfolding heap_update_wf_def
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (unfold update_heap_concrete_def)
  apply (red_fun_op_bpl_tac1 CtxtWf: CtxtWf)
    using field_ty_fun_opt_closed_args[OF TyRepWf] 
       apply (fastforce simp: map_instantiate_nil)
      apply (simp only: map_instantiate_nil)    
      apply simp
    using field_ty_fun_two_params field_ty_fun_opt_tcon
        apply (metis fst_eqD length_0_conv length_Suc_conv lessI list.distinct(1) nth_Cons_0 nth_Cons_Suc)
     apply (rule field_ty_fun_two_params)
    apply blast
      apply (simp only: map_instantiate_nil)
      apply simp
    by (blast elim: cons_exp_elim)
    
lemma mask_read_wf_concrete:
  assumes 
    CtxtWf: "ctxt_wf Pr TyRep F fun_repr ctxt" and
    TyRepWf: "wf_ty_repr_bpl TyRep"
  shows "mask_read_wf TyRep ctxt (read_mask_concrete fun_repr)"   
  unfolding mask_read_wf_def
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (unfold read_mask_concrete_def)
  apply (red_fun_op_bpl_tac1 CtxtWf: CtxtWf)
    using field_ty_fun_opt_closed_args[OF TyRepWf] 
       apply (fastforce simp: map_instantiate_nil)
      apply (simp only: map_instantiate_nil)    
      apply simp
    using field_ty_fun_two_params field_ty_fun_opt_tcon
    apply (metis fst_eqD length_0_conv length_Suc_conv lessI list.distinct(1) nth_Cons_0 nth_Cons_Suc)
     apply (rule field_ty_fun_two_params)
    apply blast
     apply (simp only: map_instantiate_nil)
    apply simp
    by (blast elim: cons_exp_elim)

lemma mask_update_wf_concrete:
  assumes 
    CtxtWf: "ctxt_wf Pr TyRep F fun_repr ctxt" and
    TyRepWf: "wf_ty_repr_bpl TyRep"
  shows "mask_update_wf TyRep ctxt (update_mask_concrete fun_repr)"  
  unfolding mask_update_wf_def
  apply (rule allI)+
  apply (rule conjI)
   apply (rule impI)
   apply (unfold update_mask_concrete_def)
   apply (red_fun_op_bpl_tac1 CtxtWf: CtxtWf)
    using field_ty_fun_opt_closed_args[OF TyRepWf] 
       apply (fastforce simp: map_instantiate_nil)
      apply (simp only: map_instantiate_nil)    
      apply simp
    using field_ty_fun_two_params field_ty_fun_opt_tcon
    apply (metis fst_eqD length_0_conv length_Suc_conv lessI list.distinct(1) nth_Cons_0 nth_Cons_Suc)
     apply (rule field_ty_fun_two_params)
    apply blast
     apply (simp only: map_instantiate_nil)
    apply simp
    by (blast elim: cons_exp_elim)

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
  | "fun_repr_concrete FUpdateHeap = ''updHeap''"
  | "fun_repr_concrete FReadMask = ''readMask''"
  | "fun_repr_concrete FUpdateMask = ''updMask''"
  | "fun_repr_concrete FReadKnownFoldedMask = ''readPMask''"
  | "fun_repr_concrete FUpdateKnownFoldedMask = ''updPMask''"
  | "fun_repr_concrete FGoodState = ''state''"
  | "fun_repr_concrete FGoodMask = ''GoodMask''"
  | "fun_repr_concrete FHasPerm = ''HasDirectPerm''"
  | "fun_repr_concrete FIdenticalOnKnownLocs = ''IdenticalOnKnownLocations''"  

(* potentially useful to prove injectivity:
lemma "card {''readHeap'', ''updHeap'', ''readMask'', ''updMask'', ''state'', ''HasDirectPerm'', ''IdenticalOnKnownLocations''} = 7"
  by simp
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
    "tcon_enum_to_id TCRef = ''Ref''"
  | "tcon_enum_to_id TCField = ''Field''"
  | "tcon_enum_to_id TCHeap = ''HeapType''"
  | "tcon_enum_to_id TCMask = ''MaskType''"
  | "tcon_enum_to_id TCKnownFoldedMask = ''PMaskType''"
  | "tcon_enum_to_id TCFrameFragment = ''FrameFragment''"
  | "tcon_enum_to_id TCNormalField = ''NormalField''"

text \<open>Type representation instantiation without predicates and domains\<close>

definition ty_repr_basic :: "('a \<Rightarrow> abs_type) \<Rightarrow> 'a ty_repr_bpl"
  where "ty_repr_basic A = 
     \<lparr>  tcon_id_repr = tcon_enum_to_id,
        pred_snap_field_type = (\<lambda>_. None),
        pred_knownfolded_field_type = (\<lambda>_. None),
        domain_translation = (\<lambda>_. None),
        domain_type = A \<rparr>"

lemma wf_ty_repr_basic: "wf_ty_repr_bpl (ty_repr_basic A)"
  sorry (* TODO *)
(*
  unfolding wf_ty_repr_bpl_def
  apply (intro conjI)
    apply clarify
  using ty_repr_basic_def
    apply (metis option.discI ty_repr_bpl.select_convs(4))
  using ty_repr_basic_def
   apply (metis option.discI ty_repr_bpl.select_convs(2))
  using ty_repr_basic_def
   apply (metis option.discI ty_repr_bpl.select_convs(3))
  apply (unfold ty_repr_basic_def)
  apply simp
  done
*)

lemma type_interp_rel_wf_vbpl_basic: "type_interp_rel_wf A_vpr (vbpl_absval_ty (ty_repr_basic A_vpr)) (ty_repr_basic A_vpr)"
  unfolding ty_repr_basic_def
  by (simp add: type_interp_rel_wf_vbpl_no_domains)

subsection \<open>Helper definitions\<close>

text \<open>Since currently Carbon always generates the same constants and global variables in the same order,
one can use the following variable name mapping for the constants.\<close>

fun const_repr_basic :: "boogie_const \<Rightarrow> vname"
  where 
    "const_repr_basic CNoPerm = 3"
  | "const_repr_basic CWritePerm = 4"
  | "const_repr_basic CNull = 0"
  | "const_repr_basic CZeroMask = 1"

lemma inj_const_repr_basic: "inj const_repr_basic"
  unfolding inj_def
  apply (rule allI)+
  apply (rule impI)
  apply (rename_tac c1 c2)
  by (case_tac c1; case_tac c2; simp)

lemma const_repr_basic_bound: "const_repr_basic c = x \<Longrightarrow> x \<le> 4"
  by (cases c) auto

lemma const_repr_basic_bound_2: "\<forall>x \<in> range const_repr_basic. x \<ge> 0 \<and> x \<le> 4"
  using const_repr_basic_bound
  by fastforce  

subsubsection \<open> \<^const>\<open>const_repr_basic\<close> helper lemmas \<close>

lemma lookup_no_perm_const: 
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 3 = Some (boogie_const_val CNoPerm)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

lemma lookup_write_perm_const: 
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 4 = Some (boogie_const_val CWritePerm)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

lemma lookup_null_const:
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 0 = Some (boogie_const_val CNull)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

lemma lookup_zero_mask_const: 
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 1 = Some (boogie_const_val CZeroMask)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

end