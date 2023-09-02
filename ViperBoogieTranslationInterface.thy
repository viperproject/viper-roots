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

lemma list_all_comp:
  assumes "list_all P xs" and
          "\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> (Q \<circ> P) x"
        shows "list_all (Q \<circ> P) xs"
  using assms
  using list.pred_mono_strong by blast


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
    using list_all_comp[OF field_ty_fun_opt_closed_args[OF TyRepWf]] closed_instantiate 
       apply (metis TyRepWf closed.simps(3) field_ty_fun_opt_closed instantiate.simps(3) snd_conv)
          apply (rule field_ty_fun_two_params)
       apply blast
      apply (insert field_ty_fun_opt_closed_args[OF TyRepWf])
      apply simp
    using closed_instantiate
      apply (metis field_ty_fun_opt_tcon fst_conv list_all_simps(1) snd_eqD)

      apply (rule field_ty_fun_two_params)
       apply blast    
    by (fastforce elim: cons_exp_elim simp: select_heap_aux_def)+

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
  using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] 
     apply (metis TyRepWf case_prod_conv field_ty_fun_opt_closed_args snd_def)
          apply (rule field_ty_fun_two_params)
       apply blast
      apply (insert field_ty_fun_opt_closed_args[OF TyRepWf])
      apply simp
    using closed_instantiate
      apply (metis field_ty_fun_opt_tcon fst_conv list_all_simps(1) snd_eqD)
    
     apply (rule field_ty_fun_two_params)
    apply blast
     apply simp
  apply simp
    using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] field_ty_fun_two_params field_ty_fun_opt_tcon
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
   using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] 
     apply (metis TyRepWf case_prod_conv field_ty_fun_opt_closed_args snd_def)
          apply (rule field_ty_fun_two_params)
       apply blast
      apply (insert field_ty_fun_opt_closed_args[OF TyRepWf])
      apply simp
    using closed_instantiate
      apply (metis field_ty_fun_opt_tcon fst_conv list_all_simps(1) snd_eqD)   
     apply (rule field_ty_fun_two_params)
    apply blast
     apply simp
  apply simp
    using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] field_ty_fun_two_params field_ty_fun_opt_tcon
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
   using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] 
     apply (metis TyRepWf case_prod_conv field_ty_fun_opt_closed_args snd_def)
          apply (rule field_ty_fun_two_params)
       apply blast
      apply (insert field_ty_fun_opt_closed_args[OF TyRepWf])
      apply simp
    using closed_instantiate
      apply (metis field_ty_fun_opt_tcon fst_conv list_all_simps(1) snd_eqD)   
     apply (rule field_ty_fun_two_params)
    apply blast
     apply simp
  apply simp
    using closed_map_instantiate[OF field_ty_fun_opt_closed_args[OF TyRepWf]] field_ty_fun_two_params field_ty_fun_opt_tcon
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
  | "fun_repr_concrete FIsPredicateField = ''IsPredicateField''"
  | "fun_repr_concrete FIsWandField = ''IsWandField''"

lemma fun_repr_concrete_inj: "inj fun_repr_concrete"
  unfolding inj_def
proof clarify
  fix x y
  show "fun_repr_concrete x = fun_repr_concrete y \<Longrightarrow> x = y"
    by (cases x; cases y; simp)
qed

subsection \<open>Boogie Type representation instantiation\<close>

fun tcon_enum_to_id :: "tcon_enum \<Rightarrow> tcon_id"
  where
    "tcon_enum_to_id TCRef = ''Ref''"
  | "tcon_enum_to_id TCField = ''Field''"
  | "tcon_enum_to_id TCHeap = ''HeapType''"
  | "tcon_enum_to_id TCMask = ''MaskType''"
  | "tcon_enum_to_id TCKnownFoldedMask = ''PMaskType''"
  | "tcon_enum_to_id TCFrameFragment = ''FrameType''"
  | "tcon_enum_to_id TCNormalField = ''NormalField''"

lemma inj_tcon_enum_to_id: "inj tcon_enum_to_id"
  unfolding inj_def
  apply (rule allI | rule impI)+
  apply (rename_tac a b)
  by (case_tac a; case_tac b; simp)

text \<open>Type representation instantiation without predicates and domains\<close>

definition ty_repr_basic :: "('a \<Rightarrow> abs_type) \<Rightarrow> 'a ty_repr_bpl"
  where "ty_repr_basic A = 
     \<lparr>  tcon_id_repr = tcon_enum_to_id,
        pred_snap_field_type = (\<lambda>_. None),
        pred_knownfolded_field_type = (\<lambda>_. None),
        domain_translation = (\<lambda>_. None),
        domain_type = A \<rparr>"

lemma wf_ty_repr_basic: "wf_ty_repr_bpl (ty_repr_basic A)"
  unfolding wf_ty_repr_bpl_def ty_repr_basic_def
  by (simp_all add: inj_tcon_enum_to_id)

subsection \<open>Helper inversion lemmas\<close>

text \<open>Here, we prove inversion lemmas on \<^const>\<open>type_of_vbpl_val\<close> in terms of specific equalities,
      where the type representation is instantiated to \<^const>\<open>ty_repr_basic\<close>.
      General versions of inversion lemmas are already proved in a different theory via implications. 
      For some generated proofs, it is useful to phrase the inversion as an equality (where one direction is trivial)
      and where the type representation is instantiated.
\<close>

lemma type_interp_rel_wf_vbpl_basic: "type_interp_rel_wf A_vpr (vbpl_absval_ty (ty_repr_basic A_vpr)) (ty_repr_basic A_vpr)"
  unfolding ty_repr_basic_def
  by (simp add: type_interp_rel_wf_vbpl_no_domains)

lemma mask_inversion_eq_type_of_vbpl_val:
  assumes "wf_ty_repr_bpl TyRep"
  shows "type_of_vbpl_val TyRep v = TConSingle (TMaskId TyRep) = (\<exists>m. v = AbsV (AMask m) \<and> (id type_of_vbpl_val) TyRep v = TConSingle (TMaskId TyRep))"
  using mask_inversion_type_of_vbpl_val[OF assms]
  by auto
  
lemma mask_inversion_eq_type_of_vbpl_val_concrete: 
  "type_of_vbpl_val (ty_repr_basic A) v = TConSingle ''MaskType'' = (\<exists>m. v = AbsV (AMask m) \<and> (id type_of_vbpl_val) (ty_repr_basic A) v = TConSingle ''MaskType'')"
  using mask_inversion_eq_type_of_vbpl_val[OF wf_ty_repr_basic] 
  by (auto simp: ty_repr_basic_def)

lemma heap_inversion_eq_type_of_vbpl_val:
  assumes "wf_ty_repr_bpl TyRep"
  shows "type_of_vbpl_val TyRep v = TConSingle (THeapId TyRep) = (\<exists>h. v = AbsV (AHeap h) \<and> (id type_of_vbpl_val) TyRep v = TConSingle (THeapId TyRep))"
  using heap_inversion_type_of_vbpl_val[OF assms]  
  by auto

lemma heap_inversion_eq_type_of_vbpl_val_concrete:
  "type_of_vbpl_val (ty_repr_basic A) v = TConSingle ''HeapType'' = (\<exists>h. v = AbsV (AHeap h) \<and> (id type_of_vbpl_val) (ty_repr_basic A) v = TConSingle ''HeapType'')"
  using heap_inversion_eq_type_of_vbpl_val[OF wf_ty_repr_basic]
  by (auto simp: ty_repr_basic_def)

lemma ref_inversion_eq_type_of_vbpl_val:
  assumes "wf_ty_repr_bpl TyRep"
  shows "type_of_vbpl_val TyRep v = TConSingle (TRefId TyRep) = (\<exists>r. v = AbsV (ARef r) \<and> (id type_of_vbpl_val) TyRep v = TConSingle (TRefId TyRep))"
  using ref_inversion_type_of_vbpl_val[OF assms]
  by auto

lemma ref_inversion_eq_type_of_vbpl_val_concrete:
  "type_of_vbpl_val (ty_repr_basic A) v = TCon ''Ref'' [] = (\<exists>r. v = AbsV (ARef r) \<and> (id type_of_vbpl_val) (ty_repr_basic A) v = TCon ''Ref'' [])"
  using ref_inversion_eq_type_of_vbpl_val[OF wf_ty_repr_basic]
  by (auto simp add: ty_repr_basic_def)

lemma field_inversion_eq_type_of_vbpl_val:
  assumes "wf_ty_repr_bpl TyRep"
  shows "type_of_vbpl_val TyRep v = TCon (TFieldId TyRep) [t1,t2] = (\<exists>f. v = AbsV (AField f) \<and> (id type_of_vbpl_val) TyRep v = TCon (TFieldId TyRep) [t1,t2])"
  using field_inversion_type_of_vbpl_val_2[OF assms]
  by auto

lemma field_inversion_eq_type_of_vbpl_val_concrete:
  "(type_of_vbpl_val (ty_repr_basic A) v = TCon ''Field'' [t1, t2]) = (\<exists>f. v = AbsV (AField f) \<and> (id type_of_vbpl_val) (ty_repr_basic A) v = TCon ''Field'' [t1, t2])" 
proof -
  have *: "TFieldId (ty_repr_basic A) = ''Field''"
    by (simp add: ty_repr_basic_def)

  show ?thesis
    using field_inversion_eq_type_of_vbpl_val[where ?TyRep = "ty_repr_basic A", OF wf_ty_repr_basic]    
    unfolding *
    by blast
qed    

lemma realv_inversion_type_of_vbpl_val:
  "type_of_val A v = TPrim TReal = (\<exists>i. v = RealV i \<and> (id type_of_val) A v = TPrim TReal)"
  using VCExprHelper.treal_realv
  by auto

lemmas inversion_type_of_vbpl_val_equalities =
 heap_inversion_eq_type_of_vbpl_val_concrete
 mask_inversion_eq_type_of_vbpl_val_concrete
 ref_inversion_eq_type_of_vbpl_val_concrete
 field_inversion_eq_type_of_vbpl_val_concrete

subsection \<open>Helper definitions\<close>

text \<open>Since currently Carbon always generates the same constants and global variables in the same order,
one can use the following variable name mapping for the constants.\<close>

\<comment>\<open>TODO: ideally the constants representation is generated by the verifier instead of hard-coded to 
be more robust to changes in the verifier\<close>

fun const_repr_basic :: "boogie_const \<Rightarrow> vname"
  where 
    "const_repr_basic CNoPerm = 3"
  | "const_repr_basic CWritePerm = 4"
  | "const_repr_basic CNull = 0"
  | "const_repr_basic CZeroMask = 1"
  | "const_repr_basic CKnownFoldedZeroMask = 2"
  | "const_repr_basic CEmptyFrame = 5"

lemma inj_const_repr_basic: "inj const_repr_basic"
  unfolding inj_def
  apply (rule allI)+
  apply (rule impI)
  apply (rename_tac c1 c2)
  by (case_tac c1; case_tac c2; simp)

lemma const_repr_basic_bound: "const_repr_basic c = x \<Longrightarrow> x \<le> 5"
  by (cases c) auto

lemma range_const_repr_basic: "range (const_repr_basic) = {0,1,2,3,4,5}"
proof -   
  have "UNIV = {CNoPerm, CWritePerm, CNull, CZeroMask, CKnownFoldedZeroMask, CEmptyFrame}"
    apply standard
     apply standard
     apply (case_tac x; simp)
    apply standard
    apply (case_tac x; simp)
    done

  show ?thesis
    apply (subst \<open>UNIV = _\<close>)
    apply simp
    by blast
qed

lemma const_repr_basic_bound_2: "\<forall>x \<in> range const_repr_basic. x \<ge> 0 \<and> x \<le> 5"
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

lemma lookup_known_folded_zero_mask_const: 
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 2 = Some (boogie_const_val CKnownFoldedZeroMask)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

lemma lookup_empty_frame_const: 
  assumes "boogie_const_rel const_repr_basic \<Lambda> ns"
  shows "lookup_var \<Lambda> ns 5 = Some (boogie_const_val CEmptyFrame)"
  by (rule boogie_const_rel_lookup_2[OF assms]) auto

lemmas lookup_boogie_const_concrete_lemmas =
  lookup_no_perm_const
  lookup_write_perm_const
  lookup_null_const
  lookup_zero_mask_const
  lookup_known_folded_zero_mask_const
  lookup_empty_frame_const

end