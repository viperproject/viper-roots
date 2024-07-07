theory ViperBoogieRelUtil
  imports ViperBoogieTranslationInterface ExpRel Simulation
begin

subsection \<open>Temporary variable management\<close>

lemma store_temporary_var:
  assumes
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" and
         DisjAux: "temp_var \<notin> state_rel0_disj_vars Tr AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some \<tau>_bpl" and
         RedRhs:  "red_expr_bpl ctxt e ns v" and
         TyValBpl:  "type_of_val (type_interp ctxt) v = \<tau>_bpl"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq v)) ctxt \<omega>def \<omega> ns')"
           (is "\<exists>ns'. ?red ns' \<and> ?R' \<omega> ns'")
proof (rule exI, rule conjI)
  let ?ns' = "update_var (var_context ctxt) ns temp_var v"

  have StateRel2: "state_rel Pr StateCons TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq v)) ctxt \<omega>def \<omega> ?ns'"
    using state_rel_new_auxvar[OF \<open>?R \<omega> ns\<close> DisjAux _ TyInterp LookupTyTemp] TyValBpl
    unfolding pred_eq_def
    by simp    

  show "?red ?ns'"
    apply (rule red_ast_bpl_one_simple_cmd)
    by (fastforce intro!: RedAssign LookupTyTemp RedRhs simp:TyValBpl EmptyRtype)

  show "?R' \<omega> ?ns'"
    using StateRel2
    by blast
qed

lemma setup_oldh:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns")
      and TyInterp: "ty_interp ctxt = vbpl_absval_ty TyRep"
      and EmptyRType: "rtype_interp ctxt = []"
      and DisjAux: "oldH \<notin> state_rel0_disj_vars Tr AuxPred"
      and traceDefined: "get_trace_total \<omega> lbl = Some \<phi> \<and> get_total_full \<omega> = \<phi>"
      and lblNotPreviouslyDefined: "fst (label_hm_translation Tr) lbl = None"
      and oldMType: "lookup_var_ty (var_context ctxt) oldH = Some (TConSingle (THeapId TyRep))"
      and "f = ((fst (label_hm_translation Tr))(lbl \<mapsto> oldH), (snd (label_hm_translation Tr)))"
      and "Tr' = Tr \<lparr> label_hm_translation := f \<rparr>"
      and "h = heap_var Tr"
    shows "\<exists> ns'. red_ast_bpl P ctxt
                  (((BigBlock name ((Lang.Assign oldH (Var h)) # cs) s tr), cont), Normal ns)
                  ((BigBlock name cs s tr, cont), Normal ns') \<and>
                    (state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ns')"
proof -
  (* Define some shorthand *)
  let ?\<Lambda> = "var_context ctxt"
  let ?A = "type_interp ctxt"
  let ?FieldTr = "field_translation Tr"
  let ?FieldTr' = "field_translation Tr'"
  let ?heapVar = "heap_var Tr"
  let ?maskVar = "mask_var Tr"
  let ?\<omega>_trace_total = "get_trace_total \<omega>"
  let ?Tr_heap_labels = "fst (label_hm_translation Tr)"
  let ?Tr_mask_labels = "snd (label_hm_translation Tr)"
  let ?Tr'_heap_labels = "fst (label_hm_translation Tr')"
  let ?Tr'_mask_labels = "snd (label_hm_translation Tr')"
  (* Extract the heap value from the existing StateRel *)
  from StateRel obtain heapValue where
    heapVarValue: "lookup_var ?\<Lambda> ns ?heapVar = Some (AbsV (AHeap heapValue))" and
    heapVarType: "lookup_var_ty ?\<Lambda> ?heapVar = Some (TConSingle (THeapId TyRep))"
    unfolding state_rel_def state_rel0_def heap_var_rel_def
    by fast
 from StateRel obtain maskValue where
    maskVarValue: "lookup_var ?\<Lambda> ns ?maskVar = Some (AbsV (AMask maskValue))" and
    maskVarType: "lookup_var_ty ?\<Lambda> ?maskVar = Some (TConSingle (TMaskId TyRep))"
    unfolding state_rel_def state_rel0_def mask_var_rel_def
    by fast

  (* The new state is the existing state, with oldHeap set to the heap value *)
  let ?ns' = "update_var ?\<Lambda> ns oldH (AbsV (AHeap heapValue))"

  show ?thesis
  proof (intro exI, intro conjI)
    show "red_ast_bpl P ctxt ((BigBlock name (Assign oldH (expr.Var h) # cs) s tr, cont), Normal ns)
       ((BigBlock name cs s tr, cont), Normal ?ns')"
    proof (rule red_ast_bpl_one_assign)
      show "lookup_var_ty (var_context ctxt) oldH = Some (TConSingle (THeapId TyRep))"
        by (simp add: oldMType)
      show "red_expr_bpl ctxt (expr.Var h) ns (AbsV (AHeap heapValue))"
        by (simp add: \<open>h = _\<close> heapVarValue red_expr_red_exprs.RedVar)
      show "type_of_val (type_interp ctxt) (AbsV (AHeap heapValue)) = instantiate (rtype_interp ctxt) (TConSingle (THeapId TyRep))"
        by (metis EmptyRType StateRel heapVarType heapVarValue option.sel state_rel_state_well_typed state_well_typed_lookup)
    qed

    show "state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ?ns'"
      unfolding state_rel_def state_rel0_def
    proof (intro conjI)
      show "valid_heap_mask (get_mh_total_full \<omega>def)"
        using StateRel state_rel_wf_mask_def_simple by blast
      show "valid_heap_mask (get_mh_total_full \<omega>)"
        using StateRel state_rel_wf_mask_simple by blast
      show "consistent_state_rel_opt (state_rel_opt Tr') \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>"
        by (metis StateRel \<open>Tr' = _\<close> state_rel_consistent tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9))
      show "type_interp ctxt = vbpl_absval_ty TyRep"
        using StateRel state_rel_type_interp by blast
      show "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr') (get_store_total \<omega>) ?ns'"
        by (metis (no_types, lifting) DisjAux StateRel Sup_insert UnCI \<open>Tr' = _\<close> list.simps(15) state_rel_store_rel store_rel_stable tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      show "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
      proof -
        have disjoint_list_Tr: "disjoint_list (state_rel0_disj_list Tr AuxPred)"
          using StateRel state_rel_disjoint
          by fast
        let ?xs = "[{heap_var Tr, heap_var_def Tr},
                    {mask_var Tr, mask_var_def Tr},
                    (ran (var_translation Tr)), 
                    (ran (field_translation Tr)),
                    (range (const_repr Tr)),
                    dom AuxPred]"
        let ?M =  "vars_label_hm_tr (label_hm_translation Tr)"
        let ?ys = "[]"
        have disjointWithOldH: "disjoint_list (?xs @ (?M \<union> {oldH}) # ?ys)"
        proof (rule disjoint_list_add)
          show "disjoint_list (?xs @ (?M # ?ys))"
            using disjoint_list_Tr
            by simp
          show  "\<forall> A \<in> set (?xs @ ?ys). oldH \<notin> A"
            using DisjAux
            by force
        qed
        have "?xs @ (?M \<union> {oldH}) # ?ys = state_rel0_disj_list Tr' AuxPred"
        proof -
          have xs_equal: "?xs =  [{heap_var Tr', heap_var_def Tr'},
                                  {mask_var Tr', mask_var_def Tr'},
                                  (ran (var_translation Tr')), 
                                  (ran (field_translation Tr')),
                                  (range (const_repr Tr')),
                                  dom AuxPred]"
            using \<open>Tr' = _\<close>
            by simp
          have MEqual: "vars_label_hm_tr (label_hm_translation Tr') = {oldH} \<union> ?M"
            using \<open>f = _\<close> \<open>Tr' = _\<close> lblNotPreviouslyDefined vars_label_hm_tr_def
            by simp
          show "?xs @ (?M \<union> {oldH}) # ?ys = state_rel0_disj_list Tr' AuxPred"
            using xs_equal MEqual
            by simp
        qed
        thus "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
          using disjointWithOldH
          by simp
      qed
      show "get_store_total \<omega>def = get_store_total \<omega>"
        using StateRel state_rel_eval_welldef_eq by blast
      show "get_trace_total \<omega>def = get_trace_total \<omega>"
        using StateRel state_rel_eval_welldef_eq by blast
      show "get_h_total_full \<omega>def = get_h_total_full \<omega>"
        using StateRel state_rel_eval_welldef_eq by blast
      show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>) ?ns'"
        by (metis (no_types, lifting) StateRel \<open>Tr' = _\<close> heapVarValue heap_var_rel_stable state_rel_heap_var_rel tr_vpr_bpl.select_convs(1) tr_vpr_bpl.select_convs(5) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other update_var_same)
      show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var Tr') (get_mh_total_full \<omega>) ?ns'"
        by (metis (mono_tags, lifting) DisjAux StateRel Sup_insert UnCI \<open>Tr' = _\<close> insertCI list.simps(15) mask_var_rel_stable state_rel_mask_var_rel tr_vpr_bpl.select_convs(2) tr_vpr_bpl.select_convs(5) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var_def Tr') (get_hh_total_full \<omega>def) ?ns'"
        by (metis (mono_tags, lifting) DisjAux StateRel Sup_insert UnI1 \<open>Tr' = _\<close> heap_var_rel_stable insertCI list.simps(15) state_rel_heap_var_def_rel tr_vpr_bpl.select_convs(3) tr_vpr_bpl.select_convs(5) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (mask_var_def Tr') (get_mh_total_full \<omega>def) ?ns'"
        by (metis (no_types, lifting) DisjAux StateRel Sup_insert UnCI \<open>Tr' = _\<close> insertCI list.simps(15) mask_var_rel_stable state_rel_mask_var_def_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      show "field_rel Pr ?\<Lambda> (field_translation Tr') ?ns'"
        by (metis (no_types, lifting) DisjAux StateRel Sup_insert UnCI \<open>Tr' = _\<close> field_rel_stable list.simps(15) state_rel_field_rel tr_vpr_bpl.select_convs(5) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      show "boogie_const_rel (const_repr Tr') ?\<Lambda> ?ns'"
        unfolding boogie_const_rel_def
      proof (intro allI)
        fix const
        show "lookup_var (var_context ctxt) ?ns' (const_repr Tr' const) = Some (boogie_const_val const)"
          by (metis (mono_tags, lifting) DisjAux StateRel Sup_insert UnCI \<open>Tr' = _\<close> boogie_const_rel_lookup list.simps(15) range_eqI state_rel_boogie_const_rel tr_vpr_bpl.select_convs(8) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
      qed
      show "state_well_typed (type_interp ctxt) ?\<Lambda> [] ?ns'"
        by (metis StateRel \<open>\<And>thesis. (\<And>heapValue. \<lbrakk>lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap heapValue)); lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep))\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> heapVarValue oldMType option.sel state_rel_state_well_typed state_well_typed_lookup state_well_typed_upd_2)
      show "aux_vars_pred_sat ?\<Lambda> AuxPred ?ns'"
        unfolding aux_vars_pred_sat_def
      proof (intro allI, intro impI)
        fix x P
        assume "AuxPred x = Some P"
        thus "has_Some P (lookup_var ?\<Lambda> (update_var ?\<Lambda> ns oldH (AbsV (AHeap heapValue))) x)"
          using DisjAux StateRel state_rel_aux_pred_sat_lookup by fastforce
      qed
      show "label_hm_rel Pr ?\<Lambda> TyRep (field_translation Tr') (label_hm_translation Tr') (get_trace_total \<omega>) ?ns'"
        unfolding label_hm_rel_def
      proof (intro conjI)
        show "label_rel (\<lambda>h \<phi>. heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') h (get_hh_total \<phi>)) (fst (label_hm_translation Tr')) (get_trace_total \<omega>) ?ns'"
          unfolding label_rel_def
        proof (intro allI, intro impI)
          fix l h
          assume premise: "fst (label_hm_translation Tr') l = Some h"
          show "\<exists> \<phi>'. get_trace_total \<omega> l = Some \<phi>' \<and>
                heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') h (get_hh_total \<phi>') ?ns'"
            by (smt (verit) DisjAux StateRel Sup_insert UnI1 Un_commute \<open>heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>) (update_var (var_context ctxt) ns oldH (AbsV (AHeap heapValue)))\<close> \<open>f = _\<close> \<open>Tr' = _\<close> fst_conv fun_upd_apply get_hh_total_full.elims heapVarValue heap_var_rel_def label_hm_rel_def label_rel_def list.simps(15) oldMType option.simps(1) premise ranI state_rel_label_hm_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) traceDefined update_var_apply vars_label_hm_tr_def)
        qed
        show "label_rel (\<lambda>m \<phi>. mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') m (get_mh_total \<phi>)) (snd (label_hm_translation Tr')) (get_trace_total \<omega>) ?ns'"
          unfolding label_rel_def
        proof (intro allI, intro impI)
          fix l h
          assume premise: "snd (label_hm_translation Tr') l = Some h"
          have "snd (label_hm_translation Tr') = snd (label_hm_translation Tr)"
            by (simp add: \<open>f = _\<close> \<open>Tr' = _\<close>)
          hence "\<exists>\<phi>. get_trace_total \<omega> l = Some \<phi> \<and>
                     mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) h (get_mh_total \<phi>) ns"
            by (metis (mono_tags, lifting) StateRel  label_hm_rel_def label_rel_def premise state_rel_label_hm_rel)
          thus "\<exists>\<phi>. get_trace_total \<omega> l = Some \<phi> \<and>
                     mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') h (get_mh_total \<phi>) ?ns'"
            by (metis (no_types, lifting) DisjAux Sup_insert UnI1 Un_commute \<open>f = _\<close> \<open>Tr' = _\<close> list.simps(15) mask_var_rel_def premise prod.sel(2) ranI tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other vars_label_hm_tr_def)
        qed
        show " \<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
          using StateRel state_rel_label_hm_rel label_hm_rel_def
          by blast
      qed
    qed
  qed
qed

lemma setup_oldm:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
          TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          EmptyRType: "rtype_interp ctxt = []" and
          DisjAux: "old_m \<notin> state_rel0_disj_vars Tr AuxPred" and
          trace_defined: "get_trace_total \<omega> lbl = Some \<phi> \<and> get_total_full \<omega> = \<phi>" and
          (* This assumption states that lbl was not previously defined in the mask map. Verify this assumption *)
          lbl_not_previously_defined: "snd (label_hm_translation Tr) lbl = None" and
          (* Here we assume that old_m has the mask type-- make sure this is the proper assumption about old_m later *)
          old_m_type: "lookup_var_ty (var_context ctxt) old_m = Some (TConSingle (TMaskId TyRep))" and
          (* This includes only the mask update in the label_hm_translation, should the heap be included as well? *)
          f: "f = (fst (label_hm_translation Tr), (snd (label_hm_translation Tr)) (lbl \<mapsto> old_m))" and
          Tr': "Tr' = Tr \<lparr> label_hm_translation := f \<rparr>" and
          "m = mask_var Tr"
  shows "\<exists> ns'. red_ast_bpl P ctxt
                (((BigBlock name ((Lang.Assign old_m (Var m)) # cs) s tr), cont), Normal ns)
                ((BigBlock name cs s tr, cont), Normal ns') \<and>
                  (state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ns')"
proof -
  let ?\<Lambda> = "var_context ctxt"
  let ?A = "type_interp ctxt"
  let ?FieldTr = "field_translation Tr"
  let ?FieldTr' = "field_translation Tr'"
  have FieldTr_is_FieldTr': "?FieldTr = ?FieldTr'"
    using Tr'
    by simp
  let ?m = "mask_var Tr"
  let ?\<omega>_trace_total = "get_trace_total \<omega>"
  let ?Tr_heap_labels = "fst (label_hm_translation Tr)"
  let ?Tr_mask_labels = "snd (label_hm_translation Tr)"
  let ?Tr'_heap_labels = "fst (label_hm_translation Tr')"
  let ?Tr'_mask_labels = "snd (label_hm_translation Tr')"
  from StateRel obtain mask_value where
    lookup_var: "lookup_var ?\<Lambda> ns ?m = Some (AbsV (AMask mask_value))" and
    lookup_var_type: "lookup_var_ty ?\<Lambda> ?m = Some (TConSingle (TMaskId TyRep))"
    unfolding state_rel_def state_rel0_def mask_var_rel_def
    by fast
  (* The new state is the existing state, with old_m set to the mask value *)
  let ?ns' = "update_var ?\<Lambda> ns old_m (AbsV (AMask mask_value))"
  have normal_execution: "red_ast_bpl P ctxt ((BigBlock name (Lang.Assign old_m (Var ?m)#cs) s tr, cont), Normal ns) ((BigBlock name cs s tr, cont), Normal ?ns')"
  proof (rule red_ast_bpl_one_assign)
    from lookup_var TyInterp EmptyRType have 
      "vbpl_absval_ty TyRep, var_context ctxt, fun_interp ctxt, [] \<turnstile> \<langle>(Var ?m), ns\<rangle> \<Down> (AbsV (AMask mask_value))"
      by (simp add: red_expr_red_exprs.RedVar)
    thus red_expr_bpl: "red_expr_bpl ctxt (Var ?m) ns (AbsV (AMask mask_value))"
      using EmptyRType TyInterp
      by simp
    thus type_of_val: "type_of_val (type_interp ctxt) (AbsV (AMask mask_value)) = instantiate (rtype_interp ctxt) (TConSingle (TMaskId TyRep))"
      using TyInterp
      by simp
    thus "lookup_var_ty (var_context ctxt) old_m = Some (TConSingle (TMaskId TyRep))"
      using old_m_type
      by simp
  qed

  have new_state_rel: "(state_rel Pr StateCons TyRep Tr' AuxPred ctxt \<omega>def \<omega> ?ns')"
    unfolding state_rel_def state_rel0_def
  proof(intro conjI)
    show consistent_state_rel_opt: "consistent_state_rel_opt (state_rel_opt Tr') \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>"
    proof -
      have "consistent_state_rel_opt (state_rel_opt Tr') \<Longrightarrow>  StateCons \<omega>def \<and> StateCons \<omega>"
      proof -
        assume premise: "(consistent_state_rel_opt (state_rel_opt Tr'))"
        have "consistent_state_rel_opt (state_rel_opt Tr') = consistent_state_rel_opt (state_rel_opt Tr)"
          using Tr'
          by simp
        thus "StateCons \<omega>def \<and> StateCons \<omega>"
          using premise StateRel state_rel_consistent
          by blast
      qed
      thus "consistent_state_rel_opt (state_rel_opt Tr') \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>" by simp
    qed
    show "store_rel ?A ?\<Lambda> (var_translation Tr') (get_store_total \<omega>) ?ns'"
      by (metis DisjAux StateRel Sup_insert Tr' UnI1 Un_commute list.simps(15) state_rel_store_rel store_rel_stable tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
    show disjoint_list: "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
    proof -
      have disjoint_list_Tr: "disjoint_list (state_rel0_disj_list Tr AuxPred)"
        using StateRel state_rel_disjoint
        by fast
      let ?xs = "[{heap_var Tr, heap_var_def Tr},
                  {mask_var Tr, mask_var_def Tr},
                  (ran (var_translation Tr)), 
                  (ran (field_translation Tr)),
                  (range (const_repr Tr)),
                  dom AuxPred]"
      let ?M =  "vars_label_hm_tr (label_hm_translation Tr)"
      let ?ys = "[]"
      have disjoint_with_old_m: "disjoint_list (?xs @ (?M \<union> {old_m}) # ?ys)"
      proof (rule disjoint_list_add)
        show "disjoint_list (?xs @ (?M # ?ys))"
          using disjoint_list_Tr
          by simp
        show  "\<forall> A \<in> set (?xs @ ?ys). old_m \<notin> A"
          using DisjAux
          by force
      qed
      have a: "?xs @ (?M \<union> {old_m}) # ?ys = state_rel0_disj_list Tr' AuxPred"
      proof -
        have xs_equal: "?xs =  [{heap_var Tr', heap_var_def Tr'},
                     {mask_var Tr', mask_var_def Tr'},
                     (ran (var_translation Tr')), 
                     (ran (field_translation Tr')),
                     (range (const_repr Tr')),
                     dom AuxPred]"
          using Tr'
          by simp
        have M_equal: "vars_label_hm_tr (label_hm_translation Tr') = {old_m} \<union> ?M"
          using f Tr' lbl_not_previously_defined vars_label_hm_tr_def
          by (simp)
        show "?xs @ (?M \<union> {old_m}) # ?ys = state_rel0_disj_list Tr' AuxPred"
          using xs_equal M_equal
          by simp
      qed
      show "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
        using a disjoint_with_old_m
        by simp
    qed

    show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' (heap_var Tr') (get_hh_total_full \<omega>) ?ns'"
    proof -
      let ?hvar = "heap_var Tr"
      have heap_var_same: "heap_var Tr' = ?hvar"
        using Tr'
        by simp
      have heap_var_rel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>) ns"
        using StateRel state_rel_heap_var_rel
        by fast
      then obtain hb where
        hb: "(lookup_var ?\<Lambda> ns ?hvar = Some (AbsV (AHeap hb)) \<and>
            lookup_var_ty ?\<Lambda> ?hvar = Some (TConSingle (THeapId TyRep)) \<and>
            vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[]) \<and>
            heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb) \<and>
            total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
        using heap_var_rel_def
        by blast
      have heap_defined: "lookup_var ?\<Lambda> ?ns' ?hvar = Some (AbsV (AHeap hb))"
        using heap_var_rel hb DisjAux
        by simp
      have heap_type_defined: "lookup_var_ty ?\<Lambda> ?hvar = Some (TConSingle (THeapId TyRep))"
        using heap_var_rel hb
        by simp
      have heap_rel: "heap_rel Pr (field_translation Tr') (get_hh_total_full \<omega>) hb"
        using hb Tr'
        by simp
      show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') (heap_var Tr') (get_hh_total_full \<omega>) ?ns'"
        using hb heap_defined heap_type_defined heap_rel Tr' heap_var_rel_def
        by fastforce
    qed

    show "mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr' (mask_var Tr') (get_mh_total_full \<omega>) ?ns'"
      by (metis (no_types, lifting) StateRel Tr' lookup_var mask_var_rel_stable state_rel_mask_var_rel tr_vpr_bpl.select_convs(2) tr_vpr_bpl.select_convs(5) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_opt_other update_var_same update_var_update_var_opt)
    show  "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' (heap_var_def Tr') (get_hh_total_full \<omega>def) ?ns'"
    proof -
      let ?hvar_def = "heap_var_def Tr"
      have heap_var_def_same: "heap_var_def Tr' = ?hvar_def"
        using Tr'
        by simp
      have heap_var_rel: "heap_var_rel Pr (var_context ctxt) TyRep ?FieldTr ?hvar_def (get_hh_total_full \<omega>def) ns"
        using StateRel state_rel_heap_var_def_rel
        by fast
      then obtain hb where
        hb: "(lookup_var ?\<Lambda> ns ?hvar_def = Some (AbsV (AHeap hb)) \<and>
            lookup_var_ty ?\<Lambda> ?hvar_def = Some (TConSingle (THeapId TyRep)) \<and>
            vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[]) \<and>
            heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>def) hb) \<and>
            total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
        using heap_var_rel_def
        by blast
      have heap_defined: "lookup_var ?\<Lambda> ?ns' ?hvar_def = Some (AbsV (AHeap hb))"
        using heap_var_rel hb DisjAux
        by simp
      have heap_type_defined: "lookup_var_ty ?\<Lambda> ?hvar_def = Some (TConSingle (THeapId TyRep))"
        using heap_var_rel hb
        by simp
      have heap_rel: "heap_rel Pr ?FieldTr (get_hh_total_full \<omega>def) hb"
        using hb Tr'
        by simp
      have "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr (heap_var_def Tr') (get_hh_total_full \<omega>def) ?ns'"
      proof -
        have sg1: "lookup_var ?\<Lambda> ?ns' ?hvar_def = Some (AbsV (AHeap hb))"
          using Tr' hb DisjAux
          by simp
        have sg2: "lookup_var_ty ?\<Lambda> ?hvar_def = Some (TConSingle (THeapId TyRep))"
          using Tr' hb DisjAux heap_defined
          by force
        have sg3: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and> heap_rel Pr ?FieldTr (get_hh_total_full \<omega>def) hb"
          using hb
          by simp
        have sg4: "total_heap_well_typed Pr (domain_type TyRep)  (get_hh_total_full \<omega>def)"
          using hb
          by simp
        show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr (heap_var_def Tr') (get_hh_total_full \<omega>def) ?ns'"
          using sg1 sg2 sg3 sg4 heap_var_def_same heap_var_rel_def
          by fastforce
      qed
      thus "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' (heap_var_def Tr') (get_hh_total_full \<omega>def) ?ns'"
        using Tr'
        by fastforce
    qed
    show mask_var_rel_\<omega>def: "mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr' (mask_var_def Tr') (get_mh_total_full \<omega>def) ?ns'"
      by (metis (no_types, lifting) DisjAux StateRel Sup_insert Tr' UnCI insertCI list.simps(15) mask_var_rel_stable state_rel_mask_var_def_rel tr_vpr_bpl.ext_inject tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) update_var_other)
    
    show "field_rel Pr ?\<Lambda> ?FieldTr' ?ns'"
      unfolding field_rel_def
    proof (intro conjI)
      have field_tr_equal: "?FieldTr' = ?FieldTr"
        using Tr'
        by simp
      show "inj_on ?FieldTr' (dom ?FieldTr')"
        using StateRel field_rel_def state_rel_field_rel field_tr_equal
        by metis
      show "(\<forall>f f_vty.
        declared_fields Pr f = Some f_vty \<longrightarrow>
        has_Some
         (\<lambda>f_bpl.
             lookup_var (var_context ctxt) ?ns' f_bpl =
             Some (AbsV (AField (NormalField f_bpl f_vty))))
         (?FieldTr' f))"
      proof -
        have "(\<And>field f_vty.
              declared_fields Pr field = Some f_vty \<Longrightarrow>
              has_Some (\<lambda>f_bpl. lookup_var ?\<Lambda> ?ns' f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (?FieldTr' field))"
        proof -
          fix field f_vty
          assume viper_field_declared: "declared_fields Pr field = Some f_vty"
          let ?FieldExists = "\<lambda>f_bpl. lookup_var ?\<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))"
          let ?FieldExists' = "\<lambda>f_bpl. lookup_var ?\<Lambda> ?ns' f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))"
          have field_rel_Tr: "field_rel Pr ?\<Lambda> (field_translation Tr) ns"
            using StateRel state_rel_field_rel
            by fast
          hence "(\<forall>f f_vty. declared_fields Pr f = Some f_vty \<longrightarrow> 
               has_Some (\<lambda>f_bpl. lookup_var ?\<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (?FieldTr' f))"
            using field_rel_def field_tr_equal
            by fastforce
          hence has_Some_ns: "has_Some (\<lambda>f_bpl. lookup_var ?\<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (?FieldTr' field)"
            using viper_field_declared
            by simp
          then obtain f_bpl where
            FieldTr_field: "?FieldTr' field = Some f_bpl"
            by fastforce
          have "lookup_var ?\<Lambda> ?ns' f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))"
          proof -
            have "f_bpl \<noteq> old_m"
              using FieldTr_field ranI DisjAux field_tr_equal
              by fastforce
            hence "lookup_var ?\<Lambda> ?ns' f_bpl = lookup_var ?\<Lambda> ns f_bpl"
              by simp
            thus "lookup_var ?\<Lambda> ?ns' f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))"
              using FieldTr_field has_Some_ns
              by simp
          qed
          hence "?FieldExists' f_bpl" by simp
          thus "has_Some ?FieldExists' (?FieldTr' field)"
            using FieldTr_field
            by simp
        qed
        thus "(\<forall>f f_vty.
              declared_fields Pr f = Some f_vty \<longrightarrow>
              has_Some (\<lambda>f_bpl. lookup_var ?\<Lambda> ?ns' f_bpl = Some (AbsV (AField (NormalField f_bpl f_vty)))) (?FieldTr' f))"
          by simp
      qed
    qed

    show "boogie_const_rel (const_repr Tr') ?\<Lambda> ?ns'"
    proof -
      let ?C = "const_repr Tr'"
      have "\<And>const. lookup_var ?\<Lambda> ?ns' (?C const) = Some (boogie_const_val const)"
      proof -
        fix const
        have "old_m \<notin> range ?C"
          using DisjAux Tr'
          by force
        hence "?C const \<noteq> old_m"
          by fast
        hence lookup_var_equal: "lookup_var ?\<Lambda> ?ns' (?C const) = lookup_var ?\<Lambda> ns (?C const)"
          by simp
        have "lookup_var ?\<Lambda> ns (?C const) =  Some (boogie_const_val const)"
          by (metis StateRel Tr' boogie_const_rel_lookup state_rel_boogie_const_rel tr_vpr_bpl.select_convs(8) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9))
        thus "lookup_var ?\<Lambda> ?ns' (?C const) = Some (boogie_const_val const)"
          using lookup_var_equal
          by simp
      qed
      thus "boogie_const_rel (const_repr Tr') ?\<Lambda> ?ns'"
        using boogie_const_rel_def
        by fast
    qed
 
    show "state_well_typed ?A ?\<Lambda> [] ?ns'"
      by (metis StateRel lookup_var lookup_var_type old_m_type option.sel state_rel_state_well_typed state_well_typed_lookup state_well_typed_upd_2)

    show  "aux_vars_pred_sat ?\<Lambda> AuxPred ?ns'"
    proof -
      have "(\<And>x P. AuxPred x = Some P \<Longrightarrow> has_Some (\<lambda>v. P v) (lookup_var ?\<Lambda> ?ns' x))"
      proof -
        fix x P
        assume predicate_defined: "AuxPred x = Some P"
        show "has_Some (\<lambda>v. P v) (lookup_var ?\<Lambda> ?ns' x)"
        proof (cases)
          assume x_is_old_m: "x = old_m"
          hence "lookup_var ?\<Lambda> ?ns' x = Some (AbsV (AMask mask_value))"
            by simp
          thus "has_Some (\<lambda>v. P v) (lookup_var ?\<Lambda> ?ns' x)"
            using DisjAux predicate_defined x_is_old_m
            by auto
        next
          assume "x \<noteq> old_m"
          hence "lookup_var ?\<Lambda> ?ns' x = lookup_var ?\<Lambda> ns x"
            by simp
          thus "has_Some (\<lambda>v. P v) (lookup_var ?\<Lambda> ?ns' x)"
            using StateRel predicate_defined state_rel_aux_pred_sat_lookup
            by fastforce
        qed
      qed
      thus "aux_vars_pred_sat ?\<Lambda> AuxPred ?ns'"
        using aux_vars_pred_sat_def
        by fast
    qed

    show "label_hm_rel Pr ?\<Lambda> TyRep ?FieldTr' (label_hm_translation Tr') ?\<omega>_trace_total ?ns'"
      unfolding label_hm_rel_def
    proof (intro conjI)
      let ?HeapPred =  "\<lambda>h \<phi>. heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_hh_total \<phi>)"
      let ?HeapPred' =  "\<lambda>h \<phi>. heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' h (get_hh_total \<phi>)"
      show "label_rel ?HeapPred' ?Tr'_heap_labels ?\<omega>_trace_total ?ns'"
      proof -
        have "label_rel ?HeapPred (fst (label_hm_translation Tr)) (get_trace_total \<omega>) ns"
          using StateRel Tr'
          by (simp add: label_hm_rel_def state_rel0_def state_rel_def)
        hence label_rel: "label_rel ?HeapPred' ?Tr_heap_labels (get_trace_total \<omega>) ns"
          using FieldTr_is_FieldTr'
          by simp
        have "\<And> l h. ?Tr_heap_labels l = Some h \<Longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ?ns')"
        proof -
          fix l h
          assume l_in_heap: "?Tr_heap_labels l = Some h"
          show "\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ?ns'"
          proof (cases)
            assume l_is_lbl: "l = lbl"
            have sg1: "?\<omega>_trace_total l = Some \<phi>"
              using l_is_lbl trace_defined
              by simp
            have "?HeapPred h \<phi> ns"
              by (metis (mono_tags, lifting) FieldTr_is_FieldTr' l_in_heap l_is_lbl label_rel label_rel_def option.sel trace_defined)
            hence sg2: "?HeapPred' h \<phi> ?ns'"
              by (metis (no_types, lifting) DisjAux FieldTr_is_FieldTr' Sup_insert UnCI heap_var_rel_def l_in_heap list.simps(15) ranI update_var_opt_other update_var_update_var_opt vars_label_hm_tr_def)
            show "(\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ?ns')"
              using sg1 sg2
              by simp
          next
            assume l_is_not_lbl: "l \<noteq> lbl"
            have label_rel_contents: "(\<forall> l h. ?Tr_heap_labels l = Some h \<longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ns))"
              using label_rel label_rel_def
              by meson
            have tr_heap_labels_defined: "?Tr_heap_labels l = Some h"
              using l_in_heap f Tr'
              by simp
            obtain \<phi> where
              sg1: "?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ns"
              using label_rel_contents tr_heap_labels_defined
              by fast
            have sg2: "?HeapPred' h \<phi> ?ns'"
            proof -
              have "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' h (get_hh_total \<phi>) ?ns'"
              proof -
                have h_is_not_old_m: "h \<noteq> old_m"
                  by (metis (mono_tags, opaque_lifting) DisjAux Sup_insert UnCI list.simps(15) ranI tr_heap_labels_defined vars_label_hm_tr_def)
                obtain hb where lookup_var: "lookup_var ?\<Lambda> ?ns' h = Some (AbsV (AHeap hb))"
                  by (metis h_is_not_old_m heap_var_rel_def sg1 update_var_other)
                have lookup_var_ty: "lookup_var_ty ?\<Lambda> h = Some (TConSingle (THeapId TyRep))"
                  using heap_var_rel_def sg1
                  by fast
                have vbpl_absval_ty_opt: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
                  by (metis Semantics.val.inject(2) h_is_not_old_m heap_var_rel_def lookup_var option.sel sg1 update_var_other)
                have heap_rel: "heap_rel Pr ?FieldTr' (get_hh_total \<phi>) hb"
                  by (metis Semantics.val.inject(2) h_is_not_old_m heap_var_rel_def lookup_var option.sel sg1 update_var_other vbpl_absval.simps(4))
                have total_heap_well_typed: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total \<phi>)"
                  using heap_var_rel_def sg1 by blast
                show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr' h (get_hh_total \<phi>) ?ns'"
                  using lookup_var lookup_var_ty vbpl_absval_ty_opt heap_rel total_heap_well_typed heap_var_rel_def
                  by blast
              qed
              thus "?HeapPred' h \<phi> ?ns'"
                using Tr'
                by simp
            qed
            show "\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ?ns'"
              using sg1 sg2
              by simp
          qed
        qed
        hence "\<forall>l h. ?Tr'_heap_labels l = Some h \<longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?HeapPred' h \<phi> ?ns')"
          using Tr' f
          by simp
        thus "label_rel ?HeapPred' ?Tr'_heap_labels ?\<omega>_trace_total ?ns'"
          unfolding label_rel_def
          by simp
      qed
      let ?MaskPred = "\<lambda>m \<phi>. mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr m (get_mh_total \<phi>)"
      let ?MaskPred' = "\<lambda>m \<phi>. mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr' m (get_mh_total \<phi>)"
      show "label_rel ?MaskPred' ?Tr'_mask_labels ?\<omega>_trace_total ?ns'"
      proof -
        have "label_rel ?MaskPred ?Tr_mask_labels ?\<omega>_trace_total ns"
          using StateRel label_hm_rel_def state_rel_label_hm_rel
          by metis
        hence label_rel: "label_rel ?MaskPred ?Tr_mask_labels ?\<omega>_trace_total ns"
          using FieldTr_is_FieldTr'
          by simp
        have "\<And> l h. ?Tr'_mask_labels l = Some h \<Longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' h \<phi> ?ns')"
        proof -
          fix l m
          assume l_in_mask: "?Tr'_mask_labels l = Some m"
          show "\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' m \<phi> ?ns'"
          proof (cases)
            assume l_is_lbl: "l = lbl"
            have sg1: "?\<omega>_trace_total l = Some \<phi>"
              using l_is_lbl trace_defined
              by simp
            have sg2: "?MaskPred' m \<phi> ?ns'"
              using l_in_mask l_is_lbl f lbl_not_previously_defined
              by (metis (no_types, lifting) FieldTr_is_FieldTr' StateRel Tr' fun_upd_same get_mh_total_full.simps lookup_var mask_var_rel_def old_m_type option.sel snd_conv state_rel_obtain_mask tr_vpr_bpl.select_convs(9) tr_vpr_bpl.surjective tr_vpr_bpl.update_convs(9) trace_defined update_var_same)
            show "(\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' m \<phi> ?ns')"
              using sg1 sg2
              by simp
          next
            fix \<phi>
            assume l_is_not_lbl: "l \<noteq> lbl"
            have label_rel_contents: "(\<forall> lbl m. ?Tr_mask_labels lbl = Some m \<longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total lbl = Some \<phi> \<and> ?MaskPred' m \<phi> ns))"
              using label_rel label_rel_def FieldTr_is_FieldTr'
              by (metis (mono_tags, lifting))
            have tr_mask_labels_defined: "?Tr_mask_labels l = Some m"
              using l_in_mask f l_is_not_lbl Tr'
              by simp
            obtain \<phi> where
              sg1: "?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' m \<phi> ?ns'"
              using label_rel_contents tr_mask_labels_defined
              by (metis (mono_tags, lifting) DisjAux Sup_insert UnCI list.simps(15) mask_var_rel_stable ranI update_var_other vars_label_hm_tr_def)
            thus "(\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' m \<phi> ?ns')"
              using sg1
              by simp
          qed
        qed
        hence "\<forall> l h. ?Tr'_mask_labels l = Some h \<longrightarrow> (\<exists>\<phi>. ?\<omega>_trace_total l = Some \<phi> \<and> ?MaskPred' h \<phi> ?ns')" by simp
        thus "label_rel ?MaskPred' ?Tr'_mask_labels ?\<omega>_trace_total ?ns'"
          using label_rel_def
          by blast
      qed
      show "\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
        by (meson StateRel label_hm_rel_def state_rel_label_hm_rel)
    qed

    show "valid_heap_mask (get_mh_total_full \<omega>def)"
      using StateRel state_rel_wf_mask_def_simple
      by fast

    show "valid_heap_mask (get_mh_total_full \<omega>)"
      using StateRel state_rel_wf_mask_simple
      by fast

    show "type_interp ctxt = vbpl_absval_ty TyRep"
      using TyInterp
      by simp

    show "get_store_total \<omega>def = get_store_total \<omega>"
      using StateRel state_rel_eval_welldef_eq
      by blast

    show "get_trace_total \<omega>def = get_trace_total \<omega>"
      using StateRel state_rel_eval_welldef_eq
      by blast

    show "get_h_total_full \<omega>def = get_h_total_full \<omega>"
      using StateRel state_rel_eval_welldef_eq
      by blast
  qed
  show ?thesis
    using normal_execution new_state_rel \<open>m = _\<close>
    by blast
qed

(* if tracked then heap_rel holds for all labels *)
lemma label_tracked_implies_heap_rel:
  (* If the label_hm_rel relation holds for a given translation record and viper state *)
  assumes "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
  (* And the total state is defined at some label *)
      and "get_trace_total \<omega> lbl = Some \<phi>"
  (* And the heap variable is hvar *)
      and "(fst (label_hm_translation Tr)) lbl = Some hvar"
  (* Then heap_var_rel holds between Tr and hvar *)
    shows "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar (get_hh_total \<phi>) ns"
  using assms label_hm_rel_def label_rel_def
  by (metis (mono_tags, lifting) option.sel)

lemma label_tracked_implies_mask_rel:
  assumes "label_hm_rel Pr (var_context ctxt) TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
  (* And the total state is defined at some label *)
      and "get_trace_total \<omega> lbl = Some \<phi>"
  (* And the heap variable is mvar *)
      and "(snd (label_hm_translation Tr)) lbl = Some mvar"
  (* Then heap_var_rel holds between Tr and mvar *)
    shows "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar (get_mh_total \<phi>) ns"
  using assms label_hm_rel_def label_rel_def
  by (metis (mono_tags, lifting) option.sel)


lemma state_rel_can_add_trace:
  assumes StateRel: "state_rel_def_same Pr (\<lambda>_. True) TyRep Tr AuxPred ctxt \<omega> ns"
      and labelHMTranslationEmpty: "label_hm_translation Tr = (Map.empty, Map.empty)"
      and "\<omega>' = update_trace_total \<omega> [lbl \<mapsto> get_total_full \<omega>]"
      and labelNotInHMTranslation: "lbl \<notin> dom (fst (label_hm_translation Tr)) \<and> lbl \<notin> dom (snd (label_hm_translation Tr))"
    shows "state_rel_def_same Pr (\<lambda>_. True) TyRep Tr AuxPred ctxt \<omega>' ns \<and>
           get_trace_total \<omega>' = [lbl \<mapsto> get_total_full \<omega>']"
proof (intro conjI)
  show "state_rel_def_same Pr (\<lambda>_. True) TyRep Tr AuxPred ctxt \<omega>' ns"
    unfolding state_rel_def state_rel0_def
  proof (intro conjI, simp_all, tactic distinct_subgoals_tac)
    let ?\<Lambda> = "var_context ctxt"
    let ?FieldTr = "field_translation Tr"
    show "valid_heap_mask (get_mh_total (get_total_full \<omega>'))"
      using StateRel \<open>\<omega>' = _\<close> state_rel_wf_mask_def_simple by fastforce
    show "type_interp ctxt = vbpl_absval_ty TyRep"
      using StateRel state_rel_type_interp by blast
    show "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr) (get_store_total \<omega>') ns"
      by (metis StateRel \<open>\<omega>' = _\<close> state_rel_store_rel update_trace_total_store_same)
    show "disjoint_list (state_rel0_disj_list Tr AuxPred)"
      using StateRel state_rel_disjoint
      by fast
    show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr (heap_var Tr) (get_hh_total (get_total_full \<omega>')) ns"
      using StateRel \<open>\<omega>' = _\<close> state_rel_heap_var_rel
      by force
    show "mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr (mask_var Tr) (get_mh_total (get_total_full \<omega>')) ns"
      using StateRel \<open>\<omega>' = _\<close> state_rel_mask_var_rel
      by force
    show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr (heap_var_def Tr) (get_hh_total (get_total_full \<omega>'))
     ns"
      using StateRel \<open>\<omega>' = _\<close> state_rel_heap_var_def_rel
      by fastforce
    show "mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr (mask_var_def Tr) (get_mh_total (get_total_full \<omega>'))
     ns"
      using StateRel \<open>\<omega>' = _\<close> state_rel_mask_var_def_rel
      by fastforce
    show "field_rel Pr ?\<Lambda> ?FieldTr ns"
      using StateRel state_rel_field_rel
      by blast
    show "boogie_const_rel (const_repr Tr) ?\<Lambda> ns"
      using StateRel state_rel_boogie_const_rel
      by fast
    show "state_well_typed (type_interp ctxt) ?\<Lambda> [] ns"
      using StateRel state_rel_state_well_typed
      by fast
    show "aux_vars_pred_sat ?\<Lambda> AuxPred ns"
      using StateRel state_rel_aux_vars_pred_sat
      by fast
    show "label_hm_rel Pr ?\<Lambda> TyRep ?FieldTr (label_hm_translation Tr) (get_trace_total \<omega>') ns"
      unfolding label_hm_rel_def
    proof (intro conjI)
      show "label_rel (\<lambda>h \<phi>. heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_hh_total \<phi>)) (fst (label_hm_translation Tr)) (get_trace_total \<omega>') ns"
        by (simp add: labelHMTranslationEmpty label_rel_def)
      show "label_rel (\<lambda>m \<phi>. mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr m (get_mh_total \<phi>)) (snd (label_hm_translation Tr)) (get_trace_total \<omega>') ns"
        by (simp add: labelHMTranslationEmpty label_rel_def)
      show "\<forall>l \<phi>. get_trace_total \<omega>' l = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
      proof (intro allI, intro impI)
        fix l \<phi>
        assume premise: "get_trace_total \<omega>' l = Some \<phi>"
        have "get_trace_total \<omega>' = [lbl \<mapsto> get_total_full \<omega>]"
          using \<open>\<omega>' = _\<close>
          by simp
        hence "l = lbl"
          by (metis fun_upd_apply option.discI premise)
        hence "\<phi> = get_total_full \<omega>"
          using \<open>get_trace_total \<omega>' = _\<close> premise
          by simp   
        hence "get_mh_total \<phi> = get_mh_total_full \<omega>"
          by simp
        from StateRel state_rel_wf_mask_simple have "wf_mask_simple (get_mh_total_full \<omega>)"
          by blast
        thus "valid_heap_mask (get_mh_total \<phi>)" 
          using \<open>get_mh_total \<phi> = _\<close>
          by simp
      qed
    qed
  qed
  show "get_trace_total \<omega>' = [lbl \<mapsto> get_total_full \<omega>']"
    using \<open>\<omega>' = _\<close> by simp
qed

lemma element_not_in_any_set_implies_not_in_disj_vars:
  assumes "e \<notin> {heap_var Tr, heap_var_def Tr}"
      and "e \<notin> {mask_var Tr, mask_var_def Tr}"
      and "e \<notin> ran (var_translation Tr)"
      and "e \<notin> ran (field_translation Tr)"
      and "e \<notin>  range (const_repr Tr)"
      and "e \<notin> dom AuxPred"
      and "e \<notin> vars_label_hm_tr (label_hm_translation Tr)"
    shows "e \<notin> state_rel0_disj_vars Tr AuxPred"
  using assms by auto

abbreviation state_rel0_disj_list
  where "state_rel0_disj_list Tr AuxPred \<equiv> [{heap_var Tr, heap_var_def Tr},
                      {mask_var Tr, mask_var_def Tr},
                      (ran (var_translation Tr)), 
                      (ran (field_translation Tr)),
                      (range (const_repr Tr)),
                      dom AuxPred,
                      vars_label_hm_tr (label_hm_translation Tr)]"

lemma store_vpr_exp_to_temporary_var:
  assumes  
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega>def \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" and
         DisjAux: "temp_var \<notin> state_rel0_disj_vars Tr AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some \<tau>_bpl" and
  RedRhsVpr:  "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
  ExpRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e_vpr e_bpl" and
         TyValBpl:  "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = \<tau>_bpl"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e_bpl # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq (val_rel_vpr_bpl v))) ctxt \<omega>def \<omega> ns')"
proof (rule store_temporary_var[OF StateRel TyInterp EmptyRtype DisjAux LookupTyTemp _ TyValBpl])
  show "red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v)"
    using exp_rel_vpr_bpl_elim[OF ExpRel] RedRhsVpr StateRel
    by metis
qed

lemma store_temporary_perm_rel:
  assumes
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega>def \<omega> ns") and
  RedPerm:  "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
  ExpRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e_vpr e_bpl" and
         DisjAux: "temp_var \<notin> state_rel0_disj_vars Tr AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some (TPrim TReal)" and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" 
  shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e_bpl # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq (RealV p))) ctxt \<omega>def \<omega> ns')"
           (is "\<exists>ns'. ?red ns' \<and> ?R' \<omega> ns'")
   using store_vpr_exp_to_temporary_var[OF StateRel TyInterp EmptyRtype DisjAux LookupTyTemp RedPerm ExpRel]
   by simp

subsection \<open>Permission checks\<close>

lemma pos_perm_rel_nontrivial:
  assumes "zero_perm = const_repr Tr CNoPerm" and
          StateRelImpl:"\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt \<omega>def \<omega> ns" and
          SuccessCond:"\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow> \<omega> = \<omega>' \<and> p \<ge> 0" and
          FailCond: "\<And> \<omega>. Fail \<omega> \<Longrightarrow> p < 0"
shows "rel_general (uncurry R) 
                   (uncurry R)
     Success Fail
     P ctxt
     (BigBlock name (cmd.Assert (expr.Var temp_perm \<guillemotleft>Ge\<guillemotright> expr.Var zero_perm) # cs) s tr, cont)
     (BigBlock name cs s tr, cont)" (is "rel_general ?R ?R ?Success ?Fail P ctxt ?\<gamma> ?\<gamma>'")
proof (rule assert_single_step_rel[where ?cond="\<lambda>_. p \<ge> 0"])
  fix \<omega>def_\<omega> ns
  
  assume "uncurry R \<omega>def_\<omega> ns" 
  hence StateRel: "state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV p))) ctxt (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns"
    using StateRelImpl
    by simp
  let ?p_bpl = "RealV p"
  
  have LookupTempPerm: "lookup_var (var_context ctxt) ns temp_perm = Some ?p_bpl"
    using state_rel_aux_pred_sat_lookup_2[OF StateRel]
    unfolding pred_eq_def
    by (metis (full_types) fun_upd_same)
  thus "red_expr_bpl ctxt (expr.Var temp_perm \<guillemotleft>Ge\<guillemotright> expr.Var zero_perm) ns (BoolV (0 \<le> p))"
        by (auto intro!: red_expr_red_exprs.intros                         
             intro: LookupTempPerm
                    boogie_const_rel_lookup[OF state_rel0_boogie_const_rel[OF state_rel_state_rel0[OF StateRel]]]
             simp: \<open>zero_perm = _\<close> )
qed (insert assms, auto)

subsection \<open>Mask Update\<close>

lemma mask_upd_rel:
  assumes

   StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>
                           state_rel Pr StateCons TyRep Tr AuxPred ctxt (fst \<omega>) (snd \<omega>) ns" and     
    Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> (\<And> \<omega> \<omega>' ns a. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> r = Address a \<Longrightarrow> StateCons (snd \<omega>'))" and                                      
    WfTyRep:  "wf_ty_repr_bpl TyRep" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
    MaskVar: "m_bpl = mask_var Tr" and
    FieldRelSingle: "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    SuccessUpdState: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow>
                         fst \<omega>' = (if mask_var_def Tr = mask_var Tr \<and> r \<noteq> Null then snd \<omega>' else fst \<omega>) \<and>
                         snd \<omega>' = (if r = Null then (snd \<omega>) else 
                                      update_mh_loc_total_full (snd \<omega>) (the_address r,f_vpr) (p_preal \<omega>))" and
    RedRcvBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))" and
    RedPermBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> 
                   red_expr_bpl ctxt new_perm_bpl ns 
                               (if r = Null then RealV 0 else (RealV (Rep_preal (p_preal \<omega>)))) \<and>
                   (r \<noteq> Null \<longrightarrow> pgte pwrite (p_preal \<omega>))"
  shows "rel_general R 
                  (uncurry (state_rel Pr StateCons TyRep Tr AuxPred ctxt))
                  Success
                  (\<lambda> \<omega>. False) 
                  P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
proof (rule rel_intro)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns" and Success: "Success \<omega> \<omega>'"

  note StateRelInst = StateRel[OF \<open>R \<omega> ns\<close>]
  
  obtain f_bpl \<tau>_vpr where
    FieldLookup: "declared_fields Pr f_vpr = Some \<tau>_vpr" and
    TyTr: "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl" and
    FieldTr: "field_translation Tr f_vpr = Some f_bpl" and
    "e_f_bpl = Lang.Var f_bpl"
  using FieldRelSingle
  by (auto elim: field_rel_single_elim)

  hence FieldLookupBpl: "lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField (NormalField f_bpl \<tau>_vpr)))"
      (is "_ = Some (AbsV (AField ?f_bpl_val))")
    using state_rel_field_rel[OF StateRelInst]
    unfolding field_rel_def
    by fastforce

  obtain mb where
        LookupMask: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
        LookupMaskTy: "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep))" and
        MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full (snd \<omega>)) mb"
    using state_rel_obtain_mask[OF StateRelInst]
    by blast

  let ?p' = "if r = Null then 0 else Rep_preal (p_preal \<omega>)"
  let ?mb' = "mb ( (r, ?f_bpl_val) := ?p' )"
        
  have RedMaskUpdBpl:
    "red_expr_bpl ctxt m_upd_bpl ns (AbsV (AMask ?mb'))" 
    apply (subst \<open>m_upd_bpl = _\<close>)
    apply (subst \<open>e_f_bpl = _\<close>)
    apply (subst \<open>m_bpl = _\<close>)
    apply (rule mask_update_wf_apply[OF MaskUpdateWf])
        apply (fastforce intro: RedVar LookupMask)
       apply (fastforce intro: RedRcvBpl[OF \<open>R \<omega> ns\<close> Success])
      apply (fastforce intro: RedVar FieldLookupBpl)
    using RedPermBpl[OF \<open>R \<omega> ns\<close> Success]
     apply fastforce
    using TyTr
    by simp
    
  let ?\<omega>' = "(if r = Null then (snd \<omega>) else update_mh_loc_total_full (snd \<omega>) (the_address r,f_vpr) (p_preal \<omega>))"

  let ?ns' = "update_var (var_context ctxt) ns m_bpl (AbsV (AMask ?mb'))"

  have RedAstBpl:
     "red_ast_bpl P ctxt ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns) 
                         ((BigBlock name cs str tr, cont), Normal ?ns')"
    using \<open>m_bpl = _\<close> LookupMaskTy TyInterp RedMaskUpdBpl
    by (auto intro!: red_ast_bpl_one_simple_cmd Semantics.RedAssign)

  show "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign m_bpl m_upd_bpl # cs) str tr, cont), Normal ns)
              ((BigBlock name cs str tr, cont), Normal ns') \<and>
             uncurry (state_rel Pr StateCons TyRep Tr AuxPred ctxt) \<omega>' ns'"
  proof (cases "r = Null")
    case True
    hence "?mb' = mb"
      using MaskRel
      unfolding mask_rel_def
      by fastforce
    moreover have "fst \<omega> = fst \<omega>'"
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] True
      by argo
    ultimately show ?thesis
        using \<open>r = Null\<close> MaskVar RedAstBpl SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] update_var_same_state[OF LookupMask] StateRelInst
        by auto        
  next
    case False
    from this obtain a where "r = Address a" 
      using ref.exhaust by auto
    hence "snd \<omega>' = update_mh_loc_total_full (snd \<omega>) (a,f_vpr) (p_preal \<omega>)"
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False
      by simp
   
    have "?mb' = mask_bpl_upd_normal_field mb (Address a) f_bpl \<tau>_vpr (Rep_preal (p_preal \<omega>))"
      unfolding mask_bpl_upd_normal_field_def
      by (simp add: \<open>r = _\<close>)      

    have "state_rel Pr StateCons TyRep Tr AuxPred ctxt (fst \<omega>') (snd \<omega>') ?ns'"
      apply (subst \<open>snd \<omega>' = _\<close>)+
      apply (subst \<open>?mb' = _\<close>)
      apply (subst \<open>m_bpl = _\<close>)
      apply (rule state_rel_mask_update_4[OF StateRelInst])
               apply simp
              
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False \<open>r = _\<close>
              apply force
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False \<open>r = _\<close>
             apply argo
      using Consistent[OF _ \<open>R \<omega> ns\<close> Success \<open>r = Address a\<close>] \<open>snd \<omega>' = _\<close>      
             apply simp
            apply (simp add: TyInterp)      
           apply (simp add: LookupMask)
      using RedPermBpl[OF \<open>R \<omega> ns\<close> Success] False
          apply simp
         apply (simp add: FieldLookup)
        apply (simp add: FieldTr)
       apply (simp add: TyTr)
      apply simp
      done  
    thus ?thesis
      using RedAstBpl
      by auto
  qed
qed (simp)

text \<open>Same lemma as above but specialized for a relation on two states where the well-definedness state
      is the same as the evaluation state. 
      It seems to be more convenient to define such an alternate version instead of directly working with
      the above lemma.\<close>

lemma mask_upd_rel_2:
  assumes
   StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>
                           state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns" and  
    Consistent: "\<And> \<omega> \<omega>' ns a. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> r = Address a \<Longrightarrow> StateCons \<omega>'" and
    WfTyRep:  "wf_ty_repr_bpl TyRep" and
    MaskVarDefSame: "mask_var_def Tr = mask_var Tr" and
    TyInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
    MaskUpdateWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    MaskUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
    MaskVar: "m_bpl = mask_var Tr" and
    FieldRelSingle: "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    SuccessUpdState: "\<And> \<omega> \<omega>'. Success \<omega> \<omega>' \<Longrightarrow>
                         \<omega>' = (if r = Null then \<omega> else 
                                      update_mh_loc_total_full \<omega> (the_address r,f_vpr) (p_preal \<omega>))" and
    RedRcvBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))" and
    RedPermBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> 
                   red_expr_bpl ctxt new_perm_bpl ns 
                               (if r = Null then RealV 0 else (RealV (Rep_preal (p_preal \<omega>)))) \<and>
                   (r \<noteq> Null \<longrightarrow> pgte pwrite (p_preal \<omega>))"
  shows "rel_general R 
                  (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
                  Success
                  (\<lambda> \<omega>. False) P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
  apply (rule rel_general_convert, rule rel_general_conseq_fail, rule rel_general_conseq_output, 
         rule mask_upd_rel[where ?p_preal="p_preal \<circ> snd" and r=r])
  using assms
  by fastforce+

subsection \<open>Constructing a well-typed Boogie heap from a Viper heap (TODO: move somewhere more suitable)\<close>

fun construct_bpl_heap_from_vpr_heap :: "program \<Rightarrow> (field_ident \<rightharpoonup> vname) \<Rightarrow> 'a total_heap \<Rightarrow> 'a bpl_heap_ty"
  where "construct_bpl_heap_from_vpr_heap Pr tr_field h = 
          (\<lambda> loc_bpl. 
                  case (snd loc_bpl) of
                    NormalField f t \<Rightarrow> 
                      if (\<exists>loc_vpr. fst loc_bpl = Address (fst loc_vpr) \<and>
                                    declared_fields Pr (snd loc_vpr) = Some t \<and> 
                                    tr_field (snd loc_vpr) = Some f) then
                        Some (val_rel_vpr_bpl (h (the_address (fst loc_bpl), 
                                              (SOME fid_vpr. declared_fields Pr fid_vpr = Some t \<and> tr_field fid_vpr = Some f))))
                      else 
                        None
                  | _ \<Rightarrow> None
             )"

lemma construct_bpl_heap_from_vpr_heap_aux:
assumes "declared_fields Pr fid = Some t" and
        "tr_field fid = Some fid_bpl" and
        "inj_on tr_field (dom tr_field)"
      shows "construct_bpl_heap_from_vpr_heap Pr tr_field h (Address a, NormalField fid_bpl t) = Some (val_rel_vpr_bpl (h (a, fid)))"
  using assms  
proof -
  have 
  "construct_bpl_heap_from_vpr_heap Pr tr_field h (Address a, NormalField fid_bpl t) =
       Some (val_rel_vpr_bpl (h (a, (SOME fid_vpr. declared_fields Pr fid_vpr = Some t \<and> tr_field fid_vpr = Some fid_bpl)))) "
    using assms
    by auto

  moreover have "(SOME fid_vpr. declared_fields Pr fid_vpr = Some t \<and> tr_field fid_vpr = Some fid_bpl) = fid"
    using assms(2-)
    by (metis (mono_tags, lifting) assms(1) domI inj_onD someI_ex)

  ultimately show ?thesis
    by blast
qed

lemma construct_bpl_heap_from_vpr_heap_aux_2:
  assumes "construct_bpl_heap_from_vpr_heap Pr tr_field h (r, f) = Some v"
  shows "\<exists>a t fid fid_bpl. r = Address a \<and> 
                           declared_fields Pr fid = Some t \<and>
                           tr_field fid = Some fid_bpl \<and>
                           f = NormalField fid_bpl t \<and>                          
                           v = (val_rel_vpr_bpl (h (a, fid)))"
proof -
  from assms obtain fid_bpl t where "f = NormalField fid_bpl t"
    by (simp split: vb_field.split_asm)
    
  have  "(\<exists>loc_vpr. r = Address (fst loc_vpr) \<and>
                                    declared_fields Pr (snd loc_vpr) = Some t \<and>                                
                                    tr_field (snd loc_vpr) = Some fid_bpl)"
    using assms
    apply (simp add: \<open>f = _\<close>)
    by (meson option.distinct(1))

  from this obtain a fid_vpr where "r = Address a" and 
                           *: "declared_fields Pr fid_vpr = Some t" and 
                           **: "tr_field fid_vpr = Some fid_bpl"
    by auto

  hence
  ***: "construct_bpl_heap_from_vpr_heap Pr tr_field h (Address a, f) =
       Some (val_rel_vpr_bpl (h (a, (SOME fid_vpr. declared_fields Pr fid_vpr = Some t \<and> tr_field fid_vpr = Some fid_bpl)))) "
    by (auto simp: \<open>f = _\<close>)  
  
  with * ** obtain fid_vpr2 where 
    "declared_fields Pr fid_vpr2 = Some t" and 
    "tr_field fid_vpr2 = Some fid_bpl" and
    "fid_vpr2 = (SOME fid_vpr. declared_fields Pr fid_vpr = Some t \<and> tr_field fid_vpr = Some fid_bpl)"
    
    by (metis (mono_tags, lifting) someI2)

  thus ?thesis
    using \<open>r = _\<close> \<open>f = _\<close> *** assms
    by force
qed

lemma construct_bpl_heap_from_vpr_heap_correct_aux:
  assumes WfTyRep: "wf_ty_repr_bpl TyRep" and
          HeapWellTyVpr: "total_heap_well_typed Pr \<Delta> h" and
          DomainType: "domain_type TyRep = \<Delta>" and
          Inj: "inj_on tr_field (dom tr_field)"
        shows "let hb = construct_bpl_heap_from_vpr_heap Pr tr_field h in
              heap_rel Pr tr_field h hb \<and>
              vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
proof -
  let ?hb = "construct_bpl_heap_from_vpr_heap Pr tr_field h"

  have "heap_rel Pr tr_field h ?hb"
    unfolding heap_rel_def
  proof (rule allI | rule impI)+
    fix l :: heap_loc
    fix field_ty_vpr field_bpl
    assume "declared_fields Pr (snd l) = Some field_ty_vpr" and
           "tr_field (snd l) = Some field_bpl"

    thus "?hb (Address (fst l), NormalField field_bpl field_ty_vpr) = Some (val_rel_vpr_bpl (h l))"
      using construct_bpl_heap_from_vpr_heap_aux Inj
      by (metis prod.collapse)
  qed

  moreover have "vbpl_absval_ty_opt TyRep (AHeap ?hb) = Some ((THeapId TyRep) ,[])"
  proof (rule heap_bpl_well_typed)
    fix r f v fieldKind \<tau>_bpl
    assume "construct_bpl_heap_from_vpr_heap Pr tr_field h (r, f) = Some v" and
           FieldTyFun: "field_ty_fun_opt TyRep f = Some (TFieldId TyRep, [fieldKind, \<tau>_bpl])"

    from this obtain a \<tau>_vpr fid fid_bpl
      where "r = Address a" and 
            "tr_field fid = Some fid_bpl" and
            "declared_fields Pr fid = Some \<tau>_vpr" and
            "f = NormalField fid_bpl \<tau>_vpr" and
            "v = val_rel_vpr_bpl (h (a, fid))"
      using construct_bpl_heap_from_vpr_heap_aux_2
      by blast

    from \<open>f = _\<close> FieldTyFun have "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl"
      by simp

    moreover from HeapWellTyVpr \<open>declared_fields Pr fid = Some \<tau>_vpr\<close> have
      "has_type \<Delta> \<tau>_vpr (h (a, fid))"
      unfolding total_heap_well_typed_def
      by simp

    ultimately have "type_of_vbpl_val TyRep (val_rel_vpr_bpl (h (a, fid))) = \<tau>_bpl"
      using vpr_to_bpl_val_type has_type_get_type DomainType
      by blast
      

    thus "type_of_vbpl_val TyRep v = \<tau>_bpl"
      apply (subst \<open>v = _\<close>)
      using type_of_val_not_dummy
            vpr_to_bpl_ty_not_dummy[OF WfTyRep \<open>vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl\<close>] 
      by blast
  qed

  ultimately show ?thesis
    by presburger
qed

lemma construct_bpl_heap_from_vpr_heap_correct:
  assumes WfTyRep: "wf_ty_repr_bpl TyRep" and
          HeapWellTyVpr: "total_heap_well_typed Pr \<Delta> h" and
          DomainType: "domain_type TyRep = \<Delta>" and
          Inj: "inj_on tr_field (dom tr_field)"
  shows "\<exists>hb. heap_rel Pr tr_field h hb \<and>
              vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
  using assms construct_bpl_heap_from_vpr_heap_correct_aux
  by meson

subsection \<open>Updating the trace\<close>

\<comment>\<open>Need to update both the well-definedness and the evaluation state, because the state relation demands
that they only differ on the mask.\<close>

lemma state_rel_upd_trace_subset:
  assumes "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> wf_total_consistency ctxt_vpr StateCons StateCons_t" 
      and "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> (\<And> lbl \<phi>. t lbl = Some \<phi> \<Longrightarrow> StateCons_t \<phi>)" 
      and StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
          \<comment>\<open>the active (i.e., tracked by \<^const>\<open>label_hm_translation\<close>) labels tracked by the new trace 
             must match the previous trace\<close>
      and ActiveLabels: "\<And>lbl. lbl \<in> active_labels_hm_tr (label_hm_translation Tr) \<Longrightarrow> \<exists>\<phi>. t lbl = Some \<phi> \<and> get_trace_total \<omega> lbl = Some \<phi>"
          \<comment>\<open>All untracked members of the trace must be valid\<close>
      and UntrackedStatesValid: "\<forall>lbl \<phi>. t lbl = Some \<phi> \<longrightarrow> lbl \<notin> active_labels_hm_tr (label_hm_translation Tr) \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt (update_trace_total \<omega>def t) (update_trace_total \<omega> t) ns"
proof - 
  let ?\<Lambda> = "var_context ctxt"
  let ?FieldTr = "field_translation Tr"
  from assms have ConsistencyUpd: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_trace_total \<omega>def t) \<and> StateCons (update_trace_total \<omega> t)"
    using state_rel_consistent total_consistency_trace_update_2
    by (metis update_trace_total.simps)

  have LabelRel: 
    "label_hm_rel Pr ?\<Lambda> TyRep ?FieldTr (label_hm_translation Tr) (get_trace_total (update_trace_total \<omega> t)) ns"
    (* This should be true because the trace meets the definitions we need, see assumptions *)
  proof (subst label_hm_rel_def, (subst label_rel_def)+, intro conjI)
    show "\<forall>lbl h.
       fst (label_hm_translation Tr) lbl = Some h \<longrightarrow>
       (\<exists>\<phi>. get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi> \<and>
            heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_hh_total \<phi>) ns)"
    proof (intro allI, intro impI)
      fix lbl h
      assume LabelDefined: "fst (label_hm_translation Tr) lbl = Some h"
      hence "lbl \<in> active_labels_hm_tr (label_hm_translation Tr)"
        using active_labels_hm_tr_def by fast
      then obtain \<phi> where
        "t lbl = Some \<phi>" and
        "get_trace_total \<omega> lbl = Some \<phi>"
        using ActiveLabels by fast
      show "\<exists>\<phi>. get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi> \<and>
                heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_hh_total \<phi>) ns"
      proof (intro exI, intro conjI)
        show "get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi>"
          using \<open>t lbl = _\<close> by simp
        show "heap_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_hh_total \<phi>) ns"
          using StateRel LabelDefined \<open>get_trace_total \<omega> lbl = Some \<phi>\<close> label_tracked_implies_heap_rel state_rel_label_hm_rel
          by fast
      qed
    qed

    show "\<forall>lbl h.
       snd (label_hm_translation Tr) lbl = Some h \<longrightarrow>
       (\<exists>\<phi>. get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi> \<and>
            mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_mh_total \<phi>) ns)"
    proof (intro allI, intro impI)
      fix lbl h
      assume LabelDefined: "snd (label_hm_translation Tr) lbl = Some h"
      hence "lbl \<in> active_labels_hm_tr (label_hm_translation Tr)"
        using active_labels_hm_tr_def by fast
      then obtain \<phi> where
        "t lbl = Some \<phi>" and
        "get_trace_total \<omega> lbl = Some \<phi>"
        using ActiveLabels by fast
      show "\<exists>\<phi>. get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi> \<and>
                mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_mh_total \<phi>) ns"
      proof (intro exI, intro conjI)
        show "get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi>"
          using \<open>t lbl = _\<close> by simp
        show "mask_var_rel Pr ?\<Lambda> TyRep ?FieldTr h (get_mh_total \<phi>) ns"
          using StateRel LabelDefined \<open>get_trace_total \<omega> lbl = Some \<phi>\<close> label_tracked_implies_mask_rel state_rel_label_hm_rel
          by fast
      qed
    qed

    (* Show that all members of the trace are valid *)
    show "\<forall>lbl \<phi>. get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
    proof (intro allI, intro impI)
      fix lbl \<phi>
      assume LabelInTrace: "get_trace_total (update_trace_total \<omega> t) lbl = Some \<phi>"
      show "valid_heap_mask (get_mh_total \<phi>)"
      proof (cases "lbl \<in> active_labels_hm_tr (label_hm_translation Tr)")
        case False
        thus ?thesis
          using LabelInTrace UntrackedStatesValid by simp
      next
        case True
        hence "get_trace_total \<omega> lbl = Some \<phi>"
          using ActiveLabels LabelInTrace by fastforce
        thus ?thesis
          using StateRel state_rel_label_hm_rel label_hm_rel_def by fast
      qed
    qed
  qed

  show ?thesis
    unfolding state_rel_def state_rel0_def
    apply (intro conjI)
                     apply (insert StateRel[simplified state_rel_def state_rel0_def] ConsistencyUpd LabelRel)
                     apply (solves \<open>simp\<close>)+
                 apply (fastforce simp: store_rel_def)
                apply (solves \<open>simp\<close>)+
          apply (fastforce simp: heap_var_rel_def mask_var_rel_def)+
    done
qed

subsection \<open>State components that do not affect state relation\<close>

text \<open>The properties here will have to be adjusted once new features are added that require 
taking more state components into account. \<close>


text \<open>The following lemma will not hold once the state relation tracks predicates.\<close>

lemma state_rel_pred_independent:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns" and
          "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons \<omega>'" and
          "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'"      
          "get_hh_total_full \<omega> = get_hh_total_full \<omega>'" and
          "get_mh_total_full \<omega> = get_mh_total_full \<omega>'"         
  shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>' \<omega>' ns"
  unfolding state_rel_def state_rel0_def 
  apply (intro conjI)
                   apply (insert assms[simplified state_rel_def state_rel0_def])
                   apply (solves \<open>simp\<close>)+
               apply (fastforce simp: store_rel_def)
             apply (solves \<open>simp\<close>)+
         apply (fastforce simp: heap_var_rel_def mask_var_rel_def)+
  done

lemma state_rel_mask_pred_independent:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns"
      and "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_mp_total_full \<omega> mp)"
  shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt (update_mp_total_full \<omega> mp) (update_mp_total_full \<omega> mp) ns"
  using assms
  by (rule state_rel_pred_independent) auto

lemma state_rel_heap_pred_independent:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns"
      and "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_hp_total_full \<omega> mp)"
  shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt (update_hp_total_full \<omega> mp) (update_hp_total_full \<omega> mp) ns"
  using assms
  by (rule state_rel_pred_independent) auto


               
subsection \<open>Introducing new Boogie variables for the evaluation and well-definedness state\<close>

subsubsection \<open>Evaluation state\<close>

text \<open>The premises of the following lemma should be in-sync with the analogous lemma that updates the heap.
      If they are not in-sync, then need to change the corresponding tactics.\<close>

lemma mask_eval_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and LookupTyNewVar: "lookup_var_ty (var_context ctxt) mvar' = Some (TConSingle (TMaskId TyRep))"
      and  "mvar = mask_var Tr"      
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
\<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
      and VarFresh: "mvar' \<notin> state_rel0_disj_vars Tr AuxPred"
      and NewBoogieState: "ns' = update_var (var_context ctxt) ns mvar' (the (lookup_var (var_context ctxt) ns mvar))"
    shows "red_ast_bpl P ctxt ((BigBlock name (Assign mvar' (Var mvar)#cs) str tr, cont), Normal ns) 
                              ((BigBlock name cs str tr, cont), Normal ns') \<and>
           state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"
proof -
  from state_rel_mask_var_rel[OF StateRel]
  obtain mb where LookupVarOldVar: "lookup_var (var_context ctxt) ns mvar = Some (AbsV (AMask mb))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding mask_var_rel_def \<open>mvar = _\<close>
    by blast

  hence Eq: "ns' = update_var (var_context ctxt) ns mvar' (AbsV (AMask mb))"
    by (simp add: NewBoogieState)

  have Red: "red_ast_bpl P ctxt ((BigBlock name (Assign mvar' (Var mvar)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns')"
    unfolding Eq
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
     apply (fastforce intro: RedVar LookupVarOldVar simp: \<open>mvar = _\<close>)
    apply (simp add: TypeInterp)
    done

  have StateRel':"state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns'"
    unfolding Eq
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    by (simp add: TypeInterp)

  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar' (get_mh_total_full \<omega>) ns'"
    unfolding mask_var_rel_def Eq
    using LookupTyNewVar MaskRel
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"        
    apply (rule state_rel_mask_var_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by auto
        
  with Red show ?thesis
    by fast
qed

lemma heap_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupTyNewVar: "lookup_var_ty (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep))" and
          "hvar = heap_var Tr" and          
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>heap_var Tr\<close>.
             The proof was simpler when adding this constraint (because it allows one to do the proof
             by first treating the new variable as a new auxiliary variable)\<close>
          VarFresh: "hvar' \<notin> state_rel0_disj_vars Tr AuxPred" 
        shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign hvar' (Var hvar)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns') \<and>
                     state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"
proof -
  from state_rel_heap_var_rel[OF StateRel]
  obtain hb where LookupVarOldVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and
                  HeapTy: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and  
                  HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb" and
                  HeapTyVpr: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
    unfolding heap_var_rel_def
    by blast

  let ?ns' = "update_var (var_context ctxt) ns hvar' (AbsV (AHeap hb))"

  have Red: "red_ast_bpl P ctxt ((BigBlock name (Assign hvar' (Var hvar)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ?ns')"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
     apply (fastforce intro: RedVar LookupVarOldVar simp: \<open>hvar = _\<close>)
    using HeapTy TypeInterp
    by simp

  have StateRel':"state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    using HeapTy TypeInterp
    by simp

  have HeapVarRel': "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar' (get_hh_total_full \<omega>) ?ns'"
    unfolding heap_var_rel_def 
    using LookupTyNewVar HeapRel HeapTy HeapTyVpr
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_heap_var_update[OF StateRel' HeapVarRel'])      
    using VarFresh
    by simp
   
  with Red show ?thesis
    by fast
qed

subsubsection \<open>Well-definedness state\<close>

text \<open>The premises of the following lemma should be in-sync with the analogous lemma that updates the heap.
      If they are not in-sync, then need to change the corresponding tactics.\<close>

text \<open>The following lemma is proved analogously to the corresponding lemma for \<^const>\<open>mask_var\<close>. 
      It would be nice to share the proofs.\<close>

lemma mask_def_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupTyNewVar: "lookup_var_ty (var_context ctxt) mvar_def' = Some (TConSingle (TMaskId TyRep))" and
          "mvar_def = mask_var_def Tr" and          
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var_def Tr\<close>.
             The proof was simpler when adding this constraint (because it allows one to do the proof
             by first treating the new variable as a new auxiliary variable) \<close>
          VarFresh: "mvar_def' \<notin> state_rel0_disj_vars Tr AuxPred"
        shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign mvar_def' (Var mvar_def)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns') \<and>
                     state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"
proof -
  from state_rel_mask_var_def_rel[OF StateRel]
  obtain mb where LookupVarOldVar: "lookup_var (var_context ctxt) ns (mask_var_def Tr) = Some (AbsV (AMask mb))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) mb"
    unfolding mask_var_rel_def
    by blast

  let ?ns' = "update_var (var_context ctxt) ns mvar_def' (AbsV (AMask mb))"

  have Red: "red_ast_bpl P ctxt ((BigBlock name (Assign mvar_def' (Var mvar_def)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ?ns')"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
     apply (fastforce intro: RedVar LookupVarOldVar simp: \<open>mvar_def = _\<close>)
    apply (simp add: TypeInterp)
    done

  have StateRel':"state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    by (simp add: TypeInterp)

  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar_def' (get_mh_total_full \<omega>def) ?ns'"
    unfolding mask_var_rel_def 
    using LookupTyNewVar MaskRel
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_mask_var_def_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by simp
        
  with Red show ?thesis
    by fast
qed

text \<open>The following lemma is proved analogously to the corresponding lemma for \<^const>\<open>heap_var\<close>. 
      It would be nice to share the proofs.\<close>

lemma heap_def_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupTyNewVar: "lookup_var_ty (var_context ctxt) hvar_def' = Some (TConSingle (THeapId TyRep))" and
          "hvar_def = heap_var_def Tr" and          
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
         \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>heap_var_def Tr\<close>.
           The proof was simpler when adding this constraint (because it allows one to do the proof
           by first treating the new variable as a new auxiliary variable) \<close>
          VarFresh: "hvar_def' \<notin> state_rel0_disj_vars Tr AuxPred" 
        shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign hvar_def' (Var hvar_def)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns') \<and>
                     state_rel Pr StateCons TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"
proof -
  from state_rel_heap_var_def_rel[OF StateRel]
  obtain hb where LookupVarOldVar: "lookup_var (var_context ctxt) ns (heap_var_def Tr) = Some (AbsV (AHeap hb))" and
                  HeapTy: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and  
                  HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>def) hb" and
                  HeapTyVpr: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
    unfolding heap_var_rel_def
    by blast

  let ?ns' = "update_var (var_context ctxt) ns hvar_def' (AbsV (AHeap hb))"

  have Red: "red_ast_bpl P ctxt ((BigBlock name (Assign hvar_def' (Var hvar_def)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ?ns')"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
     apply (fastforce intro: RedVar LookupVarOldVar simp: \<open>hvar_def = _\<close>)
    using HeapTy TypeInterp
    by simp

  have StateRel':"state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    using HeapTy TypeInterp
    by simp

  have HeapVarRel': "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar_def' (get_hh_total_full \<omega>def) ?ns'"
    unfolding heap_var_rel_def 
    using LookupTyNewVar HeapRel HeapTy HeapTyVpr
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_heap_var_def_update[OF StateRel' HeapVarRel'])      
    using VarFresh
    by simp
   
  with Red show ?thesis
    by fast
qed

subsection \<open>Updating the definedness and evaluation state\<close>

lemma mask_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupTyNewVar: "lookup_var_ty (var_context ctxt) mvar' = Some (TConSingle (TMaskId TyRep))" and
          WfMask:         "wf_mask_simple mh'" and
          Consistent: "(consistent_state_rel_opt (state_rel_opt Tr)) \<Longrightarrow> 
                        StateCons (update_mh_total_full \<omega> mh') \<and> StateCons (update_mh_total_full \<omega>def mh')" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and          
          Disj: "mvar' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union> 
                      vars_label_hm_tr (label_hm_translation Tr))" and
        RedRhsBpl:  "red_expr_bpl ctxt e_bpl ns (AbsV (AMask mbpl'))" and
        MaskRel:    "mask_rel Pr (field_translation Tr) mh' mbpl'"
        shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign mvar' e_bpl#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns') \<and>
                     state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt (update_mh_total_full \<omega>def mh') (update_mh_total_full \<omega> mh') ns'"
proof -

  let ?\<omega>' = "update_mh_total_full \<omega> mh'"
  let ?\<omega>def' = "update_mh_total_full \<omega>def mh'"
  let ?ns' = "update_var (var_context ctxt) ns mvar' (AbsV (AMask mbpl'))"

  have Red: "red_ast_bpl P ctxt   ((BigBlock name ((Assign mvar' e_bpl)#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ?ns')"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar RedRhsBpl])
    apply (simp add: TypeInterp)
    done

  have BinderEmpty: "binder_state ns = Map.empty"
    using StateRel
    by (simp add: state_rel_def state_rel0_def state_well_typed_def)

  have StateRel':"state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt ?\<omega>def' ?\<omega>' ?ns'"
    apply (rule state_rel_mask_update_wip[OF StateRel TypeInterp])
               apply simp
    using mask_var_disjoint[OF state_rel_state_rel0[OF StateRel]] Disj
              apply simp
             apply (rule update_mh_m_total)
    using state_rel_eval_welldef_eq[OF StateRel]
            apply simp

           apply simp
          apply (simp add: WfMask)
           apply (simp add: WfMask)
          apply (erule Consistent)
        apply (fastforce simp: mask_var_rel_def intro: LookupTyNewVar MaskRel)
       apply (fastforce simp: mask_var_rel_def intro: LookupTyNewVar MaskRel)
      apply (metis global_state_update_local global_state_update_other option.exhaust)
         apply (simp add: update_var_old_global_same)
    using BinderEmpty
    by (simp add: update_var_binder_same)

  show ?thesis
    using Red StateRel'
    by blast
qed

lemma heap_var_eval_def_havoc_upd_red_ast_bpl_propagate:
  assumes 
          StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupDeclNewVar: "lookup_var_decl (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep), None)" and
          Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> 
                       StateCons (update_hh_total_full \<omega>def hh') \<and> StateCons (update_hh_total_full \<omega> hh')" and 
          WfTyRep: "wf_ty_repr_bpl TyRep" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          TotalHeapWellTy: "total_heap_well_typed Pr (domain_type TyRep) hh'" and
          VarFresh: "hvar' \<notin> 
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred \<union>
                      vars_label_hm_tr (label_hm_translation Tr)" 
        shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Havoc hvar'#cs) str tr, cont), Normal ns) 
                                  ((BigBlock name cs str tr, cont), Normal ns') \<and>
                     state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', heap_var_def := hvar'\<rparr>) AuxPred ctxt (update_hh_total_full \<omega>def hh') (update_hh_total_full \<omega> hh') ns'"
proof -
  from state_rel_field_rel[OF StateRel] 
  have Inj: "inj_on (field_translation Tr) (dom (field_translation Tr))"
    unfolding field_rel_def
    by blast

  from construct_bpl_heap_from_vpr_heap_correct[OF WfTyRep TotalHeapWellTy _ Inj ] obtain hb where
        HeapRel: "heap_rel Pr (field_translation Tr) hh' hb" and
        HeapTyBpl: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])"
    by blast

  let ?ns' = "update_var (var_context ctxt) ns hvar' (AbsV (AHeap hb))"

  have HeapSameEvalDef: "get_h_total_full \<omega>def = get_h_total_full \<omega>"
    using StateRel
    by (simp add: state_rel_def state_rel0_def)

  hence HeapPredSameEvalDef: "get_hp_total_full \<omega>def = get_hp_total_full \<omega>"
    by simp

  have HeapVarRel: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar' hh' ?ns'"
    unfolding heap_var_rel_def
    using lookup_var_decl_ty_Some LookupDeclNewVar HeapTyBpl HeapRel TotalHeapWellTy
    by auto

  hence HeapVarRelDef: "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar' hh' ?ns'"
    by (rule heap_var_rel_stable) auto
  have BinderEmpty: "binder_state ns = Map.empty"
    using StateRel
    by (simp add: state_rel_def state_rel0_def state_well_typed_def)

  have StateRel': "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', heap_var_def := hvar'\<rparr>) AuxPred ctxt (update_hh_total_full \<omega>def hh') (update_hh_total_full \<omega> hh') ?ns'" 
    apply (rule state_rel_heap_update[OF StateRel TypeInterp])
             apply blast
    using VarFresh
            apply blast
           apply (rule update_hh_h_total)
          apply (subst HeapPredSameEvalDef)
            apply (rule update_hh_h_total)
           apply (erule Consistent)
         apply simp
        apply (simp add: HeapVarRel)
       apply (simp add: HeapVarRelDef)    
      apply (metis LookupDeclNewVar global_state_update_local global_state_update_other lookup_var_decl_local_2)
     apply (simp add: update_var_old_global_same)
    using BinderEmpty
    by (simp add: update_var_binder_same)

  show ?thesis
    apply (rule exI)
    apply (rule conjI[OF _ StateRel'])
    apply (rule red_ast_bpl_one_havoc[OF LookupDeclNewVar])
     apply (subst TypeInterp)
    using HeapTyBpl
     apply simp
    by simp
qed

lemma state_rel_active_label_exists:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and "lbl \<in> active_labels_hm_tr (label_hm_translation Tr)"
    shows "\<exists>\<phi>. get_trace_total \<omega> lbl = Some \<phi>"
  using state_rel_label_hm_rel[OF StateRel, simplified label_hm_rel_def label_rel_def] \<open>lbl \<in> _\<close>[simplified active_labels_hm_tr_def]
  by blast

lemma post_framing_propagate_aux:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>0 \<omega>0 ns" and
          WfTyRep: "wf_ty_repr_bpl TyRep" and
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          StoreSame: "get_store_total \<omega>0 = get_store_total \<omega>1" and
          OldStateSame: "get_trace_total \<omega>1 old_label = get_trace_total \<omega>0 old_label" and
          DomLabelMap: "active_labels_hm_tr (label_hm_translation Tr) \<subseteq> {old_label}" and
          WfMask: "wf_mask_simple (get_mh_total_full \<omega>1)" and
          Consistent: "StateCons \<omega>1" and
          HeapWellTy: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>1)" and
          LookupDeclHeap: "lookup_var_decl (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep), None)" and
          LookupTyMask: "lookup_var_ty (var_context ctxt) mvar' = Some (TConSingle (TMaskId TyRep))" and
          RedMaskBpl: "\<And>\<omega>0  \<omega> ns hvar hvar'. state_rel Pr StateCons TyRep ((disable_consistent_state_rel_opt Tr)\<lparr>heap_var := hvar, heap_var_def := hvar'\<rparr>) AuxPred ctxt \<omega>0 \<omega> ns \<Longrightarrow>
                                    red_expr_bpl ctxt e_bpl ns (AbsV (AMask mbpl'))" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>1) mbpl'" and
                \<comment>\<open> could weaken the disjointness condition such that the heap and mask variable can 
                    stay the same\<close>
          Disj: "{hvar', mvar'} \<inter> ({heap_var Tr, heap_var_def Tr} \<union> 
                              {mask_var Tr, mask_var_def Tr} \<union>
                              (ran (var_translation Tr)) \<union>
                              (ran (field_translation Tr)) \<union>
                              (range (const_repr Tr)) \<union>
                              dom AuxPred \<union>
                              vars_label_hm_tr (label_hm_translation Tr)) = {}" (is "?A \<inter> ?B = {}") and
                "hvar' \<noteq> mvar'"
  shows  "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Havoc hvar'#Assign mvar' e_bpl#cs) str tr, cont), Normal ns) 
                            ((BigBlock name cs str tr, cont), Normal ns') \<and>
                state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt \<omega>1 \<omega>1 ns'"
proof -
  from Disj have "hvar' \<notin> ?B" and "mvar' \<notin> ?B"
    by fast+
                            
  let ?hh' = "get_hh_total_full \<omega>1"
  let ?mh' = "get_mh_total_full \<omega>1"

  \<comment>\<open>We temporarily disable the state consistency so that we can reason about the heap and mask updates separately
     (the intermediate states may not be consistent).\<close>
  let ?Tr' = "disable_consistent_state_rel_opt Tr"
  from heap_var_eval_def_havoc_upd_red_ast_bpl_propagate[OF state_rel_disable_consistency[OF StateRel] LookupDeclHeap _ WfTyRep TypeInterp HeapWellTy ] \<open>hvar' \<notin> ?B\<close> obtain ns'
    where RedBpl1: "red_ast_bpl P ctxt ((BigBlock name (Havoc hvar'#Assign mvar' e_bpl#cs) str tr, cont), Normal ns) 
                            ((BigBlock name (Assign mvar' e_bpl#cs) str tr, cont), Normal ns')" and
          StateRel1: "state_rel Pr StateCons TyRep (?Tr'\<lparr>heap_var := hvar', heap_var_def := hvar'\<rparr>) AuxPred ctxt (update_hh_total_full \<omega>0 ?hh') (update_hh_total_full \<omega>0 ?hh') ns'"
    by force

  let ?\<omega>' = "(update_mh_total_full (update_hh_total_full \<omega>0 (get_hh_total_full \<omega>1)) ?mh')"

  from mask_var_upd_red_ast_bpl_propagate[OF StateRel1 LookupTyMask WfMask _ TypeInterp _ RedMaskBpl[OF StateRel1] ]
  obtain ns'' where
     RedBpl2: "red_ast_bpl P ctxt ((BigBlock name (Assign mvar' e_bpl # cs) str tr, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal ns'')" and
     StateRel2: "state_rel Pr StateCons TyRep (?Tr'\<lparr>heap_var := hvar', heap_var_def := hvar', mask_var := mvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt ?\<omega>' ?\<omega>' ns''"
    using \<open>mvar' \<notin> _\<close> \<open>hvar' \<noteq> mvar'\<close> MaskRel
    by force    

  have Aux:"?Tr'\<lparr>heap_var := hvar', heap_var_def := hvar', mask_var := mvar', mask_var_def := mvar'\<rparr> = ?Tr'\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>"
    by simp

  have StateRel3: "state_rel Pr StateCons TyRep (?Tr'\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt ?\<omega>' ?\<omega>' ns''"
    using StateRel2 Aux
    by argo
    
  let ?\<omega>'' = "update_trace_total (update_hp_total_full (update_mp_total_full ?\<omega>' (get_mp_total_full \<omega>1)) (get_hp_total_full \<omega>1)) (get_trace_total \<omega>1)"

  have
    StateRel4: "state_rel Pr StateCons TyRep (?Tr'\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt ?\<omega>'' ?\<omega>'' ns''"
  proof -
    have *: "\<And>lbl. lbl \<in> active_labels_hm_tr (label_hm_translation Tr) \<Longrightarrow> \<exists>\<phi>. get_trace_total \<omega>1 lbl = Some \<phi> \<and> get_trace_total \<omega>0 lbl = Some \<phi>"
      using DomLabelMap state_rel_active_label_exists[OF StateRel] OldStateSame
      by auto

    have UntrackedStatesValid: "\<forall>lbl \<phi>. get_trace_total \<omega>1 lbl = Some \<phi> \<longrightarrow> lbl \<notin> active_labels_hm_tr (label_hm_translation Tr) \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
    proof (intro allI, intro impI)
      fix lbl \<phi>
      assume "get_trace_total \<omega>1 lbl = Some \<phi>"
         and "lbl \<notin> active_labels_hm_tr (label_hm_translation Tr)"
      show "valid_heap_mask (get_mh_total \<phi>)"
        (* TODO how to prove this *)
        sorry
    qed

    show ?thesis
    apply (rule state_rel_upd_trace_subset[OF _ _ state_rel_heap_pred_independent[OF state_rel_mask_pred_independent[OF StateRel3]]])
      by (simp_all add: * UntrackedStatesValid)
  qed

  \<comment>\<open>Here, we reenable the state consistency using the consistency assumption on the final state.\<close>

  have "?\<omega>'' = \<omega>1"
    apply (rule full_total_state.equality)
       apply (simp add:  StoreSame)
      apply simp
     apply (rule total_state.equality)
    by auto

  hence  "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt \<omega>1 \<omega>1 ns''"
    using state_rel_enable_consistency_2[OF StateRel4] Consistent
    by auto

  thus ?thesis
    using RedBpl1 RedBpl2 red_ast_bpl_transitive state_rel_enable_consistency Consistent
    by blast
qed


subsection \<open>Tracking states in the auxiliary variables\<close>

definition pred_eq_mask
  where "pred_eq_mask Pr TyRep FieldTr ctxt m \<omega> v \<equiv> 
            lookup_var_ty (var_context ctxt) m = Some (TConSingle (TMaskId TyRep)) \<and>
            (\<exists>mb. v = AbsV (AMask mb) \<and> mask_rel Pr FieldTr (get_mh_total_full \<omega>) mb)"


definition pred_eq_heap_aux
  where "pred_eq_heap_aux Pr TyRep FieldTr \<omega> hb \<equiv>
               vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[]) \<and>
               heap_rel Pr FieldTr (get_hh_total_full \<omega>) hb"


definition pred_eq_heap
  where "pred_eq_heap Pr TyRep FieldTr ctxt h \<omega> v \<equiv> 
           lookup_var_ty (var_context ctxt) h = Some (TConSingle (THeapId TyRep)) \<and>
           (\<exists>hb. v = AbsV (AHeap hb) \<and>
                                         pred_eq_heap_aux Pr TyRep FieldTr \<omega> hb) \<and>
                                    total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"

definition aux_pred_capture_state
  where "aux_pred_capture_state Pr TyRep FieldTr AuxPred ctxt m h \<omega> \<equiv>
           AuxPred(m \<mapsto> pred_eq_mask Pr TyRep FieldTr ctxt m \<omega>)
                  (h \<mapsto> pred_eq_heap Pr TyRep FieldTr ctxt h \<omega>)"

lemma aux_pred_capture_state_dom: 
  "dom (aux_pred_capture_state Pr TyRep Tr AuxPred ctxt m h \<omega>) = dom AuxPred \<union> {m,h}"
  unfolding aux_pred_capture_state_def
  by auto

find_theorems dom map_upd_set

abbreviation state_rel_capture_total_state :: \<comment>\<open>make type explicit to ensure that the Viper states have the same type\<close>
 "program
     \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
        \<Rightarrow> 'a ty_repr_bpl
           \<Rightarrow> tr_vpr_bpl
             \<Rightarrow> (field_ident \<rightharpoonup> Lang.vname)
              \<Rightarrow> (nat \<Rightarrow> ('a vbpl_absval Semantics.val \<Rightarrow> bool) option)
                 \<Rightarrow> ('a vbpl_absval, 'b) econtext_bpl_general_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a vbpl_absval nstate \<Rightarrow> bool"
  where "state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred ctxt m h \<omega> \<equiv> 
          state_rel Pr StateCons TyRep Tr 
                         (aux_pred_capture_state Pr TyRep FieldTr0 AuxPred ctxt m h \<omega>)
                         ctxt"

lemma state_rel_capture_total_stateI:
  assumes "state_rel Pr StateCons TyRep Tr AuxPred' ctxt \<omega>def \<omega> ns"
      and "AuxPred' = (AuxPred(m \<mapsto> pred_eq_mask Pr TyRep FieldTr0 ctxt m \<omega>0)
                              (h \<mapsto> pred_eq_heap Pr TyRep FieldTr0 ctxt h \<omega>0))"
    shows "state_rel_capture_total_state Pr StateCons TyRep Tr FieldTr0 AuxPred  ctxt m h \<omega>0 \<omega>def \<omega> ns"
  using assms
  unfolding aux_pred_capture_state_def
  by simp

lemma state_rel_capture_current_mask:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and LookupVarTy: "lookup_var_ty (var_context ctxt) m' = Some (TConSingle (TMaskId TyRep))"
      and LookupMaskVarSame: "lookup_var (var_context ctxt) ns m' = lookup_var (var_context ctxt) ns (mask_var Tr)"
      and "m' \<notin> state_rel0_disj_vars Tr AuxPred"
      and FieldTr: "field_tr = field_translation Tr"
    shows "state_rel Pr StateCons TyRep Tr (AuxPred(m' \<mapsto> pred_eq_mask Pr TyRep field_tr ctxt m' \<omega>)) ctxt \<omega>def \<omega> ns"
proof -
  from state_rel_mask_var_rel[OF StateRel] obtain mb where
    MaskVarRel: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb)) \<and> 
                 mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding mask_var_rel_def
    by blast

  let ?ns' = "update_var (var_context ctxt) ns m' (AbsV (AMask mb))"

  have "ns = ?ns'"
    using LookupMaskVarSame
    by (simp add: MaskVarRel update_var_same_state)

  moreover have "state_rel Pr StateCons TyRep Tr (AuxPred(m' \<mapsto> pred_eq_mask Pr TyRep (field_translation Tr) ctxt m' \<omega>)) ctxt \<omega>def \<omega> ?ns'"
  proof (rule state_rel_new_auxvar[OF StateRel \<open>m' \<notin> _\<close>])
    show "pred_eq_mask Pr TyRep (field_translation Tr) ctxt m' \<omega> (AbsV (AMask mb))"
      unfolding pred_eq_mask_def
      using MaskVarRel LookupVarTy
      by simp
  next 
    show "lookup_var_ty (var_context ctxt) m' = Some (TConSingle (TMaskId TyRep))"
      by (rule LookupVarTy)
  qed (insert TypeInterp, simp_all)

  ultimately show ?thesis
    by (simp add: FieldTr)
qed

lemma state_rel_def_same_set_synchronize_mask_var:
  assumes StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and Cases: "mvar' = mask_var Tr \<or> mvar' = mask_var_def Tr"
    shows "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> mask_var := mvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt \<omega> ns"
proof -  
  show ?thesis
  proof (cases rule: disjE[OF Cases])
    case 1
    have "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> mask_var_def := mvar' \<rparr>) AuxPred ctxt \<omega> ns"
      apply (rule state_rel_mask_var_def_update[OF StateRel])
      using state_rel_mask_var_rel[OF StateRel] \<open>mvar' = _\<close>      
       apply simp
      using state_rel_mask_var_disjoint[OF StateRel, where ?mvar = mvar'] \<open>mvar' = _\<close>
      by fast
    then show ?thesis 
      using \<open>mvar' = _\<close>
      by simp
  next
    case 2
    have "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> mask_var := mvar' \<rparr>) AuxPred ctxt \<omega> ns"
      apply (rule state_rel_mask_var_update[OF StateRel])
      using state_rel_mask_var_def_rel[OF StateRel] \<open>mvar' = _\<close>
       apply simp
      using state_rel_mask_var_disjoint[OF StateRel, where ?mvar = mvar'] \<open>mvar' = _\<close>
      by fast
    then show ?thesis 
      using \<open>mvar' = _\<close>
      by simp
  qed
qed

lemma state_rel_def_same_set_synchronize_heap_var:
  assumes StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and Cases: "hvar' = heap_var Tr \<or> hvar' = heap_var_def Tr"
    shows "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> heap_var := hvar', heap_var_def := hvar'\<rparr>) AuxPred ctxt \<omega> ns"
proof -  
  show ?thesis
  proof (cases rule: disjE[OF Cases])
    case 1
    have "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> heap_var_def := hvar' \<rparr>) AuxPred ctxt \<omega> ns"
      apply (rule state_rel_heap_var_def_update[OF StateRel])
      using state_rel_heap_var_rel[OF StateRel] \<open>hvar' = _\<close>      
       apply simp
      using state_rel_heap_var_disjoint[OF StateRel, where ?hvar = hvar'] \<open>hvar' = _\<close>
      by fast
    then show ?thesis 
      using \<open>hvar' = _\<close>
      by simp
  next
    case 2
    have "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> heap_var := hvar' \<rparr>) AuxPred ctxt \<omega> ns"
      apply (rule state_rel_heap_var_update[OF StateRel])
      using state_rel_heap_var_def_rel[OF StateRel] \<open>hvar' = _\<close>
       apply simp
      using state_rel_heap_var_disjoint[OF StateRel, where ?hvar = hvar'] \<open>hvar' = _\<close>
      by fast
    then show ?thesis 
      using \<open>hvar' = _\<close>
      by simp
  qed
qed

lemma mask_eval_var_upd_red_ast_bpl_propagate_capture:
  assumes StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and LookupTyNewVar: "lookup_var_ty (var_context ctxt) mvar' = Some (TConSingle (TMaskId TyRep))"
      and  "mvar = mask_var Tr"      
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var Tr\<close>.
         The proof was simpler when adding this constraint (because it allows one to do the proof
         by first treating the new variable as a new auxiliary variable) \<close>
      and VarFresh: "mvar' \<notin> state_rel0_disj_vars Tr AuxPred"
    shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign mvar' (Var mvar)#cs) str tr, cont), Normal ns) 
                              ((BigBlock name cs str tr, cont), Normal ns') \<and>
           state_rel_def_same Pr StateCons TyRep (Tr\<lparr>mask_var := mvar', mask_var_def := mvar'\<rparr>) (AuxPred(mvar \<mapsto> pred_eq_mask Pr TyRep (field_translation Tr) ctxt mvar \<omega>)) ctxt \<omega> ns'"
           (is "\<exists>ns'. ?GoalRed ns' \<and> ?GoalStateRel ns'")
proof -
  from state_rel_mask_var_rel[OF StateRel]
  obtain mb where LookupVarOldVar: "lookup_var (var_context ctxt) ns mvar = Some (AbsV (AMask mb))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding mask_var_rel_def \<open>mvar = _\<close>
    by blast

  let ?ns' = "update_var (var_context ctxt) ns mvar' (AbsV (AMask mb))"

  have Red: "?GoalRed ?ns'"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
    apply (simp add: LookupVarOldVar red_expr_red_exprs.RedVar)
    apply (simp add: TypeInterp)
    done

  have StateRel':"state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ?ns'"
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    by (simp add: TypeInterp)


  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar' (get_mh_total_full \<omega>) ?ns'"
    unfolding mask_var_rel_def
    using LookupTyNewVar MaskRel
    by fastforce

  have StateRelAux: "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega> ?ns'"        
    apply (rule state_rel_mask_var_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by simp

  have StateRel': "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>mask_var := mvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt \<omega> ?ns'"
    using state_rel_def_same_set_synchronize_mask_var[OF StateRelAux, where ?mvar' = mvar']
    by simp

  have "?GoalStateRel ?ns'"
  proof (rule state_rel_capture_current_mask[OF StateRel'], simp_all)
    show "lookup_var_ty (var_context ctxt) mvar = Some (TConSingle (TMaskId TyRep))"
      using state_rel_mask_var_rel[OF StateRel, simplified mask_var_rel_def] \<open>mvar = _\<close>
      by fast
  qed (insert TypeInterp state_rel_mask_var_disjoint[OF StateRel, where ?mvar=mvar] \<open>mvar = _\<close> VarFresh LookupVarOldVar, simp_all)
      
  with \<open>?GoalRed ?ns'\<close> show ?thesis
    by blast
qed


lemma state_rel_capture_current_heap:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and LookupVarTy: "lookup_var_ty (var_context ctxt) h' = Some (TConSingle (THeapId TyRep))"
      and LookupHeapVarSame: "lookup_var (var_context ctxt) ns h' = lookup_var (var_context ctxt) ns (heap_var Tr)"
      and "h' \<notin> state_rel0_disj_vars Tr AuxPred"
      and FieldTr: "field_tr = field_translation Tr"
    shows "state_rel Pr StateCons TyRep Tr (AuxPred(h' \<mapsto> pred_eq_heap Pr TyRep field_tr ctxt h' \<omega>)) ctxt \<omega>def \<omega> ns"
proof -
  from state_rel_heap_var_rel[OF StateRel] obtain hb where
    HeapVarRel: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and> 
                 vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
                 heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb \<and>
                 total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
    unfolding heap_var_rel_def
    by blast

  let ?ns' = "update_var (var_context ctxt) ns h' (AbsV (AHeap hb))"

  have "ns = ?ns'"
    using LookupHeapVarSame
    by (simp add: HeapVarRel update_var_same_state)

  moreover have "state_rel Pr StateCons TyRep Tr (AuxPred(h' \<mapsto> pred_eq_heap Pr TyRep (field_translation Tr) ctxt h' \<omega>)) ctxt \<omega>def \<omega> ?ns'"
  proof (rule state_rel_new_auxvar[OF StateRel \<open>h' \<notin> _\<close>])
    show "pred_eq_heap Pr TyRep (field_translation Tr) ctxt h' \<omega> (AbsV (AHeap hb))"
      unfolding pred_eq_heap_def pred_eq_heap_aux_def      
      using HeapVarRel LookupVarTy
      by blast
  next
    show "lookup_var_ty (var_context ctxt) h' = Some (TConSingle (THeapId TyRep))"
      by (rule LookupVarTy)
  next
    show "type_of_val (type_interp ctxt) (AbsV (AHeap hb)) = TConSingle (THeapId TyRep)"
      using HeapVarRel
      by (metis LookupHeapVarSame LookupVarTy StateRel instantiate_nil option.sel state_rel_state_well_typed state_well_typed_lookup)  
  qed (insert TypeInterp, simp_all)

  ultimately show ?thesis
    by (simp add: FieldTr)
qed

lemma heap_eval_var_upd_red_ast_bpl_propagate_capture:
  assumes StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
      and LookupTyNewVar: "lookup_var_ty (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep))"
      and  "hvar = heap_var Tr"      
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and VarFresh:  
          "hvar' \<notin> state_rel0_disj_vars Tr AuxPred"
    shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name (Assign hvar' (Var hvar)#cs) str tr, cont), Normal ns) 
                              ((BigBlock name cs str tr, cont), Normal ns') \<and>
           state_rel_def_same Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', heap_var_def := hvar'\<rparr>) (AuxPred(hvar \<mapsto> pred_eq_heap Pr TyRep (field_translation Tr) ctxt hvar \<omega>)) ctxt \<omega> ns'"
           (is "\<exists>ns'. ?GoalRed ns' \<and> ?GoalStateRel ns'")
proof -
  from state_rel_heap_var_rel[OF StateRel, simplified heap_var_rel_def]
  obtain hb where LookupVarOldVar: "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb))" and                  
                  ValTyOpt: "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
                  HeapRel:  "ViperBoogieBasicRel.heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb" and
                  TotalHeapWellTy: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
  by blast

  let ?ns' = "update_var (var_context ctxt) ns hvar' (AbsV (AHeap hb))"

  have Red: "?GoalRed ?ns'"
    apply (rule red_ast_bpl_one_assign[OF LookupTyNewVar])
     apply (simp add: LookupVarOldVar red_expr_red_exprs.RedVar \<open>hvar = _\<close>)
    using TypeInterp ValTyOpt ViperBoogieAbsValueInst.type_of_vbpl_val_case_of
    by simp    

  have StateRel':"state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ?ns'"
    apply (rule state_rel_independent_var[OF StateRel])
    using VarFresh
       apply blast
      apply (simp add: TypeInterp)
     apply (rule LookupTyNewVar)
    using TypeInterp ValTyOpt ViperBoogieAbsValueInst.type_of_vbpl_val_case_of
    by simp

  have HeapVarRel': "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) hvar' (get_hh_total_full \<omega>) ?ns'"
    unfolding heap_var_rel_def
    using LookupTyNewVar ValTyOpt HeapRel TotalHeapWellTy
    by simp

  have StateRelAux: "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>heap_var := hvar'\<rparr>) AuxPred ctxt \<omega> ?ns'"        
    apply (rule state_rel_heap_var_update[OF StateRel' HeapVarRel'])
    using VarFresh
    by simp

  have StateRel': "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', heap_var_def := hvar'\<rparr>) AuxPred ctxt \<omega> ?ns'"
    using state_rel_def_same_set_synchronize_heap_var[OF StateRelAux, where ?hvar' = hvar']
    by simp

  have "?GoalStateRel ?ns'"
  proof (rule state_rel_capture_current_heap[OF StateRel'], simp_all)
    show "lookup_var_ty (var_context ctxt) hvar = Some (TConSingle (THeapId TyRep))"
      using state_rel_heap_var_rel[OF StateRel, simplified heap_var_rel_def] \<open>hvar = _\<close>
      by fast
  qed (insert TypeInterp state_rel_heap_var_disjoint[OF StateRel, where ?hvar=hvar] \<open>hvar = _\<close> VarFresh LookupVarOldVar, simp_all)
      
  with \<open>?GoalRed ?ns'\<close> show ?thesis
    by blast
qed

lemma state_rel_capture_total_state_change_eval_and_def_state:
  assumes AuxPred': "AuxPred' = AuxPred 
                            (mdef \<mapsto> pred_eq_mask Pr TyRep FieldTr ctxt mdef \<omega>def)
                            (hdef \<mapsto> pred_eq_heap Pr TyRep FieldTr ctxt hdef \<omega>def)
                            (m \<mapsto> pred_eq_mask Pr TyRep FieldTr ctxt m (\<omega> :: 'a full_total_state))                    
                            (h \<mapsto> pred_eq_heap Pr TyRep FieldTr ctxt h \<omega>)"
      and ValidHeapMask: "valid_heap_mask (get_mh_total_full \<omega>def) \<and> valid_heap_mask (get_mh_total_full \<omega>)"
      and Consistent: "consistent_state_rel_opt (state_rel_opt Tr) \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>"
      (* Added these two assumptions so that we can know that these only differ on the total state *)
      (* Should we re-frame this by defining \<omega>def in terms of \<omega>def_old? *)
      and "\<omega>def = \<omega>def_old \<lparr> get_total_full := \<phi>def_old \<rparr>"
      and "\<omega>   = \<omega>_old     \<lparr> get_total_full := \<phi>_old \<rparr>"
      and SameHeap: "get_h_total_full \<omega>def = get_h_total_full \<omega>"
      (* Do we need additional assumptions about the "current" state? e.g. that it is well-formed *)
      and StateRel: "state_rel Pr StateCons TyRep Tr' AuxPred' ctxt \<omega>def_old \<omega>_old ns"
      (* May not actually need these two *)
      and MaskRelEquiv: "mdef = m \<Longrightarrow> (\<And>mb :: 'a bpl_mask_ty.  
                                             (mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>)  mb) \<longleftrightarrow>
                                             (mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) mb))"
      and HeapRelEquiv: "hdef = h \<Longrightarrow> (\<And>hb :: 'a bpl_heap_ty.  
                                             (pred_eq_heap_aux Pr TyRep (field_translation Tr) \<omega> hb =
                                              pred_eq_heap_aux Pr TyRep (field_translation Tr) \<omega>def hb) \<and>
                                             (total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>) \<longleftrightarrow>
                                              total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)))"
      and DisjMaskHeap: "{m,mdef} \<inter> {h,hdef} = {}"
      and "FieldTr = field_translation Tr"
      and DisjAuxPred: "{m,h,mdef,hdef} \<inter> dom AuxPred = {}"
      and "Tr = Tr' \<lparr> mask_var := m, heap_var := h, mask_var_def := mdef, heap_var_def := hdef \<rparr>"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
proof -
  let ?\<Lambda> = "var_context ctxt"
  from state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=m] DisjMaskHeap
  obtain mb where LookupMask: "lookup_var (var_context ctxt) ns m = Some (AbsV (AMask mb))" and
                  LookupVarTyMask: "lookup_var_ty (var_context ctxt) m = Some (TConSingle (TMaskId TyRep))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    using \<open>FieldTr = _\<close> \<open>AuxPred' =_\<close>
    unfolding pred_eq_mask_def 
    by auto

  from state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=h] DisjMaskHeap
  obtain hb where LookupVarTyHeap: "lookup_var_ty (var_context ctxt) h = Some (TConSingle (THeapId TyRep))" and
                  LookupHeap: "lookup_var (var_context ctxt) ns h = Some (AbsV (AHeap hb))" and
                  PredEqHeapAux: "pred_eq_heap_aux Pr TyRep (field_translation Tr) \<omega> hb" and
                  TotalHeapWellTy: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>)"
    using \<open>FieldTr = _\<close> \<open>AuxPred' =_\<close>
    unfolding pred_eq_heap_def \<open>Tr = _\<close> 
    by auto  

  obtain mbdef where 
              LookupMaskDef: "lookup_var (var_context ctxt) ns mdef = Some (AbsV (AMask mbdef))" and
              LookupVarTyMaskDef: "lookup_var_ty (var_context ctxt) mdef = Some (TConSingle (TMaskId TyRep))" and
              MaskRelDef: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>def) mbdef" 
  proof (cases "mdef = m")
    case True
    with that[where ?mbdef = mb] show ?thesis 
      using LookupMask LookupVarTyMask MaskRel MaskRelEquiv
      by fast
  next
    case False
    hence Pred: "AuxPred' mdef = Some (pred_eq_mask Pr TyRep FieldTr ctxt mdef \<omega>def)"
      using \<open>AuxPred' =_\<close> DisjMaskHeap
      by simp
    with that state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=mdef, OF Pred] 
    show ?thesis
      using \<open>FieldTr = _\<close>
      unfolding pred_eq_mask_def 
      by blast
  qed
      
  obtain hbdef where 
        LookupVarTyHeapDef: "lookup_var_ty (var_context ctxt) hdef = Some (TConSingle (THeapId TyRep))" and
        LookupHeapDef: "lookup_var (var_context ctxt) ns hdef = Some (AbsV (AHeap hbdef))" and
        PredEqHeapAuxDef: "pred_eq_heap_aux Pr TyRep (field_translation Tr) \<omega>def hbdef" and
        TotalHeapWellTyDef: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
  proof (cases "hdef = h")
    case True
    with that[where ?hbdef = hb, simplified True, OF LookupVarTyHeap LookupHeap] show ?thesis 
      using LookupVarTyHeap LookupHeap PredEqHeapAux TotalHeapWellTy HeapRelEquiv
      by auto      
  next
    case False
    hence Pred: "AuxPred' hdef = Some (pred_eq_heap Pr TyRep FieldTr ctxt hdef \<omega>def)"
      using \<open>AuxPred' =_\<close> DisjMaskHeap
      by simp
    with that state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=hdef, OF Pred] 
    show ?thesis
      using \<open>FieldTr = _\<close>
      unfolding pred_eq_heap_def 
      by blast
  qed

  (* mask_rel \<omega> m and mask_rel \<omega>def mdef and m = mdef should imply
     get_mh_total \<omega> and get_mh_total \<omega>def are the same on the relevant locations *)
  show "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  proof (subst state_rel_def, subst state_rel0_def, intro conjI)
    (* Need an assumption that says that the current state is well formed *)
    show "valid_heap_mask (get_mh_total_full \<omega>def)"
      using ValidHeapMask by simp
  next
    show "valid_heap_mask (get_mh_total_full \<omega>)"
      using ValidHeapMask by simp
  next
      (* Do we need an assumption
         WfTotalConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      ? *)
    show "consistent_state_rel_opt (state_rel_opt Tr) \<longrightarrow> StateCons \<omega>def \<and> StateCons \<omega>"
      using Consistent by simp
  next
    show "type_interp ctxt = vbpl_absval_ty TyRep"
      using StateRel state_rel_type_interp by fast
  next
    show "store_rel (type_interp ctxt) ?\<Lambda> (var_translation Tr) (get_store_total \<omega>) ns"
    proof -
      have "var_translation Tr = var_translation Tr'"
        using \<open>Tr = _\<close> by simp
      have "get_store_total \<omega> = get_store_total \<omega>_old" using \<open>\<omega> = _\<close> by simp
      thus ?thesis
        using StateRel state_rel_store_rel \<open>var_translation Tr = var_translation Tr'\<close> by fastforce
    qed
  next
    show "disjoint_list (state_rel0_disj_list Tr AuxPred)"
    proof -
      \<comment>\<open>This is our starting point\<close>
      have DisjointList: "disjoint_list (state_rel0_disj_list Tr' AuxPred')"
        using StateRel state_rel_disjoint by fast
      \<comment>\<open>We proceed in three steps\<close>
      \<comment>\<open>First, we switch from AuxPred' to AuxPred\<close>
      have DisjointListAuxPred: "disjoint_list (state_rel0_disj_list Tr' AuxPred)"
      proof (rule disjoint_list_restrict_auxpred[where ?AuxPred = "AuxPred'"],
             simp add: DisjointList)
        show "dom AuxPred \<subseteq> dom AuxPred'"
          using \<open>AuxPred' = _\<close> by fastforce
      qed
      \<comment>\<open>Next, we switch the heap variables\<close>
      let ?TrCurrentHeap = "Tr' \<lparr> heap_var := h, heap_var_def := hdef \<rparr>"
      have DisjointListCurrentHeap: "disjoint_list (state_rel0_disj_list ?TrCurrentHeap AuxPred)"
      proof (rule disjoint_list_change_heap[where ?Tr = "Tr'"], simp add: DisjointListAuxPred, simp)
        show "h \<notin> \<Union> (set (state_rel0_disj_list Tr' AuxPred))"
        proof -
          let ?xs = "[{heap_var Tr', heap_var_def Tr'},
                      {mask_var Tr', mask_var_def Tr'},
                      (ran (var_translation Tr')), 
                      (ran (field_translation Tr')),
                      (range (const_repr Tr'))]"
          let ?M = "dom AuxPred'"
          let ?M' = "dom AuxPred"
          let ?ys ="[vars_label_hm_tr (label_hm_translation Tr')]"
          have "h \<notin> \<Union> (set (?xs @ (?M' # ?ys)))"
          proof (rule disjoint_list_removed_from_set)
            show "disjoint_list (?xs @ (?M # ?ys))"
              using DisjointList by simp
            show "h \<in> dom AuxPred'"
              using \<open>AuxPred' = _\<close> by simp
            show "h \<notin> dom AuxPred"
              using DisjAuxPred by simp
          qed
          thus ?thesis by simp
        qed
        show "hdef \<notin> \<Union> (set (ViperBoogieRelUtil.state_rel0_disj_list Tr' AuxPred))"
        proof -
          let ?xs = "[{heap_var Tr', heap_var_def Tr'},
                      {mask_var Tr', mask_var_def Tr'},
                      (ran (var_translation Tr')), 
                      (ran (field_translation Tr')),
                      (range (const_repr Tr'))]"
          let ?M = "dom AuxPred'"
          let ?M' = "dom AuxPred"
          let ?ys ="[vars_label_hm_tr (label_hm_translation Tr')]"
          have "hdef \<notin> \<Union> (set (?xs @ (?M' # ?ys)))"
          proof (rule disjoint_list_removed_from_set)
            show "disjoint_list (?xs @ (?M # ?ys))"
              using DisjointList by simp
            show "hdef \<in> dom AuxPred'"
              using \<open>AuxPred' = _\<close> by simp
            show "hdef \<notin> dom AuxPred"
              using DisjAuxPred by simp
          qed
          thus ?thesis by simp
        qed
      qed

      \<comment>\<open>Finally change the mask variables\<close>
      thus "disjoint_list (state_rel0_disj_list Tr AuxPred)"
      proof (rule disjoint_list_change_mask[where Tr = ?TrCurrentHeap and ?m' = m and ?mdef' = mdef],
             simp add: \<open>Tr = _\<close>)
        show "m \<notin> \<Union> (set (state_rel0_disj_list ?TrCurrentHeap AuxPred))"
        proof -
          let ?xs = "[{heap_var Tr', heap_var_def Tr'},
                      {mask_var Tr', mask_var_def Tr'},
                      (ran (var_translation Tr')), 
                      (ran (field_translation Tr')),
                      (range (const_repr Tr'))]"
          let ?M = "dom AuxPred'"
          let ?M' = "dom AuxPred"
          let ?ys ="[vars_label_hm_tr (label_hm_translation Tr')]"
          have "m \<notin> \<Union> (set (?xs @ (?M' # ?ys)))"
          proof (rule disjoint_list_removed_from_set)
            show "disjoint_list (?xs @ (?M # ?ys))"
              using DisjointList by simp
            show "m \<in> dom AuxPred'"
              using \<open>AuxPred' = _\<close> by simp
            show "m \<notin> dom AuxPred"
              using DisjAuxPred by simp
          qed
          thus ?thesis
            using DisjMaskHeap by fastforce
        qed
        show "mdef \<notin> \<Union> (set (state_rel0_disj_list ?TrCurrentHeap AuxPred))"
        proof -
          let ?xs = "[{heap_var Tr', heap_var_def Tr'},
                      {mask_var Tr', mask_var_def Tr'},
                      (ran (var_translation Tr')), 
                      (ran (field_translation Tr')),
                      (range (const_repr Tr'))]"
          let ?M = "dom AuxPred'"
          let ?M' = "dom AuxPred"
          let ?ys ="[vars_label_hm_tr (label_hm_translation Tr')]"
          have "mdef \<notin> \<Union> (set (?xs @ (?M' # ?ys)))"
          proof (rule disjoint_list_removed_from_set)
            show "disjoint_list (?xs @ (?M # ?ys))"
              using DisjointList by simp
            show "mdef \<in> dom AuxPred'"
              using \<open>AuxPred' = _\<close> by simp
            show "mdef \<notin> dom AuxPred"
              using DisjAuxPred by simp
          qed
          thus ?thesis
            using DisjMaskHeap by fastforce
        qed
      qed
    qed
  next
    show "get_store_total \<omega>def = get_store_total \<omega>"
      using \<open>\<omega>def = _\<close> \<open>\<omega> = _\<close> StateRel state_rel_eval_welldef_eq
      by fastforce
  next
    show "get_trace_total \<omega>def = get_trace_total \<omega>"
      using \<open>\<omega>def = _\<close> \<open>\<omega> = _\<close> StateRel state_rel_eval_welldef_eq
      by fastforce
  next
    (* Need an assumption that says that the total states are the same *)
    show "get_h_total_full \<omega>def = get_h_total_full \<omega>"
      using SameHeap by simp
  next
    show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>) ns"
      unfolding heap_var_rel_def
    proof (intro conjI)
      show "\<exists>hb. lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
         lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId TyRep)) \<and>
         vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
         heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
      proof (intro exI, intro conjI)
        show "lookup_var ?\<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap hb))" 
          using LookupHeap \<open>Tr = _\<close> by simp
        show "lookup_var_ty ?\<Lambda> (heap_var Tr) = Some (TConSingle (THeapId TyRep))"
          using LookupVarTyHeap \<open>Tr = _\<close> by simp
        show "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])"
          using PredEqHeapAux pred_eq_heap_aux_def by fast
        show "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) hb"
          using PredEqHeapAux pred_eq_heap_aux_def by fast
      qed
      show "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>) "
        using TotalHeapWellTy by simp
    qed
  next
    show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>) ns"
      unfolding mask_var_rel_def
      using LookupMask LookupVarTyMask MaskRel \<open>Tr = _\<close> by simp
  next
    show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def) ns"
      unfolding heap_var_rel_def
    proof (intro conjI)
      show "\<exists>hb. lookup_var ?\<Lambda> ns (heap_var_def Tr) = Some (AbsV (AHeap hb)) \<and>
         lookup_var_ty ?\<Lambda> (heap_var_def Tr) = Some (TConSingle (THeapId TyRep)) \<and>
         vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
         heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>def) hb"
      proof (intro exI, intro conjI)
        show "lookup_var ?\<Lambda> ns (heap_var_def Tr) = Some (AbsV (AHeap hbdef))"
          using LookupHeapDef \<open>Tr = _\<close> by simp
        show "lookup_var_ty ?\<Lambda> (heap_var_def Tr) = Some (TConSingle (THeapId TyRep))"
          using LookupVarTyHeapDef \<open>Tr = _\<close> by simp
        show "vbpl_absval_ty_opt TyRep (AHeap hbdef) = Some (THeapId TyRep, [])"
          using PredEqHeapAuxDef pred_eq_heap_aux_def by fast
        show "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>def) hbdef"
          using PredEqHeapAuxDef pred_eq_heap_aux_def by fast
      qed
      show "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>def)"
        using TotalHeapWellTyDef by simp
    qed
  next
    show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def) ns"
      unfolding mask_var_rel_def
      using LookupMaskDef LookupVarTyMaskDef MaskRelDef \<open>Tr = _\<close> by simp
  next 
    show "field_rel Pr (var_context ctxt) (field_translation Tr) ns"
      using StateRel state_rel_field_rel \<open>Tr = _\<close> by fastforce
  next
    show "boogie_const_rel (const_repr Tr) (var_context ctxt) ns"
      using StateRel state_rel_boogie_const_rel \<open>Tr = _\<close> by fastforce
  next
    show "state_well_typed (type_interp ctxt) (var_context ctxt) [] ns"
      using StateRel state_rel_state_well_typed by fast
  next
    show "aux_vars_pred_sat ?\<Lambda> AuxPred ns"
      unfolding aux_vars_pred_sat_def
    proof (intro allI, intro impI)
      fix x P
      assume PredicateDefined: "AuxPred x = Some P"
      show "has_Some P (lookup_var ?\<Lambda> ns x)"
      proof (cases "x = h \<or> x = m \<or> x = hdef \<or> x = mdef")
        case False
        hence "AuxPred' x = Some P"
          using \<open>AuxPred' = _\<close> PredicateDefined by simp
        thus "has_Some P (lookup_var ?\<Lambda> ns x)"
          using StateRel \<open>AuxPred' x = Some P\<close> state_rel_aux_pred_sat_lookup
          by blast
      next
        case True
        then consider
             (H)    "x = h"
           | (M)    "x \<noteq> h \<and> x = m"
           | (HDef) "x \<noteq> h \<and> x \<noteq> m \<and> x = hdef"
           | (MDef) "x \<noteq> h \<and> x \<noteq> m \<and> x \<noteq> hdef \<and> x = mdef"
          by fast
        thus "has_Some P (lookup_var ?\<Lambda> ns x)"
        proof (cases)
          case H
          thus ?thesis
            using DisjAuxPred PredicateDefined by fast
        next
          case M
          thus ?thesis
            using DisjAuxPred PredicateDefined by fast
        next
          case HDef
          thus ?thesis
            using DisjAuxPred PredicateDefined by fast
        next
          case MDef
          thus ?thesis
            using DisjAuxPred PredicateDefined by fast
        qed
      qed
    qed
  next
    show "label_hm_rel Pr ?\<Lambda> TyRep (field_translation Tr) (label_hm_translation Tr) (get_trace_total \<omega>) ns"
      unfolding label_hm_rel_def
    proof (intro conjI)
      show "label_rel (\<lambda>h \<phi>. heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) h (get_hh_total \<phi>)) (fst (label_hm_translation Tr)) (get_trace_total \<omega>) ns"
        unfolding label_rel_def
      proof (intro allI, intro impI)
        fix l h
        assume LabelDefined: "fst (label_hm_translation Tr) l = Some h"
        have LabelRel: "\<forall>lbl h. (fst (label_hm_translation Tr')) lbl = Some h \<longrightarrow>
                          (\<exists>\<phi>. (get_trace_total \<omega>_old) lbl = Some \<phi> \<and>
                          heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') h (get_hh_total \<phi>) ns)"
          using StateRel state_rel_label_hm_rel
          unfolding label_hm_rel_def label_rel_def
          by fast
        then obtain \<phi> where
          "get_trace_total \<omega>_old l = Some \<phi>" and
          HeapVarRel: "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') h (get_hh_total \<phi>) ns"
          using \<open>Tr = _\<close> LabelDefined
          by fastforce
        show "\<exists>\<phi>. get_trace_total \<omega> l = Some \<phi> \<and>
            heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) h (get_hh_total \<phi>) ns"
        proof (intro exI, intro conjI)
          show "get_trace_total \<omega> l = Some \<phi>"
            using \<open>get_trace_total \<omega>_old l = Some \<phi>\<close> \<open>\<omega> = _\<close> by simp
          show "heap_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) h (get_hh_total \<phi>) ns"
          proof -
            have "field_translation Tr = field_translation Tr'"
              using \<open>Tr = _\<close> by simp
            thus ?thesis
              using HeapVarRel by simp
          qed
        qed
      qed
      show "label_rel (\<lambda>m \<phi>. mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) m (get_mh_total \<phi>)) (snd (label_hm_translation Tr)) (get_trace_total \<omega>) ns"
        unfolding label_rel_def
      proof (intro allI, intro impI)
        fix l m
        assume LabelDefined: "snd (label_hm_translation Tr) l = Some m"
        have LabelRel: "\<forall>lbl m. (snd (label_hm_translation Tr')) lbl = Some m \<longrightarrow>
                          (\<exists>\<phi>. (get_trace_total \<omega>_old) lbl = Some \<phi> \<and>
                          mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') m (get_mh_total \<phi>) ns)"
          using StateRel state_rel_label_hm_rel
          unfolding label_hm_rel_def label_rel_def
          by fast
        then obtain \<phi> where
          "get_trace_total \<omega>_old l = Some \<phi>" and
          MaskVarRel: "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr') m (get_mh_total \<phi>) ns"
          using \<open>Tr = _\<close> LabelDefined by fastforce
        show "\<exists>\<phi>. get_trace_total \<omega> l = Some \<phi> \<and>
            mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) m (get_mh_total \<phi>) ns"
        proof (intro exI, intro conjI)
          show "get_trace_total \<omega> l = Some \<phi>"
            using \<open>get_trace_total \<omega>_old l = _\<close> \<open>\<omega> = _\<close> by simp
          show "mask_var_rel Pr ?\<Lambda> TyRep (field_translation Tr) m (get_mh_total \<phi>) ns"
          proof -
            have "field_translation Tr = field_translation Tr'"
              using \<open>Tr = _\<close> by simp
            thus ?thesis
              using MaskVarRel by simp
          qed
        qed
      qed
      show "\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> valid_heap_mask (get_mh_total \<phi>)"
      proof (intro allI, intro impI)
        fix lbl \<phi>
        assume "get_trace_total \<omega> lbl = Some \<phi>"
        show "valid_heap_mask (get_mh_total \<phi>)"
          by (metis StateRel \<open>get_trace_total \<omega> lbl = Some \<phi>\<close> \<open>\<omega> = _\<close> full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3) label_hm_rel_def state_rel_label_hm_rel)
      qed
    qed
  qed
qed

(*
lemma state_rel_capture_total_state_change_eval_state_alt:
  assumes StateRel: "state_rel_capture_total_state Pr StateCons TyRep Tr' FieldTr0 AuxPred ctxt m h \<omega>0 \<omega>def \<omega> ns"      
      and "m \<noteq> h"
      and "FieldTr0 = field_translation Tr"
      and DisjAuxPred: "{m,h} \<inter> dom AuxPred = {}"
      and "\<omega>0 = \<omega>def"
      and "Tr = Tr'\<lparr>mask_var := m, heap_var := h, mask_var_def := m, heap_var_def := h\<rparr>"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega>0 ns"
proof (rule state_rel_capture_total_state_change_eval_and_def_state[where ?mdef=m and ?hdef = h and ?m = m and ?h =h 
                                                              and ?\<omega>def = \<omega>def and ?\<omega> = \<omega> and ?Tr' = Tr' ], 
       simp)
  from StateRel 
  show " state_rel Pr StateCons TyRep Tr' (AuxPred(m \<mapsto> pred_eq_mask Pr TyRep FieldTr0 ctxt m \<omega>0, h \<mapsto> pred_eq_heap Pr TyRep FieldTr0 ctxt h \<omega>0)) ctxt \<omega>def
     \<omega> ns"
    by (simp add: aux_pred_capture_state_def)    
qed (insert assms, auto) *)

lemma state_rel_capture_total_state_change_eval_state:
  assumes StateRel: "state_rel_capture_total_state Pr StateCons TyRep Tr' FieldTr0 AuxPred ctxt m h \<omega>0 \<omega>def \<omega> ns"      
      and "m \<noteq> h"
      and "FieldTr0 = field_translation Tr"
      and DisjAuxPred: "{m,h} \<inter> dom AuxPred = {}"
      and "\<omega>0 = \<omega>def"
      and "Tr = Tr'\<lparr>mask_var := m, heap_var := h, mask_var_def := m, heap_var_def := h\<rparr>"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega>0 ns"
proof -

  from state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=m] \<open>m \<noteq> h\<close>
  obtain mb where LookupMask: "lookup_var (var_context ctxt) ns m = Some (AbsV (AMask mb))" and
                  LookupVarTyMask: "lookup_var_ty (var_context ctxt) m = Some (TConSingle (TMaskId TyRep))" and
                  MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>0) mb"
    using state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=m] \<open>m \<noteq> h\<close> \<open>FieldTr0 = _\<close>    
    unfolding aux_pred_capture_state_def pred_eq_mask_def 
    by auto
  
  obtain hb where LookupVarTyHeap: "lookup_var_ty (var_context ctxt) h = Some (TConSingle (THeapId TyRep))" and
                  LookupHeap: "lookup_var (var_context ctxt) ns h = Some (AbsV (AHeap hb))" and
                  PredEqHeapAux: "pred_eq_heap_aux Pr TyRep (field_translation Tr) \<omega>0 hb" and
                  TotalHeapWellTy: "total_heap_well_typed Pr (domain_type TyRep) (get_hh_total_full \<omega>0)"
    using state_rel_aux_pred_sat_lookup_2[OF StateRel, where ?aux_var=h] \<open>m \<noteq> h\<close> \<open>FieldTr0 = _\<close>    
    unfolding pred_eq_heap_def \<open>Tr = _\<close> aux_pred_capture_state_def
    by auto
  
  show ?thesis
    unfolding state_rel_def state_rel0_def
  proof (intro conjI)
    show "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var Tr) (get_hh_total_full \<omega>0) ns"
      unfolding heap_var_rel_def \<open>Tr = _\<close>
      apply (intro conjI)
       apply (rule exI[where ?x = hb])
      using  PredEqHeapAux[simplified pred_eq_heap_aux_def] 
       apply (simp add: LookupHeap LookupVarTyHeap \<open>Tr = _\<close>  del: vbpl_absval_ty_opt_heap_simp_alt)
      apply (rule TotalHeapWellTy)
      done

    thus "heap_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (heap_var_def Tr) (get_hh_total_full \<omega>def) ns"
      using \<open>Tr = _\<close> \<open>\<omega>0 = \<omega>def\<close>
      by auto
  next
    show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) (get_mh_total_full \<omega>0) ns"
      unfolding mask_var_rel_def
      apply (rule exI[where ?x = mb])
      using LookupMask LookupVarTyMask MaskRel \<open>Tr = _\<close>
      by simp

    thus "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var_def Tr) (get_mh_total_full \<omega>def) ns"
      using \<open>Tr = _\<close> \<open>\<omega>0 = \<omega>def\<close>
      by auto
  next
    show "aux_vars_pred_sat (var_context ctxt) AuxPred ns"
      apply (rule aux_vars_pred_sat_weaken[OF state_rel_aux_vars_pred_sat[OF StateRel]])
      using DisjAuxPred
      unfolding aux_pred_capture_state_def
       apply fastforce
      using DisjAuxPred
      by (metis (no_types, lifting) domIff insert_disjoint(2) map_upd_Some_unfold option.distinct(1))
  next 
    show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) (get_store_total \<omega>0) ns"
    proof -
      have "var_translation Tr = var_translation Tr'"
        by (simp add: \<open>Tr = _\<close>)
      with state_rel_store_rel[OF StateRel] state_rel_eval_welldef_eq[OF StateRel]
      show ?thesis
        using  \<open>\<omega>0 = \<omega>def\<close>
        by metis
    qed
  next
    have Disj1: "disjoint_list (state_rel0_disj_list Tr' AuxPred)"      
      using state_rel_disjoint[OF StateRel, simplified aux_pred_capture_state_dom]
      apply (rule disjoint_list_subset_list_all2)
      by fastforce

    have Disj2: "disjoint_list
     ([{heap_var Tr', heap_var_def Tr'}]@
       (({mask_var Tr', mask_var_def Tr'} \<union> {m})#
       [ran (var_translation Tr'), ran (field_translation Tr'), range (const_repr Tr'), 
        dom AuxPred, vars_label_hm_tr (label_hm_translation Tr')]))"
      apply (rule disjoint_list_add_set)
      using Disj1
      apply simp
      using state_rel_aux_pred_disjoint[OF StateRel, simplified aux_pred_capture_state_dom] DisjAuxPred
      by fastforce
      

    have "disjoint_list
       ([]@(({heap_var Tr', heap_var_def Tr'} \<union> {h})#
        [{mask_var Tr', mask_var_def Tr', m},
        ran (var_translation Tr'), ran (field_translation Tr'), range (const_repr Tr'),
        dom AuxPred, vars_label_hm_tr (label_hm_translation Tr')]))"
      apply (rule disjoint_list_add_set)      
      using Disj2
       apply simp
       apply (erule disjoint_list_subset_list_all2)
       apply simp
      using state_rel_aux_pred_disjoint[OF StateRel, simplified aux_pred_capture_state_dom] DisjAuxPred \<open>m \<noteq> h\<close>
      by force

    thus "disjoint_list (state_rel0_disj_list Tr AuxPred)"
      apply (rule disjoint_list_subset_list_all2)
      apply (simp add: \<open>Tr = _\<close>)
      done

  qed (insert StateRel[simplified state_rel_def state_rel0_def] 
              state_rel_state_well_typed[OF StateRel]  
              \<open>\<omega>0 = \<omega>def\<close> \<open>Tr = _\<close>, simp_all)
qed


subsection \<open>Tracking the well-definedness state\<close>

lemma state_rel_def_same_to_state_rel:
  assumes "rel_ext_eq (state_rel_def_same vpr_prog StateCons TyRep Tr AuxPred ctxt) \<omega>def \<omega> ns"      
  shows "state_rel vpr_prog StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
  using assms
  by simp

lemma red_ast_bpl_rel_to_state_rel:
  assumes "\<And> \<omega> ns. R1 \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr AuxPred ctxt (fst \<omega>) (snd \<omega>) ns"
  shows "red_ast_bpl_rel R1 (uncurry (state_rel Pr StateCons TyRep Tr AuxPred ctxt))  P ctxt \<gamma> \<gamma>"
  apply (rule red_ast_bpl_rel_input_implies_output)
  using assms
  by simp

subsection \<open>Instantiating the output relation\<close>

text \<open>The following lemmas are useful for constraining the output relation, if the output relation is a
      schematic variable in the goal.\<close>

lemma red_ast_bpl_rel_inst_state_rel_same:
  assumes "red_ast_bpl_rel R0 R0 P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R0 P ctxt \<gamma>1 \<gamma>2"
  using assms
  by blast 

lemma red_ast_bpl_rel_inst_state_rel_conjunct2:
  assumes "\<And> \<omega> ns. R0 \<omega> ns = (Q \<omega> \<and> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns)"
      and "R1 = state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt"
      and "red_ast_bpl_rel R0 (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) P ctxt \<gamma>1 \<gamma>2"
    shows "red_ast_bpl_rel R0 R1 P ctxt \<gamma>1 \<gamma>2"
  using assms
  by blast  

subsection \<open>Monotonicity\<close>

lemma true_mono_prop_downward: "mono_prop_downward (\<lambda>_. True)"
  unfolding mono_prop_downward_def
  by blast

lemma true_mono_prop_downward_ord: "mono_prop_downward_ord (\<lambda>_. True)"
  unfolding mono_prop_downward_ord_def
  by blast

subsection \<open>Utility theorems for Proof Generation\<close>

lemma state_rel_eq_conj_helper_1:
  assumes "R = (\<lambda>\<omega>def \<omega> ns. (state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<and> (\<omega>def = \<omega>)))"
  shows "R = (\<lambda>\<omega>def \<omega> ns. (state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<and> (\<omega>def = \<omega>)))"
  using assms
  by simp
  

lemma state_rel_eq_conj_helper_2:
  assumes "R = state_rel Pr StateCons TyRep Tr AuxPred ctxt"
  shows "R = (\<lambda>\<omega>def \<omega> ns. state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns \<and> ((\<lambda> \<omega>def \<omega>. True) \<omega>def \<omega>))"
  using assms
  by simp

end