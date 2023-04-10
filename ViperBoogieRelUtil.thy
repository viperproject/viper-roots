theory ViperBoogieRelUtil
  imports ViperBoogieTranslationInterface ExpRel Simulation
begin

subsection \<open>Temporary variable management\<close>

lemma store_temporary_var:
  assumes
  StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some \<tau>_bpl" and
         RedRhs:  "red_expr_bpl ctxt e ns v" and
         TyValBpl:  "type_of_val (type_interp ctxt) v = \<tau>_bpl"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq v)) ctxt \<omega>def \<omega> ns')"
           (is "\<exists>ns'. ?red ns' \<and> ?R' \<omega> ns'")
proof (rule exI, rule conjI)
  let ?ns' = "update_var (var_context ctxt) ns temp_var v"

  have StateRel2: "state_rel Pr TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq v)) ctxt \<omega>def \<omega> ?ns'"
    using state_rel_new_auxvar[OF \<open>?R \<omega> ns\<close> DisjAux _ TyInterp LookupTyTemp] TyValBpl
    unfolding pred_eq_def
    by simp    

  show "?red ?ns'"
    apply (rule red_ast_bpl_one_simple_cmd)
    by (fastforce intro!: RedAssign LookupTyTemp RedRhs simp:TyValBpl )

  show "?R' \<omega> ?ns'"
    using StateRel2
    by blast
qed

lemma store_vpr_exp_to_temporary_var:
  assumes  
  StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega>def \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some \<tau>_bpl" and
  RedRhsVpr:  "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
  ExpRel: "exp_rel_vpr_bpl (state_rel Pr TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e_vpr e_bpl" and
         TyValBpl:  "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = \<tau>_bpl"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e_bpl # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq (val_rel_vpr_bpl v))) ctxt \<omega>def \<omega> ns')"
proof (rule store_temporary_var[OF StateRel TyInterp DisjAux LookupTyTemp _ TyValBpl])
  show "red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v)"
    using exp_rel_vpr_bpl_elim_2[OF ExpRel] RedRhsVpr StateRel
    by metis
qed

lemma store_temporary_perm_rel:
  assumes
  StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega>def \<omega> ns") and
  RedPerm:  "ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
  ExpRel: "exp_rel_vpr_bpl (state_rel Pr TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e_vpr e_bpl" and
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some (TPrim TReal)" and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep"
  shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e_bpl # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega>def \<omega> ns')"
           (is "\<exists>ns'. ?red ns' \<and> ?R' \<omega> ns'")
   using store_vpr_exp_to_temporary_var[OF StateRel TyInterp DisjAux LookupTyTemp RedPerm ExpRel]
   by simp

subsection \<open>Store well-definedness state in fresh variables\<close>

lemma store_new_mask_def:
  assumes
  StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "mvar_def' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTy: "lookup_var_ty (var_context ctxt) mvar_def' = Some (TConSingle (TMaskId TyRep))" and
                  "mvar_def = mask_var_def Tr"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign mvar_def' (Var mvar_def) # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns')"
proof -
  from state_rel_mask_var_def_rel[OF StateRel] obtain m where 
    LookupMaskVarDef: "lookup_var (var_context ctxt) ns (mask_var_def Tr) = Some (AbsV (AMask m))"    
    unfolding mask_var_rel_def
    by blast

  let ?ns' = "(update_var (var_context ctxt) ns mvar_def' (AbsV (AMask m)))"

  have StateRelUpd: "state_rel Pr TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    using state_rel_mask_var_def_update[OF StateRel DisjAux LookupTy LookupMaskVarDef]
    by blast

  show ?thesis
    apply (rule exI)
    apply (rule conjI)
     apply (rule red_ast_bpl_one_assign)
       apply (rule LookupTy)
      apply (fastforce intro: RedVar LookupMaskVarDef simp: \<open>mvar_def = _\<close>)
     apply (simp add: TyInterp)
    apply (rule StateRelUpd)
    done
qed

lemma store_new_heap_def:
  assumes
  StateRel: "state_rel Pr TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "hvar_def' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTy: "lookup_var_ty (var_context ctxt) hvar_def' = Some (TConSingle (THeapId TyRep))" and
                  "hvar_def = heap_var_def Tr"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign hvar_def' (Var hvar_def) # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns')"
proof -
  from state_rel_heap_var_def_rel[OF StateRel] obtain h where 
    LookupMaskVarDef: "lookup_var (var_context ctxt) ns (heap_var_def Tr) = Some (AbsV (AHeap h))"  and
                      "vbpl_absval_ty_opt TyRep (AHeap h) = Some (THeapId TyRep, [])"
    unfolding heap_var_rel_def
    by blast

  hence HeapType: "type_of_val (type_interp ctxt) (AbsV (AHeap h)) = TConSingle (THeapId TyRep)"
    using TyInterp
    by simp

  let ?ns' = "(update_var (var_context ctxt) ns hvar_def' (AbsV (AHeap h)))"

  have StateRelUpd: "state_rel Pr TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    using state_rel_heap_var_def_update[OF StateRel DisjAux LookupTy LookupMaskVarDef]
    by blast

  show ?thesis
    apply (rule exI)
    apply (rule conjI)
     apply (rule red_ast_bpl_one_assign)
       apply (rule LookupTy)
      apply (fastforce intro: RedVar LookupMaskVarDef simp: \<open>hvar_def = _\<close>)
     apply (simp only: instantiate_nil)
     apply (rule HeapType)
    apply (rule StateRelUpd)
    done
qed

subsection \<open>Permission checks\<close>

lemma pos_perm_rel_nontrivial:
  assumes "zero_perm = const_repr Tr CNoPerm" and
          StateRelImpl:"\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega>def \<omega> ns" and
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
  hence StateRel: "state_rel Pr TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns"
    using StateRelImpl
    by simp
  let ?p_bpl = "RealV (real_of_rat p)"
  
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



end