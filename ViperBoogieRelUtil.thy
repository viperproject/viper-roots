theory ViperBoogieRelUtil
  imports ViperBoogieTranslationInterface ExpRel Simulation
begin

subsection \<open>Temporary variable management\<close>

lemma store_temporary_var:
  assumes
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" and
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
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

lemma store_vpr_exp_to_temporary_var:
  assumes  
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega>def \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" and
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
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
         DisjAux: "temp_var \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTyTemp: "lookup_var_ty (var_context ctxt) temp_var = Some (TPrim TReal)" and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         EmptyRtype: "rtype_interp ctxt = []" 
  shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign temp_var e_bpl # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep Tr (AuxPred(temp_var \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega>def \<omega> ns')"
           (is "\<exists>ns'. ?red ns' \<and> ?R' \<omega> ns'")
   using store_vpr_exp_to_temporary_var[OF StateRel TyInterp EmptyRtype DisjAux LookupTyTemp RedPerm ExpRel]
   by simp

subsection \<open>Store well-definedness state in fresh variables\<close>

(*
lemma store_new_mask_def:
  assumes
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "mvar_def' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTy: "lookup_var_ty (var_context ctxt) mvar_def' = Some (TConSingle (TMaskId TyRep))" and
                  "mvar_def = mask_var_def Tr"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign mvar_def' (Var mvar_def) # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns')"
proof -
  from state_rel_mask_var_def_rel[OF StateRel] obtain m where 
    LookupMaskVarDef: "lookup_var (var_context ctxt) ns (mask_var_def Tr) = Some (AbsV (AMask m))"    
    unfolding mask_var_rel_def
    by blast

  let ?ns' = "(update_var (var_context ctxt) ns mvar_def' (AbsV (AMask m)))"

  have StateRelUpd: "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
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
  StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" (is "?R \<omega> ns") and
         TyInterp:  "type_interp ctxt = vbpl_absval_ty TyRep" and
         DisjAux: "hvar_def' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> 
                     ran (field_translation Tr) \<union> range (const_repr Tr) \<union> dom AuxPred" and
         LookupTy: "lookup_var_ty (var_context ctxt) hvar_def' = Some (TConSingle (THeapId TyRep))" and
                  "hvar_def = heap_var_def Tr"
   shows "\<exists>ns'. red_ast_bpl P ctxt (((BigBlock name (Lang.Assign hvar_def' (Var hvar_def) # cs) s tr), cont), Normal ns)
                                   ((BigBlock name cs s tr, cont), Normal ns') \<and>
                (state_rel Pr StateCons TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns')"
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

  have StateRelUpd: "state_rel Pr StateCons TyRep (Tr\<lparr>heap_var_def := hvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
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
*)
subsection \<open>Permission checks\<close>

lemma pos_perm_rel_nontrivial:
  assumes "zero_perm = const_repr Tr CNoPerm" and
          StateRelImpl:"\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt \<omega>def \<omega> ns" and
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
  hence StateRel: "state_rel Pr StateCons TyRep Tr (AuxPred(temp_perm \<mapsto> pred_eq (RealV (real_of_rat p)))) ctxt (fst \<omega>def_\<omega>) (snd \<omega>def_\<omega>) ns"
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
                                      update_mh_loc_total_full (snd \<omega>) (the_address r,f_vpr) (p_prat \<omega>))" and
    RedRcvBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))" and
    RedPermBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> 
                   red_expr_bpl ctxt new_perm_bpl ns 
                               (if r = Null then RealV 0 else (RealV (real_of_rat (Rep_prat (p_prat \<omega>))))) \<and>
                   (r \<noteq> Null \<longrightarrow> pgte pwrite (p_prat \<omega>))"
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

  let ?p' = "if r = Null then 0 else real_of_rat (Rep_prat (p_prat \<omega>))"
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
    
  let ?\<omega>' = "(if r = Null then (snd \<omega>) else update_mh_loc_total_full (snd \<omega>) (the_address r,f_vpr) (p_prat \<omega>))"

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
    hence "snd \<omega>' = update_mh_loc_total_full (snd \<omega>) (a,f_vpr) (p_prat \<omega>)"
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False
      by simp
   
    have "?mb' = mask_bpl_upd_normal_field mb (Address a) f_bpl \<tau>_vpr (real_of_rat (Rep_prat (p_prat \<omega>)))"
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
                                      update_mh_loc_total_full \<omega> (the_address r,f_vpr) (p_prat \<omega>))" and
    RedRcvBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))" and
    RedPermBpl: "\<And> \<omega> \<omega>' ns. R \<omega> ns \<Longrightarrow> Success \<omega> \<omega>' \<Longrightarrow> 
                   red_expr_bpl ctxt new_perm_bpl ns 
                               (if r = Null then RealV 0 else (RealV (real_of_rat (Rep_prat (p_prat \<omega>))))) \<and>
                   (r \<noteq> Null \<longrightarrow> pgte pwrite (p_prat \<omega>))"
  shows "rel_general R 
                  (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt)
                  Success
                  (\<lambda> \<omega>. False) P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
  apply (rule rel_general_convert, rule rel_general_conseq_fail, rule rel_general_conseq_output, 
         rule mask_upd_rel[where ?p_prat="p_prat \<circ> snd" and r=r])
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

subsection \<open>State components that do not affect state relation\<close>

text \<open>The properties here will have to be adjusted once new features are added that require 
taking more state components into account. \<close>


text \<open>The following lemma will not hold once the state relation tracks old states.\<close>

\<comment>\<open>Need to update both the well-definedness and the evaluation state, because the state relation demands
that they only differ on the mask.\<close>
lemma state_rel_trace_independent:
  assumes "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> wf_total_consistency ctxt_vpr StateCons StateCons_t" 
      and "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> (\<And> lbl \<phi>. t lbl = Some \<phi> \<Longrightarrow> StateCons_t \<phi>)" 
      and StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
    shows "state_rel Pr StateCons TyRep Tr AuxPred ctxt (update_trace_total \<omega>def t) (update_trace_total \<omega> t) ns"
proof - 
  from assms have ConsistencyUpd: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons (update_trace_total \<omega>def t) \<and> StateCons (update_trace_total \<omega> t)"
    using state_rel_consistent total_consistency_trace_update_2
    by (metis update_trace_total.simps)

  show ?thesis
    unfolding state_rel_def state_rel0_def
    apply (intro conjI)
                 apply (insert StateRel[simplified state_rel_def state_rel0_def] ConsistencyUpd)
                   apply (solves \<open>simp\<close>)+
              apply (fastforce simp: store_rel_def)
             apply (solves \<open>simp\<close>)+
           apply (fastforce simp: heap_var_rel_def mask_var_rel_def)+
    done

qed

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
      and VarFresh: "mvar' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"
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


  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar' \<omega> ns'"
    unfolding mask_var_rel_def Eq
    using LookupTyNewVar MaskRel
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega>def \<omega> ns'"        
    apply (rule state_rel_mask_var_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by blast
        
  with Red show ?thesis
    by fast
qed

lemma heap_var_upd_red_ast_bpl_propagate:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
          LookupTyNewVar: "lookup_var_ty (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep))" and
          "hvar = heap_var Tr" and          
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          VarFresh: "hvar' \<notin> 
                       \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>heap_var Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
                      ({heap_var Tr, heap_var_def Tr} \<union>
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)" 
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
    by blast
   
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
          VarFresh: "mvar_def' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var_def Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)" 
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


  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar_def' \<omega>def ?ns'"
    unfolding mask_var_rel_def 
    using LookupTyNewVar MaskRel
    by fastforce

  have "state_rel Pr StateCons TyRep (Tr\<lparr>mask_var_def := mvar_def'\<rparr>) AuxPred ctxt \<omega>def \<omega> ?ns'"
    apply (rule state_rel_mask_var_def_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by blast
        
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
          VarFresh: "hvar_def' \<notin> 
                       \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>heap_var_def Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
                      ({heap_var Tr, heap_var_def Tr} \<union>
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)" 
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
    by blast
   
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
                      dom AuxPred)" and
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
                      dom AuxPred" 
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

lemma post_framing_propagate_aux:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>0 \<omega>0 ns" and
          WfTyRep: "wf_ty_repr_bpl TyRep" and
          (*WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t" and*)
          TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep" and
          StoreSame: "get_store_total \<omega>0 = get_store_total \<omega>1" and
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
                              dom AuxPred) = {}" (is "?A \<inter> ?B = {}") and
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

  from state_rel_trace_independent[OF _ _ state_rel_heap_pred_independent[OF state_rel_mask_pred_independent[OF StateRel3]]] have
    StateRel4: "state_rel Pr StateCons TyRep (?Tr'\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred ctxt ?\<omega>'' ?\<omega>'' ns''"
    by simp
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
      and "m' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
          range (const_repr Tr) \<union>
          dom AuxPred"
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
      and VarFresh: "mvar' \<notin> ({heap_var Tr, heap_var_def Tr} \<union>
                      \<comment>\<open>The theorem should also hold, if the new variable is not different from \<^term>\<open>mask_var Tr\<close>.
                         The proof was simpler when adding this constraint (because it allows one to do the proof
                         by first treating the new variable as a new auxiliary variable) \<close>
                      {mask_var Tr, mask_var_def Tr} \<union>
                      (ran (var_translation Tr)) \<union>
                      (ran (field_translation Tr)) \<union>
                      (range (const_repr Tr)) \<union>
                      dom AuxPred)"
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


  have MaskVarRel': "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) mvar' \<omega> ?ns'"
    unfolding mask_var_rel_def
    using LookupTyNewVar MaskRel
    by fastforce

  have StateRelAux: "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>mask_var := mvar'\<rparr>) AuxPred ctxt \<omega> ?ns'"        
    apply (rule state_rel_mask_var_update[OF StateRel' MaskVarRel'])
    using VarFresh
    by blast

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
      and "h' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
          range (const_repr Tr) \<union>
          dom AuxPred"
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
          "hvar' \<notin> {heap_var Tr, mask_var Tr, heap_var_def Tr, mask_var_def Tr} \<union> ran (var_translation Tr) \<union> ran (field_translation Tr) \<union>
          range (const_repr Tr) \<union>
          dom AuxPred"
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
    by blast

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
    show "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var Tr) \<omega>0 ns"
      unfolding mask_var_rel_def
      apply (rule exI[where ?x = mb])
      using LookupMask LookupVarTyMask MaskRel \<open>Tr = _\<close>
      by simp

    thus "mask_var_rel Pr (var_context ctxt) TyRep (field_translation Tr) (mask_var_def Tr) \<omega>def ns"
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
    show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) \<omega>0 ns"
    proof -
      have "var_translation Tr = var_translation Tr'"
        by (simp add: \<open>Tr = _\<close>)
      with state_rel_store_rel[OF StateRel] state_rel_eval_welldef_eq[OF StateRel] store_rel_stable
      show ?thesis
        using  \<open>\<omega>0 = \<omega>def\<close>
        by metis
    qed
  next
    have Disj1: "disjoint_list
     [{heap_var Tr', heap_var_def Tr'},
      {mask_var Tr', mask_var_def Tr'},
      ran (var_translation Tr'), ran (field_translation Tr'),
      range (const_repr Tr'), dom AuxPred]"      
      using state_rel_disjoint[OF StateRel, simplified aux_pred_capture_state_dom]
      apply (rule disjoint_list_subset_list_all2)
      by fastforce

    have Disj2: "disjoint_list
     ([{heap_var Tr', heap_var_def Tr'}]@
       (({mask_var Tr', mask_var_def Tr'} \<union> {m})#
       [ran (var_translation Tr'), ran (field_translation Tr'), range (const_repr Tr'), dom AuxPred]))"
      apply (rule disjoint_list_add_set)
      using Disj1
       apply simp
      using state_rel_aux_pred_disjoint[OF StateRel, simplified aux_pred_capture_state_dom] DisjAuxPred
      by force

    have  "disjoint_list
       ([]@(({heap_var Tr', heap_var_def Tr'} \<union> {h})#
        [{mask_var Tr', mask_var_def Tr', m},
        ran (var_translation Tr'), ran (field_translation Tr'),
        range (const_repr Tr'), dom AuxPred]))"
      apply (rule disjoint_list_add_set)      
      using Disj2
       apply simp
       apply (erule disjoint_list_subset_list_all2)
       apply simp
      using state_rel_aux_pred_disjoint[OF StateRel, simplified aux_pred_capture_state_dom] DisjAuxPred \<open>m \<noteq> h\<close>
      by force

    thus "disjoint_list
     [{heap_var Tr, heap_var_def Tr},
      {mask_var Tr, mask_var_def Tr},
      ran (var_translation Tr), ran (field_translation Tr),
      range (const_repr Tr), dom AuxPred]"
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
         
end