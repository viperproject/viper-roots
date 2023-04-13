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

(*
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
*)
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

    subsection \<open>Mask Update\<close>

lemma mask_upd_rel:
  assumes
   StateRel: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow>
                           state_rel Pr TyRep Tr AuxPred ctxt (fst \<omega>) (snd \<omega>) ns" and      
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
                  (uncurry (state_rel Pr TyRep Tr AuxPred ctxt))
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
             uncurry (state_rel Pr TyRep Tr AuxPred ctxt) \<omega>' ns'"
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

    have "state_rel Pr TyRep Tr AuxPred ctxt (fst \<omega>') (snd \<omega>') ?ns'"
      apply (subst \<open>snd \<omega>' = _\<close>)+
      apply (subst \<open>?mb' = _\<close>)
      apply (subst \<open>m_bpl = _\<close>)
      apply (rule state_rel_mask_update_3[OF StateRelInst])
               apply simp
              
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False \<open>r = _\<close>
              apply force
      using SuccessUpdState[OF \<open>R \<omega> ns\<close> Success] False \<open>r = _\<close>
             apply argo
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
                           state_rel_def_same Pr TyRep Tr AuxPred ctxt \<omega> ns" and      
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
                  (state_rel_def_same Pr TyRep Tr AuxPred ctxt)
                  Success
                  (\<lambda> \<omega>. False) P ctxt 
                  (BigBlock name ((Assign m_bpl m_upd_bpl) # cs) str tr, cont) 
                  (BigBlock name cs str tr, cont)"
  apply (rule rel_general_convert, rule rel_general_conseq_fail, rule rel_general_conseq_output, 
         rule mask_upd_rel[where ?p_prat="p_prat \<circ> snd" and r=r])
  using assms
  by fastforce+

subsection \<open>Constructing a well-typed Boogie heap from a Viper heap\<close>

fun construct_bpl_heap_from_vpr_heap :: "'a total_heap \<Rightarrow> 'a bpl_heap_ty"
  where "construct_bpl_heap_from_vpr_heap h = undefined" \<comment>\<open>TODO\<close>


lemma construct_bpl_heap_from_vpr_heap_correct:
  assumes "wf_ty_repr_bpl TyRep"
  shows "\<exists>hb. heap_rel Pr tr_field h hb \<and>
              vbpl_absval_ty_opt TyRep (AHeap hb) = Some ((THeapId TyRep) ,[])"
  sorry


end