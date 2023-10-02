theory ExhaleRelML
imports Boogie_Lang.HelperML ExprWfRelML ExhaleRel ViperBoogieHelperML CPGHelperML
begin

ML \<open>
  val Rmsg' = run_and_print_if_fail_2_tac' 

  datatype 'a exhale_rel_hint = 
    AtomicExhHint of 'a 
  | StarExhHint of ( ('a exhale_rel_hint) * ('a exhale_rel_hint))
  | ImpExhHint of 
       exp_wf_rel_info *       
       exp_rel_info *
       ('a exhale_rel_hint)
  | NoExhHint (* used for debugging purposes *)

  type 'a exhale_rel_complete_hint = {
     setup_well_def_state_tac: basic_stmt_rel_info -> Proof.context -> int -> tactic,
     (* chooses the invariant instantiation *)
     exhale_stmt_rel_thm: thm, 
     (* if defined, then this is the lookup decl theorem of the temporarily havoced heap, otherwise 
        there is no havoc because the assertion is pure *)
     lookup_decl_exhale_heap: thm option, 
     exhale_rel_hint: 'a exhale_rel_hint 
  }

  type 'a atomic_exhale_rel_tac = (Proof.context -> basic_stmt_rel_info -> (Proof.context -> basic_stmt_rel_info -> int -> tactic) option -> 'a -> int -> tactic)

  type 'a exhale_rel_info = {
    basic_info: basic_stmt_rel_info,
    atomic_exhale_rel_tac: 'a atomic_exhale_rel_tac,
     (* states that the invariant is an exhale relation invariant *)
    is_exh_rel_inv_thm: thm,
    (* if set, then it is a tactic that justifies the well-definedness simulation on a list of expressions
       without needing to perform well-definedness checks *)
    no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option 
  }

  fun exhale_rel_aux_tac ctxt (info: 'a exhale_rel_info) (hint: 'a exhale_rel_hint) =
    case hint of
      StarExhHint (left_hint, right_hint) => 
        (Rmsg' "ExhaleRel Star" (resolve_tac ctxt [@{thm exhale_rel_star_2}]) ctxt) THEN'
        (Rmsg' "ExhaleRel Star exhale rel inv" (resolve_tac ctxt [#is_exh_rel_inv_thm info]) ctxt) THEN' 
        (Rmsg' "ExhaleRel Star inv constraint on left assertion" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (exhale_rel_aux_tac ctxt info left_hint |> SOLVED') THEN'
        (exhale_rel_aux_tac ctxt info right_hint |> SOLVED')
    | ImpExhHint (exp_wf_rel_info, exp_rel_info, right_hint) => 
         (Rmsg' "ExhaleRel Imp" (resolve_tac ctxt [@{thm exhale_rel_imp_2}]) ctxt) THEN'
         (Rmsg' "ExhaleRel Imp exhale rel inv" (resolve_tac ctxt [#is_exh_rel_inv_thm info]) ctxt) THEN'
         (Rmsg' "ExhaleRel Imp inv constraint on cond" (assm_full_simp_solved_tac ctxt) ctxt) THEN' 
         (
           (Rmsg' "ExhaleRel Imp 1" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
           (Rmsg' "ExhaleRel Imp wf cond" (exp_wf_rel_tac (#basic_info info) exp_wf_rel_info exp_rel_info ctxt (#no_def_checks_tac_opt info) |> SOLVED') ctxt) THEN'
           (Rmsg' "ExhaleRel Imp 2" ((progress_tac ctxt) |> SOLVED') ctxt)
         ) THEN'
          (Rmsg' "ExhaleRel Imp empty else" (* empty else block *)                
                 ((unfold_bigblock_in_goal ctxt) THEN'
                 (assm_full_simp_solved_tac ctxt))
              ctxt)  THEN'
         (
           (Rmsg' "ExhaleRel Imp cond rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
         ) THEN'
         (
           simplify_continuation ctxt THEN'
          (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
             variable for the recursive call to exhale_rel_tac *)
           (Rmsg' "ExhaleRel Imp 3" (resolve_tac ctxt [@{thm exhale_rel_propagate_post}]) ctxt) THEN'           
           (exhale_rel_aux_tac ctxt info right_hint |> SOLVED') THEN'
           (Rmsg' "ExhaleRel Imp 4" (progress_red_bpl_rel_tac ctxt) ctxt)
         )
    | AtomicExhHint atomicHint => (#atomic_exhale_rel_tac info) ctxt (#basic_info info) (#no_def_checks_tac_opt info) atomicHint
    | NoExhHint => K all_tac
\<close>

ML \<open>

  datatype atomic_exhale_rel_hint = 
    PureExpExhHint of 
       exp_wf_rel_info *
       exp_rel_info 
  | FieldAccExhHint of
       exp_wf_rel_info * 
       exp_rel_info *
       thm * (* auxiliary variable lookup var ty theorem *)
       thm *  (* auxiliary variable lookup var from state relation theorem *)
       thm (* expression relation permission access theorem *)

  fun exh_no_def_checks_tac ctxt (info: basic_stmt_rel_info) : int -> tactic  =
    resolve_tac ctxt [ @{thm framing_exhI_exprs_wf_rel} OF [ #consistency_down_mono_thm info ] ] THEN'
    blast_tac ctxt THEN' (* framing_exh *)
    assm_full_simp_solved_tac ctxt THEN'  (* subexpression equality *)
    assm_full_simp_solved_tac ctxt THEN'  (* subexpression constraint *)
    assm_full_simp_solved_tac ctxt  (* assertion constraint *)

  fun store_temporary_perm_exh_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_ty_thm =
    store_temporary_perm_tac 
         ctxt 
         info 
         exp_rel_info 
         lookup_aux_var_ty_thm
         (fn ctxt => (resolve_tac ctxt @{thms exhale_field_acc_rel_assms_perm_eval}) THEN' blast_tac ctxt)  
 
  fun prove_perm_non_negative_exh_tac ctxt (info: basic_stmt_rel_info) lookup_aux_var_state_rel_thm =
      (Rmsg' "Exh Prove Perm Nonnegative 1" (resolve_tac ctxt @{thms rel_propagate_pre_assert_2}) ctxt) THEN'
      (Rmsg' "Exh Prove Perm Nonnegative - Introduce Facts" 
              (EVERY' [intro_fact_lookup_no_perm_const_tac ctxt (#tr_def_thm info),
              intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_state_rel_thm]) ctxt) THEN'
      (Rmsg' "Exh Prove Perm Nonnegative - Boogie Expression Reduction" (prove_red_expr_bpl_tac ctxt) ctxt) THEN'
      (Rmsg' "Exh Prove Perm Nonnegative - Success Condition" 
             (assm_full_simp_solved_with_thms_tac @{thms exhale_field_acc_rel_perm_success_def} ctxt) ctxt)

  fun prove_sufficient_perm_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_state_rel_thm exp_rel_perm_access_thm =
    (Rmsg' "Exh Prove Sufficient Perm 1" (resolve_tac ctxt @{thms rel_general_cond_2}) ctxt) THEN' 
      (* if condition *)
      (Rmsg' "Exh Prove Sufficient Perm - Introduce Facts Cond" 
            (EVERY' [intro_fact_lookup_no_perm_const_tac ctxt (#tr_def_thm info),
            intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_state_rel_thm]) ctxt) THEN'
      (Rmsg' "Exh Prove Sufficient Perm - Boogie Expression Reduction" (prove_red_expr_bpl_tac ctxt) ctxt) THEN'
      (* then branch *)
      (Rmsg' "Exh Prove Sufficient Perm - Simplify Continuation" (simplify_continuation ctxt) ctxt) THEN'
      (Rmsg' "Exh Prove Sufficient Perm - Unfold and Progress Big Blocks" (rewrite_rel_general_tac ctxt) ctxt) THEN'
      (* apply post propagation here, since will need to progress from empty block to the continuation *)
      (Rmsg' "Exh Prove Sufficient Perm - Propagate Post" (resolve_tac ctxt @{thms rel_propagate_post_2}) ctxt) THEN'
        (Rmsg' "Exh Prove Sufficient Perm - Propagate Pre Assert" (resolve_tac ctxt @{thms rel_propagate_pre_assert_2}) ctxt) THEN'
          (Rmsg' "Exh Prove Sufficient Perm - Introduce Facts Assert" 
                (EVERY' [ intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_state_rel_thm,
                         intro_fact_mask_lookup_reduction ctxt info exp_rel_info exp_rel_perm_access_thm
                                                          (fn ctxt => resolve_tac ctxt @{thms exhale_field_acc_rel_assms_ref_eval} THEN'
                                                                      fastforce_tac ctxt [])
                        ]) ctxt) THEN'
          (Rmsg' "Exh Prove Sufficient Perm - Red Assert" (prove_red_expr_bpl_tac ctxt |> SOLVED') ctxt) THEN'
          (Rmsg' "Exh Prove Sufficient Perm - Success Condition" 
                      (simp_only_tac @{thms exhale_field_acc_rel_perm_success_def} ctxt THEN'
                       fastforce_tac ctxt @{thms of_rat_less_eq}) ctxt) THEN'
          (Rmsg' "Exh Prove Sufficient Perm - Finish Then Branch"
                     (resolve_tac ctxt @{thms rel_general_success_refl} THEN'
                      simp_only_tac @{thms exhale_field_acc_rel_perm_success_def exhale_field_acc_rel_assms_def} ctxt THEN'
                      (* We add RedLit_case to deal with the case when the permission is a literal *)
                      fast_force_tac_with_elims_simps ctxt @{thms TotalExpressions.RedLit_case} @{thms of_rat_less_eq} THEN'
                      assm_full_simp_solved_tac ctxt) ctxt) THEN'
       (Rmsg' "Exh Prove Sufficient Perm - Progress from then-branch" (progress_red_bpl_rel_tac ctxt) ctxt) THEN'

       (* else branch *)
       (Rmsg' "Exh Prove Sufficient Perm - Else Branch"
              (EVERY' [simplify_continuation ctxt,
                       resolve_tac ctxt @{thms rel_propagate_pre_2_only_state_rel},
                       progress_red_bpl_rel_tac ctxt,
                       resolve_tac ctxt @{thms rel_general_success_refl},
                       simp_only_tac @{thms exhale_field_acc_rel_perm_success_def} ctxt,
                       fastforce_tac ctxt @{thms prat_non_negative},
                       assm_full_simp_solved_tac ctxt]) ctxt) 

  fun upd_exhale_field_acc_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =    
    (Rmsg' "UpdExhField Init Progress" (rewrite_rel_general_tac ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField 1" (resolve_tac ctxt @{thms exhale_rel_field_acc_upd_rel}) ctxt) THEN'
    (Rmsg' "UpdExhField StateRel" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'    
   (* old version: (Rmsg' "UpdExhField Dom AuxPred" (fastforce_tac ctxt []) ctxt) THEN' *)
    (Rmsg' "UpdExhField Dom AuxPred" (#aux_var_disj_tac info ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField Wf TyRepr" (resolve_tac ctxt @{thms wf_ty_repr_basic}) ctxt) THEN'
    (Rmsg' "UpdExhField Wf Total Consistency" (resolve_tac ctxt [#consistency_wf_thm info]) ctxt) THEN'
    (Rmsg' "UpdExhField MaskDef Different" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField TyInterp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField MaskUpdateWf" (resolve_tac ctxt [@{thm mask_update_wf_concrete} OF [#ctxt_wf_thm info, @{thm wf_ty_repr_basic}]]) ctxt) THEN'
    (Rmsg' "UpdExhField MaskReadWf" (resolve_tac ctxt [@{thm mask_read_wf_concrete} OF [#ctxt_wf_thm info, @{thm wf_ty_repr_basic}]]) ctxt) THEN'
    (Rmsg' "UpdExhField MaskUpdateBpl" (assm_full_simp_solved_with_thms_tac @{thms update_mask_concrete_def ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField MaskReadBpl" (assm_full_simp_solved_with_thms_tac @{thms read_mask_concrete_def ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField MaskVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField FieldRel" ((#field_rel_single_tac info) ctxt) ctxt) THEN'
    (Rmsg' "UpdExhField RcvRel" (exp_rel_tac exp_rel_info ctxt) ctxt)

  fun atomic_exhale_field_acc_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) exh_field_acc_hint =
    case exh_field_acc_hint of
      FieldAccExhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm, exp_rel_perm_access_thm) =>
        (Rmsg' "ExhField 1" (resolve_tac ctxt @{thms exhale_rel_field_acc}) ctxt) THEN'
          (*(Rmsg' "ExhField wf rcv" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
          (Rmsg' "ExhField wf perm" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'*)
          (Rmsg' "ExhField wf subexpressions" (exps_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt 2) ctxt) THEN'   
          (Rmsg' "ExhField unfold current bigblock" (rewrite_rel_general_tac ctxt) ctxt) THEN'     
          (Rmsg' "ExhField 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
          (Rmsg' "ExhField 3 propagate" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
          (store_temporary_perm_exh_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
          (prove_perm_non_negative_exh_tac ctxt info lookup_aux_var_state_rel_thm) THEN'
          (prove_sufficient_perm_tac ctxt info exp_rel_info lookup_aux_var_state_rel_thm exp_rel_perm_access_thm) THEN'
          (upd_exhale_field_acc_tac ctxt info exp_rel_info)
    | _ => error("only support FieldAccExhHint")
  
  fun atomic_exhale_rel_inst_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) atomic_exh_hint = 
    case atomic_exh_hint of
      PureExpExhHint (exp_wf_rel_info, exp_rel_info) => 
         (Rmsg' "ExhPure exp init" (resolve_tac ctxt @{thms exhale_rel_pure}) ctxt) THEN'
         (Rmsg' "ExhPure wf extend" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
         (Rmsg' "ExhPure wf" (exp_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt |> SOLVED') ctxt) THEN'
         (Rmsg' "ExhPure progress after wf" (progress_tac ctxt) ctxt) THEN' 
         (Rmsg' "ExhPure exp rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
    | FieldAccExhHint _ => 
         atomic_exhale_field_acc_tac ctxt info no_def_checks_tac_opt atomic_exh_hint

\<close>


end
