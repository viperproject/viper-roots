theory InhaleRelML
imports Boogie_Lang.HelperML ExprWfRelML InhaleRel ViperBoogieHelperML
begin

ML \<open>

  val Rmsg' = run_and_print_if_fail_2_tac' 

  datatype 'a inhale_rel_hint = 
    AtomicInhHint of 'a 
  | StarInhHint of ( ('a inhale_rel_hint) * ('a inhale_rel_hint))
  | ImpInhHint of 
       exp_wf_rel_info *       
       exp_rel_info *
       ('a inhale_rel_hint)
  | NoInhHint (* used for debugging purposes *)

  type 'a atomic_inhale_rel_tac = (Proof.context -> basic_stmt_rel_info ->  (Proof.context -> basic_stmt_rel_info -> int -> tactic) option ->'a -> int -> tactic)

  type 'a inhale_rel_complete_hint = {
    inhale_stmt_rel_thm: thm, (* chooses the invariant instantiation *)
    inhale_rel_hint: 'a inhale_rel_hint
  }

  type 'a inhale_rel_info = {
    basic_info: basic_stmt_rel_info,
    atomic_inhale_rel_tac: 'a atomic_inhale_rel_tac,
    (* states that the invariant is an inhale relation invariant *)
    is_inh_rel_inv_thm: thm,
    (* if set, then it is a tactic that justifies the well-definedness simulation on a list of expressions
       without needing to perform well-definedness checks *)
    no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option
  }

  fun inhale_rel_aux_tac ctxt (info: 'a inhale_rel_info) (hint: 'a inhale_rel_hint) =
    case hint of
      StarInhHint (left_hint, right_hint) => 
        (Rmsg' "InhaleRel Star Init" (resolve_tac ctxt @{thms inhale_rel_star_2}) ctxt) THEN' 
        (Rmsg' "InhaleRel Star Inv" (resolve_tac ctxt [#is_inh_rel_inv_thm info]) ctxt) THEN'
        (inhale_rel_aux_tac ctxt info left_hint |> SOLVED') THEN'
        (inhale_rel_aux_tac ctxt info right_hint |> SOLVED')
    | ImpInhHint (exp_wf_rel_info, exp_rel_info, right_hint) => 
         (
           (Rmsg' "InhaleRel Imp Init" (resolve_tac ctxt @{thms inhale_rel_imp_2}) ctxt) THEN'
           (Rmsg' "InhaleRel Imp Inv" (resolve_tac ctxt [#is_inh_rel_inv_thm info]) ctxt) THEN'
           (Rmsg' "InhaleRel Imp 1" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
           (Rmsg' "InhaleRel wf cond" (exp_wf_rel_tac (#basic_info info) exp_wf_rel_info exp_rel_info ctxt (#no_def_checks_tac_opt info) |> SOLVED') ctxt) THEN'
           (Rmsg' "InhaleRel Imp 2" ((progress_tac ctxt) |> SOLVED') ctxt)
         ) THEN'
          (Rmsg' "InhaleRel empty else" (* empty else block *)                
                 ((unfold_bigblock_in_goal ctxt) THEN'
                 (assm_full_simp_solved_tac ctxt))
              ctxt)  THEN'
         (
           (Rmsg' "InhaleRel cond rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
         ) THEN'
         (
          (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
             variable for the recursive call to inhale_rel_tac *)
           simplify_continuation ctxt THEN'
           (Rmsg' "InhaleRel 3" (resolve_tac ctxt [@{thm inhale_propagate_post}]) ctxt) THEN'           
           (inhale_rel_aux_tac ctxt info right_hint |> SOLVED') THEN'
           (Rmsg' "InhaleRel 4" (progress_red_bpl_rel_tac ctxt) ctxt)
         )
    | AtomicInhHint atomicHint => (#atomic_inhale_rel_tac info) ctxt (#basic_info info) (#no_def_checks_tac_opt info) atomicHint
    | NoInhHint => K all_tac
 
  (* TODO: Once functions are introduced, then there can also be a good state assumption at the beginning.
           Might want to control this via the hints *)    
  fun inhale_rel_tac ctxt (info: 'a inhale_rel_info) (hint: 'a inhale_rel_hint) =
   (let val basic_info = #basic_info info in
     (Rmsg' "InhaleRel Init" (resolve_tac ctxt @{thms inhale_propagate_post}) ctxt) THEN'
     inhale_rel_aux_tac ctxt info hint THEN'
     (Rmsg' "InhaleRel Good State" (rewrite_red_bpl_rel_tac ctxt THEN'
                                    progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info)) ctxt)
    end)

\<close>

ML \<open>

  datatype atomic_inhale_rel_hint = 
    PureExpInhHint of 
       exp_wf_rel_info *
       exp_rel_info 
  | FieldAccInhHint of
       exp_wf_rel_info * 
       exp_rel_info *
       thm * (* auxiliary variable lookup var ty theorem *)
       thm (* auxiliary variable lookup var from state relation theorem *)

  fun inh_no_def_checks_tac ctxt (_: basic_stmt_rel_info) : int -> tactic  =
    resolve_tac ctxt [ @{thm assertion_framing_state_inh_exprs_wf_rel} ] THEN'
    blast_tac ctxt THEN' (* assertion_framing_state *)
    assm_full_simp_solved_tac ctxt  (* subexpression equality *)

  fun store_temporary_inh_perm_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_ty_thm =
        store_temporary_perm_tac 
         ctxt 
         info 
         exp_rel_info 
         lookup_aux_var_ty_thm
         (fn ctxt => blast_tac ctxt)

  fun prove_perm_non_negative_inh_tac ctxt (info: basic_stmt_rel_info) lookup_aux_var_state_rel_thm =
      (Rmsg' "Inh Prove Perm Nonnegative - Init" (resolve_tac ctxt @{thms rel_propagate_pre_assert_2}) ctxt) THEN'
      (Rmsg' "Inh Prove Perm Nonnegative - Introduce Facts" 
              (EVERY' [intro_fact_lookup_no_perm_const_tac ctxt (#tr_def_thm info),
              intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_state_rel_thm]) ctxt) THEN'
      (Rmsg' "Inh Prove Perm Nonnegative - Boogie Expression Reduction" (prove_red_expr_bpl_tac ctxt) ctxt) THEN'
      (Rmsg' "Inh Prove Perm Nonnegative - Success Condition" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "Inh Prove Perm Nonnegative - Finalize 1" (resolve_tac ctxt @{thms rel_general_success_refl}) ctxt) THEN'
       (* We add RedLit_case to deal with the case when the permission is a literal *)
      (Rmsg' "Inh Prove Perm Nonnegative - Finalize 2" (fast_force_tac (ctxt addEs @{thms TotalExpressions.RedLit_case})) ctxt) THEN'
      (Rmsg' "Inh Prove Perm Nonnegative - Finalize 3" (assm_full_simp_solved_tac ctxt) ctxt)

(* old version
  fun non_null_rcv_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =
    (Rmsg' "Inh apply non-null rcv" (eresolve_tac ctxt @{thms inhale_field_acc_non_null_rcv_rel}) ctxt) THEN'
    (Rmsg' "Inh non-null rcv 2" (assume_tac ctxt) ctxt) THEN'
    (Rmsg' "Inh non-null rcv rel" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
    (Rmsg' "Inh non-null null const" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "Inh non-null noperm const" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt)
*)

  fun non_null_rcv_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_state_rel_thm = 
   (Rmsg' "Inh Assume Rcv Non-Null - Init 1" (resolve_tac ctxt @{thms rel_propagate_pre_assume}) ctxt) THEN'
   (Rmsg' "Inh Assume Rcv Non-Null - Init 2" (resolve_tac ctxt @{thms conjI}) ctxt) THEN'
   (Rmsg' "Inh Assume Rcv Non-Null - Introduce Facts" 
            (EVERY' [intro_fact_lookup_no_perm_const_tac ctxt (#tr_def_thm info),
                     intro_fact_lookup_null_const_tac ctxt (#tr_def_thm info),
                     intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_state_rel_thm,
                     intro_fact_rcv_lookup_reduction ctxt exp_rel_info @{thm exp_rel_ref_access} 
                                 (fn ctxt => resolve_tac ctxt @{thms inhale_field_acc_rel_assm_ref_eval} THEN' blast_tac ctxt)]) ctxt) THEN'
   (Rmsg' "Inh Assume Rcv Non-Null - Synthesize Assume Condition" (prove_red_expr_bpl_tac ctxt) ctxt) THEN'
   (* We add RedLit_case to deal with the case when the permission is a literal *)
   (Rmsg' "Inh Assume Rcv Non-Null - Prove Assume Condition Holds" (fast_force_tac (add_simps @{thms inhale_acc_normal_premise_def} (ctxt addEs @{thms TotalExpressions.RedLit_case}) )) ctxt)

  fun inhale_rel_field_acc_upd_rel_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =
    (Rmsg' "inh field acc upd 0" (resolve_tac ctxt @{thms inhale_rel_field_acc_upd_rel}) ctxt) THEN'
    (Rmsg' "inh field acc upd 1" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd aux var disjoint" (#aux_var_disj_tac info ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd wf ty repr" (resolve_tac ctxt @{thms wf_ty_repr_basic}) ctxt) THEN'
    (Rmsg' "inh field acc upd def mask and eval mask same" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd ty interp eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "inh field acc mask update wf concrete" (resolve_tac ctxt [ @{thm mask_update_wf_concrete} OF [#ctxt_wf_thm info, @{thm wf_ty_repr_basic}]]) ctxt) THEN'
    (Rmsg' "inh field acc mask read wf concrete" (resolve_tac ctxt [ @{thm mask_read_wf_concrete} OF [#ctxt_wf_thm info, @{thm wf_ty_repr_basic}]]) ctxt) THEN'
    (Rmsg' "inh field acc upd 2" (assm_full_simp_solved_with_thms_tac @{thms update_mask_concrete_def ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd 3" (assm_full_simp_solved_with_thms_tac @{thms read_mask_concrete_def ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd 4" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "inh field acc field rel" (#field_rel_single_tac info ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd rcv rel" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt)

  fun atomic_inhale_field_acc_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) inh_field_acc_hint =
    case inh_field_acc_hint of
      FieldAccInhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm) =>
        (Rmsg' "InhField 1" (resolve_tac ctxt @{thms inhale_field_acc_rel}) ctxt) THEN'
          (*(Rmsg' "InhField wf rcv" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
          (Rmsg' "InhField wf perm" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'*)
          (Rmsg' "ExhField wf subexpressions" (exps_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt 2) ctxt) THEN'
          (Rmsg' "InhField unfold current bigblock" (rewrite_rel_general_tac ctxt) ctxt) THEN'     
          (Rmsg' "InhField 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
            (Rmsg' "InhField 2b red_ast_bpl_relI" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
            (store_temporary_inh_perm_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
            (prove_perm_non_negative_inh_tac ctxt info lookup_aux_var_state_rel_thm) THEN'  
            (non_null_rcv_tac ctxt info exp_rel_info lookup_aux_var_state_rel_thm) THEN'
            (inhale_rel_field_acc_upd_rel_tac ctxt (info: basic_stmt_rel_info) exp_rel_info)
    | _ => error("only support FieldAccInhHint")
  
  fun atomic_inhale_rel_inst_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) atomic_inh_hint = 
    case atomic_inh_hint of
      PureExpInhHint (exp_wf_rel_info, exp_rel_info) => 
         (Rmsg' "InhPure exp init" (resolve_tac ctxt @{thms inhale_pure_exp_rel}) ctxt) THEN'
         (Rmsg' "InhPure wf extend" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
         (Rmsg' "InhPure wf" (exp_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt |> SOLVED') ctxt) THEN'
         (Rmsg' "InhPure progress after wf" (progress_tac ctxt) ctxt) THEN' 
         (Rmsg' "InhPure exp rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
    | FieldAccInhHint _ => 
         (Rmsg' "InhField acc propagate" (resolve_tac ctxt @{thms inhale_propagate_post}) ctxt) THEN'
         atomic_inhale_field_acc_tac ctxt info no_def_checks_tac_opt atomic_inh_hint THEN'
         (Rmsg' "InhField acc good state" (progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm info) (#tr_def_thm info)) ctxt)

\<close>


end
