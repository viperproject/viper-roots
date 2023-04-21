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

  type 'a atomic_inhale_rel_tac = (Proof.context -> basic_stmt_rel_info -> 'a -> int -> tactic)

  type 'a inhale_rel_info = {
    basic_info: basic_stmt_rel_info,
    atomic_inhale_rel_tac: 'a atomic_inhale_rel_tac
  }

  fun inhale_rel_aux_tac ctxt (info: 'a inhale_rel_info) (hint: 'a inhale_rel_hint) =
    case hint of
      StarInhHint (left_hint, right_hint) => 
        (Rmsg' "InhaleRel Star" (resolve_tac ctxt [@{thm inhale_rel_star}]) ctxt) THEN' 
        (inhale_rel_aux_tac ctxt info left_hint |> SOLVED') THEN'
        (inhale_rel_aux_tac ctxt info right_hint |> SOLVED')
    | ImpInhHint (exp_wf_rel_info, exp_rel_info, right_hint) => 
         (
           (Rmsg' "ImpInh 1" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
           (Rmsg' "ImpInh wf cond" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
           (Rmsg' "ImpInh 2" ((progress_tac ctxt) |> SOLVED') ctxt)
         ) THEN'
          (Rmsg' "ImpInh empty else" (* empty else block *)                
                 ((unfold_bigblock_in_goal ctxt) THEN'
                 (assm_full_simp_solved_tac ctxt))
              ctxt)  THEN'
         (
           (Rmsg' "ImpInh cond rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
         ) THEN'
         (
          (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
             variable for the recursive call to inhale_rel_tac *)
           simplify_continuation ctxt THEN'
           (Rmsg' "ImpInh 3" (resolve_tac ctxt [@{thm inhale_propagate_post}]) ctxt) THEN'           
           (inhale_rel_aux_tac ctxt info right_hint |> SOLVED') THEN'
           (Rmsg' "ImpInh 4" (progress_tac ctxt) ctxt)
         )
    | AtomicInhHint atomicHint => (#atomic_inhale_rel_tac info) ctxt (#basic_info info) atomicHint
    | NoInhHint => K all_tac
 
  (* TODO: Once functions are introduced, then there can also be a good state assumption at the beginning.
           Might want to control this via the hints *)    
  fun inhale_rel_tac ctxt (info: 'a inhale_rel_info) (hint: 'a inhale_rel_hint) =
   (let val basic_info = #basic_info info in
     (Rmsg' "InhaleRel 1" (resolve_tac ctxt @{thms inhale_propagate_post}) ctxt) THEN'
     inhale_rel_aux_tac ctxt info hint THEN'
     (Rmsg' "InhaleRel 2 Progress" (progress_assume_good_state_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info)) ctxt)
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
       thm (* auxiliary variable lookup var ty theorem *)

  (*TODO: generalize such that it captures a more general version *)
  fun store_temporary_perm_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_ty_thm =
    (Rmsg' "store perm 1" (eresolve_tac ctxt @{thms store_temporary_perm_rel}) ctxt) THEN'
    (Rmsg' "store perm eval perm" (blast_tac ctxt) ctxt) THEN'
    (Rmsg' "store perm rel perm" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
    (Rmsg' "store perm disjointness" ((#aux_var_disj_tac info ctxt) |> SOLVED') ctxt) THEN'
    (Rmsg' "store perm lookup" (assm_full_simp_solved_with_thms_tac [lookup_aux_var_ty_thm] ctxt) ctxt) THEN'
    (Rmsg' "store perm 2" (assm_full_simp_solved_tac ctxt) ctxt)

  fun non_null_rcv_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =
    (Rmsg' "apply non-null rcv" (eresolve_tac ctxt @{thms inhale_field_acc_non_null_rcv_rel}) ctxt) THEN'
    (Rmsg' "non-null rcv 2" (assume_tac ctxt) ctxt) THEN'
    (Rmsg' "non-null rcv rel" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
    (Rmsg' "non-null null const" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
    (Rmsg' "non-null noperm const" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt)

  fun inhale_rel_field_acc_upd_rel_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =
    (Rmsg' "inh field acc upd 0" (resolve_tac ctxt @{thms inhale_rel_field_acc_upd_rel}) ctxt) THEN'
    (Rmsg' "inh field acc upd 1" (assume_tac ctxt) ctxt) THEN'
    (Rmsg' "inh field acc upd aux var disjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
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

  fun atomic_inhale_field_acc_tac ctxt (info: basic_stmt_rel_info) inh_field_acc_hint =
    case inh_field_acc_hint of
      FieldAccInhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm) =>
        (Rmsg' "InhField 1" (resolve_tac ctxt @{thms inhale_field_acc_rel}) ctxt) THEN'
          (Rmsg' "InhField wf rcv" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
          (Rmsg' "InhField wf perm" ((exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
  
          (Rmsg' "InhField 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
            (store_temporary_perm_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
            (Rmsg' "InhField Pos Perm Nontrivial" (resolve_tac ctxt @{thms pos_perm_rel_nontrivial_inh}) ctxt) THEN'
              (Rmsg' "InhField zero perm const" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  
          (Rmsg' "InhField 3 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_success_2}) ctxt) THEN'
            (Rmsg' "InhField 4" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
            (non_null_rcv_tac ctxt info exp_rel_info) THEN'
            (inhale_rel_field_acc_upd_rel_tac ctxt (info: basic_stmt_rel_info) exp_rel_info)
    | _ => error("only support FieldAccInhHint")
  
  fun atomic_inhale_rel_inst_tac ctxt (info: basic_stmt_rel_info) atomic_inh_hint = 
    case atomic_inh_hint of
      PureExpInhHint _ => error ("do not support pure inhale")
    | FieldAccInhHint _ => 
         (resolve_tac ctxt @{thms inhale_propagate_post}) THEN'
         atomic_inhale_field_acc_tac  ctxt info atomic_inh_hint THEN'
         progress_assume_good_state_tac ctxt (#ctxt_wf_thm info) (#tr_def_thm info)
\<close>


end
