theory StmtRelML
imports Boogie_Lang.HelperML ExprWfRelML StmtRel InhaleRelML ViperBoogieHelperML
begin

ML \<open>
  val Rmsg' = run_and_print_if_fail_2_tac' 

  fun zero_mask_lookup_tac ctxt tr_def_thm =
    resolve_tac ctxt [@{thm boogie_const_rel_lookup_2[where ?const = CZeroMask]}] THEN'
    resolve_tac ctxt [@{thm state_rel_boogie_const}] THEN'
    blast_tac ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_tac ctxt

  datatype 'a stmt_rel_hint = 
    AtomicHint of 'a 
  | SeqnHint of ('a stmt_rel_hint) list
  | IfHint of 
       exp_wf_rel_info *       
       exp_rel_info *
       ('a stmt_rel_hint) * (* thn branch *)
       ('a stmt_rel_hint)   (* els branch *)
  | NoHint (* used for debugging purposes *)      

  type ('a,'i) atomic_rel_tac = (Proof.context -> 'i inhale_rel_info ->  basic_stmt_rel_info -> 'a -> int -> tactic)

  type ('a, 'i) stmt_rel_info = {
    basic_stmt_rel_info: basic_stmt_rel_info,
    atomic_rel_tac: ('a,'i) atomic_rel_tac,
    inhale_rel_info: 'i inhale_rel_info
  }

 fun stmt_rel_tac ctxt (info: ('a, 'i) stmt_rel_info) (stmt_rel_hint: 'a stmt_rel_hint) =
    case stmt_rel_hint of 
       SeqnHint [] => resolve_tac ctxt [@{thm stmt_rel_skip}]
    |  SeqnHint [_] => error "SeqnHint with single node appears"
    |  SeqnHint (h::hs) => stmt_rel_tac_seq ctxt info (h::hs)
    | _ => stmt_rel_single_stmt_tac ctxt info stmt_rel_hint
and
     stmt_rel_tac_seq _ _ [] = K all_tac
   | stmt_rel_tac_seq ctxt (info: ('a, 'i) stmt_rel_info) [h] =
       stmt_rel_tac ctxt info h
   | stmt_rel_tac_seq ctxt (info: ('a, 'i) stmt_rel_info) (h1 :: h2 :: hs) = 
       resolve_tac ctxt [@{thm stmt_rel_seq_same_rel}] THEN'
       stmt_rel_tac ctxt info h1 THEN'
       stmt_rel_tac_seq ctxt info (h2 :: hs)
and 
     stmt_rel_single_stmt_tac _ _ NoHint = K all_tac
   | stmt_rel_single_stmt_tac ctxt (info: ('a, 'i) stmt_rel_info) hint_hd =
    (* Each statement associated with a hint is translated by the actual encoding followed by 
       \<open>assume state(Heap, Mask)\<close>. This is why we apply a propagation rule first. *)
    resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}] THEN'
    (
      case hint_hd of
        AtomicHint a => (#atomic_rel_tac info) ctxt (#inhale_rel_info info) (#basic_stmt_rel_info info) a
      | IfHint (exp_wf_rel_info, exp_rel_info, thn_hint, els_hint) =>
           (Rmsg' "If0" (resolve_tac ctxt [@{thm stmt_rel_if}]) ctxt) THEN'
           (
             (Rmsg' "If1" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
             (Rmsg' "If wf cond" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
             (Rmsg' "If2" ((progress_tac ctxt) |> SOLVED') ctxt)
           ) THEN'
           (
             (Rmsg' "If cond rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
           ) THEN'
           (
            (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
               variable for the recursive call to stmt_rel_tac *)
             simplify_continuation ctxt THEN'
             (Rmsg' "If3" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN'           
             (stmt_rel_tac ctxt info thn_hint |> SOLVED') THEN'
             (Rmsg' "If4" (progress_tac ctxt) ctxt)
           ) THEN'
           (
            (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
               variable for the recursive call to stmt_rel_tac *)
            simplify_continuation ctxt THEN'
            (Rmsg' "If5" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN'           
            (stmt_rel_tac ctxt info els_hint |> SOLVED') THEN'
            (Rmsg' "If6" (progress_tac ctxt) ctxt)
           )
      | _ => error "unsupported hint in stmt_rel_single_stmt_tac"
    ) THEN'
    (* now reduce \<open>assume state(Heap, Mask)\<close> *)
    progress_assume_good_state_tac ctxt (#ctxt_wf_thm (#basic_stmt_rel_info info)) (#tr_def_thm (#basic_stmt_rel_info info))
\<close>

ML \<open>

  datatype atomic_rel_hint = 
     AssignHint of 
       exp_wf_rel_info *
       exp_rel_info * (* for relating RHS of assignment *)
       thm (* lookup target theorem *)
  | FieldAssignHint of
       exp_wf_rel_info * (* well-definedness receiver *)
       exp_wf_rel_info * (* well-definedness rhs *)
       exp_rel_info * (* receiver *)
       exp_rel_info   (* rhs *)
  | InhaleHint of (atomic_inhale_rel_hint inhale_rel_hint)

  fun red_assign_tac ctxt (basic_stmt_rel_info : basic_stmt_rel_info) exp_wf_rel_info (exp_rel_info : exp_rel_info) lookup_bpl_target_thm =
    (* TODO     (Rmsg' "Assign1" (resolve_tac ctxt [@{thm assign_rel_simple[where ?Trep=ty_repr_basic]}]) ctxt) THEN' *)
    (Rmsg' "Assign1" (resolve_tac ctxt [@{thm assign_rel_simple}]) ctxt) THEN'
    (Rmsg' "Assign2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign3" ((#var_context_vpr_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign3b" (simp_only_tac [#type_interp_econtext basic_stmt_rel_info] ctxt THEN'
                        resolve_tac ctxt @{thms type_interp_rel_wf_vbpl_basic}) ctxt) THEN'
    
    (* well-def RHS *)
    (* begin *)
    (Rmsg' "Assign4" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
    (Rmsg' "Assign Wf RHS" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign5" (progress_tac ctxt) ctxt) THEN'
    (* end *)
    
    (Rmsg' "Assign6" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign7" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN' 
    
    (* prove updated Viper and Boogie states are still in relation *)
    (* begin *)
    (Rmsg' "Assign8" (resolve_tac ctxt [@{thm state_rel_store_update_2}]) ctxt) THEN'
    (Rmsg' "Assign9" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign10" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign11" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign12" ( (#var_rel_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign13" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign14" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign15" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (* end *)
        
    (Rmsg' "Assign16" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)


  fun field_rel_single_inst_tac field_rel_tac field_lookup_tac ctxt =
    resolve_tac ctxt [@{thm field_rel_single_intro}] THEN'
    field_lookup_tac ctxt THEN'
    (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) THEN'
    field_rel_tac ctxt THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt

  fun wf_writeable_field_rel_tac rcv_exp_rel_info (basic_stmt_rel_info : basic_stmt_rel_info) ctxt =
     (* need to first progress the configuration in case the currently active bigblock is not unfolded or
        if the current bigblock is empty *)
     resolve_tac ctxt [@{thm wf_rel_extend_2_same_rel}] THEN' 
     progress_tac ctxt THEN'
     (Rmsg' "WfWriteableField1" (resolve_tac ctxt [@{thm syn_field_access_writeable_wf_rel} OF 
                                                     [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]
                                                  ]) ctxt) THEN'
     (Rmsg' "WfWriteableField2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField3" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info, @{thm read_mask_concrete_def}] ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField4" (simp_tac_with_thms [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'     
     (Rmsg' "WfWriteableField5" (resolve_tac ctxt [@{thm mask_read_wf_concrete} OF 
                                                     [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]
                                                  ]) ctxt) THEN'
     (Rmsg' "WfWriteableField6" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField7 (exp rel rcv)" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField8" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField9 (single field rel)" ((#field_rel_single_tac basic_stmt_rel_info) ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField10" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt)

     

  fun field_assign_rel_tac ctxt (basic_stmt_rel_info : basic_stmt_rel_info) atomic_hint =
    (case atomic_hint of 
       FieldAssignHint (rcv_wf_rel_info, rhs_wf_rel_info, rcv_exp_rel_info, rhs_exp_rel_info) =>
       (Rmsg' "FieldAssign1" (resolve_tac ctxt [@{thm field_assign_rel_inst[OF wf_ty_repr_basic]}]) ctxt) THEN'
       (Rmsg' "FieldAssign2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign3" (simp_tac_with_thms [#tr_def_thm basic_stmt_rel_info] ctxt THEN'
                              resolve_tac ctxt [@{thm heap_update_wf_concrete} OF [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]])
                               ctxt) THEN'
       (Rmsg' "FieldAssign4" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign5" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign6" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (* TODO: need to use wf_rel_extend *)
       (Rmsg' "FieldAssign7 (Wf Rcv)" (exp_wf_rel_non_trivial_tac rcv_wf_rel_info rcv_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign8 (Wf Rhs)" (exp_wf_rel_non_trivial_tac rhs_wf_rel_info rhs_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign9 (Wf Writeable Field)" (wf_writeable_field_rel_tac rcv_exp_rel_info basic_stmt_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign10" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign11" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info, @{thm update_heap_concrete_def}, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign12 (Exp Rel Rcv)" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign13 (single field rel)" ((#field_rel_single_tac basic_stmt_rel_info) ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign14 (Exp Rel Rhs)" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt)

    | _ => error "field assign rel tac only handles field assignment"
    )

  fun atomic_rel_inst_tac ctxt (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (basic_info : basic_stmt_rel_info) (atomic_hint : atomic_rel_hint)  = 
    (case atomic_hint of 
        AssignHint (exp_wf_rel_info, exp_rel_info, lookup_bpl_target_thm) => 
               red_assign_tac ctxt basic_info exp_wf_rel_info exp_rel_info lookup_bpl_target_thm
     |  FieldAssignHint _ => field_assign_rel_tac ctxt basic_info atomic_hint
     | InhaleHint inh_rel_hint => 
        resolve_tac ctxt @{thms inhale_stmt_rel} THEN'
        inhale_rel_tac ctxt inhale_info inh_rel_hint        
    )
\<close>

end