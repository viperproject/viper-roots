theory StmtRelML
imports Boogie_Lang.HelperML ExprWfRelML StmtRel InhaleRelML ExhaleRelML ViperBoogieHelperML
begin

ML \<open>
  val Rmsg' = run_and_print_if_fail_2_tac' 
                  
  fun zero_mask_lookup_tac ctxt tr_def_thm =
    resolve_tac ctxt [@{thm boogie_const_rel_lookup_2[where ?const = CZeroMask]}] THEN'
    resolve_tac ctxt [@{thm state_rel_boogie_const_rel}] THEN'
    blast_tac ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_tac ctxt

  datatype 'a stmt_rel_hint = 
    AtomicHint of 'a 
  | ScopeHint of thm * ('a stmt_rel_hint) (* lookup decl theorem for scoped variable, and hint for body *)
  | SeqnHint of ('a stmt_rel_hint) list
  | IfHint of 
       exp_wf_rel_info *       
       exp_rel_info *
       ('a stmt_rel_hint) * (* thn branch *)
       ('a stmt_rel_hint)   (* els branch *)
  | NoHint (* used for debugging purposes *)      

  type ('a, 'i, 'e) atomic_rel_tac = (Proof.context -> 'i inhale_rel_info -> 'e exhale_rel_info ->  basic_stmt_rel_info -> 'a -> int -> tactic)

  type ('a, 'i, 'e) stmt_rel_info = {
    basic_stmt_rel_info: basic_stmt_rel_info,
    atomic_rel_tac: ('a, 'i, 'e) atomic_rel_tac,
    inhale_rel_info: 'i inhale_rel_info,
    exhale_rel_info: 'e exhale_rel_info
  }

 (* tactic to unfold current bigblock (or progress empty bigblock) for a stmt_rel goal, 
    see comment for progress_red_bpl_rel_tac *)
 fun progress_stmt_rel_tac ctxt =
   resolve_tac ctxt @{thms stmt_rel_propagate_pre_2} THEN'
   progress_red_bpl_rel_tac ctxt

 fun stmt_rel_tac ctxt (info: ('a, 'i, 'e) stmt_rel_info) (stmt_rel_hint: 'a stmt_rel_hint) =
    case stmt_rel_hint of 
      SeqnHint [] => (Rmsg' "Skip" (resolve_tac ctxt [@{thm stmt_rel_skip}]) ctxt)
    | SeqnHint [_] => error "SeqnHint with single node appears"
    | SeqnHint (h::hs) => stmt_rel_tac_seq ctxt info (h::hs)
   (* scopes are handled here, because in the Scala AST they are bound to sequential composition
      in particular, there is no "good state" assumption just for a scope (if scopes were instead handled
      in stmt_rel_single_stmt_tac, then "good state" assumptions would be expected) *)
    | ScopeHint (lookup_decl_thm, body_hint) =>
       (Rmsg' "Scope init" (resolve_tac ctxt [@{thm scoped_var_stmt_rel_simplify_tr} OF [#consistency_wf_thm (#basic_stmt_rel_info info)]]) ctxt) THEN'
       (Rmsg' "Scope domain type eq" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
       (Rmsg' "Scope type interp eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
       (Rmsg' "Scope empty rtype" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
       (Rmsg' "Scope state rel" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
       (Rmsg' "Scope progress to havoc" (progress_red_bpl_rel_tac ctxt) ctxt) THEN'
       (Rmsg' "Scope variable disjointness" (#aux_var_disj_tac (#basic_stmt_rel_info info) ctxt) ctxt) THEN'
       (Rmsg' "Scope lookup var decl" (assm_full_simp_solved_with_thms_tac [lookup_decl_thm] ctxt) ctxt) THEN'
       (Rmsg' "Scope vpr to bpl ty" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
       (Rmsg' "Scope simplify translation record" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
       (stmt_rel_tac ctxt info body_hint |> SOLVED')
    | _ => stmt_rel_single_stmt_tac ctxt info stmt_rel_hint
and
     stmt_rel_tac_seq _ _ [] = K all_tac
   | stmt_rel_tac_seq ctxt (info: ('a, 'i, 'e) stmt_rel_info) [h] =
       stmt_rel_tac ctxt info h
   | stmt_rel_tac_seq ctxt (info: ('a, 'i, 'e) stmt_rel_info) (h1 :: h2 :: hs) = 
       resolve_tac ctxt [@{thm stmt_rel_seq_same_rel}] THEN'
       stmt_rel_tac ctxt info h1 THEN'
       stmt_rel_tac_seq ctxt info (h2 :: hs)
and 
     stmt_rel_single_stmt_tac _ _ NoHint = K all_tac         
   | stmt_rel_single_stmt_tac ctxt (info: ('a, 'i, 'e) stmt_rel_info) hint_hd =
    (* Each statement associated with a hint is translated by the actual encoding followed by 
       \<open>assume state(Heap, Mask)\<close>. This is why we apply a propagation rule first. *)
    (Rmsg' "stmt_rel_propagate_2_init" (resolve_tac ctxt [@{thm stmt_rel_propagate_3}]) ctxt) THEN'
    (
      case hint_hd of
        AtomicHint a => (#atomic_rel_tac info) ctxt (#inhale_rel_info info) (#exhale_rel_info info) (#basic_stmt_rel_info info) a
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
            (* Apply propagation rule here, so that target program point in stmt_rel is a schematic 
               variable for the recursive call to stmt_rel_tac (important, since then it is fine 
               to progress to an empty block essentially consuming all big blocks, instead of
               having to progress to the big block after the if-statement). Same for else-branch. *)
             simplify_continuation ctxt THEN'
             (Rmsg' "If3 Then" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN'
             (* rewrite then-branch, since block will be folded *)
             (Rmsg' "If4 Then" (progress_stmt_rel_tac ctxt) ctxt) THEN'                    
             (stmt_rel_tac ctxt info thn_hint |> SOLVED') THEN'
             (Rmsg' "If5 Then" (progress_red_bpl_rel_tac ctxt) ctxt)
           ) THEN'
           (
            simplify_continuation ctxt THEN'
            (Rmsg' "If3 Else" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN' 
            (* rewrite else-branch, since block will be folded *)
            (Rmsg' "If4 Else" (progress_stmt_rel_tac ctxt) ctxt) THEN' 
            (stmt_rel_tac ctxt info els_hint |> SOLVED') THEN'
            (Rmsg' "If5 Else" (progress_red_bpl_rel_tac ctxt) ctxt)
           ) THEN'
           (rewrite_red_bpl_rel_tac ctxt) (*rewrite here to make sure good state can be progressed after *)
      | _ => error "unsupported hint in stmt_rel_single_stmt_tac"
    ) THEN'
    (* Now reduce \<open>assume state(Heap, Mask)\<close> or otherwise progress without executing a Boogie command
       (one example where an extra good state assumption does not appear here is when running the tactic
        in cases where inhale was invoked directly in the InhaleModule instead of via translateStmt
        such as when inhaling the precondition).
       It might be better to control this via hints, because this tactic may reduce a good state
       assumption that should not be reduced at this point. *)
     (Rmsg' "Progress Good State" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm (#basic_stmt_rel_info info)) (#tr_def_thms (#basic_stmt_rel_info info))) ORELSE' (progress_red_bpl_rel_tac ctxt)) ctxt)
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
  | InhaleHint of (atomic_inhale_rel_hint inhale_rel_complete_hint)
  | ExhaleHint of (atomic_exhale_rel_hint exhale_rel_complete_hint)
  | AssertHint of (atomic_exhale_rel_hint assert_rel_complete_hint)
  | MethodCallHint of 
       string * (* callee name *)
       thm list * (* Boogie return variable lookup decl theorem *)
       (atomic_inhale_rel_hint inhale_rel_info) *
       (atomic_exhale_rel_hint exhale_rel_info) *
       (atomic_exhale_rel_hint exhale_rel_complete_hint) * (* exhale pre *)
       (atomic_inhale_rel_hint inhale_rel_complete_hint)   (* inhale post *)

  fun red_assign_tac ctxt (basic_stmt_rel_info : basic_stmt_rel_info) exp_wf_rel_info (exp_rel_info : exp_rel_info) lookup_bpl_target_thm =
    (Rmsg' "Assign 1" (resolve_tac ctxt [@{thm var_assign_rel_inst} OF [#consistency_wf_thm basic_stmt_rel_info]]) ctxt) THEN'
    (Rmsg' "Assign StateRel Eq" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign Consistent" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign VprTy" ((#var_context_vpr_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign TyRelWf" (simp_only_tac [#type_interp_econtext basic_stmt_rel_info] ctxt THEN'
                        resolve_tac ctxt @{thms type_interp_rel_wf_vbpl_basic}) ctxt) THEN'
    (Rmsg' "Assign EmptyRtype" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    
    (* well-def RHS *)
    (* begin *)
    (Rmsg' "Assign4" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
    (Rmsg' "Assign Wf RHS" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign5" (progress_tac ctxt) ctxt) THEN'
    (* end *)

    (Rmsg' "Assign var translation" ( (#var_rel_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    
    (Rmsg' "Assign LHS Bpl Ty" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign TyRel" (assm_full_simp_solved_with_thms_tac [@{thm ty_repr_basic_def}] ctxt) ctxt) THEN' 
    (Rmsg' "Assign Rhs Rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)   


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
     (Rmsg' "WfWriteableField MaskRead Wf" (resolve_tac ctxt [@{thm mask_read_wf_concrete} OF [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]]) ctxt) THEN'
     (Rmsg' "WfWriteableField2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField3" (assm_full_simp_solved_with_thms_tac (@{thm read_mask_concrete_def} :: (#tr_def_thms basic_stmt_rel_info)) ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField6" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField7 (exp rel rcv)" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField8" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField9 (single field rel)" ((#field_rel_single_tac basic_stmt_rel_info) ctxt) ctxt) THEN'
     (Rmsg' "WfWriteableField10" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt)     

  fun field_assign_rel_tac ctxt (basic_stmt_rel_info : basic_stmt_rel_info) atomic_hint =
    (case atomic_hint of 
       FieldAssignHint (rcv_wf_rel_info, rhs_wf_rel_info, rcv_exp_rel_info, rhs_exp_rel_info) =>
       (Rmsg' "FieldAssign 1" (resolve_tac ctxt [@{thm field_assign_rel_inst} OF [@{thm wf_ty_repr_basic}, #consistency_wf_thm basic_stmt_rel_info]]) ctxt) THEN'
       (Rmsg' "FieldAssign RStateRel" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapVarDefSame" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign DomainType" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign TypeInterp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapUpdWf" (resolve_tac ctxt [@{thm heap_update_wf_concrete} OF [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]])
                                         ctxt) THEN'
       (* TODO: need to use wf_rel_extend *)
       (Rmsg' "FieldAssign7 (Wf Rcv)" (exp_wf_rel_non_trivial_tac rcv_wf_rel_info rcv_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign8 (Wf Rhs)" (exp_wf_rel_non_trivial_tac rhs_wf_rel_info rhs_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign9 (Wf Writeable Field)" (wf_writeable_field_rel_tac rcv_exp_rel_info basic_stmt_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapVar" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapUpdateBpl" (assm_full_simp_solved_with_thms_tac ([@{thm update_heap_concrete_def}, @{thm ty_repr_basic_def}] @ #tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign Exp Rel Rcv" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign FieldRel" ((#field_rel_single_tac basic_stmt_rel_info) ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign Exp Rel Rhs" (exp_rel_tac rcv_exp_rel_info ctxt) ctxt)

    | _ => error "field assign rel tac only handles field assignment"
    )

  fun exhale_revert_state_relation ctxt (basic_info: basic_stmt_rel_info) = 
    resolve_tac ctxt @{thms red_ast_bpl_rel_weaken_input} THEN'
    resolve_tac ctxt @{thms state_rel_set_def_to_eval} THEN'
    assm_full_simp_solved_tac ctxt THEN'
    resolve_tac ctxt @{thms red_ast_bpl_rel_input_implies_output} THEN'
    assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_info) ctxt
                                                                                   
  fun exhale_havoc_tac ctxt (basic_info: basic_stmt_rel_info) (lookup_decl_exhale_heap_thm: thm) =
    let val tr_thms = #tr_def_thms basic_info in
      (Rmsg' "exhale havoc 1" (resolve_tac ctxt @{thms exhale_stmt_rel_finish}) ctxt) THEN'
      (Rmsg' "exhale havoc StateRel"  (assm_full_simp_solved_with_thms_tac tr_thms ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc CtxtWf"  (resolve_tac ctxt [#ctxt_wf_thm basic_info]) ctxt) THEN'
      (Rmsg' "exhale havoc WfTyRepr"  (resolve_tac ctxt @{thms wf_ty_repr_basic}) ctxt) THEN'
      (Rmsg' "exhale havoc ProgramTotal" (resolve_tac ctxt [@{thm HOL.sym} OF [#vpr_program_ctxt_eq_thm basic_info]]) ctxt) THEN'
      (Rmsg' "exhale havoc DomainType" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc WellDefSame" (assm_full_simp_solved_with_thms_tac tr_thms ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc IdOnKnownLocsName" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc TypeInterp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc StateCons" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc ElemExhaleState" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc HeapVar" (assm_full_simp_solved_with_thms_tac tr_thms ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc MaskVar" (assm_full_simp_solved_with_thms_tac tr_thms ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc LookupDeclExhaleHeap" (assm_full_simp_solved_with_thms_tac [@{thm ty_repr_basic_def},  lookup_decl_exhale_heap_thm] ctxt) ctxt) THEN'
      (Rmsg' "exhale havoc ExhaleHeapFresh" (#aux_var_disj_tac basic_info ctxt) ctxt)
    end

  fun exhale_pure_no_havoc_tac ctxt =
    (Rmsg' "exhale no havoc init" (resolve_tac ctxt @{thms exhale_pure_stmt_rel_upd_havoc}) ctxt) THEN'
    (* The "ORELSE' blast_tac" case was added because for some reason simp_then_if_not_solved_blast_tac did not work.
       For that example, when the goal was copied into the Isabelle GUI, then running simp_then_if_not_solved_blast_tac 
       worked. It is not clear why. *)
    (Rmsg' "exhale no havoc state rel" (simp_then_if_not_solved_blast_tac ctxt ORELSE' blast_tac ctxt) ctxt) THEN'
    (Rmsg' "exhale no havoc success cond" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "exhale no havoc pure assertion cond" (assm_full_simp_solved_tac ctxt) ctxt)

  fun normal_exhale_rel_tac ctxt (info: 'a exhale_rel_info) (hint: 'a normal_exhale_rel_complete_hint) =    
    (Rmsg' "stmt rel exhale pre propagate" (resolve_tac ctxt @{thms exhale_rel_propagate_pre_no_inv_same_exh}) ctxt) THEN'
    (Rmsg' "stmt rel exhale propagate progress" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN' (progress_red_bpl_rel_tac ctxt)) ctxt) THEN'
(*  old version: (Rmsg' "stmt rel exhale track well-def" (resolve_tac ctxt [@{thm red_ast_bpl_rel_weaken_input} OF @{thms state_rel_def_same_to_state_rel}] THEN' simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'*)
    (Rmsg' "stmt rel exhale track well-def propagate" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive}) ctxt) THEN'
    (Rmsg' "stmt rel exhale track well-def" (resolve_tac ctxt @{thms red_ast_bpl_rel_to_state_rel} THEN' simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
    (Rmsg' "setup well-def state exhale" ((#setup_well_def_state_tac hint) (#basic_info info) ctxt) ctxt) THEN'
    exhale_rel_aux_tac ctxt info (#exhale_rel_hint hint) THEN'
    (Rmsg' "stmt rel exhale havoc pre propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2_only_state_rel}) ctxt) THEN'
    (* apply transitive rule such to make sure that the active big block before exhale_finish_tac is unfolded *)
    (Rmsg' "stmt rel exhale red ast bpl transitive" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive_3}) ctxt) THEN'
      (Rmsg' "exhale revert state relation" (exhale_revert_state_relation ctxt (#basic_info info)) ctxt) THEN'
      (Rmsg' "stmt rel exhale progress" (progress_red_bpl_rel_tac ctxt) ctxt) THEN'
    (case (#lookup_decl_exhale_heap hint) of
         SOME lookup_decl_exhale_heap_thm =>  
            (Rmsg' "stmt rel exhale havoc rel intro" (resolve_tac ctxt @{thms rel_intro_no_fail}) ctxt) THEN'
            exhale_havoc_tac ctxt (#basic_info info) lookup_decl_exhale_heap_thm
       | NONE => exhale_pure_no_havoc_tac ctxt
    )

  fun exhale_rel_setup_well_def_tac (setup_well_def_tac: Proof.context -> int -> tactic) ctxt =
    (Rmsg' "stmt rel assert exhale rel pre propagate" (resolve_tac ctxt @{thms exhale_rel_propagate_pre_no_inv}) ctxt) THEN'
    (Rmsg' "stmt rel assert propagate progress" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN' (progress_red_bpl_rel_tac ctxt)) ctxt) THEN'
    (Rmsg' "stmt rel assert setup well-def state exhale" (setup_well_def_tac ctxt) ctxt)

  fun assert_rel_tac ctxt (info: 'a exhale_rel_info) (hint: 'a assert_rel_complete_hint) =
     exhale_rel_aux_tac ctxt info (#exhale_rel_hint hint) THEN'
    (Rmsg' "stmt rel assert reset state" ((#reset_state_tac hint) (#basic_info info) ctxt) ctxt)
  
  fun assert_rel_init_tac_standard setup_assert_state_tacs (basic_info: basic_stmt_rel_info) (setup_well_def_tac: Proof.context -> int -> tactic) ctxt =    
    (Rmsg' "assert rel invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel setup assert propagate" (resolve_tac ctxt @{thms exhale_rel_propagate_pre_no_inv}) ctxt) THEN'
    (Rmsg' "assert rel setup assert state tac" 
          ( EVERY'_red_ast_bpl_rel_transitive_custom ctxt 
            @{thm red_ast_bpl_rel_transitive_with_inv_capture_state[where ?Q="\<lambda>\<omega>. fst \<omega> = snd \<omega>"]}
           (map (fn tac => tac basic_info) setup_assert_state_tacs)) ctxt) THEN'
    (Rmsg' "assert rel show state rel capture init 1" (resolve_tac ctxt @{thms red_ast_bpl_rel_input_implies_output}) ctxt) THEN'
    (Rmsg' "assert rel show state rel capture init 2" (state_rel_capture_state_intro ctxt) ctxt) THEN'
    exhale_rel_setup_well_def_tac setup_well_def_tac ctxt THEN'
    (* abstract captured state such that AuxPred does not depend on state, otherwise automation does not work
       we abstract at this point, because at this point we can make sure that the input and output relation are the same,
       which is required by the lemma *)
    (Rmsg' "assert rel exhale rel capture state abstract" (resolve_tac ctxt @{thms exhale_rel_capture_state_abstract}) ctxt)

  fun assert_rel_init_tac_pure (_: basic_stmt_rel_info) (setup_well_def_tac: Proof.context -> int -> tactic) ctxt =    
    (Rmsg' "assert rel invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel setup assert propagate" (resolve_tac ctxt @{thms exhale_rel_propagate_pre_no_inv_same_exh}) ctxt) THEN'
    (Rmsg' "stmt rel assert propagate progress" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN' (progress_red_bpl_rel_tac ctxt)) ctxt) THEN'
    (Rmsg' "stmt rel exhale track well-def" (resolve_tac ctxt [@{thm red_ast_bpl_rel_weaken_input} OF @{thms state_rel_def_same_to_state_rel}] THEN' assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "stmt rel assert setup well-def state exhale" (setup_well_def_tac ctxt) ctxt)

  fun assert_rel_reset_state_tac_standard (basic_info: basic_stmt_rel_info) ctxt =
    (Rmsg' "assert rel reset state init" (resolve_tac ctxt @{thms rel_general_success_refl_2}) ctxt) THEN'
    (Rmsg' "assert rel reset state no failure" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset state simplify goal" (asm_full_simp_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset tac change eval state init" (resolve_tac ctxt @{thms state_rel_capture_total_state_change_eval_state}) ctxt) THEN'
    (Rmsg' "assert rel reset tac state rel" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset tac mask and heap disjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset tac field translation eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset tac aux pred disjointness" ((#aux_var_disj_tac basic_info) ctxt) ctxt) THEN'
    (Rmsg' "assert rel reset tac well def same" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "assert rel translation records update" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_info) ctxt) ctxt)

  fun assert_rel_reset_state_tac_pure (basic_info: basic_stmt_rel_info) ctxt =
    (Rmsg' "assert pure rel reset state init" (resolve_tac ctxt @{thms rel_propagate_pre_2_only_state_rel}) ctxt) THEN'
      (Rmsg' "assert pure rel reset state weaken input" (resolve_tac ctxt @{thms red_ast_bpl_rel_weaken_input}) ctxt) THEN'
        (Rmsg' "assert pure rel reset state set def to eval" (resolve_tac ctxt @{thms state_rel_set_def_to_eval}) ctxt) THEN'
          (Rmsg' "assert pure rel reset state implication input rel" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "assert pure rel reset state input implies output" (resolve_tac ctxt @{thms red_ast_bpl_rel_input_implies_output}) ctxt) THEN'
          (Rmsg' "assert pure rel reset state input implies output 2" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_info) ctxt) ctxt) THEN'
    (Rmsg' "assert pure rel reset state finish" (resolve_tac ctxt @{thms assert_reset_state_pure}) ctxt) THEN'
      (Rmsg' "assert pure rel reset state finish 2" (blast_tac ctxt) ctxt) THEN'
      (Rmsg' "assert pure rel reset state finish 3" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "assert pure rel reset state finish 3" (assm_full_simp_solved_tac ctxt) ctxt)

                 
  fun atomic_rel_inst_tac ctxt (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) (atomic_hint : atomic_rel_hint)  = 
    (case atomic_hint of 
        AssignHint (exp_wf_rel_info, exp_rel_info, lookup_bpl_target_thm) => 
               red_assign_tac ctxt basic_info exp_wf_rel_info exp_rel_info lookup_bpl_target_thm
     |  FieldAssignHint _ => field_assign_rel_tac ctxt basic_info atomic_hint
     | InhaleHint inh_complete_hint => 
        (Rmsg' "AtomicInh Start" (resolve_tac ctxt [#inhale_stmt_rel_thm inh_complete_hint]) ctxt) THEN'
        (Rmsg' "AtomicInh StateRel" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "AtomicInh Invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (inhale_rel_tac ctxt inhale_info (#inhale_rel_hint inh_complete_hint))
     | ExhaleHint (NormalExhCompleteHint exh_complete_hint) =>
        (Rmsg' "AtomicExh1 Start" (resolve_tac ctxt [(#exhale_stmt_rel_thm exh_complete_hint) OF [(#consistency_wf_thm basic_info)]]) ctxt) THEN'
        (Rmsg' "AtomicExh2 Consistency" (fastforce_tac ctxt []) ctxt) THEN'
        (Rmsg' "AtomicExh3 Invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (normal_exhale_rel_tac ctxt exhale_info exh_complete_hint)
     | ExhaleHint TrivialExhCompleteHint =>
        (Rmsg' "AtomicExh Trivial" (resolve_tac ctxt @{thms exhale_true_stmt_rel_2}) ctxt) THEN'
        (Rmsg' "AtomicExh Trivial State Rel Impies" (simp_then_if_not_solved_blast_tac ctxt) ctxt)
     | AssertHint assert_complete_hint =>
        (Rmsg' "AtomicAssert Start" (resolve_tac ctxt [#assert_stmt_rel_thm assert_complete_hint]) ctxt) THEN'
        (Rmsg' "AtomicAssert Init" ((#init_tac assert_complete_hint) basic_info (#setup_well_def_state_tac assert_complete_hint basic_info) ctxt) ctxt) THEN' 
        (assert_rel_tac ctxt exhale_info assert_complete_hint)
     | MethodCallHint (callee_name, rets_lookup_decl_thms, inhale_info_call, exhale_info_call, exh_pre_complete_hint, inh_post_complete_hint) => 
        let val callee_data = Symtab.lookup (#method_data_table basic_info) callee_name |> Option.valOf in
        (Rmsg' "MethodCall Start" (resolve_tac ctxt [@{thm method_call_stmt_rel_inst} OF [#consistency_wf_thm basic_info, #consistency_down_mono_thm basic_info]]) ctxt) THEN'
        (Rmsg' "MethodCall Program Eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ConsistencyEnabled" (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_info @ [@{thm default_state_rel_options_def}]) ctxt) ctxt) THEN'
        (Rmsg' "MethodCall MdeclSome" (assm_full_simp_solved_with_thms_tac [#method_lookup_thm callee_data] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall MethodSpecsFramed" (EVERY' [eresolve_tac ctxt @{thms vpr_method_spec_correct_total_from_all}, 
                                                  resolve_tac ctxt [#method_lookup_thm callee_data]]) ctxt) THEN'
        (Rmsg' "MethodCall MethodSpecSubset" (assm_full_simp_solved_with_thms_tac [#method_pre_thm callee_data, #method_post_thm callee_data] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall OnlyArgsInPre" (fastforce_tac ctxt [#method_pre_thm callee_data]) ctxt) THEN'
        (Rmsg' "MethodCall Empty Rinterp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall DomainTyRep" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
        (Rmsg' "MethodCall TyInterpBplEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall StateRelConcrete" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ArgsAreVars" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ArgsVarsEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ArgsSubsetVarTranslation" (#var_rel_tac basic_info ctxt) ctxt) THEN'
        (Rmsg' "MethodCall XsBplEq" (#var_rel_tac basic_info ctxt) ctxt) THEN'
        (Rmsg' "MethodCall RetsSubsetVarTranslation" (#var_rel_tac basic_info ctxt) ctxt) THEN' 
        (Rmsg' "MethodCall YsBplEq" (#var_rel_tac basic_info ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ArgsAndRetsDisjoint" (assm_full_simp_solved_with_thms_tac [@{thm shift_and_add_def}] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Distinct Args" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Distinct Rets" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall LookupDeclRetsBpl" (assm_full_simp_solved_with_thms_tac ([#method_rets_thm callee_data, @{thm ty_repr_basic_def}, @{thm shift_and_add_def}]@rets_lookup_decl_thms)  ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Var Translation Pre Eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Exhale Pre" ( simp_only_tac [#method_pre_thm callee_data] ctxt THEN'
                                         atomic_rel_inst_tac ctxt inhale_info_call exhale_info_call basic_info (ExhaleHint exh_pre_complete_hint)) ctxt) THEN'
        (Rmsg' "MethodCall Havoc Rets Eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Var Translation Post Eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Inhale Post" (simp_only_tac [#method_post_thm callee_data] ctxt THEN'
                                        atomic_rel_inst_tac ctxt inhale_info_call exhale_info_call basic_info (InhaleHint inh_post_complete_hint)) ctxt)

       end
    )

\<close>

end