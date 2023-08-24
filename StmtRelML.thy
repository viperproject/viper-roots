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
    |  SeqnHint [_] => error "SeqnHint with single node appears"
    |  SeqnHint (h::hs) => stmt_rel_tac_seq ctxt info (h::hs)
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
             (Rmsg' "If3" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN'           
             (stmt_rel_tac ctxt info thn_hint |> SOLVED') THEN'
             (Rmsg' "If4" (progress_red_bpl_rel_tac ctxt) ctxt)
           ) THEN'
           (
            simplify_continuation ctxt THEN'
            (Rmsg' "If5" (resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}]) ctxt) THEN'           
            (stmt_rel_tac ctxt info els_hint |> SOLVED') THEN'
            (Rmsg' "If6" (progress_red_bpl_rel_tac ctxt) ctxt)
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
     (Rmsg' "Progress Good State" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm (#basic_stmt_rel_info info)) (#tr_def_thm (#basic_stmt_rel_info info))) ORELSE' (progress_red_bpl_rel_tac ctxt)) ctxt)
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
  | MethodCallHint of 
       string * (* callee name *)
       thm list * (* Boogie return variable lookup decl theorem *)
       (atomic_inhale_rel_hint inhale_rel_info) *
       (atomic_exhale_rel_hint exhale_rel_info) *
       (atomic_exhale_rel_hint exhale_rel_complete_hint) * (* exhale pre *)
       (atomic_inhale_rel_hint inhale_rel_complete_hint)   (* inhale post *)

  fun red_assign_tac ctxt (basic_stmt_rel_info : basic_stmt_rel_info) exp_wf_rel_info (exp_rel_info : exp_rel_info) lookup_bpl_target_thm =
    (* TODO     (Rmsg' "Assign1" (resolve_tac ctxt [@{thm assign_rel_simple[where ?Trep=ty_repr_basic]}]) ctxt) THEN' *)
    (Rmsg' "Assign 1" (resolve_tac ctxt [@{thm assign_rel_simple}]) ctxt) THEN'
    (Rmsg' "Assign R_def" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign VprTy" ((#var_context_vpr_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign TyRelWf" (simp_only_tac [#type_interp_econtext basic_stmt_rel_info] ctxt THEN'
                        resolve_tac ctxt @{thms type_interp_rel_wf_vbpl_basic}) ctxt) THEN'
    
    (* well-def RHS *)
    (* begin *)
    (Rmsg' "Assign4" (resolve_tac ctxt [@{thm wf_rel_extend_1_same_rel}]) ctxt) THEN'
    (Rmsg' "Assign Wf RHS" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign5" (progress_tac ctxt) ctxt) THEN'
    (* end *)
    
    (Rmsg' "Assign Ty LHS" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign TyRel" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN' 
    
    (* prove updated Viper and Boogie states are still in relation *)
    (* begin *)
    (Rmsg' "Assign RAssign (state rel store update)" (resolve_tac ctxt [@{thm state_rel_store_update_2}]) ctxt) THEN'
    (Rmsg' "Assign StateRel (state rel store update)" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign WellDefSame  (state rel store update)" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign VarCtxt  (state rel store update)" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign VarTr  (state rel store update)" ( (#var_rel_tac basic_stmt_rel_info) ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign ValRelVprBpl  (state rel store update)" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign TyBpl (state rel store update)" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign TypeOfVal (state rel store update)" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (* end *)
        
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
       (Rmsg' "FieldAssign 1" (resolve_tac ctxt [@{thm field_assign_rel_inst[OF wf_ty_repr_basic]}]) ctxt) THEN'
       (Rmsg' "FieldAssign RStateRel" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapUpdWf" (resolve_tac ctxt [@{thm heap_update_wf_concrete} OF [#ctxt_wf_thm basic_stmt_rel_info, @{thm wf_ty_repr_basic}]])
                                         ctxt) THEN'
       (Rmsg' "FieldAssign DomainType" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign TypeInterp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign Rext" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
       (* TODO: need to use wf_rel_extend *)
       (Rmsg' "FieldAssign7 (Wf Rcv)" (exp_wf_rel_non_trivial_tac rcv_wf_rel_info rcv_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign8 (Wf Rhs)" (exp_wf_rel_non_trivial_tac rhs_wf_rel_info rhs_exp_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign9 (Wf Writeable Field)" (wf_writeable_field_rel_tac rcv_exp_rel_info basic_stmt_rel_info ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
       (Rmsg' "FieldAssign HeapUpdateBpl" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info, @{thm update_heap_concrete_def}, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
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
    assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info] ctxt
                                                                                   
  fun exhale_finish_tac ctxt (basic_info: basic_stmt_rel_info) (hint: 'a exhale_rel_complete_hint) =
    let val tr_thm = #tr_def_thm basic_info in
      (Rmsg' "exhale finish 1" (resolve_tac ctxt @{thms exhale_stmt_rel_finish}) ctxt) THEN'
      (Rmsg' "exhale finish StateRel"  (assm_full_simp_solved_with_thms_tac [tr_thm] ctxt) ctxt) THEN'
      (Rmsg' "exhale finish CtxtWf"  (resolve_tac ctxt [#ctxt_wf_thm basic_info]) ctxt) THEN'
      (Rmsg' "exhale finish WfTyRepr"  (resolve_tac ctxt @{thms wf_ty_repr_basic}) ctxt) THEN'
      (Rmsg' "exhale finish ProgramTotal" (resolve_tac ctxt [@{thm HOL.sym} OF [#vpr_program_ctxt_eq_thm basic_info]]) ctxt) THEN'
      (Rmsg' "exhale finish DomainType" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
      (Rmsg' "exhale finish WellDefSame" (assm_full_simp_solved_with_thms_tac [tr_thm] ctxt) ctxt) THEN'
      (Rmsg' "exhale finish IdOnKnownLocsName" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale finish TypeInterp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale finish StateCons" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale finish ElemExhaleState" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
      (Rmsg' "exhale finish HeapVar" (assm_full_simp_solved_with_thms_tac [tr_thm] ctxt) ctxt) THEN'
      (Rmsg' "exhale finish MaskVar" (assm_full_simp_solved_with_thms_tac [tr_thm] ctxt) ctxt) THEN'
      (Rmsg' "exhale finish LookupDeclExhaleHeap" (assm_full_simp_solved_with_thms_tac [@{thm ty_repr_basic_def},  #lookup_decl_exhale_heap hint] ctxt) ctxt) THEN'
      (Rmsg' "exhale finish ExhaleHeapFresh" (#aux_var_disj_tac basic_info ctxt) ctxt)

    end

  fun exhale_rel_tac ctxt (info: 'a exhale_rel_info) (hint: 'a exhale_rel_complete_hint) =
    (Rmsg' "stmt rel exhale progress" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN' (progress_red_bpl_rel_tac ctxt)) ctxt) THEN'
    (Rmsg' "setup well-def state exhale" ((#setup_well_def_state_tac hint) (#basic_info info) ctxt) ctxt) THEN'
    exhale_rel_aux_tac ctxt info (#exhale_rel_hint hint) THEN'
    (* apply transitive rule such to make sure that the active big block before exhale_finish_tac is unfolded *)
    (Rmsg' "stmt rel exhale red ast bpl transitive" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive_3}) ctxt) THEN'
      (Rmsg' "exhale revert state relation" (exhale_revert_state_relation ctxt (#basic_info info)) ctxt) THEN'
      (Rmsg' "stmt rel exhale progress" (progress_red_bpl_rel_tac ctxt) ctxt) THEN'
    exhale_finish_tac ctxt (#basic_info info) hint
                 
  fun atomic_rel_inst_tac ctxt (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) (atomic_hint : atomic_rel_hint)  = 
    (case atomic_hint of 
        AssignHint (exp_wf_rel_info, exp_rel_info, lookup_bpl_target_thm) => 
               red_assign_tac ctxt basic_info exp_wf_rel_info exp_rel_info lookup_bpl_target_thm
     |  FieldAssignHint _ => field_assign_rel_tac ctxt basic_info atomic_hint
     | InhaleHint inh_complete_hint => 
        (Rmsg' "AtomincInh Start" (resolve_tac ctxt [#inhale_stmt_rel_thm inh_complete_hint]) ctxt) THEN'
        (Rmsg' "AtomincInh StateRel" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "AtomincInh Invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (inhale_rel_tac ctxt inhale_info (#inhale_rel_hint inh_complete_hint))
     | ExhaleHint exh_complete_hint =>
        (Rmsg' "AtomicExh1 Start" (resolve_tac ctxt [(#exhale_stmt_rel_thm exh_complete_hint) OF [(#consistency_wf_thm basic_info)]]) ctxt) THEN'
        (Rmsg' "AtomicExh2 Consistency" (fastforce_tac ctxt []) ctxt) THEN'
        (Rmsg' "AtomicExh3 Invariant" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (exhale_rel_tac ctxt exhale_info exh_complete_hint)
     | MethodCallHint (callee_name, rets_lookup_decl_thms, inhale_info_call, exhale_info_call, exh_pre_complete_hint, inh_post_complete_hint) => 
        let val callee_data = Symtab.lookup (#method_data_table basic_info) callee_name |> Option.valOf in
        (Rmsg' "MethodCall Start" (resolve_tac ctxt [@{thm method_call_stmt_rel} OF [#consistency_wf_thm basic_info, #consistency_down_mono_thm basic_info]]) ctxt) THEN'
        (Rmsg' "MethodCall Program Eq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall ConsistencyEnabled" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall MdeclSome" (assm_full_simp_solved_with_thms_tac [#method_lookup_thm callee_data] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall MethodSpecsFramed" (EVERY' [eresolve_tac ctxt @{thms vpr_method_spec_correct_total_from_all}, 
                                                  resolve_tac ctxt [#method_lookup_thm callee_data]]) ctxt) THEN'
        (Rmsg' "MethodCall MethodSpecSubset" (assm_full_simp_solved_with_thms_tac [#method_pre_thm callee_data, #method_post_thm callee_data] ctxt) ctxt) THEN'
        (Rmsg' "MethodCall OnlyArgsInPre" (assm_full_simp_solved_with_thms_tac [#method_pre_thm callee_data] ctxt) ctxt) THEN'
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
        (Rmsg' "MethodCall ArgsAndRetsDisjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Distinct Args" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall Distinct Rets" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
        (Rmsg' "MethodCall LookupDeclRetsBpl" (assm_full_simp_solved_with_thms_tac ([#method_rets_thm callee_data, @{thm ty_repr_basic_def}]@rets_lookup_decl_thms)  ctxt) ctxt) THEN'
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