theory StmtRelML
imports Boogie_Lang.HelperML ExprWfRelML ExpProofGenTest 
begin

ML \<open>
  val Rmsg' = run_and_print_if_fail_2_tac' 

  fun zero_mask_lookup_tac ctxt tr_def_thm =
    resolve_tac ctxt [@{thm boogie_const_rel_lookup_2[where ?const = CZeroMask]}] THEN'
    resolve_tac ctxt [@{thm state_rel_boogie_const}] THEN'
    blast_tac ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_tac ctxt

(*
  apply (rule exI)
   apply (rule red_ast_bpl_propagate_rel)
     apply (rule red_ast_bpl_one_simple_cmd)

   \<comment>\<open>show \<open>assume state(Heap,Mask)\<close> reduces normally\<close>
     apply (tactic \<open>red_assume_good_state_tac @{context} @{thm CtxtWf} @{thm tr_vpr_bpl_1_def} 1\<close>)
    apply simp
   apply (rule conjI)
    apply (simp, rule red_ast_bpl_refl)
   apply assumption
*)

  fun red_assume_good_state_tac ctxt ctxt_wf_thm tr_def_thm = 
    resolve_tac ctxt [@{thm RedAssumeOk}] THEN'
    resolve_tac ctxt [@{thm assume_state_normal} OF [ctxt_wf_thm]] THEN'
    resolve_tac ctxt [@{thm tr_def_field_translation} OF [tr_def_thm]] THEN'
    fastforce_tac ctxt [] THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt
  
  fun progress_assume_good_state_tac ctxt ctxt_wf_thm tr_def_thm =
    resolve_tac ctxt [@{thm exI}] THEN'
    resolve_tac ctxt [@{thm red_ast_bpl_propagate_same_rel}] THEN'
    resolve_tac ctxt [@{thm red_ast_bpl_one_simple_cmd}] THEN'
    red_assume_good_state_tac ctxt ctxt_wf_thm tr_def_thm THEN'
    assume_tac ctxt THEN'
    resolve_tac ctxt [@{thm conjI}] THEN'
    resolve_tac ctxt [@{thm red_ast_bpl_refl}] THEN'
    assume_tac ctxt

  fun red_assign_tac ctxt exp_rel_info var_context_vpr_tac var_rel_tac lookup_bpl_target_thm =
    (Rmsg' "Assign1" (resolve_tac ctxt [@{thm assign_rel_simple[where ?Trep=ty_repr_basic]}]) ctxt) THEN'
    (Rmsg' "Assign2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign3" (var_context_vpr_tac ctxt |> SOLVED') ctxt) THEN'
    
    (* well-def RHS *)
    (* begin *)
    (Rmsg' "Assign4" (resolve_tac ctxt [@{thm wf_rel_extend_1}]) ctxt) THEN'
    (Rmsg' "Assign Wf RHS" (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') ctxt) THEN'
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
    (Rmsg' "Assign12" (var_rel_tac ctxt |> SOLVED') ctxt) THEN'
    (Rmsg' "Assign13" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (Rmsg' "Assign14" (assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt) ctxt) THEN'
    (Rmsg' "Assign15" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
    (* end *)
        
    (Rmsg' "Assign16" (assm_full_simp_solved_with_thms_tac @{thms type_interp_rel_wf_vbpl_no_domains ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "Assign17" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)

  datatype stmt_rel_hint = 
    AssignHint of 
       exp_rel_info * (* for relating RHS of assignment *)
       thm (* lookup target theorem *) 
  | SeqnHint of stmt_rel_hint list
  | IfHint of 
       stmt_rel_hint * (* thn branch *)
       stmt_rel_hint
              

  type stmt_rel_info = {
      ctxt_wf_thm: thm,
      tr_def_thm: thm,
      var_rel_tac: (Proof.context -> int -> tactic),
      var_context_vpr_tac: (Proof.context -> int -> tactic)
 }
  


 fun stmt_rel_tac ctxt (info: stmt_rel_info) stmt_rel_hint =
    case stmt_rel_hint of 
       SeqnHint [] => resolve_tac ctxt [@{thm stmt_rel_skip}]
    |  SeqnHint (h::hs) => stmt_rel_tac_seq ctxt info (h::hs)
    | _ => stmt_rel_single_stmt_tac ctxt info stmt_rel_hint
and
     stmt_rel_tac_seq _ _ [] = K all_tac
   | stmt_rel_tac_seq ctxt (info: stmt_rel_info) (h :: hs) = 
        resolve_tac ctxt [@{thm stmt_rel_seq_same_rel}] THEN'
        stmt_rel_tac ctxt info h THEN'
        stmt_rel_tac_seq ctxt info hs
and 
   stmt_rel_single_stmt_tac ctxt (info: stmt_rel_info) hint_hd =
    (* Each statement associated with a hint is translated by the actual encoding followed by 
       \<open>assume state(Heap, Mask)\<close>. This is why we apply a propagation rule first. *)
    resolve_tac ctxt [@{thm stmt_rel_propagate_2_same_rel}] THEN'
    (
      case hint_hd of
        AssignHint (exp_rel_info, lookup_bpl_target_thm) => 
               red_assign_tac ctxt exp_rel_info 
                        (#var_context_vpr_tac info) 
                        (#var_rel_tac info) 
                        lookup_bpl_target_thm
      | IfHint (_, _) =>
           (* TODO: apply stmt_rel_if *)
           K no_tac
      | _ => error "unsupported hint in stmt_rel_single_stmt_tac"
    ) THEN'
    (* now reduce \<open>assume state(Heap, Mask)\<close> *)
    progress_assume_good_state_tac ctxt (#ctxt_wf_thm info) (#tr_def_thm info)  
    

(*
    case stmt_rel_hints of
      [] => K all_tac
    | (hint_hd :: hints_tl) => 
       (* We first need to go to the next Viper statement that is not a sequential composition *)
       REPEAT_DETERM' (resolve_tac ctxt [@{thm stmt_rel_seq_same_rel}]) THEN'
       stmt_rel_single_stmt_tac ctxt info hint_hd THEN'
       stmt_rel_tac ctxt info hints_tl
*)

\<close>

end