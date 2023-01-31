theory StmtRelML
imports Boogie_Lang.HelperML ExprWfRelML ExpProofGenTest 
begin

(*

method zero_mask_lookup_tac uses tr_def =
       (rule boogie_const_rel_lookup_2[where ?const = CZeroMask],
        rule state_rel_boogie_const,
         blast,
         simp add: tr_def,
         simp)
(* (rule tr_def_field_translation[OF tr_def], fastforce)*)
method red_assume_good_state uses CtxtWf tr_def =
     (rule RedAssumeOk,
      rule assume_state_normal[OF CtxtWf],
      (rule tr_def_field_translation[OF tr_def], fastforce),
      simp add: tr_def,
      simp add: tr_def,
      simp add: tr_def,
      simp add: tr_def)
*)

ML \<open>
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
    resolve_tac ctxt [@{thm assign_rel_simple[where ?Trep=ty_repr_basic]}] THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    (var_context_vpr_tac ctxt |> SOLVED') THEN'
    
    (* well-def RHS *)
    (* begin *)
    resolve_tac ctxt [@{thm wf_rel_extend_1}] THEN'
    exp_wf_rel_non_trivial_tac exp_rel_info ctxt THEN'
    progress_tac ctxt THEN'
    (* end *)
    
    assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN' 
    
    (* prove updated Viper and Boogie states are still in relation *)
    (* begin *)
    resolve_tac ctxt [@{thm state_rel_store_update_2}] THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    (var_rel_tac ctxt |> SOLVED') THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [lookup_bpl_target_thm] ctxt THEN'
    assm_full_simp_solved_with_thms_tac [] ctxt THEN'
    (* end *)
        
    assm_full_simp_solved_with_thms_tac @{thms type_interp_rel_wf_vbpl_no_domains ty_repr_basic_def} ctxt THEN'
    exp_rel_tac exp_rel_info ctxt

  datatype stmt_rel_hint = AssignHint of 
                                     exp_rel_info * (* for relating RHS of assignment *)
                                     thm (* lookup target theorem *)

  type stmt_rel_info = {
      ctxt_wf_thm: thm,
      tr_def_thm: thm,
      var_rel_tac: (Proof.context -> int -> tactic),
      var_context_vpr_tac: (Proof.context -> int -> tactic)
 }
  


  fun stmt_rel_single_stmt_tac ctxt (info: stmt_rel_info) hint_hd =
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
    ) THEN'
    (* now reduce \<open>assume state(Heap, Mask)\<close> *)
    progress_assume_good_state_tac ctxt (#ctxt_wf_thm info) (#tr_def_thm info)        
          

  fun stmt_rel_tac ctxt (info: stmt_rel_info) stmt_rel_hints =
    case stmt_rel_hints of
      [] => K all_tac
    | (hint_hd :: hints_tl) => 
       (* We first need to go to the next Viper statement that is not a sequential composition *)
       REPEAT_DETERM' (resolve_tac ctxt [@{thm stmt_rel_seq_same_rel}]) THEN'
       stmt_rel_single_stmt_tac ctxt info hint_hd THEN'
       stmt_rel_tac ctxt info hints_tl


\<close>

end