theory ViperBoogieHelperML
imports ViperBoogieFunctionInst TotalViperHelperML Boogie_Lang.HelperML
begin

ML \<open>

  fun red_assume_good_state_tac ctxt ctxt_wf_thm tr_def_thm = 
    resolve_tac ctxt [@{thm RedAssumeOk}] THEN'
    resolve_tac ctxt [@{thm assume_state_normal} OF [ctxt_wf_thm]] THEN'
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

  fun progress_assume_good_state_rel_tac ctxt ctxt_wf_thm tr_def_thm =
    resolve_tac ctxt [@{thm red_ast_bpl_rel_one_simple_cmd}] THEN'
    resolve_tac ctxt [@{thm exI}] THEN'
    resolve_tac ctxt [@{thm conjI}] THEN'
    red_assume_good_state_tac ctxt ctxt_wf_thm tr_def_thm THEN'
    assume_tac ctxt

\<close>

end