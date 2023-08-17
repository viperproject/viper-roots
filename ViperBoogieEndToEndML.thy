theory ViperBoogieEndToEndML
imports ViperBoogieEndToEnd CPGHelperML ViperBoogieHelperML
begin

ML \<open>

  fun post_framing_rel_init_tac ctxt (basic_info : basic_stmt_rel_info) lookup_heap_var_thm lookup_mask_var_thm =
    (Rmsg' "Post Framing Init - Start" (resolve_tac ctxt [ @{thm post_framing_rel_aux} OF [@{thm wf_ty_repr_basic}, #consistency_wf_thm basic_info]]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Type Interp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Domain Type" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Program" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Heap" 
            (simp_tac_with_thms @{thms ty_repr_basic_def} ctxt THEN'
            resolve_tac ctxt [lookup_heap_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Mask" 
            (simp_tac_with_thms @{thms ty_repr_basic_def} ctxt THEN'
             resolve_tac ctxt [lookup_mask_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Zero Mask" 
            (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info] ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Disjointntess" ((#aux_var_disj_tac basic_info) ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Heap and Mask Disjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 1"
         (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN'
         resolve_tac ctxt @{thms red_ast_bpl_rel_if_nondet_then} THEN'
         (* One_nat_def is applied as a hack to match 1 and Suc 0.
           It would be good to solve this problem more generally such that there cannot be such
           mismatches at this point *)
         progress_rel_tac_2 (fn ctxt => simp_only_tac @{thms One_nat_def} ctxt) ctxt THEN'
         simplify_continuation ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 2" (resolve_tac ctxt @{thms stmt_rel_propagate_same_rel}) ctxt) THEN'
    (Rmsg' "Post Framing Init - Assume Good State" (progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info)) ctxt)

\<close>

end