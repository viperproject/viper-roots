theory TotalViperHelperML
imports Boogie_Lang.HelperML
begin

ML \<open>

fun print_and_fail_tac msg ctxt = ((print_tac ctxt msg) THEN no_tac)

fun run_and_print_if_fail_tac' msg tac ctxt =
    (tac ctxt) ORELSE' (K (print_and_fail_tac msg ctxt))

fun run_and_print_if_fail_2_tac' msg tac ctxt =
   (* tac ORELSE' (K (print_and_fail_tac msg ctxt)): this version is slower, because it prints all subgoals
      and it does not terminate the execution (as opposed to the current solution that raises an exception) *)
   tac ORELSE' (SUBGOAL (fn (t,_) => raise TERM (msg,[t])))

fun print_then_run_tac msg ctxt = K (print_tac ctxt msg)

fun REPEAT_DETERM' tac x =
   REPEAT_DETERM (tac x)

fun apply_tacs_seq [] = K (all_tac)
 | apply_tacs_seq (tac :: tacs) = tac THEN' (apply_tacs_seq tacs)

fun del_simps [] ctxt = ctxt
 |  del_simps (thm::thms) ctxt = del_simps thms (Simplifier.del_simp thm ctxt)

(* This basically applies the cut rule \<lbrakk>P; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q. It has the same effect as
   cut_tac, except that one must first prove P (while in cut_tac one must first prove P \<Longrightarrow> Q) *)
fun revcut_tac rule i = resolve0_tac [revcut_rl] i THEN resolve0_tac [rule] i

fun force_tac_with_simps ctxt thms = Clasimp.force_tac (add_simps thms ctxt)

fun fast_force_tac_with_elims_simps ctxt elim_thms simp_thms = 
           Clasimp.fast_force_tac (add_simps simp_thms (ctxt addEs elim_thms) )

fun TRY_TAC' tac = tac ORELSE' (K all_tac)

type method_data =
     { method_arg_thm : thm,
       method_rets_thm : thm,
       method_pre_thm : thm,
       method_post_thm : thm,
       method_lookup_thm : thm }

\<close>

end