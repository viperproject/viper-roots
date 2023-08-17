theory TotalViperHelperML
imports Boogie_Lang.HelperML
begin

ML \<open>

fun print_and_fail_tac msg ctxt = ((print_tac ctxt msg) THEN no_tac)

fun run_and_print_if_fail_tac' msg tac ctxt =
    (tac ctxt) ORELSE' (K (print_and_fail_tac msg ctxt))

fun run_and_print_if_fail_2_tac' msg tac ctxt =
    tac ORELSE' (K (print_and_fail_tac msg ctxt))

fun print_then_run_tac msg ctxt = K (print_tac ctxt msg)

fun REPEAT_DETERM' tac x =
   REPEAT_DETERM (tac x)

fun apply_tacs_seq [] = K (all_tac)
 | apply_tacs_seq (tac :: tacs) = tac THEN' (apply_tacs_seq tacs)

(* This basically applies the cut rule \<lbrakk>P; P \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q. It has the same effect as
   cut_tac, except that one must first prove P (while in cut_tac one must first prove P \<Longrightarrow> Q) *)
fun revcut_tac rule i = resolve0_tac [revcut_rl] i THEN resolve0_tac [rule] i

fun force_tac_with_simps ctxt thms = Clasimp.force_tac (add_simps thms ctxt)

fun TRY_TAC' tac = tac ORELSE' (K all_tac)

\<close>

end