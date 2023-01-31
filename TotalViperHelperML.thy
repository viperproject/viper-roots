theory TotalViperHelperML
imports Main
begin

ML \<open>
fun run_and_print_if_fail_tac tac ctxt =
    (tac ctxt) ORELSE (print_tac ctxt "failure" THEN no_tac)

fun run_and_print_if_fail_tac' msg tac ctxt =
    (tac ctxt) ORELSE' (K ((print_tac ctxt msg) THEN no_tac))

fun REPEAT_DETERM' tac x =
   REPEAT_DETERM (tac x)

fun apply_tacs_seq [] = K (all_tac)
 | apply_tacs_seq (tac :: tacs) = tac THEN' (apply_tacs_seq tacs)
\<close>

end