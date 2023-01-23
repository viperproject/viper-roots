theory TotalViperHelperML
imports Main
begin

ML \<open>
fun run_and_print_if_fail_tac tac ctxt =
    (tac ctxt) ORELSE (print_tac ctxt "failure" THEN no_tac)

fun run_and_print_if_fail_tac' msg tac ctxt =
    (tac ctxt) ORELSE' (K ((print_tac ctxt msg) THEN no_tac))
\<close>

end