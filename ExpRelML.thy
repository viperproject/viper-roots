theory ExpRelML
imports ExpRel Boogie_Lang.TypingML Boogie_Lang.HelperML
begin

subsection \<open>Auxiliary lemmas for the tactics\<close>

lemmas state_rel_var_rel = store_rel_var_rel_2[OF state_rel0_store_rel[OF state_rel_state_rel0]]
lemmas state_rel_lit_rel = boogie_const_lit_rel[OF state_rel0_boogie_const[OF state_rel_state_rel0]]
lemmas state_rel_state_well_typed = state_rel0_state_well_typed[OF state_rel_state_rel0]

subsection \<open>ML tactics\<close>

ML \<open>

datatype boogie_prim_type = TBool | TInt | TReal

(* provide type safety theorem for each primitive type *)
type type_safety_thm_map = boogie_prim_type -> thm

(* type_safety_thm lookup_var_rel_tac vpr_lit_bpl_exp_rel_tac lookup_var_thms *)
datatype exp_rel_info = ExpRelInfo0 of type_safety_thm_map * 
                                     (Proof.context -> int -> tactic) * 
                                     (Proof.context -> int -> tactic) *
                                     thm list ; 

fun sel_type_safety_thm_map (info : exp_rel_info) : type_safety_thm_map =
  case info of ExpRelInfo0 (res, _, _ ,_) => res

fun sel_lookup_var_rel_tac (info : exp_rel_info) : (Proof.context -> int -> tactic) =
  case info of ExpRelInfo0 (_, res, _ ,_) => res

fun sel_vpr_lit_bpl_exp_rel_tac (info : exp_rel_info) : (Proof.context -> int -> tactic) =
  case info of ExpRelInfo0 (_, _, res ,_) => res

fun sel_lookup_var_thms (info : exp_rel_info) : thm list =
  case info of ExpRelInfo0 (_, _, _ ,res) => res

fun var_rel_tac lookup_var_rel_tac ctxt =
  resolve_tac ctxt [@{thm exp_rel_var}] THEN'
  resolve_tac ctxt [@{thm state_rel_var_rel}] THEN'
  fastforce_tac ctxt [] THEN' (* blast may be faster here *)
  lookup_var_rel_tac ctxt

fun lit_tac vpr_lit_bpl_exp_rel_tac ctxt = 
  resolve_tac ctxt [@{thm exp_rel_lit}] THEN'
  resolve_tac ctxt [@{thm state_rel_lit_rel}] THEN'
  fastforce_tac ctxt [] THEN' (* blast may be faster here *)
  vpr_lit_bpl_exp_rel_tac ctxt

fun expr_red_tac type_safety_thm lookup_var_thms ctxt = 
  resolve_tac ctxt [type_safety_thm] THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  typing_tac ctxt NoPolyHint lookup_var_thms []

(* TODO:
   write method recursively to get more information when expression relation should finish solving the goal
   and to avoid solving more goals than just the provided one
 *)

(*
fun exp_rel_rec_tac type_safety_thm_map lookup_var_rel_tac vpr_lit_bpl_exp_rel_tac lookup_var_thms ctxt =
  FIRST' [
    var_rel_tac lookup_var_rel_tac ctxt |> SOLVED',
    lit_tac vpr_lit_bpl_exp_rel_tac ctxt |> SOLVED',
    (fn i => fn st => binop_eager_rel_tac ctxt i st) |> SOLVED',
    (fn i => fn st => binop_lazy_rel_tac (type_safety_thm_map TBool) lookup_var_thms ctxt i st)
  ] 
*)

fun binop_eager_rel_tac info ctxt = 
  resolve_tac ctxt [@{thm exp_rel_binop_eager}] THEN'
  assm_full_simp_solved_tac ctxt THEN' (* bop *)
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') THEN' (* e1 *)
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') (* e2 *)
and
  binop_lazy_rel_tac info ctxt = 
  resolve_tac ctxt [@{thm exp_rel_binop_lazy}] THEN'
  assm_full_simp_solved_tac ctxt THEN' (* bop *) 
  (fn i => fn st => 
     (* e2 reduces to a Boolean *)
     expr_red_tac (sel_type_safety_thm_map info TBool) (sel_lookup_var_thms info) ctxt i st) THEN' 
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') THEN' (* e1 *) 
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') (* e2 *)
and 
  (* the reason for abstraction over the state st in multiple places is to avoid infinite recursion due
     to eager evaluation of arguments in a function call *)
   exp_rel_tac info ctxt =
      FIRST' [
        var_rel_tac (sel_lookup_var_rel_tac info) ctxt |> SOLVED',
        lit_tac (sel_vpr_lit_bpl_exp_rel_tac info) ctxt |> SOLVED',
        (fn i => fn st => binop_eager_rel_tac info ctxt i st) |> SOLVED',
        (fn i => fn st => binop_lazy_rel_tac info ctxt i st) |> SOLVED'
      ]
\<close>

end