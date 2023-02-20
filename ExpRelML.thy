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

fun gen_type_safety_thm_map fun_interp_wf fun_decls_wf var_context_wf state_wf =
   let val type_safety_bpl_aux_bool = 
            @{thm type_safety_top_level_inv} OF [fun_interp_wf, fun_decls_wf, var_context_wf, state_wf]
       val type_safety_bpl_aux_int = 
            @{thm type_safety_top_level_inv_int} OF [fun_interp_wf, fun_decls_wf, var_context_wf, state_wf] 
       val type_safety_bpl_aux_real =
            @{thm type_safety_top_level_inv_real} OF [fun_interp_wf, fun_decls_wf, var_context_wf, state_wf] 
    in
    (fn primTy => 
       case primTy of
          TBool => type_safety_bpl_aux_bool
        | TInt => type_safety_bpl_aux_int
        | TReal => type_safety_bpl_aux_real
    )
   end

type exp_rel_info = {
    type_safety_thm_map : type_safety_thm_map,
    lookup_var_rel_tac : Proof.context -> int -> tactic,
    vpr_lit_bpl_exp_rel_tac : Proof.context -> int -> tactic,
    lookup_var_thms : thm list,
    (* should be tactic that given goal to relate Viper field access reduces the goal to a single
       goal where the receiver expression must be related *)       
    field_access_rel_pre_tac : Proof.context -> int -> tactic 
}

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

fun binop_eager_rel_tac info ctxt = 
  resolve_tac ctxt [@{thm exp_rel_binop_eager}] THEN'
  assm_full_simp_solved_tac ctxt THEN' (* bop *)
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') THEN' (* e1 *)
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') (* e2 *)
and
  binop_lazy_rel_tac (info : exp_rel_info) ctxt = 
  resolve_tac ctxt [@{thm exp_rel_binop_lazy}] THEN'
  assm_full_simp_solved_tac ctxt THEN' (* bop *) 
  (fn i => fn st => 
     (* e2 reduces to a Boolean *)
     expr_red_tac (#type_safety_thm_map info TBool) (#lookup_var_thms info) ctxt i st) THEN' 
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') THEN' (* e1 *) 
  ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED') (* e2 *)
and
  field_access_rel_tac (info : exp_rel_info) ctxt = 
    (#field_access_rel_pre_tac info ctxt) THEN'
    ((fn i => fn st => exp_rel_tac info ctxt i st) |> SOLVED')

and 
  (* the reason for abstraction over the state st in multiple places is to avoid infinite recursion due
     to eager evaluation of arguments in a function call *)
   exp_rel_tac (info : exp_rel_info) ctxt =
      FIRST' [
        var_rel_tac (#lookup_var_rel_tac info) ctxt |> SOLVED',
        lit_tac (#vpr_lit_bpl_exp_rel_tac info) ctxt |> SOLVED',
        (fn i => fn st => binop_eager_rel_tac info ctxt i st) |> SOLVED',
        (fn i => fn st => binop_lazy_rel_tac info ctxt i st) |> SOLVED',
        (fn i => fn st => field_access_rel_tac info ctxt i st) |> SOLVED'
      ]
\<close>

ML
 \<open> fun field_access_rel_pre_tac_aux heap_read_wf_tac head_read_match_tac field_rel_tac field_lookup_tac ctxt =
    resolve_tac ctxt [@{thm exp_rel_field_access} OF [@{thm state_rel_state_rel0}]] THEN'
    blast_tac ctxt THEN'
    heap_read_wf_tac ctxt THEN'
    head_read_match_tac ctxt THEN'
    field_rel_tac ctxt THEN'
    assm_full_simp_solved_tac ctxt THEN'
    field_lookup_tac ctxt THEN'
    assm_full_simp_solved_tac ctxt
\<close>

end