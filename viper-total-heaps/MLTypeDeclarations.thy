theory MLTypeDeclarations

(* This is a file for containing all ML types declared for the proof generation *)

imports Main

begin

ML \<open>

type method_data =
     { method_arg_thm : thm,
       method_rets_thm : thm,
       method_pre_thm : thm,
       method_post_thm : thm,
       method_lookup_thm : thm }

(* general information for tactics *)

  (* TODO rename *)
  type basic_stmt_rel_info = {
      ctxt_wf_thm: thm,
      consistency_wf_thm: thm,
      consistency_down_mono_thm: thm,
      tr_def_thms: thm list,
      method_data_table: method_data Symtab.table,
      vpr_program_ctxt_eq_thm: thm,
      var_rel_tac: (Proof.context -> int -> tactic),
      var_context_vpr_tac: (Proof.context -> int -> tactic),
      field_rel_single_tac : (Proof.context -> int -> tactic),
      aux_var_disj_tac: (Proof.context -> int -> tactic),
      type_interp_econtext: thm  
  }

(* ExpRel *)

datatype type_safety_key = TBool | TInt | TReal | TSameType

(* provide type safety theorems *)
type type_safety_thm_map = type_safety_key -> thm

type exp_rel_info = {
    basic_stmt_rel_info: basic_stmt_rel_info,
    type_safety_thm_map : type_safety_thm_map,
    lookup_var_rel_tac : Proof.context -> int -> tactic,
    vpr_lit_bpl_exp_rel_tac : Proof.context -> int -> tactic,
    lookup_var_thms : thm list,
    lookup_fun_bpl_thms: thm list,
    (* tactic to simplify the context projection on the runtype interpretation *)
    simplify_rtype_interp_tac: Proof.context -> int -> tactic,
    (* should be tactic that given goal to relate Viper field access reduces the goal to a single
       goal where the receiver expression must be related *)       
    field_access_rel_pre_tac : Proof.context -> int -> tactic
}

(* ExpWfRel *)
  type exp_wf_rel_info = {
    basic_stmt_rel_info: basic_stmt_rel_info,
    (* tactic that solves wf_rel_fieldacc *)       
    field_access_wf_rel_syn_tac : Proof.context -> int -> tactic 
  }

\<close>


end