theory CPGHelperML
  imports ViperBoogieRelUtil TotalViperHelperML ExpRelML  "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac' 

fun simplify_continuation ctxt = simp_only_tac @{thms convert_list_to_cont.simps} ctxt

fun unfold_bigblock_atomic ctxt bigblock =
  case bigblock of
    Const (bigblock_name, _) =>
    ( let val thm = Proof_Context.get_thms ctxt (bigblock_name ^ "_def")
      in
         Local_Defs.unfold_tac ctxt thm
      end )
  | _ => all_tac

fun is_empty_bigblock bigblock =
  case bigblock of 
   Const (@{const_name BigBlock}, _) 
   $ _ (* name *)
   $ Const (@{const_name Nil}, _)
   $ Const (@{const_name None}, _)
   $ Const (@{const_name None}, _)
    => true
  | _ => false

fun unfold_bigblock_in_program_point ctxt (program_point, _) =
    case program_point of 
     Const (@{const_name Product_Type.Pair}, _) $ bigblock $ cont =>
        if is_empty_bigblock bigblock then
           (case cont of (* if the current big block is empty, we unfold the next big block *)
              Const (@{const_name KSeq}, _) $ bigblock_in_cont $ _ => 
                unfold_bigblock_atomic ctxt bigblock_in_cont
            | _ => all_tac)
        else
          unfold_bigblock_atomic ctxt bigblock        
     | _ => all_tac   

(* input term t should not have any metaimplications or metaquantifications *)
fun unfold_bigblock_in_goal_aux ctxt (t,i) =
  case t of 
    @{term "Trueprop"} $ t' => unfold_bigblock_in_goal_aux ctxt (t',i)
     (* just recurse in the first conjunct *)
  | @{term "(\<and>)"} $ conj1 $ _ => (unfold_bigblock_in_goal_aux ctxt (conj1, i))
  | Const (@{const_name "red_ast_bpl"}, _) 
         $ _ (* AST *)
         $ _ (* econtext_bpl *)
         $ (Const (@{const_name Product_Type.Pair}, _) $ program_point $ _)
         $ _ (* end config *) =>
            unfold_bigblock_in_program_point ctxt (program_point, i)
  | Const (@{const_name "red_ast_bpl_rel"}, _) 
         $ _ (* input relation *)
         $ _ (* output relation *)
         $ _ (* AST *)
         $ _ (* econtext_bpl *)
         $ program_point
         $ _ (* end config *) =>
            unfold_bigblock_in_program_point ctxt (program_point, i)
  | Const (@{const_name "is_empty_bigblock"}, _) $ bigblock =>
      unfold_bigblock_atomic ctxt bigblock
  | _ => (writeln(Syntax.string_of_term ctxt t); all_tac)
  

(* The following tactic unfolds in certain contexts the currently active bigblock or the next 
bigblock if the currently active bigblock is empty.?aux_var
The goal is to make sure that after this tactic the (bigblock, continuation) configuration is in 
a form where bigblock is unfolded and not empty. The nonemptiness guarantee relies on the assumption
 that an empty bigblock is not succeeded by another empty bigblock. *)
fun unfold_bigblock_in_goal ctxt =
  SUBGOAL (fn (t,i) => unfold_bigblock_in_goal_aux ctxt (Logic.strip_assums_concl t, i))

  (* progress_tac tries to solve a goal of the form 
         \<open>\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'\<close>
     The tactic tries to solve the goal by instantiating \<gamma>1 to be the unfolded bigblock version of \<gamma>0. 
     
     In cases where \<gamma>0 is an already unfolded (resp. folded) empty bigblock, \<gamma>1 is instantiated to be the 
     unfolded (resp. folded) block version of \<gamma>0's successor. *)
fun progress_tac ctxt = 
   resolve_tac ctxt [@{thm exI}] THEN'
   resolve_tac ctxt [@{thm conjI}] THEN'
   (unfold_bigblock_in_goal ctxt) THEN'
   (resolve_tac ctxt [@{thm red_ast_bpl_empty_block}] ORELSE'
    resolve_tac ctxt [@{thm red_ast_bpl_refl}]) THEN'
   assm_full_simp_solved_tac ctxt

(* unfolds the active big block (as described above) for a rel_general goal *)
fun unfold_bigblock_in_rel_general ctxt =
  (resolve_tac ctxt @{thms rel_propagate_pre_2} THEN' progress_tac ctxt)

(* general information for tactics *)
  (* TODO rename *)
  type basic_stmt_rel_info = {
      ctxt_wf_thm: thm,
      consistency_wf_thm: thm,
      tr_def_thm: thm,
      vpr_program_ctxt_eq_thm: thm,
      var_rel_tac: (Proof.context -> int -> tactic),
      var_context_vpr_tac: (Proof.context -> int -> tactic),
      field_rel_single_tac : (Proof.context -> int -> tactic),
      aux_var_disj_tac: (Proof.context -> int -> tactic),
      type_interp_econtext: thm  
  }


(* Tactic for proving that a Boogie expression reduces, i.e., goals of the form
   "red_expr_bpl ctxt e ns v" (where v is either a fixed value or contains schematic variables).
   The tactic only deals in a custom way with certain operators in the expression. For other
   operators assume_tac is invoked. For example, lookup facts about variables should
   already be in the context or in the goal.
 *)
fun prove_red_expr_bpl_tac ctxt =
  FIRST_AND_THEN' 
    [
   (* We first check whether we can solve the goal directly via an assumption. If we do
      not do this first, then certain assumptions might not apply later and as a result the tactic
      could fail *)
      assume_tac ctxt, 
      resolve_tac ctxt [@{thm Semantics.RedVar}],
      resolve_tac ctxt [@{thm Semantics.RedLit}],
      resolve_tac ctxt [@{thm Semantics.RedBinOp}],
      resolve_tac ctxt [@{thm Semantics.RedUnOp}]
    ]

    [
      fn _ => fn st => all_tac st,
      fn i => fn st => assm_full_simp_solved_tac ctxt i st,
      fn _ => fn st => all_tac st,
      fn i => fn st =>
        (i,st) |->
        (
          (prove_red_expr_bpl_tac ctxt |> SOLVED') (* e1 *) THEN' 
          (prove_red_expr_bpl_tac ctxt |> SOLVED') (* e2 *) THEN'
          (force_tac_with_simps ctxt [] |> SOLVED')           (* binop_eval *)
        ),
     fn i => fn st =>
       (i,st) |->
       (
          (prove_red_expr_bpl_tac ctxt |> SOLVED') (* e *) THEN' 
          (force_tac_with_simps ctxt [] |> SOLVED')           (* unop_eval *)
       )
    ]

fun upd_def_var_tac_aux (basic_stmt_rel_info : basic_stmt_rel_info) lookup_ty_new_var_thm errorMsgPrefix ctxt =
  (Rmsg' (errorMsgPrefix^"DefVar2") (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar3") (assm_full_simp_solved_with_thms_tac [lookup_ty_new_var_thm, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar4") (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_stmt_rel_info] ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar5") (assm_full_simp_solved_tac ctxt) ctxt) THEN' 
  (Rmsg' (errorMsgPrefix^"DefVarAuxVarDisj") ((#aux_var_disj_tac basic_stmt_rel_info) ctxt) ctxt)

fun upd_mask_def_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt =
  (Rmsg' "UpdHeapDefVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "UpdMaskDefVar2" (resolve_tac ctxt @{thms mask_def_var_upd_red_ast_bpl_propagate}) ctxt) THEN'
  (upd_def_var_tac_aux basic_stmt_rel_info lookup_ty_new_var_thm "UpdMask" ctxt)

fun upd_heap_def_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt  =
  (Rmsg' "UpdHeapDefVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "UpdHeapDefVar2" (resolve_tac ctxt @{thms heap_def_var_upd_red_ast_bpl_propagate}) ctxt) THEN'
  (upd_def_var_tac_aux basic_stmt_rel_info lookup_ty_new_var_thm "UpdHeap" ctxt)


fun setup_well_def_state_mask_heap_tac (basic_stmt_rel_info : basic_stmt_rel_info) lookup_ty_mask_var_thm lookup_ty_heap_var_thm ctxt =
  (Rmsg' "SetupDefState" (resolve_tac ctxt @{thms red_ast_bpl_propagate_transitive}) ctxt) THEN'
  (upd_mask_def_var_tac lookup_ty_mask_var_thm basic_stmt_rel_info ctxt) THEN'
  (upd_heap_def_var_tac lookup_ty_heap_var_thm basic_stmt_rel_info ctxt)

fun EVERY'_red_ast_bpl_rel_transitive _ [] = K all_tac
|   EVERY'_red_ast_bpl_rel_transitive ctxt (tac :: tacs) = 
      resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN'
      tac ctxt THEN'               
      EVERY'_red_ast_bpl_rel_transitive ctxt tacs

fun EVERY'_red_ast_bpl_rel_transitive_refl ctxt tacs = 
    EVERY'_red_ast_bpl_rel_transitive ctxt tacs THEN'
    resolve_tac ctxt @{thms red_ast_bpl_rel_refl}
      


(* tactic for introducing temporary perm variable *)

fun store_temporary_perm_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_ty_thm eval_vpr_perm_tac =
  (Rmsg' "store perm 1" (resolve_tac ctxt @{thms store_temporary_perm_rel}) ctxt) THEN'
  (Rmsg' "store perm 2" ((simp_tac_with_thms [] ctxt THEN' (blast_tac ctxt ORELSE' (K all_tac))) |> SOLVED') ctxt) THEN'
  (Rmsg' "store perm eval vpr perm" (eval_vpr_perm_tac ctxt) ctxt) THEN'
  (Rmsg' "store perm rel perm" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
  (Rmsg' "store perm disjointness" ((#aux_var_disj_tac info ctxt) |> SOLVED') ctxt) THEN'
  (Rmsg' "store perm lookup" (assm_full_simp_solved_with_thms_tac [lookup_aux_var_ty_thm] ctxt) ctxt) THEN'
  (Rmsg' "store perm 2" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "store perm empty rtype_interp" (assm_full_simp_solved_tac ctxt) ctxt)

\<close>

ML \<open>

(* tactics for introducing facts into goals *)

fun intro_fact_lookup_no_perm_const_tac ctxt tr_def_thm = 
  revcut_tac @{thm lookup_no_perm_const[OF state_rel_boogie_const_rel_2]} THEN'
  fastforce_tac ctxt [] THEN'
  assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt

fun intro_fact_lookup_null_const_tac ctxt tr_def_thm = 
  revcut_tac @{thm lookup_null_const[OF state_rel_boogie_const_rel_2]} THEN'
  fastforce_tac ctxt [] THEN'
  assm_full_simp_solved_with_thms_tac [tr_def_thm] ctxt

(* lookup_aux_var_thm should already instantiate the auxiliary variable *)
fun intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_thm = 
  revcut_tac lookup_aux_var_thm THEN'
  fastforce_tac ctxt [] THEN'    
  assm_full_simp_solved_tac ctxt

(* the Viper field name must be instantiated in exp_rel_perm_access_thm *)
fun intro_fact_mask_lookup_reduction ctxt (info: basic_stmt_rel_info) exp_rel_info exp_rel_perm_access_thm vpr_rcv_red_tac =
  (Rmsg' "intro mask lookup red 1" (revcut_tac exp_rel_perm_access_thm) ctxt) THEN'
  (Rmsg' "intro mask lookup red 2" (resolve_tac ctxt @{thms mask_read_wf_concrete} THEN'
                                    resolve_tac ctxt [#ctxt_wf_thm info])
                                      ctxt) THEN'
  (Rmsg' "intro mask lookup red 4" (resolve_tac ctxt @{thms wf_ty_repr_basic}) ctxt) THEN'
  (Rmsg' "intro mask lookup red 5" (blast_tac ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 6" (vpr_rcv_red_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "intro mask lookup red 7" ((#field_rel_single_tac info) ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "intro mask lookup red 8" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 9" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 10" (exp_rel_tac exp_rel_info ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 11" (assm_full_simp_solved_with_thms_tac @{thms read_mask_concrete_def} ctxt) ctxt)

\<close>


end