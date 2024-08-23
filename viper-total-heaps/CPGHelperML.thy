theory CPGHelperML
  imports ViperBoogieRelUtil MLTypeDeclarations TotalViperHelperML ExpRelML  "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac' 

fun simp_then_if_not_solved_blast_tac ctxt = 
  (simp_tac_with_thms [] ctxt |> SOLVED') ORELSE' (simp_tac_with_thms [] ctxt THEN' blast_tac ctxt)

fun simplify_continuation ctxt = simp_only_tac @{thms convert_list_to_cont.simps} ctxt

fun unfold_bigblock_atomic (ctxt : Proof.context) (bigblock : term) : (int -> tactic) =
  case bigblock of
    Const (bigblock_name, _) =>
    ( let val thm = Proof_Context.get_thms ctxt (bigblock_name ^ "_def")
      in         
         simp_only_tac thm ctxt
         (*(K (unfold_tac ctxt thm))*) (* unfold_tac has an effect on all subgoals, which we avoid, since it makes tactics less robust *)
      end )
  | _ => K all_tac

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
            | _ => K all_tac)
        else
          unfold_bigblock_atomic ctxt bigblock        
     | _ => K all_tac   

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
  | _ => (writeln(Syntax.string_of_term ctxt t); K all_tac)
  

(* The following tactic unfolds in certain contexts the currently active bigblock or the next 
bigblock if the currently active bigblock is empty.?aux_var
The goal is to make sure that after this tactic the (bigblock, continuation) configuration is in 
a form where bigblock is unfolded and not empty. The nonemptiness guarantee relies on the assumption
 that an empty bigblock is not succeeded by another empty bigblock. *)
fun unfold_bigblock_in_goal ctxt =
  SUBGOAL (fn (t,i) => unfold_bigblock_in_goal_aux ctxt (Logic.strip_assums_concl t, i) i)

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

(* progress_red_bpl_rel_tac is analogous to progress_tac except that the goal is expressed via \<open>red_ast_bpl_rel\<close> *)
fun progress_red_bpl_rel_tac ctxt = 
   (unfold_bigblock_in_goal ctxt) THEN'
   (resolve_tac ctxt [@{thm red_ast_bpl_rel_empty_block}] ORELSE'
    resolve_tac ctxt [@{thm red_ast_bpl_rel_refl}])

fun progress_red_bpl_rel_tac_2 tac ctxt = 
   (unfold_bigblock_in_goal ctxt) THEN'
   (tac ctxt) THEN'
   (resolve_tac ctxt @{thms red_ast_bpl_rel_empty_block} ORELSE'
    resolve_tac ctxt @{thms red_ast_bpl_rel_refl})

(* rewrite_red_bpl_rel_tac rewrites a goal \<open>red_ast_bpl_rel\<close> such that the current big block is unfolded
   (or if it is empty it is progressed to the next one)  *)
fun rewrite_red_bpl_rel_tac ctxt =
  (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive_2}) THEN'
  (progress_red_bpl_rel_tac ctxt)

(* rewrite_rel_general_tac is analogous to rewrite_red_bpl_rel_tac except it deals with \<open>rel_general\<close>
   goals instead of \<open>red_ast_bpl_rel\<close> goals *)
fun rewrite_rel_general_tac ctxt =
   (resolve_tac ctxt @{thms rel_propagate_pre_3_only_state_rel}) THEN'
   (progress_red_bpl_rel_tac ctxt)
                                 
(* general information for tactics *)

  (* TODO rename *)
  type basic_stmt_rel_info = {
      ctxt_wf_thm: thm,
      consistency_wf_thm: thm,
      consistency_down_mono_thm: thm,
      (* Require multiple tr_def theorems to acommodate translation records with and without saved old state *)
      tr_def_thms: thm list,
      method_data_table: method_data Symtab.table,
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
  (Rmsg' (errorMsgPrefix^"DefVar3") (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar4") (assm_full_simp_solved_with_thms_tac [lookup_ty_new_var_thm, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar5") (assm_full_simp_solved_with_thms_tac (#tr_def_thms basic_stmt_rel_info) ctxt) ctxt) THEN'
  (Rmsg' (errorMsgPrefix^"DefVar6") (assm_full_simp_solved_tac ctxt) ctxt) THEN' 
  (Rmsg' (errorMsgPrefix^"DefVarAuxVarDisj") ((#aux_var_disj_tac basic_stmt_rel_info) ctxt) ctxt)

fun upd_mask_def_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt =
  (Rmsg' "UpdMaskDefVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "UpdMaskDefVar2" (resolve_tac ctxt @{thms mask_def_var_upd_red_ast_bpl_propagate}) ctxt) THEN'
  (upd_def_var_tac_aux basic_stmt_rel_info lookup_ty_new_var_thm "UpdMask" ctxt)

fun upd_heap_def_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt  =
  (Rmsg' "UpdHeapDefVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "UpdHeapDefVar2" (resolve_tac ctxt @{thms heap_def_var_upd_red_ast_bpl_propagate}) ctxt) THEN'
  (upd_def_var_tac_aux basic_stmt_rel_info lookup_ty_new_var_thm "UpdHeap" ctxt)

fun capture_mask_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt =
  (Rmsg' "CaptureMaskVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "CaptureMaskVar2" (resolve_tac ctxt @{thms mask_eval_var_upd_red_ast_bpl_propagate_capture}) ctxt) THEN'
  (upd_def_var_tac_aux basic_stmt_rel_info lookup_ty_new_var_thm "CaptureMask" ctxt)

fun capture_heap_var_tac lookup_ty_new_var_thm (basic_stmt_rel_info : basic_stmt_rel_info) ctxt =
  (Rmsg' "CaptureHeapVar1" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
  (Rmsg' "CaptureHeapVar2" (resolve_tac ctxt @{thms heap_eval_var_upd_red_ast_bpl_propagate_capture}) ctxt) THEN'
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
    ((* old version: resolve_tac ctxt @{thms red_ast_bpl_rel_input_implies_output} THEN' *)
      resolve_tac ctxt @{thms red_ast_bpl_rel_input_eq_output} THEN'
      assm_full_simp_solved_tac ctxt
    )


fun EVERY'_red_ast_bpl_rel_transitive_custom _ _ [] = K all_tac
|   EVERY'_red_ast_bpl_rel_transitive_custom ctxt transitive_thm (tac :: tacs) = 
      resolve_tac ctxt [transitive_thm] THEN'
      tac ctxt THEN' 
      assm_full_simp_solved_tac ctxt THEN'            
      EVERY'_red_ast_bpl_rel_transitive_custom ctxt transitive_thm tacs

fun EVERY'_red_ast_bpl_rel_transitive_with_inv_fst_eq_snd ctxt tacs =
    EVERY'_red_ast_bpl_rel_transitive_custom ctxt 
           @{thm red_ast_bpl_rel_transitive_with_inv[where ?Q="\<lambda>\<omega>. fst \<omega> = snd \<omega>"]}
           tacs

fun state_rel_capture_state_intro ctxt =
  (Rmsg' "state rel capture state intro 1" (asm_full_simp_tac ctxt) ctxt) THEN'
  (Rmsg' "state rel capture state intro 2" (resolve_tac ctxt @{thms state_rel_capture_total_stateI}) ctxt) THEN'
  (Rmsg' "state rel capture state intro 3" (blast_tac ctxt) ctxt) THEN'
  (Rmsg' "state rel capture state intro 4" (fastforce_tac ctxt []) ctxt)

(* tactic for introducing temporary perm variable,
   assumes that the current big block is unfolded *)

fun store_temporary_perm_tac ctxt (info: basic_stmt_rel_info) exp_rel_info lookup_aux_var_ty_thm eval_vpr_perm_tac =
  (Rmsg' "store perm init" (resolve_tac ctxt @{thms store_temporary_perm_rel}) ctxt) THEN'
  (Rmsg' "store perm state rel" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
  (Rmsg' "store perm eval vpr perm" (eval_vpr_perm_tac ctxt) ctxt) THEN'
  (Rmsg' "store perm rel perm" ((exp_rel_tac exp_rel_info ctxt) |> SOLVED') ctxt) THEN'
  (Rmsg' "store perm disjointness" ((#aux_var_disj_tac info ctxt) |> SOLVED') ctxt) THEN'
  (Rmsg' "store perm lookup" (assm_full_simp_solved_with_thms_tac [lookup_aux_var_ty_thm] ctxt) ctxt) THEN'
  (Rmsg' "store perm type interp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "store perm empty rtype_interp" (assm_full_simp_solved_tac ctxt) ctxt)

\<close>

ML \<open>

(* tactics for introducing facts into goals *)

fun intro_fact_lookup_no_perm_const_tac ctxt tr_def_thms = 
  revcut_tac @{thm lookup_no_perm_const[OF state_rel_boogie_const_rel_2]} THEN'
  fastforce_tac ctxt [] THEN'
  assm_full_simp_solved_with_thms_tac tr_def_thms ctxt

fun intro_fact_lookup_null_const_tac ctxt tr_def_thms = 
  revcut_tac @{thm lookup_null_const[OF state_rel_boogie_const_rel_2]} THEN'
  fastforce_tac ctxt [] THEN'
  assm_full_simp_solved_with_thms_tac tr_def_thms ctxt

(* lookup_aux_var_thm should already instantiate the auxiliary variable *)

fun intro_fact_lookup_aux_var_tac ctxt lookup_aux_var_thm = 
  revcut_tac lookup_aux_var_thm THEN'
  fastforce_tac ctxt [] THEN'    
  assm_full_simp_solved_tac ctxt

fun intro_fact_rcv_lookup_reduction ctxt exp_rel_info exp_rel_ref_access_thm vpr_rcv_red_tac =
  (Rmsg' "intro rcv lookup red 1" (revcut_tac exp_rel_ref_access_thm) ctxt) THEN'
  (Rmsg' "intro rcv lookup red 2" (blast_tac ctxt) ctxt) THEN'
  (Rmsg' "intro rcv lookup red 3" (vpr_rcv_red_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "intro rcv lookup red 4" (exp_rel_tac exp_rel_info ctxt) ctxt)

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
  (Rmsg' "intro mask lookup red 8" (assm_full_simp_solved_with_thms_tac (#tr_def_thms info) ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 9" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 10" (exp_rel_tac exp_rel_info ctxt) ctxt) THEN'
  (Rmsg' "intro mask lookup red 11" (assm_full_simp_solved_with_thms_tac @{thms read_mask_concrete_def} ctxt) ctxt)

\<close>


end