theory CPGHelperML
  imports ViperBoogieBasicRel Boogie_Lang.HelperML
begin

ML \<open>

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
  | Const (@{const_name "is_empty_bigblock"}, _) $ bigblock =>
      unfold_bigblock_atomic ctxt bigblock
  | _ => (writeln(Syntax.string_of_term ctxt t); all_tac)
  

(* The following tactic unfolds in certain contexts the currently active bigblock or the next 
bigblock if the currently active bigblock is empty.
The goal is to make sure that after this tactic the (bigblock, continuation) configuration is in 
a form where bigblock is unfolded and not empty. The nonemptiness guarantee relies on the assumption
 that an empty bigblocks is not succeeded by another empty bigblock. *)
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

(* general information for tactics *)
  (* TODO rename *)
  type basic_stmt_rel_info = {
      ctxt_wf_thm: thm,
      tr_def_thm: thm,
      var_rel_tac: (Proof.context -> int -> tactic),
      var_context_vpr_tac: (Proof.context -> int -> tactic),
      field_rel_single_tac : (Proof.context -> int -> tactic),
      aux_var_disj_tac: (Proof.context -> int -> tactic),
      type_interp_econtext: thm  
  }


\<close>


end