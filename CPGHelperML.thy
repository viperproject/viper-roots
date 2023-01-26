theory CPGHelperML
  imports ViperBoogieBasicRel
begin

ML \<open>
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
\<close>


end