theory InhaleRelML
imports Boogie_Lang.HelperML ExprWfRelML InhaleRel 
begin

ML \<open>
  val Rmsg' = run_and_print_if_fail_2_tac' 

  datatype 'a inhale_rel_hint = 
    AtomicInhHint of 'a 
  | StarInhHint of ( ('a inhale_rel_hint) * ('a inhale_rel_hint))
  | ImpInhHint of 
       exp_wf_rel_info *       
       exp_rel_info *
       ('a inhale_rel_hint)
  | NoInhHint (* used for debugging purposes *)

  type 'a atomic_inhale_rel_tac = (Proof.context -> basic_stmt_rel_info -> 'a -> int -> tactic)

  type 'a inhale_rel_info = {
    basic_info: basic_stmt_rel_info,
    atomic_rel_tac: 'a atomic_inhale_rel_tac
  }

  fun inhale_rel_tac ctxt (info: 'a inhale_rel_info) (hint: 'a inhale_rel_hint) =
    case hint of
      StarInhHint (left_hint, right_hint) => 
        resolve_tac ctxt [@{thm inhale_rel_star}] THEN' 
        (inhale_rel_tac ctxt info left_hint |> SOLVED') THEN'
        (inhale_rel_tac ctxt info right_hint |> SOLVED')
    | ImpInhHint (exp_wf_rel_info, exp_rel_info, right_hint) => 
         (
           (Rmsg' "ImpInh 1" (resolve_tac ctxt [@{thm wf_rel_extend_1}]) ctxt) THEN'
           (Rmsg' "ImpInh wf cond" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') ctxt) THEN'
           (Rmsg' "ImpInh 2" ((progress_tac ctxt) |> SOLVED') ctxt)
         ) THEN'
          (Rmsg' "ImpInh empty else" (* empty else block *)                
                 ((unfold_bigblock_in_goal ctxt) THEN'
                 (assm_full_simp_solved_tac ctxt))
              ctxt)  THEN'
         (
           (Rmsg' "ImpInh cond rel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt)
         ) THEN'
         (
          (* apply propagation rule here, so that target program point in stmt_rel is a schematic 
             variable for the recursive call to inhale_rel_tac *)
           simplify_continuation ctxt THEN'
           (Rmsg' "ImpInh 3" (resolve_tac ctxt [@{thm inhale_propagate_post}]) ctxt) THEN'           
           (inhale_rel_tac ctxt info right_hint |> SOLVED') THEN'
           (Rmsg' "ImpInh 4" (progress_tac ctxt) ctxt)
         )
    | AtomicInhHint atomicHint => (#atomic_rel_tac info) ctxt (#basic_info info) atomicHint
    | NoInhHint => K all_tac
\<close>

ML \<open>
  datatype atomic_inhale_rel_hint = 
    PureExpInhHint of 
       exp_wf_rel_info *
       exp_rel_info 
  | FieldAccInhHint of
       exp_wf_rel_info * 
       exp_rel_info
\<close>


end
