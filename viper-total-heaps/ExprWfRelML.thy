theory ExprWfRelML
imports ExprWfRel ExpRelML TotalViperHelperML TotalViperHelperML CPGHelperML
begin

text \<open>We define a tactic for proving that a Boogie statement captures the well-definedness check
of a Viper expression. The tactics in general may not assume right before the tactic is invoked
that the current Boogie configuration already matches the corresponding wf_rel lemma rule that 
must be applied next. Thus, tactics may have to first progress the current Boogie configuration. 
Moreover, tactics need not ensure at the end that the Boogie configuration is in a position where 
the next simple command is already in the active big block. So, if a tactic A invokes tactic B, then 
tactic A may need to progress the current Boogie configuration after tactic B has finished.
\<close>
ML \<open>
  val Rmsg' = run_and_print_if_fail_tac'

  type exp_wf_rel_info = {
    (* tactic that solves wf_rel_fieldacc *)       
    field_access_wf_rel_syn_tac : Proof.context -> int -> tactic 
  }
  
  fun bop_wf_rel_div_mod exp_rel_info ctxt = 
      (* need to first progress the configuration in case the currently active bigblock is not unfolded or
         if the current bigblock is empty *)
      resolve_tac ctxt [@{thm wf_rel_extend_2_same_rel}] THEN' 
      progress_tac ctxt THEN'
      resolve_tac ctxt [@{thm syn_bop_op_non_trivial_wf_rel}] THEN'
      (Rmsg' "div_rel_1" assm_full_simp_solved_tac ctxt) (* bop *) THEN'
      (exp_rel_tac exp_rel_info ctxt |> SOLVED') THEN'
      (Rmsg' "div_rel_2" assm_full_simp_solved_tac ctxt) THEN' (* integer operation \<rightarrow> integer constant zero*)
      (Rmsg' "div_rel_3" assm_full_simp_solved_tac ctxt) THEN' (* real division -> integer or real constant zero *)
      
      ( (* prove divisor reduces to an integer if zero is an integer constant *)
        (assm_full_simp_solved_tac ctxt) ORELSE'        
          (expr_red_tac (#type_safety_thm_map exp_rel_info TInt)
                        (#simplify_rtype_interp_tac exp_rel_info)
                        (#lookup_var_thms exp_rel_info) 
                        (#lookup_fun_bpl_thms exp_rel_info) 
                        ctxt)          
      ) THEN'
        
      ( (* prove divisor reduces to a real if zero is a real constant *) 
        (Rmsg' "div_rel_5" assm_full_simp_solved_tac ctxt) ORELSE'
        expr_red_tac (#type_safety_thm_map exp_rel_info TReal)
                     (#simplify_rtype_interp_tac exp_rel_info) 
                     (#lookup_var_thms exp_rel_info) 
                     (#lookup_fun_bpl_thms exp_rel_info) 
                     ctxt
      )
    
  fun bop_wf_rel_tac exp_rel_info ctxt =
    FIRST' [
      resolve_tac ctxt [@{thm wf_rel_bop_op_trivial}] THEN'
      assm_full_simp_solved_tac ctxt, (* bop *)
      
      bop_wf_rel_div_mod exp_rel_info ctxt |> SOLVED'
   ]            
 
  fun exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt = 
     FIRST_AND_THEN' [
       resolve_tac ctxt [@{thm var_expr_wf_rel}], (* var *)
       resolve_tac ctxt [@{thm lit_expr_wf_rel}], (* lit *)
       resolve_tac ctxt [@{thm unop_expr_wf_rel_2}], (* uop *)
       resolve_tac ctxt [@{thm binop_eager_expr_wf_rel}] THEN' (* bop eager *)
       assm_full_simp_solved_tac ctxt, 
       resolve_tac ctxt [@{thm syn_lazy_bop_wf_rel_2}] THEN' (* bop lazy *) 
       assm_full_simp_solved_tac ctxt,   
       resolve_tac ctxt [@{thm field_access_wf_rel}], (* field access *)
       resolve_tac ctxt @{thms cond_exp_wf_rel} (* conditional expression *)
      ] [  
       fn _ => fn st => all_tac st, (* var *)
       fn _ => fn st => all_tac st, (* lit *)
       fn i => fn st => exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt i st, (* uop *)
       fn i => fn st => binop_eager_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt i st, (* bop eager *)
       fn i => fn st => binop_lazy_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt i st, (* bop lazy *)
       fn i => fn st => field_access_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt i st, (* field access *)
       fn i => fn st => cond_exp_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt i st (* cond exp *)
      ]
   and 
    binop_eager_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt =        
      (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') THEN' (* e1 *)
      (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') THEN' (* e2 *)
      (bop_wf_rel_tac exp_rel_info ctxt |> SOLVED')
   and 
      binop_lazy_wf_rel_tac exp_wf_rel_info exp_rel_info ctxt =   
         (Rmsg' "Wf E1" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info) ctxt |> SOLVED') THEN' (* e1 *)
         (Rmsg' "Lazy1" progress_tac ctxt) THEN' (* progress to if *) 
         (Rmsg' "LazyEmptyElse" (* empty else block *)
                (fn ctxt => 
                   (unfold_bigblock_in_goal ctxt) THEN'
                   (assm_full_simp_solved_tac ctxt)
                )
                ctxt) THEN'
         (Rmsg' "Lazy2" assm_full_simp_solved_tac ctxt) THEN' (* guard And/Imp *)
         (Rmsg' "Lazy3" assm_full_simp_solved_tac ctxt) THEN' (* guard Or *)
         ((Rmsg' "Lazy4" (exp_rel_tac exp_rel_info) ctxt) |> SOLVED') THEN' (* e1 exp rel *)
         (Rmsg' "Simplify Cont" simplify_continuation ctxt) THEN' (* simplify continuation since we introduce convert_list_to_cont *)
         (Rmsg' "Wf E2" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info) ctxt |> SOLVED') THEN' (* e2 *)
         (Rmsg' "Progress2" progress_tac ctxt |> SOLVED')  (* progress to expected configuration *)
   and
     field_access_wf_rel_tac (exp_wf_rel_info : exp_wf_rel_info) exp_rel_info ctxt =
       (* progress to field access *)
       resolve_tac ctxt [@{thm wf_rel_extend_2_same_rel}] THEN' 
       progress_tac ctxt THEN'
       (Rmsg' "Wf Rcv Field Access" (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info) ctxt |> SOLVED') THEN'  (* receiver *)
       (Rmsg' "Wf Field Access" (#field_access_wf_rel_syn_tac exp_wf_rel_info) ctxt |> SOLVED')
   and
    cond_exp_wf_rel_tac (exp_wf_rel_info : exp_wf_rel_info) exp_rel_info ctxt =       
       (
         resolve_tac ctxt @{thms wf_rel_extend_1_same_rel} THEN' 
         (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') THEN' (* cond wf *)
         progress_tac ctxt (* progress if *) 
       ) THEN'
       (exp_rel_tac exp_rel_info ctxt |> SOLVED') THEN' (* cond exp rel *)
       ( (* then branch *)
         simplify_continuation ctxt THEN'
         (* Apply propagation rule here, so that target program point in stmt_rel is a schematic 
            variable for the recursive call to exp_wf_rel_tac *)
         resolve_tac ctxt @{thms wf_rel_extend_1_same_rel} THEN'
         (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') THEN'
         progress_tac ctxt
       ) THEN'
       ( (* else branch *)
         simplify_continuation ctxt THEN'
        (* Apply propagation rule here, so that target program point in stmt_rel is a schematic 
           variable for the recursive call to exp_wf_rel_tac *)
         resolve_tac ctxt @{thms wf_rel_extend_1_same_rel} THEN'
         (exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt |> SOLVED') THEN'
         progress_tac ctxt
       )

   fun exps_wf_rel_aux_tac exp_wf_rel_info exp_rel_info ctxt k = 
     (if k <= 0 then
        resolve_tac ctxt [@{thm HOL.refl}]
      else 
        resolve_tac ctxt [@{thm exI}] THEN'
        resolve_tac ctxt [@{thm conjI}] THEN'
        exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt THEN'
        exps_wf_rel_aux_tac exp_wf_rel_info exp_rel_info ctxt (k-1)
      )

   (* The following tactic proves the well-definedness of a list of expressions. 
      The argument k should be the number of expressions in the list.
      If the option argument is NONE, then well-definedness checks are performed in the Boogie encoding
      and otherwise well-definedness checks are omitted in which case the option argument must provide
      a tactic to deal with that case. *)

   fun exps_wf_rel_tac _ exp_wf_rel_info exp_rel_info ctxt NONE k =   
       resolve_tac ctxt [@{thm exprs_wf_rel_alt_implies_exprs_wf_rel}] THEN'
       simp_only_tac @{thms exprs_wf_rel_alt.simps} ctxt THEN'        
       exps_wf_rel_aux_tac exp_wf_rel_info exp_rel_info ctxt k
     | exps_wf_rel_tac basic_info _ _ ctxt (SOME no_checks_tac) _ =
       no_checks_tac ctxt basic_info

   (* The following tactic proves the well-definedness of a single expression. The option tactic
      is the same as for exps_wf_rel_tac and thus deals with the well-definedness of a list of expressions
      (hence the tactic below converts the goal into a goal for a singleton expression in the case when
       the option tactic is used). *)
   fun exp_wf_rel_tac _ exp_wf_rel_info exp_rel_info ctxt NONE =
       exp_wf_rel_non_trivial_tac exp_wf_rel_info exp_rel_info ctxt
     | exp_wf_rel_tac basic_info _ _ ctxt (SOME no_checks_tac) =
       resolve_tac ctxt [@{thm exprs_wf_rel_singletonD}] THEN'
       no_checks_tac ctxt basic_info

\<close>

ML \<open>
  fun field_access_wf_rel_tac_aux init_tac lookup_mask_var_tac field_rel_single_tac ty_args_eq_tac (exp_rel_info : exp_rel_info) ctxt =
    (Rmsg' "Wf Field Access 1 (init)" init_tac ctxt) THEN'
    (Rmsg' "Wf Field Access 2 (empty rtype)" assm_full_simp_solved_tac ctxt) THEN'
    (Rmsg' "Wf Field Access 3 (state rel)" assm_full_simp_solved_tac ctxt) THEN'
    (Rmsg' "Wf Field Access 4 (rcv rel)" (exp_rel_tac exp_rel_info) ctxt |> SOLVED') THEN'
    (Rmsg' "Wf Field Access 5 (has perm fun lookup)" assm_full_simp_solved_tac ctxt) THEN'
    (Rmsg' "Wf Field Access 6 (mask var)" lookup_mask_var_tac ctxt |> SOLVED') THEN'
    (Rmsg' "Wf Field Access 7 (field rel single)" field_rel_single_tac ctxt |> SOLVED') THEN'
    (Rmsg' "Wf Field Access 8 (type params)" ty_args_eq_tac ctxt |> SOLVED')

\<close>

end