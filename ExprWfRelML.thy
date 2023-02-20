theory ExprWfRelML
imports ExprWfRel ExpRelML TotalViperHelperML Boogie_Lang.HelperML TotalViper.CPGHelperML
begin

text \<open>We define a tactic for proving that a Boogie statement captures the well-definedness check
of a Viper expression. The tactics in general may not assume right before the tactic is invoked
that the current Boogie configuration already matches the corresponding wf_rel lemma rule that 
must be applied next. Thus, tactics may have to first progress the current Boogie configuration. 
Moreover, tactics need not ensure at the end that the Boogie configuration is in a position where 
the next simple command is already in the active big block. So, if a tactic A invokes tactic B, then 
tactic A may need to progress the current Boogie configuration.
\<close>
ML \<open>
  val Rmsg' = run_and_print_if_fail_tac' 

  fun exp_wf_rel_trivial_tac ctxt =
      FIRST' [
       resolve_tac ctxt [@{thm var_expr_wf_rel}],

       resolve_tac ctxt [@{thm lit_expr_wf_rel}],    

       resolve_tac ctxt [@{thm unop_expr_wf_rel_2}] THEN' 
       (fn i => fn st =>  exp_wf_rel_trivial_tac ctxt i st),
       
       fn i => fn st =>
         (i,st) |->
         ( 
           resolve_tac ctxt [@{thm binop_eager_expr_wf_rel}] THEN'
           assm_full_simp_solved_tac ctxt THEN'
           (exp_wf_rel_trivial_tac ctxt |> SOLVED') THEN'
           (exp_wf_rel_trivial_tac ctxt |> SOLVED') THEN'
           resolve_tac ctxt [@{thm wf_rel_bop_op_trivial}] THEN'
           assm_full_simp_solved_tac ctxt
         ),
  
       fn i => fn st => 
         (i,st) |->
         (
           resolve_tac ctxt [@{thm binop_lazy_expr_wf_rel}] THEN'
           assm_full_simp_solved_tac ctxt THEN'
           (exp_wf_rel_trivial_tac ctxt |> SOLVED') THEN'
           (exp_wf_rel_trivial_tac ctxt |> SOLVED') THEN'
           resolve_tac ctxt [@{thm wf_rel_no_failure_refl}]
         )
      ]

  
  fun bop_wf_rel_div_mod exp_rel_info ctxt = 
      (* need to first progress the configuration in case the currently active bigblock is not unfolded or
         if the current bigblock is empty *)
      resolve_tac ctxt [@{thm wf_rel_extend_2}] THEN' 
      progress_tac ctxt THEN'
      resolve_tac ctxt [@{thm syn_bop_op_non_trivial_wf_rel}] THEN'
      (Rmsg' "div_rel_1" assm_full_simp_solved_tac ctxt) (* bop *) THEN'
      (exp_rel_tac exp_rel_info ctxt |> SOLVED') THEN'
      (Rmsg' "div_rel_2" assm_full_simp_solved_tac ctxt) THEN' (* integer operation \<rightarrow> integer constant zero*)
      (Rmsg' "div_rel_3" assm_full_simp_solved_tac ctxt) THEN' (* real division -> integer or real constant zero *)
      
      ( (* prove divisor reduces to an integer if zero is an integer constant *)
        (assm_full_simp_solved_tac ctxt) ORELSE'        
          (expr_red_tac (#type_safety_thm_map exp_rel_info TInt)  (#lookup_var_thms exp_rel_info) ctxt)          
      ) THEN'
        
      ( (* prove divisor reduces to a real if zero is a real constant *) 
        (Rmsg' "div_rel_5" assm_full_simp_solved_tac ctxt) ORELSE'
        expr_red_tac (#type_safety_thm_map exp_rel_info TReal) (#lookup_var_thms exp_rel_info) ctxt
      )
    
  fun bop_wf_rel_tac exp_rel_info ctxt =
    FIRST' [
      resolve_tac ctxt [@{thm wf_rel_bop_op_trivial}] THEN'
      assm_full_simp_solved_tac ctxt, (* bop *)
      
      bop_wf_rel_div_mod exp_rel_info ctxt |> SOLVED'
   ]      
  
  fun exp_wf_rel_non_trivial_tac exp_rel_info ctxt = 
     FIRST_AND_THEN' [
       resolve_tac ctxt [@{thm var_expr_wf_rel}],
       resolve_tac ctxt [@{thm lit_expr_wf_rel}],    
       resolve_tac ctxt [@{thm unop_expr_wf_rel_2}],       
       resolve_tac ctxt [@{thm binop_eager_expr_wf_rel}] THEN'
       assm_full_simp_solved_tac ctxt,
       resolve_tac ctxt [@{thm syn_lazy_bop_wf_rel_2}] THEN'
       assm_full_simp_solved_tac ctxt
      ] [  
       fn _ => fn st => all_tac st, (* var *)
       fn _ => fn st => all_tac st, (* lit *)
       fn i => fn st => exp_wf_rel_non_trivial_tac exp_rel_info ctxt i st, (* uop *)
       fn i => fn st => binop_eager_wf_rel_tac exp_rel_info ctxt i st, (* bop eager *)
       fn i => fn st => binop_lazy_wf_rel_tac exp_rel_info ctxt i st (* bop lazy *)
      ]
   and 
    binop_eager_wf_rel_tac exp_rel_info ctxt =        
      (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e1 *)
      (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e2 *)
      (bop_wf_rel_tac exp_rel_info ctxt |> SOLVED')
   and 
      binop_lazy_wf_rel_tac exp_rel_info ctxt =   
        (
         (Rmsg' "Wf E1" (exp_wf_rel_non_trivial_tac exp_rel_info) ctxt |> SOLVED') THEN' (* e1 *)
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
         (Rmsg' "Wf E2" (exp_wf_rel_non_trivial_tac exp_rel_info) ctxt |> SOLVED') THEN' (* e2 *)
         (Rmsg' "Progress2" progress_tac ctxt |> SOLVED')  (* progress to expected configuration *)
        )
\<close>

end