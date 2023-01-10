theory ExprWfRelML
imports ExprWfRel ExpRelML TotalViperHelperML Boogie_Lang.HelperML
begin

ML \<open>

  val R' = run_and_print_if_fail_tac' "failure"
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
      resolve_tac ctxt [@{thm syn_bop_op_non_trivial_wf_rel}] THEN'
      (Rmsg' "div_rel_1" assm_full_simp_solved_tac ctxt) (* bop *) THEN'
      (exp_rel_tac exp_rel_info ctxt |> SOLVED') THEN'
      (Rmsg' "div_rel_2" assm_full_simp_solved_tac ctxt) THEN' (* integer operation \<rightarrow> integer constant zero*)
      (Rmsg' "div_rel_3" assm_full_simp_solved_tac ctxt) THEN' (* real division -> integer or real constant zero *)
      
      ( (* prove divisor reduces to an integer if zero is an integer constant *)
        (assm_full_simp_solved_tac ctxt) ORELSE'        
          (expr_red_tac (sel_type_safety_thm_map exp_rel_info TInt)  (sel_lookup_var_thms exp_rel_info) ctxt)          
      ) THEN'
        
      ( (* prove divisor reduces to a real if zero is a real constant *) 
        (Rmsg' "div_rel_5" assm_full_simp_solved_tac ctxt) ORELSE'
        expr_red_tac (sel_type_safety_thm_map exp_rel_info TReal) (sel_lookup_var_thms exp_rel_info) ctxt
      )
    
  fun bop_wf_rel_tac exp_rel_info ctxt =
    FIRST' [
      resolve_tac ctxt [@{thm wf_rel_bop_op_trivial}] THEN'
      assm_full_simp_solved_tac ctxt, (* bop *)
      
      bop_wf_rel_div_mod exp_rel_info ctxt |> SOLVED'
   ]
        
  fun progress_tac ctxt = 
     (asm_full_simp_tac ctxt ORELSE' (K all_tac)) THEN'  (* simplify continuation *)
     resolve_tac ctxt [@{thm exI}] THEN'
     resolve_tac ctxt [@{thm conjI}] THEN'     
     (resolve_tac ctxt [@{thm red_ast_bpl_refl}] ORELSE' 
      resolve_tac ctxt [@{thm red_ast_bpl_empty_block}]) THEN'
     assm_full_simp_solved_tac ctxt


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
       fn _ => fn st => (writeln "var"; all_tac) st, (* var *)
       fn _ => fn st => (writeln "lit"; all_tac) st, (* lit *)
       fn i => fn st => (writeln "uop"; exp_wf_rel_non_trivial_tac exp_rel_info ctxt i st), (* uop *)
       fn i => fn st => (writeln "bop_eager"; binop_eager_wf_rel_tac exp_rel_info ctxt i st), (* bop eager *)
       fn i => fn st => (writeln "bop_lazy"; binop_lazy_wf_rel_tac exp_rel_info ctxt) i st (* bop lazy *)
      ]
   and 
    binop_eager_wf_rel_tac exp_rel_info ctxt =        
      (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e1 *)
      (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e2 *)
      (bop_wf_rel_tac exp_rel_info ctxt |> SOLVED')
   and 
      binop_lazy_wf_rel_tac exp_rel_info ctxt =   
        (
         (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e1 *)
         (Rmsg' "Lazy1" progress_tac ctxt) THEN' (* progress to if *)        
         (Rmsg' "Lazy2" assm_full_simp_solved_tac ctxt) THEN' (* guard And/Imp *)
         (Rmsg' "Lazy3" assm_full_simp_solved_tac ctxt) THEN' (* guard Or *)
         ((Rmsg' "Lazy4" (exp_rel_tac exp_rel_info) ctxt) |> SOLVED') THEN' (* e1 exp rel *)
         (exp_wf_rel_non_trivial_tac exp_rel_info ctxt |> SOLVED') THEN' (* e2 *)
         (progress_tac ctxt |> SOLVED') (* progress to expected configuration *)
        )
    
(*
 fun vc_expr_rel_select_tac ctxt red_expr_tac assms (t,i) =
  case (Logic.strip_assums_concl t) of
    Const (@{const_name "HOL.eq"},_) $ _ $ _ => 0
   | @{term "Trueprop"} $ t' => 0
*)
\<close>

end