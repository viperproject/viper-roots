theory ViperBoogieEndToEndML
imports ViperBoogieEndToEnd CPGHelperML ViperBoogieHelperML ViperBoogieFunctionInst
begin

ML \<open>

  fun post_framing_rel_init_tac ctxt (basic_info : basic_stmt_rel_info) lookup_heap_var_thm lookup_mask_var_thm =
    (Rmsg' "Post Framing Init - Start" (resolve_tac ctxt [ @{thm post_framing_rel_aux} OF [@{thm wf_ty_repr_basic}, #consistency_wf_thm basic_info]]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Type Interp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Domain Type" (assm_full_simp_solved_with_thms_tac @{thms ty_repr_basic_def} ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Program" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Heap" 
            (simp_tac_with_thms @{thms ty_repr_basic_def} ctxt THEN'
            resolve_tac ctxt [lookup_heap_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Lookup Mask" 
            (simp_tac_with_thms @{thms ty_repr_basic_def} ctxt THEN'
             resolve_tac ctxt [lookup_mask_var_thm]) ctxt) THEN'
    (Rmsg' "Post Framing Init - Zero Mask" 
            (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info] ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Disjointntess" ((#aux_var_disj_tac basic_info) ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Heap and Mask Disjoint" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 1"
         (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN'
         resolve_tac ctxt @{thms red_ast_bpl_rel_if_nondet_then} THEN'
         (* One_nat_def is applied as a hack to match 1 and Suc 0.
           It would be good to solve this problem more generally such that there cannot be such
           mismatches at this point *)
         progress_red_bpl_rel_tac_2 (fn ctxt => simp_only_tac @{thms One_nat_def} ctxt) ctxt THEN'
         simplify_continuation ctxt) ctxt) THEN'
    (Rmsg' "Post Framing Init - Propagate 2" (resolve_tac ctxt @{thms stmt_rel_propagate_same_rel}) ctxt) THEN'
    (Rmsg' "Post Framing Init - Assume Good State" (progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info)) ctxt)

\<close>

method fun_interp_wf_aux_tac for fid :: fun_enum_bpl uses  fun_wf_thm  = 
      ((rule exI, rule conjI),
      (rule fun_interp_vpr_bpl_concrete_lookup[OF fun_repr_concrete_inj, where ?fid=fid]),
      simp,
      (simp del: fun_interp_single_wf.simps fun_interp_single_wf_2.simps),
      (rule lift_fun_decl_fun_interp_single_wf_eq[OF _ fun_wf_thm[OF wf_ty_repr_basic]]),
      (simp add: ty_repr_basic_def))

lemmas axioms_sat_proof_del = vbpl_absval_ty.simps type_of_val.simps full_ext_env.simps

method simplify_bound_var_tac = 
   (simp add: inversion_type_of_vbpl_val_equalities realv_inversion_type_of_vbpl_val del: axioms_sat_proof_del id_apply),
   (erule conjE, erule exE)+,
   (simp only: id_apply)

method axiom_proof_init =
   (simp only: expr_sat_def),
   ((rule RedForallT_True | rule RedForAllTrue)+ | succeed),
   (simplify_bound_var_tac) ? \<comment>\<open>only makes sense if there is at least one universal value quantifier\<close>

ML \<open>
   
  \<comment>\<open>TODO: move to same location as add_simps\<close>
  fun del_simps [] ctxt = ctxt
   |  del_simps (thm::thms) ctxt = del_simps thms (Simplifier.del_simp thm ctxt)

  type axiom_tac_data = {
    lookup_const_tac : (int -> tactic),
    finterp_eval_tac : (Proof.context -> term -> int -> tactic),
    fun_interp_inst_def_thm: thm,    
    lookup_field_tac: (int -> tactic)
  }

  fun extract_fun_enum_bpl t =
    case t of 
      @{term "Trueprop"} $ t' => extract_fun_enum_bpl t'
    | Const (@{const_name HOL.eq}, _) $ lhs $ _ => extract_fun_enum_bpl lhs
    | Const (@{const_name "fun_interp_vpr_bpl"}, _) 
           $ _ (* program *)
           $ _ (* type representation *)
           $ _ (* field translation *)
           $ fun_enum
           $ _ (* type parameters *)
           $ _ (* function arguments *) =>
             fun_enum
    | _ => raise TERM ("goal is not fun_interp_vpr_bpl", [t])

  fun axiom_aux_tac ctxt lookup_const_thms del_thms (axiom_tac_data : axiom_tac_data) = 
    FIRST_AND_THEN' [
       resolve_tac ctxt @{thms RedVar},
       resolve_tac ctxt @{thms RedBVar},
       resolve_tac ctxt @{thms RedBinOp},
       resolve_tac ctxt @{thms RedFunOp},
       resolve_tac ctxt @{thms RedLit},
       resolve_tac ctxt @{thms RedUnOp},
       Rmsg' "Unexpected case" (K no_tac) ctxt
    ] [
      (* Var *)
      (Rmsg' "RedVar" ( (#lookup_const_tac axiom_tac_data |> SOLVED') ORELSE' 
                        (#lookup_field_tac axiom_tac_data |> SOLVED')) ctxt), 

      (* BVar *)
       Rmsg' "RedBVar simp" (assm_full_simp_solved_tac ctxt) ctxt,
   
      (* BinOp *)
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       Rmsg' "RedBinOp simp" (assm_full_simp_solved_tac ctxt) ctxt,

      (* FunOp *)
       (Rmsg' "RedFunOp init"
         (simp_only_tac [#fun_interp_inst_def_thm axiom_tac_data] ctxt THEN'
          resolve_tac ctxt @{thms fun_interp_vpr_bpl_concrete_lookup[OF fun_repr_concrete_inj]} THEN'
          fast_tac (ctxt addIs @{thms fun_repr_concrete.simps})) ctxt) THEN'
      
       (* function arguments *)
       (fn i => fn st => axiom_aux_list_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       (* function interpretation evaluation *)
       (Rmsg' "RedFunOp finish"
             (SUBGOAL (fn (t,i) => (#finterp_eval_tac axiom_tac_data) ctxt (extract_fun_enum_bpl (Logic.strip_assums_concl t)) i) 
                                            |> SOLVED') ctxt),

       (* Lit *)
       K all_tac,

       (* UnOp *)
       (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) THEN'
       Rmsg' "ReUnOp simp" (assm_full_simp_solved_tac ctxt) ctxt,

       (* unexpected case *)
       K no_tac
     ]

and axiom_aux_list_tac ctxt lookup_const_thms del_thms (axiom_tac_data : axiom_tac_data) =
    FIRST_AND_THEN'
      [ resolve_tac ctxt @{thms RedExpListCons},
        resolve_tac ctxt @{thms RedExpListNil},
        Rmsg' "Unexpected case: axiom_aux_list_tac" (K no_tac) ctxt
      ] 
      [ (* cons *)
        ((fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st) |> SOLVED') THEN'
        (fn i => fn st => axiom_aux_list_tac ctxt lookup_const_thms del_thms axiom_tac_data i st),

        (* nil *)
        K all_tac,

       (* unexpected case *)
        K no_tac
      ]

fun finterp_eval_concrete_tac del_thms ctxt t = 
  case t of
    Const (@{const_name FReadHeap}, _) => 
     asm_full_simp_tac (del_simps  (@{thm fun_upd_apply}::del_thms) (add_simps @{thms lift_fun_bpl_def heap_upd_ty_preserved_2_basic} ctxt)) THEN'
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps @{thms ty_repr_basic_def} ctxt))
  | Const (@{const_name FReadMask}, _) =>
     asm_full_simp_tac (del_simps (@{thm fun_upd_apply}::del_thms) (add_simps @{thms lift_fun_bpl_def} ctxt)) THEN'
     asm_full_simp_tac (del_simps @{thms fun_upd_apply} (add_simps @{thms ty_repr_basic_def} ctxt))
  | _ =>      
     asm_full_simp_tac (del_simps del_thms (add_simps @{thms lift_fun_bpl_def ty_repr_basic_def ty_bpl_normal_field} ctxt))   

fun axiom_tac ctxt fun_interp_inst_def_thm lookup_const_thms lookup_fields_thms del_thms =
  let val axiom_tac_data : axiom_tac_data = { 
     lookup_const_tac = asm_full_simp_tac (del_simps del_thms (add_simps (@{thm lookup_full_ext_env_same} :: lookup_const_thms) ctxt)),
     lookup_field_tac = asm_full_simp_tac (del_simps del_thms (add_simps (@{thm lookup_full_ext_env_same} :: lookup_fields_thms) ctxt)),
     finterp_eval_tac = finterp_eval_concrete_tac del_thms,
     fun_interp_inst_def_thm = fun_interp_inst_def_thm
  }
  in (fn i => fn st => axiom_aux_tac ctxt lookup_const_thms del_thms axiom_tac_data i st)
  end

\<close>

end