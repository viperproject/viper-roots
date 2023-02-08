theory ViperBoogieEndToEnd
imports ExpProofGenTest
begin

definition stmt_correct_total_2 where
"stmt_correct_total_2 ctxt R \<Lambda> s \<equiv>
      (\<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
                red_stmt_total ctxt R \<Lambda> s \<omega> r \<longrightarrow> r \<noteq> RFailure)"

term red_cfg

term stmt_rel

typ "'a vbpl_absval"

lemma proc_is_correct_elim:
  assumes 
     "proc_is_correct A fun_decls constants global_vars axioms proc proc_body_satisfies_spec_general" and
     "proc_body proc = Some (locals, p_body)" and
     "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)" and
     "\<forall>v. closed ((type_of_val A) v)" and
     "fun_interp_wf A fun_decls \<Gamma>" and
     "(list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc)" and
     "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
     "state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc))" and
     "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
shows 
  "(proc_body_satisfies_spec_general 
                                        A [] (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc) (proc_checked_posts proc) p_body
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> )"
  using assms
  by fastforce

lemma valid_configuration_not_failure:
  assumes "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts bb cont state"
  shows "state \<noteq> Failure"
  using assms
  unfolding valid_configuration_def
  by simp

(*
declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]
*)

type_synonym ('a,'m) proc_body_satisfies_spec_ty = 
   "'a absval_ty_fun \<Rightarrow> 'm proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"

abbreviation state_rel_initial where 
  "state_rel_initial ctxt Pr ty_rep tr_vpr_bpl wd_mask w ns \<equiv> 
       state_rel Pr ty_rep tr_vpr_bpl ctxt wd_mask w w ns"

abbreviation red_bigblock_multi where
  "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast \<equiv> rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> ast)"

lemma end_to_end_stmt_rel:
  assumes ProcBodySome: "proc_body proc_bpl = Some (locals_bpl, proc_body_bpl)" and

          \<comment>\<open>Viper encoding does not use Boogie procedure preconditions\<close>
          ProcPresEmpty: "proc_pres proc_bpl = []" and
          \<comment>\<open>The Boogie procedure is correct.\<close>             
             \<comment>\<open>Note that we need to explicitly provide the type for term\<open>A\<close> to 
                be able to instantiate A with \<^term>\<open>vbpl_absval_ty ty_rep\<close>\<close>
          Boogie_correct: "\<And>A :: ('a vbpl_absval) absval_ty_fun. proc_is_correct A fun_decls constants global_vars axioms (proc_bpl :: ast procedure) 
                  (Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty))" and          


          \<comment>\<open>Viper and Boogie statement are related\<close>
          StmtRel: "stmt_rel 
             \<comment>\<open>input relation\<close>
             (state_rel_empty (state_rel_initial ctxt Pr (ty_rep :: 'a ty_repr_bpl) tr_vpr_bpl (mask_var tr_vpr_bpl)))
             \<comment>\<open>output relation is irrelevant\<close>
             R' 
             ctxt_vpr StateCons \<Lambda> P ctxt 
             stmt_vpr 
             \<comment>\<open>initial program point in Boogie procedure body\<close>
             (convert_ast_to_program_point proc_body_bpl)
             \<comment>\<open>output program point in Boogie procedure body is irrelevant\<close>
             \<gamma>'"  and 

\<comment>\<open>TODO: I have not yet proved the following assumptions for specific Boogie programs\<close>
     InitialStateRel: "\<And> \<omega>. is_empty_total \<omega> \<Longrightarrow> 
                       \<exists>ns.  (state_rel_empty (state_rel_initial ctxt Pr (ty_rep :: 'a ty_repr_bpl) tr_vpr_bpl (mask_var tr_vpr_bpl))) \<omega> ns" and
     WfTyRep: "wf_ty_repr_bpl ty_rep" and
     FunInterp: "fun_interp_wf (vbpl_absval_ty ty_rep) fun_decls \<Gamma>" and
     TyEnvClosed: "(list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc_bpl)" and
     GlobalsWf: "state_typ_wf (vbpl_absval_ty ty_rep) \<Omega> gs (constants @ global_vars)" and
     LocalsWf: "state_typ_wf (vbpl_absval_ty ty_rep) \<Omega> ls ((proc_args proc_bpl)@ (locals_bpl @ proc_rets proc_bpl))" and
     AxiomsSat: "axioms_sat (vbpl_absval_ty ty_rep) (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"

  shows "stmt_correct_total_2 ctxt_vpr StateCons \<Lambda> stmt_vpr"
  unfolding stmt_correct_total_2_def
proof (rule allI | rule impI)+
  fix \<omega> r 
  assume "is_empty_total \<omega>" and RedStmtVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> r"
  
  let ?abs="vbpl_absval_ty ty_rep"

  note Boogie_correct_inst=Boogie_correct[where ?A="?abs"]

  
  have ProcBodyBplCorrect:
      "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) ?abs [] (constants@global_vars, (proc_args proc_bpl)@(locals_bpl@(proc_rets proc_bpl))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc_bpl) (proc_checked_posts proc_bpl) proc_body_bpl
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
  proof (rule proc_is_correct_elim[OF Boogie_correct_inst ProcBodySome])
    show "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_vbpl_val ty_rep v = t)"
      by (simp add: closed_types_inhabited)
  next
    show "\<forall>v. closed (type_of_vbpl_val ty_rep v)"
    proof (rule allI)
      fix v
      show "closed (type_of_vbpl_val ty_rep v)"
      proof (cases v)
        case (LitV x1)
        then show ?thesis by simp
      next
        case (AbsV x2)
        then show ?thesis 
          using vbpl_absval_ty_closed[OF WfTyRep]
          by fastforce
      qed
    qed
  next
    show "fun_interp_wf (vbpl_absval_ty ty_rep) fun_decls \<Gamma>"
      by (rule FunInterp)
  next
    show "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc_bpl"
      by (rule TyEnvClosed)
  next
    show "state_typ_wf (vbpl_absval_ty ty_rep) \<Omega> gs (constants @ global_vars)"
      by (rule GlobalsWf)
  next 
    show "state_typ_wf (vbpl_absval_ty ty_rep) \<Omega> ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      by (rule LocalsWf)
  next
    show "axioms_sat (vbpl_absval_ty ty_rep) (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
      by (rule AxiomsSat)
  qed

  show "r \<noteq> RFailure"
  proof (rule ccontr)
    assume "\<not> r \<noteq> RFailure"
    hence "r = RFailure" by simp

    from \<open>is_empty_total \<omega>\<close> obtain ns where 
      StmtRelInitialInst: 
      "(state_rel_empty (state_rel_initial ctxt Pr (ty_rep :: 'a ty_repr_bpl) tr_vpr_bpl (mask_var tr_vpr_bpl))) \<omega> ns"
      using InitialStateRel
      by blast

    from stmt_rel_failure_elim[OF StmtRel StmtRelInitialInst] RedStmtVpr \<open>r = _\<close> obtain c' where
      "snd c' = Failure" and 
      RedBpl: "red_ast_bpl P ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
      by blast

    let ?c'_program_point = "fst c'"
    let ?c'_bigblock = "fst ?c'_program_point"
    let ?c'_cont = "snd ?c'_program_point"


    from RedBpl have 
      "(red_bigblock_multi (vbpl_absval_ty ty_rep) [] (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl) \<Gamma> \<Omega> proc_body_bpl)\<^sup>*\<^sup>*
         (init_ast proc_body_bpl \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) (?c'_bigblock, ?c'_cont, Failure)"
      unfolding red_ast_bpl_def
   \<comment>\<open>TODO: need to prove that if Boogie program reduces to Failure with red_ast_bpl, then this must also be the case with
           red_bigblock (difference is that red_ast_bpl reduces simple command by simple command, while red_bigblock reduces
           all the simple commands at once)\<close>
      sorry

    with ProcBodyBplCorrect
    show False
    using ProcPresEmpty valid_configuration_not_failure
    unfolding Ast.proc_body_satisfies_spec_def expr_all_sat_def
    by fastforce
qed
qed

(*
declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]
*)
term red_bigblock_small
lemma red_ast_block_red_bigblock_failure_preserve:
  assumes "red_ast_bpl P ctxt c c'" and 
          \<comment>\<open>If \<^const>\<open>red_ast_bpl\<close> does not reduce to failure, then the lemma does not hold, since
             \<^const>\<open>red_ast_bpl\<close> can take more steps.\<close>
          "snd c' = Failure" and 
          "type_interp ctxt = A" and "var_context ctxt = \<Lambda>" and "fun_interp ctxt = \<Gamma>"
        shows "\<exists>d'. red_bigblock_multi A ([] :: ast proc_context) \<Lambda> \<Gamma> [] P (fst (fst c), snd (fst c), snd c) d' 
                    \<and> (snd (snd d') = Failure)"
  using assms
  unfolding red_ast_bpl_def
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by auto    
next
  case (step y z)
  from this obtain d' where    
     Red2: "ViperBoogieEndToEnd.red_bigblock_multi A ([] :: ast proc_context) \<Lambda> \<Gamma> [] P (fst (fst z), snd (fst z), snd z) d'" and
     Red2StateFailure: "snd (snd d') = Failure"
    by blast

  from \<open>red_bigblock_small P ctxt y z\<close>
  show ?case
  proof cases
    case (RedBigBlockSmallSimpleCmd c s s' name cs str tr cont)
    show ?thesis
    proof (cases s')
      case (Normal ns')
      then show ?thesis sorry
    next
      case Failure
      then show ?thesis sorry
    next
      case Magic
      then show ?thesis sorry
    qed
  next
    case (RedBigBlockSmallNoSimpleCmdOneStep name str tr cont s b' cont' s')
    then show ?thesis 
      using Red2 Red2StateFailure assms
      by (metis (no_types, lifting) converse_rtranclp_into_rtranclp fstI sndI step.prems(3))
  qed           
qed
      

end