theory ViperBoogieEndToEnd
imports ExpProofGenTest
begin

definition stmt_correct_total_2 where
  "stmt_correct_total_2 ctxt R \<Lambda> s \<equiv>
        \<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
                  red_stmt_total ctxt R \<Lambda> s \<omega> r \<longrightarrow> r \<noteq> RFailure"

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

(*
      "\<lbrakk> (type_interp ctxt), ([] :: ast proc_context), (var_context ctxt), (fun_interp ctxt), [] \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s' \<rbrakk> \<Longrightarrow>
       red_bigblock_small P ctxt (((BigBlock name (c#cs) str tr), cont), s) (((BigBlock name cs str tr), cont), s')"
*)
lemma test:
  assumes RedSingleCmd: "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s'" and
          Red: "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name cs str tr, cont, s') c'"
  shows "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name (c#cs) str tr, cont, s) c'"
  sorry
  

lemma red_ast_block_red_bigblock_failure_preserve:
  assumes "red_ast_bpl P ctxt c c'" and 
          "snd c = Normal ns" and
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
     Red2: "red_bigblock_multi A ([] :: ast proc_context) \<Lambda> \<Gamma> [] P (fst (fst z), snd (fst z), snd z) d'" and
     Red2StateFailure: "snd (snd d') = Failure"
    by blast  

  from \<open>red_bigblock_small P ctxt y z\<close>
  show ?case
  proof cases
    case (RedBigBlockSmallSimpleCmd c s s' name cs str tr cont)
    have "red_bigblock_multi (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) [] P (BigBlock name (c # cs) str tr, cont, s) d'"
      apply (rule test)
      using RedBigBlockSmallSimpleCmd
      apply simp
      using Red2 \<open>z = _\<close> assms
      by simp
    thus ?thesis
      using Red2StateFailure \<open>y = _\<close> assms
      by fastforce
  next
    case (RedBigBlockSmallNoSimpleCmdOneStep name str tr cont s b' cont' s')
    then show ?thesis 
      using Red2 Red2StateFailure assms
      by (metis (no_types, lifting) converse_rtranclp_into_rtranclp fstI sndI step.prems(3))
  qed           
qed

lemma init_ast_convert_ast_to_program_point_eq:
  "(init_ast ast ns) =  (fst (convert_ast_to_program_point ast), snd (convert_ast_to_program_point ast),
         Normal ns)"
  by (cases ast) auto

lemma proc_body_satisfies_spec_valid_config:
  assumes "proc_body_satisfies_spec A M \<Lambda> \<Gamma> \<Omega> pres posts ast ns" and
          "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns pres" and
          "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> ast) (init_ast ast ns) (bb, cont, state)"
        shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts bb cont state"
  using assms
  unfolding proc_body_satisfies_spec_def
  by blast


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
             ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt 
             stmt_vpr 
             \<comment>\<open>initial program point in Boogie procedure body\<close>
             (convert_ast_to_program_point proc_body_bpl)
             \<comment>\<open>output program point in Boogie procedure body is irrelevant\<close>
             \<gamma>'"  and 
    TypeInterpEq: "type_interp ctxt = (vbpl_absval_ty ty_rep)" and
    ProcTyArgsEmpty: "proc_ty_args proc_bpl = 0" and
    VarCtxtEq: "var_context ctxt = (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)" and
\<comment>\<open>TODO: I have not yet proved the following assumptions for specific Boogie programs\<close>
     WfTyRep: "wf_ty_repr_bpl ty_rep" and
     FunInterp: "fun_interp_wf (vbpl_absval_ty ty_rep) fun_decls (fun_interp ctxt)" and
     InitialStateRel: "\<And> \<omega>. is_empty_total \<omega> \<Longrightarrow> 
                       \<exists>ns ls gs.
                           ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> \<and>  
                           (state_rel_empty (state_rel_initial ctxt Pr (ty_rep :: 'a ty_repr_bpl) tr_vpr_bpl (mask_var tr_vpr_bpl))) \<omega> ns \<and>
                           state_typ_wf (vbpl_absval_ty ty_rep) [] gs (constants @ global_vars) \<and>
                           state_typ_wf (vbpl_absval_ty ty_rep) [] ls ((proc_args proc_bpl)@ (locals_bpl @ proc_rets proc_bpl)) \<and>
                           axioms_sat (vbpl_absval_ty ty_rep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"

  shows "stmt_correct_total_2 ctxt_vpr StateCons \<Lambda> stmt_vpr"
  unfolding stmt_correct_total_2_def
proof (rule allI | rule impI)+
  fix \<omega> r 
  assume "is_empty_total \<omega>" and RedStmtVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> r"
  
  let ?abs="vbpl_absval_ty ty_rep"

  note Boogie_correct_inst=Boogie_correct[where ?A="?abs"]

  obtain ns ls gs where 
    "ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>" and
  StmtRelInitialInst: 
    "(state_rel_empty (state_rel_initial ctxt Pr (ty_rep :: 'a ty_repr_bpl) tr_vpr_bpl (mask_var tr_vpr_bpl))) \<omega> ns" and
  GlobalsWf:
    "state_typ_wf (vbpl_absval_ty ty_rep) [] gs (constants @ global_vars)" and
  LocalsWf:
    "state_typ_wf (vbpl_absval_ty ty_rep) [] ls ((proc_args proc_bpl)@ (locals_bpl @ proc_rets proc_bpl))" and
  AxiomsSat:
    "axioms_sat (vbpl_absval_ty ty_rep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
    using InitialStateRel[OF \<open>is_empty_total \<omega>\<close>]
    by blast
  
  have ProcBodyBplCorrect:
      "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) ?abs [] (constants@global_vars, (proc_args proc_bpl)@(locals_bpl@(proc_rets proc_bpl))) (fun_interp ctxt) [] 
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
    show "fun_interp_wf (vbpl_absval_ty ty_rep) fun_decls (fun_interp ctxt)"
      by (rule FunInterp)
  next
    show "list_all closed [] \<and> length []  = proc_ty_args proc_bpl"
      by (simp add: ProcTyArgsEmpty)
  next
    show "state_typ_wf (vbpl_absval_ty ty_rep) [] gs (constants @ global_vars)"
      by (rule GlobalsWf)
  next 
    show "state_typ_wf (vbpl_absval_ty ty_rep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      by (rule LocalsWf)
  next
    show "axioms_sat (vbpl_absval_ty ty_rep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
      by (rule AxiomsSat)
  qed

  show "r \<noteq> RFailure"
  proof (rule ccontr)
    assume "\<not> r \<noteq> RFailure"
    hence "r = RFailure" by simp

    from stmt_rel_failure_elim[OF StmtRel StmtRelInitialInst] RedStmtVpr \<open>r = _\<close> obtain c' where
     FailureConfig: "snd c' = Failure" and 
      RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
      by blast

    let ?c'_program_point = "fst c'"
    let ?c'_bigblock = "fst ?c'_program_point"
    let ?c'_cont = "snd ?c'_program_point"

    thm red_ast_block_red_bigblock_failure_preserve[OF RedBpl FailureConfig TypeInterpEq VarCtxtEq HOL.refl]
    thm RedBpl

    obtain d' where 
      RedBigBlockMulti: "(red_bigblock_multi (vbpl_absval_ty ty_rep) ([] :: ast proc_context) (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl) (fun_interp ctxt) [] proc_body_bpl)\<^sup>*\<^sup>*
         (init_ast proc_body_bpl \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) d'" and
      "snd (snd d') = Failure"
   \<comment>\<open>TODO: need to prove that if Boogie program reduces to Failure with red_ast_bpl, then this must also be the case with
           red_bigblock (difference is that red_ast_bpl reduces simple command by simple command, while red_bigblock reduces
           all the simple commands at once)\<close>
      using red_ast_block_red_bigblock_failure_preserve[OF RedBpl FailureConfig TypeInterpEq VarCtxtEq HOL.refl]
            \<open>ns = _\<close>      
      by (auto simp: init_ast_convert_ast_to_program_point_eq)
    
    let ?d'_bigblock = "fst d'"
    let ?d'_cont = "fst (snd d')"
    let ?d'_state = "snd (snd d')"

    have "Ast.valid_configuration (vbpl_absval_ty ty_rep) (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)
         (fun_interp ctxt) [] (Ast.proc_checked_posts proc_bpl) ?d'_bigblock ?d'_cont ?d'_state"
      apply (rule proc_body_satisfies_spec_valid_config[OF ProcBodyBplCorrect] )
      using ProcPresEmpty RedBigBlockMulti
      unfolding expr_all_sat_def
      by auto
    thus False
      using \<open>snd (snd d') = Failure\<close> valid_configuration_not_failure
      by blast    
  qed
qed
      

end