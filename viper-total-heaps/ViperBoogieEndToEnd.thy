theory ViperBoogieEndToEnd
imports StmtRel
begin

text \<open>Accesses to old expressions are represented via labeled old expressions with label \<^const>\<open>old_label\<close>.\<close>  

lemma valid_configuration_not_failure:
  assumes "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts bb cont state"
  shows "state \<noteq> Failure"
  using assms
  unfolding valid_configuration_def
  by simp

type_synonym ('a,'m) proc_body_satisfies_spec_ty = 
   "'a absval_ty_fun \<Rightarrow> 'm proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"

abbreviation state_rel_well_def_same where 
  "state_rel_well_def_same ctxt Pr StateCons TyRep Tr AuxPred w ns \<equiv> 
       state_rel Pr StateCons TyRep Tr AuxPred ctxt w w ns"

text \<open>The following lemma will not hold once we track old states.\<close>

lemma state_rel_well_def_same_old_state:
  assumes "state_rel_well_def_same ctxt Pr StateCons TyRep Tr AuxPred w ns" and
          "wf_total_consistency ctxt_vpr StateCons StateCons_t"
          "\<And>l \<phi>. t l = Some \<phi> \<Longrightarrow> StateCons_t \<phi>" 
  shows "state_rel_well_def_same ctxt Pr StateCons TyRep Tr AuxPred (update_trace_total w t) ns"
  unfolding state_rel_def state_rel0_def 
  using state_rel_trace_independent
  oops
(*
  apply (intro conjI)
                 apply (insert assms[simplified state_rel_def state_rel0_def])
                 apply (solves \<open>simp\<close>)+
              apply (fastforce simp: store_rel_def)
             apply (solves \<open>simp\<close>)+
         apply (fastforce simp: heap_var_rel_def mask_var_rel_def)+
  done
*)

abbreviation red_bigblock_multi where
  "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast \<equiv> rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> ast)"

lemma magic_stays_red_bigblock:
  assumes " A,M,\<Lambda>,\<Gamma>,\<Omega>,ast \<turnstile> \<langle>y\<rangle> \<longrightarrow> z" and
         "snd (snd y) = Magic"
       shows  "snd (snd z) = Magic"
  using assms
  by (cases) auto

lemma magic_stays_red_bigblock_multi:
   assumes "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast \<gamma> \<gamma>'" and
      "snd (snd \<gamma>) = Magic"
    shows "snd (snd \<gamma>') = Magic"
  using assms 
  apply induction
   apply simp
  using magic_stays_red_bigblock
  by blast  

inductive_cases RedSimpleCmdsCons_case: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name (c#cs) str_cmd tr_cmd), cont0, Normal n_s)\<rangle> \<longrightarrow> y"

lemma red_bigblock_multi_simple_cmds_cons_failure:
  assumes 
          RedMulti: "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast \<gamma> \<gamma>'" and
               "\<gamma> = (BigBlock name cs str tr, cont, s')" and
          RedSingleCmd: "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>c, s\<rangle> \<rightarrow> s'" and
          FailureConfig:   "snd (snd \<gamma>') = Failure"
             shows "\<exists> \<gamma>'. red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name (c#cs) str tr, cont, s) \<gamma>' \<and> snd (snd \<gamma>') = Failure"
proof (cases s')
  case (Normal ns)
  hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> Normal ns"
    using RedSingleCmd
    by simp
  from this obtain ns0 where "s = Normal ns0"
    by (cases) (assumption+)

  from RedMulti have RedMulti2: "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name cs str tr, cont, Normal ns) \<gamma>'"
    using \<open>\<gamma> = _\<close> \<open>s' = _\<close>
    by blast

  from this
  obtain s'' where "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s''" and 
                   RedMultiEmptySimpleCmds: "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name [] str tr, cont, s'') \<gamma>'"
  proof -
    assume *: "(\<And>s''. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] s'' \<Longrightarrow>
            red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name [] str tr, cont, s'') \<gamma>' \<Longrightarrow> thesis)"
    show ?thesis
    proof (cases cs)
      case Nil
      thus ?thesis
        using * RedMulti2 RedCmdListNil by blast
    next
      case (Cons c' cs')

      from RedMulti2 \<open>cs = _\<close> obtain s'' where "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s''" and
                                      "red_bigblock_multi A M \<Lambda> \<Gamma> \<Omega> ast (BigBlock name [] str tr, cont, s'') \<gamma>'"
        apply (cases rule: converse_rtranclpE)
        using FailureConfig
         apply fastforce
        using RedSimpleCmdsCons_case
        by metis

      then show ?thesis 
        using * by simp
    qed
  qed

  hence RedList: "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>c#cs, s\<rangle> [\<rightarrow>] s''"
    using RedSingleCmd \<open>s' = _\<close>
    by (auto intro: RedCmdListCons)

  show ?thesis     
    apply (rule exI, rule conjI)
     apply (rule converse_rtranclp_into_rtranclp)
    apply (subst \<open>s = _\<close>)
      apply (rule RedSimpleCmds)
    using RedList RedMultiEmptySimpleCmds \<open>s = _\<close> FailureConfig
    by auto        
next
  case Failure
  hence RedListFailure: "A, M, \<Lambda>, \<Gamma>, \<Omega> \<turnstile> \<langle>c#cs, s\<rangle> [\<rightarrow>] Failure"
    using RedSingleCmd
    by (simp add: RedCmdListCons failure_red_cmd_list)
  show ?thesis
  proof (cases s)
    case (Normal ns)
    show ?thesis 
      apply (subst Normal)
      apply (rule exI, rule conjI)
       apply (rule converse_rtranclp_into_rtranclp)
        apply (rule RedSimpleCmds)
      using RedListFailure Normal
      by auto            
  next
    case Failure
    then show ?thesis 
      by auto
  next
    case Magic
    \<comment>\<open>cannot occur\<close>
    with RedListFailure show ?thesis
      using magic_stays_cmd_list by blast
  qed
next
  case Magic
  \<comment>\<open>cannot occur\<close>
  then show ?thesis 
    using magic_stays_red_bigblock_multi assms
    by (metis RedMulti sndI state.distinct(5))
qed

lemma red_ast_block_red_bigblock_failure_preserve:
  assumes "red_ast_bpl P ctxt c c'" and 
          "snd c' = Failure" and 
          "type_interp ctxt = A" and 
          "var_context ctxt = \<Lambda>" and 
          "fun_interp ctxt = \<Gamma>"
          "rtype_interp ctxt = \<Omega>"
        shows "\<exists>d'. red_bigblock_multi A ([] :: ast proc_context) \<Lambda> \<Gamma> \<Omega> P (fst (fst c), snd (fst c), snd c) d' 
                    \<and> (snd (snd d') = Failure)"
  using assms
  unfolding red_ast_bpl_def
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by auto    
next
  case (step y z)
  from this obtain d' where    
     Red2: "red_bigblock_multi A ([] :: ast proc_context) \<Lambda> \<Gamma> \<Omega> P (fst (fst z), snd (fst z), snd z) d'" and
     Red2StateFailure: "snd (snd d') = Failure"
    by blast

  from \<open>red_bigblock_small P ctxt y z\<close>
  show ?case
  proof cases
    case (RedBigBlockSmallSimpleCmd c s s' name cs str tr cont)
    from this obtain \<gamma>' where
    "red_bigblock_multi (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) (rtype_interp ctxt) P (BigBlock name (c # cs) str tr, cont, s) \<gamma>' \<and>
     (snd (snd \<gamma>')) = Failure"
      using red_bigblock_multi_simple_cmds_cons_failure RedBigBlockSmallSimpleCmd Red2
      by (metis Red2StateFailure assms(3) assms(5) fstI snd_conv step.prems(3) step.prems(5))
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
  "(init_ast ast ns) = (fst (convert_ast_to_program_point ast), snd (convert_ast_to_program_point ast),
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

text\<open>\<^const>\<open>Ast.proc_body_satisfies_spec\<close> is expressed via \<^const>\<open>red_bigblock\<close>, while \<^const>\<open>red_ast_bpl\<close> 
     is expressed via \<^const>\<open>red_bigblock_small\<close>. The following lemma bridges the gap.\<close>

lemma red_ast_bpl_proc_body_sat_spec:
  assumes RedBpl: "red_ast_bpl proc_body_ast ctxt (convert_ast_to_program_point proc_body_ast, Normal ns) c'" and
          PreconditionsSat: "expr_all_sat (type_interp ctxt) (var_context ctxt) (fun_interp ctxt) (rtype_interp ctxt) ns pres" and
          ProcBodySatSpec: "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) (type_interp ctxt) [] (var_context ctxt) (fun_interp ctxt) (rtype_interp ctxt) 
                                       pres posts proc_body_ast ns"
        shows "snd c' \<noteq> Failure"
proof (rule ccontr)
  assume "\<not> snd c' \<noteq> Failure"
  hence "snd c' = Failure"
    by simp
    
  obtain d' where 
    RedBigBlockMulti: "(red_bigblock_multi (type_interp ctxt) ([] :: ast proc_context) (var_context ctxt) (fun_interp ctxt) (rtype_interp ctxt) proc_body_ast)\<^sup>*\<^sup>*
       (init_ast proc_body_ast ns) d'" and
    "snd (snd d') = Failure"  
        using red_ast_block_red_bigblock_failure_preserve[OF RedBpl \<open>snd c' = _\<close>] init_ast_convert_ast_to_program_point_eq
        by (metis fstI r_into_rtranclp sndI)
      
  let ?d'_bigblock = "fst d'"
  let ?d'_cont = "fst (snd d')"
  let ?d'_state = "snd (snd d')"

  have "Ast.valid_configuration (type_interp ctxt) (var_context ctxt)
       (fun_interp ctxt) (rtype_interp ctxt) posts ?d'_bigblock ?d'_cont ?d'_state"
    apply (rule proc_body_satisfies_spec_valid_config[OF ProcBodySatSpec] )
    using PreconditionsSat RedBigBlockMulti
    unfolding expr_all_sat_def
    by auto
  thus False
    using \<open>snd (snd d') = Failure\<close> valid_configuration_not_failure
    by blast 
qed

definition post_framing_rel_aux
  where "post_framing_rel_aux ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl R0 \<gamma>Pre \<omega>1 ns \<equiv>
    (\<exists>ns' \<gamma>Framing0 \<gamma>Framing1 RPostFrame R'. \<comment>\<open>output Boogie program point and output relation are irrelevant\<close>
                                  red_ast_bpl proc_body_bpl ctxt (\<gamma>Pre, Normal ns) (\<gamma>Framing0, Normal ns') \<and> RPostFrame \<omega>1 ns' \<and>
                                  \<comment>\<open>expressed via \<^const>\<open>stmt_rel\<close> because \<^const>\<open>inhale_rel\<close> does not allow arbitrary input and output relations\<close>
                                  stmt_rel RPostFrame R' ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Inhale (method_decl.post mdecl)) \<gamma>Framing0 \<gamma>Framing1)"

definition post_framing_rel
  where "post_framing_rel ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl R0 \<gamma>Pre \<equiv>
           (\<forall>\<omega>0 \<omega>1 ns. R0 \<omega>0 ns \<longrightarrow> get_store_total \<omega>0 = get_store_total \<omega>1 \<longrightarrow> 
                               \<comment>\<open>One could omit emptiness and instead use a separate monotonicity theorem
                                  for inhale. We do this in a separate step.\<close> 
                               is_empty_total_full \<omega>1 \<longrightarrow>                                                             
                               total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>1) \<longrightarrow>
                               post_framing_rel_aux ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl R0 \<gamma>Pre \<omega>1 ns
                   )"

definition method_rel
  where "method_rel R0 R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl \<gamma>0 \<equiv> 
          (\<exists> \<gamma>Pre. stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Inhale (method_decl.pre mdecl)) \<gamma>0 \<gamma>Pre \<and>
                   post_framing_rel ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl R1 \<gamma>Pre \<and>
                   (  \<comment>\<open>The correctness of the spec must be taken into account in this left-hand side here and 
                         not in a previous conjunct, since the previous conjunct is required to justify the 
                         correctness of the spec.
                         We need this left-hand side, because the Boogie encoding may rely on the correctness
                         of the specs.\<close> 
                      method_decl.body mdecl \<noteq> None \<longrightarrow> \<comment>\<open>correctness of body is relevant only if the method has a body\<close>
                      vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr) \<longrightarrow> 
                      (\<exists>\<gamma>Body \<gamma>Post R1'. \<comment>\<open>output Boogie program point and output relation are irrelevant\<close>
                         stmt_rel R1 R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (the (method_decl.body mdecl)) \<gamma>Pre \<gamma>Body \<and>    
                          \<comment>\<open>because framedness of the postcondition was checked above, we may use it here.
                             TODO: could make sense to abstract \<^const>\<open>framing_exh\<close> away via a parameter\<close>                   
                         stmt_rel (\<lambda> \<omega> ns. R1 \<omega> ns \<and> framing_exh ctxt_vpr StateCons (method_decl.post mdecl) \<omega> \<omega>) 
                                  R1' ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Exhale (method_decl.post mdecl)) \<gamma>Body \<gamma>Post
                      )
                   )
          )"

lemma post_framing_rel_aux:
  assumes WfTyRep: "wf_ty_repr_bpl TyRep" 
      and WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and TypeInterp: "type_interp ctxt = vbpl_absval_ty TyRep"
      and "domain_type TyRep = absval_interp_total ctxt_vpr"
      and "Pr = program_total ctxt_vpr"
      and LookupDeclHeap: "lookup_var_decl (var_context ctxt) hvar' = Some (TConSingle (THeapId TyRep), None)"
      and LookupTyMask: "lookup_var_ty (var_context ctxt) mvar' = Some (TConSingle (TMaskId TyRep))"
      and ZeroMaskConst: "const_repr Tr CZeroMask = zero_mask_var"
      and Disj: "{hvar', mvar'} \<inter> ({heap_var Tr, heap_var_def Tr} \<union>
                              {mask_var Tr, mask_var_def Tr} \<union>
                              (ran (var_translation Tr)) \<union>
                              (ran (field_translation Tr)) \<union>
                              (range (const_repr Tr)) \<union>
                              dom AuxPred) = {}" (is "?A \<inter> ?B = {}")
      and "hvar' \<noteq> mvar'"
      and PropagateBpl: "red_ast_bpl_rel (state_rel_well_def_same ctxt Pr StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred) 
                                         (state_rel_well_def_same ctxt Pr StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred) proc_body_bpl ctxt 
                                         \<gamma>Pre 
                                         (BigBlock name (Havoc hvar' # Assign mvar' (Var zero_mask_var) # cs) str tr, cont)"
      and PostInhRel: 
             "stmt_rel (state_rel_well_def_same ctxt Pr StateCons TyRep (Tr\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) AuxPred)
                       R' ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt
                       (Inhale (method_decl.post mdecl))
                       (BigBlock name cs str tr, cont)
                       \<gamma>'" 
shows "post_framing_rel ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl 
                        (state_rel_well_def_same ctxt Pr StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)
                        \<gamma>Pre"
  unfolding post_framing_rel_def
proof (rule allI | rule impI)+
  fix \<omega>0 \<omega>1 :: "'a full_total_state "
  fix ns
  assume "state_rel_well_def_same ctxt Pr StateCons TyRep Tr AuxPred \<omega>0 ns" (is "?R Tr \<omega>0 ns") and
         StoreSame: "get_store_total \<omega>0 = get_store_total \<omega>1" and
         HeapWellTy:  "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>1)" and
         IsEmpty: "is_empty_total_full \<omega>1"

  with PropagateBpl obtain ns1 where 
    RedBpl1: "red_ast_bpl proc_body_bpl ctxt 
                              (\<gamma>Pre, Normal ns)
                              ((BigBlock name (Havoc hvar' # Assign mvar' (Var zero_mask_var) # cs) str tr, cont), Normal ns1)" and
    R1: "?R Tr \<omega>0 ns1"
    unfolding red_ast_bpl_rel_def
    by blast    

  have *: "\<And>\<omega>0 \<omega> ns hvar' hvar. state_rel Pr StateCons TyRep ((disable_consistent_state_rel_opt Tr)\<lparr>heap_var := hvar, heap_var_def := hvar'\<rparr>) AuxPred ctxt \<omega>0 \<omega> ns \<Longrightarrow> 
                    red_expr_bpl ctxt (Var zero_mask_var) ns (AbsV (AMask zero_mask_bpl))"
    apply (rule RedVar)
    using boogie_const_rel_lookup[OF state_rel_boogie_const_rel, where ?const = CZeroMask]
          ZeroMaskConst
    by fastforce

  have "StateCons \<omega>1"
    using WfConsistency[simplified wf_total_consistency_def] IsEmpty
    by blast

  from post_framing_propagate_aux[OF R1 WfTyRep TypeInterp StoreSame _ \<open>StateCons \<omega>1\<close> _ LookupDeclHeap LookupTyMask * zero_mask_rel_2 Disj \<open>hvar' \<noteq> _\<close>]
       HeapWellTy \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
       IsEmpty obtain ns2 where
    "red_ast_bpl proc_body_bpl ctxt
        ((BigBlock name (cmd.Havoc hvar' # Assign mvar' (expr.Var zero_mask_var) # cs) str tr, cont),
         Normal ns1)
        ((BigBlock name cs str tr, cont), Normal ns2)" and
    R2: "?R (Tr\<lparr>heap_var := hvar', mask_var := mvar', heap_var_def := hvar', mask_var_def := mvar'\<rparr>) \<omega>1 ns2"             
    using is_empty_total_wf_mask[OF IsEmpty] 
    by force
    
  with RedBpl1 have RedBpl2: "red_ast_bpl proc_body_bpl ctxt (\<gamma>Pre, Normal ns) ((BigBlock name cs str tr, cont), Normal ns2)"
    using red_ast_bpl_transitive
    by fast
   
  show "post_framing_rel_aux ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl (?R Tr) \<gamma>Pre \<omega>1 ns"
    unfolding post_framing_rel_aux_def
    apply ((rule exI)+, intro conjI)
      apply (rule RedBpl2)
     apply (rule R2)
    apply (rule PostInhRel)
    done
qed

lemma post_framing_rel_framing_trivial:
  assumes "method_decl.post mdecl = (Atomic (Pure (ELit (ViperLang.LBool True))))"
  shows "post_framing_rel ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl R \<gamma>Pre"
  unfolding post_framing_rel_def post_framing_rel_aux_def
  by (metis assms inhale_rel_true inhale_stmt_rel_no_inv red_ast_bpl_refl)

definition vpr_method_correct_total_partial :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_correct_total_partial ctxt StateCons mdecl \<equiv>
         vpr_method_correct_total_aux ctxt StateCons mdecl 
          (\<lambda>ctxt R mdecl \<omega>pre \<omega>.
                vpr_postcondition_framed ctxt R (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>) \<and>
                (method_decl.body mdecl \<noteq> None \<longrightarrow> 
                 vpr_all_method_spec_correct_total ctxt StateCons (program_total ctxt) \<longrightarrow>
                 vpr_method_body_correct ctxt R mdecl \<omega>pre)
          )
       "

lemma vpr_method_correct_total_from_partial:
  assumes "methods (program_total ctxt) m = Some mdecl"
      and "\<And> m' mdecl' . methods (program_total ctxt) m' = Some mdecl' \<Longrightarrow> vpr_method_correct_total_partial ctxt StateCons mdecl'"
    shows "vpr_method_correct_total ctxt StateCons mdecl"
proof -
  have SpecsCorrect: "vpr_all_method_spec_correct_total ctxt StateCons (program_total ctxt)"
    unfolding vpr_all_method_spec_correct_total_def
  proof (rule allI | rule impI)+
    fix m mdecl
    assume "methods (program_total ctxt) m = Some mdecl"
    hence "vpr_method_correct_total_partial ctxt StateCons mdecl"
      using assms
      by blast    
    thus "vpr_method_spec_correct_total ctxt StateCons mdecl"
      unfolding vpr_method_correct_total_partial_def vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
      by blast
  qed

  have "vpr_method_correct_total_partial ctxt StateCons mdecl"
    using assms
    by auto

  thus "vpr_method_correct_total ctxt StateCons mdecl"
    using SpecsCorrect
    unfolding vpr_method_correct_total_partial_def vpr_method_correct_total_def vpr_method_correct_total_aux_def
    by blast
qed

subsection \<open>Main helper lemma for final theorem\<close>

lemma end_to_end_vpr_method_correct_partial:
  assumes 
          \<comment>\<open>The Boogie procedure is correct. Note that we need to explicitly provide the types such that
             we can then instantiate the Boogie type interpretation with \<^term>\<open>vbpl_absval_ty TyRep\<close>.\<close>
          Boogie_correct: "proc_is_correct (vbpl_absval_ty (TyRep :: 'a ty_repr_bpl)) fun_decls constants unique_consts global_vars axioms (proc_bpl :: ast procedure) 
                  (Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty))"
      and ConsistencyDownwardMono: "mono_prop_downward_ord StateCons"
      and WfTyRep: "wf_ty_repr_bpl TyRep"
      and WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"

\<comment>\<open> Viper properties\<close>
      and DomainType: "domain_type TyRep = absval_interp_total ctxt_vpr"
      and ProgMethod: "methods (program_total ctxt_vpr) mname = Some mdecl"
      and VprMethodBody: "method_decl.body mdecl \<noteq> None \<Longrightarrow> method_decl.body mdecl = Some body_vpr"
      and VprNoPermSupportedSpec: "no_perm_assertion (method_decl.pre mdecl) \<and> supported_assertion (method_decl.pre mdecl) \<and>
                                   no_perm_assertion (method_decl.post mdecl) \<and> supported_assertion (method_decl.post mdecl)"
      and OnlyArgsInPre: "\<And> x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow> x < length (method_decl.args mdecl)"
      and ArgsUnmodified: "method_decl.body mdecl \<noteq> None \<Longrightarrow> 
                                  (\<And>x. x < length (method_decl.args mdecl) \<Longrightarrow> x \<notin> modif body_vpr)"
      and "\<Lambda> = nth_option (method_decl.args mdecl @ rets mdecl)"      

\<comment>\<open>Boogie properties\<close>
      and FunInterp: "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      and TypeInterpEq: "type_interp ctxt = vbpl_absval_ty TyRep"  
      and "rtype_interp ctxt = []"
      and VarCtxtEq: "var_context ctxt = (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
          \<comment>\<open>The Viper encoding does not use Boogie procedure preconditions\<close>
      and ProcPresEmpty: "proc_pres proc_bpl = []"
      and ProcTyArgsEmpty: "proc_ty_args proc_bpl = 0"
      and ProcBodySome: "proc_body proc_bpl = Some (locals_bpl, proc_body_bpl)"

\<comment>\<open>method rel\<close>
      and VprMethodRel: "method_rel 
               (state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred))
               (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)
               ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl               
               (convert_ast_to_program_point proc_body_bpl)" 
          (is "method_rel ?R0 ?R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl ?\<gamma>0")
      and ConsistencyEnabled: "consistent_state_rel_opt (state_rel_opt Tr)"

\<comment>\<open>construct initial state\<close>
      and InitialStateRel: "\<And> \<omega>.  
                       vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total \<omega>) \<Longrightarrow>
                       total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>) \<Longrightarrow>
                       is_empty_total_full \<omega> \<Longrightarrow>
                       \<exists>ns ls gs.
                           ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> \<and>  
                           \<comment>\<open>well-typedness of Boogie state follows from state relation\<close>
                           (state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)) \<omega> ns \<and>
                           unique_constants_distinct gs unique_consts \<and>
                           axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
shows "vpr_method_correct_total_partial ctxt_vpr StateCons mdecl"
  unfolding vpr_method_correct_total_partial_def vpr_method_correct_total_aux_def
proof (rule allI | rule impI)+
  text \<open>Proof setup: deconstruct relation statement\<close>

  let ?R1Post = "\<lambda>\<omega> ns. ?R1 \<omega> ns \<and> framing_exh ctxt_vpr StateCons (method_decl.post mdecl) \<omega> \<omega>"

  from VprMethodRel obtain \<gamma>Pre \<gamma>Body \<gamma>Post Rend where 
    PreInhRel: "stmt_rel ?R0 ?R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Inhale (method_decl.pre mdecl)) ?\<gamma>0 \<gamma>Pre" and
    PostFramingRel: "post_framing_rel ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt mdecl ?R1 \<gamma>Pre" and
    BodyRel: "method_decl.body mdecl \<noteq> None \<Longrightarrow>
              vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr) \<Longrightarrow>
              stmt_rel ?R1 ?R1 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt body_vpr \<gamma>Pre \<gamma>Body" and
    PostExhRel: "method_decl.body mdecl \<noteq> None \<Longrightarrow>
              vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr) \<Longrightarrow>
              stmt_rel ?R1Post Rend ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Exhale (method_decl.post mdecl)) \<gamma>Body \<gamma>Post"
    unfolding method_rel_def
    using VprMethodBody
    by fastforce   

  text \<open>start actual proof\<close>

  let ?\<Lambda> = "(nth_option (method_decl.args mdecl @ rets mdecl))"
  fix \<omega> rpre
  assume 
         StoreWellTy: "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total \<omega>)" and
         HeapWellTy: "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>)" and
         "is_empty_total_full \<omega>" and
         RedInhPre: "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) \<omega> rpre"
  
  let ?abs = "vbpl_absval_ty TyRep"

  note Boogie_correct_inst=Boogie_correct

  obtain ns ls gs where 
    "ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>" and
  StateRelInitialInst: 
    "state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred) \<omega> ns" and
  UniqueConstants:
    "unique_constants_distinct gs unique_consts" and
  AxiomsSat:
    "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
    using InitialStateRel[OF StoreWellTy HeapWellTy \<open>is_empty_total_full \<omega>\<close>]
    by blast

  from StateRelInitialInst have StateRel: "state_rel (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt \<omega> \<omega> ns"
    by (simp add: state_rel_empty_def)
    
  have
    GlobalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)" and
    LocalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] ls ((proc_args proc_bpl)@ (locals_bpl @ proc_rets proc_bpl))"
    using state_rel_state_well_typed[OF StateRel] \<open>ns = _\<close> VarCtxtEq TypeInterpEq
    unfolding state_rel_empty_def state_well_typed_def 
    by auto          
  
  have ProcBodyBplCorrect:
      "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) ?abs [] (constants@global_vars, (proc_args proc_bpl)@(locals_bpl@(proc_rets proc_bpl))) (fun_interp ctxt) [] 
                                       (proc_all_pres proc_bpl) (proc_checked_posts proc_bpl) proc_body_bpl
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
  proof (rule proc_is_correct_elim[OF Boogie_correct_inst ProcBodySome])
    show "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_vbpl_val TyRep v = t)"
      by (simp add: closed_types_inhabited)
  next
    show "\<forall>v. closed (type_of_vbpl_val TyRep v)"
    proof (rule allI)
      fix v
      show "closed (type_of_vbpl_val TyRep v)"
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
    show "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      by (rule FunInterp)
  next
    show "list_all closed [] \<and> length []  = proc_ty_args proc_bpl"
      by (simp add: ProcTyArgsEmpty)
  next
    show "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)"
      by (rule GlobalsWf)
  next 
    show "state_typ_wf (vbpl_absval_ty TyRep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      by (rule LocalsWf)
  next
    show "unique_constants_distinct gs unique_consts"
      by (rule UniqueConstants)
  next
    show "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
      by (rule AxiomsSat)
  qed

  show "rpre \<noteq> RFailure \<and>
       (\<forall>\<omega>pre.
           rpre = RNormal \<omega>pre \<longrightarrow>
           vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>) \<and> 
           (method_decl.body mdecl \<noteq> None \<longrightarrow> vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr) \<longrightarrow>
            vpr_method_body_correct ctxt_vpr StateCons mdecl \<omega>pre)
        )"
        (is "?Goal1 \<and> ?Goal2")
  proof (rule conjI)

    show "rpre \<noteq> RFailure"
    proof (rule ccontr)
      assume "\<not> rpre \<noteq> RFailure"
      hence "rpre = RFailure" by simp
      with stmt_rel_failure_elim[OF PreInhRel StateRelInitialInst] RedInhPre
       obtain c' where
        FailureConfig: "snd c' = Failure" and 
        RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
        using RedInhale
        by blast  

      have "snd c' \<noteq> Failure"
        using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
              ProcPresEmpty ProcBodyBplCorrect
        unfolding expr_all_sat_def
        by (simp add: \<open>var_context _ = _\<close> \<open>type_interp _ = _\<close> \<open>rtype_interp _ =_\<close> \<open>ns = _\<close>)

      thus False
        using \<open>snd c' = Failure\<close>
        by simp 
    qed
  next
    show ?Goal2
    proof (rule allI | rule impI | rule conjI)+
      fix \<omega>pre
      assume "rpre = RNormal \<omega>pre"

      have StoreSame: "get_store_total \<omega>pre = get_store_total \<omega>"
        using RedInhPre \<open>rpre = RNormal \<omega>pre\<close> inhale_only_changes_mask by blast

      from stmt_rel_normal_elim[OF PreInhRel StateRelInitialInst] RedInhPre
          obtain nspre where
            RedPreBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) (\<gamma>Pre, Normal nspre)" and
            Rpre: "state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons TyRep Tr AuxPred \<omega>pre nspre" (is "?R \<omega>pre nspre")
            using RedInhale \<open>rpre = RNormal \<omega>pre\<close>
            by blast

      show PostFramed: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full \<omega>pre) (get_store_total \<omega>)"
        unfolding vpr_postcondition_framed_def assertion_framing_state_def
      proof (rule allI | rule impI)+
        fix mh trace res
        let ?\<omega>Post = "\<lparr>get_store_total = get_store_total \<omega>, get_trace_total = trace, get_total_full = mh\<rparr>"
        let ?\<omega>PostEmpty = "empty_full_total_state (get_store_total \<omega>) trace (get_hh_total mh) (get_hp_total mh)"
        assume 
              "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total mh)"
          and TraceOldState: "trace old_label = Some (get_total_full \<omega>pre)"
          and RedInhPost:"red_inhale ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>Post res"

        hence HeapWellTy: "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full ?\<omega>PostEmpty)"
          by (simp add: empty_full_total_state_def)
        
        from PostFramingRel obtain ns' \<gamma>Framing0 \<gamma>Framing1 RPostFrameStart RPostFrameEnd where 
          RedPreToFramingBpl: "red_ast_bpl proc_body_bpl ctxt (\<gamma>Pre, Normal nspre) (\<gamma>Framing0, Normal ns')" and
          "RPostFrameStart ?\<omega>PostEmpty ns'" and
          PostFramingInhRel: "stmt_rel RPostFrameStart RPostFrameEnd ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt (Inhale (method_decl.post mdecl)) \<gamma>Framing0 \<gamma>Framing1"
          using Rpre StoreSame is_empty_empty_full_total_state  HeapWellTy
          unfolding post_framing_rel_def post_framing_rel_aux_def
          by (metis get_store_empty_full_total_state)

        show "res \<noteq> RFailure"
        proof (rule ccontr)
          assume "\<not> res \<noteq> RFailure"
          hence "res = RFailure"
            by simp

          have "?\<omega>PostEmpty \<le> ?\<omega>Post"
            apply (rule is_empty_total_full_less_eq[OF is_empty_empty_full_total_state])
            by (simp_all add: empty_full_total_state_def)

          with inhale_no_perm_downwards_mono(3) ConsistencyDownwardMono  RedInhPost 
          have "red_inhale ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>PostEmpty RFailure"
            using is_empty_empty_full_total_state \<open>res = _\<close>  VprNoPermSupportedSpec supported_assertion_no_unfolding
            by blast
            
          with stmt_rel_failure_elim[OF PostFramingInhRel \<open>RPostFrameStart _ _\<close>]
          obtain c' where "red_ast_bpl proc_body_bpl ctxt (\<gamma>Framing0, Normal ns') c'" and 
                          "snd c' = Failure"
            using RedInhale \<open>\<Lambda> = _\<close>
            by blast
            
          with RedPreBpl RedPreToFramingBpl
          have RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
            using red_ast_bpl_transitive
            by blast

          have "snd c' \<noteq> Failure"
            using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
              ProcPresEmpty ProcBodyBplCorrect
            unfolding expr_all_sat_def
            by (simp add: \<open>var_context _ = _\<close> \<open>type_interp _ = _\<close> \<open>rtype_interp _ =_\<close> \<open>ns = _\<close>)
          thus False 
            by (simp add: \<open>snd c' = Failure\<close>)
        qed
      qed

      show "method_decl.body mdecl \<noteq> None \<longrightarrow> vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr) \<longrightarrow> vpr_method_body_correct ctxt_vpr StateCons mdecl \<omega>pre"
        unfolding vpr_method_body_correct_def
      proof (rule allI | rule impI | rule conjI)+
        let ?\<omega>pre' = "(update_trace_total \<omega>pre [old_label \<mapsto> get_total_full \<omega>pre])"
        let ?\<Lambda> = "(nth_option (method_decl.args mdecl @ rets mdecl))"
        let ?mbody = "(the (method_decl.body mdecl))"
        fix rpost
        assume "method_decl.body mdecl \<noteq> None"
           and SpecsCorrect: "vpr_all_method_spec_correct_total ctxt_vpr StateCons (program_total ctxt_vpr)"   
           and RedBodyVpr: "red_stmt_total ctxt_vpr StateCons ?\<Lambda> 
                               (Seq ?mbody (Exhale (method_decl.post mdecl)))
                               ?\<omega>pre' rpost"

        with VprMethodBody have VprMethodBodySome: "method_decl.body mdecl = Some body_vpr"
          by fast

        \<comment>\<open>the following will have to be adjusted once we track old states\<close>
        have Rpre_old_upd:"?R (update_trace_total \<omega>pre ([old_label \<mapsto> get_total_full \<omega>pre])) nspre"
        proof -
          have *: "consistent_state_rel_opt (state_rel_opt Tr) \<Longrightarrow> StateCons_t (get_total_full \<omega>pre)"
            using WfConsistency state_rel_consistent[OF Rpre]
            unfolding wf_total_consistency_def
            by blast
          show ?thesis
            apply (rule state_rel_trace_independent[OF WfConsistency])
            using *
             apply (simp split: if_split_asm)
            using Rpre
            by blast
        qed
 
        show "rpost \<noteq> RFailure"
        proof (rule ccontr)
          assume "\<not> rpost \<noteq> RFailure"
          hence "rpost = RFailure" by simp
          with RedBodyVpr 
          have RedCasesVpr: "red_stmt_total ctxt_vpr StateCons ?\<Lambda> ?mbody ?\<omega>pre' RFailure \<or>
               (\<exists>\<omega>body. red_stmt_total ctxt_vpr StateCons ?\<Lambda> ?mbody ?\<omega>pre' (RNormal \<omega>body) \<and>
                        red_stmt_total ctxt_vpr StateCons ?\<Lambda> (Exhale (method_decl.post mdecl)) \<omega>body RFailure)"
            (is "?Case1 \<or> ?Case2")
            by (auto elim: red_stmt_total_inversion_thms)
          
          show False
          proof (rule disjE[OF RedCasesVpr])
            assume ?Case1
   
            with stmt_rel_failure_elim[OF BodyRel Rpre_old_upd] RedBodyVpr obtain c' 
              where "snd c' = Failure" and "red_ast_bpl proc_body_bpl ctxt (\<gamma>Pre, Normal nspre) c'"
              using \<open>\<Lambda> = _\<close> VprMethodBodySome SpecsCorrect
              by fastforce
  
            hence RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
              using RedPreBpl red_ast_bpl_transitive
              by blast
  
            have "snd c' \<noteq> Failure"
              using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
                ProcPresEmpty ProcBodyBplCorrect
              unfolding expr_all_sat_def
              by (simp add: \<open>var_context _ = _\<close> \<open>type_interp _ = _\<close> \<open>rtype_interp _ =_\<close> \<open>ns = _\<close>)
            thus False 
              by (simp add: \<open>snd c' = Failure\<close>)
          next
            assume ?Case2
            from this obtain \<omega>body where
              RedBodyVpr: "red_stmt_total ctxt_vpr StateCons ?\<Lambda> ?mbody ?\<omega>pre' (RNormal \<omega>body)" and
              RedExhPost: "red_exhale ctxt_vpr StateCons \<omega>body (method_decl.post mdecl) \<omega>body RFailure"
              by (auto elim: red_stmt_total_inversion_thms)

            from stmt_rel_normal_elim[OF BodyRel Rpre_old_upd] RedBodyVpr obtain nsbody
              where 
               RedBodyBpl: "red_ast_bpl proc_body_bpl ctxt (\<gamma>Pre, Normal nspre) (\<gamma>Body, Normal nsbody)" and
               Rbody: "state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons TyRep Tr AuxPred \<omega>body nsbody"
              using \<open>\<Lambda> = _\<close> VprMethodBodySome SpecsCorrect
              by auto

            have FramingExhPost: "framing_exh ctxt_vpr StateCons (method_decl.post mdecl) \<omega>body \<omega>body"
            proof (rule framing_exhI_state_rel[OF Rbody ConsistencyEnabled])

              from SpecsCorrect and ProgMethod 
              have SpecCorrectMdecl: "vpr_method_spec_correct_total ctxt_vpr StateCons mdecl"
                unfolding vpr_all_method_spec_correct_total_def
                by blast

              let ?\<omega>_store_body = "(\<omega> \<lparr> get_store_total := get_store_total \<omega>body \<rparr>)"
              have StoresAgreeOnArgs: "\<And> x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow> get_store_total \<omega> x = get_store_total ?\<omega>_store_body x" (is "\<And>x. ?A x \<Longrightarrow> ?B x")
                  \<comment>\<open>use that body does not modify arguments\<close>
              proof -
                fix x
                assume "?A x"
                hence "x < length (method_decl.args mdecl)"
                  using OnlyArgsInPre
                  by blast
                hence "x \<notin> modif body_vpr"
                  using ArgsUnmodified VprMethodBodySome
                  by simp
                hence "get_store_total \<omega> x = get_store_total \<omega>body x"
                  using red_stmt_preserves_unmodified_variables VprMethodBodySome RedBodyVpr \<open>get_store_total \<omega>pre = get_store_total \<omega>\<close>
                  by fastforce
                thus "?B x"
                  by simp           
              qed                

              with OnlyArgsInPre VprNoPermSupportedSpec RedInhPre \<open>rpre = RNormal \<omega>pre\<close>
              have RedInhStoreBody: "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) 
                        ?\<omega>_store_body (RNormal (\<omega>pre \<lparr> get_store_total := get_store_total \<omega>body \<rparr>))"
                using red_pure_exp_inhale_store_same_on_free_var(3)[OF RedInhPre _ StoresAgreeOnArgs] WfConsistency
                by simp
                
              hence 
               PostFramedStoreBody: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full (\<omega>pre\<lparr>get_store_total := get_store_total \<omega>body\<rparr>))
                                                                                     (get_store_total ?\<omega>_store_body)"            
              proof (rule vpr_method_correct_total_aux_normalD[OF SpecCorrectMdecl[simplified vpr_method_spec_correct_total_def]])
                show "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total ?\<omega>_store_body)"
                  apply simp
                  using RedBodyVpr \<open>get_store_total \<omega>pre = get_store_total \<omega>\<close> red_stmt_preserves_well_typed_store StoreWellTy
                  by (metis update_trace_total_store_same)
              next
                show "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full (\<omega>\<lparr>get_store_total := get_store_total \<omega>body\<rparr>))"
                  using HeapWellTy 
                  by simp
              next
                show "is_empty_total_full (\<omega>\<lparr>get_store_total := get_store_total \<omega>body\<rparr>)"
                  using \<open>is_empty_total_full \<omega>\<close>
                  unfolding is_empty_total_full_def
                  by simp
              qed

              let ?\<phi> = "get_total_full \<omega>body \<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr>"

              show "assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) (update_m_total_full \<omega>body zero_mask zero_mask)"
              proof (rule vpr_postcondition_framed_assertion_framing_state[OF PostFramedStoreBody])
                show "update_m_total_full \<omega>body zero_mask zero_mask = 
                     \<lparr>get_store_total = get_store_total (\<omega>\<lparr>get_store_total := get_store_total \<omega>body\<rparr>), get_trace_total = get_trace_total \<omega>body, 
                                                           get_total_full = ?\<phi>\<rparr>"
                  by auto
              next
                show "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total ?\<phi>)"
                  using state_rel_heap_var_rel[OF Rbody] DomainType
                  unfolding heap_var_rel_def
                  by simp
              next
                show "valid_heap_mask (get_mh_total ?\<phi>)"
                  using wf_zero_mask by auto                                    
              next
                show "get_trace_total \<omega>body old_label = Some (get_total_full (\<omega>pre\<lparr>get_store_total := get_store_total \<omega>body\<rparr>))"
                  using red_stmt_preserves_labels RedBodyVpr \<comment>\<open>Use that body does not overwrite the old label\<close>
                  by fastforce
              qed
            qed

            with stmt_rel_failure_elim[OF PostExhRel]
            obtain c' where "snd c' = Failure" and 
                            "red_ast_bpl proc_body_bpl ctxt (\<gamma>Body, Normal nsbody) c'"
              using Rbody VprMethodBodySome FramingExhPost RedExhPost RedExhaleFailure SpecsCorrect 
              by blast

            hence RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'"
              using RedPreBpl RedBodyBpl red_ast_bpl_transitive
              by blast

            have "snd c' \<noteq> Failure"
            using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
              ProcPresEmpty ProcBodyBplCorrect
            unfolding expr_all_sat_def
            by (simp add: \<open>var_context _ = _\<close> \<open>type_interp _ = _\<close> \<open>rtype_interp _ =_\<close> \<open>ns = _\<close>)
            thus False 
              by (simp add: \<open>snd c' = Failure\<close>)
          qed
        qed
      qed
    qed
  qed
qed

  subsection \<open>General setup for constructing well-typed states\<close>

fun named_state_var_context :: "'a absval_ty_fun \<Rightarrow> vdecls \<Rightarrow> 'a named_state"
  where "named_state_var_context A vs x = 
             (if x \<in> dom (lookup_vdecls_ty vs) then
               Some (SOME v. \<exists>t. lookup_vdecls_ty vs x = Some t \<and> type_of_val A v = t)
              else 
               None)"

lemma named_state_var_context_dom: "dom (named_state_var_context A vs) = dom (lookup_vdecls_ty vs)" (is "dom (?f vs) = dom (?g vs)")  
proof
  show "dom (?f vs) \<subseteq> dom (?g vs)"
  proof
    fix x
    assume "x \<in> dom (?f vs)"
    from this obtain arg where "?f vs x = Some arg"
      by fast
    thus "x \<in> dom (?g vs)"
      apply simp
      by (meson option.distinct(1))
  qed
qed auto        

fun extend_named_state_var_context :: "'a absval_ty_fun \<Rightarrow> vdecls \<Rightarrow> 'a named_state \<Rightarrow> 'a named_state"
  where "extend_named_state_var_context A vs ns = 
           named_state_var_context A vs ++ ns"

lemma extend_named_state_var_context_dom: 
  "dom (extend_named_state_var_context A vs ns) = dom ns \<union> dom (lookup_vdecls_ty vs)" 
  by (simp add: named_state_var_context_dom)

lemma named_state_var_context_state_typ_wf:  
  assumes "list_all (closed \<circ> (fst \<circ> snd)) vs" and
         Inhabited: "\<And>t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t"
  shows "state_typ_wf A [] (named_state_var_context A vs) vs"
  unfolding state_typ_wf_def
proof (rule allI | rule impI)+
  fix x t
  assume *: "lookup_vdecls_ty vs x = Some t"

  hence "(named_state_var_context A vs x) = Some (SOME v. \<exists>t. lookup_vdecls_ty vs x = Some t \<and> type_of_val A v = t)"
     (is "_ = Some ?v")
    by force

  from * have "closed t"
    using assms(1)
    by (metis comp_apply fst_eqD fun.map_comp lookup_vdecls_ty_map_of map_of_list_all)

  hence "type_of_val A ?v = t"
    using Inhabited *
    by (metis (mono_tags, lifting) exE_some option.inject)
  thus "map_option (type_of_val A) (named_state_var_context A vs x) = Some (instantiate [] t)"
    using *
    by auto
qed

lemma extend_named_state_var_context_state_typ_wf:
  assumes Closed: "list_all (closed \<circ> (fst \<circ> snd)) vs" and
         Inhabited: "\<And>t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
         StateWellTy: "\<And>x t v. lookup_vdecls_ty vs x = Some t \<Longrightarrow> ns x = Some v \<Longrightarrow> 
                      type_of_val A v = t"         
  shows "state_typ_wf A [] (extend_named_state_var_context A vs ns) vs"
  unfolding state_typ_wf_def
proof (rule allI | rule impI)+
  fix x t
  assume "lookup_vdecls_ty vs x = Some t"  

  show "map_option (type_of_val A) (extend_named_state_var_context A vs ns x) = Some (instantiate [] t)"
    
  proof (cases "x \<in> dom ns")
    case True
    thus ?thesis 
      using StateWellTy \<open>lookup_vdecls_ty vs x = Some t\<close> by auto      
  next
    case False
    then show ?thesis 
      using named_state_var_context_state_typ_wf[OF Closed Inhabited]
      by (metis \<open>lookup_vdecls_ty vs x = Some t\<close> extend_named_state_var_context.simps map_add_dom_app_simps(3) state_typ_wf_def)
  qed
qed

subsection \<open>Constructing initial state\<close>

subsubsection \<open>Global state\<close>

fun initial_global_state_aux :: "program \<Rightarrow> tr_vpr_bpl \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) named_state"
  where "initial_global_state_aux Pr Tr \<omega> x = 
           (if x = heap_var Tr then
              Some (AbsV (AHeap (construct_bpl_heap_from_vpr_heap Pr (field_translation Tr) (get_hh_total_full \<omega>))))
           else 
             if x = mask_var Tr then
                Some (AbsV (AMask (\<lambda>_. 0)))
             else 
                if x \<in> range (const_repr Tr) then
                  Some (boogie_const_val (SOME c. const_repr Tr c = x))
                else
                  (if (\<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some x)  then
                    Some (AbsV (AField (NormalField x (SOME t. \<exists>f_vpr. field_translation Tr f_vpr = Some x \<and> 
                                                                       declared_fields Pr f_vpr = Some t))))
                   else None)             
           )"

lemma dom_initial_global_state_aux: "dom (initial_global_state_aux Pr Tr \<omega>) \<subseteq>
  {heap_var Tr, mask_var Tr} \<union> {f_bpl. \<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some f_bpl}  \<union> range (const_repr Tr)"
  unfolding dom_def ran_def
  by auto

lemma initial_global_state_aux_heap: 
  "initial_global_state_aux Pr Tr \<omega> (heap_var Tr) = Some (AbsV (AHeap (construct_bpl_heap_from_vpr_heap Pr (field_translation Tr) (get_hh_total_full \<omega>))))"
  by simp

lemma initial_global_state_aux_mask: 
  assumes "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]"
  shows  "initial_global_state_aux Pr Tr \<omega> (mask_var Tr) = Some (AbsV (AMask (\<lambda>_. 0)))"
proof -
  have "mask_var Tr \<noteq> heap_var Tr"
    using assms
    unfolding disjoint_list_def
    apply (rule allE[where ?x = 0])
    apply (erule allE[where ?x = 1])
    by simp

  thus ?thesis
    by simp
qed

lemma initial_global_state_aux_const: 
  assumes Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          Const: "x \<in> range (const_repr Tr)"
        shows  "initial_global_state_aux Pr Tr \<omega> x = Some (boogie_const_val (SOME c. const_repr Tr c = x))"
proof -
  have "x \<noteq> heap_var Tr"
    apply (insert Disj)
    apply (unfold disjoint_list_def)
    apply (erule allE[where ?x = 0])
    apply (erule allE[where ?x = 3])
    apply simp
    using Const
    by blast

  moreover have "x \<noteq> mask_var Tr"
    apply (insert Disj)
    apply (unfold disjoint_list_def)
    apply (erule allE[where ?x = 1])
    apply (erule allE[where ?x = 3])
    apply simp
    using Const
    by blast

  ultimately show ?thesis
    using Const
    by simp
qed

lemma initial_global_state_aux_field: 
  assumes Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          Field: "\<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some x"
  shows  "initial_global_state_aux Pr Tr \<omega> x = Some (AbsV (AField (NormalField x (SOME t. \<exists>f_vpr. field_translation Tr f_vpr = Some x \<and> 
                                                                       declared_fields Pr f_vpr = Some t))))"
proof -
  have "x \<in> ran (field_translation Tr)"
    using Field ranI
    by fast

  have "x \<noteq> heap_var Tr"
    apply (insert Disj)
    apply (unfold disjoint_list_def)
    apply (erule allE[where ?x = 0])
    apply (erule allE[where ?x = 2])
    apply simp
    using \<open>x \<in> _\<close>
    by blast

  moreover have "x \<noteq> mask_var Tr"
    apply (insert Disj)
    apply (unfold disjoint_list_def)
    apply (erule allE[where ?x = 1])
    apply (erule allE[where ?x = 2])
    apply simp
    using \<open>x \<in> _\<close>
    by blast

  moreover have "x \<notin> range (const_repr Tr)"
    apply (insert Disj)
    apply (unfold disjoint_list_def)
    apply (erule allE[where ?x = 3])
    apply (erule allE[where ?x = 2])
    apply simp
    using \<open>x \<in> _\<close>
    by (meson disjnt_iff)

  ultimately show ?thesis
    using Field
    by simp
qed


lemma eq_someD:
  assumes "a = f (SOME t. Q t)" and "Q t"
  obtains t' where "Q t' \<and> a = f t'"
  using assms 
  by (metis someI_ex)

lemma initial_global_state_aux_field_2: 
  assumes Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          Inj: "inj_on (field_translation Tr) (dom (field_translation Tr))" and
          FieldTr: "field_translation Tr f_vpr = Some x" and
          FieldVpr: "declared_fields Pr f_vpr = Some t"
        shows  "initial_global_state_aux Pr Tr \<omega> x = Some (AbsV (AField (NormalField x t)))" (is "?g x = _")
proof -
  have *: "\<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some x"
    using FieldTr FieldVpr
    by blast

  note Aux = initial_global_state_aux_field[OF Disj *] 

  from FieldTr FieldVpr obtain f'_vpr t' where 
    "?g x = Some (AbsV (AField (NormalField x t')))" and
    "field_translation Tr f'_vpr = Some x \<and> declared_fields Pr f'_vpr = Some t'"  
    using eq_someD[where ?f= "\<lambda>t. Some (AbsV (AField (NormalField x t)))", OF Aux]
    by metis

  thus ?thesis
    using Inj FieldTr FieldVpr   
    by (metis domI inj_on_contraD option.inject)
qed

definition initial_global_state 
  where "initial_global_state T vs Pr Tr \<omega> \<equiv> extend_named_state_var_context (vbpl_absval_ty T) vs (initial_global_state_aux Pr Tr \<omega>)"
                                                                                                              
lemma initial_global_state_aux_typ_wf:
  assumes 
          WfTyRepr: "wf_ty_repr_bpl T" and
          InjTrField:  "inj_on (field_translation Tr) (dom (field_translation Tr))" and
          Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          Closed: "list_all (closed \<circ> (fst \<circ> snd)) vs" and
          VprHeapTy: "total_heap_well_typed Pr (domain_type T) (get_hh_total_full \<omega>)" and
          FieldTrTy: "\<And>f_vpr t_vpr. declared_fields Pr f_vpr = Some t_vpr \<Longrightarrow>
                        \<exists>f_bpl t_bpl.  
                             field_translation Tr f_vpr = Some f_bpl \<and>
                             vpr_to_bpl_ty T t_vpr = Some t_bpl \<and>
                             lookup_vdecls_ty vs f_bpl = Some (TCon (TFieldId T) [TConSingle (TNormalFieldId T), t_bpl])" and
          HeapTy: "lookup_vdecls_ty vs (heap_var Tr) = Some (TConSingle (THeapId T))" and
          MaskTy: "lookup_vdecls_ty vs (mask_var Tr) = Some (TConSingle (TMaskId T))" and
          ConstTy: "\<And>c. lookup_vdecls_ty vs (const_repr Tr c) = Some (boogie_const_ty T c)"
        shows "state_typ_wf (vbpl_absval_ty T) [] (initial_global_state T vs Pr Tr \<omega>) vs"
  unfolding initial_global_state_def
proof (rule extend_named_state_var_context_state_typ_wf[OF Closed closed_types_inhabited])
  let ?field_tr_dom = "{f_bpl. \<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some f_bpl}"

  fix x t v
  assume LookupTy: "lookup_vdecls_ty vs x = Some t" and
         "initial_global_state_aux Pr Tr \<omega> x = Some v" (is "?ns x = _")

  hence *:"x \<in> {heap_var Tr} \<union> {mask_var Tr} \<union> ?field_tr_dom \<union> range (const_repr Tr)"
    using dom_initial_global_state_aux
    by blast

  show "type_of_vbpl_val T v = t"
  proof (cases rule: Set.UnE[OF *])
    case 1
    then show ?thesis 
    proof (cases rule: Set.UnE[OF 1])
      case 1
      then show ?thesis
      proof (cases rule: Set.UnE[OF 1])
      case 1 \<comment>\<open>heap_var case\<close>
        hence "x = heap_var Tr" by simp
        hence "v = (AbsV (AHeap (construct_bpl_heap_from_vpr_heap Pr (field_translation Tr) (get_hh_total_full \<omega>))))" (is "v = ?h")
          using \<open>?ns x = Some v\<close>
          by simp
        have "type_of_vbpl_val T ?h = (TConSingle (THeapId T))"
          using construct_bpl_heap_from_vpr_heap_correct_aux[OF WfTyRepr VprHeapTy _ InjTrField]
          by simp      
        
        then show ?thesis        
          using HeapTy LookupTy \<open>v = _\<close> \<open>x = heap_var Tr\<close> 
          by auto
      next
        case 2 \<comment>\<open>mask_var case\<close>
        hence "x = mask_var Tr" by simp
        hence "v = AbsV (AMask (\<lambda>_. 0))"
          using \<open>?ns x = Some v\<close>  initial_global_state_aux_mask[OF Disj, where ?Pr=Pr and ?\<omega>=\<omega>]
          by simp        
  
        then show ?thesis 
          using MaskTy LookupTy \<open>x = _\<close>
          by simp    
      qed
    next
      case 2 \<comment>\<open>field translation\<close>
      from this obtain f_vpr t_vpr where FieldLookup: "declared_fields Pr f_vpr = Some t_vpr" and 
                                     FieldTr: "field_translation Tr f_vpr = Some x"
        by blast
      from this obtain t_bpl where 
         TyBpl: "vpr_to_bpl_ty T t_vpr = Some t_bpl" and
         LookupFieldTyBpl: "lookup_vdecls_ty vs x = Some (TCon (TFieldId T) [TConSingle (TNormalFieldId T), t_bpl])"         
        using FieldTrTy[OF FieldLookup]
        by auto
        
      from initial_global_state_aux_field_2[OF Disj InjTrField FieldTr FieldLookup, where ?\<omega>=\<omega>] have
         "v = AbsV (AField (NormalField x t_vpr))"
        using \<open>?ns x = Some v\<close>
        by simp
        
      thus ?thesis
        using LookupFieldTyBpl LookupTy TyBpl 
        by simp        
    qed
  next
    case 2 \<comment>\<open>const case\<close>
    hence "v = boogie_const_val (SOME c. const_repr Tr c = x)"
      using \<open>?ns x = Some v\<close> initial_global_state_aux_const[OF Disj \<open>x \<in> range (const_repr Tr)\<close>, where ?Pr = Pr and ?\<omega> = \<omega>]
      by simp      

    then show ?thesis 
      using boogie_const_val_well_ty ConstTy LookupTy
      by (metis (mono_tags, lifting) "2" image_iff option.inject verit_sko_ex')
  qed
qed

subsubsection \<open>Local state\<close>

fun initial_local_state_aux :: "tr_vpr_bpl \<Rightarrow> 'a full_total_state \<Rightarrow> ('a vbpl_absval) named_state"
  where "initial_local_state_aux Tr \<omega> x = 
           (if x \<in> ran (var_translation Tr) then 
             Some (SOME v. \<exists>x_vpr v_vpr. var_translation Tr x_vpr = Some x \<and> 
                                     get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                                     v = val_rel_vpr_bpl v_vpr)
           else 
             None)"

lemma dom_initial_local_state_aux: "dom (initial_local_state_aux Tr \<omega>) = ran (var_translation Tr)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix x
    assume "x \<in> ?A"
    from this obtain y where "initial_local_state_aux Tr \<omega> x = Some y"
      by blast
    thus "x \<in> ?B"
      apply simp
      by (meson option.distinct(1))
  qed
qed auto

lemma initial_local_state_aux_Some:
  assumes Inj: "inj_on (var_translation Tr) (dom (var_translation Tr))" and
          VarTrSome: "var_translation Tr x_vpr = Some x_bpl" and
          StoreSome: "get_store_total \<omega> x_vpr = Some v_vpr"
        shows "initial_local_state_aux Tr \<omega> x_bpl = Some (val_rel_vpr_bpl v_vpr)" (is "?f x = Some ?v_bpl")
proof -
  from VarTrSome have "x_bpl \<in> ran (var_translation Tr)"
    by (simp add: ranI)

  hence "?f x_bpl = Some (SOME v. \<exists>x_vpr v_vpr. var_translation Tr x_vpr = Some x_bpl \<and> 
                                     get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                                     v = val_rel_vpr_bpl v_vpr)" (is "_ = Some ?v")
    by simp

  moreover from eq_someD[where ?f = Some, OF this] obtain x_vpr' v_vpr' where
    "var_translation Tr x_vpr' = Some x_bpl" and
    "get_store_total \<omega> x_vpr' = Some v_vpr'"
    "?v = val_rel_vpr_bpl v_vpr'"
    using StoreSome VarTrSome
    by (metis (no_types, lifting) calculation option.inject)    

  ultimately show ?thesis
    using assms
    by (metis (mono_tags, lifting) domI option.sel the_inv_into_f_f)
qed


definition initial_local_state
  where "initial_local_state T vs Tr \<omega> \<equiv> extend_named_state_var_context (vbpl_absval_ty T) vs (initial_local_state_aux Tr \<omega>)"

lemma initial_local_state_aux_typ_wf:
  assumes 
          WfTyRepr: "wf_ty_repr_bpl T" and
          Closed: "list_all (closed \<circ> (fst \<circ> snd)) vs" and
          VarTranslationTy: "\<And> x_vpr x_bpl. var_translation Tr x_vpr = Some x_bpl \<Longrightarrow>
                                   (\<exists>v_vpr. get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                                            (\<exists>t. lookup_vdecls_ty vs x_bpl = Some t \<and>
                                                 type_of_vbpl_val T (val_rel_vpr_bpl v_vpr) = t))" and
          Inj:  "inj_on (var_translation Tr) (dom (var_translation Tr))"
        shows "state_typ_wf (vbpl_absval_ty T) [] (initial_local_state T vs Tr \<omega>) vs"
  unfolding initial_local_state_def
proof (rule extend_named_state_var_context_state_typ_wf[OF Closed closed_types_inhabited])
  fix x t v
  assume LookupTy: "lookup_vdecls_ty vs x = Some t" and
         *: "initial_local_state_aux Tr \<omega> x = Some v"

  hence "x \<in> ran (var_translation Tr)"
    by (metis initial_local_state_aux.simps option.distinct(1))

  hence "v = (SOME v. \<exists>x_vpr v_vpr. var_translation Tr x_vpr = Some x \<and> 
                                     get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                                     v = val_rel_vpr_bpl v_vpr)"
    using *
    by auto

  from \<open>x \<in> _\<close> obtain x_vpr where VarTr: "var_translation Tr x_vpr = Some x"
    unfolding ran_def
    by blast

  moreover from this obtain v_vpr where 
        Store: "get_store_total \<omega> x_vpr = Some v_vpr" and 
        TyBpl: "type_of_vbpl_val T (val_rel_vpr_bpl v_vpr) = t"
    using VarTranslationTy LookupTy
    by fastforce

  have "\<exists>v x_vpr v_vpr. var_translation Tr x_vpr = Some x \<and> get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                               v = val_rel_vpr_bpl v_vpr"
    apply (rule exI)+
    apply (intro conjI)
      apply (rule VarTr)
     apply (rule Store)
    apply simp
    done

  from this obtain x_vpr' v_vpr' where 
    "var_translation Tr x_vpr' = Some x" and 
    "get_store_total \<omega> x_vpr' = Some v_vpr'" and
    "v = val_rel_vpr_bpl v_vpr'"
    using \<open>v = _\<close>    
    using * Inj initial_local_state_aux_Some 
    by fastforce

  hence "v = val_rel_vpr_bpl v_vpr"
    using VarTr Inj
    by (metis Store domI inj_on_eq_iff option.sel)

  thus "type_of_vbpl_val T v = t"
    using TyBpl
    by simp
qed

subsubsection \<open>Properties\<close>

lemma list_all2_map_of:
  assumes ListAll2: "list_all2 P xs ys" and
          Fst: "\<forall> x y. P x y \<longrightarrow> fst x = fst y" and
          MapOf: "map_of xs a = Some b"
        shows "\<exists>c. map_of ys a = Some c \<and> P (a,b) (a,c)"
  using ListAll2 MapOf
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case 
  proof (cases "a = fst x")
    case True
    hence "map_of (y # ys) a = Some (snd y)"
      using Cons.hyps Fst by auto
    moreover from \<open>a = fst x\<close> have "snd x = b"
      using Cons
      by simp
    ultimately show ?thesis 
      using \<open>P x y\<close> \<open>a = fst x\<close>
      by (metis Fst prod.collapse)
  next
    case False
    then show ?thesis 
      using Cons Fst old.prod.exhaust 
      by auto
  qed   
qed

definition field_tr_prop
  where "field_tr_prop T global_decls f_vpr_ty_vpr f_vpr_f_bpl \<equiv>  
      \<exists>ty_bpl.
           (fst f_vpr_ty_vpr = fst f_vpr_f_bpl)   \<and>
            vpr_to_bpl_ty T (snd f_vpr_ty_vpr) = Some ty_bpl \<and>
            lookup_vdecls_ty global_decls (snd f_vpr_f_bpl) =
            Some
             (TCon (TFieldId T) [TConSingle (TNormalFieldId T), ty_bpl])"

lemma field_tr_prop_fst: "\<forall>f_vpr_ty_vpr f_vpr_f_bpl. field_tr_prop T global_decls f_vpr_ty_vpr f_vpr_f_bpl \<longrightarrow> fst f_vpr_ty_vpr = fst f_vpr_f_bpl"
  by (simp add: field_tr_prop_def)

definition var_rel_prop
  where "var_rel_prop T local_decls ty_vpr var_vpr \<equiv> 
          \<exists>ty_bpl. vpr_to_bpl_ty T ty_vpr = Some ty_bpl \<and>
                   lookup_vdecls_ty local_decls var_vpr = Some ty_bpl"

lemma var_rel_prop_aux:
  assumes WellTy: "vpr_store_well_typed A \<Lambda> \<sigma>" 
      and "domain_type T = A"
      and ListAll: "list_all (\<lambda>var_vpr_var_bpl. \<exists>t. \<Lambda> (fst var_vpr_var_bpl) = Some t \<and> var_rel_prop T local_decls t (snd var_vpr_var_bpl)) var_rel_list"
      and LookupVarRel: "map_of var_rel_list x_vpr = Some x_bpl"
  shows "\<exists>v_vpr. \<sigma> x_vpr = Some v_vpr \<and> 
                                      (\<exists>t. lookup_vdecls_ty local_decls x_bpl = Some t \<and>
                                           type_of_vbpl_val T (val_rel_vpr_bpl v_vpr) = t)"
proof -
  from LookupVarRel obtain i
    where  "i < length var_rel_list" and
           "var_rel_list ! i = (x_vpr, x_bpl)"
    by (meson in_set_conv_nth map_of_SomeD)

  with ListAll 
  obtain t where "\<Lambda> x_vpr = Some t" and
           Prop: "var_rel_prop T local_decls t x_bpl"
    by (auto simp: list_all_length)

  from this obtain v_vpr where "\<sigma> x_vpr = Some v_vpr \<and> get_type A v_vpr = t"
    using WellTy
    unfolding vpr_store_well_typed_def
    by blast

  thus ?thesis
    using Prop \<open>domain_type T = A\<close> vpr_to_bpl_val_type
    unfolding var_rel_prop_def
    by blast
qed
    
lemma boogie_const_rel_aux:
  assumes ConstTy: "\<And>c. lookup_vdecls_ty (fst \<Lambda>) (const_repr Tr c) = Some (boogie_const_ty T c)" and
          GlobalsLocalsDisj: "set (map fst (fst \<Lambda>)) \<inter> set (map fst (snd \<Lambda>)) = {}" and
          DisjAux: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          InitGlobalState: "\<And>x. x \<in> range (const_repr Tr) \<Longrightarrow> global_state ns x = initial_global_state T (fst \<Lambda>) Pr Tr \<omega> x" and
          InjConstRepr: "inj (const_repr Tr)"
  shows   "boogie_const_rel (const_repr Tr) \<Lambda> ns"
  unfolding boogie_const_rel_def
  proof (rule allI)
    fix c
    let ?cr = "const_repr Tr c"

    from ConstTy GlobalsLocalsDisj
    have LookupVar: "lookup_var \<Lambda> ns ?cr = global_state ns ?cr"
      by (metis lookup_var_global_disj lookup_vdecls_ty_map_of prod.exhaust_sel)

    from initial_global_state_aux_const[OF DisjAux, where ?Pr="Pr" and ?\<omega>=\<omega> and ?x="?cr"] InjConstRepr
    have "initial_global_state_aux Pr Tr \<omega> (const_repr Tr c) = Some (boogie_const_val c)"
    using inj_eq by fastforce

    hence "global_state ns ?cr = Some (boogie_const_val c)"
      by (simp add: InitGlobalState initial_global_state_def)

    with LookupVar show "lookup_var \<Lambda> ns (const_repr Tr c) = Some (boogie_const_val c)"
      by argo
  qed

lemma field_rel_aux:
assumes FieldTrTy: "\<And>f_vpr t_vpr. 
                              declared_fields Pr f_vpr = Some t_vpr \<Longrightarrow>
                            \<exists> f_bpl.  
                               field_translation Tr f_vpr = Some f_bpl \<and>
                               field_tr_prop T (fst \<Lambda>) (f_vpr, t_vpr) (f_vpr, f_bpl)"
    and GlobalsLocalsDisj: "set (map fst (fst \<Lambda>)) \<inter> set (map fst (snd \<Lambda>)) = {}"
    and DisjAux: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]"
    and InitGlobalState: "\<And>x. x \<in> ran (field_translation Tr) \<Longrightarrow> global_state ns x = initial_global_state T (fst \<Lambda>) Pr Tr \<omega> x"
    and InjFieldTr: "inj_on (field_translation Tr) (dom (field_translation Tr))"
  shows "field_rel Pr \<Lambda> (field_translation Tr) ns"
    unfolding field_rel_def
  proof (rule conjI[OF InjFieldTr], (rule allI | rule impI)+)
    fix f_vpr t_vpr
    assume FieldLookup: "declared_fields Pr f_vpr = Some t_vpr"
    with FieldTrTy obtain f_bpl t_bpl
      where FieldTr: "field_translation Tr f_vpr = Some f_bpl" and
                     "vpr_to_bpl_ty T t_vpr = Some t_bpl" and
            FieldGlobal:  "lookup_vdecls_ty (fst \<Lambda>) f_bpl = Some (TCon (TFieldId T) [TConSingle (TNormalFieldId T), t_bpl])"
      unfolding field_tr_prop_def
      by fastforce

    hence "f_bpl \<in> ran (field_translation Tr)"
      unfolding ran_def
      by blast

    from FieldGlobal GlobalsLocalsDisj have 
      "lookup_var \<Lambda> ns f_bpl = global_state ns f_bpl"
      by (metis lookup_var_global_disj lookup_vdecls_ty_map_of prod.exhaust_sel)
    
    moreover from initial_global_state_aux_field_2[OF DisjAux InjFieldTr FieldTr FieldLookup, where ?\<omega>=\<omega>]
    have "global_state ns f_bpl = Some (AbsV (AField (NormalField f_bpl t_vpr)))"
      using InitGlobalState \<open>f_bpl \<in> _\<close>
      by (simp add: initial_global_state_def)
    
    ultimately show "has_Some (\<lambda>f_bpl. lookup_var \<Lambda> ns f_bpl = Some (AbsV (AField (NormalField f_bpl t_vpr)))) (field_translation Tr f_vpr)"
      using FieldTr
      by simp
  qed

definition disj_vars_state_relation
  where "disj_vars_state_relation Tr AuxPred =
              disjoint_list [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (var_translation Tr), 
                               ran (field_translation Tr), range (const_repr Tr), dom AuxPred]"

definition field_tr_prop_full
  where "field_tr_prop_full Pr global_vdecls TyRep FieldTr \<equiv> \<forall>f_vpr t_vpr. 
                          declared_fields Pr f_vpr = Some t_vpr \<longrightarrow>
                          (\<exists> f_bpl.  
                           FieldTr f_vpr = Some f_bpl \<and>
                           field_tr_prop TyRep global_vdecls (f_vpr, t_vpr) (f_vpr, f_bpl))"

lemma init_state_in_state_relation:
  assumes  WfTyRepr: "wf_ty_repr_bpl T" and
         Disj: "disj_vars_state_relation Tr Map.empty" and
          "is_empty_total_full \<omega>" and
          ViperHeapWellTy: "total_heap_well_typed ((program_total ctxt_vpr)) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>)" and
          WfMask: "wf_mask_simple (get_mh_total_full \<omega>)" and
          Consistent: "StateCons \<omega>" and
         TyInterp: "type_interp ctxt = vbpl_absval_ty T" and
          DomainTy:  "domain_type T = absval_interp_total ctxt_vpr" and
          "ns = \<lparr> old_global_state = initial_global_state T (fst (var_context ctxt)) (program_total ctxt_vpr) Tr \<omega>,
                  global_state = initial_global_state T (fst (var_context ctxt)) (program_total ctxt_vpr) Tr \<omega>,
                  local_state = initial_local_state T (snd (var_context ctxt)) Tr \<omega>,
                  binder_state = Map.empty \<rparr>" and
         InjVarTr: "inj_on (var_translation Tr) (dom (var_translation Tr))" and

          ClosedGlobals: "list_all (closed \<circ> (fst \<circ> snd)) (fst (var_context ctxt))" and
          ClosedLocals: "list_all (closed \<circ> (fst \<circ> snd)) (snd (var_context ctxt))" and
          GlobalsLocalsDisj: "set (map fst (fst (var_context ctxt))) \<inter> set (map fst (snd (var_context ctxt))) = {}" and

          "heap_var Tr = heap_var_def Tr" and
          "mask_var Tr = mask_var_def Tr" and

\<comment>\<open>Global state assumptions\<close>
          InjFieldTr:  "inj_on (field_translation Tr) (dom (field_translation Tr))" and
          InjConstRepr: "inj (const_repr Tr)" and
          FieldTrTy: "field_tr_prop_full (program_total ctxt_vpr) (fst (var_context ctxt)) T (field_translation Tr)" and
          HeapTy: "lookup_vdecls_ty (fst (var_context ctxt)) (heap_var Tr) = Some (TConSingle (THeapId T))" and
          MaskTy: "lookup_vdecls_ty (fst (var_context ctxt)) (mask_var Tr) = Some (TConSingle (TMaskId T))" and
          ConstTy: "\<And>c. lookup_vdecls_ty (fst (var_context ctxt)) (const_repr Tr c) = Some (boogie_const_ty T c)" and

\<comment>\<open>Local state assumptions\<close>
          VarTranslationTy: "\<And> x_vpr x_bpl. var_translation Tr x_vpr = Some x_bpl \<Longrightarrow>
                                   (\<exists>v_vpr. get_store_total \<omega> x_vpr = Some v_vpr \<and> 
                                            (\<exists>t. lookup_vdecls_ty (snd (var_context ctxt)) x_bpl = Some t \<and>
                                                 type_of_vbpl_val T (val_rel_vpr_bpl v_vpr) = t))"


  shows "state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons T Tr Map.empty) \<omega> ns"
proof -
  from \<open>ns = _\<close> have
    "local_state ns = initial_local_state T (snd (var_context ctxt)) Tr \<omega>" and
    "global_state ns = initial_global_state T (fst (var_context ctxt)) (program_total ctxt_vpr) Tr \<omega>" and
    "old_global_state ns = global_state ns" and
    "binder_state ns = Map.empty"
    by simp_all

  note DisjSimp = Disj[simplified disj_vars_state_relation_def]

  have "disjoint_list [{heap_var Tr, heap_var_def Tr}, {mask_var Tr, mask_var_def Tr}, ran (field_translation Tr), range (const_repr Tr)]"
    by (rule disjoint_list_sublist[OF DisjSimp]) fastforce    
  hence DisjAux: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]"
    by (rule disjoint_list_subset_list_all2) blast

  show ?thesis
  unfolding state_rel_empty_def state_rel_def state_rel0_def
  proof (rule conjI[OF \<open>is_empty_total_full \<omega>\<close>], intro conjI)

    have Aux: "\<And>var_vpr var_bpl val_vpr.
         var_translation Tr var_vpr = Some var_bpl \<Longrightarrow> get_store_total \<omega> var_vpr = Some val_vpr \<Longrightarrow> 
         lookup_var (var_context ctxt) ns var_bpl = Some (val_rel_vpr_bpl val_vpr)"
    proof -    
      fix var_vpr var_bpl val_vpr
      assume VarTrSome: "var_translation Tr var_vpr = Some var_bpl" and
             "get_store_total \<omega> var_vpr = Some val_vpr" 
  
      moreover from this obtain t where LookupTy: "lookup_vdecls_ty (snd (var_context ctxt)) var_bpl = Some t"
        using VarTranslationTy
        by blast
  
      ultimately have "local_state ns var_bpl = Some (val_rel_vpr_bpl val_vpr)"
        apply (subst \<open>local_state ns = _\<close>)
        using initial_local_state_aux_Some[OF InjVarTr]
        by (fastforce simp: initial_local_state_def)
  
      thus "lookup_var (var_context ctxt) ns var_bpl = Some (val_rel_vpr_bpl val_vpr)"
        using LookupTy
        by (metis lookup_var_local lookup_vdecls_ty_map_of prod.exhaust_sel)
    qed
             
    show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) \<omega> ns"
      unfolding store_rel_def
      apply (rule conjI[OF InjVarTr], (rule allI | rule impI)+)
      using VarTranslationTy TyInterp Aux
      by (metis lookup_vdecls_ty_local_3)
  
  next
  
    show "heap_var_rel (program_total ctxt_vpr) (var_context ctxt) T (field_translation Tr) (heap_var Tr) \<omega> ns"
      unfolding heap_var_rel_def
    proof (intro conjI, rule exI, intro conjI)
      have "global_state ns (heap_var Tr) = Some (AbsV (AHeap (construct_bpl_heap_from_vpr_heap (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>))))"
                      (is "_ = Some (AbsV (AHeap ?hb))")
        by (simp add: \<open>global_state ns = _\<close> initial_global_state_def) 
    
      with GlobalsLocalsDisj and HeapTy
      show "lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap ?hb))"
        by (metis lookup_var_global_disj lookup_vdecls_ty_map_of prod.collapse)
    next
      from GlobalsLocalsDisj and HeapTy
      show "lookup_var_ty (var_context ctxt) (heap_var Tr) = Some (TConSingle (THeapId T))"
        by (metis lookup_var_decl_global_2 lookup_var_ty_def lookup_vdecls_ty_def lookup_vdecls_ty_map_of)
    next
      show "vbpl_absval_ty_opt T (AHeap (construct_bpl_heap_from_vpr_heap (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>))) = Some (THeapId T, [])"
        using construct_bpl_heap_from_vpr_heap_correct_aux[OF WfTyRepr ViperHeapWellTy DomainTy InjFieldTr] 
        by meson
    next
      show "heap_rel (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>)
       (construct_bpl_heap_from_vpr_heap (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>))"
        using construct_bpl_heap_from_vpr_heap_correct_aux[OF WfTyRepr ViperHeapWellTy DomainTy InjFieldTr] 
        by meson
    next 
      show "total_heap_well_typed (program_total ctxt_vpr) (domain_type T) (get_hh_total_full \<omega>)"        
        using DomainTy ViperHeapWellTy by auto
    qed
  
    thus "heap_var_rel (program_total ctxt_vpr) (var_context ctxt) T (field_translation Tr) (heap_var_def Tr) \<omega> ns"
      using \<open>heap_var Tr = _\<close>
      by simp
  next  
    show "mask_var_rel (program_total ctxt_vpr) (var_context ctxt) T (field_translation Tr) (mask_var Tr) \<omega> ns"
      unfolding mask_var_rel_def
    proof (rule exI, intro conjI)
                    
      have "global_state ns (mask_var Tr) = Some (AbsV (AMask zero_mask_bpl))"
                      (is "_ = Some (AbsV (AMask ?mb))")
        apply (subst \<open>global_state ns = _\<close>)
        using initial_global_state_aux_mask[OF DisjAux, where ?Pr="program_total ctxt_vpr" and ?\<omega>=\<omega>]
        by (simp add: initial_global_state_def)
  
      with GlobalsLocalsDisj and MaskTy      
      show "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask ?mb))"
        by (metis lookup_var_global_disj lookup_vdecls_ty_map_of prod.collapse)
    next
      show "lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId T))"
        using GlobalsLocalsDisj and MaskTy
        by (metis (no_types, opaque_lifting) lookup_var_decl_global_2 lookup_var_ty_def lookup_vdecls_ty_def lookup_vdecls_ty_map_of option.inject)
    next    
      show "mask_rel (program_total ctxt_vpr) (field_translation Tr) (get_mh_total_full \<omega>) zero_mask_bpl"
        using \<open>is_empty_total_full \<omega>\<close>
        unfolding mask_rel_def is_empty_total_full_def is_empty_total_def zero_mask_def      
        by (simp add: zero_preal.rep_eq)
    qed
  
    thus "mask_var_rel (program_total ctxt_vpr) (var_context ctxt) T (field_translation Tr) (mask_var_def Tr) \<omega> ns"
      using \<open>mask_var Tr = _\<close>
      by simp
  
    show "field_rel (program_total ctxt_vpr) (var_context ctxt) (field_translation Tr) ns"
      unfolding field_rel_def
    proof (rule conjI[OF InjFieldTr], (rule allI | rule impI)+)
      fix f_vpr t_vpr
      assume FieldLookup: "declared_fields (program_total ctxt_vpr) f_vpr = Some t_vpr"
      with FieldTrTy obtain f_bpl t_bpl
        where FieldTr: "field_translation Tr f_vpr = Some f_bpl" and
                       "vpr_to_bpl_ty T t_vpr = Some t_bpl" and
              FieldGlobal:  "lookup_vdecls_ty (fst (var_context ctxt)) f_bpl = Some (TCon (TFieldId T) [TConSingle (TNormalFieldId T), t_bpl])"
        unfolding field_tr_prop_full_def field_tr_prop_def
        by fastforce

      from FieldGlobal GlobalsLocalsDisj have 
        "lookup_var (var_context ctxt) ns f_bpl = global_state ns f_bpl"
        by (metis lookup_var_global_disj lookup_vdecls_ty_map_of prod.exhaust_sel)
      
      moreover from initial_global_state_aux_field_2[OF DisjAux InjFieldTr FieldTr FieldLookup, where ?\<omega>=\<omega>]
      have "global_state ns f_bpl = Some (AbsV (AField (NormalField f_bpl t_vpr)))"
        using \<open>global_state ns = _\<close>
        by (simp add: initial_global_state_def)
      
      ultimately show "has_Some (\<lambda>f_bpl. lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField (NormalField f_bpl t_vpr)))) (field_translation Tr f_vpr)"
        using FieldTr
        by simp
    qed
  next  
    show "boogie_const_rel (const_repr Tr) (var_context ctxt) ns"
      using ConstTy GlobalsLocalsDisj DisjAux \<open>global_state ns = _\<close> InjConstRepr boogie_const_rel_aux
      by metis
  next
  
    show "state_well_typed (type_interp ctxt) (var_context ctxt) [] ns"
      unfolding state_well_typed_def
    proof (intro conjI)
      show "state_typ_wf (type_interp ctxt) [] (local_state ns) (snd (var_context ctxt))"
        apply (subst \<open>local_state ns = _\<close>)
        apply (subst TyInterp)
        by (rule initial_local_state_aux_typ_wf[OF WfTyRepr ClosedLocals VarTranslationTy InjVarTr])
    next
      show "state_typ_wf (type_interp ctxt) [] (global_state ns) (fst (var_context ctxt))"
        apply (subst \<open>global_state ns = _\<close>)
        apply (subst TyInterp)
        apply (rule initial_global_state_aux_typ_wf[OF WfTyRepr InjFieldTr DisjAux ClosedGlobals _ _ HeapTy MaskTy ConstTy])
        using ViperHeapWellTy DomainTy
         apply simp
        using FieldTrTy
        unfolding field_tr_prop_full_def field_tr_prop_def
        by simp
    
      thus "state_typ_wf (type_interp ctxt) [] (old_global_state ns) (fst (var_context ctxt))"
        using \<open>old_global_state ns = _\<close>
        by simp
    next
      show "binder_state ns = Map.empty"
        by (rule \<open>binder_state ns = _\<close>)
    qed
  next  
    show "aux_vars_pred_sat (var_context ctxt) Map.empty ns"
      by (simp add: aux_vars_pred_sat_def)  
  qed (insert assms DisjSimp, auto)
qed

subsection \<open>Unique constants helper lemmas\<close>

lemma unique_consts_field_prop:
  assumes RanFieldTr: "set unique_cs \<subseteq> ran (field_translation Tr)"
      and DomEq: "dom (declared_fields Pr) = dom (field_translation Tr)"
    shows "\<forall> c \<in> set unique_cs. \<exists> f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some c"
proof
  fix c
  assume "c \<in> set unique_cs"
  from this obtain f_vpr where "field_translation Tr f_vpr = Some c"
    using RanFieldTr
    unfolding ran_def
    by blast
  with DomEq 
  show "\<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some c"
    by blast
qed

lemma unique_constants_initial_global_state:
  assumes Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]"
      and "distinct unique_cs"
      and FieldProp: "\<forall> c \<in> set unique_cs. \<exists> f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some c"
    shows "unique_constants_distinct (initial_global_state TyRep \<Lambda> Pr Tr \<omega>) unique_cs" (is "unique_constants_distinct ?gs unique_cs")
  using assms
proof (induction unique_cs)
  case Nil
  then show ?case by (simp add: unique_constants_distinct_def)
next
  case (Cons c cs)  

  have GlobalStateFieldLookup: "\<And> c'. c' \<in> set (c#cs) \<Longrightarrow> \<exists>t. ?gs c' = Some (AbsV (AField (NormalField c' t)))"
  proof -
    fix c'
    assume "c' \<in> set (c#cs)"
    from this Cons obtain f_vpr where FieldLookup: "declared_fields Pr f_vpr \<noteq> None" and 
                               FieldTr: "field_translation Tr f_vpr = Some c'"    
      by fast

    with initial_global_state_aux_field[OF Disj]
    obtain t where "initial_global_state_aux Pr Tr \<omega> c' = Some (AbsV (AField (NormalField c' t)))"
      by blast
    hence "?gs c' = Some (AbsV (AField (NormalField c' t)))"
      unfolding initial_global_state_def
      by simp
    thus "\<exists>t. ?gs c' = Some (AbsV (AField (NormalField c' t)))"
      by simp
  qed 

  show ?case 
    unfolding unique_constants_distinct_def 
  proof (simp, rule conjI)
    show "distinct (map (\<lambda>x. the (?gs x)) cs)"
    proof -
      have "unique_constants_distinct (initial_global_state TyRep \<Lambda> Pr Tr \<omega>) cs"
        using Cons
        by simp
      thus ?thesis
        unfolding unique_constants_distinct_def
        by blast
    qed

  next
    show "the (?gs c) \<notin> (\<lambda>x. the (?gs x)) ` set cs" (is "_ \<notin> ?M")
    proof 
      assume "the (?gs c) \<in> ?M"
      from this obtain c' where 
        "c' \<in> set cs" and
        Eq: "the (?gs c) = the (?gs c')"
        by blast

      obtain t where "the (?gs c) = AbsV (AField (NormalField c t))"
        using GlobalStateFieldLookup
        by fastforce

      moreover obtain t' where "the (?gs c') = AbsV (AField (NormalField c' t'))"
        using GlobalStateFieldLookup \<open>c' \<in> _\<close>
        by fastforce

      moreover have "c \<noteq> c'"
        using \<open>distinct (c # cs)\<close> \<open>c' \<in> _\<close>
        by auto

      ultimately show False
        using Eq
        by auto
    qed
  qed
qed

subsection \<open>Misc\<close>

lemma inter_disjoint_intervals:
  assumes "\<forall>x \<in> A :: ('a :: linorder) set . x \<ge> a_min \<and> x \<le> a_max" and
          "\<forall>x \<in> B. x \<ge> b_min \<and> x \<le> b_max" and
          "a_min \<le> a_max \<and> b_min \<le> b_max \<and> (a_max < b_min \<or> b_max < a_min)"
        shows "A \<inter> B = {}"
  using assms  
  by fastforce     

method rename_case_simp_tac = 
     (rename_tac j1, 
      case_tac j1,
      solves \<open>simp add: Set.Int_commute\<close>)

lemma disj_helper_tr_vpr_bpl:
  assumes "heap_var Tr \<noteq> mask_var Tr" and
          "{heap_var Tr, mask_var Tr} \<inter> ran (var_translation Tr) = {}" and
          "{heap_var Tr, mask_var Tr} \<inter> ran (field_translation Tr) = {}" and
          "{heap_var Tr, mask_var Tr} \<inter> range (const_repr Tr) = {}" and
          "ran (var_translation Tr) \<inter> ran (field_translation Tr) = {}" and
          "ran (var_translation Tr) \<inter> range (const_repr Tr) = {}" and
          "ran (field_translation Tr) \<inter> range (const_repr Tr) = {}"

  shows "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr), 
                               ran (field_translation Tr), range (const_repr Tr)]" (is "disjoint_list ?M")
  unfolding disjoint_list_def
proof clarify
  fix i j
  assume "0 \<le> i" and
         "i < length ?M" and
         "0 \<le> j" and
         "j < length ?M" and
         "i \<noteq> j" 
  thus  "disjnt (?M ! i) (?M ! j)"
    unfolding disjnt_def
    apply (cases i)
    apply (insert assms)
     \<comment>\<open> i = 0 \<close>

     apply (cases j)
      apply simp 
      apply (solves \<open>simp\<close> | rename_case_simp_tac)+
    apply (rename_tac i1)
    apply (case_tac i1)
     \<comment>\<open> i = 1 \<close>

     apply (cases j)
      apply simp
      apply (solves \<open>simp\<close> | rename_case_simp_tac)+
    apply (rename_tac i2)
    apply (case_tac i2)

     \<comment>\<open> i = 2 \<close>

     apply (cases j)
      apply simp
      apply (solves \<open>simp\<close> | rename_case_simp_tac)+
    apply (rename_tac i3)
    apply (case_tac i3)

     \<comment>\<open> i = 3 \<close>

     apply (cases j)
      apply simp
      apply (solves \<open>simp\<close> | rename_case_simp_tac)+
    apply (rename_tac i4)
    apply (case_tac i4)

     \<comment>\<open> i = 4 \<close>
     apply (cases j)
      apply simp
      apply (solves \<open>simp\<close> | rename_case_simp_tac)+
    done
qed

lemma disjoint_list_append_empty:
  assumes "disjoint_list xs"
  shows "disjoint_list (xs@[{}])"
  unfolding disjoint_list_def
proof clarify
  fix i j
  assume *: "0 \<le> i" "i < length (xs @ [{}])" "0 \<le> j" "j < length (xs @ [{}])" "i \<noteq> j"
  show "disjnt ((xs @ [{}]) ! i) ((xs @ [{}]) ! j)"
  proof (cases "i = length xs \<or> j = length xs")
    case True
    then show ?thesis 
      using *
      unfolding disjnt_def
      by fastforce
  next
    case False
    with * have "i < length xs \<and> j < length xs"
      by simp
    then show ?thesis 
      using assms *
      unfolding disjoint_list_def
      by (metis list_update_append1 list_update_id nth_list_update_eq)            
  qed
qed

lemma disjoint_list_drop_last:
  assumes "disjoint_list xs"
     and "xs = xs'@[x]" \<comment>\<open>add as separate assumption such conclusion unifies with more goals\<close>
   shows "disjoint_list xs'"
  apply (rule disjoint_list_sublist[OF assms(1)])
  using assms  
  by force

lemma disjoint_list_drop_i:
  assumes "disjoint_list (xs :: ('a set) list)"
      and "i < length xs"
      and "xs' = take i xs @ drop (i+1) xs"
    shows "disjoint_list (xs' :: ('a set) list)"
proof - 
  from \<open>i < length xs\<close> 
  have "xs = take i xs @ ((xs ! i) # drop (i+1) xs)"
    by (simp add: id_take_nth_drop)

  show ?thesis
  apply (rule disjoint_list_sublist[OF assms(1)])
    apply (subst \<open>xs = _\<close>)
    apply (subst \<open>xs' = _\<close>)
    by simp
qed

lemma disj_vars_state_relation_initialI:
  assumes "heap_var Tr = heap_var_def Tr"
      and "mask_var Tr = mask_var_def Tr"
      and "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (var_translation Tr),
                               ran (field_translation Tr), range (const_repr Tr)]"
    shows "disj_vars_state_relation Tr Map.empty"
  unfolding disj_vars_state_relation_def
  using assms disjoint_list_append_empty
  by fastforce

text \<open>helper tactic for proving disjointness of global Boogie variables\<close>

method disjoint_globals_aux_tac uses disj_prop_aux =
     (rule disjoint_list_subset_list_all2,
      rule disjoint_list_drop_last, \<comment>\<open>drop auxiliary variables\<close>
      rule disjoint_list_drop_i[where ?i=2, OF disj_prop_aux], \<comment>\<open>drop variable translation\<close>
      simp,
      simp,
      simp,
      simp)

lemma initial_global_state_state_restriction:
  assumes Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and
          ConstantsRange:"set (map fst constants) = range (const_repr Tr) \<union> ran (field_translation Tr)" and 
          Elem: "x \<in> range (const_repr Tr) \<union> ran (field_translation Tr)" 
  shows "state_restriction (initial_global_state T (constants@globals) Pr Tr \<omega>) constants x = initial_global_state T constants Pr Tr \<omega> x"
  unfolding state_restriction_def
proof -
  let ?ns0 = "initial_global_state T (constants@globals) Pr Tr \<omega>"
  let ?ns1 = "initial_global_state T constants Pr Tr \<omega>"

  have Aux:"\<And>a a' b y z. b y = Some z \<Longrightarrow>  (a ++ b) y = (a' ++ b) y"
    by simp

  have "?ns0 x = ?ns1 x"
  proof (cases rule:  Set.UnE[OF \<open>x \<in> _\<close>])
    case 1
    show ?thesis 
      apply (simp add: initial_global_state_def, rule Aux)
      using initial_global_state_aux_const[OF Disj 1]
      by blast
  next
    case 2
    show ?thesis
    proof (cases "\<exists>f_vpr. declared_fields Pr f_vpr \<noteq> None \<and> field_translation Tr f_vpr = Some x")
      case True
      show ?thesis         
        apply (simp add: initial_global_state_def, rule Aux)
        using initial_global_state_aux_field[OF Disj True]
        by blast
    next
      case False
      have "x \<noteq> heap_var Tr"
        apply (insert Disj 2)
        apply (unfold disjoint_list_def)
        apply (erule allE[where ?x=0])
        apply (erule allE[where ?x=2])
        by auto

      moreover have "x \<noteq> mask_var Tr"
        apply (insert Disj 2)
        apply (unfold disjoint_list_def)
        apply (erule allE[where ?x=1])
        apply (erule allE[where ?x=2])
        by auto
      moreover have "x \<notin> range (const_repr Tr)"
        apply (insert Disj 2)
        apply (unfold disjoint_list_def)
        apply (erule allE[where ?x=3])
        apply (erule allE[where ?x=2])
        apply simp
        by (meson disjnt_iff)
      ultimately have LookupAux: "initial_global_state_aux Pr Tr \<omega> x = None"
        using False
        by simp

      from Elem ConstantsRange have "x \<in> set (map fst constants)"
        by simp

      hence DomConstants: "x \<in> dom (lookup_vdecls_ty constants)"
        unfolding lookup_vdecls_ty_def
        by (simp add: dom_map_of_2 dom_map_option)

      from \<open>x \<in> set (map fst constants)\<close> have
          DomConstantsGlobals: "x \<in> dom (lookup_vdecls_ty (constants@globals))"
        unfolding lookup_vdecls_ty_def
        using DomConstants lookup_vdecls_ty_def by force       
        
      have "named_state_var_context (vbpl_absval_ty T) constants x = 
           Some (SOME v. \<exists>t. lookup_vdecls_ty constants x = Some t \<and> type_of_val (vbpl_absval_ty T) v = t)"
        using ConstantsRange Elem
        by (simp add: DomConstants)

      have "lookup_vdecls_ty constants x = lookup_vdecls_ty (constants@globals) x"
        using lookup_vdecls_ty_def DomConstants
        by auto         
      hence "named_state_var_context (vbpl_absval_ty T) constants x = named_state_var_context (vbpl_absval_ty T) (constants@globals) x"
        using DomConstants DomConstantsGlobals
        by simp
      with LookupAux show ?thesis 
        unfolding initial_global_state_def
        by (simp add: domIff map_add_dom_app_simps(3))
    qed     
  qed

  moreover have "map_of constants x \<noteq> None"
    using ConstantsRange \<open>x \<in> _\<close>
    by (simp add: map_of_eq_None_iff)

  ultimately show "option_if (map_of constants x \<noteq> None) (?ns0 x) = ?ns1 x"
    by presburger  
qed

lemma boogie_axioms_state_restriction_aux:
  assumes "gs = initial_global_state T (constants@globals) Pr Tr \<omega>" and
          "C = const_repr Tr" and
         ConstTy: "\<And>c. lookup_vdecls_ty constants (const_repr Tr c) = Some (boogie_const_ty T c)" and 
         FieldProp: "field_tr_prop_full Pr constants T (field_translation Tr)" and
          Disj: "disjoint_list [{heap_var Tr}, {mask_var Tr}, ran (field_translation Tr), range (const_repr Tr)]" and          
          InjConstRepr: "inj (const_repr Tr)" and
          InjFieldTr: "inj_on (field_translation Tr) (dom (field_translation Tr))" and
          ConstantsRange:"set (map fst constants) = range (const_repr Tr) \<union> ran (field_translation Tr)" and 
         AxiomsSatGeneral: "\<And> ns. boogie_const_rel C (constants, []) ns \<Longrightarrow>  
                                  field_rel Pr (constants, []) (field_translation Tr) ns \<Longrightarrow>
                                  axioms_sat A (constants, []) \<Gamma> ns axioms"
  shows "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
proof -
  let ?ns = "(global_to_nstate (state_restriction gs constants))"
  have "boogie_const_rel (const_repr Tr) (constants, []) ?ns"    
    apply (rule boogie_const_rel_aux)
        apply (simp add: ConstTy)
       apply simp
      apply (rule Disj)
     apply (subst \<open>gs = _\<close>)
     apply (simp del: extend_named_state_var_context.simps)
     apply (rule initial_global_state_state_restriction[OF Disj ConstantsRange])
     apply simp
    by (rule InjConstRepr)

  moreover have "field_rel Pr (constants, []) (field_translation Tr) ?ns"
    apply (rule field_rel_aux)
    using FieldProp
    apply (fastforce simp: field_tr_prop_full_def)
        apply simp
       apply (rule Disj)
     apply (subst \<open>gs = _\<close> )
     apply (simp del: extend_named_state_var_context.simps)
     apply (rule initial_global_state_state_restriction[OF Disj ConstantsRange])
     apply simp
    by (rule InjFieldTr)

  ultimately show ?thesis
    using AxiomsSatGeneral \<open>C = _\<close>
    by simp
qed

lemma expr_sat_rewrite: "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool b); b\<rbrakk> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool True)"  
  by simp

lemma heap_upd_ty_preserved_2:
  assumes Wf: "wf_ty_repr_bpl T"
      and OldHeap: "type_of_vbpl_val T (AbsV (AHeap hb)) = TConSingle (THeapId T)"
      and FieldTy2: "type_of_vbpl_val T (AbsV (AField f)) = TCon (TFieldId T) [\<tau>, \<tau>']"
      and NewVal: "type_of_vbpl_val T v = \<tau>'"
    shows "type_of_vbpl_val T (AbsV (AHeap (hb ((r,f) \<mapsto> v)))) = TConSingle (THeapId T)" (is "?lhs = ?rhs")
proof -
  have "THeapId T \<noteq> TDummyId T"
    using tdummyid_fresh[OF Wf]
    by (metis UnI1 range_eqI)

  with type_of_val_not_dummy[OF OldHeap]
  have "(vbpl_absval_ty_opt T ((AHeap hb))) = Some (THeapId T, [])"
    by simp

  moreover from type_of_val_not_dummy[OF FieldTy2] 
  have "field_ty_fun_opt T f = Some (TFieldId T, [\<tau>, \<tau>'])"
    by simp
    
  ultimately show ?thesis
    using heap_upd_ty_preserved NewVal
    by (metis OldHeap type_of_val.simps(2) vbpl_absval_ty.simps)
qed   

lemma heap_upd_ty_preserved_2_basic:
  assumes OldHeap: "type_of_vbpl_val (ty_repr_basic A) (AbsV (AHeap hb)) = TConSingle ''HeapType''"
      and FieldTy2: "type_of_vbpl_val (ty_repr_basic A) (AbsV (AField f)) = TCon ''Field'' [\<tau>, \<tau>']"
      and  NewVal: "type_of_vbpl_val (ty_repr_basic A) v = \<tau>'"
    shows "type_of_vbpl_val (ty_repr_basic A) (AbsV (AHeap (hb ((r,f) \<mapsto> v)))) = TConSingle ''HeapType''"
  using heap_upd_ty_preserved_2[OF wf_ty_repr_basic]
  unfolding ty_repr_basic_def
  by (metis FieldTy2 NewVal OldHeap tcon_enum_to_id.simps(2) tcon_enum_to_id.simps(3) ty_repr_basic_def ty_repr_bpl.select_convs(1))

end