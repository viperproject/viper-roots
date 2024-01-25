theory RelArchive
imports StmtRel
begin 

lemma method_call_stmt_rel_archived:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and ConsistencyDownwardMono: "mono_prop_downward_ord StateCons"
      and "Pr = program_total ctxt_vpr"
          \<comment>\<open>We need to require state consistency, otherwise framing_exh cannot be established.\<close>
      and ConsistencyEnabled: "consistent_state_rel_opt (state_rel_opt Tr)"
      and MdeclSome:  "program.methods (program_total ctxt_vpr) m = Some mdecl"
      and MethodSpecsFramed: "vpr_method_spec_correct_total ctxt_vpr StateCons mdecl"
      and MethodSpecSubset:  "no_perm_assertion (method_decl.pre mdecl) \<and>                                    
                              no_perm_assertion (method_decl.post mdecl) \<and> 
                              no_unfolding_assertion (method_decl.pre mdecl) \<and>
                              no_unfolding_assertion (method_decl.post mdecl)"
      and OnlyArgsInPre: "\<And> x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow> x < length es"
      and "rtype_interp ctxt = []"
      and DomainTyRep: "domain_type TyRep = absval_interp_total ctxt_vpr"
      and TyInterpBplEq:   "type_interp ctxt = vbpl_absval_ty TyRep"
      and StateRelConcrete: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"              
      and ArgsAreVars: "list_all (\<lambda>x. \<exists>a. x = ViperLang.Var a) es" \<comment>\<open>simplifying assumption: only variables as arguments\<close>
      and "xs = map the_var es"
      and "set xs \<subseteq> dom (var_translation Tr)"
      and XsBplEq: "map (the \<circ> var_translation Tr) xs = xs_bpl"
      and "set ys \<subseteq> dom (var_translation Tr)"
      and YsBplEq: "map (the \<circ> var_translation Tr) ys = ys_bpl"
      and "set xs_bpl \<inter> set ys_bpl = {}" \<comment>\<open>simplifying assumption: targets and arguments do not clash\<close>
      and "distinct xs" \<comment>\<open>simplifying assumption: arguments are distinct\<close>
      and "distinct ys"
             \<comment>\<open>TODO: One could probably track the following fact on declared types also via the variable relation
                      where one ensures that the declared Viper and Boogie types match for variables related by
                      the variable relation.\<close>
      and LookupDeclRetsBpl: 
                     "list_all2 (\<lambda>y_bpl t_vpr. \<exists>t_bpl. vpr_to_bpl_ty TyRep t_vpr = Some t_bpl \<and>
                                           lookup_var_decl (var_context ctxt) y_bpl = Some (t_bpl, None))
                                ys_bpl (method_decl.rets mdecl)"
          \<comment>\<open> Since the rule only deals with variables in the arguments, well-definedness holds trivially
             ExpWfRel: "exprs_wf_rel Rdef ctxt_vpr StateCons P ctxt es \<gamma> \<gamma>def"\<close>
                   \<comment>\<open>simplifying assumption: unoptimized exhale and inhale\<close>
                        \<comment>\<open>"var_tr' = [[0..<length es] [\<mapsto>] rev xs_bpl]" and \<close>
      and "var_tr' = [[0..<length es] [\<mapsto>] xs_bpl]"
      and ExhalePreRel:
                      "\<And> fpred.                                                
                        stmt_rel 
                              (\<lambda>\<omega> ns.
                                 state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt \<omega> ns \<and>
                                 framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) \<omega> \<omega>)
                              (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) fpred) ctxt) 
                              ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                              (Exhale (method_decl.pre mdecl)) \<gamma> (BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)"
      and "cs_pre = havocs_list_bpl ys_bpl @ cs_pre_suffix"
      and "var_tr'' = Map.empty(upt 0 (length es+length ys) [\<mapsto>] (xs_bpl @ ys_bpl))"
      and InhalePostRel: 
          "\<And> fpred.  stmt_rel 
                        (\<lambda> \<omega> ns. 
                         state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt \<omega> ns \<and>
                         assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) \<omega> 
                        )
                        (state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) fpred) ctxt)
                        ctxt_vpr StateCons \<Lambda>_vpr P ctxt 
                        (Inhale (method_decl.post mdecl)) (BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre) \<gamma>'"
      shows "stmt_rel R (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr StateCons \<Lambda>_vpr P ctxt (MethodCall ys m es) \<gamma> \<gamma>'"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns" 
  \<comment>\<open>Prove various properties before showing the goal\<close>
  hence StateRel: "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt \<omega> ns"
    using StateRelConcrete
    by blast  

  hence "StateCons_t (get_total_full \<omega>)"
    using state_rel_consistent StateRel WfConsistency ConsistencyEnabled
    unfolding wf_total_consistency_def
    by blast
    
  have "es = map pure_exp.Var xs"
  proof (rule nth_equalityI)
    show "length es = length (map pure_exp.Var xs)"
      using \<open>xs = _\<close>
      by simp
  next
    fix i 
    assume "i < length es"
    show "es ! i = map pure_exp.Var xs ! i"
    proof -
      have "xs ! i = the_var (es ! i)"
        using \<open>i < _\<close> \<open>xs = _\<close>
        by simp
      moreover from ArgsAreVars obtain x where
          "es ! i = pure_exp.Var x"
        using \<open>i < _\<close>                 
        by (fastforce simp: list_all_length)

      ultimately show ?thesis
        using \<open>i < length es\<close> \<open>xs = _\<close> by auto
    qed            
  qed

  have "set xs_bpl \<subseteq> ran (var_translation Tr)"
  proof 
    fix x_bpl
    assume "x_bpl \<in> set xs_bpl"

    from this obtain x_vpr where "x_vpr \<in> set xs" and "the ((var_translation Tr) x_vpr) = x_bpl"
      using XsBplEq
      by auto

    moreover with \<open>set xs \<subseteq> dom (var_translation Tr)\<close> obtain x_bpl' where "var_translation Tr x_vpr = Some x_bpl'"
      by fast

    ultimately show "x_bpl \<in> ran (var_translation Tr)"
      by (simp add: ranI)
  qed

  have "set ys_bpl \<subseteq> ran (var_translation Tr)"
  proof 
    fix x_bpl
    assume "x_bpl \<in> set ys_bpl"

    from this obtain x_vpr where "x_vpr \<in> set ys" and "the ((var_translation Tr) x_vpr) = x_bpl"
      using YsBplEq
      by auto

    moreover with \<open>set ys \<subseteq> dom (var_translation Tr)\<close> obtain x_bpl' where "var_translation Tr x_vpr = Some x_bpl'"
      by fast

    ultimately show "x_bpl \<in> ran (var_translation Tr)"
      by (simp add: ranI)
  qed

  have "distinct xs_bpl" and "distinct ys_bpl"
  proof -
    have "inj_on (var_translation Tr) (dom (var_translation Tr))"
    using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
    unfolding store_rel_def
    by blast

    thus "distinct ys_bpl" and "distinct xs_bpl"
      using XsBplEq YsBplEq distinct_map_the_inj_on_subset \<open>distinct xs\<close> \<open>distinct ys\<close> \<open>set xs \<subseteq> _\<close> \<open>set ys \<subseteq> _\<close> 
      by blast+
  qed

  \<comment>\<open>Show the goal\<close>

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (MethodCall ys m es) \<omega> res"

  thus "rel_vpr_aux (state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt) P ctxt \<gamma> \<gamma>' ns res"
  proof (cases)
    case (RedMethodCall v_args mdecl' v_rets resPre resPost)
     \<comment>\<open>All arguments evaluate normally\<close>

    from MdeclSome RedMethodCall have "mdecl = mdecl'"
      by force

    have ListAllArgsEvalVpr: "list_all2 (\<lambda>e v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) es v_args"
      using red_pure_exps_total_list_all2 RedMethodCall
      by blast

    hence "length es = length v_args"
      by (simp add: list_all2_lengthD)

    have "length xs = length xs_bpl"
      using XsBplEq
      by auto

    have "length xs_bpl = length v_args"
      using RedMethodCall \<open>xs = _\<close> XsBplEq
      by (metis ListAllArgsEvalVpr length_map list_all2_lengthD)    

    have "length ys = length ys_bpl"
      using YsBplEq by auto

    hence "length ys_bpl = length v_rets"
      using RedMethodCall
      unfolding vals_well_typed_def
      by (metis length_map list_all2_lengthD)

    note LengthEqs = \<open>length es = length v_args\<close> \<open>length xs = length xs_bpl\<close> \<open>length xs_bpl = length v_args\<close>
                     \<open>length ys = length ys_bpl\<close> \<open>length ys_bpl = length v_rets\<close>

    have "list_all2 (\<lambda>x v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>ViperLang.Var x; \<omega>\<rangle> [\<Down>]\<^sub>t Val v) xs v_args"
    proof (rule list_all2_all_nthI)
      show "length xs = length v_args"
        using LengthEqs
        by simp
    next
      fix i
      assume "i < length xs"
     
      hence *: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>es ! i; \<omega>\<rangle> [\<Down>]\<^sub>t Val (v_args ! i)"
        using ListAllArgsEvalVpr LengthEqs
        by (simp add: list_all2_conv_all_nth)

      have "es ! i = pure_exp.Var (xs ! i)"
        using \<open>i < _\<close> \<open>es = _\<close>
        by auto
  
      thus "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>pure_exp.Var (xs ! i);\<omega>\<rangle> [\<Down>]\<^sub>t Val (v_args ! i)"
        using *
        by simp
    qed        

    hence StoreValArgsVpr: "list_all2 (\<lambda>x v. get_store_total \<omega> x = Some v) xs v_args"
      using TotalExpressions.RedVar_case
      by (metis (mono_tags, lifting) list_all2_mono)

    have StoreRelAuxArgs: 
      "list_all2 (\<lambda> x_vpr x_bpl. store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns x_vpr x_bpl) xs xs_bpl"
    proof (rule list_all2_all_nthI)
      fix i
      assume "i < length xs"

      let ?x_vpr = "xs ! i"
      let ?x_bpl = "xs_bpl ! i"


      have "var_translation Tr (xs ! i) = Some (xs_bpl ! i)"
        using XsBplEq \<open>set xs \<subseteq> dom _\<close> \<open>i < _\<close> nth_mem
        by fastforce

      thus "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns ?x_vpr ?x_bpl"
        using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
        unfolding store_var_rel_aux_def store_rel_def
        by blast 
    next
      show "length xs = length xs_bpl"
        using XsBplEq by auto
    qed

    have ValRelArgs: "list_all2 
          (\<lambda> v_vpr x_bpl. lookup_var (var_context ctxt) ns x_bpl = Some (val_rel_vpr_bpl v_vpr) \<and>
                          (\<exists>ty_bpl. lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl \<and> 
                          type_of_val (type_interp ctxt) (val_rel_vpr_bpl v_vpr) = ty_bpl)) 
          v_args 
          xs_bpl"
    proof (rule list_all2_all_nthI)
      show "length v_args = length xs_bpl"
        by (simp add: \<open>length xs_bpl = length v_args\<close>)
    next
      fix i 
      assume "i < length v_args"

      with \<open>length xs_bpl = length v_args\<close> have
        "store_var_rel_aux (type_interp ctxt) (var_context ctxt) \<omega> ns (xs ! i) (xs_bpl ! i)"
        using StoreRelAuxArgs
        by (metis list_all2_nthD2)

      thus "lookup_var (var_context ctxt) ns (xs_bpl ! i) = Some (val_rel_vpr_bpl (v_args ! i)) \<and>
         (\<exists>ty_bpl. lookup_var_ty (var_context ctxt) (xs_bpl ! i) = Some ty_bpl \<and> 
         type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! i)) = ty_bpl)"        
        using StoreValArgsVpr \<open>i < _\<close>
        unfolding store_var_rel_aux_def
        by (simp add: list_all2_conv_all_nth)
    qed

      \<comment>\<open>Show state rel with new var translation, which is required to use the exhale relation on the
         precondition\<close>

    let ?\<omega>0 = "\<lparr>get_store_total = shift_and_add_list_alt Map.empty v_args, 
                get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                get_total_full = get_total_full \<omega>\<rparr>"

    let ?fpred  = "(\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))"

    note ExhalePreRelInst = ExhalePreRel
    (*note InhalePostRelInst = InhalePostRel[OF \<open>set ls = _\<close> \<open>length ls = length ?ps\<close>]*)
    let ?AuxPredPre = "(map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) ?fpred)"
    let ?RCall = "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr' \<rparr>) ?AuxPredPre ctxt"
    have StateRelDuringCall: "?RCall ?\<omega>0 ns"
    proof -
      from var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] have 
        *: "ran (var_translation Tr) \<inter> dom AuxPred = {}"
        by blast

      have AuxSub: "map_upd_set AuxPred (ran (var_translation Tr) - set xs_bpl) ?fpred \<subseteq>\<^sub>m
            map_upd_set AuxPred (ran (var_translation Tr)) ?fpred"
        unfolding map_upd_set_def
        apply (rule map_add_le_dom_disjoint)
        using *
         apply (smt (verit) disjoint_iff_not_equal domIff)
        by (smt (verit) Diff_iff domIff map_le_def)

      have StoreRel: "store_rel (type_interp ctxt) (var_context ctxt) var_tr' ?\<omega>0 ns"
      proof (rule store_relI)
        \<comment>\<open>Could adjust state rel with an additional parameter that switches off injectivity on the variable translation.
           Then, one could support multiple arguments being the same variable. Injectivity is useful only if there
           are changes to the local Viper variables.\<close>
        show "inj_on var_tr' (dom var_tr')"
          unfolding \<open>var_tr' = _\<close>
          using inj_on_upt_distinct \<open>distinct xs_bpl\<close> LengthEqs
          by fastforce
      next
        fix x_vpr x_bpl
        assume VarTrSome: "var_tr' x_vpr = Some x_bpl" 
        with \<open>var_tr' = _\<close>
        have "x_vpr \<in> set [0..<length es]"
          by (metis Some_Some_ifD map_upds_apply_nontin)
        hence "x_vpr < length es"
          by simp
        hence "x_vpr < length v_args"
          using ListAllArgsEvalVpr
          using list_all2_lengthD by force
        with ValRelArgs
        have *:"lookup_var (var_context ctxt) ns (xs_bpl ! x_vpr) = Some (val_rel_vpr_bpl ( v_args ! x_vpr))"
          using list_all2_nthD 
          by blast
        
        have "x_bpl = xs_bpl ! x_vpr"
        proof -
          from \<open>x_vpr \<in> _\<close> have *: "x_vpr = [0..<length es] ! x_vpr"
            by simp
          thus ?thesis
            using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys = "xs_bpl"]
                  LengthEqs VarTrSome \<open>x_vpr < length v_args\<close> \<open>var_tr' = _\<close> 
            by auto
        qed          

        hence "x_bpl \<in> set xs_bpl"
          using \<open>x_vpr < length v_args\<close> \<open>length xs_bpl = length v_args\<close>
          by force

        from ValRelArgs obtain \<tau>_bpl where
          XBplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some \<tau>_bpl" 
                  "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! x_vpr)) = \<tau>_bpl"
          using  \<open>x_bpl = _\<close> \<open>x_vpr < length v_args\<close> list_all2_nthD by blast          

        show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>0 ns x_vpr x_bpl"
          unfolding store_var_rel_aux_def
        proof ((rule exI)+, intro conjI)
          show "get_store_total ?\<omega>0 x_vpr = Some (v_args ! x_vpr)"
            using shift_and_add_list_alt_lookup_1 \<open>x_vpr < length v_args\<close>
            by auto
        next
          from * \<open>x_bpl = _\<close> 
          show "lookup_var (var_context ctxt) ns x_bpl = Some (val_rel_vpr_bpl (v_args ! x_vpr))"
            by simp  
        next
          show "lookup_var_ty (var_context ctxt) x_bpl = Some \<tau>_bpl"
            using XBplTy
            by blast
        next
          show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_args ! x_vpr)) = \<tau>_bpl"
            using XBplTy
            by blast
        qed
      qed      

      have "ran var_tr' = set xs_bpl"
        using map_upds_upt_ran LengthEqs
        unfolding \<open>var_tr' = _\<close>
        by force
  
      have "state_rel Pr StateCons TyRep (Tr \<lparr> var_translation := Map.empty \<rparr>) ?AuxPredPre ctxt \<omega> \<omega> ns"
        apply (rule state_rel_aux_pred_remove)
         apply (rule state_rel_transfer_var_tr_to_aux_pred[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]])
          apply simp
          apply simp
         apply simp
        by (rule AuxSub)        

      thus ?thesis
      proof (rule state_rel_store_update[where ?f= var_tr'])
        show "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<Longrightarrow> StateCons ?\<omega>0"
          apply (rule total_consistencyI[OF WfConsistency])
           apply (insert \<open>StateCons_t (get_total_full \<omega>)\<close>)
           apply (solves \<open>simp\<close>)
          apply simp
          by (metis option.distinct(1) option.inject)           
      next
        show "binder_state ns = Map.empty"
          using state_rel_state_well_typed[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>], simplified state_well_typed_def]
          by simp
      next
        show "store_rel (type_interp ctxt) (var_context ctxt) var_tr' ?\<omega>0 ns"
          using StoreRel
          by blast
      qed (insert  var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] \<open>set xs_bpl \<subseteq> _\<close> \<open>ran var_tr' = _\<close>,
           auto simp add: map_upd_set_lookup_2)
    qed

    have StoreSameOnArgs: "\<And>x. x \<in> free_var_assertion (method_decl.pre mdecl) \<Longrightarrow>
               shift_and_add_list_alt Map.empty (v_args @ v_rets) x = 
               shift_and_add_list_alt Map.empty v_args x" (is "\<And>x. _ \<Longrightarrow> ?store_args_rets x = ?store_args x")
    proof -
      fix x 
      assume "x \<in> free_var_assertion (method_decl.pre mdecl)"
      hence *: "x < length v_args"
        using OnlyArgsInPre LengthEqs
        by auto
      hence **: "x < length (v_args @ v_rets)"
        by simp

      thus "?store_args_rets x = ?store_args x"
      proof -
        have "shift_and_add_list_alt Map.empty (v_args @ v_rets) x = Some ((v_args @ v_rets) ! x)"
          using shift_and_add_list_alt_lookup_1[OF **]
          by blast
        also have "... = Some (v_args ! x)"
          using \<open>x < length v_args\<close>
          by (simp add: nth_append)
        finally show "shift_and_add_list_alt Map.empty (v_args @ v_rets) x = shift_and_add_list_alt Map.empty v_args x"
          using shift_and_add_list_alt_lookup_1[OF \<open>x < length v_args\<close>]
          by simp
      qed
    qed
    
    have AssertionFramingInit: "framing_exh ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0 ?\<omega>0"
    proof -
      let ?\<omega>0_rets_empty = "\<lparr> get_store_total = shift_and_add_list_alt Map.empty (v_args@v_rets), 
                    get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                    get_total_full = (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>"
      let ?\<omega>0_empty = "?\<omega>0\<lparr> get_total_full := (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>"

      have "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty"
        unfolding assertion_framing_state_def
      proof (rule allI, rule impI)+
        fix res
        assume "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty res"           
        moreover have "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (shift_and_add_list_alt Map.empty (v_args@v_rets))"
          apply (rule vpr_store_well_typed_append)
          using RedMethodCall \<open>mdecl = mdecl'\<close>
          by (auto dest: vals_well_typed_same_lengthD)
        moreover have "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full ?\<omega>0_rets_empty)"
          using state_rel_heap_var_rel[OF StateRel] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
          unfolding heap_var_rel_def
          by simp
        moreover have "is_empty_total_full ?\<omega>0_rets_empty"
          by (simp add: is_empty_total_full_def is_empty_total_def)
        ultimately show "res \<noteq> RFailure"
          using MethodSpecsFramed
          unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
          by (metis full_total_state.select_convs(1))          
      qed

      hence AssertionFraming_\<omega>0'_only_args: "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_empty"
     \<comment>\<open>using that return variables do not appear in precondition\<close>
        apply (rule assertion_framing_store_same_on_free_var)
        apply (insert StoreSameOnArgs, insert MethodSpecSubset)
        by auto

      show ?thesis        
      proof (rule framing_exhI[OF _ _ AssertionFraming_\<omega>0'_only_args])
        show "StateCons ?\<omega>0"
          using StateRelDuringCall state_rel_consistent ConsistencyEnabled
          by fastforce
      next
        show "valid_heap_mask (get_mh_total_full ?\<omega>0)"
          using StateRelDuringCall state_rel_wf_mask_simple
          by fast
      next        
        show "?\<omega>0_empty \<oplus> ?\<omega>0 = Some ?\<omega>0"
          by (rule plus_full_total_state_zero_mask) simp_all          
      next
        show "?\<omega>0 \<succeq> ?\<omega>0"
          by (simp add: succ_refl)
      qed
    qed

    note RCallPre = conjI[OF \<open>?RCall ?\<omega>0 ns\<close> AssertionFramingInit]

    show ?thesis 
    proof (cases "resPre")
      case RMagic
      then show ?thesis \<comment>\<open>trivial case\<close>
        using RedMethodCall
        by (auto intro: rel_vpr_aux_intro)
    next
      case RFailure
      with RedMethodCall \<open>mdecl = _\<close> 
      obtain c where 
          "red_ast_bpl P ctxt (\<gamma>, Normal ns) c" and
          "snd c = Failure"
        using stmt_rel_failure_elim[OF ExhalePreRelInst RCallPre]
        by blast
      moreover have "res = RFailure"
        using RFailure RedMethodCall
        by argo
      ultimately show ?thesis         
        using red_ast_bpl_transitive
        by (blast intro: rel_vpr_aux_intro)                  
    next
      case (RNormal \<omega>pre)
      let ?\<gamma>pre = "(BigBlock name_pre cs_pre str_pre tr_pre, cont_pre)"
      from RNormal RedMethodCall \<open>mdecl = _\<close>
      obtain nspre where
        RedBplPre: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>pre, Normal nspre)" and
        "?RCall \<omega>pre nspre"
        using stmt_rel_normal_elim[OF ExhalePreRelInst RCallPre]
        by blast

      let ?\<omega>havoc = "\<lparr> get_store_total = (shift_and_add_list_alt Map.empty (v_args@v_rets)), 
                       get_trace_total = [old_label \<mapsto> get_total_full \<omega>], 
                       get_total_full = get_total_full \<omega>pre \<rparr>"
 
      note InhalePostRelInst = InhalePostRel

      let ?AuxPredPost = "(map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) ?fpred)"
      let ?RCallPost = "state_rel_def_same Pr StateCons TyRep (Tr\<lparr> var_translation := var_tr'' \<rparr>) ?AuxPredPost ctxt"

      let ?v_rets_bpl = "map (val_rel_vpr_bpl) v_rets"

      let ?nshavoc = "update_var_list (var_context ctxt) nspre ys_bpl ?v_rets_bpl"

      have *: "length ys_bpl = length (map val_rel_vpr_bpl v_rets)"
      proof -
          have "length ys = length ys_bpl"
            using YsBplEq by auto
          moreover have "length ys = length v_rets"
            using RedMethodCall
            unfolding vals_well_typed_def
            by (metis length_map list_all2_lengthD)
          ultimately show ?thesis
            by simp
        qed

      have YsBplCorrectTypes: "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) 
                                     ys_bpl 
                                     (map val_rel_vpr_bpl v_rets)"
        proof (rule list_all2_all_nthI[OF *])        
          fix n
          assume "n < length ys_bpl"
          
          from this obtain t_bpl where 
            "vpr_to_bpl_ty TyRep ((rets mdecl) ! n) = Some t_bpl"
            "lookup_var_decl (var_context ctxt) (ys_bpl ! n) = Some (t_bpl, None)"
            using LookupDeclRetsBpl
            by (blast dest: list_all2_nthD)

          moreover have "get_type (absval_interp_total ctxt_vpr) (v_rets ! n) = (rets mdecl) ! n"
            using * \<open>n < _\<close> \<open>vals_well_typed (absval_interp_total ctxt_vpr) v_rets (rets mdecl')\<close>
            unfolding vals_well_typed_def  \<open>mdecl = mdecl'\<close>
            by (metis length_map nth_map)           

          ultimately 
         show "lookup_var_decl (var_context ctxt) (ys_bpl ! n) = 
                 Some (type_of_val (type_interp ctxt) (map val_rel_vpr_bpl v_rets ! n), None)"
           apply simp
           using DomainTyRep vpr_to_bpl_val_type TyInterpBplEq 
           by (metis "*" \<open>n < length ys_bpl\<close> list_update_id list_update_same_conv map_update)
       qed

      have
        RedBplHavoc: "red_ast_bpl P ctxt (?\<gamma>pre, Normal nspre) ((BigBlock name_pre cs_pre_suffix str_pre tr_pre, cont_pre), Normal ?nshavoc)"
        unfolding \<open>cs_pre = _\<close>
      proof (rule red_ast_bpl_havoc_list, simp add: \<open>rtype_interp ctxt = _\<close>)   
        show "list_all2 (\<lambda>x v. lookup_var_decl (var_context ctxt) x = Some (type_of_val (type_interp ctxt) v, None)) ys_bpl (map val_rel_vpr_bpl v_rets)"
          using YsBplCorrectTypes
          by simp
      qed

     have "ran var_tr'' = set xs_bpl \<union> set ys_bpl"
       using LengthEqs map_upds_ran_distinct
       unfolding \<open>var_tr'' = _\<close>
       by (simp add: map_upds_upt_ran)

     from \<open>?RCall \<omega>pre nspre\<close> have
       "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>var_translation := var_tr'\<rparr>)
          (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl)) (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x)))) ctxt \<omega>pre nspre"
       apply (rule state_rel_aux_pred_remove)
       apply (rule map_upd_set_subset)
        apply blast
       using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
       by blast

     hence
      "?RCallPost ?\<omega>havoc ?nshavoc"
     proof (rule state_rel_store_update[where ?f=var_tr''])
       fix x
       assume "x \<notin> ran var_tr''"
       hence "x \<notin> set ys_bpl"
         using \<open>ran var_tr'' = _\<close>
         by blast

       thus "lookup_var (var_context ctxt) nspre x = 
             lookup_var (var_context ctxt) (update_var_list (var_context ctxt) nspre ys_bpl (map val_rel_vpr_bpl v_rets)) x"
         using lookup_update_var_list_other LengthEqs
         by (metis length_map)
     next
       show "store_rel (type_interp ctxt) (var_context ctxt) var_tr'' ?\<omega>havoc ?nshavoc"
       proof (rule store_relI)
         show "inj_on var_tr'' (dom var_tr'')"
         proof -
           have *: "distinct (xs_bpl @ ys_bpl)"
             using \<open>distinct xs_bpl\<close> \<open>distinct ys_bpl\<close> \<open>set xs_bpl \<inter> set ys_bpl = {}\<close>
                   distinct_append
             by blast

           thus ?thesis
             using LengthEqs inj_on_upt_distinct[OF *]
             unfolding \<open>var_tr'' = _\<close>
             by simp
         qed        
       next
         fix var_vpr var_bpl
         assume VarTrSome: "var_tr'' var_vpr = Some var_bpl"

         with \<open>var_tr'' = _\<close>
         have "var_vpr \<in> dom [[0..<length es + length ys] [\<mapsto>] xs_bpl @ ys_bpl]"
           by (fastforce intro: domI)
         hence "var_vpr < length es + length ys"
           using map_upds_dom LengthEqs
           by simp

         hence "var_vpr = [0..<length es + length ys] ! var_vpr"
           by simp

         from VarTrSome \<open>var_tr'' = _\<close> 
         have VarBplEqNth: "var_bpl = (xs_bpl @ ys_bpl) ! var_vpr"
           using LengthEqs \<open>var_vpr < length es + length ys\<close>
                 map_upds_distinct_nth[OF distinct_upt \<open>var_vpr = _\<close>, where ?m=Map.empty and ?ys="xs_bpl @ ys_bpl"]
           by force

         have HavocStoreVprLookupAux: "get_store_total ?\<omega>havoc var_vpr = Some ((v_args @ v_rets) ! var_vpr)"
             apply (simp add: shift_and_add_list_alt_lookup)
             using \<open>var_vpr < _\<close> LengthEqs
             by linarith

         show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>havoc ?nshavoc var_vpr var_bpl"
         proof (cases "var_vpr < length es")
           case True
             \<comment>\<open>Prove facts properties \<^term>\<open>var_bpl\<close>\<close>
             hence "var_bpl = xs_bpl ! var_vpr"
               using VarBplEqNth LengthEqs
               by (simp add: nth_append) 
             hence "var_bpl \<in> set xs_bpl"
               using LengthEqs True
               by simp
             hence LookupVarBplAux: "lookup_var (var_context ctxt) ?nshavoc var_bpl = lookup_var (var_context ctxt) nspre var_bpl"
               using \<open>set xs_bpl \<inter> set ys_bpl = {}\<close> lookup_update_var_list_other LengthEqs
               by (metis Int_iff empty_iff length_map)

             have "var_tr' var_vpr = Some (xs_bpl ! var_vpr)"
             proof -
               have *: "var_vpr = [0..<length es] ! var_vpr"
                 using True
                 by simp
               show ?thesis
               unfolding \<open>var_tr' = _\<close>
               using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys="xs_bpl"]
                     LengthEqs True
               by fastforce
             qed

             with state_rel_store_rel[OF \<open>?RCall \<omega>pre nspre\<close>] 
             obtain ty_bpl where
                  VarBplValRel: "lookup_var (var_context ctxt) nspre var_bpl = Some (val_rel_vpr_bpl (the (get_store_total \<omega>pre var_vpr)))" and
                  LookupTyVarBpl: "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl" and
                  TypeOfValRel:  "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (the (get_store_total \<omega>pre var_vpr))) = ty_bpl"
               using \<open>var_bpl = xs_bpl ! var_vpr\<close>
               unfolding store_rel_def
               by fastforce

             from RedMethodCall have \<comment>\<open>exhale does not change the store\<close>
                 StorePreVprEq: "get_store_total \<omega>pre = shift_and_add_list_alt Map.empty v_args"
               using \<open>resPre = _\<close> exhale_only_changes_total_state
               by force
                 
             hence StorePreVprEqLookup: "get_store_total \<omega>pre var_vpr = Some (v_args ! var_vpr)"
               using True LengthEqs
               by (simp add: shift_and_add_list_alt_lookup_1)

             show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) ?\<omega>havoc ?nshavoc var_vpr var_bpl"
               unfolding store_var_rel_aux_def
             proof ( (rule exI)+, intro conjI, rule HavocStoreVprLookupAux)
               from StorePreVprEqLookup
               show "lookup_var (var_context ctxt) ?nshavoc var_bpl =
                     Some (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr))" 
               using VarBplValRel LookupVarBplAux True LengthEqs
               by (simp add: nth_append)
             next
               show "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl"
                 by (rule LookupTyVarBpl)
             next
               show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr)) = ty_bpl"
                 using TypeOfValRel StorePreVprEqLookup LengthEqs
                 by (metis True nth_append option.sel)
             qed
         next
           case False
           hence VarVprLength: "var_vpr \<ge> length es \<and> var_vpr < length es + length ys"
             using \<open>var_vpr < _\<close>
             by simp

           hence "(xs_bpl @ ys_bpl) ! var_vpr = ys_bpl ! (var_vpr - length xs_bpl)"
             using LengthEqs
             by (simp add: nth_append)

           hence VarBplYsBplNth: "var_bpl = ys_bpl ! (var_vpr - length xs_bpl)" (is "_ = _ ! ?id_bpl")
             using \<open>var_bpl  = _\<close>
             by blast

           hence "var_bpl \<in> set ys_bpl"
             using VarVprLength LengthEqs
             by fastforce

           from VarBplYsBplNth obtain t_bpl where 
              LookupDeclVarBpl: 
                  "vpr_to_bpl_ty TyRep ((rets mdecl) ! ?id_bpl) = Some t_bpl \<and> 
                   lookup_var_decl (var_context ctxt) var_bpl = Some (t_bpl, None)"
             using list_all2_nthD[OF LookupDeclRetsBpl] VarVprLength LengthEqs
             by fastforce

           have *: "((v_args @ v_rets) ! var_vpr) = v_rets ! (var_vpr - length xs_bpl)" (is "_ = ?val_vpr")
             using LengthEqs VarVprLength
             by (simp add: nth_append)

           have "?id_bpl < length ys_bpl"
             using VarVprLength LengthEqs
             by linarith

           show ?thesis
             unfolding store_var_rel_aux_def
           proof ((rule exI)+, intro conjI, rule HavocStoreVprLookupAux)
             show "lookup_var (var_context ctxt) ?nshavoc var_bpl = Some (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr))" (is "?lhs = ?rhs")
             proof -

               have "?lhs = [ ys_bpl [\<mapsto>] (map val_rel_vpr_bpl v_rets) ] var_bpl"
                 apply (rule lookup_update_var_list_same[ OF \<open>var_bpl \<in> _\<close> ])
                 using LengthEqs
                 by simp
               also have "... = Some ((map val_rel_vpr_bpl v_rets) ! (var_vpr - length xs_bpl))"
                 apply (rule map_upds_distinct_nth)
                 using \<open>distinct ys_bpl\<close>
                    apply simp
                   apply (simp add: VarBplYsBplNth)
                 using LengthEqs VarVprLength
                  apply fastforce
                 using LengthEqs
                 by simp

               finally show ?thesis                 
                 using * VarVprLength LengthEqs nth_map
                 by fastforce                 
             qed
           next
             show "lookup_var_ty (var_context ctxt) var_bpl = Some t_bpl"
               using LookupDeclVarBpl
               by (simp add: lookup_var_decl_ty_Some)
           next         
             from YsBplCorrectTypes
             have "lookup_var_decl (var_context ctxt) (ys_bpl ! ?id_bpl) = Some (type_of_val (type_interp ctxt) (val_rel_vpr_bpl ?val_vpr), None)"
               using \<open>?id_bpl < _\<close>
               by (simp add: list_all2_conv_all_nth rev_map)

             hence "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ?val_vpr) = t_bpl" 
               using LookupDeclVarBpl VarBplYsBplNth
               by simp

             thus "type_of_val (type_interp ctxt) (val_rel_vpr_bpl ((v_args @ v_rets) ! var_vpr)) = t_bpl"
               using *
               by simp
           qed
         qed
       qed
     next
       note aux_disj_thms = var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]] 
              \<open>set xs_bpl \<subseteq> _\<close> \<open>set ys_bpl \<subseteq> _\<close> \<open>ran var_tr'' = _\<close>
       show "ran var_tr'' \<inter>
            ({heap_var (Tr\<lparr>var_translation := var_tr'\<rparr>), heap_var_def (Tr\<lparr>var_translation := var_tr'\<rparr>)} \<union>
             {mask_var (Tr\<lparr>var_translation := var_tr'\<rparr>), mask_var_def (Tr\<lparr>var_translation := var_tr'\<rparr>)} \<union>
             ran (field_translation (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<union>
             range (const_repr (Tr\<lparr>var_translation := var_tr'\<rparr>)) \<union>
             dom (map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl))
                   (\<lambda>x. pred_eq (the (lookup_var (var_context ctxt) ns x))))) = {}"
         apply simp
         apply (intro conjI)

         using aux_disj_thms
             apply blast
         using aux_disj_thms
            apply blast
         using aux_disj_thms
           apply blast
         using aux_disj_thms
          apply blast
         using aux_disj_thms
         by (auto simp add: map_upd_set_dom)
     next 
       have "StateCons_t (get_total_full \<omega>pre)"
       proof -
         have "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr'\<rparr>))"
           by (simp add: ConsistencyEnabled)
         with state_rel_consistent[OF \<open>?RCall \<omega>pre nspre\<close>]  WfConsistency 
         show ?thesis
           unfolding wf_total_consistency_def
           by blast
       qed                  

       show "StateCons
              \<lparr> get_store_total = shift_and_add_list_alt Map.empty (v_args @ v_rets), 
                get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                get_total_full = get_total_full \<omega>pre \<rparr>"
         apply (rule total_consistencyI[OF WfConsistency])
          apply (simp add: \<open>StateCons_t (get_total_full \<omega>pre)\<close>)          
         apply simp
         by (fastforce  split: if_split_asm intro: \<open>StateCons_t (get_total_full \<omega>)\<close> )         
     next
       fix x
       assume "map_of (snd (var_context ctxt)) x \<noteq> None"
       thus "global_state ?nshavoc x = global_state nspre x"
         using global_state_update_var_list_local 
         by blast
     next
       show "old_global_state ?nshavoc = old_global_state nspre"
         by (simp add: update_var_list_old_global_state_same)
     next
       show "binder_state ?nshavoc = Map.empty"
         using state_rel_state_well_typed[OF \<open>?RCall \<omega>pre nspre\<close>, simplified state_well_typed_def]
         by (simp add: update_var_list_binder_state_same)
     qed simp_all

      from RedMethodCall RNormal have 
         RedInh: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Inhale (method_decl.post mdecl')) ?\<omega>havoc resPost" and
         "res = map_stmt_result_total (reset_state_after_call ys v_rets \<omega>) resPost"
        by blast+

      have PostFramed: "assertion_framing_state ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>havoc"       
      proof -
        \<comment>\<open>We know that the postcondition is framed w.r.t. the precondition. More precisely, the assumption
           tells us that \<^emph>\<open>if\<close> the precondition is normally inhaled from an empty state \<^term>\<open>\<omega>_empty\<close> to reach \<^term>\<open>\<omega>inh\<close>, then the postcondition
           is framed in any well-typed state whose store is the same as \<^term>\<open>get_store_total \<omega>_empty\<close> and whose old state is given 
           by \<^term>\<open>\<omega>inh\<close>.

           We first show that we can inhale the precondition from an empty state to reach \<^term>\<open>RNormal (?\<omega>0 \<ominus> \<omega>pre)\<close>
           using the fact that the precondition was successfully exhaled from \<^term>\<open>?\<omega>0\<close> to reach \<^term>\<open>\<omega>pre\<close>.
           From this, we will then learn that the postcondition is framed in
           \<^term>\<open>?\<omega>havoc \<lparr> get_trace_total := [old_label \<mapsto> get_total_full (?\<omega>0 \<ominus> \<omega>pre)] \<rparr> \<close>.
           From this we conclude the proof with a monotonicity argument (using that 
           \<^prop>\<open>get_total_full ?\<omega>0 \<succeq> get_total_full (?\<omega>0 \<ominus> \<omega>pre)\<close>)\<close>        

        let ?\<omega>0_rets =  "?\<omega>0\<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"
        let ?\<omega>0_rets_empty = "?\<omega>0\<lparr>   get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets),
                                      get_total_full := (get_total_full \<omega>)\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr> \<rparr>" 

        let ?\<omega>pre_rets = "\<omega>pre \<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"
        from \<open>red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Exhale (method_decl.pre mdecl')) ?\<omega>0 resPre\<close> 
        obtain \<omega>pre_exh_aux where
          RedExh: "red_exhale ctxt_vpr StateCons ?\<omega>0 (method_decl.pre mdecl') ?\<omega>0 (RNormal \<omega>pre_exh_aux)"
          using \<open>resPre = _\<close>
          by (cases) auto 

        hence "?\<omega>0 \<succeq> \<omega>pre_exh_aux"
          using exhale_normal_result_smaller
          by blast

        let ?\<omega>pre_exh_aux_rets = "\<omega>pre_exh_aux\<lparr> get_store_total := shift_and_add_list_alt Map.empty (v_args@v_rets) \<rparr>"

        have "?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets"
        proof -
          have TraceEq: "get_trace_total ?\<omega>0_rets = get_trace_total ?\<omega>pre_exh_aux_rets"
            using exhale_only_changes_total_state_aux[OF RedExh]
            by auto

          have *: "?\<omega>0_rets \<ge> ?\<omega>pre_exh_aux_rets"
            apply (rule less_eq_full_total_stateI)
               apply simp
            using TraceEq
              apply simp
              apply simp
            using full_total_state_succ_implies_gte[OF \<open>?\<omega>0 \<succeq> \<omega>pre_exh_aux\<close>] less_eq_full_total_stateD
            apply fastforce
            by simp
          show ?thesis 
            using full_total_state_gte_implies_succ[OF *] TraceEq
            by argo
        qed

        have StoreWellTy: "vpr_store_well_typed (absval_interp_total ctxt_vpr) (nth_option (method_decl.args mdecl @ rets mdecl)) (get_store_total ?\<omega>0_rets_empty)"
          apply simp
          apply (rule vpr_store_well_typed_append)
          using RedMethodCall \<open>mdecl = mdecl'\<close>
          by (auto dest: vals_well_typed_same_lengthD)
        moreover have HeapWellTy: "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full ?\<omega>0_rets_empty)"
          using state_rel_heap_var_rel[OF StateRel] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
          unfolding heap_var_rel_def
          by simp
        moreover have EmptyState: "is_empty_total_full ?\<omega>0_rets_empty"
          unfolding is_empty_total_full_def is_empty_total_def
          by auto
        moreover have "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl) ?\<omega>0_rets_empty (RNormal (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets))"
        proof -
          have RedExhRets: "red_exhale ctxt_vpr StateCons ?\<omega>0_rets (method_decl.pre mdecl') ?\<omega>0_rets (RNormal ?\<omega>pre_exh_aux_rets)"
            apply (rule exhale_same_on_free_var[OF RedExh]) \<comment>\<open>using that the return variables do not appear in the precondition\<close>
            using StoreSameOnArgs \<open>mdecl = _\<close> MethodSpecSubset
            by auto

          moreover have SumDefined: "?\<omega>0_rets_empty \<oplus> (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = Some (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)"
          proof -
            have "get_h_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = get_h_total_full ?\<omega>0_rets"
            using minus_full_total_state_only_mask_different
            by blast
            hence *: "get_h_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) = get_h_total_full ?\<omega>0_rets_empty"
              by simp

            show ?thesis
              apply (rule plus_full_total_state_zero_mask)
               apply (simp add: minus_full_total_state_only_mask_different)
              using *
               apply simp
              by simp
          qed
          moreover have PreFramed: "assertion_framing_state ctxt_vpr StateCons (method_decl.pre mdecl') ?\<omega>0_rets_empty"
            unfolding assertion_framing_state_def \<comment>\<open>using that the precondition is self-framing\<close>
          proof (rule allI | rule impI)+
            fix res
            assume "red_inhale ctxt_vpr StateCons (method_decl.pre mdecl') ?\<omega>0_rets_empty res"
            with StoreWellTy HeapWellTy EmptyState
            show "res \<noteq> RFailure"
              using MethodSpecsFramed
              unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def \<open>mdecl = _\<close>
              by blast
          qed
          moreover have ValidRes: "StateCons (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets) \<and> valid_heap_mask (get_mh_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets))"
          proof (rule conjI)
            let ?\<omega>minus = "?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets"
            have gt_\<omega>minus: "?\<omega>0_rets \<succeq> ?\<omega>minus"
            using \<open>?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets\<close> minus_smaller 
            by auto

            show "StateCons ?\<omega>minus"
            proof (rule mono_prop_downwardD[OF wf_total_consistency_trace_mono_downwardD[OF WfConsistency] _ gt_\<omega>minus])
              show "StateCons ?\<omega>0_rets"
                apply (rule total_consistency_store_update[OF WfConsistency])
                using state_rel_consistent StateRelDuringCall ConsistencyEnabled
                apply fastforce
                by simp_all
            qed
          
            show "valid_heap_mask (get_mh_total_full ?\<omega>minus)"
              apply (rule valid_heap_mask_downward_mono)
               apply (rule state_rel_wf_mask_simple[OF StateRelDuringCall])
              using gt_\<omega>minus full_total_state_greater_mask 
              by fastforce
          qed
          moreover have "mono_prop_downward StateCons"
            using ConsistencyDownwardMono mono_prop_downward_ord_implies_mono_prop_downward 
            by auto
          ultimately show ?thesis
            using exhale_inhale_normal MethodSpecSubset \<open>mdecl = _\<close>
            by blast
        qed
        ultimately have PostFramedAuxSmaller: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)) (get_store_total ?\<omega>0_rets)"
          using MethodSpecsFramed
          unfolding vpr_method_spec_correct_total_def vpr_method_correct_total_aux_def
          by fastforce

        have PostFramedAux: "vpr_postcondition_framed ctxt_vpr StateCons (method_decl.post mdecl) (get_total_full \<omega>) (get_store_total ?\<omega>0_rets)"
        proof -
          have "(get_total_full (?\<omega>0_rets \<ominus> ?\<omega>pre_exh_aux_rets)) \<le> (get_total_full \<omega>)"
            by (metis \<open>?\<omega>0_rets \<succeq> ?\<omega>pre_exh_aux_rets\<close> full_total_state.select_convs(3) full_total_state.update_convs(1) greater_full_total_state_total_state minus_smaller total_state_greater_equiv)
          thus ?thesis
            using vpr_postcondition_framed_mono ConsistencyDownwardMono MethodSpecSubset PostFramedAuxSmaller 
            by blast
        qed

      show ?thesis
      unfolding assertion_framing_state_def
      proof (rule allI, rule impI)+
        let ?\<phi>havoc = "get_total_full ?\<omega>havoc"
        let ?\<omega>havoc2 = "\<lparr> get_store_total = get_store_total ?\<omega>0_rets, 
                          get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                          get_total_full = ?\<phi>havoc \<rparr>"

          fix res
          assume "red_inhale ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>havoc res"
          hence "red_inhale ctxt_vpr StateCons (method_decl.post mdecl) ?\<omega>havoc2 res"
            by auto
          moreover have "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total ?\<phi>havoc)"
            using state_rel_heap_var_rel[OF \<open>?RCallPost ?\<omega>havoc ?nshavoc\<close>] \<open>Pr = _\<close> \<open>domain_type TyRep = _\<close>
            unfolding heap_var_rel_def
            by simp
          moreover have "valid_heap_mask (get_mh_total ?\<phi>havoc)"
            using \<open>?RCallPost ?\<omega>havoc ?nshavoc\<close> state_rel_wf_mask_simple
            by fastforce
          ultimately show "res \<noteq> RFailure"
            using PostFramedAux
            unfolding vpr_postcondition_framed_def
            using assertion_framing_state_def 
            by (metis fun_upd_same)                     
        qed
      qed

      note RCallPostConj = conjI[OF \<open>?RCallPost ?\<omega>havoc ?nshavoc\<close> PostFramed]     

      show ?thesis  
      proof (cases resPost)
        case RMagic
        then show ?thesis \<comment>\<open>trivial case\<close>
          using \<open>res = _\<close>
          by (auto intro: rel_vpr_aux_intro)
      next
        case RFailure
          with RedInh stmt_rel_failure_elim[OF InhalePostRelInst RCallPostConj] \<open>mdecl = _\<close>
          obtain c where 
              "red_ast_bpl P ctxt (?\<gamma>pre, Normal nspre) c" and
              "snd c = Failure"
            using RedBplHavoc red_ast_bpl_transitive
            by blast
          moreover from RFailure \<open>res = _\<close> have "res = RFailure"
            by simp
          ultimately show ?thesis 
            using RedBplPre red_ast_bpl_transitive
            by (blast intro: rel_vpr_aux_intro)
      next
        case (RNormal \<omega>post)
          with RedInh stmt_rel_normal_elim[OF InhalePostRelInst RCallPostConj] \<open>mdecl = _\<close>
          obtain nspost where 
              "red_ast_bpl P ctxt (?\<gamma>pre, Normal nspre) (\<gamma>', Normal nspost)" and
              "?RCallPost \<omega>post nspost"
            using RedBplHavoc red_ast_bpl_transitive
            by blast
          hence "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal nspost)"
            using RedBplPre red_ast_bpl_transitive
            by blast

          moreover have "get_store_total \<omega>post = get_store_total ?\<omega>havoc"
          using RedMethodCall \<open>resPre = _\<close> \<open>resPost = _\<close> inhale_only_changes_mask(3)
          by (metis RedInhale_case sub_expressions.simps(7))

          moreover from RNormal \<open>res = _\<close> have "res = RNormal (reset_state_after_call ys v_rets \<omega> \<omega>post)"
            by simp
            
          moreover have                                          
             "state_rel_def_same Pr StateCons TyRep Tr AuxPred ctxt (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost"
          proof -
            from \<open>?RCallPost \<omega>post nspost\<close> have
              "state_rel_def_same Pr StateCons TyRep (Tr\<lparr>var_translation := var_tr''\<rparr>) AuxPred ctxt \<omega>post nspost"
              apply (rule state_rel_aux_pred_remove)
              apply (rule map_upd_set_subset2)
              using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
              by blast

            thus ?thesis
            proof (rule state_rel_store_update[where ?f="var_translation Tr"])
              show "store_rel (type_interp ctxt) (var_context ctxt) (var_translation Tr) 
                              (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost"
              proof (rule store_relI)
                show "inj_on (var_translation Tr) (dom (var_translation Tr))"
                  using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                  by (simp add: store_rel_def)
              next
                fix var_vpr var_bpl
                assume VarTrSome: "var_translation Tr var_vpr = Some var_bpl"
                show "store_var_rel_aux (type_interp ctxt) (var_context ctxt) (reset_state_after_call ys v_rets \<omega> \<omega>post) nspost var_vpr var_bpl"
                proof (cases "var_vpr \<in> set ys")
                  case True
                  from this obtain id where "var_vpr = ys ! id" and "id < length ys"
                    by (metis in_set_conv_nth)
                  hence "var_bpl = ys_bpl ! id"
                    using YsBplEq VarTrSome
                    by auto

                  have *: "(length es + id) = [0..<length es + length ys] ! (length es + id)"
                    using \<open>id < _\<close> LengthEqs
                    by auto

                  have "var_tr'' (length es + id) = Some var_bpl"
                    using \<open>id < _\<close> LengthEqs map_upds_distinct_nth[OF distinct_upt *, 
                                                                   where ?m=Map.empty and ?ys="xs_bpl @ ys_bpl"]
                    unfolding \<open>var_tr'' = _\<close> \<open>var_bpl = (ys_bpl ! id)\<close>
                    by (smt (verit) True add.commute add_less_cancel_right diff_less diff_zero length_append length_pos_if_in_set length_rev length_upt nth_append_length_plus rev_append zero_less_Suc)

                  from this obtain val_vpr ty_bpl where
                    AuxStoreRel:
                     "get_store_total \<omega>post (length es + id) = Some val_vpr \<and>
                     lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl val_vpr) \<and>
                     lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl \<and>
                     type_of_val (type_interp ctxt) (val_rel_vpr_bpl val_vpr) = ty_bpl"
                    using state_rel_store_rel[OF \<open>?RCallPost \<omega>post nspost\<close>]
                    unfolding store_rel_def
                    by auto

                  have "val_vpr = v_rets ! id"
                  proof -
                    have *: "(length es + id) < length (v_args @ v_rets)"
                              using \<open>id < _\<close> LengthEqs
                              by simp
                    have "get_store_total \<omega>post (length es + id) = shift_and_add_list_alt Map.empty (v_args @ v_rets) (length es + id)"
                        by (simp add: \<open>get_store_total \<omega>post = _\<close>)
                    also have "... = Some ((v_args @ v_rets) ! (length es + id))"
                      using \<open>id < _\<close> shift_and_add_list_alt_lookup_1[OF *] 
                      by blast
                    also have "... = Some (v_rets ! id)"
                      using LengthEqs
                      by fastforce
                    finally show ?thesis
                      using AuxStoreRel
                      by auto  
                  qed
                     
                  show ?thesis
                  unfolding store_var_rel_aux_def
                  proof ((rule exI)+, intro conjI)
                    show "get_store_total (reset_state_after_call ys v_rets \<omega> \<omega>post) var_vpr = Some (v_rets ! id)"
                      unfolding reset_state_after_call_def
                      apply simp
                      using \<open>var_vpr = _\<close> \<open>distinct ys\<close> map_upds_distinct_nth \<open>id < _\<close> LengthEqs
                      by metis
                  next
                    show "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl (v_rets ! id))"
                      using AuxStoreRel \<open>val_vpr = v_rets ! id\<close>                                           
                      by simp
                  next
                    show "lookup_var_ty (var_context ctxt) var_bpl = Some ty_bpl"
                      using AuxStoreRel
                      by blast
                  next
                    show "type_of_val (type_interp ctxt) (val_rel_vpr_bpl (v_rets ! id)) = ty_bpl"
                      using AuxStoreRel\<open>val_vpr = v_rets ! id\<close>
                      by blast
                  qed
                next
                  case False
                  \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is not a target variable and thus we need to show that
                     it still contains the same value as before the call. \<close>

                  hence "var_bpl \<notin> set ys_bpl"
                    using map_the_inj_not_in state_rel_var_tr_inj[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                          YsBplEq VarTrSome \<open>set ys \<subseteq> _\<close>
                    by fast

                  have "get_store_total (reset_state_after_call ys v_rets \<omega> \<omega>post) var_vpr = 
                         get_store_total \<omega> var_vpr"
                    unfolding reset_state_after_call_def
                    by (simp add: False)

                  moreover have "lookup_var (var_context ctxt) nspost var_bpl = 
                                 lookup_var (var_context ctxt) ns var_bpl"
                  proof -
                    from VarTrSome obtain v_bpl where 
                      LookupVarBpl: "lookup_var (var_context ctxt) ns var_bpl = Some v_bpl"
                      using state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                      unfolding store_rel_def
                      by blast                    

                    show ?thesis
                    proof (cases "var_vpr \<in> set xs")
                      case True
                      \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is an argument variable, which means the proof
                         tracked the corresponding Boogie variable in the variable translation. Thus,
                         by showing that the Viper local store did not change during the call (except
                         for target variables), we can show that the Boogie variable was not modified either.\<close>

                      have "var_bpl \<in> set xs_bpl"
                      proof -
                        from \<open>var_vpr \<in> set xs\<close> obtain i where
                             "i < length xs" and "xs ! i = var_vpr"
                          by (meson in_set_conv_nth)

                        thus ?thesis
                          using XsBplEq VarTrSome LengthEqs
                          by (metis comp_eq_dest_lhs nth_map nth_mem option.sel)
                      qed

                      from this obtain i where "i < length xs_bpl" and "var_bpl = xs_bpl ! i"
                        by (metis in_set_conv_nth)

                      hence *: "i = [0..<length es+length ys] ! i"
                        using LengthEqs
                        by fastforce

                      have "var_tr'' i = Some var_bpl"
                        using map_upds_distinct_nth[OF distinct_upt *, where ?m=Map.empty and ?ys="xs_bpl@ys_bpl"] 
                              LengthEqs
                        unfolding \<open>var_tr'' = _\<close> \<open>var_bpl = _\<close>
                        using \<open>i < _\<close>
                        by (simp add: nth_append)
                                                                                              
                      with state_rel_store_rel[OF \<open>?RCallPost \<omega>post nspost\<close>] obtain val_vpr where 
                        "get_store_total \<omega>post i = Some val_vpr" and
                        "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl val_vpr)"
                        unfolding store_rel_def
                        by auto

                      hence "lookup_var (var_context ctxt) nspost var_bpl = Some (val_rel_vpr_bpl (v_args ! i))"
                        unfolding \<open>get_store_total \<omega>post = _\<close>
                        using \<open>i < _\<close> LengthEqs
                        by (simp add: shift_and_add_list_alt_lookup nth_append)

                      moreover from ValRelArgs have
                        "lookup_var (var_context ctxt) ns var_bpl = Some (val_rel_vpr_bpl (v_args ! i))"
                        using \<open>var_bpl = _\<close>
                        by (simp add: \<open>i < length xs_bpl\<close> list_all2_conv_all_nth)

                      ultimately show ?thesis
                        by simp
                    next
                      case False
                      \<comment>\<open>In this case, \<^term>\<open>var_vpr\<close> is not an argument variable or target variable.
                         Thus, the proof tracked the corresponding Boogie variable explicitly as an 
                         auxiliary variable that must still have the same value as before the call.\<close>
                      
                      hence "var_bpl \<notin> set xs_bpl" 
                        using map_the_inj_not_in state_rel_var_tr_inj[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                              XsBplEq VarTrSome \<open>set xs \<subseteq> _\<close>
                        by fast
                                             
                      have *: "map_upd_set AuxPred (ran (var_translation Tr) - (set xs_bpl \<union> set ys_bpl))
                               ?fpred var_bpl = Some (?fpred var_bpl)"
                        apply (rule map_upd_set_lookup_1)
                        using \<open>var_bpl \<notin> set xs_bpl\<close> \<open>var_bpl \<notin> set ys_bpl\<close> VarTrSome
                              ranI
                        by fast

                      thus ?thesis
                        using state_rel_aux_pred_sat_lookup[OF \<open>?RCallPost \<omega>post nspost\<close> *]
                              LookupVarBpl
                        unfolding pred_eq_def
                        by (simp add: has_Some_iff)
                      qed                   
                    qed
                  ultimately show ?thesis
                    using VarTrSome state_rel_store_rel[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                    unfolding store_var_rel_aux_def store_rel_def
                    by presburger                    
                qed
              qed
            next
              have "StateCons_t (get_total_full \<omega>post)"
              proof -
                have "consistent_state_rel_opt (state_rel_opt (Tr\<lparr>var_translation := var_tr''\<rparr>))"
                  by (simp add: ConsistencyEnabled)

                with \<open>?RCallPost \<omega>post _\<close> state_rel_consistent WfConsistency 
                show ?thesis
                unfolding wf_total_consistency_def                
                by blast
              qed

              show "StateCons (reset_state_after_call ys v_rets \<omega> \<omega>post)"
                unfolding reset_state_after_call_def
                apply (rule total_consistencyI[OF WfConsistency])
                 apply (simp add: \<open>StateCons_t (get_total_full \<omega>post)\<close>)                 
                using state_rel_consistent[OF StateRel] WfConsistency ConsistencyEnabled
                unfolding wf_total_consistency_def
                by simp
            next
              show "binder_state nspost = Map.empty"
                using state_rel_state_well_typed[OF \<open>?RCallPost \<omega>post nspost\<close>, simplified state_well_typed_def]
                by simp
            next
              show "ran (var_translation Tr) \<inter>
                   ({heap_var (Tr\<lparr>var_translation := var_tr''\<rparr>), heap_var_def (Tr\<lparr>var_translation := var_tr''\<rparr>)} \<union>
                    {mask_var (Tr\<lparr>var_translation := var_tr''\<rparr>), mask_var_def (Tr\<lparr>var_translation := var_tr''\<rparr>)} \<union>
                    ran (field_translation (Tr\<lparr>var_translation := var_tr''\<rparr>)) \<union>
                    range (const_repr (Tr\<lparr>var_translation := var_tr''\<rparr>)) \<union>
                    dom AuxPred) =
                   {}"
                using var_translation_disjoint[OF StateRelConcrete[OF \<open>R \<omega> ns\<close>]]
                by simp
            qed (simp_all add: reset_state_after_call_def)
              
          qed
            
          ultimately show ?thesis 
            by (blast intro: rel_vpr_aux_intro)
        qed
      qed
  next
    case RedSubExpressionFailure
    \<comment>\<open>Since the arguments are assumed to be arguments, this case cannot occur\<close>
    have SubExpEq: "sub_expressions (MethodCall ys m es) = map ViperLang.Var xs"
      by (simp add: \<open>es = _\<close>) 

    from RedSubExpressionFailure
    show ?thesis
      unfolding SubExpEq
    proof -
      assume "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) (map pure_exp.Var xs) \<omega> None"

      from this obtain i where 
        "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>pure_exp.Var (xs ! i); \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        using red_exp_list_failure_nth
        by (metis SubExpEq length_map local.RedSubExpressionFailure(2) nth_map)
        
      hence False
        by (cases) auto

      thus ?thesis
        by simp
    qed
  qed
qed


end