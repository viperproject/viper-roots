theory PaperResultsSupport
imports TotalViper.ViperBoogieEndToEnd TotalViper.TraceIndepProperty
begin

subsection \<open>BPROP\<close>

definition bsim
  where "bsim R R\<^sub>1 P ctxt \<gamma> \<gamma>1 \<equiv> rel_general R R\<^sub>1 (\<lambda>\<tau> \<tau>'. \<tau> = \<tau>') (\<lambda>_. False) P ctxt \<gamma> \<gamma>1"

lemma bsim_red_ast_bpl_rel:
  shows "bsim R R\<^sub>1 P ctxt \<gamma> \<gamma>' \<longleftrightarrow> red_ast_bpl_rel R R\<^sub>1 P ctxt \<gamma> \<gamma>'"
  unfolding bsim_def red_ast_bpl_rel_def rel_general_def
  by auto

lemma brop_paper:
  assumes "bsim R R\<^sub>1 P ctxt \<gamma> \<gamma>\<^sub>1"
      and "rel_general R\<^sub>1 R\<^sub>2 S F P ctxt \<gamma>\<^sub>1 \<gamma>\<^sub>2"
      and "bsim R\<^sub>2 R' P ctxt \<gamma>\<^sub>2 \<gamma>\<^sub>3"
    shows "rel_general R R' S F P ctxt \<gamma> \<gamma>\<^sub>3"
proof -
  from assms(1) have "red_ast_bpl_rel R R\<^sub>1 P ctxt \<gamma> \<gamma>\<^sub>1"
    by (simp add: bsim_red_ast_bpl_rel)
  with assms(2) have "rel_general R R\<^sub>2 S F P ctxt \<gamma> \<gamma>\<^sub>2"
    using rel_propagate_pre
    unfolding red_ast_bpl_rel_def
    by metis
  with assms(3) show ?thesis
    using rel_propagate_post
    by (simp add: bsim_red_ast_bpl_rel)
qed

subsection \<open>Correspondence nonDetSelect and havocLocs\<close>

definition non_det_select
  where "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v' \<equiv>
 
         \<comment>\<open>corresponds to \<open>st(\<sigma>\<^sub>v') = st(\<sigma>\<^sub>v'')\<close> in the paper\<close>
         get_store_total \<sigma>\<^sub>v' = get_store_total \<sigma>\<^sub>v'' \<and>

         \<comment>\<open>corresponds to \<open>\<pi>(\<sigma>\<^sub>v') = \<pi>(\<sigma>\<^sub>v'')\<close> in the paper\<close>
         get_mh_total_full \<sigma>\<^sub>v' = get_mh_total_full \<sigma>\<^sub>v'' \<and>

         \<comment>\<open>corresponds to \<open>\<forall>l. (\<pi>(\<sigma>\<^sub>v')(l) = 0 \<or> \<pi>(\<sigma>\<^sub>v'') > 0) \<longrightarrow> h(\<sigma>\<^sub>v')(l) = h(\<sigma>\<^sub>v'')(l)\<close>\<close>
         (\<forall>l. (get_mh_total_full \<sigma>\<^sub>v l = 0 \<or> get_mh_total_full \<sigma>\<^sub>v'' l > 0) \<longrightarrow> get_hh_total_full \<sigma>\<^sub>v' l = get_hh_total_full \<sigma>\<^sub>v'' l) \<and>
         
         \<comment>\<open>This conjunct just states that the new heap must be well-typed, which we omitted from the paper for 
            the sake of presentation\<close>
         total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<sigma>\<^sub>v') \<and>
         
         \<comment>\<open>The following three conjuncts express equality on components of Viper states that are 
            not required in the paper subset.\<close>
         get_trace_total \<sigma>\<^sub>v' = get_trace_total \<sigma>\<^sub>v'' \<and>
         get_mp_total_full \<sigma>\<^sub>v' = get_mp_total_full \<sigma>\<^sub>v'' \<and>
         get_hp_total_full \<sigma>\<^sub>v' = get_hp_total_full \<sigma>\<^sub>v''"

lemma non_det_select_heap_upd_1:
  assumes "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh'"
      and "\<forall>l. (get_mh_total_full \<sigma>\<^sub>v l = 0 \<or> get_mh_total_full \<sigma>\<^sub>v'' l > 0) \<longrightarrow> hh' l = get_hh_total_full \<sigma>\<^sub>v'' l"
    shows "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' (update_hh_total_full \<sigma>\<^sub>v'' hh')"
  unfolding non_det_select_def
  using assms
  by auto          

lemma non_det_select_havoc_locs_1:
  assumes "\<sigma>\<^sub>v' \<in> havoc_locs_state ctxt \<sigma>\<^sub>v'' {loc. get_mh_total_full \<sigma>\<^sub>v loc > 0 \<and> get_mh_total_full \<sigma>\<^sub>v'' loc = 0}"
  shows "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'"
proof -
  let ?hlocs = "{loc. get_mh_total_full \<sigma>\<^sub>v loc > 0 \<and> get_mh_total_full \<sigma>\<^sub>v'' loc = 0}"
  from assms obtain hh' where 
      "\<sigma>\<^sub>v' = update_hh_total_full \<sigma>\<^sub>v'' hh'"
  and WellTyped: "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh'"
  and "hh' \<in> havoc_locs_heap (get_hh_total_full \<sigma>\<^sub>v'') ?hlocs"
    unfolding havoc_locs_state_def
    by blast

  show ?thesis
    apply (subst \<open>\<sigma>\<^sub>v' = _\<close>)
    apply (rule non_det_select_heap_upd_1)
     apply (rule WellTyped)
    using \<open>hh' \<in> _\<close>
    unfolding havoc_locs_heap_def
    by force
qed

lemma non_det_select_heap_upd_2:
  assumes "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'"
  shows "\<exists>hh'. total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh' \<and>
               \<sigma>\<^sub>v' = update_hh_total_full \<sigma>\<^sub>v'' hh' \<and>
               (\<forall>l. (get_mh_total_full \<sigma>\<^sub>v l = 0 \<or> get_mh_total_full \<sigma>\<^sub>v'' l > 0) \<longrightarrow> hh' l = get_hh_total_full \<sigma>\<^sub>v'' l)"
proof -
  let ?hh' = "get_hh_total_full \<sigma>\<^sub>v'"

  note Aux = assms[simplified non_det_select_def]

  have "\<sigma>\<^sub>v' = update_hh_total_full \<sigma>\<^sub>v'' ?hh'"
    apply (rule full_total_state.equality)
    using Aux
    by auto
  
  show ?thesis
    apply (rule exI[where ?x = ?hh'])
    using Aux \<open>\<sigma>\<^sub>v' = _ \<close>
    by blast
qed

lemma non_det_select_havoc_locs_2:
  assumes "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v'"
  shows  "\<sigma>\<^sub>v' \<in> havoc_locs_state ctxt \<sigma>\<^sub>v'' {loc. get_mh_total_full \<sigma>\<^sub>v loc > 0 \<and> get_mh_total_full \<sigma>\<^sub>v'' loc = 0}"
proof -
  from assms obtain hh'
    where "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh'"
      and "\<sigma>\<^sub>v' = update_hh_total_full \<sigma>\<^sub>v'' hh'"
      and "(\<forall>l. (get_mh_total_full \<sigma>\<^sub>v l = 0 \<or> get_mh_total_full \<sigma>\<^sub>v'' l > 0) \<longrightarrow> hh' l = get_hh_total_full \<sigma>\<^sub>v'' l)"
    using non_det_select_heap_upd_2
    by blast

  thus ?thesis
    unfolding havoc_locs_state_def havoc_locs_heap_def
    using pperm_pnone_pgt
    by blast
qed

lemma non_det_select_havoc_locs_equivalence:
  "non_det_select ctxt \<sigma>\<^sub>v \<sigma>\<^sub>v'' \<sigma>\<^sub>v' \<longleftrightarrow> 
   \<sigma>\<^sub>v' \<in> havoc_locs_state ctxt \<sigma>\<^sub>v'' {loc. get_mh_total_full \<sigma>\<^sub>v loc > 0 \<and> get_mh_total_full \<sigma>\<^sub>v'' loc = 0}"
  using non_det_select_havoc_locs_1 non_det_select_havoc_locs_2
  by blast

subsection \<open>Misc definitions\<close>

definition exprs_wf_rel_2 :: "('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 
                              ('a vpr_state \<Rightarrow> 'a vpr_state \<Rightarrow>  ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 'a total_context \<Rightarrow> ('a vpr_state \<Rightarrow> bool) \<Rightarrow>  ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
       viper_expr list \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where "exprs_wf_rel_2 R R' ctxt_vpr StateCons P ctxt es \<equiv>
           wf_rel R R' (\<lambda>\<omega>def \<omega>. \<exists>vs. red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> (Some vs)) 
                       (\<lambda>\<omega>def \<omega>. red_pure_exps_total ctxt_vpr StateCons (Some \<omega>def) es \<omega> None) P ctxt"

subsection \<open>Remcheck relationship definition without additional predicate\<close>

text \<open>We work directly with \<^const>\<open>exhale_rel\<close>, which introduces a predicate \<^term>\<open>Q\<close> to track conditions
      on assertions separately.
      Alternatively, it would be possible to first provide a base definition 
      that does not introduce \<^term>\<open>Q\<close> and then to use an instantiation to obtain the version \<^term>\<open>Q\<close>. 

      Concretely, we could define the following base definition:\<close>

definition exhale_rel0
    where "exhale_rel0 R R' ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv> 
             rel_general (uncurry R) (uncurry R')
             \<comment>\<open>The well-definedness state remains the same\<close>
             (\<lambda> \<omega>0_\<omega> \<omega>0_\<omega>'. (fst \<omega>0_\<omega>) = (fst \<omega>0_\<omega>') \<and> red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) (RNormal (snd \<omega>0_\<omega>')))
             (\<lambda> \<omega>0_\<omega>. red_exhale ctxt_vpr StateCons (fst \<omega>0_\<omega>) assertion_vpr (snd \<omega>0_\<omega>) RFailure)
             P ctxt \<gamma> \<gamma>'"

text \<open>Then, the original definition is equivalent to a specific instantiation of \<^const>\<open>exhale_rel0\<close>:\<close>

lemma exhale_rel_exhale_rel0_inst_equiv: 
  "exhale_rel R R' Q ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>' \<longleftrightarrow>
   exhale_rel0 (\<lambda>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<and> Q A \<omega>def \<omega>) R' ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>'"
  unfolding exhale_rel_def exhale_rel0_def
  by simp

text \<open>The following lemma shows that we can do the reverse as well. We can express the base definition
      \<^const>\<open>exhale_rel0\<close> in terms of the original definition by instantiating \<^term>\<open>Q\<close> to be the \
      predicate that is always true.\<close>

lemma exhale_rel0_rel_equiv: 
  "exhale_rel0 R R' ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<longleftrightarrow>
   exhale_rel R R' (\<lambda> _ _ _. True) ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  unfolding exhale_rel_def exhale_rel0_def
  by presburger

text \<open>The stmt relation rule when using  \<^const>\<open>exhale_rel0\<close> is then given by\<close>

lemma exhale0_stmt_rel:
  assumes WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and Consistent: "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> StateCons \<omega>"
      and ExhaleRel: "exhale_rel0 (rel_ext_eq R) Rexh ctxt_vpr StateCons P ctxt A \<gamma> \<gamma>2"
      and UpdHavoc: "rel_general (uncurry Rexh) (\<lambda>\<omega> ns. R_out (snd \<omega>) ns) 
               (\<lambda>\<omega> \<omega>'. \<comment>\<open>the current evaluation state was reached by exhaling A from the current well-definedness state\<close>
                       red_exhale ctxt_vpr StateCons (fst \<omega>) A (fst \<omega>) (RNormal (snd \<omega>)) \<and> 
                       \<comment>\<open>the updated state is a havoc of the current evaluation state\<close>
                       snd \<omega>' \<in> havoc_locs_state ctxt_vpr (snd \<omega>) ({loc. get_mh_total_full (fst \<omega>) loc > 0 \<and> get_mh_total_full (snd \<omega>) loc = 0}) \<and>
                       StateCons (snd \<omega>')
                ) (\<lambda>_. False) P ctxt \<gamma>2 \<gamma>'"
    shows "stmt_rel R R_out ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Exhale A) \<gamma> \<gamma>'"
  apply (rule exhale_stmt_rel[OF WfConsistency Consistent])
     apply assumption
  using ExhaleRel exhale_rel0_rel_equiv
    apply blast
   apply simp
  by (rule UpdHavoc)

subsection \<open>Relationship Viper Method Correctness\<close>

definition all_methods_in_core_subset
  where "all_methods_in_core_subset ctxt \<equiv>
             (\<forall>mname m. methods (program_total ctxt) mname = Some m \<longrightarrow>
                      assertion_in_core_subset (method_decl.pre m) \<and>
                      assertion_in_core_subset (method_decl.post m))"

definition vpr_method_correct_paper :: "'a total_context \<Rightarrow> method_decl \<Rightarrow> bool" where
  "vpr_method_correct_paper ctxt m \<equiv>
         \<forall>(\<sigma>\<^sub>v :: 'a full_total_state) r\<^sub>v. 
            \<comment>\<open>These first two premises state that the store must be well-typed w.r.t. the arguments and result
               variable types and that the heap must be well-typed w.r.t. the field declarations. Both
               of these premises were omitted in the paper for the sake of presentation (as pointed out
               in footnote 7 on line 832 in the paper).\<close>
            vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args m @ method_decl.rets m)) (get_store_total \<sigma>\<^sub>v) \<longrightarrow>
            total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<sigma>\<^sub>v) \<longrightarrow>
                          
            \<comment>\<open>The following premise corresponds to \<open>\<forall>l. \<pi>(\<sigma>\<^sub>v)(l) = 0\<close> in the paper\<close>
            is_empty_total_full \<sigma>\<^sub>v \<longrightarrow>

            (\<forall>mbody. method_decl.body m = Some mbody \<longrightarrow>
              (               
                red_stmt_total ctxt (\<lambda>_. True) (nth_option (method_decl.args m @ method_decl.rets m))
                                    (Seq (Inhale (method_decl.pre m)) (Seq mbody (Exhale (method_decl.post m))))
                                    \<sigma>\<^sub>v
                                    r\<^sub>v \<longrightarrow>
                r\<^sub>v \<noteq> RFailure
              )
            )"

lemma method_correctness_stronger_than_paper:
  assumes "vpr_method_correct_total ctxt (\<lambda>_.True) m"
      and "method_decl.body m = Some mbody"
      and MethodInPaperSubset: "assertion_in_core_subset (method_decl.pre m) \<and>
                                assertion_in_core_subset (method_decl.post m) \<and>
                                stmt_in_core_subset mbody"
    shows "vpr_method_correct_paper ctxt m"
  unfolding vpr_method_correct_paper_def
proof (rule allI | rule impI)+
  fix \<sigma>\<^sub>v r\<^sub>v mbody'
  assume StoreWt: "vpr_store_well_typed (absval_interp_total ctxt) (nth_option (method_decl.args m @ rets m)) (get_store_total \<sigma>\<^sub>v)"
     and HeapWt: "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<sigma>\<^sub>v)"
     and EmptyInit: "is_empty_total_full \<sigma>\<^sub>v"
     and SomeBody: "method_decl.body m = Some mbody'"
     and RedStmt: "red_stmt_total ctxt (\<lambda>_. True) (nth_option (method_decl.args m @ rets m))
          (Seq (Inhale (method_decl.pre m)) (Seq mbody' (Exhale (method_decl.post m)))) \<sigma>\<^sub>v r\<^sub>v"

  hence "mbody' = mbody"
    using \<open>method_decl.body m = Some mbody\<close>
    by simp

  let ?\<Lambda> = "(nth_option (method_decl.args m @ rets m))"

  note Aux = assms(1)[simplified vpr_method_correct_total_2_new_equiv vpr_method_correct_total_expanded_def]

  from RedStmt
  show "r\<^sub>v \<noteq> RFailure"
  proof (cases)
    case (RedSeq \<sigma>1)
    hence "red_inhale ctxt (\<lambda>_. True) (method_decl.pre m) \<sigma>\<^sub>v (RNormal \<sigma>1)"
      by (auto elim: RedInhale_case)

    with Aux StoreWt HeapWt EmptyInit
    have BodyCorrect: "(\<forall>mbody. method_decl.body m = Some mbody \<longrightarrow> vpr_method_body_correct ctxt (\<lambda>_. True) m \<sigma>1)"
      by blast
    let ?\<sigma>1' = "update_trace_total \<sigma>1 (Map.empty(old_label \<mapsto> get_total_full \<sigma>1))"
    from BodyCorrect have AuxBody: "\<forall>r. red_stmt_total ctxt (\<lambda>_.True) ?\<Lambda>
                                (Seq mbody (Exhale (method_decl.post m)))
                                ?\<sigma>1' 
                                r \<longrightarrow> r \<noteq> RFailure"
      using SomeBody \<open>method_decl.body m = Some mbody\<close>
      unfolding vpr_method_body_correct_def 
      by auto

    have DifferOnlyOnTrace: "states_differ_only_on_trace \<sigma>1 ?\<sigma>1'"
      by simp

    have BodyExhalePostInSubset: "stmt_in_core_subset (Seq mbody (Exhale (method_decl.post m)))"
      using MethodInPaperSubset
      unfolding all_methods_in_core_subset_def
      by simp

    show "r\<^sub>v \<noteq> RFailure"
    proof 
      assume "r\<^sub>v = RFailure"
      hence "red_stmt_total ctxt (\<lambda>_.True) ?\<Lambda>
                                (Seq mbody (Exhale (method_decl.post m)))
                                ?\<sigma>1' 
                                RFailure"        
        using red_stmt_trace_indep[OF RedSeq(2)[simplified \<open>mbody' = mbody\<close>] BodyExhalePostInSubset DifferOnlyOnTrace]  
        by blast
      thus False
        using AuxBody
        by blast
    qed
  next
    case RedSeqFailureOrMagic
    hence "red_inhale ctxt (\<lambda>_. True) (method_decl.pre m) \<sigma>\<^sub>v r\<^sub>v"
      by (auto elim: RedInhale_case)
    with Aux StoreWt HeapWt EmptyInit
    show ?thesis
      by blast
  qed simp
qed


end