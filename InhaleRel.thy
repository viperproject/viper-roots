theory InhaleRel
  imports ExpRel ExprWfRel TotalViper.ViperBoogieTranslationInterface Simulation
begin

definition inhale_rel ::
     "('a full_total_state \<Rightarrow> 'a vbpl_absval nstate \<Rightarrow> bool)
     \<Rightarrow> 'a total_context
        \<Rightarrow> ('a full_total_state \<Rightarrow> bool)
           \<Rightarrow> bigblock list
                    \<Rightarrow> 'a econtext_bpl
                       \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert
                          \<Rightarrow> bigblock \<times> cont \<Rightarrow> bigblock \<times> cont \<Rightarrow> bool"
  where "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<equiv>
         rel_general R R 
           (\<lambda> \<omega> \<omega>'. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>'))
           (\<lambda> \<omega>. red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure)
           P ctxt \<gamma> \<gamma>'"


lemma inhale_rel_intro:
  assumes
    "\<And>\<omega> ns \<omega>'. 
      R \<omega> ns \<Longrightarrow> 
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
      (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and

    "\<And>\<omega> ns.
      R \<omega> ns \<Longrightarrow>
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure \<Longrightarrow>
      (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_intro)

definition inhale_rel_aux
  where "inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res \<equiv>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                   \<comment>\<open>Normal Viper inhale executions can be simulated by normal Boogie executions\<close>
                   (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                   \<comment>\<open>If a Viper inhale executions fails, then there is a failing Boogie execution\<close>
                   (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure))"

lemma inhale_rel_intro_2:
  assumes
    "\<And>\<omega> ns res. 
      R \<omega> ns \<Longrightarrow> 
      red_inhale ctxt_vpr StateCons assertion_vpr \<omega> res \<Longrightarrow>
      inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res"
  shows "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'"
  using assms
  unfolding inhale_rel_def inhale_rel_aux_def
  by (auto intro: rel_intro)

lemma inhale_rel_aux_intro:
  assumes "\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow>
           (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns'))" and
          "res = RFailure \<Longrightarrow> (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
        shows "inhale_rel_aux R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>' \<omega> ns res"
  using assms
  unfolding inhale_rel_aux_def
  by blast

lemma inhale_rel_normal_elim:
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> (RNormal \<omega>')"
  shows "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega>' ns')"
  using assms
  unfolding inhale_rel_def
  by (auto intro: rel_success_elim)

lemma inhale_rel_failure_elim:
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt assertion_vpr \<gamma> \<gamma>'" and 
          "R \<omega> ns" and 
          "red_inhale ctxt_vpr StateCons assertion_vpr \<omega> RFailure"
  shows "\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure"
  using assms
  unfolding inhale_rel_def rel_general_def
  by auto

subsection \<open>Structural rules\<close>

lemma inhale_rel_star: 
  assumes "inhale_rel R ctxt_vpr StateCons P ctxt A1 \<gamma>1 \<gamma>2" and
          "inhale_rel R ctxt_vpr StateCons P ctxt A2 \<gamma>2 \<gamma>3"
        shows "inhale_rel R ctxt_vpr StateCons P ctxt (A1 && A2) \<gamma>1 \<gamma>3"
  using assms
  unfolding inhale_rel_def
  apply (rule rel_general_comp)
  by (auto elim: InhStar_case)

lemma inhale_rel_imp:
  assumes 
   ExpWfRel:          
        "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr StateCons P ctxt cond 
         \<gamma>1
         (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) [empty_else_block], KSeq next cont)" 
        (is "expr_wf_rel _ ctxt_vpr StateCons P ctxt cond _ ?\<gamma>_if") and
   EmptyElse: "is_empty_bigblock empty_else_block" and
   ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl" and
   RhsRel: "inhale_rel R ctxt_vpr StateCons P ctxt A (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)"
                (is "inhale_rel R _ _ _ _ _ ?\<gamma>_thn (next, cont)")
              shows "inhale_rel R ctxt_vpr StateCons P ctxt (assert.Imp cond A) \<gamma>1 (next, cont)"
  using wf_rel_general_1[OF ExpWfRel] RhsRel
  unfolding inhale_rel_def
proof (rule rel_general_cond)
  show "rel_general R R (\<lambda> \<omega> \<omega>'. \<omega> = \<omega>') (\<lambda>_. False) P ctxt (empty_else_block, convert_list_to_cont [] (KSeq next cont)) (next, cont)"
    apply (rule rel_intro)
    using red_ast_bpl_empty_block_2[OF EmptyElse]
    apply fastforce
    by simp
next
  fix \<omega> \<omega>' ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> (RNormal \<omega>')" and "R \<omega> ns"
  thus "((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> red_inhale ctxt_vpr StateCons A \<omega> (RNormal \<omega>') \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> \<omega> = \<omega>')"
    apply (cases)
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
    apply (metis val_rel_vpr_bpl.simps(2))
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
    by (metis val_rel_vpr_bpl.simps(2))
next
  fix \<omega> ns
  assume "red_inhale ctxt_vpr StateCons (assert.Imp cond A) \<omega> RFailure" and "R \<omega> ns"
  thus "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
       ((\<exists>v. ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and> \<omega> = \<omega>) \<and>
       (red_expr_bpl ctxt cond_bpl ns (BoolV True) \<and> red_inhale ctxt_vpr StateCons A \<omega> RFailure \<or>
        red_expr_bpl ctxt cond_bpl ns (BoolV False) \<and> False)"
    apply (cases)
    using exp_rel_vpr_bpl_elim_2[OF ExpRel]
     apply (metis val_rel_vpr_bpl.simps(2))
    by auto
qed

subsection \<open>Field access predicate rule\<close>

lemma inhale_rel_field_acc:
  assumes 
    MaskUpdWf: "mask_update_wf TyRep ctxt mask_upd_bpl" and
    WfRcv: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_rcv_vpr \<gamma> \<gamma>1" and
    WfPerm: "expr_wf_rel (state_rel_ext R) ctxt_vpr StateCons P ctxt e_p \<gamma>1 \<gamma>2" and
    WfInh:  "wf_rel (state_rel_ext R)
                  Rext' 
                  (\<lambda> \<omega>def \<omega>. \<exists>p r. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p \<ge> 0 \<and>
                                   ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_rcv_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef r)) \<and> (p > 0 \<longrightarrow> r \<noteq> Null))  
                  (\<lambda> \<omega>def \<omega>. \<exists>p. ctxt_vpr, StateCons, Some \<omega>def \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)) \<and> p < 0)
                  P ctxt \<gamma>2 \<gamma>3" and
            "m_bpl = mask_var Tr" and
    MaskUpdBpl:
       "\<And> \<omega> ns. Rext' \<omega> \<omega> ns \<Longrightarrow> \<exists> ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')" and
    HeapUpdateBpl: "m_upd_bpl = mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
    RcvRel: "exp_rel_vpr_bpl Rext' ctxt_vpr ctxt e_rcv_vpr rcv_bpl" and
    FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    NewPermRel: "exp_rel_vpr_bpl Rext' ctxt_vpr ctxt (ViperLang.Binop (Perm e_rcv_vpr f) ViperLang.Add e_p) new_perm_bpl" 

    (*
     \<comment>\<open>Inhale property for R\<close>
    RInhale:  "\<And> \<omega> ns ty_vpr hb r f_bpl p. Rext' \<omega> \<omega> ns \<Longrightarrow>
                     declared_fields (program_total ctxt_vpr) f_vpr = Some ty_vpr \<Longrightarrow>
                     field_translation Tr f_vpr = Some f_bpl \<Longrightarrow>
                     vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl \<Longrightarrow>
                     (pgt p pnone  \<Longrightarrow> r \<noteq> Null) \<Longrightarrow>
                     (\<exists>mb f_bpl_val. 
                       lookup_var_ty (var_context ctxt) (mask_var Tr) = Some (TConSingle (TMaskId TyRep)) \<and>
                       lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb)) \<and>
                       lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
                       field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<and>
                       Rext'
                         (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (the_address r, f_vpr) p)
                         (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (the_address r, f_vpr) p)
                         (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AMask (mb ( (r, f_bpl_val) := real_of_rat (Rep_prat p) ))))
                         ))"*)
    
  shows "inhale_rel R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>'"
proof (rule inhale_rel_intro_2)
  fix \<omega> ns res
  assume "R \<omega> ns"
  hence Rext0: "state_rel_ext R \<omega> \<omega> ns"
    by simp

  assume "red_inhale ctxt_vpr StateCons (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<omega> res"
  thus "inhale_rel_aux R ctxt_vpr StateCons P ctxt (Atomic (Acc e_rcv_vpr f (PureExp e_p))) \<gamma> \<gamma>' \<omega> ns res"
  proof (cases)
    case (InhAcc r p W')
    from this obtain ns1 where Rext1: "state_rel_ext R \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF WfRcv Rext0]
      by blast
    with InhAcc obtain ns2 where Rext2: "state_rel_ext R \<omega> \<omega> ns2" and Red2: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF WfPerm Rext1] red_ast_bpl_transitive
      by blast

    show ?thesis
    proof (rule inhale_rel_aux_intro)
      \<comment>\<open>Normal case\<close>
      let ?\<gamma>3 = "((BigBlock name ((Lang.Assign m_bpl m_upd_bpl)#cs) str tr), cont)"

      fix \<omega>'
      assume "res = RNormal \<omega>'"
      hence "0 \<le> p" and "W' \<noteq> {}" and "0 < p \<longrightarrow> r \<noteq> Null" and "\<omega>' \<in> W'"
      using th_result_rel_normal InhAcc
      by auto

      with InhAcc obtain ns3 where Rext3: "Rext' \<omega> \<omega> ns3" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>3, Normal ns3)"
        using wf_rel_normal_elim[OF WfInh Rext2] red_ast_bpl_transitive[OF Red2]
        by blast

      let ?p_bpl = "real_of_rat p"
      let ?p_prat = "Abs_prat p"

      have "pgt ?p_prat pnone  \<Longrightarrow> r \<noteq> Null"
        using \<open>0 < p \<longrightarrow> r \<noteq> Null\<close> \<open>p \<ge> 0\<close> pnone_def prat_pgt_pnone
        by fastforce        

      obtain f_bpl \<tau>_vpr where
          FieldLookup: "declared_fields (program_total ctxt_vpr) f_vpr = Some \<tau>_vpr" and
          TyTr: "vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl" and
          FieldTr: "field_translation Tr f_vpr = Some f_bpl" and
          "e_f_bpl = Lang.Var f_bpl"
        using FieldRelSingle
        by (auto elim: field_rel_single_elim)

      from Rext3 

      from MaskUpdWf have
        RedMaskUpdBpl:
        "red_expr_bpl ctxt (mask_upd_bpl (Lang.Var m_bpl) e_rcv_bpl e_f_bpl new_perm_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])
                           ns3
                           (AbsV (AMask (m ( (r, f_bpl_val) := ?p_bpl))))"
       (* 
            from HeapUpdWf have 
            RedHeapUpdBpl:
           "red_expr_bpl ctxt (heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])
                                   ns3 (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))"
           apply (rule heap_update_wf_apply)
           using  \<open>h_bpl = _\<close> Semantics.RedVar[OF LookupHeapVarBpl]
                 apply simp
                apply (rule HeapWellTyBpl)
               apply (rule RedRcvBpl)
           using \<open>e_f_bpl = _\<close> Semantics.RedVar[OF LookupFieldVarBpl]
              apply simp
             apply (rule FieldTyBpl)
            apply (rule RedRhsBpl)
           apply (simp add: NewValTypeBpl)
           done
       *)
        
        
      
    
    then show ?thesis sorry
  next 
    case InhSubAtomicFailure
    then show ?thesis sorry
  qed
next
  


end