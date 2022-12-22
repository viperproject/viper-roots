theory ExpRel
imports ViperBoogieBasicRel
begin

fun unop_rel :: "ViperLang.unop \<Rightarrow> Lang.unop"
  where 
    "unop_rel ViperLang.Minus = Lang.UMinus"
  | "unop_rel ViperLang.Not = Lang.Not"

lemma unop_rel_correct: 
  assumes 
    "eval_unop uop_vpr v_vpr = BinopNormal v_vpr'" and
    "unop_rel uop_vpr = uop_bpl"
  shows "unop_eval_val uop_bpl (val_rel_vpr_bpl v_vpr) = Some (val_rel_vpr_bpl v_vpr')  "
  apply (insert assms)
  by (erule eval_unop.elims) (auto simp: of_rat_minus)   

fun binop_rel :: "ViperLang.binop \<Rightarrow> Lang.binop"
  where 
    "binop_rel ViperLang.Add = Lang.Add"
  | "binop_rel ViperLang.Sub = Lang.Sub"
  | "binop_rel ViperLang.Mult = Lang.Mul"
  | "binop_rel ViperLang.IntDiv = Lang.Div"
  | "binop_rel ViperLang.PermDiv = Lang.RealDiv"
  | "binop_rel ViperLang.Mod = Lang.Mod"
  | "binop_rel ViperLang.Eq = Lang.Eq"
  | "binop_rel ViperLang.Neq = Lang.Neq"
  | "binop_rel ViperLang.Gt = Lang.Gt"
  | "binop_rel ViperLang.Gte = Lang.Ge"
  | "binop_rel ViperLang.Lt = Lang.Lt"
  | "binop_rel ViperLang.Lte = Lang.Le"
  | "binop_rel ViperLang.Or = Lang.Or"
  | "binop_rel ViperLang.BImp = Lang.Imp"
  | "binop_rel ViperLang.And = Lang.And"

lemma binop_lazy_rel_correct:
  assumes "eval_binop_lazy v_vpr bop_vpr = Some v'_vpr" and
          "binop_rel bop_vpr = bop_bpl" and
          "binop_eval_val bop_bpl (val_rel_vpr_bpl v_vpr) v_bpl \<noteq> None"
  shows   "binop_eval_val bop_bpl (val_rel_vpr_bpl v_vpr) v_bpl = Some (val_rel_vpr_bpl v'_vpr)"
  using assms
  apply (cases rule: eval_binop_lazy.elims)
  apply simp_all
  by (cases v_bpl; (rename_tac lit, case_tac lit, auto))+

lemma binop_nonlazy_rel_correct:
  assumes "eval_binop v1_vpr bop_vpr v2_vpr = BinopNormal v_vpr" and
          "binop_rel bop_vpr = bop_bpl"
  shows   "binop_eval_val bop_bpl (val_rel_vpr_bpl v1_vpr) (val_rel_vpr_bpl v2_vpr) = Some (val_rel_vpr_bpl v_vpr)"
  using assms
  apply (cases rule: eval_binop.elims)
                      apply simp_all
    apply (cases bop_vpr)
                  apply simp_all
      \<comment>\<open>integer division of two integers\<close>
      apply (unfold Semantics.smt_div_def Semantics.eucl_div_def Binop.smt_div_def Binop.eucl_div_def)
      apply fastforce
     \<comment>\<open>real division of two integers\<close>
    apply (unfold smt_real_div_def)
     apply (metis (mono_tags, opaque_lifting) Fract_of_int_quotient binop_result.distinct(5) binop_result.inject of_int_0_eq_iff of_rat_divide of_rat_of_int_eq val_rel_vpr_bpl.simps(5))
      \<comment>\<open>modulo\<close>
    apply (unfold Semantics.smt_mod_def Semantics.eucl_mod_def Binop.smt_mod_def Binop.eucl_mod_def)
    apply fastforce
   
   \<comment>\<open>operator between two reals\<close>
   apply (cases bop_vpr)
                  apply (simp_all add: of_rat_add of_rat_diff of_rat_mult smt_real_div_def of_rat_less of_rat_less_eq)
\<comment>\<open>operator between two booleans\<close>
  using real_divide_code apply auto[1]
  apply (cases bop_vpr) 
                apply simp_all
  done 

text \<open>Syntactic Viper-Boogie expression relation. Unfolding expressions are currently not considered.
If one considers permission introspection within unfolding expression (whose meaning is not clear 
as explored), then one would have to take into account different masks in the Boogie expression.
Carbon does not take this into account such kinds of expressions right now.
\<close>

inductive syn_exp_rel :: "ViperLang.program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> viper_expr \<Rightarrow> boogie_expr \<Rightarrow> bool"
  for Pr :: ViperLang.program and Trep :: "'a ty_repr_bpl" and Tr :: tr_vpr_bpl
  where
    \<comment>\<open>The only global variables in the Boogie encoding are Heap and Mask, which do not have a variable 
       counter part in Viper.\<close>
       VarRel: 
       "\<lbrakk> var_translation Tr x = Some y \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Trep Tr (ViperLang.Var x) (Lang.Var y)"
     | LitRel: 
       "\<lbrakk> lit_vpr_to_expr_bpl (const_repr Tr) lit = e_bpl \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Trep Tr (ViperLang.ELit lit) e_bpl"
     | FieldAccRel:
       "\<lbrakk> e_bpl = heap_read Tr (Lang.Var (heap_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId Trep), \<tau>_bpl] ; 
          syn_exp_rel Pr Trep Tr e e_rcv_bpl;
          (field_translation Tr f) = Some f_tr;
          e_f_bpl = Lang.Var f_tr;
          declared_fields Pr f = Some \<tau>;
          vpr_to_bpl_ty Trep \<tau> = Some \<tau>_bpl \<rbrakk> \<Longrightarrow>
         syn_exp_rel Pr Trep Tr (FieldAcc e f) e_bpl"
          \<comment>\<open>maybe \<^term>\<open>declared_fields Pr f \<noteq> None\<close> should be handled via a well-formedness condition \<close>
     | UnopRel:
       "\<lbrakk> unop_rel uop = uopb; 
          syn_exp_rel Pr Trep Tr e e_bpl \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Trep Tr (ViperLang.Unop uop e) (Lang.UnOp uopb e_bpl)"
     | BinopRel:
        "\<lbrakk> binop_rel bop = bopb;
           syn_exp_rel Pr Trep Tr e1 e1_bpl; 
           syn_exp_rel Pr Trep Tr e2 e2_bpl \<rbrakk> \<Longrightarrow>
           syn_exp_rel Pr Trep Tr (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
     | PermRel:
         "\<lbrakk> e_bpl = mask_read Tr (Lang.Var (mask_var Tr)) rcv_bpl f_bpl [TConSingle (TNormalFieldId Trep), the (vpr_to_bpl_ty Trep \<tau>)]; 
           syn_exp_rel Pr Trep Tr e rcv_bpl;
           (field_translation Tr f) = Some f_tr;
           f_bpl = Lang.Var f_tr;
           declared_fields Pr f = Some \<tau>;
           vpr_to_bpl_ty Trep \<tau> = Some \<tau>_bpl \<rbrakk> \<Longrightarrow>
           syn_exp_rel Pr Trep Tr (Perm e f) e_bpl"
          \<comment>\<open>maybe \<^term>\<open>declared_fields Pr f \<noteq> None\<close> should be handled via a well-formedness condition \<close>
     | FunAppRel: \<comment>\<open>maybe should abstract over how function calls are encoded\<close>
       "\<lbrakk> es_bpl = e_heap#e_args_bpl; 
          fun_translation Tr f = Some f_bpl;
          list_all2 (\<lambda>e_vpr e_bpl. syn_exp_rel Pr Trep Tr e_vpr e_bpl) es e_args_bpl;          
          e_heap = Lang.Var (heap_var Tr) \<rbrakk> \<Longrightarrow>
          syn_exp_rel Pr Trep Tr (FunApp f es) (FunExp f_bpl [] es_bpl)"

lemma syn_exp_rel_correct:
  assumes 
          "syn_exp_rel (program_total ctxt_vpr) Trep Tr e_vpr e_bpl" and 
          "ctxt_vpr, StateCons, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and

         \<comment>\<open>Need Boogie expression to reduce because Viper has lazy binary operators but Boogie does not.
           Thus, the Viper reduction on its own cannot be used to construct a Boogie reduction.\<close>
          "\<exists>v. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e_bpl ns v" and
          StateRel:"state_rel0 (program_total ctxt_vpr) A \<Lambda> Trep Tr \<omega> ns" and
          FInterpRel: "fun_interp_rel (program_total ctxt_vpr) (field_translation Tr) (fun_translation Tr) ctxt_vpr \<Gamma>" and
          HeapReadWf: "heap_read_wf Trep (create_ctxt_bpl A \<Lambda> \<Gamma>) (heap_read Tr)" and
          MaskReadWf: "mask_read_wf Trep (create_ctxt_bpl A \<Lambda> \<Gamma>) (mask_read Tr)"
        shows "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e_bpl ns (val_rel_vpr_bpl v1)"
  using assms(1-3)
proof(induction arbitrary: v1)
  case (VarRel x y)
  hence "get_store_total \<omega> x = Some v1"
    by (auto elim: TotalExpressions.RedVar_case)
  with StateRel \<open>var_translation Tr x = Some y\<close> show ?case
    unfolding state_rel0_def store_rel_def
    by (metis econtext_bpl.select_convs(2) option.inject red_expr_red_exprs.RedVar)
next
  case (LitRel lit e_bpl)
  hence "v1 = val_of_lit lit"
    by (auto elim: TotalExpressions.RedLit_case)
  moreover have "lit_translation_rel (create_ctxt_bpl A \<Lambda> \<Gamma>) ns (lit_vpr_to_expr_bpl (const_repr Tr))"
    apply (rule boogie_const_lit_rel)
    using state_rel0_boogie_const[OF StateRel]
    by simp
  ultimately show ?case
    using LitRel  
    unfolding state_rel0_def lit_translation_rel_def
    by blast
next
  case (FieldAccRel e_bpl e_rcv_bpl e_f_bpl \<tau>_bpl e f f_tr \<tau>)
  from FieldAccRel.prems obtain a where "ctxt_vpr, StateCons, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))" and HeapVal:"get_hh_total_full \<omega> (a,f) = v1" 
    using RedFieldNormal_case
    by blast
  hence LookupRcv:"A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef (Address a))"
    using FieldAccRel.IH FieldAccRel.prems \<open>e_bpl = _\<close> HeapReadWf
    unfolding heap_read_wf_def
    by (metis econtext_bpl.select_convs(1) econtext_bpl.select_convs(2) econtext_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))
  note FieldTy=\<open>declared_fields (program_total ctxt_vpr) f = Some \<tau>\<close>
  with StateRel have
      LookupField:"lookup_var \<Lambda> ns f_tr = Some (AbsV (AField (NormalField f_tr \<tau>)))"
    unfolding state_rel0_def field_rel_def
    using FieldAccRel.hyps(3) by fastforce

  from StateRel obtain h_bpl where
     LookupHeap:"lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap h_bpl))" and 
     HeapWellTy: "vbpl_absval_ty_opt Trep (AHeap h_bpl) = Some ((THeapId Trep) ,[])" and
     HeapRel:"heap_rel (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>) h_bpl"
    unfolding state_rel0_def heap_var_rel_def
    by blast  
  from HeapRel have
    "has_Some ((=) (val_rel_vpr_bpl (get_hh_total_full \<omega> (a,f))))
            (h_bpl (Address a) (NormalField f_tr \<tau>))"
    unfolding heap_rel_def
    using FieldTy \<open>field_translation Tr f = Some f_tr\<close>
    by (metis option.pred_inject(2) option.sel fst_conv snd_conv)
  hence HeapValBpl:"h_bpl (Address a) (NormalField f_tr \<tau>) = Some (val_rel_vpr_bpl v1)"
    using HeapVal
    by (metis (full_types) has_Some_iff)
  show ?case 
    apply (subst \<open>e_bpl =_ \<close>)
    apply (rule heap_read_wf_apply[OF HeapReadWf])
         apply (rule HeapValBpl)
    by (fastforce intro: LookupHeap LookupRcv LookupField RedVar HeapWellTy 
                  simp:  \<open>e_f_bpl = expr.Var f_tr\<close> \<open>vpr_to_bpl_ty _ \<tau>  = Some \<tau>_bpl\<close>)+
next
  case (UnopRel uop uopb e e_bpl)  
  then show ?case 
    by (auto elim!: TotalExpressions.RedUnop_case intro: Semantics.RedUnOp unop_rel_correct)
next
  case (BinopRel bop bopb e1 e1_bpl e2 e2_bpl)
  from this obtain w2 where 
        Red1:"\<exists>a. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e1_bpl ns a" and 
        Red2:"red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e2_bpl ns w2"
    by auto
  show ?case    
  proof (rule RedBinop_case[OF \<open>ctxt_vpr, StateCons, None \<turnstile> \<langle>Binop e1 bop e2; _\<rangle> [\<Down>]\<^sub>t _\<close>])    
    \<comment>\<open>lazy binop case\<close>
    fix v1'
    assume a:"ctxt_vpr, StateCons, None \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and eval_lazy:"eval_binop_lazy v1' bop = Some v1"
    hence Red3:"red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) e1_bpl ns (val_rel_vpr_bpl v1')"
      using BinopRel.IH(1) Red1
      by auto
    thus ?thesis
      using binop_lazy_rel_correct[OF eval_lazy \<open>binop_rel _ = _\<close>] Red2
      by (metis (no_types, opaque_lifting) BinopRel.prems(2) RedBinOp_case expr_eval_determ(1) option.distinct(1) option.sel)
  next    
    \<comment>\<open>nonlazy binop case\<close>
    fix v1' v2'
    assume "ctxt_vpr, StateCons, None \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1'" and 
           "ctxt_vpr, StateCons, None \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2'" and 
           "eval_binop v1' bop v2' = BinopNormal v1"
    thus ?thesis
      using BinopRel.IH Red1 Red2 \<open>binop_rel _ = _\<close> binop_nonlazy_rel_correct      
      by (blast intro: RedBinOp)
  qed
next
  case (PermRel e_bpl e_rcv_bpl f_bpl \<tau> e f f_tr \<tau>_bpl)
  from PermRel.prems obtain r where "ctxt_vpr, StateCons, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" 
    using RedPerm_case
    by blast  

  from StateRel have       
      LookupField:"lookup_var \<Lambda> ns f_tr = Some (AbsV (AField (NormalField f_tr \<tau>)))"
    unfolding state_rel0_def field_rel_def
    using PermRel StateRel
    by fastforce  
    
  from StateRel obtain m_bpl where
     LookupMask:"lookup_var \<Lambda> ns (mask_var Tr) = Some (AbsV (AMask m_bpl))" and 
     MaskRel:"mask_rel (program_total ctxt_vpr) (field_translation Tr) (get_mh_total_full \<omega>) m_bpl"
    unfolding state_rel0_def mask_var_rel_def
    by blast


  have FieldBplTy:"field_ty_fun_opt Trep (NormalField f_tr \<tau>) = Some (TFieldId Trep, [TConSingle (TNormalFieldId Trep), \<tau>_bpl])"
    using \<open>vpr_to_bpl_ty _ _ = _\<close>
    by simp

  show ?case
  proof (rule RedPerm_case)
    show "ctxt_vpr, StateCons, None \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      by (auto intro: PermRel)
  next
    assume "v1 = VPerm 0"
    assume "ctxt_vpr, StateCons, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null)"
    hence "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef Null)"
      using PermRel.IH PermRel.prems \<open>e_bpl = _\<close> MaskReadWf
      unfolding mask_read_wf_def
      by (metis econtext_bpl.select_convs(1) econtext_bpl.select_convs(2) econtext_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))
    with LookupField LookupMask MaskRel MaskReadWf \<open>e_bpl = _\<close> PermRel.hyps \<open>v1 = _\<close>
    show ?case
      unfolding mask_rel_def mask_read_wf_def 
      using FieldBplTy
      by (metis (mono_tags, opaque_lifting) econtext_bpl.select_convs(1) econtext_bpl.select_convs(2) econtext_bpl.select_convs(3) of_rat_0 option.sel red_expr_red_exprs.RedVar val_rel_vpr_bpl.simps(5))      
  next
    fix a
    assume "v1 = VPerm (Rep_prat (fst (snd (Rep_total_state (snd (snd \<omega>)))) (a, f)))"
    hence HeapVal:"v1 = VPerm (Rep_prat (get_mh_total_full \<omega> (a,f)))"
      by simp
    assume "ctxt_vpr, StateCons, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    hence RedRcv: "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_rcv_bpl,ns\<rangle> \<Down> AbsV (ARef (Address a))"
      using PermRel.IH PermRel.prems \<open>e_bpl = _\<close> MaskReadWf
      unfolding mask_read_wf_def
      by (metis econtext_bpl.select_convs(1) econtext_bpl.select_convs(2) econtext_bpl.select_convs(3) val_rel_vpr_bpl.simps(3))

    show ?case
      apply (subst \<open>e_bpl = _\<close>)
      apply (unfold HeapVal)
      apply (subst \<open>vpr_to_bpl_ty _ \<tau> = Some \<tau>_bpl\<close>)
      apply (simp only: val_rel_vpr_bpl.simps)
      apply (rule mask_read_wf_apply[OF MaskReadWf])
          defer
          apply (fastforce intro: red_expr_red_exprs.RedVar 
                                  LookupMask RedRcv LookupField 
                           simp: \<open>f_bpl = expr.Var f_tr\<close>  \<open>vpr_to_bpl_ty _ \<tau> = Some \<tau>_bpl\<close> FieldBplTy)+
      using MaskRel 
      unfolding mask_rel_def
      by (metis (mono_tags, lifting) PermRel.hyps(3) PermRel.hyps(5) fst_conv option.pred_inject(2) option.sel snd_conv)
  qed
next
  case (FunAppRel es_bpl e_heap e_args_bpl f f_bpl es)
  from \<open>ctxt_vpr, StateCons, None \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1\<close>
  obtain vs f_interp_vpr where     
      args_vpr: "list_all2 (\<lambda>e v. red_pure_exp_total ctxt_vpr StateCons None e \<omega> (Val v)) es vs" and
                "fun_interp_total ctxt_vpr f = Some f_interp_vpr" and
                "f_interp_vpr vs \<omega> = Some (Val v1)"
    by (blast elim: red_pure_exp_total_elims)
 
  from this obtain vs_bpl where BplArgsRed:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) es_bpl vs_bpl"
    using \<open>\<exists>a. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (FunExp f_bpl [] es_bpl) ns a\<close>    
    by (auto simp: bg_expr_list_red_all2)
  have "length es = length e_args_bpl" using FunAppRel.IH
    by (simp add: List.list_all2_conv_all_nth)
 have "length es = length vs" using args_vpr
      by (simp add: List.list_all2_conv_all_nth)

  have "list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns (val_rel_vpr_bpl v)) e_args_bpl vs"  
  proof (rule List.list_all2_all_nthI)
    show "length e_args_bpl = length vs"
      using \<open>length es = length e_args_bpl\<close> \<open>length es = length vs\<close>
      by simp
  next
    fix n
    assume "n < length e_args_bpl"
    hence "n < length es" using \<open>length es = length e_args_bpl\<close>
      by simp

    hence IHReq1:"ctxt_vpr, StateCons, None \<turnstile> \<langle>es ! n;\<omega>\<rangle> [\<Down>]\<^sub>t Val (vs ! n)"
      using args_vpr
      by (metis list_all2_conv_all_nth)

    have "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (es_bpl ! (Suc n)) ns (vs_bpl ! (Suc n))"
      using BplArgsRed \<open>n < length e_args_bpl\<close>    
      by (auto simp: \<open>es_bpl = _\<close> list_all2_conv_all_nth)
    hence IHReq2: "\<exists>v. red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (e_args_bpl ! n) ns v"
      by (auto simp: \<open>es_bpl = _\<close>)

    from IHReq1 IHReq2 FunAppRel.IH      
    show "A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e_args_bpl ! n,ns\<rangle> \<Down> val_rel_vpr_bpl (vs ! n)"
      by (auto simp: \<open>n < length e_args_bpl\<close> list_all2_conv_all_nth)
  qed      

  hence *:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) e_args_bpl (map val_rel_vpr_bpl vs)"
    by (simp add: list.rel_map(2))

  from StateRel obtain h_bpl where
     LookupHeap:"lookup_var \<Lambda> ns (heap_var Tr) = Some (AbsV (AHeap h_bpl))" and 
     HeapRel:"heap_rel (program_total ctxt_vpr) (field_translation Tr) (get_hh_total_full \<omega>) h_bpl"
    unfolding state_rel0_def heap_var_rel_def
    by blast

  from LookupHeap have "red_expr_bpl (create_ctxt_bpl A \<Lambda> \<Gamma>) (Var (heap_var Tr)) ns (AbsV (AHeap h_bpl))"
    by (auto intro: Semantics.RedVar)
  with * have A:"list_all2 (\<lambda>e v. red_expr A \<Lambda> \<Gamma> [] e ns v) ((Var (heap_var Tr))#e_args_bpl) ((AbsV (AHeap h_bpl))#(map val_rel_vpr_bpl vs))"
    by simp

  obtain f_interp_bpl where
       "\<Gamma> f_bpl = Some f_interp_bpl" and
       "fun_rel (program_total ctxt_vpr) (field_translation Tr) f_interp_vpr f_interp_bpl"
    using FInterpRel \<open>fun_translation Tr f = Some f_bpl\<close> \<open>fun_interp_total ctxt_vpr f = Some f_interp_vpr\<close>
    unfolding fun_interp_rel_def
    by (metis has_Some_iff)

  hence **:"(eval_heap_dep_bpl_fun f_interp_bpl (map val_rel_vpr_bpl vs) (AbsV (AHeap h_bpl))) = Some (val_rel_vpr_bpl v1)"
    using \<open>f_interp_vpr vs \<omega> = Some (Val v1)\<close> HeapRel
    unfolding fun_rel_def 
    apply (simp add: has_Some_iff)
    by (metis prod.collapse)    
  show ?case
    apply (rule RedFunOp)
      apply (simp add: \<open>\<Gamma> f_bpl = Some f_interp_bpl\<close>)     
     apply (simp add: bg_expr_list_red_all2)
     apply (subst \<open>es_bpl = _\<close>)
    apply (subst \<open>e_heap = _\<close>)    
     apply (rule A)
    using **
    by (simp add: eval_heap_dep_bpl_fun_def)
qed


lemma syn_exp_rel_correct_2:
  assumes 
      "syn_exp_rel (program_total ctxt_vpr) Trep Tr e_vpr e_bpl" and 
      "ctxt_vpr, StateCons, None \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
      "\<exists>v. red_expr_bpl ctxt e_bpl ns v" and
      StateRel:"state_rel (program_total ctxt_vpr) Trep Tr ctxt wdmask \<omega>def \<omega> ns" and
      TrWf: "tr_wf (program_total ctxt_vpr) ctxt_vpr ctxt Trep Tr"
shows "red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)"
  using assms tr_wf_def state_rel_def syn_exp_rel_correct
  by (metis (mono_tags, lifting) econtext_bpl.surjective old.unit.exhaust)

subsection \<open>Semantic approach\<close>

lemma exp_rel_vpr_bpl_intro:
assumes "\<And> StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                    (\<exists>v2. (red_expr_bpl ctxt e_bpl ns v2) \<and> (val_rel_vpr_bpl v1 = v2))"                   
shows "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by auto

lemma exp_rel_vpr_bpl_elim:
  assumes "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl" and
          "(\<And> StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                    (\<exists>v2. (red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)) \<and> (val_rel_vpr_bpl v1 = v2))) \<Longrightarrow> P"
  shows P
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by blast

lemma exp_rel_vpr_bpl_elim_2:
  assumes "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl" and
          "(\<And> \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                    red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)) \<Longrightarrow> P"
  shows P
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by blast

lemma exp_rel_var: 
  assumes VarRel:"\<And> \<omega> \<omega>_def ns. R \<omega>_def \<omega> ns \<Longrightarrow> (\<exists>val_vpr. ((get_store_total \<omega>) var_vpr) = Some val_vpr \<and>
                                  lookup_var (var_context ctxt) ns var_bpl = Some (val_rel_vpr_bpl val_vpr))"
  shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Var var_vpr) (Lang.Var var_bpl)"  
proof(rule exp_rel_vpr_bpl_intro)
  fix StateCons \<omega> \<omega>_def \<omega>_def_opt ns v1
  assume R:"R \<omega>_def \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ViperLang.Var var_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  hence VprLookup:"get_store_total \<omega> var_vpr = Some v1"
    by (auto elim: TotalExpressions.RedVar_case)
  show "\<exists>v2. red_expr_bpl ctxt (expr.Var var_bpl) ns v2 \<and> val_rel_vpr_bpl v1 = v2"
    apply (rule exI[where ?x="val_rel_vpr_bpl v1"])
    apply (rule conjI)
     apply (rule RedVar)
    using VarRel[OF R] VprLookup
     apply (fastforce  simp: VarRel[OF R])
    by simp
qed

lemma exp_rel_lit:
  assumes LitRel: "\<And> \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> lit_translation_rel ctxt ns litT" and
                  "litT lit_vpr = e_bpl"
  shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.ELit lit_vpr) e_bpl"
proof(rule exp_rel_vpr_bpl_intro)
  fix StateCons \<omega> \<omega>_def \<omega>_def_opt ns v1
  assume R:"R \<omega>_def_opt \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def \<turnstile> \<langle>ViperLang.ELit lit_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  hence "v1 = (val_of_lit lit_vpr)"
    using TotalExpressions.RedLit_case by blast
  show "\<exists>v2. red_expr_bpl ctxt e_bpl ns v2 \<and> val_rel_vpr_bpl v1 = v2"
    apply (rule exI[where ?x="val_rel_vpr_bpl v1"])    
    apply (rule conjI)
    using LitRel[OF R] \<open>v1 = _\<close> \<open>litT lit_vpr = e_bpl\<close>
    unfolding lit_translation_rel_def    
    by auto
qed

lemma exp_rel_field_access:
  assumes 
       StateRel0: "\<And> \<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> state_rel0 Pr (type_context ctxt) (var_context ctxt) TyRep Tr \<omega> ns" and
       HeapReadWf: "heap_read_wf TyRep ctxt hread" and
       "e_bpl = hread (expr.Var (heap_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
       RcvRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e e_rcv_bpl" and
       FieldRel: "field_translation Tr f = Some f_tr" and
       "e_f_bpl = Lang.Var f_tr" and
       FieldTy: "declared_fields Pr f = Some \<tau>" and
       FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
     shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (FieldAcc e f) e_bpl"
proof(rule exp_rel_vpr_bpl_intro)
  fix StateCons \<omega> \<omega>_def \<omega>_def_opt ns v1
  assume R:"R \<omega>_def \<omega> ns"
  assume RedVpr: "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  from this obtain a where "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))" and HeapVal:"get_hh_total_full \<omega> (a,f) = v1" 
    using RedFieldNormal_case
    by blast

  hence LookupRcv:"red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef (Address a)))"
    using exp_rel_vpr_bpl_elim[OF RcvRel] RedVpr \<open>e_bpl = _\<close> HeapReadWf
    unfolding heap_read_wf_def
    by (metis R val_rel_vpr_bpl.simps(3))
  from FieldTy FieldRel StateRel0[OF R] have 
    LookupField:"lookup_var (var_context ctxt) ns f_tr = Some (AbsV (AField (NormalField f_tr \<tau>)))"
    unfolding state_rel0_def field_rel_def
    by fastforce

  from StateRel0[OF R] obtain h_bpl where
    LookupHeap:"lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap h_bpl))" and 
    HeapWellTy: "vbpl_absval_ty_opt TyRep (AHeap h_bpl) = Some ((THeapId TyRep), [])" and
    HeapRel: "heap_rel Pr (field_translation Tr) (get_hh_total_full \<omega>) h_bpl"
  unfolding state_rel0_def heap_var_rel_def
  by blast

  from HeapRel have
    "has_Some ((=) (val_rel_vpr_bpl (get_hh_total_full \<omega> (a,f))))
            (h_bpl (Address a) (NormalField f_tr \<tau>))"
    unfolding heap_rel_def
    using FieldTy \<open>field_translation Tr f = Some f_tr\<close>
    by (metis option.pred_inject(2) option.sel fst_conv snd_conv)

  hence HeapValBpl:"h_bpl (Address a) (NormalField f_tr \<tau>) = Some (val_rel_vpr_bpl v1)"
    using HeapVal
    by (metis (full_types) has_Some_iff)

  show "\<exists>v2. red_expr_bpl ctxt e_bpl ns v2 \<and> val_rel_vpr_bpl v1 = v2"
    apply (rule exI, rule conjI)
    apply (subst \<open>e_bpl =_ \<close>)
    apply (rule heap_read_wf_apply[OF HeapReadWf])
         apply (rule HeapValBpl)
    by (fastforce intro: LookupHeap LookupRcv LookupField RedVar HeapWellTy 
                  simp:  \<open>e_f_bpl = expr.Var f_tr\<close> \<open>vpr_to_bpl_ty _ \<tau>  = Some \<tau>_bpl\<close>)+
qed

lemma exp_rel_unop:
  assumes 
    UopRel:"unop_rel uop = uopb" and 
    ExpRel:"exp_rel_vpr_bpl R ctxt_vpr ctxt e e_bpl"
  shows 
    "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Unop uop e) (Lang.UnOp uopb e_bpl)"
  apply (rule exp_rel_vpr_bpl_intro)
  apply (rule exp_rel_vpr_bpl_elim[OF ExpRel])
  by (auto elim!: TotalExpressions.RedUnop_case intro!: Semantics.RedUnOp unop_rel_correct[OF _ UopRel] )

lemma exp_rel_binop:
  assumes
   BopRel: "binop_rel bop = bopb" and
   \<comment>\<open>If the binary operation is lazy, we need a well-typedness result on e2, since the Viper reduction
      of \<^term>\<open>Binop e1 bop e2\<close> might not need to reduce e2 if e1 establishes the result.\<close>
   RedE2Bpl: "binop_lazy bop \<noteq> None \<Longrightarrow> (\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> \<exists>b. red_expr_bpl ctxt e2_bpl ns (BoolV b))" and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
 shows
   "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
proof (rule exp_rel_vpr_bpl_intro)
  fix StateCons \<omega> \<omega>_def \<omega>_def_opt ns v
  assume R: "R \<omega>_def \<omega> ns"
  assume RedVpr: "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ViperLang.Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  have "red_expr_bpl ctxt (e1_bpl \<guillemotleft>bopb\<guillemotright> e2_bpl) ns (val_rel_vpr_bpl v)"
  proof (rule RedBinop_case[OF \<open>ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>Binop e1 bop e2; _\<rangle> [\<Down>]\<^sub>t _\<close>])
    \<comment>\<open>lazy binop case\<close>
    fix v1
    assume RedE1Vpr:"ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and eval_lazy:"eval_binop_lazy v1 bop = Some v"
    obtain b1 where "v1 = VBool b1"
      by (rule eval_binop_lazy.elims[OF eval_lazy]) auto
            
    have RedE1Bpl:"red_expr_bpl ctxt e1_bpl ns (val_rel_vpr_bpl v1)"
      apply (rule exp_rel_vpr_bpl_elim[OF E1Rel])
      using R RedE1Vpr
      by auto

    from eval_lazy have "binop_lazy bop \<noteq> None"
      using eval_binop_lazy_iff_2
      by (metis option.distinct(1))
      
    from RedE2Bpl[OF _ R] obtain b2 where RedE2Bpl':"red_expr_bpl ctxt e2_bpl ns (BoolV b2)"
      using \<open>binop_lazy bop \<noteq> None\<close>
      by metis

    from BopRel \<open>binop_lazy bop \<noteq> None\<close>
    have BopEvalNormalBpl: "binop_eval_val bopb (BoolV b1) (BoolV b2) \<noteq> None"
      by (cases bop) auto

    show ?thesis
      apply (rule)
        apply (rule RedE1Bpl, rule RedE2Bpl')
      using binop_lazy_rel_correct[OF eval_lazy \<open>binop_rel _ = _\<close>] BopEvalNormalBpl
      by (auto simp: \<open>v1 = _\<close>)     
  next
    \<comment>\<open>nonlazy binop case\<close>
    fix v1 v2
    assume RedE1Vpr: "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and 
           RedE2Vpr: "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
           BopEvalNormalVpr: "eval_binop v1 bop v2 = BinopNormal v"

    have RedE1Bpl:"red_expr_bpl ctxt e1_bpl ns (val_rel_vpr_bpl v1)"
      apply (rule exp_rel_vpr_bpl_elim[OF E1Rel])
      using R RedE1Vpr
      by auto

    moreover have RedE2Bpl:"red_expr_bpl ctxt e2_bpl ns (val_rel_vpr_bpl v2)"
      apply (rule exp_rel_vpr_bpl_elim[OF E2Rel])
      using R RedE2Vpr
      by auto

    ultimately show ?thesis
      using  BopEvalNormalVpr \<open>binop_rel _ = _\<close> binop_nonlazy_rel_correct      
      by (blast intro: RedBinOp)
  qed

  thus "\<exists>v2. red_expr_bpl ctxt (e1_bpl \<guillemotleft>bopb\<guillemotright> e2_bpl) ns v2 \<and> val_rel_vpr_bpl v = v2"
    by simp
qed

lemma exp_rel_binop_eager:
  assumes
   BopRel: "binop_rel bop = bopb \<and> binop_lazy bop = None"and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
 shows
   "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
  using assms
  by (auto intro: exp_rel_binop)

lemma exp_rel_binop_lazy:
  assumes
   BopRel: "binop_rel bop = bopb \<and> binop_lazy bop \<noteq> None" and
   RedE2Bpl: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> \<exists>b. red_expr_bpl ctxt e2_bpl ns (BoolV b)" and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
 shows
   "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
  using assms
  by (auto intro: exp_rel_binop)



\<comment>\<open>TODO: semantic lemmas for expression relation with permission introspection, function evaluation, etc...\<close>

end