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

fun binop_swap_rel :: "ViperLang.binop \<rightharpoonup> Lang.binop"
  where 
    "binop_swap_rel ViperLang.Gt = Some Lang.Lt"
  | "binop_swap_rel ViperLang.Gte = Some Lang.Le"
  | "binop_swap_rel ViperLang.Lt = Some Lang.Gt"
  | "binop_swap_rel ViperLang.Lte = Some Lang.Ge"
  | "binop_swap_rel _ = None"   

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
          "binop_rel bop_vpr = bop_bpl" and
          "bop_vpr \<noteq> Mult"
  shows   "binop_eval_val bop_bpl (val_rel_vpr_bpl v1_vpr) (val_rel_vpr_bpl v2_vpr) = Some (val_rel_vpr_bpl v_vpr)"
  using assms
  apply (cases rule: eval_binop.elims)
                      apply simp_all
    apply (cases bop_vpr)
                  apply simp_all
      \<comment>\<open>integer division of two integers\<close>
      apply (unfold Semantics.smt_div_def Semantics.eucl_div_def Binop.smt_div_def Binop.eucl_div_def)
        apply fastforce

       apply (unfold Semantics.smt_real_div_def)
       apply (smt (verit) binop_result.distinct(5) binop_result.inject of_int_0_eq_iff of_rat_rat val_rel_vpr_bpl.simps(5))

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
   apply (cases bop_vpr) 
                 apply simp_all
   apply (cases bop_vpr) 
                 apply simp_all
       apply (unfold Semantics.smt_real_div_def)
   apply (metis (mono_tags, opaque_lifting) binop_result.distinct(5) binop_result.inject of_rat_divide of_rat_eq_0_iff of_rat_of_int_eq val_rel_vpr_bpl.simps(5))
  apply (cases bop_vpr)
                apply simp_all
       apply (unfold Semantics.smt_real_div_def)
  by (metis (mono_tags, lifting) binop_result.distinct(5) binop_result.inject of_int_eq_0_iff of_rat_divide of_rat_of_int_eq val_rel_vpr_bpl.simps(5))

subsection \<open>Semantic approach\<close>

lemma exp_rel_vpr_bpl_intro:
assumes "\<And> StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                    (\<exists>v2. (red_expr_bpl ctxt e_bpl ns v2) \<and> (val_rel_vpr_bpl v1 = v2))"                   
shows "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by auto

lemma exp_rel_vpr_bpl_intro_2:
assumes "\<And> StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                     red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)"                   
shows "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by auto

lemma exp_rel_vpr_bpl_elim:
  assumes "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl" and
          "(\<And> StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1. R \<omega>_def1 \<omega> ns \<Longrightarrow> 
                    (ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow> 
                    ( (red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)))) \<Longrightarrow> P"
  shows P
  using assms
  unfolding exp_rel_vpr_bpl_def exp_rel_vb_single_def 
  by blast

lemma exp_rel_vpr_bplD:
  assumes "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
      and "R \<omega>_def1 \<omega> ns"
      and "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
    shows "red_expr_bpl ctxt e_bpl ns (val_rel_vpr_bpl v1)"
  using assms
  by (auto elim: exp_rel_vpr_bpl_elim)


lemma exp_rel_equiv_vpr:
  assumes "\<And>v1 StateCons \<omega> \<omega>_def_opt. (ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e1_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1) \<Longrightarrow>
                          (ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e2_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1)" and
          "exp_rel_vpr_bpl R ctxt_vpr ctxt e2_vpr e_bpl"
        shows "exp_rel_vpr_bpl R ctxt_vpr ctxt e1_vpr e_bpl"
  using assms
  by (blast intro: exp_rel_vpr_bpl_intro elim: exp_rel_vpr_bpl_elim)

lemma exp_rel_conseq:
  assumes "exp_rel_vpr_bpl R ctxt_vpr ctxt e1_vpr e_bpl" and
          "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> R' \<omega>def \<omega> ns"
  shows "exp_rel_vpr_bpl R' ctxt_vpr ctxt e1_vpr e_bpl"
  oops

lemma exp_rel_equiv_bpl:
  assumes "\<And>ns v. red_expr_bpl ctxt e1_bpl ns v \<Longrightarrow>
                    red_expr_bpl ctxt e2_bpl ns v" and
          "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e1_bpl"
        shows "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e2_bpl"
  using assms
  by (blast intro: exp_rel_vpr_bpl_intro elim: exp_rel_vpr_bpl_elim)

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
       (* TODO: weaken assumption on R *)
       StateRel0: "\<And> \<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> state_rel0 Pr StateCons (type_interp ctxt) (var_context ctxt) TyRep Tr AuxPred \<omega>def \<omega> ns" and
       HeapReadWf: "heap_read_wf TyRep ctxt (heap_read Tr)" and
       "e_bpl = (heap_read Tr) (expr.Var (heap_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and
       FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
\<comment>\<open>receiver relation last, since that is the "implementation-independent" premise\<close>
       RcvRel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e e_rcv_bpl" 
     shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (FieldAcc e f) e_bpl"
proof(rule exp_rel_vpr_bpl_intro)
  from FieldRelSingle obtain f_tr \<tau> where
       FieldRel: "field_translation Tr f = Some f_tr" and
       "e_f_bpl = Lang.Var f_tr" and    
       FieldTy: "declared_fields Pr f = Some \<tau>" and
       FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
    by (auto elim: field_rel_single_elim)

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

  from heap_rel_elim[OF HeapRel] have
    "(h_bpl (Address a, NormalField f_tr \<tau>)) = Some (val_rel_vpr_bpl (get_hh_total_full \<omega> (a,f)))"    
    using FieldTy \<open>field_translation Tr f = Some f_tr\<close>
    by fastforce

  hence HeapValBpl:"h_bpl (Address a, NormalField f_tr \<tau>) = Some (val_rel_vpr_bpl v1)"
    using HeapVal
    by blast

  show "\<exists>v2. red_expr_bpl ctxt e_bpl ns v2 \<and> val_rel_vpr_bpl v1 = v2"
    apply (rule exI, rule conjI)
    apply (subst \<open>e_bpl =_ \<close>)
    apply (rule heap_read_wf_apply[OF HeapReadWf])
         apply (rule HeapValBpl)
    by (fastforce intro: LookupHeap LookupRcv LookupField RedVar HeapWellTy 
                  simp:  \<open>e_f_bpl = expr.Var f_tr\<close> FieldTyBpl)+
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

lemma exp_rel_condexp:
  assumes ExpRel1: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl"
      and ExpRel2: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
      and ExpRel3: "exp_rel_vpr_bpl R ctxt_vpr ctxt e3 e3_bpl"
    shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.CondExp e1 e2 e3) (Lang.CondExp e1_bpl e2_bpl e3_bpl)"
proof (rule exp_rel_vpr_bpl_intro_2)
  fix StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v
  assume R: "R \<omega>_def1 \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>pure_exp.CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"

  thus "red_expr_bpl ctxt (expr.CondExp e1_bpl e2_bpl e3_bpl) ns (val_rel_vpr_bpl v)"
  proof (cases)
    case RedCondExpTrue
    hence "red_expr_bpl ctxt e1_bpl ns (BoolV True)" and "red_expr_bpl ctxt e2_bpl ns (val_rel_vpr_bpl v)"
      using exp_rel_vpr_bplD[OF ExpRel1 R] exp_rel_vpr_bplD[OF ExpRel2 R]
      by fastforce+
    then show ?thesis 
      by (auto intro!: Semantics.RedCondExpTrue)
  next
    case RedCondExpFalse
    hence "red_expr_bpl ctxt e1_bpl ns (BoolV False)" and "red_expr_bpl ctxt e3_bpl ns (val_rel_vpr_bpl v)"
      using exp_rel_vpr_bplD[OF ExpRel1 R] exp_rel_vpr_bplD[OF ExpRel3 R]
      by fastforce+
    then show ?thesis
      by (auto intro!: Semantics.RedCondExpFalse)
  qed
qed

lemma exp_rel_oldexp:
  assumes "\<And>\<omega>def \<omega> ns. R \<omega>def \<omega> ns \<Longrightarrow> ROld (\<omega>def \<lparr> get_total_full := (the (get_trace_total \<omega> lbl)) \<rparr>) 
                                             (\<omega> \<lparr> get_total_full := (the (get_trace_total \<omega> lbl)) \<rparr>) 
                                             ns"
      and "exp_rel_vpr_bpl ROld ctxt_vpr ctxt e e_bpl"
    shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Old lbl e) e_bpl"


subsubsection \<open>Binary Operations\<close>

lemma exp_rel_binop:
  assumes
   BopRel: "binop_rel bop = bopb" and
           "bop \<noteq> Mult" and
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
      using  BopEvalNormalVpr \<open>binop_rel _ = _\<close> binop_nonlazy_rel_correct \<open>bop \<noteq> _\<close>  
      by (blast intro: RedBinOp)
  qed

  thus "\<exists>v2. red_expr_bpl ctxt (e1_bpl \<guillemotleft>bopb\<guillemotright> e2_bpl) ns v2 \<and> val_rel_vpr_bpl v = v2"
    by simp
qed

lemma exp_rel_binop_eager:
  assumes
   BopRel: "binop_rel bop = bopb \<and> binop_lazy bop = None \<and> bop \<noteq> Mult" and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
 shows
   "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
  using assms
  by (auto intro: exp_rel_binop)

lemma binop_eval_swap:
  assumes "binop_rel bop = bopb"
      and "binop_swap_rel bop = Some bopb_swap"
      and "binop_eval_val bopb v1 v2 = Some v"
    shows "binop_eval_val bopb_swap v2 v1 = Some v"
  apply (insert assms)
  apply (rule lit_val_elim[where ?v=v1]; rule lit_val_elim[where ?v=v2]; cases bop)
  by simp_all

lemma exp_rel_binop_switch_operands:
  assumes BopSwapRel: "binop_swap_rel bop = Some bopb_swap"
      and E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl"
      and E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"     
    shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e2_bpl bopb_swap e1_bpl)"
proof -
  let ?bopb = "binop_rel bop"

  from BopSwapRel have "binop_lazy bop = None \<and> bop \<noteq> Mult"
    by (cases bop) auto

  with E1Rel E2Rel exp_rel_binop_eager
  have ExpRelNormal: "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl ?bopb e2_bpl)"
    by blast

  show ?thesis
  proof (rule exp_rel_vpr_bpl_intro_2)
    fix StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v1
    assume "R \<omega>_def1 \<omega> ns"
       and "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>ViperLang.Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
    hence "red_expr_bpl ctxt (Lang.BinOp e1_bpl ?bopb e2_bpl) ns (val_rel_vpr_bpl v1)" (is "red_expr_bpl ctxt _ ns ?vb")
      using ExpRelNormal
      by (meson exp_rel_vpr_bpl_elim)

    from this obtain vb1 vb2 where
           "red_expr_bpl ctxt e1_bpl ns vb1" and "red_expr_bpl ctxt e2_bpl ns vb2"
         and "binop_eval_val ?bopb vb1 vb2 = (Some ?vb)"     
      by auto

    moreover from this have "binop_eval_val bopb_swap vb2 vb1 = (Some ?vb)"
      using binop_eval_swap BopSwapRel
      by blast

    ultimately show "red_expr_bpl ctxt (Lang.BinOp e2_bpl bopb_swap e1_bpl) ns ?vb"
      by (auto intro: RedBinOp)
  qed
qed

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

text \<open>For multiplication, we need other rules, because there is a mismatch 
between Viper and Boogie. Viper permits multiplication between integers and permissions, 
while Boogie only supports the same type for both operands.\<close>

text \<open>The following rule captures the case when the operands have the same type.\<close>

lemma exp_rel_binop_mult_no_conv:
  assumes
   BopRel: "binop_rel bop = bopb \<and> binop_lazy bop = None \<and> bop = Mult" and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl" and
   RedBplSameType: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> 
                (\<exists>v1 v2. red_expr_bpl ctxt e1_bpl ns v1 \<and> red_expr_bpl ctxt e2_bpl ns v2 \<and>
                         type_of_val (type_interp ctxt) v1 = type_of_val (type_interp ctxt) v2)"              
  shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp e1_bpl bopb e2_bpl)"
proof (rule exp_rel_vpr_bpl_intro_2)
  fix StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v
  assume R: "R \<omega>_def1 \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"

  thus "red_expr_bpl ctxt (e1_bpl \<guillemotleft>bopb\<guillemotright> e2_bpl) ns (val_rel_vpr_bpl v)"
  proof (cases)
    case (RedBinop v1 v2)   

    have RedE1Bpl:"red_expr_bpl ctxt e1_bpl ns (val_rel_vpr_bpl v1)"
      apply (rule exp_rel_vpr_bpl_elim[OF E1Rel])
      using R RedBinop
      by auto

    moreover have RedE2Bpl:"red_expr_bpl ctxt e2_bpl ns (val_rel_vpr_bpl v2)"
      apply (rule exp_rel_vpr_bpl_elim[OF E2Rel])
      using R RedBinop
      by auto

    show ?thesis
    proof (rule Semantics.RedBinOp[OF RedE1Bpl RedE2Bpl])

        have v1IntPerm: "(\<exists>i. v1 = VInt i) \<or> (\<exists>r. v1 = VPerm r)"
          apply (insert RedBinop BopRel)
          by (cases v1; cases v2; simp_all)
        moreover have v2IntPerm: "(\<exists>i. v2 = VInt i) \<or> (\<exists>r. v2 = VPerm r)"
          apply (insert RedBinop BopRel)
          by (cases v1; cases v2; simp_all)

        from RedBplSameType[OF R] obtain v1_bpl v2_bpl where 
          "red_expr_bpl ctxt e1_bpl ns v1_bpl"
        and "red_expr_bpl ctxt e2_bpl ns v2_bpl"
        and BplSameType: "type_of_val (type_interp ctxt) v1_bpl = type_of_val (type_interp ctxt) v2_bpl"
          by blast
        hence "val_rel_vpr_bpl v1 = v1_bpl" and "val_rel_vpr_bpl v2 = v2_bpl"
          using  RedE1Bpl RedE2Bpl expr_eval_determ(1)
          by blast+
        hence BplSameType': "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v1) = type_of_val (type_interp ctxt) (val_rel_vpr_bpl v2)"
          using BplSameType
          by blast
       
        consider (IntOp) i1 i2 where "val_rel_vpr_bpl v1 = IntV i1" and "val_rel_vpr_bpl v2 = IntV i2" |
                 (RealOp) r1 r2 where "val_rel_vpr_bpl v1 = RealV r1" and "val_rel_vpr_bpl v2 = RealV r2"
        proof -
          from v1IntPerm consider i where "v1 = VInt i" | r where "v1 = VPerm r"
            by auto
          thus ?thesis
          proof cases
            case 1
            hence *: "val_rel_vpr_bpl v1 = IntV i"
              by simp
            hence "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v2) = TPrim TInt"
              using BplSameType'
              by auto
            hence "\<exists>i2. val_rel_vpr_bpl v2 = IntV i2"
              by (metis ty_to_closed.simps(1) vc_tint_intv vc_type_of_val.simps)
          
            then show ?thesis 
              using * IntOp
              by blast
          next
            case 2
            hence *: "val_rel_vpr_bpl v1 = RealV (real_of_rat r)"
              by simp
            hence "type_of_val (type_interp ctxt) (val_rel_vpr_bpl v2) = TPrim TReal"
              using BplSameType'
              by auto
            hence "\<exists>i2. val_rel_vpr_bpl v2 = RealV i2"
              by (simp add: treal_realv)          
            then show ?thesis 
              using * RealOp
              by blast
          qed
        qed               
        thus "binop_eval_val bopb (val_rel_vpr_bpl v1) (val_rel_vpr_bpl v2) = Some (val_rel_vpr_bpl v)"
        proof cases
          case IntOp
          then show ?thesis 
            apply (insert BopRel RedBinop IntOp)
             apply (rule val_rel_vpr_bpl.elims[OF IntOp(1)])
                 apply simp_all
             apply (rule val_rel_vpr_bpl.elims[OF IntOp(2)])
                apply simp_all
            apply (cases bop)
            apply simp_all
            by fastforce
        next
          case RealOp
          show ?thesis 
            apply (insert RealOp BopRel RedBinop)
             apply (rule val_rel_vpr_bpl.elims[OF RealOp(1)])
                 apply simp_all
             apply (rule val_rel_vpr_bpl.elims[OF RealOp(2)])
                apply simp_all
            apply (cases bop)
                          apply simp_all
            by (metis of_rat_mult val_rel_vpr_bpl.simps(5))
        qed
      qed
    qed (insert assms, auto)
  qed

  text \<open>The following rule captures one case when the first Viper operand is an integer expression,
        but the resulting type of the operation is a permission. In practice, the Viper implementation
        ensures that the other case (where the second operand is an integer expression) cannot occur
        in the AST.\<close>

lemma exp_rel_binop_mult_permdiv_conv:
  assumes
   BopRel: "binop_rel bop = bopb \<and> binop_lazy bop = None \<and> bop \<in> { Mult, PermDiv }" and
   E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl" and
   E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl" and
  RedE1BplInt: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> (\<exists>i1. red_expr_bpl ctxt e1_bpl ns (IntV i1))" and       
  RedE2BplReal: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> (\<exists>r2. red_expr_bpl ctxt e2_bpl ns (RealV r2))"       
  shows
     "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 bop e2) (Lang.BinOp (Lang.UnOp IntToReal e1_bpl) bopb e2_bpl)"
proof (rule exp_rel_vpr_bpl_intro_2)
  fix StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v
  assume R: "R \<omega>_def1 \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"

  thus "red_expr_bpl ctxt ((Lang.UnOp IntToReal e1_bpl) \<guillemotleft>bopb\<guillemotright> e2_bpl) ns (val_rel_vpr_bpl v)"
  proof (cases)
    case (RedBinop v1 v2)     

    have "red_expr_bpl ctxt e1_bpl ns (val_rel_vpr_bpl v1)"
      apply (rule exp_rel_vpr_bpl_elim[OF E1Rel])
      using R RedBinop
      by auto
    moreover with RedE1BplInt[OF R] obtain i1 where EqV1: "val_rel_vpr_bpl v1 = IntV i1"
      using expr_eval_determ(1)
      by blast 
    ultimately have RedConvE1Bpl: "red_expr_bpl ctxt (Lang.UnOp IntToReal e1_bpl) ns (RealV (real_of_int i1))"
      by (auto intro!: Semantics.RedUnOp)
      

    have RedE2Bpl:"red_expr_bpl ctxt e2_bpl ns (val_rel_vpr_bpl v2)"
      apply (rule exp_rel_vpr_bpl_elim[OF E2Rel])
      using R RedBinop
      by auto
    with RedE2BplReal[OF R] obtain r2 where EqV2:"val_rel_vpr_bpl v2 = RealV r2"
      using expr_eval_determ(1)
      by blast

    show ?thesis
    proof (rule Semantics.RedBinOp[OF RedConvE1Bpl RedE2Bpl])
      show "binop_eval_val bopb (RealV (real_of_int i1)) (val_rel_vpr_bpl v2) = Some (val_rel_vpr_bpl v)"
        apply (insert BopRel RedBinop)
        apply (simp add: EqV2)
        apply (rule val_rel_vpr_bpl.elims[OF EqV1])
            apply simp_all
         apply (rule val_rel_vpr_bpl.elims[OF EqV2])
            apply simp_all
        apply (cases bop)
                      apply simp_all
         apply (metis of_rat_mult of_rat_of_int_eq val_rel_vpr_bpl.simps(5))
            apply (simp add: smt_real_div_def)
        by (metis binop_result.distinct(5) binop_result.inject of_rat_divide of_rat_of_int_eq val_rel_vpr_bpl.simps(5))
    qed
  qed (insert assms, auto)
qed

text \<open>The Boogie type checker rewrites equalities of Boolean expressions into iff operations\<close>

lemma exp_rel_binop_eq_iff:
  assumes E1Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e1 e1_bpl"
      and E2Rel: "exp_rel_vpr_bpl R ctxt_vpr ctxt e2 e2_bpl"
      and RedE1BplBool: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> (\<exists>b1. red_expr_bpl ctxt e1_bpl ns (BoolV b1))"
      and RedE2BplBool: "\<And>\<omega>_def \<omega> ns. R \<omega>_def \<omega> ns \<Longrightarrow> (\<exists>b2. red_expr_bpl ctxt e2_bpl ns (BoolV b2))"             
    shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (ViperLang.Binop e1 ViperLang.Eq e2) (e1_bpl \<guillemotleft>Lang.Iff\<guillemotright> e2_bpl)"
proof (rule exp_rel_vpr_bpl_intro_2)
  fix StateCons \<omega> \<omega>_def1 \<omega>_def2_opt ns v
  assume R: "R \<omega>_def1 \<omega> ns"
  assume "ctxt_vpr, StateCons, \<omega>_def2_opt \<turnstile> \<langle>Binop e1 ViperLang.binop.Eq e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"

  thus "red_expr_bpl ctxt (e1_bpl \<guillemotleft>Lang.Iff\<guillemotright> e2_bpl) ns (val_rel_vpr_bpl v)"
  proof (cases)
    case (RedBinop v1 v2)  
   
    have RedE1Bpl: "red_expr_bpl ctxt e1_bpl ns (val_rel_vpr_bpl v1)" (is "red_expr_bpl ctxt e1_bpl ns ?v1b")
      apply (rule exp_rel_vpr_bpl_elim[OF E1Rel])
      using R RedBinop
      by auto
    from this obtain b1 where "?v1b = BoolV b1"
      using RedE1BplBool[OF R] expr_eval_determ(1)
      by blast
    hence "v1 = VBool b1"
      by (cases v1) auto

    have RedE2Bpl: "red_expr_bpl ctxt e2_bpl ns (val_rel_vpr_bpl v2)" (is "red_expr_bpl ctxt e2_bpl ns ?v2b")
      apply (rule exp_rel_vpr_bpl_elim[OF E2Rel])
      using R RedBinop
      by auto
    from this obtain b2 where "?v2b = BoolV b2"
      using RedE2BplBool[OF R] expr_eval_determ(1)
      by blast
    hence "v2 = VBool b2"
       by (cases v2) auto

    show ?thesis
      apply (insert RedBinop)
      apply (rule Semantics.RedBinOp[OF RedE1Bpl RedE2Bpl])
      apply (simp add: \<open>v1 = _\<close> \<open>v2 = _\<close>)
      by fastforce
  qed (simp)
qed           

\<comment>\<open>TODO: semantic lemmas for expression relation with permission introspection, function evaluation, etc...\<close>

subsection \<open>Proving expression reduction from expression relation\<close>

lemma exp_rel_ref_access:
  assumes StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns"
      and RedRcvVpr: "ctxt_vpr, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
      and ExpRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e e_r_bpl"       
    shows "red_expr_bpl ctxt e_r_bpl ns (AbsV (ARef r))"
  using assms
  by (metis exp_rel_vpr_bpl_elim val_rel_vpr_bpl.simps(3))

lemma exp_rel_perm_access:
  assumes 
       MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and
       StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
       FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
       RedRcvBpl: "red_expr_bpl ctxt e_rcv_bpl ns (AbsV (ARef r))"               
     shows "red_expr_bpl ctxt (mask_read_bpl (expr.Var (mask_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) 
                              ns 
                              (RealV (if r = Null then 0 else real_of_rat (Rep_prat (get_mh_total_full \<omega> (the_address r, f)))))"
proof -  

  from FieldRelSingle obtain f_tr \<tau> where
       FieldRel: "field_translation Tr f = Some f_tr" and
       "e_f_bpl = Lang.Var f_tr" and    
       FieldTy: "declared_fields Pr f = Some \<tau>" and
       FieldTyBpl: "vpr_to_bpl_ty TyRep \<tau> = Some \<tau>_bpl"
    by (auto elim: field_rel_single_elim)

  from FieldTy FieldRel have 
    LookupField:"lookup_var (var_context ctxt) ns f_tr = Some (AbsV (AField (NormalField f_tr \<tau>)))"
    using state_rel_field_rel[OF StateRel]
    unfolding field_rel_def
    by fastforce

  from state_rel_mask_var_rel[OF StateRel] obtain mb
    where LookupMaskVar: "lookup_var (var_context ctxt) ns (mask_var Tr) = Some (AbsV (AMask mb))" and
          MaskRel: "mask_rel Pr (field_translation Tr) (get_mh_total_full \<omega>) mb"
    unfolding mask_var_rel_def
    by auto

  show ?thesis
  proof (cases "r = Null")
    case True
    hence MaskZeroPerm: "mb (r, (NormalField f_tr \<tau>)) = 0" 
      using MaskRel
      unfolding mask_rel_def
      by blast

    have "red_expr_bpl ctxt
                        (mask_read_bpl (expr.Var (mask_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) 
                        ns (RealV 0)"
      apply (rule mask_read_wf_apply[OF MaskReadWf])
          apply (rule MaskZeroPerm)
         apply (fastforce intro: RedVar LookupMaskVar)
        apply (rule RedRcvBpl)
       apply (fastforce intro: RedVar LookupField simp: \<open>e_f_bpl = _\<close>)
      using FieldTyBpl
      by simp
    thus ?thesis
      using \<open>r = Null\<close>
      by simp
  next
    case False
    from this obtain a where "r = Address a"
      by (auto elim: ref.exhaust)

    let ?p = "real_of_rat (Rep_prat (get_mh_total_full \<omega> (a,f)))"
    have MaskZeroPerm: "mb (Address a, (NormalField f_tr \<tau>)) = ?p" 
      using MaskRel FieldTy FieldRel
      unfolding mask_rel_def
      by fastforce

    have "red_expr_bpl ctxt
                        (mask_read_bpl (expr.Var (mask_var Tr)) e_rcv_bpl e_f_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) 
                        ns (RealV ?p)"
      apply (rule mask_read_wf_apply[OF MaskReadWf])
          apply (rule MaskZeroPerm)
         apply (fastforce intro: RedVar LookupMaskVar)     
      using RedRcvBpl \<open>r = _\<close>
        apply blast
       apply (fastforce intro: RedVar LookupField simp: \<open>e_f_bpl = _\<close>)
      using FieldTyBpl
      by simp
      
    then show ?thesis
      using \<open>r = _\<close>
      by simp
  qed
qed

text \<open>This is the same lemma as above but expressed in a way such that the conclusion can be matched 
      directly in more cases and where the receiver requirement is phrased in terms of the expression relation
      judgment.\<close>

lemma exp_rel_perm_access_2:
  assumes 
       MaskReadWf: "mask_read_wf TyRep ctxt mask_read_bpl" and
       StateRel: "state_rel Pr StateCons TyRep Tr AuxPred ctxt \<omega>def \<omega> ns" and
       RedRcvVpr: "ctxt_vpr, StateCons, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
       FieldRelSingle: "field_rel_single Pr TyRep Tr f e_f_bpl \<tau>_bpl" and
             "mvar = mask_var Tr" and
             "f_ty_bpl = TConSingle (TNormalFieldId TyRep)" and
       RcvRel: "exp_rel_vpr_bpl (state_rel Pr StateCons TyRep Tr AuxPred ctxt) ctxt_vpr ctxt e e_rcv_bpl" and
             "e_bpl = mask_read_bpl (expr.Var mvar) e_rcv_bpl e_f_bpl [f_ty_bpl, \<tau>_bpl]"
     shows "red_expr_bpl ctxt e_bpl 
                              ns 
                              (RealV (if r = Null then 0 else real_of_rat (Rep_prat (get_mh_total_full \<omega> (the_address r, f)))))"
  apply (subst \<open>e_bpl = _\<close>)
  apply (subst \<open>f_ty_bpl = _\<close>)
  apply (subst \<open>mvar = _\<close>)
  apply (rule exp_rel_perm_access[OF MaskReadWf StateRel FieldRelSingle])
  using RcvRel RedRcvVpr StateRel
  by (fastforce elim: exp_rel_vpr_bpl_elim)

end