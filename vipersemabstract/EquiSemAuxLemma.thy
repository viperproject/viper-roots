theory EquiSemAuxLemma
  imports EquiViper ViperCommon.PredicatesUtil
begin

text\<open>This file is lemmas used in proving properties of EquiSem\<close>


section \<open>Lemmas about Isabelle build-in functions\<close>

lemma list_all2_extract_premise:
  assumes sat_P: "list_all P xs"
      and P_implies_Q: "list_all2 (\<lambda>x y. P x \<longrightarrow> Q x y) xs ys"
    shows "list_all2 (\<lambda>x y. Q x y) xs ys"
proof -
  have eq_len: "length xs = length ys"
    using P_implies_Q list_all2_lengthD by auto
  have P_x: "\<forall>x \<in> set xs. P x"
    by (metis in_set_conv_decomp_last list.pred_inject(2) list_all_append sat_P)
  have P_x_implies_Q_x_y: "\<forall>(x, y) \<in> set (zip xs ys). P x \<longrightarrow> Q x y"
    by (metis P_implies_Q list_all2_iff)
  have "\<forall>(x, y) \<in> set (zip xs ys). x \<in> set xs"
    by (metis case_prodI2 set_zip_leftD)
  then have "\<forall>(x, y) \<in> set (zip xs ys). Q x y"
    using P_x P_x_implies_Q_x_y by fastforce
  then show ?thesis
    by (simp add: eq_len list_all2I)
qed

lemma in_set_zip_iff:
  "(x, y) \<in> set (zip xs ys) \<longleftrightarrow> (\<exists>i. i < length (zip xs ys) \<and> x = xs ! i \<and> y = ys ! i)"
  by (smt (verit) in_set_conv_nth length_zip min_less_iff_conj nth_zip old.prod.inject)

lemma list_all2_unique:
  assumes "list_all2 (\<lambda>x y. \<forall>y'. P x y' \<longrightarrow> y' = y) xs ys"
      and "list_all2 (\<lambda>x y'. P x y') xs ys'"
    shows "ys = ys'"
proof -
  have "length xs = length ys"
    using assms(1) list_all2_conv_all_nth by auto
  moreover have "length xs = length ys'"
    using assms(2) list_all2_conv_all_nth by auto
  ultimately have "length ys = length ys'"
    by simp
  have "list_all2 (=) ys ys'"
  proof -
    have "\<And>y y'. (y, y') \<in> set (zip ys ys') \<Longrightarrow> y = y'"
    proof -
      fix y y'
      assume "(y, y') \<in> set (zip ys ys')"
      then obtain i where "i < length (zip ys ys')" "y = ys ! i" "y' = ys' ! i"
        by (metis in_set_zip_iff)
      then have "i < length (zip xs ys)"
        by (simp add: \<open>length xs = length ys\<close>)
      obtain x where "x = xs ! i"
        by simp
      then have "\<And>y0. P x y0 \<Longrightarrow> y0 = y"
        using \<open>i < length (zip xs ys)\<close> \<open>y = ys ! i\<close> assms(1) list_all2_nthD2 by fastforce
      have "i < length (zip xs ys')"
        using \<open>i < length (zip xs ys)\<close> \<open>length ys = length ys'\<close> by auto
      then have "P x y'"
        by (simp add: \<open>x = xs ! i\<close> \<open>y' = ys' ! i\<close> assms(2) list_all2_nthD)
      then show "y = y'"
        using \<open>\<And>y0. P x y0 \<Longrightarrow> y0 = y\<close> by auto
    qed
    then have "\<forall>(y, y') \<in> set (zip ys ys'). y = y'"
      by auto
    then show ?thesis
      by (simp add: list_all2I \<open>length ys = length ys'\<close>)
  qed
  then show ?thesis
    by (simp add: list_all2_eq)
qed


section \<open>Lemmas about Functions in this Project\<close>

lemma not_gr_0:
  "(x :: preal) = 0 \<longleftrightarrow> \<not>(x > 0)"
  apply transfer
  by auto

lemma gr_0_is_ppos:
  "(x :: preal) > 0 \<longleftrightarrow> ppos x"
  apply transfer
  by simp

lemma mult_abs_preal_homomorphic:
  assumes "x > 0"
      and "y > 0"
    shows "Abs_preal x * Abs_preal y = Abs_preal (x * y)"
\<comment> \<open>All properties related to Abs_preal are proven by referring to its Rep_preal form and use the fact that Rep_preal is injection and preserves all relations\<close>
proof -
  have "Rep_preal (Abs_preal x) = x" using Abs_preal_inverse
    by (simp add: assms(1) order.strict_implies_order)
  moreover have "Rep_preal (Abs_preal y) = y" using Abs_preal_inverse
    by (simp add: assms(2) order.strict_implies_order)
  ultimately have "Rep_preal (Abs_preal x * Abs_preal y) = x * y"
    \<comment> \<open>Rep_preal is injective, so it's naturally homomorphic under *, i.e. Rep_preal (x * y) = Rep_preal x * Rep_preal y holds without additional conditions. But Abs_preal is not injective, so we need conditions and proofs for its homomorphism\<close>
    by (simp add: times_preal.rep_eq)
  then show ?thesis
    by (metis Rep_preal_inverse)
qed

lemma positive_have_inv:
  assumes "(p :: preal) > 0"
  shows "\<exists>q. q * p = 1 \<and> q > 0"
  by (metis PosReal.field_inverse PosReal.pmult_comm Rep_preal_inverse assms mult_cancel_right1 not_gr_0 times_preal.rep_eq zero_neq_one zero_preal.rep_eq zero_preal_def)

lemma mult_positive_preal_positive:
  assumes "(x :: preal) > 0"
      and "y > 0"
    shows "x * y > 0"
  using assms apply transfer
  by simp

lemma real_greater_convex:
  assumes "((v :: real) \<le> va) = (v \<le> vb)"
      and "a \<ge> 0"
      and "b \<ge> 0"
      and "a + b = 1"
    shows "(v \<le> a * va + b * vb) = (v \<le> va)"
proof -
  have "v = a * v + b * v"
    by (metis assms(4) mult_1 ring_class.ring_distribs(2))
  then show ?thesis
  proof (cases "v \<le> va")
    case True
    then have "v \<le> vb"
      by (simp add: assms(1))
    have "a * v \<le> a * va"
      by (simp add: True assms(2) mult_left_mono)
    moreover have "b * v \<le> b * vb"
      by (simp add: \<open>v \<le> vb\<close> assms(3) mult_left_mono)
    ultimately have "v \<le> a * va + b * vb"
      using \<open>v = a * v + b * v\<close> by fastforce
    then show ?thesis
      by (simp add: True)
  next
    case False
    then have "v > vb"
      by (simp add: assms(1))
    then show ?thesis
    proof (cases "a = 0")
      case True
      then have "b > 0"
        using assms(4) by auto
      then have "b * v > b * vb"
        by (simp add: \<open>vb < v\<close>)
      moreover have "a * v \<ge> a * va"
        by (simp add: True)
      ultimately show ?thesis
        using False \<open>v = a * v + b * v\<close> by linarith
    next
      case False
      then have "a * v > a * va"
        using \<open>vb < v\<close> assms(1) assms(2) by auto
      moreover have "b * v \<ge> b * vb"
        by (simp add: \<open>vb < v\<close> assms(3) mult_left_mono order_less_imp_le)
      ultimately show ?thesis
        using \<open>v = a * v + b * v\<close> \<open>vb < v\<close> assms(1) by auto
    qed
  qed
qed

lemma preal_greater_convex:
  assumes "((v :: preal) \<le> va) = (v \<le> vb)"
      and "a + b = 1"
    shows "(v \<le> a * va + b * vb) = (v \<le> va)"
proof -
  let ?v = "Rep_preal v"
  let ?va = "Rep_preal va"
  let ?vb = "Rep_preal vb"
  let ?a = "Rep_preal a"
  let ?b = "Rep_preal b"
  have "(?v \<le> ?va) = (v \<le> va)"
    using assms(1) less_eq_preal.rep_eq by auto
  moreover have "(?v \<le> ?vb) = (v \<le> vb)"
    using assms(2) less_eq_preal.rep_eq by auto
  moreover have "?a \<ge> 0"
    using Rep_preal by auto
  moreover have "?b \<ge> 0"
    using Rep_preal by auto
  moreover have "?a + ?b = 1"
    by (metis assms(2) one_preal.rep_eq plus_preal.rep_eq)
  ultimately have "(?v \<le> ?a * ?va + ?b * ?vb) = (?v \<le> ?va)"
    by (simp add: assms(1) real_greater_convex)
  moreover have "(v \<le> a * va + b * vb) = (?v \<le> ?a * ?va + ?b * ?vb)"
    by (simp add: less_eq_preal.rep_eq plus_preal.rep_eq times_preal.rep_eq)
  ultimately show ?thesis
    by (simp add: \<open>(?v \<le> ?va) = (v \<le> va)\<close>)
qed



(*
real_mult_permexpr does not seem to be defined...
*)


lemma real_mult_permexpr_case_split:
  assumes "p > 0"
  shows "real_mult_permexpr p e = Wildcard \<Longrightarrow> e = Wildcard"
    and "real_mult_permexpr p e = PureExp exp' \<Longrightarrow> \<exists>exp. e = PureExp exp"
  using assms
  by (auto elim: real_mult_permexpr.elims)


lemma shift_and_add_keep_vstate[simp]:
  shows "\<And>\<omega> v. get_state (shift_and_add_equi_state \<omega> v) = get_state \<omega>"
  using shift_and_add_equi_state_def
  by (metis get_state_set_store)

lemma read_field_mono:
  assumes "\<phi>2 \<succeq> \<phi>1"
      and "read_field \<phi>1 hl = Some v"
    shows "read_field \<phi>2 hl = Some v"
proof -
  let ?h1 = "snd (Rep_virtual_state \<phi>1)"
  let ?h2 = "snd (Rep_virtual_state \<phi>2)"
  have "Rep_virtual_state \<phi>2 \<succeq> Rep_virtual_state \<phi>1"
  proof -
    obtain \<phi>0 where "Some \<phi>2 = \<phi>1 \<oplus> \<phi>0"
      using assms(1) greater_def by auto
    then have "Some (Rep_virtual_state \<phi>2) = Rep_virtual_state \<phi>1 \<oplus> Rep_virtual_state \<phi>0"
      by (simp add: compatible_virtual_state_implies_pre_virtual_state)
    then show ?thesis
      using greater_def by auto
  qed
  then have "?h2 \<succeq> ?h1"
    by (simp add: greater_prod_eq)
  then have "?h2 hl \<succeq> ?h1 hl"
    by (simp add: greaterE)
  moreover have "read_field \<phi>1 hl = ?h1 hl"
    by (simp add: get_vh_def)
  moreover have "read_field \<phi>2 hl = ?h2 hl"
    by (simp add: get_vh_def)
  ultimately have "read_field \<phi>2 hl \<succeq> read_field \<phi>1 hl"
    by simp
  then obtain vo where "Some (read_field \<phi>2 hl) = vo \<oplus> Some v"
    using assms(2) greater_equiv by auto
  then show ?thesis
  proof (cases vo)
    case None
    then show ?thesis
      using \<open>Some (read_field \<phi>2 hl) = vo \<oplus> Some v\<close> by auto
  next
    case (Some v')
    then obtain v0 where "read_field \<phi>2 hl = Some v0" "Some v0 = v' \<oplus> v"
      by (metis (full_types) \<open>Some (read_field \<phi>2 hl) = vo \<oplus> Some v\<close> option.distinct(1) option.sel plus_option.simps(3) plus_val_def)
    moreover have "v0 = v"
      by (metis calculation(2) option.discI option.inject plus_val_def)
    ultimately show ?thesis
      by simp
  qed
qed

lemma vstate_wf_imp:
  "get_vm \<omega> hl > 0 \<Longrightarrow> get_vh \<omega> hl \<noteq> None"
proof -
  let ?w = "Rep_virtual_state \<omega>"
  let ?wm = "fst ?w"
  let ?wh = "snd ?w"
  have "get_vm \<omega> = ?wm"
    by (simp add: get_vm_def)
  moreover assume "get_vm \<omega> hl > 0"
  ultimately have "ppos (?wm hl)"
    by (simp add: gr_0_is_ppos)
  moreover have "wf_pre_virtual_state ?w"
    using Rep_virtual_state by auto
  moreover have "?w = (?wm, ?wh)"
    by simp
  ultimately have "?wh hl \<noteq> None"
    by (metis wf_pre_virtual_state_def)
  moreover have "get_vh \<omega> = ?wh"
    by (simp add: get_vh_def)
  ultimately show "get_vh \<omega> hl \<noteq> None"
    by simp
qed

lemma vstate_wf_ppos:
  assumes "ppos (get_vm st hl)"
  shows "get_vh st hl \<noteq> None"
  using assms
  by (simp add: domIff norm_preal vstate_wf_imp)

lemma vstate_wf_Some :
  assumes "ppos (get_vm st hl)"
  shows "\<exists> v. get_vh st hl = Some v"
  using assms vstate_wf_ppos by blast

section \<open>Equi Red Rules\<close>

lemma sat_wand_rule:
  assumes "\<And>a b. Some b = \<omega> \<oplus> a \<Longrightarrow> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<Longrightarrow> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>)"
  shows "\<Delta> \<Turnstile> \<langle>A --* B; \<omega>\<rangle>"
  by (simp add: assms)

lemma sat_forall_rule:
  assumes "\<And>v. v \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>"
  shows "\<Delta> \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle>"
  by (simp add: assms)

subsection \<open>red_pure cases and red_atomic_assert cases\<close>

inductive_cases RedLitInt2Val_case: "I \<turnstile> \<langle>ELit (LInt n); \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedDiv2Val_case: "I \<turnstile> \<langle>Binop e PermDiv e'; \<omega>\<rangle> [\<Down>] Val v"

inductive_cases RedMult2Val_case: "I \<turnstile> \<langle>Binop e Mult e'; \<omega>\<rangle> [\<Down>] Val (VPerm v)"

inductive_cases RedAccField_case: "red_atomic_assert I (Acc x f e) \<omega> res"
inductive_cases RedAccPred_case: "red_atomic_assert I (AccPredicate P exps e) \<omega> res"

inductive_cases RedPure_case: "red_atomic_assert \<Delta> (Pure e) \<omega> res"
inductive_cases RedPure2True_case: "red_atomic_assert I (Pure x) \<omega> (Some True)"

inductive_cases RedLit2Val_case: "I \<turnstile> \<langle>ELit l; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedVar2Val_case: "I \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedUnop2Val_case: "I \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedBinop2Val_case: "I \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedOld2Val_case: "I \<turnstile> \<langle>Old l e; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedLet2Val_case: "I \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedExist2Val_case: "I \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedForall2Val_case: "I \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedCond2Val_case: "I \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedResult2Val_case: "I \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedPerm2Val_case: "I \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedAccField2Val_case: "I \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>] Val v"
inductive_cases RedFunApp2Val_case: "I \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>] Val v"

inductive_cases RedAccFieldPerm_case: "red_atomic_assert I (Acc x f (PureExp e)) \<omega> res"
inductive_cases RedAccFieldWild_case: "red_atomic_assert I (Acc x f Wildcard) \<omega> res"
inductive_cases RedAccPredPerm_case: "red_atomic_assert I (AccPredicate P xs (PureExp e)) \<omega> res"
inductive_cases RedAccPredWild_case: "red_atomic_assert I (AccPredicate P xs Wildcard) \<omega> res"


subsection \<open>red_pure and field Acc reduction are unique\<close>

lemma red_pure_det_ind :
  (* TODO: weaken this *)
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = None"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v1 \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r2 \<Longrightarrow> Val v1 = r2"
    and "red_pure_exps \<Delta> \<omega> es vs1 \<Longrightarrow> red_pure_exps \<Delta> \<omega> es vs2 \<Longrightarrow> vs1 = vs2"
  using assms
proof (induction _ e \<omega> "Val v1" and _ \<omega> _ _ arbitrary: v1 r2 and vs2 rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps \<Delta> \<omega> exps vals)
  then have "list_all2 (\<lambda>e v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vs2"
    using red_pure_exps.cases by blast
  moreover have "list_all2 (\<lambda>e v. \<forall>r. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r) \<longrightarrow> r = Val v) exps vals"
    using RedPureExps.hyps RedPureExps.prems(2) list_all2_mono by fastforce
  ultimately show ?case
    by (smt (verit, del_insts) extended_val.inject list_all2_mono list_all2_unique)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    apply (simp add:red_pure_simps)
    using eval_binop_implies_eval_normal by fastforce
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    apply (simp add:red_pure_simps)
    using eval_binop_implies_eval_normal by fastforce
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    apply (simp (no_asm_use) add:red_pure_simps) by blast
next case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3) then show ?case
    apply (unfold red_pure_simps) by fast
next case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2) then show ?case
    apply (unfold red_pure_simps)
    by fast
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case apply (simp (no_asm_use) add:red_pure_simps) by fastforce
next
  case (RedLet \<Delta> e1 \<omega> v1 e2)
  then show ?case apply (simp (no_asm_use) add:red_pure_simps) by blast
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case apply (simp (no_asm_use) add:red_pure_simps) by blast
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case apply (simp (no_asm_use) add:red_pure_simps) by blast
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case apply (simp (no_asm_use) add:red_pure_simps) by fastforce
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  from RedFunApp.hyps(3) RedFunApp.prems(2) show ?case by (simp)
qed (simp (no_asm_use) add:red_pure_simps; simp; fastforce)+

lemma red_pure_det:
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r1"
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r2"
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = None"
  shows "r1 = r2"
  apply (cases r1; cases r2) using red_pure_det_ind assms by blast+

(* TODO: get rid of this in favor of red_pure_det? *)
lemma red_pure_val_unique:
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v1 \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v2 \<Longrightarrow> v1 = v2"
    and "red_pure_exps \<Delta> \<omega> es vs1 \<Longrightarrow> red_pure_exps \<Delta> \<omega> es vs2 \<Longrightarrow> vs1 = vs2"
proof (induction _ _ \<omega> "Val v1" and _ \<omega> _ _ arbitrary: v1 v2 and vs2 rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c \<omega> exps vals)
  then have "list_all2 (\<lambda>e v. c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vs2"
    using red_pure_exps.cases by blast
  moreover have "list_all2 (\<lambda>e v. \<forall>v'. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v') \<longrightarrow> v' = v) exps vals"
  proof -
    have "\<And>e v. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) \<and> (\<forall>x. v = x \<longrightarrow> (\<forall>xa. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val xa) \<longrightarrow> x = xa)) \<Longrightarrow> \<forall>v'. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v') \<longrightarrow> v' = v"
      by simp
    then show ?thesis
      by (smt (verit) RedPureExps.hyps list_all2_mono)
  qed
  ultimately show ?case
    by (simp add: list_all2_unique)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    using RedLit2Val_case by blast
next
  case (RedVar \<sigma> n \<Delta> uv)
  then show ?case
    by (metis RedVar2Val_case option.inject)
next
  case (RedUnop \<Delta> e \<omega> v unop)
  then show ?case
    by (metis RedUnop2Val_case binop_result.inject)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop e2)
  then show ?case
    by (metis RedBinop2Val_case eval_binop_implies_eval_normal option.inject)
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (metis RedBinop2Val_case binop_result.sel eval_binop_implies_eval_normal)
next
  case (RedOld t l \<phi> \<Delta> e \<sigma> uw)
  then show ?case
    by (smt (verit) Pair_inject RedOld2Val_case agreement.inject option.inject)
next
  case (RedLet \<Delta> e1 \<omega> v1 e2)
  then show ?case
    by (metis RedLet2Val_case)
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    by (metis RedExist2Val_case)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case
    by (metis RedExist2Val_case)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case
    by (metis RedForall2Val_case)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case
    by (metis RedForall2Val_case)
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 e3)
  then show ?case
    by (metis RedCond2Val_case val.inject(2))
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 e2)
  then show ?case
    by (metis RedCond2Val_case val.inject(2))
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    using RedPerm2Val_case by blast
next
  case (RedResult \<sigma> \<Delta> ux uy)
  then show ?case
    using RedResult2Val_case by fastforce
next
  case (RedField \<Delta> e \<omega> a f v)
  then obtain a' where "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef (Address a'))" "read_field (get_state \<omega>) (a', f) = Some v2" using RedAccField2Val_case
    by (metis read_field.elims)
  moreover have "a' = a"
    using RedField.hyps(2) calculation(1) by auto
  ultimately show ?case
    using RedField.hyps(3) by auto
next
  case (RedFunApp \<Delta> \<omega> exps vals f)
  then show ?case
    by (metis RedFunApp2Val_case option.inject)
qed

lemma red_accfield_unique:
  shows "red_atomic_assert \<Delta> (Acc x f e) \<omega> res1 \<Longrightarrow> red_atomic_assert \<Delta> (Acc x f e) \<omega> res2 \<Longrightarrow> res1 = res2"
proof (induction _ "Acc x f e" \<omega> _ rule: red_atomic_assert.induct)
  case (RedAtomicAcc \<Delta> \<omega> r p v)
  then show ?case using red_pure_val_unique(1)[of \<Delta> x \<omega> "VRef r"] red_pure_val_unique(1)[of \<Delta> p \<omega> "VPerm v"]
    sorry
next
  case (RedAtomicAccZero \<Delta> \<omega> uu p)
  then show ?case
    by (metis (no_types, lifting) RedAccFieldPerm_case less_numeral_extra(3) red_pure_val_unique(1) val.inject(3))
next
  case (RedAtomicAccWildcard \<Delta> \<omega> a)
  then show ?case sorry
(*
    by (metis RedAccFieldWild_case red_pure_val_unique(1) ref.distinct(1) ref.sel val.inject(4))
*)
next
  case (RedAtomicAccWildcardNull \<Delta> \<omega>)
  then show ?case
    by (metis RedAccFieldWild_case red_pure_val_unique(1) ref.distinct(1) val.inject(4))
next
  case (RedAtomicAccNeg \<Delta> p \<omega> v)
  then show ?case
    by (metis RedAccFieldPerm_case order.asym red_pure_val_unique(1) val.inject(3))
qed


section \<open>Separealion Algebra and Properties of EquiViper states\<close>


subsection \<open>Properties of Abstract Separealion Algebra\<close>

lemma compatible_imp_mult_compatible:
  assumes "a ## b"
  shows "(p \<odot> a) ## (p \<odot> b)"
  by (metis assms defined_def distrib_state_mult option.distinct(1) option.exhaust)

lemma compatible_iff:
  assumes "p > 0"
  shows "a ## b \<longleftrightarrow> (p \<odot> a) ## (p \<odot> b)" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume ?LHS
  then show ?RHS using compatible_imp_mult_compatible
    by blast
next
  assume ?RHS
  obtain q where "q * p = 1" using assms positive_have_inv
    by auto
  moreover have "q \<odot> (p \<odot> a) ## q \<odot> (p \<odot> b)" using \<open>?RHS\<close> compatible_imp_mult_compatible
    by blast
  ultimately show ?LHS
    by (simp add: mult_mult unit_mult)
qed

lemma compatible_mult:
  assumes "p > 0"
  shows "p \<odot> a ## b \<longleftrightarrow> a ## b"
  by (metis assms compatible_iff defined_comm larger_state_mult linorder_less_linear smaller_compatible smaller_state_mult unit_mult)

lemma compatible_mult_mult:
  assumes "p > 0"
      and "q > 0"
    shows "p \<odot> a ## q \<odot> b \<longleftrightarrow> a ## b"
  using assms compatible_iff compatible_mult by blast

lemma compatible_option:
  assumes "Some x ## Some y"
  shows "x ## y"
proof -
  obtain w where "Some w = Some x \<oplus> Some y" "w = x \<oplus> y"
    by (smt (verit) assms defined_def plus_option.simps(3))
  then have "w \<noteq> None"
    by (metis(full_types) option.distinct(1) plus_option.simps(3))
  then show ?thesis
    by (simp add: \<open>w = x \<oplus> y\<close> defined_def)
qed

(* TODO: Where to put this? *)
lemma shift_and_add_core :
  "shift_and_add_equi_state ( |\<omega>| ) v = |shift_and_add_equi_state \<omega> v|"
  by (simp add: AbstractSemantics.full_state_ext core_charact(1) core_charact(2) shift_and_add_equi_state_def)

subsection \<open>Properties about Addition on EquiViper states\<close>

lemma state_add_iff:
  shows "\<And>\<omega> a b :: 'v equi_state. Some \<omega> = a \<oplus> b \<longleftrightarrow> Some (get_store \<omega>) = get_store a \<oplus> get_store b \<and> Some (get_trace \<omega>) = get_trace a \<oplus> get_trace b \<and> Some (get_state \<omega>) = get_state a \<oplus> get_state b"
  sorry
(*
proof -
  fix \<omega> a b :: "'v equi_state"
  show "Some \<omega> = a \<oplus> b \<longleftrightarrow> Some (get_store \<omega>) = get_store a \<oplus> get_store b \<and> Some (get_trace \<omega>) = get_trace a \<oplus> get_trace b \<and> Some (get_state \<omega>) = get_state a \<oplus> get_state b"
  proof
    assume LHS: "Some \<omega> = a \<oplus> b"
    then have s_plus: "Some (get_store \<omega>) = get_store a \<oplus> get_store b" using plus_prodE sorry
      by (metis LHS getI plus_prodE)
    have snd_plus: "Some (snd \<omega>) = snd a \<oplus> snd b"
      by (metis LHS plus_prodE)
    have t_plus: "Some (get_trace \<omega>) = get_trace a \<oplus> get_trace b"
      by (metis getI plus_prodE snd_plus)
    have v_plus: "Some (get_state \<omega>) = get_state a \<oplus> get_state b"
      by (metis getI plus_prodE snd_plus)
    show "Some (get_store \<omega>) = get_store a \<oplus> get_store b \<and> Some (get_trace \<omega>) = get_trace a \<oplus> get_trace b \<and> Some (get_state \<omega>) = get_state a \<oplus> get_state b"
      using s_plus t_plus v_plus by simp
  next
    assume RHS: "Some (get_store \<omega>) = get_store a \<oplus> get_store b \<and> Some (get_trace \<omega>) = get_trace a \<oplus> get_trace b \<and> Some (get_state \<omega>) = get_state a \<oplus> get_state b"
    have fst_plus: "Some (fst \<omega>) = fst a \<oplus> fst b"
      using RHS getI by auto
    have snd_plus: "Some (snd \<omega>) = snd a \<oplus> snd b"
      by (metis RHS getI plus_prodI prod.exhaust_sel)
    have "\<omega> = (fst \<omega>, snd \<omega>)"
      by simp
    then show "Some \<omega> = a \<oplus> b"
      using fst_plus plus_prodI snd_plus by fastforce
  qed
qed
*)

lemma vstate_add_iff:
  "Some (c :: 'v virtual_state) = a \<oplus> b \<longleftrightarrow> Some (get_vh c) = get_vh a \<oplus> get_vh b \<and> Some (get_vm c) = get_vm a \<oplus> get_vm b" (is "?FULL \<longleftrightarrow> ?PART")
proof
  assume ?FULL
  then have "Some (Rep_virtual_state c) = Rep_virtual_state a \<oplus> Rep_virtual_state b"
    by (simp add: compatible_virtual_state_implies_pre_virtual_state)
  moreover have "\<And>\<omega> :: 'v virtual_state. get_vh \<omega> = snd (Rep_virtual_state \<omega>)"
    by (simp add: get_vh_def)
  moreover have "\<And>\<omega> :: 'v virtual_state. get_vm \<omega> = fst (Rep_virtual_state \<omega>)"
    by (simp add: get_vm_def)
  ultimately show ?PART
    by (metis plus_prodE)
next
  assume ?PART
  moreover have "\<And>\<omega> :: 'v virtual_state. get_vh \<omega> = snd (Rep_virtual_state \<omega>)"
    by (simp add: get_vh_def)
  moreover have "\<And>\<omega> :: 'v virtual_state. get_vm \<omega> = fst (Rep_virtual_state \<omega>)"
    by (simp add: get_vm_def)
  ultimately have "Some (Rep_virtual_state c) = Rep_virtual_state a \<oplus> Rep_virtual_state b"
    using plus_prodI by fastforce
  then show ?FULL
    by (simp add: compatible_virtual_state_implies_pre_virtual_state_rev)
qed

(*
lemma lambda_None_is_identity:
  shows "\<And>t :: 'v trace. Some t = t \<oplus> (Ag Map.Emp)"
proof -
  fix t :: "'v trace"
  have "\<And>l. Some (t l) = (t l) \<oplus> ((\<lambda>l. None) l)"
    by (simp add: commutative)
  then show "Some t = t \<oplus> (\<lambda>l. None)"
    by (simp add: plus_funI)
qed
*)

lemma zero_mask_identity:
  "Some x = x \<oplus> (zero_mask :: ('b, preal) abstract_mask)"
  by (simp add: SepAlgebra.plus_preal_def plus_funI zero_mask_def)

lemma empty_heap_identity:
  "Some h = h \<oplus> empty_heap"
  by (simp add: commutative empty_heap_def plus_funI)

lemma add_shift_and_add_interchange:
  assumes "Some (cs :: 'v store) = as \<oplus> bs"
  shows "Some (shift_and_add cs v) = shift_and_add as v \<oplus> shift_and_add bs v"
proof -
  have "\<And>l. Some (shift_and_add cs v l) = shift_and_add as v l \<oplus> shift_and_add bs v l"
  proof -
    fix l :: nat
    show "Some (shift_and_add cs v l) = shift_and_add as v l \<oplus> shift_and_add bs v l"
    proof (cases "l = 0")
      case True
      then have "shift_and_add as v l = Some v"
        by (simp add: shift_and_add_def)
      moreover have "shift_and_add bs v l = Some v"
        by (simp add: True shift_and_add_def)
      moreover have "shift_and_add cs v l = Some v"
        by (simp add: True shift_and_add_def)
      ultimately show ?thesis
        by (simp add: plus_val_def)
    next
      case False
      have "Some (cs (l - 1)) = as (l - 1) \<oplus> bs (l - 1)" using assms
        by (simp add: plus_funE)
      moreover have "shift_and_add as v l = as (l - 1)" using False shift_and_add_def
        by (metis fun_upd_apply)
      moreover have "shift_and_add bs v l = bs (l - 1)" using False shift_and_add_def
        by (metis fun_upd_apply)
      moreover have "shift_and_add cs v l = cs (l - 1)" using False shift_and_add_def
        by (metis fun_upd_apply)
      ultimately show ?thesis
        by simp
    qed
  qed
  then show ?thesis
    by (simp add: plus_funI)
qed

lemma add_shift_and_add_equi_state_interchange:
  assumes "Some c = a \<oplus> b"
  shows "Some (shift_and_add_equi_state c v) = (shift_and_add_equi_state a v) \<oplus> (shift_and_add_equi_state b v)"
proof -
  obtain cs cr as ar bs br where
        "c = (cs, cr)"
    and "a = (as, ar)"
    and "b = (bs, br)"
    using prod.exhaust_sel by blast
  moreover have "Some cr = ar \<oplus> br"
    by (metis (no_types, lifting) assms calculation(1) calculation(2) calculation(3) plus_prodE snd_conv)
(*
  moreover have "Some (shift_and_add cs v) = shift_and_add as v \<oplus> shift_and_add bs v"
    by (metis add_shift_and_add_interchange assms calculation(1) calculation(2) calculation(3) fst_eqD plus_prodE)
*)
  ultimately show ?thesis sorry
(*
    using plus_prodI snd_eqD by fastforce
*)
qed

lemma add_shift_and_add_list_interchange:
  assumes "Some (c :: 'v store) = a \<oplus> b"
  shows "Some (shift_and_add_list c v) = (shift_and_add_list a v) \<oplus> (shift_and_add_list b v)"
  using assms
proof (induction v arbitrary: a b c)
  case Nil
  then show ?case
    by simp
next
  case (Cons v vs)
  moreover have "Some (shift_and_add c v) = shift_and_add a v \<oplus> shift_and_add b v"
    by (simp add: Cons.prems add_shift_and_add_interchange)
  ultimately show ?case
    by simp
qed

lemma add_shift_and_add_list_state_interchange:
  assumes "Some c = a \<oplus> b"
  shows "Some (shift_and_add_list_state c v) = (shift_and_add_list_state a v) \<oplus> (shift_and_add_list_state b v)"
proof -
  obtain cs cr as ar bs br where
        "c = (cs, cr)"
    and "a = (as, ar)"
    and "b = (bs, br)"
    using prod.exhaust_sel by blast
  moreover have "Some cr = ar \<oplus> br"
    by (metis assms calculation plus_prodE snd_conv)
  moreover have "Some (shift_and_add_list cs v) = shift_and_add_list as v \<oplus> shift_and_add_list bs v"
    by (metis add_shift_and_add_list_interchange assms calculation(1) calculation(2) calculation(3) fst_eqD plus_prodE)
  ultimately show ?thesis
    using plus_prodI snd_eqD by fastforce
qed

lemma get_vm_additive:
  assumes "Some a = b \<oplus> c"
  shows "Some (get_vm a) = get_vm b \<oplus> get_vm c"
proof -
  let ?a = "Rep_virtual_state a"
  let ?b = "Rep_virtual_state b"
  let ?c = "Rep_virtual_state c"
  have "Some ?a = ?b \<oplus> ?c"
    by (simp add: assms compatible_virtual_state_implies_pre_virtual_state)
  moreover have "get_vm a = fst ?a"
    by (simp add: get_vm_def)
  moreover have "get_vm b = fst ?b"
    by (simp add: get_vm_def)
  moreover have "get_vm c = fst ?c"
    by (simp add: get_vm_def)
  ultimately show ?thesis
    by (metis (no_types, lifting) plus_prodE)
qed

lemma get_m_additive:
  assumes "Some a = b \<oplus> c"
  shows "get_m a hl = get_m b hl + get_m c hl"
  using EquiViper.add_masks_def assms get_vm_additive state_add_iff by blast

lemma val_option_sum:
  assumes "Some (x :: 'v val option) = a \<oplus> b"
      and "a \<noteq> None"
    shows "Some x = a \<oplus> None"
proof -
  obtain v where "a = Some v"
    using assms(2) by auto
  then have "x = Some v"
  proof (cases b)
    case None
    then show ?thesis
      using \<open>a = Some v\<close> assms(1) by auto
  next
    case (Some u)
    have "a ## b"
      using assms(1) defined_def by fastforce
    then have "v ## u"
      using Some \<open>a = Some v\<close> compatible_option by auto
    then show ?thesis
      by (smt (verit) Some \<open>a = Some v\<close> assms(1) defined_def option.sel plus_option.simps(3) plus_val_def)
  qed
  then show ?thesis
    by (simp add: \<open>a = Some v\<close>)
qed


subsection \<open>Properties about Multiplication on EquiViper states\<close>

subsubsection \<open>Distribute Multiplication on EquiViper states into Each Component\<close>

lemma mult_store_red:
  "p \<odot> (\<sigma> :: 'v store) = \<sigma>"
proof (rule ext)
  fix hl :: nat
  show "(p \<odot> \<sigma>) hl = \<sigma> hl"
  proof (cases "\<sigma> hl = None")
    case True
    then show ?thesis
      by (simp add: mult_fun_def)
  next
    case False
    then obtain v where "\<sigma> hl = Some v"
      by auto
    moreover have "p \<odot> v = v"
      by (simp add: mult_val_def)
    ultimately have "(p \<odot> \<sigma>) hl = Some v"
      by (simp add: mult_fun_def)
    then show ?thesis
      by (simp add: \<open>\<sigma> hl = Some v\<close>)
  qed
qed

lemma mult_state_red:
  "p \<odot> (\<sigma> :: 'v store, \<gamma>) = (\<sigma>, p \<odot> \<gamma>)"
proof -
  have "p \<odot> (\<sigma>, \<gamma>) = (p \<odot> \<sigma>, p \<odot> \<gamma>)"
    by (simp add: mult_prod_def)
  moreover have "p \<odot> \<sigma> = \<sigma>"
    by (simp add: mult_store_red)
  ultimately show ?thesis
    by simp
qed

definition shift_and_add_ag :: "'v ag_store \<Rightarrow> 'v \<Rightarrow> 'v ag_store" where
  "shift_and_add_ag \<sigma> x = Ag ((\<lambda>m. (the_ag \<sigma>) (m - 1))(0 \<mapsto> x))"

lemma mult_shift_and_add_equi_state_interchange:
  "p \<odot> (shift_and_add_equi_state \<omega> v) = shift_and_add_equi_state (p \<odot> \<omega>) v"
  sorry
(*
proof -
  obtain \<sigma> \<gamma> where "\<omega> = (\<sigma>, \<gamma>)"
    by (meson surj_pair)
  then have "shift_and_add_equi_state \<omega> v = (shift_and_add_ag \<sigma> v, \<gamma>)"
    by simp
  then have LHS_eq: "p \<odot> (shift_and_add_equi_state \<omega> v) = (shift_and_add \<sigma> v, p \<odot> \<gamma>)"
    by (simp add: mult_state_red)
  have "p \<odot> \<omega> = (\<sigma>, p \<odot> \<gamma>)"
    by (simp add: \<open>\<omega> = (\<sigma>, \<gamma>)\<close> mult_state_red)
  then have "shift_and_add_equi_state (p \<odot> \<omega>) v = (shift_and_add \<sigma> v, p \<odot> \<gamma>)"
    by simp
  then show ?thesis
    using LHS_eq by simp
qed
*)

lemma mult_partial_heap_red:
  "p \<odot> (h :: 'v partial_heap) = h"
proof (rule ext)
  fix hl :: heap_loc
  show "(p \<odot> h) hl = h hl"
  proof (cases "h hl = None")
    case True
    then show ?thesis
      by (simp add: mult_fun_def)
  next
    case False
    then obtain v where "h hl = Some v"
      by auto
    moreover have "p \<odot> v = v"
      by (simp add: mult_val_def)
    ultimately have "(p \<odot> h) hl = Some v"
      by (simp add: mult_fun_def)
    then show ?thesis
      by (simp add: \<open>h hl = Some v\<close>)
  qed
qed

lemma partial_heap_unchange_mult_virtual_state:
  "get_vh (p \<odot> \<omega>) = get_vh \<omega>"
proof -
  obtain h where "h = get_vh \<omega>"
    by simp
  then have "h = snd (Rep_virtual_state \<omega>)"
    by (simp add: get_vh_def)
  then obtain \<pi> where "(\<pi>, h) = Rep_virtual_state \<omega>"
    using prod.collapse by blast
  then have "Rep_virtual_state (p \<odot> \<omega>) = (p \<odot> \<pi>, p \<odot> h)"
    by (metis fst_conv mult_prod_def mult_virtual_state.rep_eq snd_conv)
  moreover have "p \<odot> h = h"
    by (simp add: mult_partial_heap_red)
  ultimately have "Rep_virtual_state (p \<odot> \<omega>) = (p \<odot> \<pi>, h)"
    by simp
  then have "get_vh (p \<odot> \<omega>) = h"
    by (simp add: get_vh_def)
  then show ?thesis
    by (simp add: \<open>h = get_vh \<omega>\<close>)
qed

lemma mult_get_v_interchange:
  "p \<odot> (get_state \<omega>) = get_state (p \<odot> \<omega>)"
  by (simp add: mult_prod_def get_state_def)

lemma mult_get_vm:
  "get_vm (p \<odot> \<phi>) = p \<odot> (get_vm \<phi>)"
proof -
  obtain \<pi> where "\<pi> = get_vm \<phi>"
    by simp
  moreover have "get_vm (p \<odot> \<phi>) = p \<odot> \<pi>"
    by (simp add: calculation get_vm_def mult_prod_def mult_virtual_state.rep_eq)
  ultimately show ?thesis
    by simp
qed

lemma mult_get_m:
  "get_m (p \<odot> \<omega>) hl = p * (get_m \<omega> hl)"
  by (metis mult_fun_def mult_get_v_interchange mult_get_vm mult_preal_def)

lemma get_m_combine:
  assumes "(v \<le> get_m \<alpha> hl) = (v \<le> get_m \<beta> hl)"
      and "a + b = 1"
      and "Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
    shows "(v \<le> get_m \<omega> hl) = (v \<le> get_m \<alpha> hl)"
proof -
  have "get_m \<omega> hl = a * (get_m \<alpha> hl) + b * (get_m \<beta> hl)"
    by (metis assms(3) get_m_additive mult_get_m)
  then show ?thesis
    using assms(1) assms(2) preal_greater_convex by presburger
qed

lemma extend_part_relation_to_tuple:
  assumes "a + b = 1"
      and "Some \<phi> = a \<odot> \<phi>a \<oplus> b \<odot> \<phi>b"
    shows "Some (s, t, \<phi>) = a \<odot> (s, t, \<phi>a) \<oplus> b \<odot> (s, t, \<phi>b)"
proof -
  have "Some s = a \<odot> s \<oplus> b \<odot> s"
    by (metis assms(1) distrib_scala_mult unit_mult)
  then have fst_rel: "Some (fst (s, t, \<phi>)) = a \<odot> (fst (s, t, \<phi>a)) \<oplus> b \<odot> (fst (s, t, \<phi>b))"
    by simp
  have " Some t = a \<odot> t \<oplus> b \<odot> t"
    by (metis assms(1) distrib_scala_mult unit_mult)
  then have "Some (fst (snd (s, t, \<phi>))) = a \<odot> (fst (snd (s, t, \<phi>a))) \<oplus> b \<odot> (fst (snd (s, t, \<phi>b)))"
    by simp
  moreover have "Some (snd (snd (s, t, \<phi>))) = a \<odot> (snd (snd (s, t, \<phi>a))) \<oplus> b \<odot> (snd (snd (s, t, \<phi>b)))"
    by (simp add: assms(2))
  moreover have "\<And>\<omega>. \<omega> = (fst \<omega>, fst (snd \<omega>), snd (snd \<omega>))"
    by simp
  ultimately show ?thesis using fst_rel
    by (simp add: mult_prod_def plus_prodI)
qed

lemma shift_and_add_list_state_rel_interchange:
  assumes "Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
  shows "Some (shift_and_add_list_state \<omega> v) = a \<odot> (shift_and_add_list_state \<alpha> v) \<oplus> b \<odot> (shift_and_add_list_state \<beta> v)"
proof -
  have "a \<odot> (shift_and_add_list_state \<alpha> v) = shift_and_add_list_state (a \<odot> \<alpha>) v"
    by (metis mult_state_red shift_and_add_list_state.simps surj_pair)
  moreover have "b \<odot> (shift_and_add_list_state \<beta> v) = shift_and_add_list_state (b \<odot> \<beta>) v"
    by (metis mult_state_red shift_and_add_list_state.simps surj_pair)
  ultimately show ?thesis using assms
    by (simp add: add_shift_and_add_list_state_interchange)
qed


subsection \<open>\<succeq> relation\<close>

lemma shift_and_add_equi_state_preserve_greater:
  assumes "\<omega>1 \<succeq> \<omega>0"
  shows "shift_and_add_equi_state \<omega>1 v \<succeq> shift_and_add_equi_state \<omega>0 v"
proof -
  obtain \<omega> where "Some \<omega>1 = \<omega> \<oplus> \<omega>0"
    using assms greater_equiv by blast
  then have "Some (shift_and_add_equi_state \<omega>1 v) = (shift_and_add_equi_state \<omega> v) \<oplus> (shift_and_add_equi_state \<omega>0 v)"
    by (simp add: add_shift_and_add_equi_state_interchange)
  then show ?thesis
    using greater_equiv by auto
qed

lemma greater_two_comp:
  assumes "p2 \<succeq> p1"
      and "q2 \<succeq> q1"
    shows "(p2, q2) \<succeq> (p1, q1)"
proof -
  obtain p where "Some p2 = p1 \<oplus> p"
    using assms(1) greater_def by auto
  moreover obtain q where "Some q2 = q1 \<oplus> q"
    using assms(2) greater_def by auto
  ultimately have "Some (p2, q2) = (p1, q1) \<oplus> (p, q)"
    by (simp add: plus_prodI)
  then show ?thesis
    using greater_def by auto
qed

subsubsection \<open>Each part's relation between \<omega>0 and \<omega>1 with \<omega>1 \<succeq> \<omega>0\<close>

lemma greater_state_has_greater_parts:
  assumes "\<omega>1 \<succeq> \<omega>0"
  shows "get_store \<omega>1 = get_store \<omega>0"
    and "get_trace \<omega>1 = get_trace \<omega>0"
    and "get_state \<omega>1 \<succeq> get_state \<omega>0"
    apply (metis assms greater_charact)
proof -
  have "get_abs_state \<omega>1 \<succeq> get_abs_state \<omega>0"
    using assms greater_charact by blast
  then have "Ag (get_trace \<omega>1) \<succeq> Ag (get_trace \<omega>0)"
    by (simp add: get_abs_state_def get_trace_def greater_prod_eq)
  then show "get_trace \<omega>1 = get_trace \<omega>0"
    by (simp add: greater_Ag)
  show "get_state \<omega>1 \<succeq> get_state \<omega>0"
    by (metis \<open>get_abs_state \<omega>1 \<succeq> get_abs_state \<omega>0\<close> get_abs_state_def get_state_def greater_prod_eq)
qed

lemma greater_cover_store:
  assumes "\<omega>1 \<succeq> \<omega>0"
      and "get_store \<omega>0 l = Some v"
    shows "get_store \<omega>1 l = Some v"
  by (metis assms(1) assms(2) greater_charact)

section \<open>red_pure for real_to_expr and binary operations on pure expressions\<close>

lemma red_real_to_expr:
  "I \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>] Val (VPerm p)"
  by (metis RedLit real_to_expr.simps val_of_lit.simps(3))
(*
proof -
  obtain r where "r = quotient_of p"
    by simp
  moreover obtain a b where "a = fst r" "b = snd r"
    by simp
  ultimately have "b \<noteq> 0"
    by (metis less_numeral_extra(3) quotient_of_denom_pos')
  have "real_to_expr p = (Binop (ELit (LInt a)) PermDiv (ELit (LInt b)))"
    by (metis \<open>a = fst r\<close> \<open>b = snd r\<close> \<open>r = quotient_of p\<close> real_to_expr.simps)
  moreover have "I \<turnstile> \<langle>ELit (LInt a); \<omega>\<rangle> [\<Down>] Val (VInt a)"
    by (metis RedLit val_of_lit.simps(2))
  moreover have "I \<turnstile> \<langle>ELit (LInt b); \<omega>\<rangle> [\<Down>] Val (VInt b)"
    by (metis RedLit val_of_lit.simps(2))
  moreover have "eval_binop (VInt a) PermDiv (VInt b) = BinopNormal (VPerm p)"
  proof -
    have "eval_int_int a PermDiv b = BinopNormal (VPerm p)"
      by (metis Rat_cases \<open>a = fst r\<close> \<open>b = snd r\<close> \<open>b \<noteq> 0\<close> \<open>r = quotient_of p\<close> eval_int_int.simps(7) prod.exhaust_sel quotient_of_eq)
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by (smt (verit, best) RedBinop)
qed
*)

lemma red_real_to_expr_unique:
  "I \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>] Val v \<Longrightarrow> v = VPerm p"
  by (metis RedLit2Val_case real_to_expr.simps val_of_lit.simps(3))
(*
proof -
  assume "I \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>] Val v"
  moreover obtain r a b where "r = quotient_of p" "a = fst r" "b = snd r"
    by simp
  ultimately have "I \<turnstile> \<langle>(Binop (ELit (LInt a)) PermDiv (ELit (LInt b))); \<omega>\<rangle> [\<Down>] Val v"
    by (metis real_to_expr.simps)
  then show "v = VPerm p"
  proof (rule RedDiv2Val_case)
    fix v1 v2
    assume "I \<turnstile> \<langle>ELit (LInt a); \<omega>\<rangle> [\<Down>] Val v1"
       and "I \<turnstile> \<langle>ELit (LInt b); \<omega>\<rangle> [\<Down>] Val v2"
       and "eval_binop v1 PermDiv v2 = BinopNormal v"
    then have "v1 = VInt a"
      by (metis RedLitInt2Val_case val_of_lit.simps(2))
    moreover have "v2 = VInt b"
      using RedLitInt2Val_case \<open>I \<turnstile> \<langle>ELit (LInt b); \<omega>\<rangle> [\<Down>] Val v2\<close> val_of_lit.simps(2) by blast
    moreover have "b \<noteq> 0"
      by (metis \<open>b = snd r\<close> \<open>r = quotient_of p\<close> less_int_code(1) quotient_of_denom_pos')
    moreover have "eval_int_int a PermDiv b = BinopNormal (VPerm p)"
      by (metis Rat_cases \<open>a = fst r\<close> \<open>b = snd r\<close> \<open>b \<noteq> 0\<close> \<open>r = quotient_of p\<close> eval_int_int.simps(7) prod.exhaust_sel quotient_of_eq)
    ultimately have "eval_binop v1 PermDiv v2 = BinopNormal (VPerm p)"
      by simp
    then show "v = VPerm p"
      by (simp add: \<open>eval_binop v1 PermDiv v2 = BinopNormal v\<close>)
  qed
qed
*)

lemma red_mult:
  assumes "p > 0"
  shows "((I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VPerm v)) \<or> (\<exists>v_int. v = real_of_int v_int \<and> I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VInt v_int)))  \<longleftrightarrow> (I \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>] Val (VPerm (p * v)))" (is "?LHS \<longleftrightarrow> ?RHS")
proof
  assume ?LHS
  moreover have "I \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>] Val (VPerm p)"
    using red_real_to_expr by blast
  moreover have "eval_binop (VPerm p) Mult (VPerm v) = BinopNormal (VPerm (p * v))"
    by simp
  ultimately show ?RHS
    by (auto simp add: RedBinop)
next
  assume ?RHS
  then show ?LHS
  proof (rule RedMult2Val_case)
    fix v1 v2
    assume "I \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>] Val v1"
       and "I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v2"
       and eval_res: "eval_binop v1 Mult v2 = BinopNormal (VPerm (p * v))"
    then have "v1 = VPerm p"
      using red_real_to_expr_unique by blast
    then obtain v' where "v2 = VPerm v'" sorry
(*
      using eval_res   by (auto elim: eval_binop.elims)
    then have "p * v' = p * v"
      using \<open>v1 = VPerm p\<close> eval_res by auto
    then have "v' = v"
      using assms by auto
    then show "I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
      using \<open>I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v2\<close> \<open>v2 = VPerm v'\<close> by auto
*)
    then consider (Perm) "(\<exists>v'. v2 = VPerm v')" | (Int) "(\<exists>v'. v2 = VInt v')"
      using eval_res by (auto elim: eval_binop.elims)
    thus ?thesis
    proof cases
      case Perm
      from this obtain v' where "v2 = VPerm v'"
        by auto
      then have "p * v' = p * v"
        using \<open>v1 = VPerm p\<close> eval_res by auto
      then have "v' = v"
        using assms by auto
      then show "?LHS"
        using \<open>I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v2\<close> \<open>v2 = VPerm v'\<close>
      by auto
    next
      case Int
      from this obtain v' where "v2 = VInt v'" 
        by auto
      then have "p * v' = p * v"
        using \<open>v1 = VPerm p\<close> eval_res by auto
      then have "v' = v"
        using assms by auto
      then show "?LHS"
        using \<open>I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v2\<close> \<open>v2 = VInt v'\<close>
        by auto
    qed
  qed
qed

subsection \<open>Multiply p and its Inverse on State and Expressions\<close>

\<comment>\<open>TODO: recheck whether this lemma holds and whether it is useful for clients 
         (earlier permission multiplication was feasible only with permission operands,
          but now integer operands are possible, which led to an experimental change for the lemma)\<close>
lemma mult_inv_on_state_and_expr:
  assumes "p > 0"
      and "q * p = 1"
    shows "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
      and "I \<turnstile> \<langle>Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult e); \<omega>\<rangle> [\<Down>] Val (VPerm v) \<Longrightarrow>
            (I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VPerm v)) \<or> (\<exists>v_int. v = real_of_int v_int \<and> I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VInt v_int))" (is "?MULT \<Longrightarrow> ?ORIGIN")
proof -
  have "q > 0"
    by (metis assms(1) assms(2) zero_less_mult_pos2 zero_less_one)
  then have "Abs_preal q * Abs_preal p = 1"
    by (simp add: assms(1) assms(2) mult_abs_preal_homomorphic one_preal_def)
  then show "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
    by (simp add: mult_mult unit_mult)

  assume ?MULT
  obtain v' where "v' = p * v"
    by simp
  then have "v = q * v'" typ real
    by (simp add: assms(2))
  then have "(I \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>] Val (VPerm v')) \<or>
             (\<exists>v_int. real_of_int v_int = v' \<and> I \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>] Val (VInt v_int))"
    using \<open>0 < q\<close> \<open>?MULT\<close> red_mult by blast
  then show ?ORIGIN
    using \<open>v' = p * v\<close> assms(1) red_mult
    sorry
qed


lemma mult_inv_on_state_implies_uniqueness:
  assumes "p > 0"
      and "\<exists>\<sigma>. P \<sigma> \<and> \<omega> = Abs_preal p \<odot> \<sigma>"
      and "\<omega> = Abs_preal p \<odot> \<omega>p"
    shows "P \<omega>p"
proof -
  obtain q where "q * p = 1"
    by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
  moreover obtain \<sigma> where "P \<sigma>" "\<omega> = Abs_preal p \<odot> \<sigma>"
    using assms(2) by auto
  ultimately have "\<sigma> = Abs_preal q \<odot> \<omega>"
    by (metis assms(1) mult_abs_preal_homomorphic mult_mult one_preal_def unit_mult zero_less_mult_pos2 zero_less_one)
  moreover have "\<omega>p = Abs_preal q \<odot> \<omega>"
    by (metis \<open>q * p = 1\<close> assms(1) assms(3) mult_abs_preal_homomorphic mult_less_0_iff mult_mult not_one_less_zero one_preal_def unit_mult zero_less_mult_iff zero_less_one)
  ultimately have "\<sigma> = \<omega>p"
    by simp
  then show "P \<omega>p"
    using \<open>P \<sigma>\<close> by auto
qed


section \<open>Separealion Algebra Instantiations\<close>

subsection \<open>Instantiation of val and virtual_state as pcm_with_core\<close>

instantiation val :: (type) pcm_with_core
begin

definition core_val :: "'a val \<Rightarrow> 'a val" where
  "core_val v = v"

instance proof
  fix x :: "'a val"
  show "Some x = x \<oplus> |x|"
    by (simp add: core_val_def plus_val_def)
  show "Some |x| = |x| \<oplus> |x|"
    by (simp add: plus_val_def)
next
  fix x c :: "'a val"
  assume "Some x = x \<oplus> c"
  then have "Some |x| = c \<oplus> x"
    by (simp add: commutative core_val_def)
  then show "\<exists>r. Some |x| = c \<oplus> r"
    by auto
next
  fix c a b :: "'a val"
  assume "Some c = a \<oplus> b"
  then show "Some |c| = |a| \<oplus> |b|"
    by (simp add: core_val_def)
next
  fix x y :: "'a val"
  assume "|x| = |y|"
  then show "x = y"
    by (simp add: core_val_def)
qed

end


instantiation virtual_state :: (type) pcm_with_core
begin

lift_definition core_virtual_state :: "'a virtual_state \<Rightarrow> 'a virtual_state"
  is core
proof -
  fix prod :: "'a pre_virtual_state"
  assume "\<exists>\<phi>. prod = \<phi> \<and> wf_pre_virtual_state \<phi>"
  then obtain \<phi> where
        "\<phi> = prod"
    and "wf_pre_virtual_state \<phi>"
    by simp
  obtain \<phi>p where "\<phi>p = |\<phi>|"
    by simp
  moreover obtain \<pi> h where "\<phi>p = (\<pi>, h)"
    by (simp add: calculation core_def)
  moreover have "wf_pre_virtual_state (\<pi>, h)"
  proof (rule wf_pre_virtual_stateI)
    fix hl
    have "\<pi> hl = 0"
      by (metis (mono_tags, opaque_lifting) \<open>\<phi>p = |\<phi>|\<close> calculation core_def core_fun core_preal_def fstI)
    then have "\<not>ppos (\<pi> hl)"
      using gr_0_is_ppos by auto
    then show "ppos (\<pi> hl) \<Longrightarrow> h hl \<noteq> None"
      by simp
  next
    show "wf_mask_simple \<pi>"
      by (metis all_pos calculation(1) calculation(2) core_def core_fun core_preal_def prod.sel(1) wf_mask_simpleI)
  qed
  ultimately show "\<exists>\<phi>. |prod| = \<phi> \<and> wf_pre_virtual_state \<phi>"
    by (simp add: \<open>\<phi> = prod\<close>)
qed

instance proof
  fix x :: "'a virtual_state"
  show "Some x = x \<oplus> |x|"
    by (simp add: compatible_virtual_state_implies_pre_virtual_state_rev core_is_smaller core_virtual_state.rep_eq)
  show "Some |x| = |x| \<oplus> |x|"
    by (simp add: compatible_virtual_state_implies_pre_virtual_state_rev core_is_pure core_virtual_state.rep_eq)
next
  fix x c :: "'a virtual_state"
  assume "Some x = x \<oplus> c"
  then show "\<exists>r. Some |x| = c \<oplus> r"
    by (smt (verit, best) asso1 compatible_virtual_state_implies_pre_virtual_state compatible_virtual_state_implies_pre_virtual_state_rev core_is_pure core_max core_virtual_state.rep_eq positivity)
next
  fix c a b :: "'a virtual_state"
  assume "Some c = a \<oplus> b"
  then show "Some |c| = |a| \<oplus> |b|"
    by (smt (verit, ccfv_SIG) compatible_virtual_state_implies_pre_virtual_state compatible_virtual_state_implies_pre_virtual_state_rev core_sum core_virtual_state.rep_eq)
next
  fix a b x y :: "'a virtual_state"
  assume "Some a = b \<oplus> x" "Some a = b \<oplus> y" "|x| = |y|"
  then show "x = y"
    by (metis Rep_virtual_state_inject cancellative compatible_virtual_state_implies_pre_virtual_state core_virtual_state.rep_eq)
qed

lemma core_structure:
  shows "get_vm |x| = zero_mask"
    and "get_vh |x| = get_vh x"
proof -
  obtain xm xh where "(xm, xh) = Rep_virtual_state x"
    by (metis surj_pair)
  moreover have "|(xm, xh)| = ( |xm|, |xh| )"
    by (simp add: core_def)
  ultimately have "Rep_virtual_state |x| = ( |xm|, |xh| )"
    by (simp add: core_virtual_state.rep_eq)
  then have "get_vm |x| = |xm|"
    by (simp add:get_vm_def)
  show "get_vm |x| = zero_mask"
  proof (rule ext)
    fix hl
    have "|xm| hl = 0"
      by (simp add: core_fun core_preal_def)
    then show "get_vm ( |x| ) hl = zero_mask hl"
      by (metis \<open>get_vm |x| = |xm|\<close> zero_mask_def)
  qed
  have "get_vh |x| = |xh|"
    by (metis \<open>Rep_virtual_state |x| = ( |xm|, |xh| )\<close> eq_snd_iff get_vh_def)
  moreover have "|xh| = xh"
  proof (rule ext)
    fix hl
    have "|xh| hl = |xh hl|"
      by (simp add: core_fun)
    moreover have "|xh hl| = xh hl"
      by (metis core_is_smaller core_option.simps(1) core_option.simps(2) not_None_eq plus_val_def)
    ultimately show "|xh| hl = xh hl"
      by simp
  qed
  moreover have "get_vh x = xh"
  proof -
    have "xh = snd (Rep_virtual_state x)"
      by (metis \<open>(xm, xh) = Rep_virtual_state x\<close> snd_conv)
    then show ?thesis
      by (simp add: get_vh_def)
  qed
  ultimately show "get_vh |x| = get_vh x"
    by simp
qed

lemma greater_comp:
  assumes "\<sigma>2 \<succeq> \<sigma>1"
      and "t2 \<succeq> t1"
      and "\<phi>2 \<succeq> \<phi>1"
    shows "(\<sigma>2, t2, \<phi>2) \<succeq> (\<sigma>1, t1, \<phi>1)"
  using greater_two_comp by (metis assms)

lemma wf_between_core_and_self:
  assumes "wf_pre_virtual_state x"
      and "x \<succeq> y"
      and "y \<succeq> |x|"
    shows "wf_pre_virtual_state y"
proof -
  let ?xh = "snd x"
  let ?xm = "fst x"
  let ?yh = "snd y"
  let ?ym = "fst y"
  let ?ch = "snd |x|"
  have "wf_pre_virtual_state (?ym, ?yh)"
  proof (rule wf_pre_virtual_stateI)
    fix hl
    assume "ppos (?ym hl)"
    have "?xm \<succeq> ?ym"
      using assms(2) greater_prod_eq by blast
    then have "?xm hl \<succeq> ?ym hl"
      by (simp add: greaterE)
    then obtain r where "Some (?xm hl) = ?ym hl \<oplus> r"
      using greater_def by auto
    then have "?xm hl = ?ym hl + r"
      by (simp add: plus_preal_def)
    then have "?xm hl \<ge> ?ym hl"
      by (metis (no_types, lifting) add.right_neutral linorder_le_cases not_gr_0 padd_mono verit_comp_simplify1(3))
    moreover have "?ym hl > 0" using \<open>ppos (?ym hl)\<close> apply transfer
      by simp
    ultimately have "?xm hl > 0"
      by simp
    then have "ppos (?xm hl)" apply transfer
      by simp
    moreover have "x = (?xm, ?xh)"
      by simp
    ultimately obtain v where "?xh hl = Some v"
      by (metis assms(1) not_None_eq wf_pre_virtual_state_def)
    then have "?ch hl = Some v"
      by (metis (mono_tags, lifting) core_def core_fun core_is_smaller core_option.simps(2) option.discI plus_val_def snd_eqD)
    moreover have "?yh hl \<succeq> ?ch hl"
      by (metis assms(3) greaterE greater_prod_eq)
    ultimately have "?yh hl = Some v"
      by (metis \<open>?xh hl = Some v\<close> assms(2) greaterE greater_prod_eq succ_antisym)
    then show "?yh hl \<noteq> None"
      by simp
  next
    show "wf_mask_simple (fst y)"
    proof (rule wf_mask_simpleI)
      fix hl
      have "pwrite \<ge> fst x hl"
        using assms(1) wf_mask_simple_def wf_pre_virtual_state_def by blast
      moreover obtain r where "Some (fst x hl) = fst y hl \<oplus> r"
        by (metis (no_types, lifting) assms(2) greater_def plus_funE plus_prodE)
      ultimately show "pwrite \<ge> fst y hl"
        by (metis SepAlgebra.plus_preal_def leD leI option.sel order_less_le_trans pos_perm_class.sum_larger)
    qed
  qed
  then show ?thesis
    by simp
qed

lemma wf_greater_preserve:
  assumes "wf_pre_virtual_state x"
      and "wf_pre_virtual_state y"
      and "x \<succeq> y"
    shows "Abs_virtual_state x \<succeq> Abs_virtual_state y"
proof -
  obtain z where "Some x = y \<oplus> z"
    using assms(3) greater_def by blast
  moreover obtain z' where "Some z' = z \<oplus> |x|"
    using calculation minus_equiv_def_any_elem by blast
  ultimately have "Some x = y \<oplus> z'"
    by (metis (no_types, lifting) asso1 core_is_smaller)
  moreover have "wf_pre_virtual_state z'"
    using \<open>Some z' = z \<oplus> |x|\<close> assms(1) calculation greater_equiv wf_between_core_and_self by blast
  moreover have "\<And>\<omega>. wf_pre_virtual_state \<omega> \<Longrightarrow> Rep_virtual_state (Abs_virtual_state \<omega>) = \<omega>"
      by (simp add: Abs_virtual_state_inverse)
  ultimately have "Some (Abs_virtual_state x) = Abs_virtual_state y \<oplus> Abs_virtual_state z'"
    by (smt (verit) assms(1) assms(2) compatible_virtual_state_implies_pre_virtual_state_rev)
  then show ?thesis
    using greater_def by auto
qed

lemma greater_heap_rule:
  assumes "\<And>hl v. (a :: 'v partial_heap) hl = Some v \<Longrightarrow> b hl = Some v"
  shows "b \<succeq> a"
  by (metis (full_types, opaque_lifting) assms commutative greaterI greater_def option.exhaust plus_option.simps(2) succ_refl)

end


subsection \<open>Instantiation of state as sep_algebra\<close>

instantiation virtual_state :: (type) sep_algebra
begin

definition u_virtual_state where "u_virtual_state = Abs_virtual_state uuu"

definition stable_virtual_state :: "'v virtual_state \<Rightarrow> bool" where
  "stable_virtual_state x \<longleftrightarrow> (\<forall>hl :: heap_loc. get_vh x hl \<noteq> None \<longrightarrow> ppos (get_vm x hl))"

definition stabilize2pre :: "'v virtual_state \<Rightarrow> 'v pre_virtual_state" where
  "stabilize2pre x = (get_vm x, get_vh x |` {hl. ppos (get_vm x hl)})"

definition stabilize_virtual_state :: "'v virtual_state \<Rightarrow> 'v virtual_state" where
  "stabilize_virtual_state x = Abs_virtual_state (stabilize2pre x)"

lemma stabilize_wf:
  "wf_pre_virtual_state (stabilize2pre x)"
proof -
  obtain \<pi> h where "stabilize2pre x = (\<pi>, h)" "\<pi> = get_vm x" "h = get_vh x |` {hl. ppos (get_vm x hl)}"
    by (simp add: stabilize2pre_def)
  moreover have "wf_pre_virtual_state (\<pi>, h)"
  proof (rule wf_pre_virtual_stateI)
    fix hl
    assume "ppos (\<pi> hl)"
    then have "get_vh x hl \<noteq> None"
    proof -
      obtain \<pi>x hx where "Rep_virtual_state x = (\<pi>x, hx)"
        by fastforce
      then have "\<pi>x = \<pi>"
        by (simp add: calculation(2) get_vm_def)
      then have "hx hl \<noteq> None"
        by (metis \<open>PosReal.ppos (\<pi> hl)\<close> \<open>Rep_virtual_state x = (\<pi>x, hx)\<close> calculation(2) get_vh_def gr_0_is_ppos prod.sel(2) vstate_wf_imp)
      moreover have "get_vh x = hx" using \<open>Rep_virtual_state x = (\<pi>x, hx)\<close>
        by (simp add:get_vh_def)
      ultimately show ?thesis
        by simp
    qed
    moreover have "ppos (get_vm x hl)"
      using \<open>PosReal.ppos (\<pi> hl)\<close> \<open>\<pi> = get_vm x\<close> by blast
    ultimately show "h hl \<noteq> None"
      by (simp add: \<open>h = get_vh x |` {hl. ppos (get_vm x hl)}\<close> restrict_map_def)
  next
    show "wf_mask_simple \<pi>"
      by (simp add:\<open>\<pi> = get_vm x\<close>)
  qed
  ultimately show ?thesis
    by simp
qed

lemma vstate_stabilize_structure:
  shows "get_vm (stabilize x) = get_vm x"
    and "get_vh (stabilize x) = get_vh x |` {hl. ppos (get_vm x hl)}"
proof -
  have "\<And>\<omega>. get_vm \<omega> = fst (Rep_virtual_state \<omega>)"
    by (simp add: get_vm_def)
  moreover have "Rep_virtual_state (Abs_virtual_state (stabilize2pre x)) = stabilize2pre x"
    by (simp add: Abs_virtual_state_inverse stabilize_wf)
  ultimately show "get_vm (stabilize x) = get_vm x"
    by (simp add: get_vm_def stabilize2pre_def stabilize_virtual_state_def)
  show "get_vh (stabilize x) = get_vh x |` {hl. ppos (get_vm x hl)}"
    using \<open>Rep_virtual_state (Abs_virtual_state (stabilize2pre x)) = stabilize2pre x\<close>
    by (simp add: get_vh_def stabilize2pre_def stabilize_virtual_state_def)
qed

lemma virtual_state_ext :
  assumes "get_vm x = get_vm y" "get_vh x = get_vh y"
  shows "x = y"
  by (metis assms(1) assms(2) core_is_smaller option.simps(1) vstate_add_iff)

instance proof
  fix x y a b :: "'v virtual_state"

  show "sep_algebra_class.stable (stabilize x)"
    by (simp add: EquiSemAuxLemma.vstate_stabilize_structure(1) EquiSemAuxLemma.vstate_stabilize_structure(2) pperm_pnone_pgt stable_virtual_state_def restrict_map_def)
  show "sep_algebra_class.stable x \<Longrightarrow> stabilize x = x"
    apply (rule virtual_state_ext)
     apply (simp_all add: EquiSemAuxLemma.vstate_stabilize_structure stable_virtual_state_def)
    apply (rule ext)
    by (metis core_option.cases eq_snd_iff mem_Collect_eq restrict_in restrict_out)

  show "Some x = stabilize x \<oplus> |x|"
    sorry
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    apply (clarsimp simp add: vstate_add_iff EquiSemAuxLemma.vstate_stabilize_structure restrict_map_def)
    apply (rule plus_funI)
    apply (simp; safe; simp?)
    sorry

  show "Some x = a \<oplus> stabilize |b| \<Longrightarrow> x = a"
    apply (clarsimp simp add: vstate_add_iff EquiSemAuxLemma.vstate_stabilize_structure
           EquiSemAuxLemma.core_structure ValueAndBasicState.zero_mask_def)
    sorry
qed

end

(*
lemma stable_rel_virtual_stateI:
  assumes "\<And>hl :: heap_loc. get_vh (x :: 'v virtual_state) hl \<noteq> None \<Longrightarrow> get_vm x hl > 0 \<or> get_vm a hl > 0"
  shows "stable_rel a x"
proof (clarsimp simp add: stable_rel_def stable_virtual_state_def)
*)



lemma stable_rel_virtual_stateE:
  assumes "stable_rel a x"
      and "get_vh x hl = Some v"
    shows "get_vm x hl > 0 \<or> get_vm a hl > 0"
  using assms apply (clarsimp simp add: stable_rel_def stable_virtual_state_def)
(* This does not hold! But it also should not hold. If there is a contradiction between a and x, all locations become stable. *)
  oops
  (* by (metis assms option.discI stable_rel_virtual_state_def) *)

subsection \<open>determinism and monotonicity properties of red_pure\<close>

lemma set_state_core :
  "set_state ( |\<omega>| ) st = set_state \<omega> st"
  apply(rule full_state_ext)
    apply (simp add: core_charact(1))
   apply simp
  by (metis get_trace_set_state greater_state_has_greater_parts(2) max_projection_prop_pure_core mpp_smaller)

lemma set_state_greater :
  assumes "\<omega>' \<succeq> \<omega>"
  shows "set_state \<omega> st = set_state \<omega>' st"
  apply (rule full_state_ext)
    apply (metis assms get_store_set_state greater_state_has_greater_parts(1))
  apply simp
  by (metis assms greater_state_has_greater_parts(1) greater_state_has_greater_parts(2) set_state_def)

lemma get_vh_Some_greater :
  assumes "get_vh (get_state \<omega>) hl = Some v"
  assumes "\<omega>' \<succeq> \<omega>"
  shows "get_vh (get_state \<omega>') hl = Some v"
  using assms
  by (metis greater_state_has_greater_parts(3) read_field.elims read_field_mono)

lemma red_pure_core_ind :
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = interp.funs \<Delta> f vals |st|"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; |\<omega>|\<rangle> [\<Down>] r"
    and "red_pure_exps \<Delta> (\<omega>) es vs \<Longrightarrow> red_pure_exps \<Delta> ( |\<omega>| ) es vs"
  using assms
proof (induction _ _ "\<omega>" "r" and _ "\<omega>" _ _ arbitrary: rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c exps vals)
  then show ?case by (simp add: list_all2_mono red_pure_red_pure_exps.RedPureExps)
next
  case (RedPropagateFailure e e' \<Delta>)
  then show ?case by (cases e'; auto simp add:red_pure_simps core_charact)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLit)
next
  case (RedVar \<omega> n v \<Delta>)
  then show ?case
    by (simp add: core_charact(1) red_pure_red_pure_exps.RedVar)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    using red_pure_red_pure_exps.RedUnop by blast
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    using red_pure_red_pure_exps.RedBinopLazy by blast
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    using red_pure_red_pure_exps.RedBinop by blast
next
  case (RedOld \<omega> l \<phi> \<Delta> e v)
  then show ?case
    by (metis get_trace_set_state red_pure_red_pure_exps.RedOld set_state_core)
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLet shift_and_add_core)
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedExistsTrue shift_and_add_core)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedExistsFalse shift_and_add_core)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedForallTrue shift_and_add_core)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedForallFalse shift_and_add_core)
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then show ?case
    by (metis (no_types, opaque_lifting) red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    using red_pure_simps(8) by blast
next
  case (RedResult \<omega> v \<Delta>)
  then show ?case
    by (simp add: core_charact(1) red_pure_simps(11))
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    using red_pure_simps(4) by blast
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopFailure)
next
  case (RedOldFailure \<omega> l \<Delta> e)
  then show ?case
    by (metis get_trace_set_state red_pure_red_pure_exps.RedOldFailure set_state_core)
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedExistsFailure shift_and_add_core)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedForallFailure shift_and_add_core)
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case sorry
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  then show ?case sorry
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case sorry
qed
(* TODO: Reprove, or rephrase *)
(*
qed (clarsimp simp add:red_pure_simps core_charact set_state_core core_structure shift_and_add_core; metis?; fastforce)+
*)

lemma red_pure_core :
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = interp.funs \<Delta> f vals |st|"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; |\<omega>|\<rangle> [\<Down>] r"
  using red_pure_core_ind assms by blast


subsubsection \<open>red_pure is monotonic wrt. greater\<close>

lemma red_pure_greater_ind :
  assumes "\<omega>' \<succeq> \<omega>"
  (* TODO: weaken this *)
  assumes "\<And> f vals st st'. interp.funs \<Delta> f vals st = interp.funs \<Delta> f vals st'"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] r"
    and "red_pure_exps \<Delta> \<omega> es vs \<Longrightarrow> red_pure_exps \<Delta> (\<omega>') es vs"
  using assms
proof (induction _ _ "\<omega>" "r" and _ "\<omega>" _ _ arbitrary: \<omega>' and \<omega>' rule: red_pure_red_pure_exps.inducts)
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis shift_and_add_equi_state_preserve_greater)
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  then show ?case by (clarsimp simp add:red_pure_simps greater_state_has_greater_parts set_state_greater; metis)
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case apply (simp add:red_pure_simps greater_state_has_greater_parts set_state_greater del:Product_Type.split_paired_All)
    by (metis)
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case
    apply (simp add:red_pure_simps greater_state_has_greater_parts del:Product_Type.split_paired_All)
    using get_vh_Some_greater by blast
next
  case (RedPureExps c exps vals)
  then show ?case by (simp add: list_all2_mono red_pure_red_pure_exps.RedPureExps del:Product_Type.split_paired_All)
next
  case (RedPropagateFailure e e' \<Delta>)
  then show ?case by (cases e'; simp add:red_pure_simps del:Product_Type.split_paired_All; metis)
qed (clarsimp simp add:red_pure_simps greater_state_has_greater_parts set_state_greater; metis?; fastforce)+

lemma red_pure_greater :
  assumes "\<omega>' \<succeq> \<omega>"
  assumes "\<And> f vals st st'. interp.funs \<Delta> f vals st = interp.funs \<Delta> f vals st'"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] r"
  using assms red_pure_greater_ind(1) by (metis)

lemma red_pure_det_defined :
  assumes "\<omega>1 ## \<omega>2"
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = None"
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>1\<rangle> [\<Down>] r1" "\<Delta> \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>] r2"
  shows "r1 = r2"
proof -
  obtain \<omega> where "\<omega> \<succeq> \<omega>1" "\<omega> \<succeq> \<omega>2"
    using assms(1) defined_def greater_def commutative by (metis (no_types, opaque_lifting) not_Some_eq)
  then show ?thesis
    by (metis assms(2) assms(3) assms(4) red_pure_det red_pure_greater)
qed

subsection \<open>add_perm and del_perm\<close>

lift_definition add_perm :: "'a virtual_state \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" is
  "\<lambda> st hl p v. ((get_vm st)(hl := pmin 1 (get_vm st hl + p)), (get_vh st)(hl \<mapsto> v))"
  apply (simp add:wf_pre_virtual_state_def wf_mask_simple_def get_vm_bound)
  using vstate_wf_Some by fastforce

lemma add_perm_get_vh [simp] :
  "get_vh (add_perm st hl p v) = (get_vh st)(hl \<mapsto> v)"
  by (simp add:get_vh_def add_perm.rep_eq)

lemma add_perm_get_vm [simp] :
  "get_vm (add_perm st hl p v) = (get_vm st)(hl := pmin 1 (get_vm st hl + p))"
  by (simp add:get_vm_def add_perm.rep_eq)

lift_definition del_perm :: "'a virtual_state \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a virtual_state" is
  "\<lambda> st hl p. ((get_vm st)(hl := get_vm st hl - p), get_vh st)"
  apply (simp add:wf_pre_virtual_state_def wf_mask_simple_def get_vm_bound vstate_wf_Some norm_preal preal_to_real)
  using preal_sub_ppos get_vm_bound
  by (smt (verit, best) PosReal.ppos.rep_eq Rep_preal less_eq_preal.rep_eq mem_Collect_eq one_preal.rep_eq vstate_wf_Some)

lemma del_perm_get_vh [simp] :
  "get_vh (del_perm st hl p) = get_vh st"
  by (simp add:del_perm.rep_eq get_vh_def)

lemma del_perm_get_vm [simp] :
  "get_vm (del_perm st hl p) = (get_vm st)(hl := get_vm st hl - p)"
  by (simp add:del_perm.rep_eq get_vm_def)

lemma del_perm_0 [simp] :
  "del_perm st hl (Abs_preal 0) = st"
  apply (rule virtual_state_ext; simp)
  apply (rule ext; simp add:preal_to_real)
  by (metis all_pos less_eq_preal.rep_eq zero_preal.rep_eq)



lemma get_state_stabilize [simp] :
  "get_state (stabilize \<omega>) = stabilize (get_state \<omega>)"
  by (simp add: get_state_def stabilize_prod_def)

lemma get_trace_stabilize [simp] :
  "get_trace (stabilize \<omega>) = get_trace \<omega>"
  by (simp add: get_trace_def stabilize_prod_def stabilize_agreement_def)

lemma get_store_stabilize [simp] :
  "get_store (stabilize \<omega>) = get_store \<omega>"
  by (simp add: get_store_def stabilize_prod_def stabilize_agreement_def)

lemma set_state_stabilize_r [simp] :
  "set_state \<omega> (stabilize st) = stabilize (set_state \<omega> st)"
  by (simp add: set_state_def stabilize_prod_def get_store_def get_trace_def stabilize_agreement_def)

lemma set_state_stabilize_l [simp] :
  "set_state (stabilize \<omega>) st = set_state \<omega> st"
  by (simp add: set_state_def stabilize_prod_def get_store_def get_trace_def stabilize_agreement_def)

lemma set_state_set_state [simp] :
  "set_state (set_state \<omega> st1) st2 = set_state \<omega> st2"
  by (simp add: full_state_ext)

lemma set_state_get_state [simp] :
  "set_state \<omega> (get_state \<omega>) = \<omega>"
  by (simp add: full_state_ext)

subsection \<open>equi_state_record\<close>

(* The automation likes to destruct tuples. equi_state_record is a crude hack to prevent the automation from doing this. *)
(* TODO: Define abs_state via typedef like integer to get rid of this hack? *)

record 'a equi_state_record =
  get_store_record :: "var \<rightharpoonup> 'a val"
  get_trace_record :: "label \<rightharpoonup> 'a virtual_state"
  get_state_record :: "'a virtual_state"

definition abs_state_from_record :: "'a equi_state_record \<Rightarrow> 'a equi_state" ("\<down>_" [80] 80) where
"\<down> \<omega> = (Ag (get_store_record \<omega>), (Ag (get_trace_record \<omega>), get_state_record \<omega>))"

definition abs_state_to_record :: "'a equi_state \<Rightarrow> 'a equi_state_record" ("\<up>_" [80] 80) where
"\<up> \<omega> = \<lparr>get_store_record = get_store \<omega>, get_trace_record = get_trace \<omega>, get_state_record = get_state \<omega> \<rparr>"

lemma abs_state_from_to_record [simp] :
  "\<up>\<down> \<omega> = \<omega>"
  by (simp add: abs_state_from_record_def abs_state_to_record_def get_state_def get_store_def get_trace_def)

lemma abs_state_to_from_record [simp] :
  "\<down>\<up> \<omega> = \<omega>"
  by (simp add: abs_state_from_record_def abs_state_to_record_def get_state_def get_store_def get_trace_def)

lemma ag_the_ag_same:
  "a = b \<longleftrightarrow> the_ag a = the_ag b"
  using agreement.expand by blast

lemma ag_comp:
  fixes x :: "'v agreement"
  shows "x ## y \<longleftrightarrow> x = y"
  by (simp add: defined_def plus_agreement_def)

lemma comp_prod:
  "a ## b \<longleftrightarrow> (fst a ## fst b \<and> snd a ## snd b)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain x where "Some x = a \<oplus> b"
    by (metis defined_def not_Some_eq)
  then have "Some (fst x) = fst a \<oplus> fst b \<and> Some (snd x) = snd a \<oplus> snd b"
    by (metis plus_prodE)
  then show ?B
    by (metis defined_def option.discI)
next
  assume ?B
  then obtain r1 r2 where "Some r1 = fst a \<oplus> fst b \<and> Some r2 = snd a \<oplus> snd b"
    by (metis defined_def option.exhaust_sel)
  then show ?A
    using defined_def plus_prodIAlt by fastforce
qed


end