theory SemSynMultEquiv
  imports FixedPointEquiSem ViperCommon.PredicatesUtil
begin

section \<open>Semantic Multiplication\<close>

definition fun_interp_indep_mask :: "'v fun_interp \<Rightarrow> bool" where
  "fun_interp_indep_mask F \<longleftrightarrow> (\<forall>\<omega> \<omega>' :: 'v virtual_state. \<forall>f :: function_ident. \<forall>args :: 'v val list. get_vh \<omega> = get_vh \<omega>' \<longrightarrow> F f args \<omega> = F f args \<omega>')"


subsection \<open>Semantic and Syntatic Multiplication Equivalence in Reducing Pure Expressions\<close>

lemma red_pure_equiv:
  assumes "fun_interp_indep_mask (interp.funs \<Delta>)"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; p \<odot> \<omega>\<rangle> [\<Down>] v"
    and "red_pure_exps \<Delta> \<omega> es vs \<Longrightarrow> red_pure_exps \<Delta> (p \<odot> \<omega>) es vs"
  sorry
(*
  using assms
proof (induct rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c \<omega> exps vals)
  then show ?case
    by (simp add: list_all2_mono red_pure_red_pure_exps.RedPureExps)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLit)
next
  case (RedVar \<sigma> n v \<Delta> uv)
  have "p \<odot> (\<sigma>, uv) = (\<sigma>, p \<odot> uv)"
    by (simp add: mult_state_red)
  then show ?case sorry
(*
    by (simp add: local.RedVar red_pure_red_pure_exps.RedVar)
*)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedUnop)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopLazy)
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinop)
next
  case (RedOld t l \<phi> \<Delta> e \<sigma> v uw)
  have "p \<odot> (\<sigma>, t, \<phi>) = (p \<odot> \<sigma>, p \<odot> t, p \<odot> \<phi>)"
    by (simp add: mult_prod_def)
  then have "\<Delta> \<turnstile> \<langle>e; (p \<odot> \<sigma>, p \<odot> t, p \<odot> \<phi>)\<rangle> [\<Down>] v"
    using RedOld.hyps(3) RedOld.prems by auto
  moreover have "(p \<odot> t) l = Some (p \<odot> \<phi>)"
    by (simp add: RedOld.hyps(1) mult_fun_def)
  ultimately have "\<Delta> \<turnstile> \<langle>Old l e; (p \<odot> \<sigma>, p \<odot> t, p \<odot> uw)\<rangle> [\<Down>] v"
    by (simp add: red_pure_red_pure_exps.RedOld)
  moreover have "p \<odot> (\<sigma>, t, uw) = (p \<odot> \<sigma>, p \<odot> t, p \<odot> uw)"
    by (simp add: mult_prod_def)
  ultimately show ?case
    by simp
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then have "\<Delta> \<turnstile> \<langle>e2; shift_and_add_equi_state (p \<odot> \<omega>) v1\<rangle> [\<Down>] r"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    using RedLet.hyps(2) RedLet.prems red_pure_red_pure_exps.RedLet by blast
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] Val (VBool True)"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  moreover have "\<And>v'. \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v'\<rangle> [\<Down>] Val (VBool b)"
    by (metis RedExistsTrue.hyps(4) RedExistsTrue.prems mult_shift_and_add_equi_state_interchange)
  ultimately show ?case
    using RedExistsTrue.hyps(1) red_pure_red_pure_exps.RedExistsTrue by blast
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then have "\<And>v. v \<in> set_from_type (interp.domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] Val (VBool False)"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedExistsFalse)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then have "\<And>v. v \<in> set_from_type (interp.domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] Val (VBool True)"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedForallTrue)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] Val (VBool False)"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    using RedForallFalse.hyps(1) red_pure_red_pure_exps.RedForallFalse by blast
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPermNull)
next
  case (RedResult \<sigma> v \<Delta> ux uy)
  then show ?case
    by (metis mult_prod_def mult_state_red red_pure_red_pure_exps.RedResult)
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopRightFailure)
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopFailure)
next
  case (RedOldFailure t l \<Delta> e uz va)
  then have "(p \<odot> t) l = None"
    by (simp add: mult_fun_def)
  moreover have "p \<odot> (uz, t, va) = (p \<odot> uz, p \<odot> t, p \<odot> va)"
    by (simp add: mult_prod_def)
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedOldFailure)
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then have "v \<in> set_from_type (interp.domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] VFailure"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedExistsFailure)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then have "v \<in> set_from_type (interp.domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state (p \<odot> \<omega>) v\<rangle> [\<Down>] VFailure"
    by (simp add: mult_shift_and_add_equi_state_interchange)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedForallFailure)
next
  case (RedPropagateFailure e e' \<Delta> \<omega>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPropagateFailure)
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case
    by (metis mult_get_v_interchange partial_heap_unchange_mult_virtual_state read_field.simps red_pure_red_pure_exps.RedField)
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  moreover have "get_vh (get_state \<omega>) = get_vh (get_state (p \<odot> \<omega>))"
    by (metis mult_get_v_interchange partial_heap_unchange_mult_virtual_state)
  ultimately have "interp.funs \<Delta> f vals (get_state (p \<odot> \<omega>)) = Some v"
    by (metis fun_interp_indep_mask_def)
  then show ?case
    using RedFunApp.hyps(2) RedFunApp.prems red_pure_red_pure_exps.RedFunApp by blast
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  moreover have "get_vh (get_state \<omega>) = get_vh (get_state (p \<odot> \<omega>))"
    by (metis mult_get_v_interchange partial_heap_unchange_mult_virtual_state)
  ultimately have "interp.funs \<Delta> f vals (get_state (p \<odot> \<omega>)) = None"
    by (metis fun_interp_indep_mask_def)
  then show ?case
    using RedFunAppFailure.hyps(2) RedFunAppFailure.prems red_pure_red_pure_exps.RedFunAppFailure by blast
qed
*)

lemma red_pure_equiv_rev:
  assumes "p > 0"
      and "fun_interp_indep_mask (interp.funs \<Delta>)"
    shows "\<Delta> \<turnstile> \<langle>e; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] v \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v"
proof -
  assume "\<Delta> \<turnstile> \<langle>e; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] v"
  obtain q where "q * p = 1"
    by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
  then have "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
    by (simp add: assms(1) mult_inv_on_state_and_expr(1))
  then show "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v"
    by (metis \<open>\<Delta> \<turnstile> \<langle>e; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] v\<close> assms(2) red_pure_equiv(1))
qed


subsection \<open>Semantic and Syntactic Multiplication Equivalence in Reducing Acc Field case\<close>

lemma red_acc_field_origin_imp_mult:
  assumes "p > 0"
      and "fun_interp_indep_mask (funs I)"
    shows "red_atomic_assert I (Acc x f e) \<omega> res \<Longrightarrow> red_atomic_assert I (Acc x f (real_mult_permexpr p e)) (Abs_preal p \<odot> \<omega>) res" (is "?LHS \<Longrightarrow> ?RHS")
  sorry
(*
proof (rule RedAccField_case)
  fix r pa v
  assume "e = PureExp pa"
     and "res = Some (is_address r \<and> Abs_preal v \<le> get_m \<omega> (the_address r, f))"
     and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)"
     and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
     and "0 < v"
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; \<omega>\<rangle> [\<Down>] Val (VPerm (p * v))"
    using assms(1) red_mult by blast
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VPerm (p * v))"
    by (simp add: assms(2) red_pure_equiv(1))
  moreover have "Abs_preal v \<le> get_m \<omega> (the_address r, f) \<longleftrightarrow> Abs_preal (p * v) \<le> get_m (Abs_preal p \<odot> \<omega>) (the_address r, f)"
  proof
    assume "Abs_preal v \<le> get_m \<omega> (the_address r, f)"
    then obtain v' where "v' = get_m \<omega> (the_address r, f)" "v' \<ge> Abs_preal v"
      by simp
    then have "get_m (Abs_preal p \<odot> \<omega>) (the_address r, f) = Abs_preal p * v'"
      using mult_get_m by blast
    moreover have "Abs_preal p * v' \<ge> Abs_preal (p * v)"
    proof -
      have Abs_preal_inverse_v: "Rep_preal (Abs_preal v) = v" using Abs_preal_inverse
        by (simp add: \<open>0 < v\<close> order.strict_implies_order)
      have Abs_preal_inverse_p: "Rep_preal (Abs_preal p) = p" using Abs_preal_inverse
        by (simp add: assms(1) order.strict_implies_order)
      have "p * v > 0"
        by (simp add: \<open>0 < v\<close> assms(1))
      then have Abs_preal_inverse_pv: "Rep_preal (Abs_preal (p * v)) = p * v" using Abs_preal_inverse
        by simp
      have "Rep_preal (Abs_preal p * v') = p * Rep_preal v'"
        by (simp add: Abs_preal_inverse_p times_preal.rep_eq)
      moreover have "Rep_preal v' \<ge> v"
        using Abs_preal_inverse_v \<open>Abs_preal v \<le> v'\<close> less_eq_preal.rep_eq by auto
      ultimately have "Rep_preal (Abs_preal p * v') \<ge> p * v"
        by (simp add: assms(1))
      then show ?thesis
        by (simp add: Abs_preal_inverse_pv less_eq_preal.rep_eq)
    qed
    ultimately show "Abs_preal (p * v) \<le> get_m (Abs_preal p \<odot> \<omega>) (the_address r, f)"
      by simp
  next
    assume "Abs_preal (p * v) \<le> get_m (Abs_preal p \<odot> \<omega>) (the_address r, f)"
    obtain v' where "v' = get_m \<omega> (the_address r, f)"
      by simp
    then have "get_m (Abs_preal p \<odot> \<omega>) (the_address r, f) = Abs_preal p * v'"
      using mult_get_m by blast
    then have "Abs_preal (p * v) \<le> Abs_preal p * v'"
      using \<open>Abs_preal (p * v) \<le> get_m (Abs_preal p \<odot> \<omega>) (the_address r, f)\<close> by auto
    have "p * v > 0"
      by (simp add: \<open>0 < v\<close> assms(1))
    then have "Rep_preal (Abs_preal (p * v)) = p * v" using Abs_preal_inverse
      by simp
    then have "p * v \<le> Rep_preal (Abs_preal p * v')"
      using \<open>Abs_preal (p * v) \<le> Abs_preal p * v'\<close> less_eq_preal.rep_eq by auto
    have "Rep_preal (Abs_preal p) = p" using Abs_preal_inverse
      by (simp add: assms(1) order.strict_implies_order)
    then have "Rep_preal (Abs_preal p * v') = p * Rep_preal v'"
      by (simp add: times_preal.rep_eq)
    then have "v \<le> Rep_preal v'"
      using \<open>p * v \<le> Rep_preal (Abs_preal p * v')\<close> assms(1) by auto
    moreover have "Rep_preal (Abs_preal v) = v" using Abs_preal_inverse
      by (simp add: \<open>0 < v\<close> order.strict_implies_order)
    ultimately have "Abs_preal v \<le> v'"
      using less_eq_preal.rep_eq by auto
    then show "Abs_preal v \<le> get_m \<omega> (the_address r, f)"
      by (simp add: \<open>v' = get_m \<omega> (the_address r, f)\<close>)
  qed
  then have "res = Some (is_address r \<and> Abs_preal (p * v) \<le> get_m (Abs_preal p \<odot> \<omega>) (the_address r, f))"
    by (simp add: \<open>res = Some (is_address r \<and> Abs_preal v \<le> get_m \<omega> (the_address r, f))\<close>)
  moreover have "p * v > 0"
    by (simp add: \<open>0 < v\<close> assms(1))
  moreover have "I \<turnstile> \<langle>x; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VRef r)"
    by (simp add: \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)\<close> assms(2) red_pure_equiv(1))
  ultimately show ?RHS
    by (simp add: RedAtomicAcc \<open>e = PureExp pa\<close>)
next
  fix uu pa
  assume "e = PureExp pa"
     and "res = Some True"
     and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)"
     and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"
    by (metis assms(1) mult_zero_right red_mult)
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VPerm 0)"
    by (simp add: assms(2) red_pure_equiv(1))
  moreover have "I \<turnstile> \<langle>x; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VRef uu)"
    by (simp add: \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)\<close> assms(2) red_pure_equiv(1))
  ultimately show ?RHS
    by (simp add: RedAtomicAccZero \<open>e = PureExp pa\<close> \<open>res = Some True\<close>)
next
  fix pa v
  assume "e = PureExp pa"
     and "res = None"
     and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
     and "v < 0"
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; \<omega>\<rangle> [\<Down>] Val (VPerm (p * v))"
    using assms(1) red_mult by blast
  then have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VPerm (p * v))"
    by (simp add: assms(2) red_pure_equiv(1))
  moreover have "p * v < 0"
    by (simp add: \<open>v < 0\<close> assms(1) mult_pos_neg)
  ultimately show ?RHS
    by (simp add: RedAtomicAccNeg \<open>e = PureExp pa\<close> \<open>res = None\<close>)
next
  fix a
  assume "e = Wildcard"
     and "res = Some (pnone < get_m \<omega> (a, f))"
     and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))"
  then have "I \<turnstile> \<langle>x; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VRef (Address a))"
    by (simp add: assms(2) red_pure_equiv(1))
  let ?v = "get_m \<omega> (a, f)"
  let ?v' = "get_m (Abs_preal p \<odot> \<omega>) (a, f)"
  have "pnone < ?v \<longleftrightarrow> pnone < ?v'"
  proof
    assume "pnone < ?v"
    then have "0 < Rep_preal ?v"
      by (simp add: less_preal.rep_eq zero_preal.rep_eq)
    have "?v' = Abs_preal p * ?v"
      by (simp add: mult_get_m)
    moreover have "Rep_preal (Abs_preal p) = p" using Abs_preal_inverse
      by (simp add: assms(1) order.strict_implies_order)
    ultimately have "Rep_preal ?v' = p * Rep_preal ?v"
      by (simp add: times_preal.rep_eq)
    then have "0 < Rep_preal ?v'"
      by (simp add: \<open>0 < Rep_preal ?v\<close> assms(1))
    then show "pnone < ?v'"
      by (simp add: less_preal.rep_eq zero_preal.rep_eq)
  next
    assume "pnone < ?v'"
    then have "0 < Rep_preal ?v'"
      by (simp add: less_preal.rep_eq zero_preal.rep_eq)
    moreover have "?v' = Abs_preal p * ?v"
      by (simp add: mult_get_m)
    moreover have "Rep_preal (Abs_preal p) = p" using Abs_preal_inverse
      by (simp add: assms(1) order.strict_implies_order)
    ultimately have "0 < p * Rep_preal ?v"
      by (simp add: times_preal.rep_eq)
    then have "0 < Rep_preal ?v"
      using assms(1) zero_less_mult_pos by auto
    then show "pnone < ?v"
      by (simp add: less_preal.rep_eq zero_preal.rep_eq)
  qed
  then have "res = Some (pnone < get_m (Abs_preal p \<odot> \<omega>) (a, f))"
    by (simp add: \<open>res = Some (pnone < get_m \<omega> (a, f))\<close>)
  moreover have "real_mult_permexpr p e = Wildcard" using \<open>e = Wildcard\<close> assms(1)
    by simp
  ultimately show ?RHS
    by (simp add: RedAtomicAccWildcard \<open>I \<turnstile> \<langle>x; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VRef (Address a))\<close>)
next
  assume "e = Wildcard"
     and "res = Some False"
     and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef Null)"
  then have "I \<turnstile> \<langle>x; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VRef Null)"
    by (simp add: assms(2) red_pure_equiv(1))
  moreover have "real_mult_permexpr p e = Wildcard" using \<open>e = Wildcard\<close> assms(1)
    by simp
  ultimately show ?RHS
    by (simp add: RedAtomicAccWildcardNull \<open>res = Some False\<close>)
qed
*)

lemma red_acc_field_mult_imp_origin:
  assumes "p > 0"
      and "fun_interp_indep_mask (funs I)"
    shows "red_atomic_assert I (Acc x f (real_mult_permexpr p e)) (Abs_preal p \<odot> \<omega>) res \<Longrightarrow> red_atomic_assert I (Acc x f e) \<omega> res" (is "?RHS \<Longrightarrow> ?LHS")
  sorry
(*
proof -
  assume ?RHS
  obtain q where "q * p = 1"
    by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
  then have "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
    by (simp add: assms(1) mult_inv_on_state_and_expr(1))
  moreover have "q > 0"
    by (metis \<open>q * p = 1\<close> assms(1) zero_less_mult_pos2 zero_less_one)
  ultimately have "red_atomic_assert I (Acc x f (real_mult_permexpr q (real_mult_permexpr p e))) \<omega> res"
    by (metis \<open>?RHS\<close> assms(2) red_acc_field_origin_imp_mult)
  then show ?LHS
  proof (rule RedAccField_case)
    fix r pa v
    assume "real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa"
       and "res = Some (is_address r \<and> Abs_preal v \<le> get_m \<omega> (the_address r, f))"
       and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)"
       and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
       and "0 < v"
    then obtain exp where "e = PureExp exp"
      by (metis \<open>0 < q\<close> assms(1) less_numeral_extra(3) no_old_exp_or_wildcard.cases real_mult_permexpr.simps(1))
    then have "pa = Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult exp)"
      using \<open>real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa\<close> by auto
    then have "I \<turnstile> \<langle>exp; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
      using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(2)
      \<comment>\<open>does not hold anymore: exp may evaluate to Val (VInt v)\<close>
      sorry
    then show ?LHS
      by (simp add: RedAtomicAcc \<open>0 < v\<close> \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)\<close> \<open>e = PureExp exp\<close> \<open>res = Some (is_address r \<and> Abs_preal v \<le> get_m \<omega> (the_address r, f))\<close>)
  next
    fix uu pa
    assume "real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa"
       and "res = Some True"
       and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)"
       and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"
    then obtain exp where "e = PureExp exp"
      by (metis \<open>0 < q\<close> \<open>q * p = 1\<close> assms(1) mult.commute mult_zero_left no_old_exp_or_wildcard.cases real_mult_permexpr.simps(1) zero_neq_one)
    then have "pa = Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult exp)"
      using \<open>real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa\<close> by auto
    then have "I \<turnstile> \<langle>exp; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"
      using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm 0)\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(2)
      \<comment>\<open>does not hold anymore: exp may evaluate tu Val (VInt v)\<close>
      sorry
    then show ?LHS
      using RedAtomicAccZero \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)\<close> \<open>e = PureExp exp\<close> \<open>res = Some True\<close> by blast
  next
    fix pa v
    assume "real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa"
       and "res = None"
       and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
       and "v < 0"
    then obtain exp where "e = PureExp exp"
      by (metis \<open>0 < q\<close> assms(1) less_numeral_extra(3) no_old_exp_or_wildcard.cases real_mult_permexpr.simps(1))
    then have "pa = Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult exp)"
      using \<open>real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa\<close> by auto
    then have "I \<turnstile> \<langle>exp; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
      using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(2)
       \<comment>\<open>does not hold anymore: exp may evaluate tu Val (VInt v)\<close>
      sorry
    then show ?LHS
      by (simp add: RedAtomicAccNeg \<open>e = PureExp exp\<close> \<open>res = None\<close> \<open>v < 0\<close>)
  next
    fix a
    assume "real_mult_permexpr q (real_mult_permexpr p e) = Wildcard"
       and "res = Some (pnone < get_m \<omega> (a, f))"
       and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))"
    then have "e = Wildcard"
      by (metis exp_or_wildcard.simps(3) real_mult_permexpr.elims)
    then show ?LHS using \<open>res = Some (pnone < get_m \<omega> (a, f))\<close> \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))\<close> RedAtomicAccWildcard
      by fast
  next
    assume "real_mult_permexpr q (real_mult_permexpr p e) = Wildcard"
       and "res = Some False"
       and "I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef Null)"
    then have "e = Wildcard"
      by (metis exp_or_wildcard.distinct(1) real_mult_permexpr.elims)
    then show ?LHS using \<open>res = Some False\<close> \<open>I \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef Null)\<close> RedAtomicAccWildcardNull
      by fast
  qed
qed
*)

subsection \<open>Semantic and Syntactic Multiplication Equivalence in Reducing Acc Predicate case\<close>

lemma red_acc_predicate_origin_imp_mult:
  assumes "p > 0"
      and "fun_interp_indep_mask (funs I)"
    shows "red_atomic_assert I (AccPredicate P xs e) \<omega> res \<Longrightarrow> red_atomic_assert I (AccPredicate P xs (real_mult_permexpr p e)) (Abs_preal p \<odot> \<omega>) res" (is "?LHS \<Longrightarrow> ?RHS")
proof (rule RedAccPred_case)
  fix vals pa v A
  assume "e = PureExp pa"
     and "res = Some (0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a))"
     and "red_pure_exps I \<omega> xs vals"
     and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
     and "0 \<le> v"
     and "interp.predicates I (P, vals) = Some A"
  then have "red_pure_exps I (Abs_preal p \<odot> \<omega>) xs vals"
    by (simp add: assms(2) red_pure_equiv(2))
  let ?v' = "p * v"
  have "0 \<le> ?v'"
    using \<open>0 \<le> v\<close> assms(1) by auto
  moreover have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; Abs_preal p \<odot> \<omega>\<rangle> [\<Down>] Val (VPerm ?v')"
    using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> assms(1) assms(2) red_mult red_pure_equiv(1) by blast
  moreover have "res = Some (0 < ?v' \<longrightarrow> (\<exists>a' \<in> A. get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a'))"
  proof -
    have "(0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)) \<longleftrightarrow> (0 < ?v' \<longrightarrow> (\<exists>a' \<in> A. get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a'))"
    proof
      assume "0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)"
      then show "0 < ?v' \<longrightarrow> (\<exists>a' \<in> A. get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a')"
      proof (cases "0 < v")
        case True
        then obtain a where "a \<in> A" "get_state \<omega> = Abs_preal v \<odot> a"
          using \<open>0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)\<close> by auto
        then have "get_state (Abs_preal p \<odot> \<omega>) = Abs_preal p \<odot> (Abs_preal v \<odot> a)"
          by (metis mult_get_v_interchange)
        moreover have "Abs_preal p \<odot> (Abs_preal v \<odot> a) = Abs_preal ?v' \<odot> a"
          by (simp add: True assms(1) mult_abs_preal_homomorphic mult_mult)
        ultimately show ?thesis
          using \<open>a \<in> A\<close> by auto
      next
        case False
        then have "\<not>(0 < ?v')"
          using assms(1) zero_less_mult_pos by auto
        then show ?thesis
          by simp
      qed
    next
      assume "0 < ?v' \<longrightarrow> (\<exists>a' \<in> A. get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a')"
      then show "0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)"
      proof (cases "0 < v")
        case True
        then have "0 < ?v'"
          by (simp add: assms(1))
        then obtain a' where "a' \<in> A" "get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a'"
          using \<open>0 < ?v' \<longrightarrow> (\<exists>a' \<in> A. get_state (Abs_preal p \<odot> \<omega>) = Abs_preal ?v' \<odot> a')\<close> by auto
        then have "get_state \<omega> = Abs_preal v \<odot> a'"
        proof -
          obtain q where "q * p = 1" using assms(1)
            by (metis less_numeral_extra(3) nonzero_eq_divide_eq)
          then have "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
            by (simp add: assms(1) mult_inv_on_state_and_expr(1))
          moreover have "q > 0"
            by (metis \<open>q * p = 1\<close> assms(1) zero_less_mult_pos2 zero_less_one)
          moreover have "Abs_preal q * Abs_preal ?v' = Abs_preal v" using \<open>q > 0\<close>
            by (metis \<open>0 < p * v\<close> \<open>q * p = 1\<close> ab_semigroup_mult_class.mult_ac(1) mult_1 mult_abs_preal_homomorphic)
          ultimately show ?thesis
            by (metis \<open>get_state (Abs_preal p \<odot> \<omega>) = Abs_preal (p * v) \<odot> a'\<close> mult_get_v_interchange mult_mult)
        qed
        then show ?thesis
          using \<open>a' \<in> A\<close> by auto
      next
        case False
        then show ?thesis
          by simp
      qed
    qed
    then show ?thesis
      by (simp add: \<open>res = Some (0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a))\<close>)
  qed
  moreover have "real_mult_permexpr p e = PureExp (Binop (real_to_expr p) Mult pa)"
    by (simp add: \<open>e = PureExp pa\<close>)
  ultimately show ?RHS
    using RedAtomicPred \<open>interp.predicates I (P, vals) = Some A\<close> \<open>red_pure_exps I (Abs_preal p \<odot> \<omega>) xs vals\<close> by fastforce
next
  fix vals A
  assume "e = Wildcard"
     and "res = Some (\<exists>a \<in> A. \<exists>\<alpha>. pnone < \<alpha> \<and> get_state \<omega> = \<alpha> \<odot> a)"
     and "red_pure_exps I \<omega> xs vals"
     and " interp.predicates I (P, vals) = Some A"
  then have "red_pure_exps I (Abs_preal p \<odot> \<omega>) xs vals"
    by (simp add: assms(2) red_pure_equiv(2))
  have "real_mult_permexpr p e = Wildcard"
    using \<open>e = Wildcard\<close> assms(1) by auto
  moreover have "res = Some (\<exists>a \<in> A. \<exists>\<alpha>'. \<alpha>' > 0 \<and> get_state (Abs_preal p \<odot> \<omega>) = \<alpha>' \<odot> a)"
  proof -
    have "(\<exists>a \<in> A. \<exists>\<alpha>. \<alpha> > 0 \<and> get_state \<omega> = \<alpha> \<odot> a) \<longleftrightarrow> (\<exists>a \<in> A. \<exists>\<alpha>'. \<alpha>' > 0 \<and> get_state (Abs_preal p \<odot> \<omega>) = \<alpha>' \<odot> a)" (is "?ORIGIN \<longleftrightarrow> ?MULT")
    proof
      assume ?ORIGIN
      then obtain a \<alpha> where "a \<in> A" "get_state \<omega> = \<alpha> \<odot> a" "\<alpha> > 0"
        by auto
      let ?\<alpha>' = "Abs_preal p * \<alpha>"
      have "get_state (Abs_preal p \<odot> \<omega>) = ?\<alpha>' \<odot> a" using \<open>get_state \<omega> = \<alpha> \<odot> a\<close>
        by (metis mult_get_v_interchange mult_mult)
      moreover have "0 < ?\<alpha>'"
      proof -
        have "0 < Rep_preal \<alpha>"
          using \<open>\<alpha> > 0\<close> less_preal.rep_eq zero_preal.rep_eq by auto
        then have "0 < p * Rep_preal \<alpha>"
          by (simp add: assms(1))
        moreover have "Rep_preal (Abs_preal p) = p" using Abs_preal_inverse
          by (simp add: assms(1) order.strict_implies_order)
        ultimately have "0 < Rep_preal (Abs_preal p * \<alpha>)"
          by (simp add: times_preal.rep_eq)
        then show ?thesis
          by (simp add: less_preal.rep_eq zero_preal.rep_eq)
      qed
      ultimately show ?MULT
        using \<open>a \<in> A\<close> by blast
    next
      assume ?MULT
      then obtain a \<alpha>' where "a \<in> A" "get_state (Abs_preal p \<odot> \<omega>) = \<alpha>' \<odot> a" "\<alpha>' > 0"
        by auto
      obtain q where "p * q = 1"
        by (metis assms(1) less_numeral_extra(3) mult.commute nonzero_divide_eq_eq)
      then have "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
        by (simp add: assms(1) mult.commute mult_inv_on_state_and_expr(1))
      moreover obtain \<alpha> where "\<alpha> = Abs_preal q * \<alpha>'"
        by simp
      moreover have "Abs_preal q * Abs_preal p * \<alpha> = \<alpha>"
        by (metis \<open>p * q = 1\<close> assms(1) mult.right_neutral mult_abs_preal_homomorphic one_preal_def pmult_comm zero_less_mult_pos)
      ultimately have "get_state \<omega> = \<alpha> \<odot> a"
        by (metis \<open>get_state (Abs_preal p \<odot> \<omega>) = \<alpha>' \<odot> a\<close> mult_get_v_interchange mult_mult)
      moreover have "0 < \<alpha>"
      proof -
        have "0 < Rep_preal \<alpha>'" using \<open>\<alpha>' > 0\<close>
          by (simp add: less_preal.rep_eq zero_preal.rep_eq)
        moreover have "Abs_preal q > 0"
          by (metis \<open>p * q = 1\<close> assms(1) less_numeral_extra(1) less_preal.rep_eq mult.commute pgt.rep_eq positive_real_preal preal_pnone_pgt zero_less_mult_pos2)
        ultimately have "0 < Rep_preal \<alpha>" using \<open>\<alpha> = Abs_preal q * \<alpha>'\<close>
          using less_preal.rep_eq mult_positive_preal_positive zero_preal.rep_eq by auto
        then show ?thesis
          by (simp add: less_preal.rep_eq zero_preal.rep_eq)
      qed
      ultimately show ?ORIGIN
        using \<open>a \<in> A\<close> by auto
    qed
    then show ?thesis
      by (simp add: \<open>res = Some (\<exists>a \<in> A. \<exists>\<alpha>. 0 < \<alpha> \<and> get_state \<omega> = \<alpha> \<odot> a)\<close>)
  qed
  ultimately show ?RHS
    using RedAtomicPredWildcard \<open>interp.predicates I (P, vals) = Some A\<close> \<open>red_pure_exps I (Abs_preal p \<odot> \<omega>) xs vals\<close> by fastforce
next
  fix pa v
  assume "e = PureExp pa"
     and "res = None"
     and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
     and "v < 0"
  then have "real_mult_permexpr p e = PureExp (Binop (real_to_expr p) Mult pa)"
    by simp
  moreover have "I \<turnstile> \<langle>Binop (real_to_expr p) Mult pa; (Abs_preal p \<odot> \<omega>)\<rangle> [\<Down>] Val (VPerm (p * v))"
    by (meson \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> assms(1) assms(2) red_mult red_pure_equiv(1))
  moreover have "p * v < 0"
    by (simp add: \<open>v < 0\<close> assms(1) mult_pos_neg)
  ultimately show ?RHS
    by (simp add: RedAtomicPredNeg \<open>res = None\<close>)
qed

lemma red_acc_predicate_mult_imp_origin:
  assumes "p > 0"
      and "fun_interp_indep_mask (funs I)"
    shows "red_atomic_assert I (AccPredicate P xs (real_mult_permexpr p e)) (Abs_preal p \<odot> \<omega>) res \<Longrightarrow> red_atomic_assert I (AccPredicate P xs e) \<omega> res" (is "?RHS \<Longrightarrow> ?LHS")
proof -
  assume ?RHS
  obtain q where "q * p = 1"
    by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
  then have "Abs_preal q \<odot> (Abs_preal p \<odot> \<omega>) = \<omega>"
    by (simp add: assms(1) mult_inv_on_state_and_expr(1))
  moreover have "q > 0"
    by (metis \<open>q * p = 1\<close> assms(1) zero_less_mult_pos2 zero_less_one)
  ultimately have "red_atomic_assert I (AccPredicate P xs (real_mult_permexpr q (real_mult_permexpr p e))) \<omega> res"
    by (metis \<open>?RHS\<close> assms(2) red_acc_predicate_origin_imp_mult)
  then show ?LHS
  proof (rule RedAccPred_case)
    fix vals pa v A
    assume "real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa"
       and "res = Some (0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a))"
       and "red_pure_exps I \<omega> xs vals"
       and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
       and "0 \<le> v"
       and "interp.predicates I (P, vals) = Some A"
    then obtain exp where "e = PureExp exp"
      by (metis \<open>0 < q\<close> assms(1) less_numeral_extra(3) no_old_exp_or_wildcard.cases real_mult_permexpr.simps(1))
    then have "pa = Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult exp)"
      using \<open>real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa\<close> by auto
    then have "I \<turnstile> \<langle>exp; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
      using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(2)
       \<comment>\<open>does not hold anymore: exp may evaluate tu Val (VInt v)\<close>
      sorry
    then show ?LHS using \<open>e = PureExp exp\<close> \<open>res = Some (0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a))\<close> \<open>red_pure_exps I \<omega> xs vals\<close> \<open>0 \<le> v\<close> \<open>interp.predicates I (P, vals) = Some A\<close>
      by (simp add: RedAtomicPred)
  next
    fix vals A
    assume "real_mult_permexpr q (real_mult_permexpr p e) = Wildcard"
       and "res = Some (\<exists>a \<in> A. \<exists>\<alpha>. \<alpha> > 0 \<and> get_state \<omega> = \<alpha> \<odot> a)"
       and "red_pure_exps I \<omega> xs vals"
       and "interp.predicates I (P, vals) = Some A"
    then have "e = Wildcard"
      by (metis exp_or_wildcard.distinct(1) real_mult_permexpr.elims)
    then show ?LHS using \<open>res = Some (\<exists>a \<in> A. \<exists>\<alpha>. \<alpha> > 0 \<and> get_state \<omega> = \<alpha> \<odot> a)\<close> \<open>red_pure_exps I \<omega> xs vals\<close> \<open>interp.predicates I (P, vals) = Some A\<close> RedAtomicPredWildcard
      by fastforce
  next
    fix pa v
    assume "real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa"
       and "res = None"
       and "I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
       and "v < 0"
    then obtain exp where "e = PureExp exp"
      by (metis \<open>0 < q\<close> assms(1) less_numeral_extra(3) no_old_exp_or_wildcard.cases real_mult_permexpr.simps(1))
    then have "pa = Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult exp)"
      using \<open>real_mult_permexpr q (real_mult_permexpr p e) = PureExp pa\<close> by auto
    then have "I \<turnstile> \<langle>exp; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
      using \<open>I \<turnstile> \<langle>pa; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> \<open>q * p = 1\<close> assms(1)
       \<comment>\<open>does not hold anymore: exp may evaluate tu Val (VInt v)\<close>
      sorry
    then show ?LHS using \<open>e = PureExp exp\<close> \<open>res = None\<close> \<open>v < 0\<close>
      by (simp add: RedAtomicPredNeg)
  qed
qed


subsection \<open>Equivalence Definition and Proof\<close>

subsubsection \<open>Definition\<close>

definition sat_sem_mult :: "('v, 'v virtual_state) interp \<Rightarrow> assertion \<Rightarrow> preal \<Rightarrow> 'v equi_state \<Rightarrow> bool" ("_ \<Turnstile>[sem] ((\<langle>_^_;_\<rangle>))" [52,0,0,0] 84) where
  "I \<Turnstile>[sem] \<langle>A^p; \<omega>\<rangle> \<longleftrightarrow> (\<exists>\<sigma> :: 'v equi_state. I \<Turnstile> \<langle>A; \<sigma>\<rangle> \<and> \<omega> = p \<odot> \<sigma>)"

definition assertion_equivalence :: "'v pred_interp \<Rightarrow> preal \<Rightarrow> assertion \<Rightarrow> assertion \<Rightarrow> bool" where
  "assertion_equivalence \<Delta> p A B \<longleftrightarrow> (\<forall>D :: 'v domain_interp. \<forall>F :: 'v fun_interp. \<forall>\<omega> :: 'v equi_state. fun_interp_indep_mask F \<longrightarrow> (let I = \<lparr> interp.domains = D, predicates = \<Delta>, funs = F \<rparr> in I \<Turnstile>[sem] \<langle>A^p; \<omega>\<rangle> \<longleftrightarrow> I \<Turnstile> \<langle>B; \<omega>\<rangle>))"

syntax assertion_equivalence_abbr :: "(assertion \<Rightarrow> preal \<Rightarrow> 'v pred_interp \<Rightarrow> assertion \<Rightarrow> bool) \<Rightarrow> ('v pred_interp \<Rightarrow> preal \<Rightarrow> assertion \<Rightarrow> assertion \<Rightarrow> bool)" ("_^_ \<equiv>[_] _" [51, 50, 52] 51)
translations "A^p \<equiv>[\<Delta>] B" == "CONST assertion_equivalence \<Delta> p A B"

lemma assertion_equivalence_rule:
  assumes "\<And>D :: 'v domain_interp. \<And>F :: 'v fun_interp. \<And>\<omega> :: 'v equi_state.
            fun_interp_indep_mask F \<Longrightarrow>
            \<lparr> interp.domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile>[sem] \<langle>A^p; \<omega>\<rangle> \<Longrightarrow>
            \<lparr> interp.domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>B; \<omega>\<rangle>"
      and "\<And>D :: 'v domain_interp. \<And>F :: 'v fun_interp. \<And>\<omega> :: 'v equi_state.
            fun_interp_indep_mask F \<Longrightarrow>
            \<lparr> interp.domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>B; \<omega>\<rangle> \<Longrightarrow>
            \<lparr> interp.domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile>[sem] \<langle>A^p; \<omega>\<rangle>"
    shows "A^p \<equiv>[\<Delta>] B"
  by (meson assertion_equivalence_def assms)

subsubsection \<open>Proof\<close>

lemma sem_syn_mult_equiv_aux:
  assumes "p > 0"
      and "fun_interp_indep_mask (funs I)"
    shows "I \<Turnstile>[sem] \<langle>A^(Abs_preal p); \<omega>\<rangle> \<longleftrightarrow> I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
proof (induct A arbitrary: \<omega>)
  case (Atomic x)
  then show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>Atomic x; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then have "red_atomic_assert I x \<omega>p (Some True)"
      by simp
    then show ?SYN
    proof (cases x)
      case (Pure x1)
      then have "I \<turnstile> \<langle>x1; \<omega>p\<rangle> [\<Down>] Val (VBool True)"
        using RedPure2True_case \<open>red_atomic_assert I x \<omega>p (Some True)\<close> by blast
      then have "I \<turnstile> \<langle>x1; \<omega>\<rangle> [\<Down>] Val (VBool True)"
        by (simp add: \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> assms(2) red_pure_equiv(1))
      then show ?thesis
        by (simp add: Pure RedAtomicPure)
    next
      case (Acc x21 x22 x23)
      then show ?thesis
        by (metis \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> \<open>red_atomic_assert I x \<omega>p (Some True)\<close> assms(1) assms(2) red_acc_field_origin_imp_mult sat.simps(1) syntactic_mult.simps(2))
    next
      case (AccPredicate x31 x32 x33)
      then show ?thesis
        by (metis \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> \<open>red_atomic_assert I x \<omega>p (Some True)\<close> assms(1) assms(2) red_acc_predicate_origin_imp_mult sat.simps(1) syntactic_mult.simps(3))
    qed
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    moreover have "I \<Turnstile> \<langle>Atomic x; ?\<omega>p\<rangle>"
    proof (cases x)
      case (Pure x1)
      then have "I \<turnstile> \<langle>x1; \<omega>\<rangle> [\<Down>] Val (VBool True)"
        by (metis RedPure2True_case \<open>I \<Turnstile> \<langle>syntactic_mult p (Atomic x); \<omega>\<rangle>\<close> sat.simps(1) syntactic_mult.simps(1))
      then have "I \<turnstile> \<langle>x1; ?\<omega>p\<rangle> [\<Down>] Val (VBool True)"
        by (simp add: assms(2) red_pure_equiv(1))
      then show ?thesis using sat.simps(1)
        by (simp add: Pure RedAtomicPure)
    next
      case (Acc x21 x22 x23)
      then show ?thesis using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat.simps(1)
        by (metis \<open>I \<Turnstile> \<langle>syntactic_mult p (Atomic x); \<omega>\<rangle>\<close> assms(1) assms(2) red_acc_field_mult_imp_origin syntactic_mult.simps(2))
    next
      case (AccPredicate x31 x32 x33)
      then show ?thesis using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat.simps(1)
        by (metis \<open>I \<Turnstile> \<langle>syntactic_mult p (Atomic x); \<omega>\<rangle>\<close> assms(1) assms(2) red_acc_predicate_mult_imp_origin syntactic_mult.simps(3))
    qed
    ultimately show ?SEM
      using sat_sem_mult_def by blast
  qed
next
  case (Imp x1a A)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>Imp x1a A; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then obtain v where "I \<turnstile> \<langle>x1a; \<omega>p\<rangle> [\<Down>] Val v" "v = VBool True \<longrightarrow> I \<Turnstile> \<langle>A; \<omega>p\<rangle>"
      by auto
    then have "I \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v"
      by (simp add: \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> assms(2) red_pure_equiv(1))
    moreover have "v = VBool True \<longrightarrow> (I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>)"
    proof
      assume "v = VBool True"
      then have "I \<Turnstile> \<langle>A; \<omega>p\<rangle>"
        by (simp add: \<open>v = VBool True \<longrightarrow> I \<Turnstile> \<langle>A; \<omega>p\<rangle>\<close>)
      then have "I \<Turnstile>[sem] \<langle>A^Abs_preal p; \<omega>\<rangle>"
        using \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> sat_sem_mult_def by blast
      then show "I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
        by (simp add: Imp.hyps)
    qed
    ultimately show ?SYN
      by auto
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    obtain v where "I \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v" "v = VBool True \<longrightarrow> I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
      using \<open>I \<Turnstile> \<langle>syntactic_mult p (Imp x1a A); \<omega>\<rangle>\<close> by auto
    then have "I \<turnstile> \<langle>x1a; ?\<omega>p\<rangle> [\<Down>] Val v"
      by (simp add: assms(2) red_pure_equiv(1))
    moreover have "v = VBool True \<longrightarrow> (I \<Turnstile> \<langle>A; ?\<omega>p\<rangle>)"
    proof
      assume "v = VBool True"
      then have "I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
        by (simp add: \<open>v = VBool True \<longrightarrow> I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>\<close>)
      then show "I \<Turnstile> \<langle>A; ?\<omega>p\<rangle>"
        by (metis Imp \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
    qed
    ultimately show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat.simps(2) sat_sem_mult_def by blast
  qed
next
  case (CondAssert x1a A1 A2)
  then show ?case sorry
next
  case (ImpureAnd A1 A2)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>ImpureAnd A1 A2; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then have "I \<Turnstile> \<langle>A1; \<omega>p\<rangle>"
      by simp
    then have "I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle>"
      using ImpureAnd.hyps(1) \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> sat_sem_mult_def by blast
    have "I \<Turnstile> \<langle>A2; \<omega>p\<rangle>"
      using \<open>I \<Turnstile> \<langle>ImpureAnd A1 A2; \<omega>p\<rangle>\<close> by auto
    then have "I \<Turnstile> \<langle>syntactic_mult p A2; \<omega>\<rangle>"
      using ImpureAnd.hyps(2) \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> sat_sem_mult_def by blast
    then show ?SYN
      by (simp add: \<open>I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle>\<close>)
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    moreover have "I \<Turnstile> \<langle>A1; ?\<omega>p\<rangle>"
    proof -
      have "I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle>"
        using \<open>I \<Turnstile> \<langle>syntactic_mult p (ImpureAnd A1 A2); \<omega>\<rangle>\<close> by auto
      then show ?thesis
        by (metis ImpureAnd.hyps(1) \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
    qed
    moreover have "I \<Turnstile> \<langle>A2; ?\<omega>p\<rangle>"
    proof -
      have "I \<Turnstile> \<langle>syntactic_mult p A2; \<omega>\<rangle>"
        using \<open>I \<Turnstile> \<langle>syntactic_mult p (ImpureAnd A1 A2); \<omega>\<rangle>\<close> by auto
      then show ?thesis
        by (metis ImpureAnd.hyps(2) \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
    qed
    ultimately show ?SEM
      using sat.simps(8) sat_sem_mult_def by blast
  qed
next
  case (ImpureOr A1 A2)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>ImpureOr A1 A2; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then have "I \<Turnstile> \<langle>A1; \<omega>p\<rangle> \<or> I \<Turnstile> \<langle>A2; \<omega>p\<rangle>"
      by simp
    then show ?SYN
    proof
      assume "I \<Turnstile> \<langle>A1; \<omega>p\<rangle>"
      then have "I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle>"
        using ImpureOr.hyps(1) \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> sat_sem_mult_def by blast
      then show ?SYN
        by simp
    next
      assume "I \<Turnstile> \<langle>A2; \<omega>p\<rangle>"
      then have "I \<Turnstile> \<langle>syntactic_mult p A2; \<omega>\<rangle>"
        using ImpureOr.hyps(2) \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> sat_sem_mult_def by blast
      then show ?SYN
        by simp
    qed
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    have "I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle> \<or> I \<Turnstile> \<langle>syntactic_mult p A2; \<omega>\<rangle>"
      using \<open>I \<Turnstile> \<langle>syntactic_mult p (ImpureOr A1 A2); \<omega>\<rangle>\<close> by auto
    then have "I \<Turnstile> \<langle>ImpureOr A1 A2; ?\<omega>p\<rangle>"
    proof
      assume "I \<Turnstile> \<langle>syntactic_mult p A1; \<omega>\<rangle>"
      then have "I \<Turnstile> \<langle>A1; ?\<omega>p\<rangle>"
        by (metis ImpureOr.hyps(1) \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
      then show ?thesis
        by simp
    next
      assume "I \<Turnstile> \<langle>syntactic_mult p A2; \<omega>\<rangle>"
      then have "I \<Turnstile> \<langle>A2; ?\<omega>p\<rangle>"
        by (metis ImpureOr.hyps(2) \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
      then show ?thesis
        by simp
    qed
    then show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat_sem_mult_def by blast
  qed
next
  case (Star A1 A2)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>Star A1 A2; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then obtain ap bp where "Some \<omega>p = ap \<oplus> bp" "I \<Turnstile> \<langle>A1; ap\<rangle>" "I \<Turnstile> \<langle>A2; bp\<rangle>"
      using sat.simps(4) by blast
    let ?a = "Abs_preal p \<odot> ap"
    let ?b = "Abs_preal p \<odot> bp"
    have "Some \<omega> = ?a \<oplus> ?b"
      by (simp add: \<open>Some \<omega>p = ap \<oplus> bp\<close> \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> distrib_state_mult)
    moreover have "I \<Turnstile> \<langle>syntactic_mult p A1; ?a\<rangle>"
      using Star.hyps(1) \<open>I \<Turnstile> \<langle>A1; ap\<rangle>\<close> sat_sem_mult_def by blast
    moreover have "I \<Turnstile> \<langle>syntactic_mult p A2; ?b\<rangle>"
      using Star.hyps(2) \<open>I \<Turnstile> \<langle>A2; bp\<rangle>\<close> sat_sem_mult_def by blast
    ultimately show ?SYN
      by (metis sat.simps(4) syntactic_mult.simps(5))
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    obtain a b where "Some \<omega> = a \<oplus> b" "I \<Turnstile> \<langle>syntactic_mult p A1; a\<rangle>" "I \<Turnstile> \<langle>syntactic_mult p A2; b\<rangle>"
      using \<open>I \<Turnstile> \<langle>syntactic_mult p (A1 && A2); \<omega>\<rangle>\<close> by auto
    let ?ap = "Abs_preal q \<odot> a"
    let ?bp = "Abs_preal q \<odot> b"
    have "Some ?\<omega>p = ?ap \<oplus> ?bp"
      by (simp add: \<open>Some \<omega> = a \<oplus> b\<close> distrib_state_mult)
    moreover have "I \<Turnstile> \<langle>A1; ?ap\<rangle>"
      by (metis Star.hyps(1) \<open>I \<Turnstile> \<langle>syntactic_mult p A1; a\<rangle>\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
    moreover have "I \<Turnstile> \<langle>A2; ?bp\<rangle>"
      by (metis Star.hyps(2) \<open>I \<Turnstile> \<langle>syntactic_mult p A2; b\<rangle>\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1) sat_sem_mult_def)
    ultimately have "I \<Turnstile> \<langle>Star A1 A2; ?\<omega>p\<rangle>"
      using sat.simps(4) by blast
    then show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat_sem_mult_def by blast
  qed
next
  case (Wand A1 A2)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>Wand A1 A2; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    have "\<And>b a. Some b = \<omega> \<oplus> a \<Longrightarrow> (I \<Turnstile> \<langle>syntactic_mult p A1; a\<rangle>) \<Longrightarrow> (I \<Turnstile> \<langle>syntactic_mult p A2; b\<rangle>)"
    proof -
      fix b a
      assume "Some b = \<omega> \<oplus> a"
         and "I \<Turnstile> \<langle>syntactic_mult p A1; a\<rangle>"
      then obtain ap where "I \<Turnstile> \<langle>A1; ap\<rangle>" "a = Abs_preal p \<odot> ap"
        using Wand.hyps(1) sat_sem_mult_def by blast
      obtain q where "q * p = 1"
        by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
      then have "ap = Abs_preal q \<odot> a"
        by (simp add: \<open>a = Abs_preal p \<odot> ap\<close> assms(1) mult_inv_on_state_and_expr(1))
      moreover have "\<omega>p = Abs_preal q \<odot> \<omega>"
        by (simp add: \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> \<open>q * p = 1\<close> assms(1) mult_inv_on_state_and_expr(1))
      moreover obtain bp where "bp = Abs_preal q \<odot> b"
        by simp
      ultimately have "Some bp = \<omega>p \<oplus> ap"
        by (simp add: \<open>Some b = \<omega> \<oplus> a\<close> distrib_state_mult)
      then have "I \<Turnstile> \<langle>A2; bp\<rangle>"
        using \<open>I \<Turnstile> \<langle>A1 --* A2; \<omega>p\<rangle>\<close> \<open>I \<Turnstile> \<langle>A1; ap\<rangle>\<close> sat.simps(5) by blast
      then have "I \<Turnstile>[sem] \<langle>A2^Abs_preal p; b\<rangle>"
        by (metis \<open>bp = Abs_preal q \<odot> b\<close> \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) sat_sem_mult_def zero_less_mult_pos2)
      then show "I \<Turnstile> \<langle>syntactic_mult p A2; b\<rangle>"
        by (simp add: Wand.hyps(2))
    qed
    then show ?SYN
      by fastforce
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    have "\<And>bp ap. Some bp = ?\<omega>p \<oplus> ap \<Longrightarrow> (I \<Turnstile> \<langle>A1; ap\<rangle>) \<Longrightarrow> (I \<Turnstile> \<langle>A2; bp\<rangle>)"
    proof -
      fix bp ap
      assume "Some bp = ?\<omega>p \<oplus> ap"
         and "I \<Turnstile> \<langle>A1; ap\<rangle>"
      let ?b = "Abs_preal p \<odot> bp"
      let ?a = "Abs_preal p \<odot> ap"
      have "Some ?b = \<omega> \<oplus> ?a"
        using \<open>Some bp = ?\<omega>p \<oplus> ap\<close> \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> distrib_state_mult by fastforce
      moreover have "I \<Turnstile> \<langle>syntactic_mult p A1; ?a\<rangle>"
      proof -
        have "I \<Turnstile>[sem] \<langle>A1^Abs_preal p; ?a\<rangle>"
          using \<open>I \<Turnstile> \<langle>A1; ap\<rangle>\<close> sat_sem_mult_def by blast
        then show ?thesis
          by (simp add: Wand.hyps(1))
      qed
      ultimately have "I \<Turnstile> \<langle>syntactic_mult p A2; ?b\<rangle>"
        by (metis \<open>I \<Turnstile> \<langle>syntactic_mult p (A1 --* A2); \<omega>\<rangle>\<close> sat.simps(5) syntactic_mult.simps(10))
      then have "I \<Turnstile>[sem] \<langle>A2^Abs_preal p; ?b\<rangle>"
        by (simp add: Wand.hyps(2))
      then show "I \<Turnstile> \<langle>A2; bp\<rangle>" using mult_inv_on_state_implies_uniqueness
        by (metis assms(1) sat_sem_mult_def)
    qed
    then show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> sat_sem_mult_def sat_wand_rule by blast
  qed
next
  case (ForAll x1a A)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>ForAll x1a A; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then have "\<And>v. v \<in> set_from_type (domains I) x1a \<Longrightarrow> I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>"
    proof -
      fix v
      assume "v \<in> set_from_type (domains I) x1a"
      then have "I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>p v\<rangle>"
        using \<open>I \<Turnstile> \<langle>ForAll x1a A; \<omega>p\<rangle>\<close> by auto
      moreover have "shift_and_add_equi_state \<omega> v = Abs_preal p \<odot> (shift_and_add_equi_state \<omega>p v)"
        by (simp add: \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> mult_shift_and_add_equi_state_interchange)
      ultimately have "I \<Turnstile>[sem] \<langle>A^Abs_preal p; shift_and_add_equi_state \<omega> v\<rangle>"
        using sat_sem_mult_def by blast
      then show "I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>"
        by (simp add: ForAll)
    qed
    then show ?SYN
      by simp
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    have "\<And>v. v \<in> set_from_type (domains I) x1a \<Longrightarrow> I \<Turnstile> \<langle>A; shift_and_add_equi_state ?\<omega>p v\<rangle>"
    proof -
      fix v
      assume "v \<in> set_from_type (domains I) x1a"
      then have "I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>"
        using \<open>I \<Turnstile> \<langle>syntactic_mult p (ForAll x1a A); \<omega>\<rangle>\<close> by auto
      then have "I \<Turnstile>[sem] \<langle>A^Abs_preal p; shift_and_add_equi_state \<omega> v\<rangle>"
        by (simp add: ForAll)
      moreover have "shift_and_add_equi_state \<omega> v = Abs_preal p \<odot> (shift_and_add_equi_state ?\<omega>p v)"
        by (metis \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> mult_shift_and_add_equi_state_interchange)
      ultimately show " I \<Turnstile> \<langle>A; shift_and_add_equi_state ?\<omega>p v\<rangle>"
        using assms(1) sat_sem_mult_def mult_inv_on_state_implies_uniqueness by blast
    qed
    then show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> (Abs_preal q \<odot> \<omega>)\<close> sat.simps(6) sat_sem_mult_def by blast
  qed
next
  case (Exists x1a A)
  show ?case (is "?SEM \<longleftrightarrow> ?SYN")
  proof
    assume ?SEM
    then obtain \<omega>p where "I \<Turnstile> \<langle>Exists x1a A; \<omega>p\<rangle>" "\<omega> = Abs_preal p \<odot> \<omega>p"
      using sat_sem_mult_def by blast
    then obtain v where "v \<in> set_from_type (domains I) x1a" "I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>p v\<rangle>"
      using sat.simps(7) by blast
    moreover have "shift_and_add_equi_state \<omega> v = Abs_preal p \<odot> (shift_and_add_equi_state \<omega>p v)"
      by (simp add: \<open>\<omega> = Abs_preal p \<odot> \<omega>p\<close> mult_shift_and_add_equi_state_interchange)
    ultimately have "I \<Turnstile>[sem] \<langle>A^Abs_preal p; shift_and_add_equi_state \<omega> v\<rangle>"
      using sat_sem_mult_def by blast
    then have "I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>"
      by (simp add: Exists)
    then show ?SYN
      using \<open>v \<in> set_from_type (interp.domains I) x1a\<close> by auto
  next
    assume ?SYN
    obtain q where "q * p = 1"
      by (metis assms(1) less_numeral_extra(3) nonzero_divide_eq_eq)
    let ?\<omega>p = "Abs_preal q \<odot> \<omega>"
    have "\<omega> = Abs_preal p \<odot> ?\<omega>p"
      by (metis \<open>q * p = 1\<close> assms(1) less_numeral_extra(1) mult.commute mult_inv_on_state_and_expr(1) zero_less_mult_pos2)
    moreover obtain v where "v \<in> set_from_type (domains I) x1a" "I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>"
      using \<open>I \<Turnstile> \<langle>syntactic_mult p (Exists x1a A); \<omega>\<rangle>\<close> by auto
    ultimately have "I \<Turnstile> \<langle>A; shift_and_add_equi_state ?\<omega>p v\<rangle>"
    proof -
      have "I \<Turnstile>[sem] \<langle>A^Abs_preal p; shift_and_add_equi_state \<omega> v\<rangle>"
        by (simp add: Exists \<open>I \<Turnstile> \<langle>syntactic_mult p A; shift_and_add_equi_state \<omega> v\<rangle>\<close>)
      moreover have "shift_and_add_equi_state \<omega> v = Abs_preal p \<odot> (shift_and_add_equi_state ?\<omega>p v)"
        by (metis \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> mult_shift_and_add_equi_state_interchange)
      ultimately show ?thesis
        using assms(1) sat_sem_mult_def mult_inv_on_state_implies_uniqueness by blast
    qed
    then show ?SEM
      using \<open>\<omega> = Abs_preal p \<odot> ?\<omega>p\<close> \<open>v \<in> set_from_type (interp.domains I) x1a\<close> sat.simps(7) sat_sem_mult_def by blast
  qed
qed

theorem sem_syn_mult_equiv:
  assumes "p > 0"
  shows "A^(Abs_preal p) \<equiv>[\<Delta>] (syntactic_mult p A)"
proof (rule assertion_equivalence_rule)
  fix D F \<omega>
  let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
  assume "fun_interp_indep_mask F"
     and "?I \<Turnstile>[sem] \<langle>A^Abs_preal p; \<omega>\<rangle>"
  then show "?I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
    by (simp add: assms sem_syn_mult_equiv_aux)
next
  fix D F \<omega>
  let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
  assume "fun_interp_indep_mask F"
     and "?I \<Turnstile> \<langle>syntactic_mult p A; \<omega>\<rangle>"
  then show "?I \<Turnstile>[sem] \<langle>A^Abs_preal p; \<omega>\<rangle>"
    by (simp add: assms sem_syn_mult_equiv_aux)
qed



end