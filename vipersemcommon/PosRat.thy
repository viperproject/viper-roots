subsection \<open>Fractional Permissions\<close>

text \<open>In this file, we define the type of positive rationals, which we use as permission amounts in
extended heaps (see FractionalHeap.thy).\<close>

theory PosRat
  imports Main HOL.Rat
begin

typedef prat = "{ r :: rat |r. r \<ge> 0}" by fastforce

setup_lifting type_definition_prat

instantiation prat :: zero_neq_one
begin

lift_definition zero_prat :: "prat" is "0" by simp

lift_definition one_prat :: "prat" is "1" by simp

instance proof
  show "0 \<noteq> (1 :: prat)"
    using one_prat.rep_eq zero_prat.rep_eq by fastforce
qed

end

instantiation prat :: comm_semiring
begin

lift_definition times_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(*)" by simp

lift_definition plus_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(+)" by simp

instance proof
  fix a b c :: prat

  show "a * b * c = a * (b * c)"
    using Rep_prat_inject times_prat.rep_eq by fastforce

  show "a * b = b * a"
    by (metis (mono_tags) Rep_prat_inject mult.commute times_prat.rep_eq)

  show "a + b + c = a + (b + c)"
    using Rep_prat_inject plus_prat.rep_eq by fastforce

  show "a + b = b + a"
    by (metis (mono_tags) Rep_prat_inject add.commute plus_prat.rep_eq)

  show "(a + b) * c = a * c + b * c"
    by (metis (mono_tags, lifting) Rep_prat_inject distrib_right plus_prat.rep_eq times_prat.rep_eq)
qed

end


instantiation prat :: comm_monoid_mult
begin

instance proof
  fix a :: prat
  show "1 * a = a"
    by (metis Rep_prat_inject lambda_one one_prat.rep_eq times_prat.rep_eq)
qed

end


instantiation prat :: inverse
begin

lift_definition divide_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(/)" by simp

definition inverse_prat :: "prat \<Rightarrow> prat" where "inverse_prat p = divide 1 p"

instance proof
qed

end

instantiation prat :: comm_monoid_add
begin

instance proof
  show "\<And>a :: prat. 0 + a = a"
    by (metis Rep_prat_inject add_0 plus_prat.rep_eq zero_prat.rep_eq)
qed

end

lemma field_inverse:
  assumes "(a :: prat) \<noteq> 0"
  shows "inverse a * a = 1"
  by (metis Rep_prat_inverse assms divide_prat.rep_eq inverse_prat_def nonzero_eq_divide_eq times_prat.rep_eq zero_prat.rep_eq)

lemma field_divide_inverse: "(a :: prat) / b = a * inverse b"
  by (metis Rep_prat_inverse divide_prat.rep_eq inverse_prat_def mult.right_neutral times_divide_eq_right times_prat.rep_eq)

lemma field_inverse_zero: "inverse (0 :: prat) = 0"
  by (metis divide_prat.abs_eq field_class.field_inverse_zero inverse_eq_divide inverse_prat_def one_prat.abs_eq one_prat.rsp zero_prat.abs_eq zero_prat.rsp)


instantiation prat :: linorder
begin

lift_definition less_prat :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(<)" done

lift_definition less_eq_prat :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(\<le>)" done

instance proof
  fix x y z :: prat
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (meson less_eq_prat.rep_eq less_prat.rep_eq nless_le verit_comp_simplify1(3))
  show "x \<le> x"
    by (simp add: less_eq_prat.rep_eq)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_prat.rep_eq by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: Rep_prat_inject less_eq_prat.rep_eq)
  show "x \<le> y \<or> y \<le> x"
    using less_eq_prat.rep_eq by force
qed

end

instantiation prat :: distrib_lattice
begin                            

lift_definition inf_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(min)" by simp
lift_definition sup_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat" is "(max)" by simp

instance proof
  fix x y z :: prat

  show "inf x y \<le> x"
    by (simp add: inf_prat.rep_eq less_eq_prat.rep_eq)

  show "inf x y \<le> y"
    by (simp add: inf_prat.rep_eq less_eq_prat.rep_eq)

  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (simp add: inf_prat.rep_eq less_eq_prat.rep_eq)

  show "x \<le> sup x y"
    by (simp add: less_eq_prat.rep_eq sup_prat.rep_eq)

  show "y \<le> sup x y"
    by (simp add: less_eq_prat.rep_eq sup_prat.rep_eq)

  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (simp add: less_eq_prat.rep_eq sup_prat.rep_eq)

  show "sup x (inf y z) = inf (sup x y) (sup x z)"
    by (metis (mono_tags, lifting) Rep_prat_inject inf_prat.rep_eq inf_rat_def sup_inf_distrib1 sup_max sup_prat.rep_eq)

qed

end



abbreviation pwrite :: prat where "pwrite \<equiv> 1"
abbreviation half :: prat where "half \<equiv> 1 / (Abs_prat 2)"
abbreviation pnone :: prat where "pnone \<equiv> 0"

abbreviation pmin :: "prat \<Rightarrow> prat \<Rightarrow> prat" where "pmin \<equiv> inf"
abbreviation pmax :: "prat \<Rightarrow> prat \<Rightarrow> prat" where "pmax \<equiv> sup"

abbreviation padd :: "prat \<Rightarrow> prat \<Rightarrow> prat" where "padd \<equiv> (+)"
abbreviation pmult :: "prat \<Rightarrow> prat \<Rightarrow> prat" where "pmult \<equiv> (*)"
abbreviation pinv :: "prat \<Rightarrow> prat" where "pinv \<equiv> inverse"
abbreviation pdiv :: "prat \<Rightarrow> prat \<Rightarrow> prat" where "pdiv \<equiv> (/)"

lift_definition pgte :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(\<ge>)" done
lift_definition pgt :: "prat \<Rightarrow> prat \<Rightarrow> bool" is "(>)" done
lift_definition ppos :: "prat \<Rightarrow> bool" is "\<lambda>p. p > 0" done

instantiation prat :: minus
begin

definition minus_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat"  where
  "minus_prat a b = Abs_prat ((Rep_prat a) - (Rep_prat b))"

instance proof
qed

end

lemma prat_pgt_pnone: "pgt p1 pnone \<Longrightarrow> p1 \<noteq> pnone"
  by (transfer) simp

lemma prat_pnone_pgt: "p1 \<noteq> pnone \<Longrightarrow> pgt p1 pnone"
  by (transfer) simp

lemma padd_mono:
  assumes "p1 \<le> p2" and "q1 \<le> q2"
  shows "padd p1 q1 \<le> padd p2 q2"
  using assms
  by (transfer) simp

lemma prat_gte_padd:
  assumes "(p :: prat) \<ge> q"
  shows "\<exists>r. p = padd q r"
  using assms
proof transfer
  fix q p :: rat
  assume "p \<ge> q" 

  from \<open>p \<ge> q\<close> have "p = q + (p-q)"
    by simp

  moreover from \<open>p \<ge> q\<close> have "p-q \<ge> 0"
    by simp

  ultimately show "\<exists>r\<in>{r |r. 0 \<le> r}. p = q + r"
    by blast
qed

lemma positive_rat_prat:
  assumes "p > 0"
  shows "(Abs_prat p) \<noteq> pnone"
  by (metis Abs_prat_inverse assms mem_Collect_eq order_less_le zero_prat.rep_eq)

lemma pmin_comm:
  "pmin a b = pmin b a"
  by (simp add: inf_sup_aci(1))

lemma pmin_greater:
  "pgte a (pmin a b)"
  by (simp add: inf_prat.rep_eq pgte.rep_eq)

lemma pmin_is:
  assumes "pgte a b"
  shows "pmin a b = b"
  by (meson assms inf_absorb2 less_eq_prat.rep_eq pgte.rep_eq)

lemma pmax_comm:
  "pmax a b = pmax b a"
  by (simp add: inf_sup_aci(5))

lemma pmax_smaller:
  "pgte (pmax a b) a"
  by (simp add: pgte.rep_eq sup_prat.rep_eq)

lemma pmax_is:
  assumes "pgte a b"
  shows "pmax a b = a"
  using assms less_eq_prat.rep_eq pgte.rep_eq sup_absorb1 by blast

lemma pmax_is_smaller:
  assumes "pgte x a"
      and "pgte x b"
    shows "pgte x (pmax a b)"
  using assms(1) assms(2) pgte.rep_eq sup_prat.rep_eq by auto

lemma prat_exists_stricly_smaller_nonzero:
  assumes "p \<noteq> pnone" 
  shows "\<exists>q. q \<noteq> pnone \<and> pgt p q"
  using assms
  apply transfer
  by (metis dense_le mem_Collect_eq nle_le)

lemma half_between_0_1:
  "pgt pwrite half"
  by (simp add: Abs_prat_inverse divide_prat.rep_eq one_prat.rep_eq pgt.rep_eq)

lemma pgt_implies_pgte:
  assumes "pgt a b"
  shows "pgte a b"
  by (meson assms less_imp_le pgt.rep_eq pgte.rep_eq)

lemma half_plus_half:
  "half + half = 1"
proof -
  have "half + half = (1 + 1) / (Abs_prat 2)"
    by (simp add: distrib_right field_divide_inverse)
  then show ?thesis
    by (metis Rep_prat_inverse divide_prat.rep_eq divide_self numeral_Bit0 numeral_One one_prat.rep_eq plus_prat.rep_eq zero_neq_numeral)
qed

lemma pgte_antisym:
  assumes "pgte a b"
      and "pgte b a"
    shows "a = b"
  by (metis Rep_prat_inverse assms(1) assms(2) leD le_less pgte.rep_eq)

lemma sum_larger:
  "pgte (padd a b) a"
  using Rep_prat pgte.rep_eq plus_prat.rep_eq by auto

lemma greater_sum_both:
  assumes "pgte a (padd b c)"
  shows "\<exists>a1 a2. a = padd a1 a2 \<and> pgte a1 b \<and> pgte a2 c"
proof -
  obtain aa bb cc where "aa = Rep_prat a" "bb = Rep_prat b" "cc = Rep_prat c"
    by simp
  then have "aa \<ge> bb + cc"
    using assms pgte.rep_eq plus_prat.rep_eq by auto
  then obtain x where "aa = bb + x" "x \<ge> cc"
    by (metis add.commute add_le_cancel_left diff_add_cancel)
  let ?a1 = "Abs_prat bb"
  let ?a2 = "Abs_prat x"
  have "a = padd ?a1 ?a2"
    by (metis Rep_prat Rep_prat_inverse \<open>aa = Rep_prat a\<close> \<open>aa = bb + x\<close> \<open>bb = Rep_prat b\<close> \<open>cc = Rep_prat c\<close> \<open>cc \<le> x\<close> dual_order.trans eq_onp_same_args mem_Collect_eq plus_prat.abs_eq)
  moreover have "?a1 \<ge> b"
    by (simp add: Rep_prat_inverse \<open>bb = Rep_prat b\<close>)
  moreover have "?a2 \<ge> c"
    using Rep_prat_inverse \<open>aa = Rep_prat a\<close> \<open>bb + cc \<le> aa\<close> \<open>bb = Rep_prat b\<close> \<open>cc = Rep_prat c\<close> calculation(1) less_eq_prat.rep_eq plus_prat.rep_eq by force
  ultimately show ?thesis
    by (metis le_iff_sup pmax_smaller)
qed


lemma padd_cancellative:
  assumes "a = padd x b"
      and "a = padd y b"
    shows "x = y"
  by (metis Rep_prat_inject add_right_imp_eq assms(1) assms(2) plus_prat.rep_eq)


lemma not_pgte_charact:
  "\<not> pgte a b \<longleftrightarrow> pgt b a"
  by (meson not_less pgt.rep_eq pgte.rep_eq)

lemma pgte_pgt:
  assumes "pgt a b"
      and "pgte c d"
    shows "pgt (padd a c) (padd b d)"
  using assms(1) assms(2) pgt.rep_eq pgte.rep_eq plus_prat.rep_eq by auto

lemma pmult_distr:
  "pmult a (padd b c) = padd (pmult a b) (pmult a c)"
  by (simp add: distrib_left)

lemma pmult_comm:
  "pmult a b = pmult b a"
  using mult.commute by auto

lemma pmult_special:
  "pmult pwrite x = x"
  by simp

lemma pinv_double_half:
  "pmult half (pinv p) = pinv (padd p p)"
  by (metis Rep_prat_inverse div_by_1 divide_divide_eq_right divide_prat.rep_eq field_divide_inverse mult_1 one_add_one one_prat.rep_eq plus_prat.rep_eq pmult_distr)

lemma pinv_inverts:
  assumes "pgte a b"
      and "ppos b"
    shows "pgte (pinv b) (pinv a)"
  by (metis assms(1) assms(2) divide_prat.rep_eq frac_le inverse_prat_def le_numeral_extra(4) linordered_nonzero_semiring_class.zero_le_one one_prat.rep_eq pgte.rep_eq ppos.rep_eq)



lemma pinv_pmult_ok:
  assumes "ppos p"
  shows "pmult p (pinv p) = pwrite"
proof -
  obtain r where "r = Rep_prat p" by simp
  then have "r * ((Fract 1 1) / r) = Fract 1 1"
    using assms ppos.rep_eq by auto
  then show ?thesis
    by (metis assms field_inverse order_less_irrefl pmult_comm ppos.rep_eq zero_prat.rep_eq)
qed


lemma pinv_pwrite:
  "pinv pwrite = pwrite"
  using divide_prat.abs_eq inverse_prat_def one_prat.rsp one_prat_def by force

lemma pmin_pmax:
  assumes "pgte x (pmin a b)"
  shows "x = pmin (pmax x a) (pmax x b)"
proof (cases "pgte x a")
  case True
  then show ?thesis
    by (metis pmax_is pmax_smaller pmin_comm pmin_is)
next
  case False
  then show ?thesis
    by (metis assms not_pgte_charact pgt_implies_pgte pmax_is pmax_smaller pmin_comm pmin_is)
qed

lemma pmin_sum:
  "padd (pmin a b) c = pmin (padd a c) (padd b c)"
  by (metis not_pgte_charact pgt_implies_pgte pgte_pgt pmin_comm pmin_is)

lemma pmin_sum_larger:
  "pgte (pmin (padd a1 b1) (padd a2 b2)) (padd (pmin a1 a2) (pmin b1 b2))"
proof (cases "pgte (padd a1 b1) (padd a2 b2)")
  case True
  then have "pmin (padd a1 b1) (padd a2 b2) = padd a2 b2"
    by (simp add: pmin_is)
  moreover have "pgte a2 (pmin a1 a2) \<and> pgte b2 (pmin b1 b2)"
    by (metis pmin_comm pmin_greater)
  ultimately show ?thesis
    by (simp add: pgte.rep_eq plus_prat.rep_eq)
next
  case False
  then have "pmin (padd a1 b1) (padd a2 b2) = padd a1 b1"
    by (metis not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
  moreover have "pgte a1 (pmin a1 a2) \<and> pgte b1 (pmin b1 b2)"
    by (metis pmin_greater)
  ultimately show ?thesis
    by (simp add: pgte.rep_eq plus_prat.rep_eq)
qed

lemma decompose_larger_than_one:
  assumes "x > (1 :: prat)"
  shows "\<exists>r. r > 0 \<and> x = 1 + r"
proof -
  have "Rep_prat x > 1"
    using assms less_prat.rep_eq one_prat.rep_eq by force
  then have "Rep_prat x = 1 + (Rep_prat x - 1)"
    by simp
  moreover have "Rep_prat x - 1 > 0"
    by (simp add: \<open>1 < Rep_prat x\<close>)
  ultimately have "Abs_prat (Rep_prat x - 1) > 0 \<and> x = 1 + (Abs_prat (Rep_prat x - 1))"
    by (metis Rep_prat Rep_prat_inverse eq_onp_same_args less_prat.abs_eq mem_Collect_eq one_prat.abs_eq one_prat.rsp order_less_imp_le plus_prat.abs_eq zero_prat.rep_eq)
  then show ?thesis by auto
qed

lemma decompose_smaller_than_one:
  assumes "x < (1 :: prat)"
  shows "\<exists>r. r > 0 \<and> 1 = x + r"
proof -
  have "Abs_prat (1 - Rep_prat x) > 0 \<and> 1 = x + (Abs_prat (1 - Rep_prat x))"
  proof
    show "pnone < Abs_prat (1 - Rep_prat x)"
      by (metis assms diff_gt_0_iff_gt eq_onp_same_args less_prat.abs_eq less_prat.rep_eq one_prat.rep_eq order_less_imp_le zero_prat.abs_eq zero_prat.rsp)
    show "pwrite = padd x (Abs_prat (1 - Rep_prat x))"
      by (metis Rep_prat Rep_prat_inverse assms diff_gt_0_iff_gt eq_onp_same_args le_add_diff_inverse less_prat.rep_eq mem_Collect_eq one_prat.rep_eq order_less_imp_le plus_prat.abs_eq)
  qed
  then show ?thesis by auto
qed

end
