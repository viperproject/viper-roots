subsection \<open>Fractional Permissions\<close>

text \<open>In this file, we define the type of positive permission amounts, which we use as permission amounts in
extended heaps (see FractionalHeap.thy).\<close>

theory PosPerm
  imports Main
begin


                     
class pos_perm = zero_neq_one + comm_semiring + comm_monoid_mult + inverse
  + comm_monoid_add + linorder + distrib_lattice + dense_linorder +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
      and field_divide_inverse: "a / b = a * inverse b"
      and field_inverse_zero: "inverse 0 = 0"
      and all_pos: "a \<ge> 0"
      and padd_mono: "p1 \<le> p2 \<and> q1 \<le> q2 \<Longrightarrow> p1 + q1 \<le> p2 + q2"
      and pperm_gte_padd: "p \<ge> q \<Longrightarrow> (\<exists>r. p = q + r)"
      and pinv_inverts: "a \<ge> b \<and> b > 0 \<Longrightarrow> inverse b \<ge> inverse a"
      and two_larger_one: "1 + 1 > 1"
      and padd_cancellative: "a = x + b \<Longrightarrow> a = y + b \<Longrightarrow> x = y"
begin

(* Why to we have these abbreviations twice? *)
abbreviation (input) pwrite where "pwrite \<equiv> 1"
abbreviation half where "half \<equiv> 1 / (1+1)"
abbreviation (input) pnone where "pnone \<equiv> 0"

abbreviation pmin :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "pmin \<equiv> inf"
abbreviation pmax :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where "pmax \<equiv> sup"

abbreviation ppos where "ppos \<equiv> (\<lambda>p. p > 0)"

lemma pperm_pgt_pnone: "p1 > pnone \<Longrightarrow> p1 \<noteq> pnone"
  by simp

lemma pperm_pnone_pgt: "p1 \<noteq> pnone \<Longrightarrow> p1 > pnone"
  by (simp add: local.all_pos local.dual_order.not_eq_order_implies_strict)

lemma pmin_comm:
  "pmin a b = pmin b a"
  by (simp add: inf_sup_aci(1))

lemma pmin_greater:
  "a \<ge> (pmin a b)"
  by simp

lemma pmin_is:
  assumes "a \<ge> b"
  shows "pmin a b = b"
  by (simp add: assms local.inf.absorb2)

lemma pmax_comm:
  "pmax a b = pmax b a"
  by (simp add: inf_sup_aci(5))

lemma pmax_smaller:
  "pmax a b \<ge> a"
  by auto

lemma pmax_is:
  assumes "a \<ge> b"
  shows "pmax a b = a"
  by (simp add: assms local.sup.absorb1)

lemma pmax_is_smaller:
  assumes "x \<ge> a"
      and "x \<ge> b"
    shows "x \<ge> (pmax a b)"
  by (simp add: assms(1) assms(2))

lemma pperm_exists_stricly_smaller_nonzero:
  assumes "p \<noteq> pnone" 
  shows "\<exists>q. q \<noteq> pnone \<and> p > q"
  by (metis assms local.dense pperm_pgt_pnone pperm_pnone_pgt)

lemma pgt_implies_pgte:
  assumes "a > b"
  shows "a \<ge> b"
  using assms by auto

lemma half_plus_half:
  "half + half = 1"
  by (metis local.add_0_left local.distrib_left local.dual_order.antisym local.field_divide_inverse local.field_inverse local.le_cases local.padd_mono local.zero_neq_one mult_commute)

lemma pgte_antisym:
  assumes "a \<ge> b"
      and "b \<ge> a"
    shows "a = b"
  by (simp add: assms(1) assms(2) local.dual_order.antisym)

lemma sum_larger:
  "a + b \<ge> a"
  by (metis local.add_0_right local.all_pos local.dual_order.eq_iff local.padd_mono)

lemma greater_sum_both:
  assumes "a \<ge> b + c"
  shows "\<exists>a1 a2. a = a1 + a2 \<and> a1 \<ge> b \<and> a2 \<ge> c"
  using add_assoc assms pperm_gte_padd sum_larger by blast

lemma not_pgte_charact:
  "\<not> a \<ge> b \<longleftrightarrow> b > a"
  by fastforce

lemma pgte_pgt:
  assumes "a > b"
      and "c \<ge> d"
    shows "a + c > b + d"
proof -
  obtain r where r_def: "a = b + r"
    using assms(1) local.dual_order.strict_iff_not local.pperm_gte_padd by blast
  then have "a + c \<ge> b + d"
    using assms(1) assms(2) local.order.strict_implies_order local.padd_mono by presburger
  then show ?thesis
    by (metis r_def assms(1) assms(2) local.order_antisym local.order_refl local.padd_cancellative local.padd_mono not_pgte_charact sum_larger)
qed

lemma pmult_distr:
  "a * (b + c) = (a * b) + (a * c)"
  by (simp add: distrib_left)

lemma pmult_comm:
  "a * b = b * a"
  using mult.commute by auto

lemma pmult_special:
  "pwrite * x = x"
  by simp


lemma pinv_pmult_ok:
  assumes "ppos p"
  shows "p * inverse p = pwrite"
  using assms local.field_inverse pmult_comm pperm_pgt_pnone by blast

lemma pinv_pwrite:
  "inverse pwrite = pwrite"
  using local.field_inverse local.one_neq_zero by fastforce

lemma pmin_pmax:
  assumes "x \<ge> pmin a b"
  shows "x = pmin (pmax x a) (pmax x b)"
  by (metis assms local.sup_inf_distrib1 pmax_is)
                                  
lemma pmin_sum:
  "pmin a b + c = pmin (a + c) (b + c)"
  by (metis not_pgte_charact pgt_implies_pgte pgte_pgt pmin_comm pmin_is)

lemma pmin_sum_larger:
  "pmin (a1 + b1) (a2 + b2) \<ge> pmin a1 a2 + pmin b1 b2"
  by (simp add: local.padd_mono)

lemma decompose_larger_than_one:
  assumes "x > 1"
  shows "\<exists>r. r > 0 \<and> x = 1 + r"
  by (metis assms local.add_0_right local.order.irrefl local.order.strict_implies_order pperm_gte_padd pperm_pnone_pgt)

lemma decompose_smaller_than_one:
  assumes "x < 1"
  shows "\<exists>r. r > 0 \<and> 1 = x + r"
  by (metis assms local.add_0_right local.order.irrefl local.order.strict_implies_order pperm_gte_padd pperm_pnone_pgt)

lemma pwrite_larger_one:
  "pwrite > half"
  by (metis half_plus_half local.dual_order.not_eq_order_implies_strict local.two_larger_one sum_larger)

lemma one_plus_one:
  "1 + 1 \<noteq> 0"
  by (metis local.dual_order.asym local.two_larger_one pperm_pnone_pgt)

lemma pinv_double_half:
  "half * (inverse p) = inverse (p + p)"
proof (cases "p = 0")
  case True
  then show ?thesis
    by (metis half_plus_half local.add_0_right local.field_inverse_zero local.mult_1_right pmult_comm pmult_distr)
next
  case False
  have "inverse p * p = pwrite \<and> inverse (p + p) * (p + p) = pwrite \<and> inverse (pwrite + pwrite) * (pwrite + pwrite) = pwrite"
    by (metis False local.dual_order.strict_iff_not local.field_inverse one_plus_one pperm_pnone_pgt sum_larger)
  then have "inverse (1 + 1) * inverse p = inverse (p + p)"
    by (metis abel_semigroup.left_commute local.mult.abel_semigroup_axioms local.mult_1_right pmult_distr)
  moreover have "half * inverse p = inverse (1 + 1) * inverse p"
    by (simp add: local.field_divide_inverse)
  ultimately show ?thesis by simp
qed


end

end
