subsection \<open>Fractional Permissions\<close>

text \<open>In this file, we define the type of positive realionals, which we use as permission amounts in
extended heaps (see FractionalHeap.thy).\<close>

theory PosReal
  imports Main HOL.Real PosPerm
begin

typedef preal = "{ r :: real |r. r \<ge> 0}" by fastforce

setup_lifting type_definition_preal

instantiation preal :: zero_neq_one
begin

lift_definition zero_preal :: "preal" is "0" by simp

lift_definition one_preal :: "preal" is "1" by simp

instance proof
  show "0 \<noteq> (1 :: preal)"
    using one_preal.rep_eq zero_preal.rep_eq by fastforce
qed

end

instantiation preal :: comm_semiring
begin

lift_definition times_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" is "(*)" by simp

lift_definition plus_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" is "(+)" by simp

instance proof
  fix a b c :: preal

  show "a * b * c = a * (b * c)"
    using Rep_preal_inject times_preal.rep_eq by fastforce

  show "a * b = b * a"
    by (metis (mono_tags) Rep_preal_inject mult.commute times_preal.rep_eq)

  show "a + b + c = a + (b + c)"
    using Rep_preal_inject plus_preal.rep_eq by fastforce

  show "a + b = b + a"
    by (metis (mono_tags) Rep_preal_inject add.commute plus_preal.rep_eq)

  show "(a + b) * c = a * c + b * c"
    by (metis (mono_tags, lifting) Rep_preal_inject distrib_right plus_preal.rep_eq times_preal.rep_eq)
qed

end


instantiation preal :: comm_monoid_mult
begin

instance proof
  fix a :: preal
  show "1 * a = a"
    by (metis Rep_preal_inject lambda_one one_preal.rep_eq times_preal.rep_eq)
qed

end


instantiation preal :: inverse
begin

lift_definition divide_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" is "(/)" by simp

definition inverse_preal :: "preal \<Rightarrow> preal" where "inverse_preal p = divide 1 p"

instance proof
qed

end

instantiation preal :: comm_monoid_add
begin

instance proof
  show "\<And>a :: preal. 0 + a = a"
    by (metis Rep_preal_inject add_0 plus_preal.rep_eq zero_preal.rep_eq)
qed

end

lemma field_inverse:
  assumes "(a :: preal) \<noteq> 0"
  shows "inverse a * a = 1"
  by (metis Rep_preal_inverse assms divide_preal.rep_eq inverse_preal_def nonzero_eq_divide_eq times_preal.rep_eq zero_preal.rep_eq)

lemma field_divide_inverse: "(a :: preal) / b = a * inverse b"
  by (metis Rep_preal_inverse divide_preal.rep_eq inverse_preal_def mult.right_neutral times_divide_eq_right times_preal.rep_eq)

lemma field_inverse_zero: "inverse (0 :: preal) = 0"
  by (metis divide_preal.abs_eq field_class.field_inverse_zero inverse_eq_divide inverse_preal_def one_preal.abs_eq one_preal.rsp zero_preal.abs_eq zero_preal.rsp)


instantiation preal :: linorder
begin

lift_definition less_preal :: "preal \<Rightarrow> preal \<Rightarrow> bool" is "(<)" done

lift_definition less_eq_preal :: "preal \<Rightarrow> preal \<Rightarrow> bool" is "(\<le>)" done

instance proof
  fix x y z :: preal
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (meson less_eq_preal.rep_eq less_preal.rep_eq nless_le verit_comp_simplify1(3))
  show "x \<le> x"
    by (simp add: less_eq_preal.rep_eq)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_preal.rep_eq by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: Rep_preal_inject less_eq_preal.rep_eq)
  show "x \<le> y \<or> y \<le> x"
    using less_eq_preal.rep_eq by force
qed

end

instantiation preal :: distrib_lattice
begin                            

lift_definition inf_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" is "(min)" by simp
lift_definition sup_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" is "(max)" by simp

instance proof
  fix x y z :: preal

  show "inf x y \<le> x"
    by (simp add: inf_preal.rep_eq less_eq_preal.rep_eq)

  show "inf x y \<le> y"
    by (simp add: inf_preal.rep_eq less_eq_preal.rep_eq)

  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (simp add: inf_preal.rep_eq less_eq_preal.rep_eq)

  show "x \<le> sup x y"
    by (simp add: less_eq_preal.rep_eq sup_preal.rep_eq)

  show "y \<le> sup x y"
    by (simp add: less_eq_preal.rep_eq sup_preal.rep_eq)

  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (simp add: less_eq_preal.rep_eq sup_preal.rep_eq)

  show "sup x (inf y z) = inf (sup x y) (sup x z)"
    using Rep_preal_inject
      inf_preal.rep_eq[of y z] inf_preal.rep_eq[of] sup_preal.rep_eq[of x y] sup_preal.rep_eq[of x z]
    by (smt (verit, del_insts))
qed

end



abbreviation pwrite :: preal where "pwrite \<equiv> 1"
abbreviation half :: preal where "half \<equiv> 1 / (Abs_preal 2)"
abbreviation pnone :: preal where "pnone \<equiv> 0"

abbreviation pmin :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "pmin \<equiv> inf"
abbreviation pmax :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "pmax \<equiv> sup"

abbreviation padd :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "padd \<equiv> (+)"
abbreviation pmult :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "pmult \<equiv> (*)"
abbreviation pinv :: "preal \<Rightarrow> preal" where "pinv \<equiv> inverse"
abbreviation pdiv :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "pdiv \<equiv> (/)"

lift_definition pgte :: "preal \<Rightarrow> preal \<Rightarrow> bool" is "(\<ge>)" done
lift_definition pgt :: "preal \<Rightarrow> preal \<Rightarrow> bool" is "(>)" done
lift_definition ppos :: "preal \<Rightarrow> bool" is "\<lambda>p. p > 0" done

instantiation preal :: minus
begin

definition minus_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal"  where
  "minus_preal a b = Abs_preal ((Rep_preal a) - (Rep_preal b))"

instance proof
qed

end

lemma preal_pgt_pnone: "pgt p1 pnone \<Longrightarrow> p1 \<noteq> pnone"
  by (transfer) simp

lemma preal_pnone_pgt: "p1 \<noteq> pnone \<Longrightarrow> pgt p1 pnone"
  by (transfer) simp

lemma padd_mono:
  assumes "p1 \<le> p2" and "q1 \<le> q2"
  shows "padd p1 q1 \<le> padd p2 q2"
  using assms
  by (transfer) simp

lemma preal_gte_padd:
  assumes "(p :: preal) \<ge> q"
  shows "\<exists>r. p = padd q r"
  using assms
proof transfer
  fix q p :: real
  assume "p \<ge> q" 

  from \<open>p \<ge> q\<close> have "p = q + (p-q)"
    by simp

  moreover from \<open>p \<ge> q\<close> have "p-q \<ge> 0"
    by simp

  ultimately show "\<exists>r\<in>{r |r. 0 \<le> r}. p = q + r"
    by blast
qed

lemma positive_real_preal:
  assumes "p > 0"
  shows "(Abs_preal p) \<noteq> pnone"
  by (metis Abs_preal_inverse assms mem_Collect_eq order_less_le zero_preal.rep_eq)

lemma pmin_comm:
  "pmin a b = pmin b a"
  by (simp add: inf_sup_aci(1))

lemma pmin_greater:
  "pgte a (pmin a b)"
  by (simp add: inf_preal.rep_eq pgte.rep_eq)

lemma pmin_is:
  assumes "pgte a b"
  shows "pmin a b = b"
  by (meson assms inf_absorb2 less_eq_preal.rep_eq pgte.rep_eq)

lemma pmax_comm:
  "pmax a b = pmax b a"
  by (simp add: inf_sup_aci(5))

lemma pmax_smaller:
  "pgte (pmax a b) a"
  by (simp add: pgte.rep_eq sup_preal.rep_eq)

lemma pmax_is:
  assumes "pgte a b"
  shows "pmax a b = a"
  using assms less_eq_preal.rep_eq pgte.rep_eq sup_absorb1 by blast

lemma pmax_is_smaller:
  assumes "pgte x a"
      and "pgte x b"
    shows "pgte x (pmax a b)"
  using assms(1) assms(2) pgte.rep_eq sup_preal.rep_eq by auto

lemma preal_exists_stricly_smaller_nonzero:
  assumes "p \<noteq> pnone" 
  shows "\<exists>q. q \<noteq> pnone \<and> pgt p q"
  using assms
  apply transfer
  by (metis dense_le mem_Collect_eq nle_le)

lemma half_between_0_1:
  "pgt pwrite half"
  by (simp add: Abs_preal_inverse divide_preal.rep_eq one_preal.rep_eq pgt.rep_eq)

lemma pgt_implies_pgte:
  assumes "pgt a b"
  shows "pgte a b"
  by (meson assms less_imp_le pgt.rep_eq pgte.rep_eq)

lemma half_plus_half:
  "half + half = 1"
  by (metis (mono_tags, opaque_lifting) Rep_preal_inverse divide_preal.rep_eq field_sum_of_halves mult_2 one_add_one one_preal.rep_eq plus_preal.rep_eq)

lemma pgte_antisym:
  assumes "pgte a b"
      and "pgte b a"
    shows "a = b"
  by (metis Rep_preal_inverse assms(1) assms(2) leD le_less pgte.rep_eq)

lemma sum_larger:
  "pgte (padd a b) a"
  using Rep_preal pgte.rep_eq plus_preal.rep_eq by auto

lemma greater_sum_both:
  assumes "pgte a (padd b c)"
  shows "\<exists>a1 a2. a = padd a1 a2 \<and> pgte a1 b \<and> pgte a2 c"
proof -
  obtain aa bb cc where "aa = Rep_preal a" "bb = Rep_preal b" "cc = Rep_preal c"
    by simp
  then have "aa \<ge> bb + cc"
    using assms pgte.rep_eq plus_preal.rep_eq by auto
  then obtain x where "aa = bb + x" "x \<ge> cc"
    by (metis add.commute add_le_cancel_left diff_add_cancel)
  then show ?thesis
    by (smt (verit, ccfv_threshold) Rep_preal Rep_preal_inverse \<open>aa = Rep_preal a\<close> \<open>bb = Rep_preal b\<close> \<open>cc = Rep_preal c\<close> add_0_right dual_order.trans eq_onp_same_args le_add_same_cancel1 mem_Collect_eq pgte.abs_eq plus_preal.abs_eq zero_preal.rsp)
qed


lemma padd_cancellative:
  assumes "a = padd x b"
      and "a = padd y b"
    shows "x = y"
  by (metis Rep_preal_inject add_right_imp_eq assms(1) assms(2) plus_preal.rep_eq)


lemma not_pgte_charact:
  "\<not> pgte a b \<longleftrightarrow> pgt b a"
  by (meson not_less pgt.rep_eq pgte.rep_eq)

lemma pgte_pgt:
  assumes "pgt a b"
      and "pgte c d"
    shows "pgt (padd a c) (padd b d)"
  using assms(1) assms(2) pgt.rep_eq pgte.rep_eq plus_preal.rep_eq by auto

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
  by (metis Rep_preal_inverse div_by_1 divide_divide_eq_right divide_preal.rep_eq field_divide_inverse mult_1 one_add_one one_preal.rep_eq plus_preal.rep_eq pmult_distr)

lemma pinv_inverts:
  assumes "pgte a b"
      and "ppos b"
    shows "pgte (pinv b) (pinv a)"
  by (metis assms(1) assms(2) divide_preal.rep_eq frac_le inverse_preal_def le_numeral_extra(4) linordered_nonzero_semiring_class.zero_le_one one_preal.rep_eq pgte.rep_eq ppos.rep_eq)



lemma pinv_pmult_ok:
  assumes "ppos p"
  shows "pmult p (pinv p) = pwrite"
proof -
  obtain r where "r = Rep_preal p" by simp
  then show ?thesis
    by (metis assms field_inverse order_less_irrefl pmult_comm ppos.rep_eq zero_preal.rep_eq)
qed


lemma pinv_pwrite:
  "pinv pwrite = pwrite"
  using divide_preal.abs_eq inverse_preal_def one_preal.rsp one_preal_def by force

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
    by (simp add: pgte.rep_eq plus_preal.rep_eq)
next
  case False
  then have "pmin (padd a1 b1) (padd a2 b2) = padd a1 b1"
    by (metis not_pgte_charact pgt_implies_pgte pmin_comm pmin_is)
  moreover have "pgte a1 (pmin a1 a2) \<and> pgte b1 (pmin b1 b2)"
    by (metis pmin_greater)
  ultimately show ?thesis
    by (simp add: pgte.rep_eq plus_preal.rep_eq)
qed


lemma decompose_larger_than_one:
  assumes "x > (1 :: preal)"
  shows "\<exists>r. r > 0 \<and> x = 1 + r"
proof -
  have "Rep_preal x > 1"
    using assms less_preal.rep_eq one_preal.rep_eq by force
  then have "Rep_preal x = 1 + (Rep_preal x - 1)"
    by simp
  moreover have "Rep_preal x - 1 > 0"
    by (simp add: \<open>1 < Rep_preal x\<close>)
  ultimately have "Abs_preal (Rep_preal x - 1) > 0 \<and> x = 1 + (Abs_preal (Rep_preal x - 1))"
    by (metis Rep_preal Rep_preal_inverse eq_onp_same_args less_preal.abs_eq mem_Collect_eq one_preal.abs_eq one_preal.rsp order_less_imp_le plus_preal.abs_eq zero_preal.rep_eq)
  then show ?thesis by auto
qed

lemma decompose_smaller_than_one:
  assumes "x < (1 :: preal)"
  shows "\<exists>r. r > 0 \<and> 1 = x + r"
proof -
  have "Abs_preal (1 - Rep_preal x) > 0 \<and> 1 = x + (Abs_preal (1 - Rep_preal x))"
    by (smt (verit, ccfv_threshold) Rep_preal Rep_preal_inverse assms eq_onp_same_args less_preal.abs_eq mem_Collect_eq one_preal.abs_eq plus_preal.abs_eq zero_preal.abs_eq)
  then show ?thesis by auto
qed


(*
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
*)


instantiation preal :: pos_perm
begin

instance proof
  fix x y a b p1 p2 q1 q2 :: preal
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" sorry
  show "\<And>a. a \<noteq> PosReal.pnone \<Longrightarrow> pmult (pinv a) a = PosReal.pwrite" sorry
  show "\<And>a b. pdiv a b = pmult a (pinv b)" sorry
  show "pinv PosReal.pnone = PosReal.pnone" sorry
  show "\<And>a. PosReal.pnone \<le> a" sorry
  show "\<And>p1 p2 q1 q2. p1 \<le> p2 \<and> q1 \<le> q2 \<Longrightarrow> padd p1 q1 \<le> padd p2 q2" sorry
  show "\<And>q p. q \<le> p \<Longrightarrow> \<exists>r. p = padd q r" sorry
  show "\<And>b a. b \<le> a \<and> PosReal.pnone < b \<Longrightarrow> pinv a \<le> pinv b" sorry
  show "PosReal.pwrite < padd PosReal.pwrite PosReal.pwrite" sorry
  show "\<And>a x b y. a = padd x b \<Longrightarrow> a = padd y b \<Longrightarrow> x = y" sorry
qed

end

end