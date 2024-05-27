theory SepAlgebraDef
  imports Main PosRat PosReal PosPerm
begin

section \<open>Partial Commutative Monoid\<close>

class pcm =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option" (infixl "\<oplus>" 63)

  assumes commutative: "a \<oplus> b = b \<oplus> a"
      and asso1: "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
      and asso2: "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
      and positivity: "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
begin

lemma asso3: "a \<oplus> b = None \<and> b \<oplus> c = Some bc \<Longrightarrow> a \<oplus> bc = None"
  by (metis local.asso2 local.commutative)

subsection \<open>Definitions\<close>

definition defined :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "##" 62) where
  "a ## b \<longleftrightarrow> a \<oplus> b \<noteq> None"

definition greater :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<succeq>" 50) where
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = b \<oplus> c)"

definition pure :: "'a \<Rightarrow> bool" where
  "pure a \<longleftrightarrow> Some a = a \<oplus> a"


definition mono_prop :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "mono_prop P \<longleftrightarrow> (\<forall>x y. y \<succeq> x \<and> P x \<longrightarrow> P y)"

definition mono_prop_downward :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "mono_prop_downward P \<longleftrightarrow> (\<forall>x y. y \<succeq> x \<and> P y \<longrightarrow> P x)"

lemma mono_prop_downwardD:
  assumes "mono_prop_downward P" and "P y" and "y \<succeq> x"
  shows "P x"
  using assms
  unfolding mono_prop_downward_def
  by blast

definition max_projection_prop :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "max_projection_prop P f \<longleftrightarrow> (\<forall>x. x \<succeq> f x \<and> P (f x) \<and>
  (\<forall>p. P p \<and> x \<succeq> p \<longrightarrow> f x \<succeq> p))"

inductive multi_plus :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  MPSingle: "multi_plus [a] a"
| MPConcat: "\<lbrakk> length la > 0 ; length lb > 0 ; multi_plus la a ; multi_plus lb b ; Some \<omega> = a \<oplus> b \<rbrakk> \<Longrightarrow> multi_plus (la @ lb)  \<omega>"

fun splus :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "splus None _ = None"
| "splus _ None = None"
| "splus (Some a) (Some b) = a \<oplus> b"


subsection \<open>Lemmas\<close>

lemma defined_comm:
  "a ## b \<longleftrightarrow> b ## a"
  by (simp add: defined_def local.commutative)

lemma greater_equiv:
  "a \<succeq> b \<longleftrightarrow> (\<exists>c. Some a = c \<oplus> b)"
  using commutative greater_def by auto

lemma smaller_compatible:
  assumes "a' ## b"
      and "a' \<succeq> a"
    shows "a ## b"
  by (metis (full_types) assms(1) assms(2) asso3 commutative defined_def greater_def)

lemma bigger_sum_smaller:
  assumes "Some c = a \<oplus> b"
      and "a \<succeq> a'"
    shows "\<exists>b'. b' \<succeq> b \<and> Some c = a' \<oplus> b'"
proof -
  obtain r where "Some a = a' \<oplus> r" 
    using assms(2) greater_def by auto
  then obtain br where "Some br = r \<oplus> b"
    by (metis assms(1) asso2 domD domIff option.discI)
  then have "Some c = a' \<oplus> br" 
    by (metis \<open>Some a = a' \<oplus> r\<close> assms(1) asso1)
  then show ?thesis 
    using \<open>Some br = r \<oplus> b\<close> commutative greater_def by force
qed

subsection \<open>splus\<close>

lemma splus_develop:
  assumes "Some a = b \<oplus> c"
  shows "a \<oplus> d = splus (splus (Some b) (Some c)) (Some d)"
  by (metis assms splus.simps(3))

lemma splus_comm:
  "splus a b = splus b a"
  apply (cases a)
   apply (cases b)
    apply simp_all
  apply (cases b)
  by (simp_all add: commutative)

lemma splus_asso:
  "splus (splus a b) c = splus a (splus b c)"
proof (cases a)
  case None
  then show ?thesis 
    by simp
next
  case (Some a')
  then have "a = Some a'" by simp
  then show ?thesis
  proof (cases b)
    case None
    then show ?thesis by (simp add: Some)
  next
    case (Some b')
    then have "b = Some b'" by simp
    then show ?thesis
    proof (cases c)
      case None
      then show ?thesis by (simp add: splus_comm)
    next
      case (Some c')
      then have "c = Some c'" by simp
      then show ?thesis
      proof (cases "a' \<oplus> b'")
        case None
        then have "a' \<oplus> b' = None" by simp
        then show ?thesis
        proof (cases "b' \<oplus> c'")
          case None
          then show ?thesis 
            by (simp add: Some \<open>a = Some a'\<close> \<open>a' \<oplus> b' = None\<close> \<open>b = Some b'\<close>)
        next
          case (Some bc)
          then show ?thesis
            by (metis (full_types) None \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> asso2 splus.simps(2) splus.simps(3) splus_comm)
        qed
      next
        case (Some ab)
        then have "Some ab = a' \<oplus> b'" by simp
        then show ?thesis
        proof (cases "b' \<oplus> c'")
          case None
          then show ?thesis 
            by (metis Some \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> asso2 splus.simps(2) splus.simps(3))
        next
          case (Some bc)
          then show ?thesis
            by (metis \<open>Some ab = a' \<oplus> b'\<close> \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> asso1 splus.simps(3))
        qed
      qed
    qed
  qed
qed



lemma compatible_smaller:
  assumes "Some x' = a' \<oplus> b"
      and "a' \<succeq> a"
    shows "\<exists>x. Some x = a \<oplus> b \<and> x' \<succeq> x"
proof -
  have "a ## b"
    by (metis assms(1) assms(2) defined_def option.discI smaller_compatible)
  then obtain x where "Some x = a \<oplus> b"
    using defined_def by auto
  then show ?thesis
    by (metis assms(1) assms(2) greater_equiv local.asso1)
qed

subsection \<open>Pure\<close>

(* Maybe need more *)
lemma pure_stable:
  assumes "pure a"
      and "pure b"
      and "Some c = a \<oplus> b"
    shows "pure c"
  by (metis assms(1) assms(2) assms(3) asso1 commutative pure_def)

(* Specific to pure *)
lemma pure_smaller:
  assumes "pure a"
      and "a \<succeq> b"
    shows "pure b"
  by (metis assms(1) assms(2) greater_def positivity pure_def)


subsection \<open>Succ is an order\<close>

lemma succ_trans:
  assumes "a \<succeq> b"
      and "b \<succeq> c"
    shows "a \<succeq> c"
  using assms(1) assms(2) bigger_sum_smaller greater_def by blast


lemma max_projection_propI:
  assumes "\<And>x. x \<succeq> f x"
      and "\<And>x. P (f x)"
      and "\<And>x p. P p \<and> x \<succeq> p \<Longrightarrow> f x \<succeq> p"
    shows "max_projection_prop P f"
  by (simp add: assms(1) assms(2) assms(3) max_projection_prop_def)

lemma max_projection_propE:
  assumes "max_projection_prop P f"
    shows "\<And>x. x \<succeq> f x"
      and "\<And>x. P (f x)"
      and "\<And>x p. P p \<and> x \<succeq> p \<Longrightarrow> f x \<succeq> p"
  using assms max_projection_prop_def by auto


lemma mpp_smaller:
  assumes "max_projection_prop P f"
  shows "x \<succeq> f x"
  using assms max_projection_propE(1) by auto

lemma mpp_compatible:
  assumes "max_projection_prop P f"
      and "a ## b"
    shows "f a ## f b"
  by (metis (mono_tags, opaque_lifting) assms(1) assms(2) commutative defined_def max_projection_prop_def smaller_compatible)

lemma mpp_prop:
  assumes "max_projection_prop P f"
  shows "P (f x)"
  by (simp add: assms max_projection_propE(2))

lemma mpp_mono:
  assumes "max_projection_prop P f"
      and "a \<succeq> b"
    shows "f a \<succeq> f b"
  by (metis assms(1) assms(2) max_projection_prop_def succ_trans)

lemma addition_bigger:
  assumes "a' \<succeq> a"
      and "Some x' = a' \<oplus> b"
      and "Some x = a \<oplus> b"
    shows "x' \<succeq> x"
  by (metis assms(1) assms(2) assms(3) asso1 bigger_sum_smaller greater_def)




lemma mono_propI:
  assumes "\<And>x y. y \<succeq> x \<and> P x \<Longrightarrow> P y"
  shows "mono_prop P"
  using assms mono_prop_def by blast




subsection \<open>multi_plus\<close>

lemma multi_decompose:
  assumes "multi_plus l \<omega>"
    shows "length l \<ge> 2 \<Longrightarrow> (\<exists>a b la lb. l = la @ lb \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b)"
  using assms
  apply (rule multi_plus.cases)
  by auto[2]

lemma multi_take_drop:
  assumes "multi_plus l \<omega>"
      and "length l \<ge> 2"
    shows "\<exists>n a b. n > 0 \<and> n < length l \<and> multi_plus (take n l) a \<and> multi_plus (drop n l) b \<and> Some \<omega> = a \<oplus> b"
proof -
  obtain a b la lb where "l = la @ lb \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b"
    using assms(1) assms(2) multi_decompose by blast
  let ?n = "length la"
  have "la = take ?n l" 
    by (simp add: \<open>l = la @ lb \<and> 0 < length la \<and> 0 < length lb \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b\<close>)
  moreover have "lb = drop ?n l" 
    by (simp add: \<open>l = la @ lb \<and> 0 < length la \<and> 0 < length lb \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b\<close>)
  ultimately show ?thesis 
    by (metis \<open>l = la @ lb \<and> 0 < length la \<and> 0 < length lb \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b\<close> length_drop zero_less_diff)
qed

lemma multi_plus_single:
  assumes "multi_plus [v] a"
  shows "a = v"
  using assms
  apply (cases)
  apply simp
  by (metis (no_types, lifting) Nil_is_append_conv butlast.simps(2) butlast_append length_greater_0_conv)

lemma multi_plus_two:
  assumes "length l \<ge> 2"
  shows "multi_plus l \<omega> \<longleftrightarrow> (\<exists>a b la lb. l = (la @ lb) \<and> length la > 0 \<and> length lb > 0 \<and> multi_plus la a \<and> multi_plus lb b \<and> Some \<omega> = a \<oplus> b)" (is "?A \<longleftrightarrow> ?B")
  by (meson MPConcat assms multi_decompose)

lemma multi_plus_head_tail:
  "length l \<le> n \<and> length l \<ge> 2 \<longrightarrow> (multi_plus l \<omega> \<longleftrightarrow> (\<exists>r. Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r))"
proof (induction n arbitrary: l \<omega>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have IH: "\<And>(l :: 'a list) \<omega>. length l \<le> n \<and> length l \<ge> 2 \<longrightarrow> multi_plus l \<omega> = (\<exists>r. Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r)"
    by blast
  then show ?case
  proof (cases "n = 0")
    case True
    then have "n = 0" by simp
    then show ?thesis by linarith
  next
    case False
    then have "length (l :: 'a list) \<ge> 2 \<and> length l \<le> n + 1 \<Longrightarrow> multi_plus l \<omega> \<longleftrightarrow> (\<exists>r. Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r)" (is "length l \<ge> 2  \<and> length l \<le> n + 1 \<Longrightarrow> ?A \<longleftrightarrow> ?B")
    proof -
      assume asm: "length (l :: 'a list) \<ge> 2 \<and> length l \<le> n + 1"
      have "?B \<Longrightarrow> ?A"
      proof -
        assume "?B"
        then obtain r where "Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r" by blast
        then have "multi_plus [hd l] (hd l)" 
          using MPSingle by blast
        moreover have "[hd l] @ (tl l) = l" 
          by (metis Suc_le_length_iff asm append_Cons list.collapse list.simps(3) numeral_2_eq_2 self_append_conv2)
        ultimately show ?A 
          by (metis (no_types, lifting) MPConcat Suc_1 Suc_le_mono asm \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> append_Nil2 length_Cons length_greater_0_conv list.size(3) not_one_le_zero zero_less_Suc)
      qed
      moreover have "?A \<Longrightarrow> ?B"
      proof -
        assume ?A
        then obtain la lb a b where "l = la @ lb" "length la > 0" "length lb > 0" "multi_plus la a" "multi_plus lb b" "Some \<omega> = a \<oplus> b"
          using asm multi_decompose by blast
        then have "length la \<le> n \<and> length la \<ge> 2 \<longrightarrow> multi_plus la a = (\<exists>r. Some a = hd la \<oplus> r \<and> multi_plus (tl la) r)"
          using IH by blast
        then show ?B
        proof (cases "length la \<ge> 2")
          case True
          then obtain ra where "Some a = (hd la) \<oplus> ra" "multi_plus (tl la) ra"
            by (metis Suc_eq_plus1 \<open>0 < length lb\<close> \<open>l = la @ lb\<close> \<open>length la \<le> n \<and> 2 \<le> length la \<longrightarrow> multi_plus la a = (\<exists>r. Some a = hd la \<oplus> r \<and> multi_plus (tl la) r)\<close> \<open>multi_plus la a\<close> append_eq_conv_conj asm drop_eq_Nil le_add1 le_less_trans length_append length_greater_0_conv less_Suc_eq_le order.not_eq_order_implies_strict)
          moreover obtain rab where "Some rab = ra \<oplus> b"
            by (metis \<open>Some \<omega> = a \<oplus> b\<close> calculation(1) asso2 option.exhaust_sel)
          then have "multi_plus ((tl la) @ lb) rab" 
            by (metis (no_types, lifting) Nil_is_append_conv \<open>multi_plus lb b\<close> calculation(2) length_greater_0_conv list.simps(3) multi_plus.cases MPConcat  )
          moreover have "Some \<omega> = hd la \<oplus> rab" 
            by (metis \<open>Some \<omega> = a \<oplus> b\<close> \<open>Some rab = ra \<oplus> b\<close> asso1 calculation(1))
          ultimately show ?B 
            using \<open>0 < length la\<close> \<open>l = la @ lb\<close> by auto
        next
          case False
          then have "length la = 1" 
            using \<open>0 < length la\<close> by linarith
          then have "la = [a]"
            by (metis Nitpick.size_list_simp(2) One_nat_def Suc_le_length_iff \<open>multi_plus la a\<close> diff_Suc_1 le_numeral_extra(4) length_0_conv list.sel(3) multi_plus_single  )
          then show ?thesis 
            using \<open>Some \<omega> = a \<oplus> b\<close> \<open>l = la @ lb\<close> \<open>multi_plus lb b\<close> by auto
        qed
      qed
      then show ?thesis using calculation by blast
    qed
    then show ?thesis by (metis (no_types, lifting) Suc_eq_plus1)
  qed
qed

lemma not_multi_plus_empty:
  "\<not> multi_plus [] \<omega>"
  by (metis Nil_is_append_conv length_greater_0_conv list.simps(3) multi_plus.simps  )

lemma multi_plus_deter:
  "length l \<le> n \<Longrightarrow> multi_plus l \<omega> \<Longrightarrow> multi_plus l \<omega>' \<Longrightarrow> \<omega> = \<omega>'"
proof (induction n arbitrary: l \<omega> \<omega>')
  case 0
  then show ?case 
    using multi_plus.cases by auto
next
  case (Suc n)
  then show ?case
  proof (cases "length l \<ge> 2")
    case True
    then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r"
      using Suc.prems(2) multi_plus_head_tail by blast
    moreover obtain r' where "Some \<omega>' = (List.hd l) \<oplus> r' \<and> multi_plus (List.tl l) r'"
      using Suc.prems(3) True multi_plus_head_tail by blast
    ultimately have "r = r'" 
      by (metis Suc.IH Suc.prems(1) drop_Suc drop_eq_Nil)
    then show ?thesis 
      by (metis \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> \<open>Some \<omega>' = hd l \<oplus> r' \<and> multi_plus (tl l) r'\<close> option.inject)
  next
    case False
    then have "length l \<le> 1" 
      by simp
    then show ?thesis
    proof (cases "length l = 0")
      case True
      then show ?thesis
        using Suc.prems(2) not_multi_plus_empty   by fastforce
    next
      case False
      then show ?thesis
        by (metis One_nat_def Suc.prems(2) Suc.prems(3) Suc_length_conv \<open>length l \<le> 1\<close> le_SucE le_zero_eq length_greater_0_conv less_numeral_extra(3) multi_plus_single  )
    qed      
  qed
qed

end





section \<open>PCM with core\<close>

class pcm_with_core = pcm +

  fixes core :: "'a \<Rightarrow> 'a" ("|_|")

  assumes core_is_smaller: "Some x = x \<oplus> |x|"
      and core_is_pure: "Some |x| = |x| \<oplus> |x|"
      and core_max: "Some x = x \<oplus> c \<Longrightarrow> (\<exists>r. Some |x| = c \<oplus> r)"
      and core_sum: "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
      and cancellative: "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
begin

definition minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>" 63)
  where "b \<ominus> a = (THE_default b (\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| ))"

lemma succ_antisym:
  assumes "a \<succeq> b"
      and "b \<succeq> a"
    shows "a = b"
proof -
  obtain ra where "Some a = b \<oplus> ra" 
    using assms(1) greater_def by auto
  obtain rb where "Some b = a \<oplus> rb" 
    using assms(2) greater_def by auto
  then have "Some a = splus (Some a) (splus (Some ra) (Some rb))"
  proof -
    have "Some b = splus (Some a) (Some rb)"
      by (simp add: \<open>Some b = a \<oplus> rb\<close>)
    then show ?thesis
      by (metis \<open>Some a = b \<oplus> ra\<close> local.commutative splus.simps(3) splus_asso)
  qed
  moreover have "Some b = splus (Some b) (splus (Some ra) (Some rb))"
    by (metis \<open>Some a = b \<oplus> ra\<close> \<open>Some b = a \<oplus> rb\<close> splus.simps(3)   splus_asso)
  moreover have "pure ra \<and> pure rb"
  proof -
    obtain rab where "Some rab = ra \<oplus> rb" 
      by (metis calculation(2) splus.elims splus.simps(3))
    then have "|a| \<succeq> rab" 
      by (metis calculation(1) core_max greater_def splus.simps(3))
    then have "pure rab" 
      using core_is_pure pure_def pure_smaller by blast
    moreover have "rab \<succeq> ra \<and> rab \<succeq> rb" 
      using \<open>Some rab = ra \<oplus> rb\<close> greater_def greater_equiv by blast
    ultimately have "pure ra" using pure_smaller 
      by blast
    moreover have "pure rb" 
      using \<open>pure rab\<close> \<open>rab \<succeq> ra \<and> rab \<succeq> rb\<close> pure_smaller by blast
    ultimately show ?thesis 
      by blast
  qed
  ultimately show ?thesis 
    by (metis \<open>Some b = a \<oplus> rb\<close> option.inject pure_def splus.simps(3)   splus_asso)
qed

lemma succ_refl:
  "a \<succeq> a"
  using core_is_smaller greater_def by blast


lemma max_projection_prop_pure_core:
  "max_projection_prop pure core"
proof (rule max_projection_propI)
  fix x
  show "x \<succeq> |x|" 
    using core_is_smaller greater_equiv by blast
  show "pure |x|" 
    by (simp add: core_is_pure pure_def)
  show "\<And>p. pure p \<and> x \<succeq> p \<Longrightarrow> |x| \<succeq> p"
  proof -
    fix p assume "pure p \<and> x \<succeq> p"
    then obtain r where "Some x = p \<oplus> r" 
      using greater_def by blast
    then show "|x| \<succeq> p"
      by (metis \<open>pure p \<and> x \<succeq> p\<close> asso1 commutative core_max greater_equiv pure_def)
  qed
qed


lemma multi_plus_implies_multi_plus_of_drop:
  assumes "multi_plus l \<omega>"
      and "n < length l"
    shows "\<exists>a. multi_plus (drop n l) a \<and> \<omega> \<succeq> a"
  using assms
proof (induction n arbitrary: l \<omega>)
  case 0
  then show ?case
    using succ_refl by fastforce
next
  case (Suc n)
  then have "length l \<ge> 2" 
    by linarith
  then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r" 
    using Suc.prems(1) multi_plus_head_tail by blast
  then obtain a where "multi_plus (drop n (List.tl l)) a \<and> r \<succeq> a" 
    using Suc.IH Suc.prems(2) by fastforce
  then show ?case 
    by (metis \<open>Some \<omega> = hd l \<oplus> r \<and> multi_plus (tl l) r\<close> bigger_sum_smaller commutative drop_Suc greater_def)
qed

lemma multi_plus_bigger_than_head:
  assumes "length l > 0"
      and "multi_plus l \<omega>"
    shows "\<omega> \<succeq> List.hd l"
proof (cases "length l \<ge> 2")
  case True
  then obtain r where "Some \<omega> = (List.hd l) \<oplus> r \<and> multi_plus (List.tl l) r" 
    using assms(1) assms(2) multi_plus_head_tail by blast
  then show ?thesis 
    using greater_def by blast
next
  case False
  then show ?thesis
    by (metis Cons_nth_drop_Suc MPSingle assms(1) assms(2) drop_0 drop_eq_Nil hd_conv_nth length_greater_0_conv not_less_eq_eq numeral_2_eq_2 multi_plus_deter succ_refl)
qed

lemma multi_plus_bigger:
  assumes "i < length l"
      and "multi_plus l \<omega>"
    shows "\<omega> \<succeq> (l ! i)"
proof -
  obtain a where "multi_plus (drop i l) a \<and> \<omega> \<succeq> a"
    using assms(1) assms(2) multi_plus_implies_multi_plus_of_drop order.strict_trans by blast
  moreover have "List.hd (drop i l) = l ! i" 
    by (simp add: assms(1) hd_drop_conv_nth)
  then show ?thesis
    by (metis (no_types, lifting) succ_trans assms(1) assms(2) drop_eq_Nil leD length_greater_0_conv multi_plus_bigger_than_head multi_plus_implies_multi_plus_of_drop)
qed

lemma mppI:
  assumes "max_projection_prop P f"
      and "a \<succeq> x"
      and "P x"
      and "x \<succeq> f a"
    shows "x = f a"
proof -
  have "f a \<succeq> x" 
    using assms(1) assms(2) assms(3) max_projection_propE(3) by auto
  then show ?thesis
    by (simp add: assms(4) succ_antisym)
qed

lemma mpp_invo:
  assumes "max_projection_prop P f"
  shows "f (f x) = f x"
  using assms max_projection_prop_def succ_antisym by auto


subsection \<open>Subtraction\<close>


lemma smaller_than_core:
  assumes "y \<succeq> x"
      and "Some z = x \<oplus> |y|"
    shows "|z| = |y|"
proof -
  have "Some |z| = |x| \<oplus> |y|"
    using assms(2) core_sum max_projection_prop_pure_core mpp_invo by fastforce
  then have "Some |z| = |x| \<oplus> |y|"
    by simp
  moreover have "|z| \<succeq> |y|" 
    using calculation greater_equiv by blast
  ultimately show ?thesis 
    by (meson addition_bigger assms(1) assms(2) core_is_smaller core_sum greater_def succ_antisym)
qed

lemma minus_unique:
  assumes "Some b = a \<oplus> x \<and> x \<succeq> |b|"
      and "Some b = a \<oplus> y \<and> y \<succeq> |b|"
    shows "x = y"
proof -
  have "|x| = |b|"
    by (metis assms(1) local.commutative local.greater_equiv local.succ_trans smaller_than_core)
  moreover have "|y| = |b|"
    by (meson assms(2) local.greater_def local.greater_equiv local.succ_trans smaller_than_core)
  ultimately show ?thesis
    using assms(1) assms(2) cancellative by auto
qed

lemma minus_exists:
  assumes "b \<succeq> a"
  shows "\<exists>x. Some b = a \<oplus> x \<and> x \<succeq> |b|"
  using assms bigger_sum_smaller core_is_smaller by blast

lemma minus_equiv_def:
  assumes "b \<succeq> a"
    shows "Some b = a \<oplus> (b \<ominus> a) \<and> (b \<ominus> a) \<succeq> |b|"
proof -
  let ?x = "THE_default b (\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| )"
  have "(\<lambda>x. Some b = a \<oplus> x \<and> x \<succeq> |b| ) ?x"
  proof (rule THE_defaultI')
    show "\<exists>!x. Some b = a \<oplus> x \<and> x \<succeq> |b|"
      using assms local.minus_unique minus_exists by blast
  qed
  then show ?thesis by (metis minus_def)
qed

lemma minus_default:
  assumes "\<not> b \<succeq> a"
  shows "b \<ominus> a = b"
  using THE_default_none assms greater_def minus_def by fastforce

lemma minusI:
  assumes "Some b = a \<oplus> x"
      and "x \<succeq> |b|"
    shows "x = b \<ominus> a"  
  using assms(1) assms(2) greater_def local.minus_unique minus_equiv_def by blast

lemma minus_core:
  "|a \<ominus> b| = |a|"
proof (cases "a \<succeq> b")
  case True
  then have "Some a = b \<oplus> (a \<ominus> b) \<and> a \<ominus> b \<succeq> |a|"
    using minus_equiv_def by auto
  then show ?thesis 
    by (meson local.greater_def local.greater_equiv local.succ_trans smaller_than_core)
next
  case False
  then show ?thesis by (simp add: minus_default)
qed

lemma minus_core_weaker:
  "|a \<ominus> b| = |a| \<ominus> |b|"
proof (cases "a \<succeq> b")
  case True
  then show ?thesis 
    by (metis greater_equiv max_projection_prop_pure_core minus_core minus_default minus_equiv_def mpp_invo succ_antisym)
next
  case False
  then show ?thesis
    by (metis greater_equiv max_projection_prop_pure_core minus_default minus_equiv_def mpp_invo succ_antisym)
qed

lemma minus_equiv_def_any_elem:
  assumes "Some x = a \<oplus> b"
  shows "Some (x \<ominus> a) = b \<oplus> |x|"
proof -
  obtain r where "Some r = b \<oplus> |x|" 
    by (metis assms core_is_smaller domD domIff option.simps(3) asso2  )
  have "r = x \<ominus> a"
  proof (rule minusI)
    show "Some x = a \<oplus> r" 
      by (metis \<open>Some r = b \<oplus> |x|\<close> assms asso1 core_is_smaller)
    moreover show "r \<succeq> |x|"
      using \<open>Some r = b \<oplus> |x|\<close> greater_equiv by blast
  qed
  then show ?thesis 
    using \<open>Some r = b \<oplus> |x|\<close> by blast
qed

lemma minus_bigger:
  assumes "Some x = a \<oplus> b"
  shows "x \<ominus> a \<succeq> b"
  using assms greater_def minus_equiv_def_any_elem by blast

lemma minus_smaller:
  assumes "x \<succeq> a"
  shows "x \<succeq> x \<ominus> a"
  using assms greater_equiv minus_equiv_def by blast

lemma minus_sum:
  assumes "Some a = b \<oplus> c"
      and "x \<succeq> a"
    shows "x \<ominus> a = (x \<ominus> b) \<ominus> c"
proof (rule minusI)
  obtain r where "Some r = c \<oplus> (x \<ominus> a)"
    by (metis assms(1) assms(2) asso2 minus_equiv_def option.exhaust_sel)
  have "r = (x \<ominus> b)"
  proof (rule minusI)
    show "Some x = b \<oplus> r" 
      by (metis \<open>Some r = c \<oplus> (x \<ominus> a)\<close> assms(1) assms(2) asso1 minus_equiv_def)
    moreover show "r \<succeq> |x|" 
      by (meson \<open>Some r = c \<oplus> (x \<ominus> a)\<close> assms(2) greater_equiv minus_equiv_def   succ_trans)
  qed
  then show "Some (x \<ominus> b) = c \<oplus> (x \<ominus> a)" 
    using \<open>Some r = c \<oplus> (x \<ominus> a)\<close> by blast
  moreover show "x \<ominus> a \<succeq> |x \<ominus> b|"
    by (simp add: assms(2) minus_core minus_equiv_def)
qed

lemma smaller_compatible_core:
  assumes "y \<succeq> x"
  shows "x ## |y|"
  by (metis assms asso2 core_is_smaller defined_def greater_equiv option.discI)

lemma smaller_pure_sum_smaller:
  assumes "y \<succeq> a"
      and "y \<succeq> b"
      and "Some x = a \<oplus> b"
      and "pure b"
    shows "y \<succeq> x"
proof -
  have "Some y = y \<oplus> b"
    by (metis assms(2) assms(4) local.asso1 local.greater_equiv local.pure_def)
  then show ?thesis
    using assms(1) assms(3) local.addition_bigger by blast
qed





lemma greater_minus_trans:
  assumes "y \<succeq> x"
      and "x \<succeq> a"
    shows "y \<ominus> a \<succeq> x \<ominus> a"
proof -
  obtain r where "Some y = x \<oplus> r" 
    using assms(1) greater_def by blast
  then obtain ra where "Some x = a \<oplus> ra" 
    using assms(2) greater_def by blast
  then have "Some (x \<ominus> a) = ra \<oplus> |x|"
    by (simp add: minus_equiv_def_any_elem)
  then obtain yy where "Some yy = (x \<ominus> a) \<oplus> r" 
    by (metis (full_types) \<open>Some y = x \<oplus> r\<close> assms(2) asso3 commutative minus_equiv_def not_Some_eq)
  moreover obtain y' where "Some y' = yy \<oplus> a"
    using \<open>Some y = x \<oplus> r\<close> assms(2) calculation local.asso1[of r] local.commutative minus_equiv_def[of x a] by metis
  moreover have "y \<succeq> y'"
    using \<open>Some y = x \<oplus> r\<close> assms(2) asso1 calculation(1) calculation(2) commutative[of a yy] minus_equiv_def[of x a]
      option.sel succ_refl[of y] by metis
  moreover obtain x' where "Some x' = (x \<ominus> a) \<oplus> a" 
    using assms(2) commutative minus_equiv_def by fastforce
  then have "y \<succeq> x'" 
    by (metis assms(1) assms(2) commutative minus_equiv_def option.sel)
  moreover have "x' \<succeq> x \<ominus> a" 
    using \<open>Some x' = x \<ominus> a \<oplus> a\<close> greater_def by auto
  ultimately show ?thesis 
    using \<open>Some x' = x \<ominus> a \<oplus> a\<close> \<open>Some y = x \<oplus> r\<close> assms(2) asso1 commutative greater_equiv minus_bigger minus_equiv_def option.sel succ_trans  
  proof -
    have f1: "Some y' = a \<oplus> yy"
      by (simp add: \<open>Some y' = yy \<oplus> a\<close> commutative)
    then have "y = y'"
      by (metis \<open>Some y = x \<oplus> r\<close> \<open>Some yy = x \<ominus> a \<oplus> r\<close> \<open>x \<succeq> a\<close> asso1 minus_equiv_def option.sel)
    then show ?thesis
      using f1 by (metis (no_types) \<open>Some yy = x \<ominus> a \<oplus> r\<close> commutative greater_equiv minus_bigger succ_trans  )
  qed
qed

lemma minus_and_plus:
  assumes "Some \<omega>' = \<omega> \<oplus> r"
      and "\<omega> \<succeq> a"
    shows "Some (\<omega>' \<ominus> a) = (\<omega> \<ominus> a) \<oplus> r"
proof -
  have "\<omega> \<succeq> \<omega> \<ominus> a" 
    by (simp add: assms(2) minus_smaller)
  then have "(\<omega> \<ominus> a) ## r" 
    by (metis (full_types) assms(1) defined_def option.discI smaller_compatible  )
  then obtain x where "Some x = (\<omega> \<ominus> a) \<oplus> r"
    using defined_def by auto
  then have "Some \<omega>' = a \<oplus> x \<and> x \<succeq> |\<omega>'|"
    by (metis (no_types, lifting) assms(1) assms(2) asso1 core_sum max_projection_prop_pure_core minus_core minus_equiv_def mpp_smaller option.inject)
  then have "x = \<omega>' \<ominus> a" 
    by (simp add: minusI)
  then show ?thesis 
    using \<open>Some x = \<omega> \<ominus> a \<oplus> r\<close> by blast
qed

lemma plus_minus_empty:
  assumes "|a| = |b|"
  shows "a \<oplus> (b \<ominus> b) = Some a"
  using assms
  by (metis core_is_smaller minusI succ_refl)

lemma minus_greater:
  assumes "\<omega> \<succeq> \<omega>2" and "\<omega>2 \<succeq> \<omega>1"
  shows "\<omega> \<ominus> \<omega>1 \<succeq> \<omega> \<ominus> \<omega>2"
proof -
  from assms have "\<omega> \<succeq> \<omega>1"
    using succ_trans 
    by blast

  from minus_exists[OF \<open>\<omega> \<succeq> \<omega>1\<close>] obtain \<omega>1_diff where 
    "Some \<omega> = \<omega>1 \<oplus> \<omega>1_diff" and
    "\<omega>1_diff \<succeq> |\<omega>|"
    by blast

  hence "\<omega>1_diff = \<omega> \<ominus> \<omega>1"
    using minusI
    by blast

  from minus_exists[OF \<open>\<omega> \<succeq> \<omega>2\<close>] obtain \<omega>2_diff where 
    "Some \<omega> = \<omega>2 \<oplus> \<omega>2_diff" and
    "\<omega>2_diff \<succeq> |\<omega>|"
    by blast

  hence "\<omega>2_diff = \<omega> \<ominus> \<omega>2"
    using minusI
    by blast

  have "\<omega>1_diff \<succeq> \<omega>2_diff"
    unfolding greater_def
    using \<open>Some \<omega> = \<omega>2 \<oplus> \<omega>2_diff\<close> \<open>\<omega>1_diff = \<omega> \<ominus> \<omega>1\<close> \<open>\<omega>2 \<succeq> \<omega>1\<close> commutative minus_and_plus by fastforce
    
  thus ?thesis
    by (simp add: \<open>\<omega>1_diff = _\<close> \<open>\<omega>2_diff = _\<close>)
qed

end






section \<open>PCM with multiplication\<close>

text \<open>Axioms from the paper\<close>

(* Isabelle limits typeclasses to one type parameter maximum, so we specialize it with preal *)

class pcm_mult = pcm +
  fixes mult :: "preal \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 64)
  assumes unit_mult: "1 \<odot> x = x"
      and mult_mult: "\<alpha> \<odot> (\<beta> \<odot> x) = (\<alpha> * \<beta>) \<odot> x"
      and distrib_state_mult: "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = (\<alpha> \<odot> a) \<oplus> (\<alpha> \<odot> b)"
      and distrib_scala_mult: "Some ((\<alpha> + \<beta>) \<odot> x) = (\<alpha> \<odot> x) \<oplus> (\<beta> \<odot> x)"
begin

lemma larger_state_mult:
  assumes "\<alpha> > (1 :: preal)"
  shows "\<alpha> \<odot> x \<succeq> x"
proof -
  obtain r where "\<alpha> = 1 + r" "r > 0"
    using assms decompose_larger_than_one by blast
  then show ?thesis
    using local.distrib_scala_mult local.greater_def local.unit_mult by auto
qed

lemma smaller_state_mult:
  assumes "\<alpha> < (1 :: preal)"
  shows "x \<succeq> \<alpha> \<odot> x"
proof -
  obtain r where "1 = \<alpha> + r" "r > 0"
    using assms decompose_smaller_than_one by blast
  then show ?thesis
    by (metis local.distrib_scala_mult local.greater_def local.unit_mult)
qed

end




section \<open>Separation algebra\<close>

class sep_algebra = pcm_with_core +

  fixes stable :: "'a \<Rightarrow> bool"
  fixes stabilize :: "'a \<Rightarrow> 'a"

  assumes already_stable: "stable x \<Longrightarrow> stabilize x = x"
    and stabilize_is_stable[simp]: "stable (stabilize x)"
    and stabilize_sum: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    and decompose_stabilize_pure: "Some x = stabilize x \<oplus> |x|"
    and stabilize_core_emp : "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b"


(*
  fixes u :: 'a

  fixes stable_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes stabilize_rel :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes stabilize_rel_sum_pure: "Some x = stabilize_rel a x \<oplus> |x|"
      and stabilize_rel_mono_left: "a \<succeq> b \<Longrightarrow> stabilize_rel a x \<succeq> stabilize_rel b x"
      and stabilize_rel_all_sum: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize_rel y x) = stabilize_rel y a \<oplus> stabilize_rel y b"
      and stabilize_rel_is_stable_rel: "stable_rel a (stabilize_rel a x)"
      and already_stable_rel: "stable_rel a x \<Longrightarrow> stabilize_rel a x = x"
      and stabilize_rel_sum_double: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize_rel u x) = stabilize_rel u a \<oplus> stabilize_rel a b"
(* TODO: Think about this one *)
      and u_neutral: "Some x = x \<oplus> u"
*)

begin

definition stable_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "stable_rel a b = (\<forall>c. a \<oplus> b = Some c \<longrightarrow> stable c)"

lemma stabilize_mono: "x \<succeq> a \<Longrightarrow> stabilize x \<succeq> stabilize a"
  using local.greater_equiv local.stabilize_sum by blast

(*
lemma stabilize_rel:
  assumes "Some x = a \<oplus> b"
  shows "stable_rel a b \<Longrightarrow> stable x" unfolding stable_def sorry


lemma stabilize_rel_order:
  "stabilize_rel a x \<succeq> stabilize x"
  by (metis local.greater_equiv local.stabilize_rel_mono_left local.u_neutral stabilize_def)

lemma stabilize_rel_mono_right:
  "x \<succeq> a \<Longrightarrow> stabilize_rel b x \<succeq> stabilize_rel b a"
  using local.greater_def local.stabilize_rel_all_sum by blast


lemma stabilize_rel_sum: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize_rel a b"
  by (simp add: local.stabilize_rel_sum_double stabilize_def)

lemma max_projection_prop_stable_rel_stabilize_rel:
  "max_projection_prop (stable_rel x) (stabilize_rel x)"
  apply (rule max_projection_propI)
  using local.greater_def local.stabilize_rel_sum_pure apply blast
  apply (simp add: local.stabilize_rel_is_stable_rel)
  by (metis local.already_stable_rel stabilize_rel_mono_right)
*)

lemma max_projection_prop_stable_stabilize:
  "max_projection_prop stable stabilize"
  by (metis local.already_stable local.commutative local.decompose_stabilize_pure local.greater_equiv local.max_projection_propI local.stabilize_is_stable stabilize_mono)

lemma core_stabilize_mono:
  assumes "a \<succeq> b"
    shows "core a \<succeq> core b"
      and "stabilize a \<succeq> stabilize b"
  using assms max_projection_prop_pure_core mpp_mono apply blast  
  using assms max_projection_prop_stable_stabilize mpp_mono by blast


lemma stable_sum:
  assumes "stable a"
      and "stable b"
      and "Some x = a \<oplus> b"
    shows "stable x"
  by (metis already_stable assms(1) assms(2) assms(3) option.sel stabilize_is_stable stabilize_sum)

(* Should hold in practice, maybe more axioms? *)
(*
lemma stability_cancellative:
  assumes "stable a"
      and "stable b"
      and "Some x = a \<oplus> r"
      and "Some x = b \<oplus> r"
    shows "a = b"
proof (rule cancellative)
  show "Some x = r \<oplus> a"
    by (simp add: assms(3) local.commutative)
  show "Some x = r \<oplus> b"
    by (simp add: assms(4) local.commutative)
  show "|a| = |b|"
    sorry

(*      and cancellative: "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
*)
qed
*)

(*
lemma stabilize_rel_invo:
  "stabilize_rel x (stabilize_rel x a) = stabilize_rel x a"
  using local.already_stable_rel local.stabilize_rel_is_stable_rel by blast
*)

definition pure_larger where
  "pure_larger a b \<longleftrightarrow> (\<exists>r. pure r \<and> Some a = b \<oplus> r)"

lemma pure_larger_trans:
  assumes "pure_larger a b"
      and "pure_larger b c"
    shows "pure_larger a c"
proof -
  obtain r1 where "Some a = b \<oplus> r1" "pure r1"
    using assms(1) pure_larger_def by blast
  moreover obtain r2 where "Some b = c \<oplus> r2" "pure r2"
    using assms(2) pure_larger_def by blast
  moreover obtain r where "Some r = r1 \<oplus> r2"
    by (metis calculation(1) calculation(3) local.asso3 local.commutative not_Some_eq)
  ultimately show ?thesis
    by (metis local.asso1 local.commutative local.pure_stable pure_larger_def)
qed

lemma pure_larger_stabilize_same:
  assumes "pure_larger a b"
  shows "stabilize a = stabilize b"
  by (metis assms local.max_projection_prop_pure_core local.mppI local.mpp_smaller local.stabilize_core_emp local.stabilize_sum local.succ_refl pure_larger_def)

lemma pure_larger_sum:
  assumes "Some x = a \<oplus> b"
      and "pure_larger x' x"
    shows "\<exists>a'. pure_larger a' a \<and> Some x' = a' \<oplus> b"
proof -
  obtain p where "Some x' = x \<oplus> p" "pure p"
    using assms(2) pure_larger_def by auto
  then obtain a' where "Some a' = a \<oplus> p"
    by (metis assms(1) domD domIff local.asso2 local.commutative)
  then have "Some x' = a' \<oplus> b"
    by (metis \<open>Some x' = x \<oplus> p\<close> assms(1) local.asso1 local.commutative)
  then show ?thesis
    using \<open>Some a' = a \<oplus> p\<close> \<open>pure p\<close> pure_larger_def by blast
qed

(*
lemma pure_larger_stabilize:
  "pure_larger x (stabilize_rel y x)"
  using local.core_is_pure local.pure_def local.stabilize_rel_sum_pure pure_larger_def by blast
*)

lemma stabilize_sum_of_stable:
  assumes "stable x"
      and "Some x = a \<oplus> b"
    shows "Some x = stabilize a \<oplus> stabilize b"
  using already_stable assms(1) assms(2) stabilize_sum by fastforce

lemma stabilize_sum_result_stable:
  assumes "Some x = a \<oplus> b"
      and "stable x"
    shows "Some x = stabilize a \<oplus> b"
proof -
  have "Some x = stabilize a \<oplus> stabilize b"
    using assms(1) assms(2) stabilize_sum_of_stable by blast
  moreover have "Some x = x \<oplus> |b|"
    by (metis assms(1) local.asso1 local.core_is_smaller)
  moreover have "Some b = stabilize b \<oplus> |b|"
    by (simp add: decompose_stabilize_pure)
  ultimately show ?thesis
    by (metis local.asso1)
qed
(*
lemma neutral_smallest:
  "\<omega> \<succeq> u"
  using greater_equiv u_neutral by blast

lemma pure_larger_stabilize_rel:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "pure_larger (stabilize_rel \<omega>' x) (stabilize_rel \<omega> x)"
proof -
  have "stabilize_rel \<omega>' x \<succeq> stabilize_rel \<omega> x"
    by (simp add: assms local.stabilize_rel_mono_left)
  moreover have "Some x = stabilize_rel \<omega>' x \<oplus> |x|"
    by (simp add: local.stabilize_rel_sum_pure)
  moreover have "Some x = stabilize_rel \<omega> x \<oplus> |x|"
    by (simp add: local.stabilize_rel_sum_pure)
  ultimately have "Some (stabilize_rel \<omega>' x) = stabilize_rel \<omega> x \<oplus> |stabilize_rel \<omega>' x|"
    sorry
  show ?thesis sorry
qed
*)

lemma obtain_pure_remainder:
  assumes "a \<succeq> b"
  shows "\<exists>r. Some a = r \<oplus> b \<and> |r| = |a|"
  using assms local.commutative local.minus_core local.minus_equiv_def by auto
(*
(* TODO EXPLORE more *)
definition is_minimum_sat where
  "is_minimum_sat P \<omega> \<longleftrightarrow> P \<omega> \<and> (\<forall>\<omega>' x. \<omega>' \<succeq> \<omega> \<and> \<omega>' \<succeq> x \<and> P x \<longrightarrow> x \<succeq> \<omega>)"

lemma is_minimum_satI:
  assumes "A \<omega>"
      and "\<And>x. \<omega>' \<succeq> x \<and> A x \<Longrightarrow> x \<succeq> \<omega>"
    shows "is_minimum_sat A \<omega>' \<omega>"
  using assms(1) assms(2) is_minimum_sat_def by blast

lemma is_minimum_satE:
  assumes "is_minimum_sat A \<omega>' \<omega>"
      and "A x"
      and "\<omega>' \<succeq> x"
    shows "x \<succeq> \<omega>"
  by (metis assms is_minimum_sat_def)
*)

lemma plus_pure_stabilize_eq :
  "Some a = b \<oplus> |c| \<Longrightarrow> stabilize a = stabilize b"
  using stabilize_core_emp stabilize_sum by blast


lemma stable_and_sum_pure_same:
  assumes "Some x = a \<oplus> p"
      and "stable x"
      and "pure p"
    shows "x = a"
proof -
  have "|x| \<succeq> p"
    using assms(1) assms(3) greater_equiv max_projection_propE(3) max_projection_prop_pure_core by blast
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) local.already_stable local.greater_def local.max_projection_prop_def local.succ_antisym max_projection_prop_stable_stabilize pure_larger_def pure_larger_stabilize_same)
qed

lemma pure_large_stable_same:
  assumes "pure_larger x a"
      and "stable x"
    shows "x = a"
  using assms(1) assms(2) pure_larger_def stable_and_sum_pure_same by blast

lemma stabilize_core_right_id :
  "Some a = a \<oplus> stabilize |a|"
  by (metis local.asso1 local.commutative local.core_is_smaller local.decompose_stabilize_pure)



subsection \<open>Expressions\<close>

definition wf_exp where
  "wf_exp e \<longleftrightarrow> (\<forall>a b v. a \<succeq> b \<and> e b = Some v \<longrightarrow> e a = Some v) \<and> (\<forall>a. e a = e |a| )"

lemma wf_expI:
  assumes "\<And>a. e a = e |a|"
      and "\<And>a b v. a \<succeq> b \<and> e b = Some v \<Longrightarrow> e a = Some v"
    shows "wf_exp e"
  using assms(1) assms(2) wf_exp_def by blast

lemma wf_expE:
  assumes "wf_exp e"
      and "a \<succeq> b"
      and "e b = Some v"
    shows "e a = Some v"
  by (meson assms(1) assms(2) assms(3) wf_exp_def)

lemma wf_exp_coreE:
  assumes "wf_exp e"
  shows "e a = e |a|"
  by (meson assms wf_exp_def)

definition negate where
  "negate b \<omega> = (if b \<omega> = None then None else Some (\<not> (the (b \<omega>))))"

lemma wf_exp_negate:
  assumes "wf_exp b"
  shows "wf_exp (negate b)"
  by (smt (verit, del_insts) assms negate_def option.collapse wf_exp_def)

lemma wf_exp_stabilize:
  assumes "e (stabilize \<omega>) = Some v"
      and "wf_exp e"
    shows "e \<omega> = Some v"
  by (meson assms(1) assms(2) decompose_stabilize_pure greater_def wf_exp_def)

lemma pure_larger_stabilize:
  "pure_larger \<omega> (stabilize \<omega>)"
  by (metis decompose_stabilize_pure max_projection_prop_def max_projection_prop_pure_core pure_larger_def)

lemma wf_exp_combinedE:
  assumes "wf_exp e"
      and "e \<omega> = Some v"
      and "|\<omega>'| \<succeq> |\<omega>|"
    shows "e \<omega>' = Some v"
  using assms(1) assms(2) assms(3) wf_expE wf_exp_coreE by fastforce


end


end