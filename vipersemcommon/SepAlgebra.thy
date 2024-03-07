theory SepAlgebra
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



                                                         
definition add_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<otimes>" 60) where
  "A \<otimes> B = { \<phi> | \<phi> a b. a \<in> A \<and> b \<in> B \<and> Some \<phi> = a \<oplus> b }"

definition greater_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<ggreater>" 50) where
  "A \<ggreater> B \<longleftrightarrow> (\<forall>a \<in> A. \<exists>b \<in> B. a \<succeq> b)"

definition up_closed :: "'a set \<Rightarrow> bool" where
  "up_closed A \<longleftrightarrow> (\<forall>\<phi>'. (\<exists>\<phi> \<in> A. \<phi>' \<succeq> \<phi>) \<longrightarrow> \<phi>' \<in> A)"

definition equiv :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<sim>" 40) where
  "A \<sim> B \<longleftrightarrow> A \<ggreater> B \<and> B \<ggreater> A"

definition setify :: "('a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool)" where
  "setify P A \<longleftrightarrow> (\<forall>x \<in> A. P x)"

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

definition under :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "under A \<omega> = { \<omega>' | \<omega>'. \<omega>' \<in> A \<and> \<omega> \<succeq> \<omega>'}"

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



subsection \<open>Lifting to sets\<close>

lemma add_set_commm:
  "A \<otimes> B = B \<otimes> A"
proof -
  have "\<And>A B. A \<otimes> B \<subseteq> B \<otimes> A"
    using add_set_def local.commutative by fastforce
  then show ?thesis by blast
qed

lemma x_elem_set_product:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = a \<oplus> b)"
  using add_set_def   by fastforce

lemma x_elem_set_product_splus:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = splus (Some a) (Some b))"
  using add_set_def   by fastforce

lemma add_set_asso:
  "(A \<otimes> B) \<otimes> C = A \<otimes> (B \<otimes> C)" (is "?A = ?B")
proof -
  have "?A \<subseteq> ?B"
  proof (rule subsetI)
    fix x assume "x \<in> ?A"
    then obtain ab c where "Some x = ab \<oplus> c" "ab \<in> A \<otimes> B" "c \<in> C"
      using x_elem_set_product by auto
    then obtain a b where "Some ab = a \<oplus> b" "a \<in> A" "b \<in> B"
      using x_elem_set_product by auto
    then obtain bc where "Some bc = b \<oplus> c" 
      by (metis \<open>Some x = ab \<oplus> c\<close> asso2 option.exhaust)
    then show "x \<in> ?B" 
      by (metis \<open>Some ab = a \<oplus> b\<close> \<open>Some x = ab \<oplus> c\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close> asso1 x_elem_set_product)
  qed
  moreover have "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix x assume "x \<in> ?B"
    then obtain a bc where "Some x = a \<oplus> bc" "a \<in> A" "bc \<in> B \<otimes> C"
      using x_elem_set_product by auto
    then obtain b c where "Some bc = b \<oplus> c" "c \<in> C" "b \<in> B"
      using x_elem_set_product by auto
    then obtain ab where "Some ab = a \<oplus> b"
      by (metis \<open>Some x = a \<oplus> bc\<close> asso3 option.collapse)
    then show "x \<in> ?A"
      by (metis \<open>Some bc = b \<oplus> c\<close> \<open>Some x = a \<oplus> bc\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>c \<in> C\<close> asso1 x_elem_set_product)
  qed
  ultimately show ?thesis by blast
qed

lemma up_closedI:
  assumes "\<And>\<phi>' \<phi>. (\<phi>' :: 'a) \<succeq> \<phi> \<and> \<phi> \<in> A \<Longrightarrow> \<phi>' \<in> A"
  shows "up_closed A"
  using assms up_closed_def by blast

lemma up_closed_plus_UNIV:
  "up_closed (A \<otimes> UNIV)"
proof (rule up_closedI)
  fix \<phi> \<phi>'
  assume asm: "\<phi>' \<succeq> \<phi> \<and> \<phi> \<in> A \<otimes> UNIV"
  then obtain r a b where "Some \<phi>' = \<phi> \<oplus> r" "Some \<phi> = a \<oplus> b" "a \<in> A"
    using greater_def x_elem_set_product by auto
  then obtain br where "Some br = b \<oplus> r" 
    by (metis asso2 option.exhaust_sel)
  then have "Some \<phi>' = a \<oplus> br" 
    by (metis \<open>Some \<phi> = a \<oplus> b\<close> \<open>Some \<phi>' = \<phi> \<oplus> r\<close> splus.simps(3) splus_asso)
  then show "\<phi>' \<in> A \<otimes> UNIV" 
    using \<open>a \<in> A\<close> x_elem_set_product by auto
qed

(*
lemma up_closed_up_mult_set:
  "up_closed (up_mult_set \<alpha> A)"
  by (simp add: up_closed_plus_UNIV up_mult_set_def)
*)

lemma succ_set_trans:
  assumes "A \<ggreater> B"
      and "B \<ggreater> C"
    shows "A \<ggreater> C"
  by (meson assms(1) assms(2) greater_set_def succ_trans)

lemma greater_setI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<succeq> b)"
    shows "A \<ggreater> B"
  by (simp add: assms greater_set_def)  

lemma bigger_set:
  assumes "A' \<ggreater> A"
  shows "A' \<otimes> B \<ggreater> A \<otimes> B"
proof (rule greater_setI)
  fix x assume "x \<in> A' \<otimes> B"
  then obtain a' b where "Some x = a' \<oplus> b" "a' \<in> A'" "b \<in> B"
    using x_elem_set_product by auto
  then obtain a where "a' \<succeq> a" "a \<in> A"
    using assms greater_set_def by blast
  then obtain ab where "Some ab = a \<oplus> b"
    by (metis \<open>Some x = a' \<oplus> b\<close> asso2 domD domIff greater_equiv)
  then show "\<exists>ab\<in>A \<otimes> B. x \<succeq> ab"
    using \<open>Some x = a' \<oplus> b\<close> \<open>a \<in> A\<close> \<open>a' \<succeq> a\<close> \<open>b \<in> B\<close> addition_bigger x_elem_set_product by blast
qed

lemma bigger_singleton:
  assumes "\<phi>' \<succeq> \<phi>"
  shows "{\<phi>'} \<ggreater> {\<phi>}"
  by (simp add: assms greater_set_def)

lemma add_set_elem:
  "\<phi> \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. Some \<phi> = a \<oplus> b \<and> a \<in> A \<and> b \<in> B)"
  using add_set_def by auto

lemma up_closed_sum:
  assumes "up_closed A"
    shows "up_closed (A \<otimes> B)"
proof (rule up_closedI)
  fix \<phi>' \<phi> assume asm: "\<phi>' \<succeq> \<phi> \<and> \<phi> \<in> A \<otimes> B"
  then obtain a b where "a \<in> A" "b \<in> B" "Some \<phi> = a \<oplus> b" 
    using add_set_elem by auto
  moreover obtain r where "Some \<phi>' = \<phi> \<oplus> r" 
    using asm greater_def by blast
  then obtain ar where "Some ar = a \<oplus> r" 
    by (metis asso2 calculation(3) commutative option.exhaust_sel option.simps(3))
  then have "ar \<in> A" 
    by (meson assms calculation(1) greater_def up_closed_def  )
  then show "\<phi>' \<in> A \<otimes> B" 
    by (metis \<open>Some \<phi>' = \<phi> \<oplus> r\<close> \<open>Some ar = a \<oplus> r\<close> add_set_elem asso1 calculation(2) calculation(3) commutative)
qed

lemma up_closed_bigger_subset:
  assumes "up_closed B"
      and "A \<ggreater> B"
    shows "A \<subseteq> B"
  by (meson assms(1) assms(2) greater_set_def up_closed_def   subsetI)

lemma equiv_stable_sum:
  assumes "A \<sim> B"
  shows "A \<otimes> C \<sim> B \<otimes> C"
  using assms bigger_set local.equiv_def by auto

lemma equiv_up_closed_subset:
  assumes "up_closed A"
      and "equiv B C"
    shows "B \<subseteq> A \<longleftrightarrow> C \<subseteq> A" (is "?B \<longleftrightarrow> ?C")
proof -
  have "?B \<Longrightarrow> ?C"
    by (meson greater_set_def up_closed_def equiv_def assms(1) assms(2) subsetD subsetI)
  moreover have "?C \<Longrightarrow> ?B"
    by (meson greater_set_def up_closed_def equiv_def assms(1) assms(2) subsetD subsetI)
  ultimately show ?thesis by blast
qed

lemma mono_propI:
  assumes "\<And>x y. y \<succeq> x \<and> P x \<Longrightarrow> P y"
  shows "mono_prop P"
  using assms mono_prop_def by blast

lemma mono_prop_set:
  assumes "A \<ggreater> B"
      and "setify P B"
      and "mono_prop P"
    shows "setify P A"
  using assms(1) assms(2) assms(3) greater_set_def local.setify_def mono_prop_def by auto

lemma mono_prop_set_equiv:
  assumes "mono_prop P"
      and "equiv A B"
    shows "setify P A \<longleftrightarrow> setify P B"
  by (meson assms(1) assms(2) local.equiv_def mono_prop_set  )

lemma setify_sum:
  "setify P (A \<otimes> B) \<longleftrightarrow> (\<forall>x \<in> A. setify P ({x} \<otimes> B))" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<Longrightarrow> ?B" 
    using local.setify_def add_set_elem   singletonD by fastforce
  moreover have "?B \<Longrightarrow> ?A" 
    using add_set_elem local.setify_def by fastforce
  ultimately show ?thesis by blast
qed

lemma setify_sum_image:
  "setify P ((Set.image f A) \<otimes> B) \<longleftrightarrow> (\<forall>x \<in> A. setify P ({f x} \<otimes> B))" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (meson image_eqI setify_sum)
  show "?B \<Longrightarrow> ?A"
    by (metis (mono_tags, lifting) imageE setify_sum)
qed

lemma equivI:
  assumes "A \<ggreater> B"
    and "B \<ggreater> A"
    shows "equiv A B"
  by (simp add: assms(1) assms(2) local.equiv_def)






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

lemma sum_then_singleton:
  "Some a = b \<oplus> c \<longleftrightarrow> {a} = {b} \<otimes> {c}" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?A \<Longrightarrow> ?B"
  proof -
    assume ?A
    then have "{a} \<subseteq> {b} \<otimes> {c}"
      using add_set_elem by auto
    moreover have "{b} \<otimes> {c} \<subseteq> {a}" 
      using add_set_elem[of _ "{b}" "{c}"] calculation insert_subset option.sel singleton_iff subsetI
      by metis
    ultimately show ?thesis by blast
  qed
  moreover have "?B \<Longrightarrow> ?A" 
    using add_set_elem by auto
  ultimately show ?thesis by blast
qed

lemma empty_set_sum:
  "{} \<otimes> A = {}" 
  by (simp add: add_set_def)

lemma is_in_set_sum:
  assumes "Some a = b \<oplus> c"
      and "c \<in> C"
    shows "a \<in> {b} \<otimes> C"
  using add_set_elem assms(1) assms(2) by blast

lemma in_set_sum:
  assumes "\<omega> \<in> A \<otimes> B"
  shows "\<exists>a \<in> A. \<omega> \<succeq> a"
  by (metis add_set_elem assms commutative greater_equiv)


end

instantiation set :: (pcm) ab_semigroup_add
begin

definition plus_set where "plus_set A B = A \<otimes> B"

instance proof
  fix a b c :: "'a set"
  show "a + b + c = a + (b + c)"
    by (simp add: add_set_asso plus_set_def)

  show "a + b = b + a"
    by (simp add: add_set_commm plus_set_def)
qed

end

section \<open>Instantiations of PCMs\<close>

subsection \<open>Product\<close>

instantiation prod :: (pcm, pcm) pcm
begin

definition plus_prod where "plus_prod a b = (let x = fst a \<oplus> fst b in let y = snd a \<oplus> snd b in
  if x = None \<or> y = None then None else Some (the x, the y))"

lemma plus_prodIAlt:
  assumes "Some x = fst a \<oplus> fst b"
      and "Some y = snd a \<oplus> snd b"
    shows "a \<oplus> b = Some (x, y)"
proof -
  have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    using assms(1) assms(2) option.discI[of "fst a \<oplus> fst b" x] option.discI[of "snd a \<oplus> snd b" y] plus_prod_def[of a b]    
    by presburger
  then show ?thesis
    by (metis assms(1) assms(2) option.sel)
qed

lemma plus_prodI:
  assumes "Some (fst x) = fst a \<oplus> fst b"
      and "Some (snd x) = snd a \<oplus> snd b"
    shows "Some x = a \<oplus> b"
proof -
  have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    using assms(1) assms(2) option.discI[of "fst a \<oplus> fst b" "fst x"] option.discI[of "snd a \<oplus> snd b" "snd x"] plus_prod_def[of a b]    
    by presburger
  then show ?thesis
    by (metis assms(1) assms(2) option.sel prod.collapse)
qed

lemma plus_prodE:
  assumes "a \<oplus> b = Some x"
  shows "fst a \<oplus> fst b = Some (fst x) \<and> snd a \<oplus> snd b = Some (snd x)"
proof -
  have "fst a \<oplus> fst b \<noteq> None \<and> snd a \<oplus> snd b \<noteq> None"
    using assms option.discI plus_prod_def[of a b] by fastforce
  then have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    by (simp add: SepAlgebra.plus_prodIAlt)
  then show ?thesis
    by (simp add: \<open>fst a \<oplus> fst b \<noteq> None \<and> snd a \<oplus> snd b \<noteq> None\<close> assms)
qed

instance proof
  fix a b c ab bc :: "'a :: pcm \<times> 'b :: pcm"
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative plus_prod_def)
  assume "a \<oplus> b = Some ab \<and> b \<oplus> c = None"
  show "ab \<oplus> c = None"
  proof (cases "fst b \<oplus> fst c")
    case None
    then show ?thesis
      by (metis (mono_tags, opaque_lifting) \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> asso2 option.exhaust option.simps(3) plus_prodE)
  next
    case (Some aa)
    then have "snd b \<oplus> snd c = None"
      by (metis \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> option.distinct(1) option.exhaust plus_prodIAlt)
    then show ?thesis
      by (metis (mono_tags, opaque_lifting) \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> asso2 not_None_eq plus_prodE)
  qed
next
  fix a b c ab bc :: "'a :: pcm \<times> 'b :: pcm"
  assume "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
  then have "fst a \<oplus> fst b = Some (fst ab) \<and> fst b \<oplus> fst c = Some (fst bc) \<and> snd a \<oplus> snd b = Some (snd ab) \<and> snd b \<oplus> snd c = Some (snd bc)"
    using SepAlgebra.plus_prodE by blast
  then have "fst ab \<oplus> fst c = fst a \<oplus> fst bc \<and> snd ab \<oplus> snd c = snd a \<oplus> snd bc"
    by (meson asso1)
  then show "ab \<oplus> c = a \<oplus> bc"
    by (simp add: plus_prod_def)
next
  fix a b c :: "'a :: pcm \<times> 'b :: pcm"

  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "Some (fst a) = fst a \<oplus> fst a \<and> Some (snd a) = snd a \<oplus> snd a"
    using plus_prodE[of a b] plus_prodE[of c c] positivity
    by metis
  then show "Some a = a \<oplus> a"
    using SepAlgebra.plus_prodIAlt by fastforce
qed


lemma greater_prod_eq:
  "x \<succeq> y \<longleftrightarrow> (fst x \<succeq> fst y) \<and> (snd x \<succeq> snd y)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain r where "Some x = y \<oplus> r"
    using greater_def by blast
  then have "Some (fst x) = fst y \<oplus> fst r \<and> Some (snd x) = snd y \<oplus> snd r"
    by (metis SepAlgebra.plus_prodE)
  then show ?B
    by (meson greater_def)
next
  assume ?B
  then obtain r1 r2 where "Some (fst x) = fst y \<oplus> r1 \<and> Some (snd x) = snd y \<oplus> r2"
    by (meson greater_def)
  then have "Some x = y \<oplus> (r1, r2)"
    using SepAlgebra.plus_prodIAlt by fastforce
  then show ?A
    using greater_def by auto
qed

end

subsection \<open>Function\<close>

datatype 'v agreement = Ag (the_ag: 'v)

instantiation "agreement" :: (type) pcm
begin

definition plus_agreement :: "'a agreement \<Rightarrow> 'a agreement \<Rightarrow> 'a agreement option" where
  "plus_agreement a b = (if a = b then Some a else None)"

instance proof
  fix a b c ab bc :: "'a agreement"
  show "a \<oplus> b = b \<oplus> a"
    using plus_agreement_def by presburger
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (metis option.sel plus_agreement_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (metis option.sel plus_agreement_def)
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a "
    by (metis SepAlgebra.plus_agreement_def)
qed


end

instantiation prat :: pcm
begin

definition plus_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat option" where
  "plus_prat a b = Some (a + b)"

instance proof
  fix a b c ab bc :: prat
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: SepAlgebra.plus_prat_def add.commute)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    using SepAlgebra.plus_prat_def add.assoc by force
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (simp add: plus_prat_def)
  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "c = 0"
    by (metis Rep_prat_inject SepAlgebra.plus_prat_def add_cancel_right_right option.sel plus_prat.rep_eq zero_prat.rep_eq)
  then show "Some a = a \<oplus> a"
    by (metis PosRat.pgte.rep_eq PosRat.sum_larger Rep_prat_inject SepAlgebra.plus_prat_def \<open>a \<oplus> b = Some c\<close> add_0 nle_le option.inject)
qed

end

instantiation preal :: pcm
begin

definition plus_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal option" where
  "plus_preal a b = Some (a + b)"

instance proof
  fix a b c ab bc :: preal
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: SepAlgebra.plus_preal_def add.commute)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    using SepAlgebra.plus_preal_def add.assoc by force
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (simp add: plus_preal_def)
  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "c = 0"
    by (metis (no_types, opaque_lifting) PosReal.padd_cancellative SepAlgebra.plus_preal_def add_0 option.sel)
  then show "Some a = a \<oplus> a"
    by (metis SepAlgebra.plus_preal_def \<open>a \<oplus> b = Some c\<close> add.commute add.right_neutral nle_le option.inject pos_perm_class.sum_larger)
qed

end




instantiation "fun" :: (type, pcm) pcm
begin

definition compatible_fun where
  "compatible_fun a b \<longleftrightarrow> (\<forall>l. a l \<oplus> b l \<noteq> None)"

lemma compatible_funI:
  assumes "\<And>l. a l \<oplus> b l \<noteq> None"
  shows "compatible_fun a b"
  by (simp add: assms compatible_fun_def)

lemma compatible_funE:
  assumes "compatible_fun a b"
  shows "a l \<oplus> b l \<noteq> None"
  by (meson assms compatible_fun_def)

definition plus_fun where
  "plus_fun a b = (if compatible_fun a b then Some (\<lambda>l. the (a l \<oplus> b l)) else None)"

lemma plus_funI:
  assumes "\<And>l. Some (x l) = a l \<oplus> b l"
    shows "Some x = a \<oplus> b"
proof -
  obtain ab where "Some ab = a \<oplus> b"
    by (metis assms compatible_fun_def option.discI plus_fun_def)
  moreover have "ab = x"
  proof (rule ext)
    fix l show "ab l = x l"
      by (metis (mono_tags, lifting) assms calculation option.discI option.sel plus_fun_def)
  qed
  ultimately show ?thesis
    by auto
qed

lemma plus_funE:
  assumes "Some x = a \<oplus> b"
  shows "Some (x l) = a l \<oplus> b l"
  by (metis (no_types, lifting) assms compatible_funE option.discI option.exhaust_sel option.sel plus_fun_def)

instance proof

  fix a b c ab bc :: "'a \<Rightarrow> 'b :: pcm"
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative compatible_fun_def plus_fun_def)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  proof -
    assume asm0: "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
    show "ab \<oplus> c = a \<oplus> bc"
    proof (cases "ab \<oplus> c")
      case None
      then obtain l where "ab l \<oplus> c l = None"
        by (metis compatible_fun_def option.discI plus_fun_def)
      then have "a l \<oplus> bc l = None"
        using SepAlgebra.plus_funE[of ab a b] plus_funE[of bc b c] asm0 asso1
        by metis
      then show ?thesis
        by (metis None compatible_fun_def plus_fun_def)
    next
      case (Some f)
      have "compatible_fun a bc"
      proof (rule compatible_funI)
        fix l
        have "ab l \<oplus> c l \<noteq> None"
          by (metis Some compatible_funE option.discI plus_fun_def)
        then show "a l \<oplus> bc l \<noteq> None"
          using asso1[of "a l" "b l" "ab l" "c l" "bc l"]
          by (metis asm0 plus_funE)
      qed
      then obtain f' where "Some f' = a \<oplus> bc"
        by (simp add: plus_fun_def)
      moreover have "f = f'"
      proof (rule ext)
        fix l 
        have "ab l \<oplus> c l = a l \<oplus> bc l"
          using asso1[of "a l" "b l" "ab l" "c l" "bc l"]
          by (metis SepAlgebra.plus_funE asm0)
        then show "f l = f' l"
          by (metis (no_types, lifting) Some calculation option.discI option.sel plus_fun_def)
      qed
      ultimately show ?thesis
        using Some by force
    qed
  qed
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (metis (mono_tags, lifting) asso2 compatible_fun_def option.discI option.exhaust_sel option.sel plus_fun_def)

  assume asm0: "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  have "compatible_fun a a"
  proof (rule compatible_funI)
    fix l show "a l \<oplus> a l \<noteq> None"
      using asm0(1) asm0(2) asso2[of "b l" "a l" ]
        commutative[of "a l"] plus_fun_def[of c c] plus_fun_def[of a b]
      by (metis option.discI plus_funE)
  qed
  then obtain aa where "Some aa = a \<oplus> a"
    by (simp add: plus_fun_def)
  moreover have "aa = a"
  proof (rule ext)
    fix l show "aa l = a l"
      by (metis (mono_tags, lifting) asm0(1) asm0(2) calculation compatible_fun_def option.discI option.exhaust_sel option.sel plus_fun_def positivity)
  qed
  ultimately show "Some a = a \<oplus> a" by simp
qed

lemma greaterI:
  fixes a :: "'a \<Rightarrow> 'b"
  assumes "\<And>l. a l \<succeq> b l"
  shows "a \<succeq> b"
proof -
  let ?r = "\<lambda>l. SOME r. Some (a l) = b l \<oplus> r"
  have "Some a = b \<oplus> ?r"
  proof (rule plus_funI)
    fix l
    show "Some (a l) = b l \<oplus> ?r l"
      using someI_ex assms greater_def by fast
  qed
  then show ?thesis
    using greater_def by blast
qed

lemma greaterE:
  assumes "a \<succeq> b"
  shows "a l \<succeq> b l"
  by (meson SepAlgebra.plus_funE assms greater_def)

end

subsection \<open>Option\<close>

instantiation option :: (pcm) pcm
begin

fun plus_option where
  "plus_option None x = Some x"
| "plus_option x None = Some x"
| "plus_option (Some a) (Some b) = (let r = a \<oplus> b in if r = None then None else Some r)"

lemma plus_optionI:
  assumes "x = Some xx"
      and "y = Some yy"
      and "Some a = xx \<oplus> yy"
    shows "Some (Some a) = x \<oplus> y"
  using assms(1) assms(2) assms(3) option.discI by fastforce

lemma plus_option_Some_None:
  "Some x \<oplus> Some y = None \<longleftrightarrow> x \<oplus> y = None"
  using option.discI by fastforce

lemma plus_optionE:
  assumes "x = Some xx"
      and "a = Some aa"
      and "b = Some bb"
      and "Some x = a \<oplus> b"
    shows "Some xx = aa \<oplus> bb"
  using plus_option.simps(3)[of aa bb]
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) option.discI option.inject)
  

instance proof
  fix a b c ab bc :: "('a :: pcm) option"

  show "a \<oplus> b = b \<oplus> a"
    apply (cases a)
    apply (metis option.discI plus_option.elims)
    by (metis commutative option.exhaust plus_option.simps(1) plus_option.simps(2) plus_option.simps(3))

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    apply (cases a; cases b; cases c)
           apply simp_all
       apply fastforce+
     apply (cases ab)
        apply force
       apply force
    apply (cases ab; cases bc)
    apply (metis (mono_tags) option.discI option.inject)
    apply (metis (mono_tags, lifting) option.discI option.inject)
     apply (metis (mono_tags, lifting) option.discI option.inject)
  proof -
    fix a' b' c' ab' bc'
    assume "(let r = a' \<oplus> b' in if r = None then None else Some r) = Some ab \<and>
       (let r = b' \<oplus> c' in if r = None then None else Some r) = Some bc"
      "a = Some a'" "b = Some b'" "c = Some c'" "ab = Some ab'" "bc = Some bc'"
    then have "ab' \<oplus> c' = a' \<oplus> bc'"
      using asso1[of a' b' ab' c' bc']
      by (metis (mono_tags, lifting) option.discI option.inject)
    then show "ab \<oplus> Some c' = Some a' \<oplus> bc"
      by (simp add: \<open>ab = Some ab'\<close> \<open>bc = Some bc'\<close>)
  qed
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    apply (cases a; cases b; cases c; cases ab)
    apply auto[14]
    using option.discI option.sel plus_option.simps(3)[of "the a" "the b"]
    apply (metis (full_types))
    by (metis SepAlgebra.plus_option_Some_None asso2 plus_optionE)
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
    apply (cases a; cases b; cases c)
           apply auto[6]
     apply (metis SepAlgebra.plus_optionI SepAlgebra.plus_option_Some_None not_Some_eq option.inject)
    by (metis plus_optionE plus_optionI positivity)
qed

end


lemma compatible_partial_functions:
  fixes a :: "'a \<rightharpoonup> ('b :: pcm)"
  shows "a ## b \<longleftrightarrow> (\<forall>l xa xb. a l = Some xa \<and> b l = Some xb \<longrightarrow> xa ## xb)" (is "?A \<longleftrightarrow> ?B")
proof
  assume asm0: ?B
  have "compatible_fun a b"
  proof (rule compatible_funI)
    fix l show "a l \<oplus> b l \<noteq> None"
      apply (cases "a l")
      apply force
      apply (cases "b l")
      apply simp
      using asm0 defined_def by force
  qed
  then show ?A
    by (simp add: defined_def plus_fun_def)
next
  assume asm0: ?A
  show "\<forall>l xa xb. a l = Some xa \<and> b l = Some xb \<longrightarrow> xa ## xb"
  proof (clarify)
    fix l xa xb assume asm1: "a l = Some xa" "b l = Some xb"
    moreover have "a l \<oplus> b l \<noteq> None"
      by (meson asm0 compatible_fun_def defined_def plus_fun_def)
    ultimately show "xa ## xb"
      using defined_def by fastforce
  qed
qed

lemma result_sum_partial_functions:
  assumes "Some x = a \<oplus> b"
  shows "a l = None \<Longrightarrow> x l = b l"
    and "b l = None \<Longrightarrow> x l = a l"
    and "a l = Some va \<and> b l = Some vb \<Longrightarrow> x l = va \<oplus> vb"
    apply (metis (no_types, lifting) assms option.discI option.sel plus_fun_def plus_option.elims)

   apply (metis (mono_tags, opaque_lifting) assms commutative option.inject plus_funE plus_option.simps(1))
  using assms option.discI option.inject plus_funE[of x a b] plus_option.simps(3)[of va vb]
  by (metis (full_types))


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



lemma up_close_equiv:
  assumes "up_closed A"
      and "up_closed B"
    shows "A \<sim> B \<longleftrightarrow> A = B"
proof -
  have "A \<sim> B \<longleftrightarrow> A \<ggreater> B \<and> B \<ggreater> A" 
    using local.equiv_def by auto
  also have "... \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A" 
    by (metis assms(1) assms(2) greater_set_def set_eq_subset succ_refl up_closed_bigger_subset)
  ultimately show ?thesis 
    by blast
qed

lemma sub_bigger:
  assumes "A \<subseteq> B"
  shows "A \<ggreater> B" 
  by (meson assms greater_set_def in_mono succ_refl)

lemma larger_set_refl:
  "A \<ggreater> A"
  by (simp add: sub_bigger)


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


section \<open>Instantiations of PCMs with core\<close>

subsection \<open>Agreement\<close>

instantiation "agreement" :: (type) pcm_with_core
begin

definition core_agreement :: "'a agreement \<Rightarrow> 'a agreement" where
  "core_agreement x = x"

instance proof
  fix a b c x y :: "'a agreement"
  show "Some x = x \<oplus> |x|"
    by (simp add: core_agreement_def plus_agreement_def)
  show "Some |x| = |x| \<oplus> |x|"
    by (simp add: \<open>Some x = x \<oplus> |x|\<close> core_agreement_def)
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    using commutative core_agreement_def by auto
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    by (simp add: core_agreement_def)
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    using core_agreement_def by auto
qed

end


subsection \<open>Product\<close>

instantiation prod :: (pcm_with_core, pcm_with_core) pcm_with_core
begin

definition core_def: "|a| = ( |fst a|, |snd a| )"

instance proof
  fix x y a b c :: "'a :: pcm_with_core \<times> 'b :: pcm_with_core"

  show "Some a = a \<oplus> |a|"
    by (simp add: core_def core_is_smaller plus_prodIAlt)

  show "Some |a| = |a| \<oplus> |a|"
    by (metis (mono_tags, opaque_lifting) SepAlgebra.core_def plus_prodIAlt core_is_pure fst_eqD snd_eqD)

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
  proof -
    assume asm0: "Some x = x \<oplus> c"
    then obtain r1 r2 where "Some |fst x| = fst c \<oplus> r1" "Some |snd x| = snd c \<oplus> r2"
      by (metis core_max plus_prodE)
    then show "\<exists>r. Some |x| = c \<oplus> r"
      by (metis core_def fst_eqD plus_prodIAlt snd_conv)
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using plus_prodE[of a b c] core_def[of a] core_def[of b] core_def[of c]
      plus_prodIAlt[of "fst |c|" "|a|" "|b|"] core_sum eq_snd_iff  prod.sel(1) by metis
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis plus_prodE cancellative core_def prod.collapse prod.sel(1) prod.sel(2))
qed

end

subsection \<open>Function\<close>

instantiation "fun" :: (type, pcm_with_core) pcm_with_core
begin

definition core_fun: "core_fun f l = |f l|"

instance proof
  fix x y a b c :: "'a \<Rightarrow> 'b"
  show "Some x = x \<oplus> |x|"
  proof -
    have "compatible_fun x |x|"
    proof (rule compatible_funI)
      fix l show "x l \<oplus> |x| l \<noteq> None"
        by (simp add: core_fun core_is_smaller option.discI)
    qed
    then obtain xx where "Some xx = x \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = x"
    proof (rule ext)
      fix l show "xx l = x l"
        by (metis (mono_tags, lifting) \<open>compatible_fun x |x|\<close> calculation core_fun core_is_smaller option.sel plus_fun_def)
    qed
    ultimately show ?thesis by blast
  qed

  show "Some |x| = |x| \<oplus> |x|"
  proof -
    have "compatible_fun ( |x| ) |x|"
    proof (rule compatible_funI)
      fix l show "|x| l \<oplus> |x| l \<noteq> None"
        by (metis core_fun core_is_pure option.discI)
    qed
    then obtain xx where "Some xx = |x| \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = |x|"
    proof (rule ext)
      fix l show "xx l = |x| l"        
        by (metis (mono_tags, lifting) \<open>compatible_fun ( |x| ) |x|\<close> calculation core_fun core_is_pure option.sel plus_fun_def)
    qed
    ultimately show ?thesis by simp
  qed

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
  proof -
    assume asm0: "Some x = x \<oplus> c"
    have "compatible_fun c |x|"
    proof (rule compatible_funI)
      fix l show "c l \<oplus> |x| l \<noteq> None"
        by (metis (mono_tags, lifting) \<open>Some x = x \<oplus> |x|\<close> asm0 asso2 compatible_funE option.simps(3) plus_fun_def)
    qed
    then obtain xx where "Some xx = c \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = |x|"
    proof (rule ext)
      fix l
      have "Some (x l) = (x l) \<oplus> (c l)"
        by (metis (mono_tags, lifting) asm0 compatible_funE option.discI option.expand option.sel plus_fun_def)
      then show "xx l = |x| l"
        using core_fun[of x l] core_is_pure[of "x l"] core_max[of "x l" "c l"]
         plus_fun_def[of c "|x|"] \<open>compatible_fun c |x|\<close> asso1[of "c l" _]
          calculation
          option.sel
          positivity[of _ _ "|x l|"]
        by metis
    qed
    ultimately show "\<exists>r. Some |x| = c \<oplus> r"
      by blast
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
  proof -
    assume asm0: "Some c = a \<oplus> b"
    have "compatible_fun ( |a| ) |b|"
    proof (rule compatible_funI)
      fix l 
      have "Some (c l) = a l \<oplus> b l"
        by (metis (mono_tags, lifting) asm0 compatible_funE option.discI option.exhaust_sel option.sel plus_fun_def)
      then show "|a| l \<oplus> |b| l \<noteq> None"
        by (metis core_fun core_sum is_none_simps(1) is_none_simps(2))
    qed
    then obtain x where "Some x = |a| \<oplus> |b|"
      by (simp add: plus_fun_def)
    moreover have "x = |c|"
    proof (rule ext)
      fix l 
      show "x l = |c| l"
        using asm0 calculation core_fun[of _ l] core_sum[of "c l" "a l" "b l"] option.sel plus_funE[of c a b] plus_funE[of x]
        by (metis (mono_tags))
    qed
    ultimately show "Some |c| = |a| \<oplus> |b|" by simp
  qed

  assume asm0: "Some a = b \<oplus> x" "Some a = b \<oplus> y" "|x| = |y|"
  show "x = y"
  proof (rule ext)
    fix l 
    have "Some (a l) = b l \<oplus> x l \<and> Some (a l) = b l \<oplus> y l \<and> |x l| = |y l|"
      by (metis (mono_tags, lifting) asm0(1) asm0(2) asm0(3) compatible_funE core_fun option.discI option.exhaust_sel option.sel plus_fun_def)
    then show "x l = y l"
      using cancellative by blast
  qed
qed

end

subsection \<open>Option\<close>

instantiation option :: (pcm_with_core) pcm_with_core
begin

fun core_option where
  "core_option None = None"
| "core_option (Some x) = Some |x|"

lemma core_option_None:
  "|x| = None \<longleftrightarrow> x = None"
  using core_option.elims by blast

lemma core_option_Some:
  "|x| \<noteq> None \<longleftrightarrow> x \<noteq> None"
  by (simp add: core_option_None)

instance proof
  fix x y a b c :: "'a option"
  show "Some x = x \<oplus> |x|"
    apply (cases x)    
     apply simp
    using core_is_smaller core_option.simps(2) plus_optionI by blast


  show "Some |x| = |x| \<oplus> |x|"
    apply (cases x)
     apply simp    
    using core_is_pure plus_optionI by fastforce


  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    apply (cases x)
    apply force
    apply (cases c)
     apply simp
    by (metis core_max core_option.simps(2) plus_optionE plus_optionI)

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    apply (cases a; cases b; cases c)
           apply auto[6]
     apply (metis option.distinct(1) option.exhaust_sel option.inject plus_optionI plus_option_Some_None)
  proof -
    fix a' b' c' assume "Some c = a \<oplus> b" "a = Some a'" "b = Some b'" "c = Some c'"
    then have "Some |c'| = |a'| \<oplus> |b'|"
      using core_sum plus_optionE by blast
    then show "Some |c| = |a| \<oplus> |b|"
      using \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> plus_optionI by fastforce
  qed
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    apply (cases a; cases b; cases x; cases y)
                   apply auto[7]
            apply (metis option.collapse option.inject option.simps(3) plus_optionI plus_option_Some_None)
           apply auto[5]
      apply (metis core_option_None)
    apply auto[1]
  proof -
    fix a' b' x' y'
    assume "Some a = b \<oplus> x" "Some a = b \<oplus> y" "|x| = |y|" "a = Some a'" "b = Some b'" "x = Some x'" "y = Some y'"
    then have "x' = y'" using cancellative[of a' b' x' y']
      by (metis core_option.simps(2) option.inject plus_optionE)
    then show "x = y"
      by (simp add: \<open>x = Some x'\<close> \<open>y = Some y'\<close>)
  qed
qed

end

lemma padd_pnone:
  "padd x pnone = x"
  by simp


instantiation prat :: pcm_with_core
begin

definition core_prat :: "prat \<Rightarrow> prat" where
  "core_prat a = 0"

instance proof
  fix a b c x y :: prat
  show "Some x = x \<oplus> |x|"
    by (simp add: core_prat_def padd_pnone plus_prat_def)
  show "Some |x| = |x| \<oplus> |x|"
    using core_prat_def padd_pnone plus_prat_def by force
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    by (metis PosRat.padd_cancellative SepAlgebra.plus_prat_def \<open>Some x = x \<oplus> |x|\<close> \<open>Some |x| = |x| \<oplus> |x|\<close> add.commute option.sel)
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using \<open>Some |x| = |x| \<oplus> |x|\<close> core_prat_def by auto
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis PosRat.padd_cancellative SepAlgebra.plus_prat_def add.commute option.sel)
qed

end

instantiation preal :: pcm_with_core
begin

definition core_preal :: "preal \<Rightarrow> preal" where
  "core_preal a = 0"

instance proof
  fix a b c x y :: preal
  show "Some x = x \<oplus> |x|"
    by (simp add: core_preal_def padd_pnone plus_preal_def)
  show "Some |x| = |x| \<oplus> |x|"
    using core_preal_def padd_pnone plus_preal_def by force
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    by (metis PosReal.padd_cancellative SepAlgebra.plus_preal_def \<open>Some x = x \<oplus> |x|\<close> \<open>Some |x| = |x| \<oplus> |x|\<close> add.commute option.sel)
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using \<open>Some |x| = |x| \<oplus> |x|\<close> core_preal_def by auto
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis PosReal.padd_cancellative SepAlgebra.plus_preal_def add.commute option.sel)
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


section \<open>Instantiations of PCMs with multiplication\<close>

instantiation preal :: pcm_mult
begin

definition mult_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "mult_preal = (*)"

instance proof
  fix \<alpha> \<beta> a b x :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_preal_def)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult.assoc mult_preal_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    by (simp add: SepAlgebra.plus_preal_def distrib_left mult.commute mult_preal_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: SepAlgebra.plus_preal_def distrib_left mult_preal_def)
qed

end

instantiation prod :: (pcm_mult, pcm_mult) pcm_mult
begin

definition mult_prod :: "preal \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" where
  "mult_prod \<alpha> x = (\<alpha> \<odot> fst x, \<alpha> \<odot> snd x)"

instance proof
  fix a b x :: "'a \<times> 'b"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_prod_def unit_mult)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult_mult mult_prod_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    apply (rule plus_prodI)
    apply (simp add: SepAlgebra.mult_prod_def distrib_scala_mult)
    by (simp add: SepAlgebra.mult_prod_def distrib_scala_mult)
  assume "Some x = a \<oplus> b"
  then have "Some (\<alpha> \<odot> fst x) = (\<alpha> \<odot> fst a) \<oplus> (\<alpha> \<odot> fst b) \<and> Some (\<alpha> \<odot> snd x) = (\<alpha> \<odot> snd a) \<oplus> (\<alpha> \<odot> snd b)"
    by (metis distrib_state_mult plus_prodE)
  then show "Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (metis fst_eqD mult_prod_def plus_prodIAlt snd_eqD)
qed

end

instantiation "fun" :: (type, pcm_mult) pcm_mult
begin

definition mult_fun where "mult_fun \<alpha> f x = \<alpha> \<odot> f x"

instance proof
  fix f a b :: "'a \<Rightarrow> 'b"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> f = f"
  proof (rule ext)
    fix x show "(pwrite \<odot> f) x = f x"
      by (simp add: mult_fun_def unit_mult)
  qed
  show "\<alpha> \<odot> (\<beta> \<odot> f) = pmult \<alpha> \<beta> \<odot> f"
  proof (rule ext)
    fix x show "(\<alpha> \<odot> (\<beta> \<odot> f)) x = (pmult \<alpha> \<beta> \<odot> f) x"
      by (simp add: mult_fun_def mult_mult)
  qed

  have "compatible_fun (\<alpha> \<odot> f) (\<beta> \<odot> f)"
    by (metis (mono_tags, lifting) compatible_fun_def distrib_scala_mult mult_fun_def option.discI)
  then obtain ff where "Some ff = \<alpha> \<odot> f \<oplus> \<beta> \<odot> f"
    by (simp add: plus_fun_def)
  moreover have "ff = padd \<alpha> \<beta> \<odot> f"
  proof (rule ext)
    fix x
    show "ff x = (padd \<alpha> \<beta> \<odot> f) x"
      by (metis (mono_tags, lifting) \<open>compatible_fun (\<alpha> \<odot> f) (\<beta> \<odot> f)\<close> calculation distrib_scala_mult mult_fun_def option.sel plus_fun_def)
  qed
  ultimately show "Some (padd \<alpha> \<beta> \<odot> f) = \<alpha> \<odot> f \<oplus> \<beta> \<odot> f"
    by blast


  assume asm0: "Some f = a \<oplus> b"
  have "compatible_fun (\<alpha> \<odot> a) (\<alpha> \<odot> b)"
  proof (rule compatible_funI)
    fix l show "(\<alpha> \<odot> a) l \<oplus> (\<alpha> \<odot> b) l \<noteq> None"
      by (metis asm0 distrib_state_mult mult_fun_def option.simps(3) plus_funE)
  qed
  then obtain ff where "Some ff = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: plus_fun_def)
  moreover have "ff = \<alpha> \<odot> f"
  proof (rule ext)
    fix x show "ff x = (\<alpha> \<odot> f) x"
      using asm0 calculation distrib_state_mult mult_fun_def option.sel plus_funE[of _ a b] plus_funE[of _ "\<alpha> \<odot> a" "\<alpha> \<odot> b"]
      by metis
  qed
  ultimately show "Some (\<alpha> \<odot> f) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by blast
qed

end

instantiation option :: (pcm_mult) pcm_mult
begin

fun mult_option :: "preal \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "mult_option \<alpha> None = None"
| "mult_option \<alpha> (Some x) = Some (\<alpha> \<odot> x)"

(* TODO *)
instance proof
  fix x a b :: "'a option"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (metis SepAlgebra.mult_option.elims unit_mult)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (metis SepAlgebra.mult_option.simps(1) mult_mult mult_option.simps(2) not_Some_eq)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    apply (cases x)
    apply simp
    using distrib_scala_mult plus_optionI by fastforce
  assume asm0: "Some x = a \<oplus> b"
  show "Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
  proof (cases "a \<noteq> None \<and> b \<noteq> None \<and> x \<noteq> None")
    case True
    then obtain aa bb xx where "a = Some aa \<and> b = Some bb \<and> x = Some xx"
      by blast
    then have "Some xx = aa \<oplus> bb"
      using asm0 plus_optionE by blast
    then have "Some (\<alpha> \<odot> xx) = \<alpha> \<odot> aa \<oplus> \<alpha> \<odot> bb"
      by (simp add: distrib_state_mult)
    then show ?thesis
      using SepAlgebra.mult_option.simps(2) \<open>a = Some aa \<and> b = Some bb \<and> x = Some xx\<close> option.discI by fastforce
  next
    case False
    then show ?thesis
      apply (cases a)
      using asm0 apply force
      apply (cases b)
      using asm0 apply auto[1]
      apply (cases x)
      apply (metis asm0 asso1 option.distinct(1) option.inject plus_option.simps(1) positivity)
      by simp
  qed
qed

end




instantiation agreement :: (type) pcm_mult
begin

definition mult_agreement :: "preal \<Rightarrow> 'a agreement \<Rightarrow> 'a agreement" where
  "mult_agreement \<alpha> x = x"

(* TODO *)
instance proof
  fix x a b :: "'a agreement"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_agreement_def)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult_agreement_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: mult_agreement_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    by (simp add: mult_agreement_def plus_agreement_def)
qed

end


section \<open>Separation algebra\<close>

class sep_algebra = pcm_with_core +

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

begin

definition stable :: "'a \<Rightarrow> bool" where
  "stable = stable_rel u"


definition stabilize :: "'a \<Rightarrow> 'a" where
  "stabilize = stabilize_rel u"

lemma stabilize_rel_order:
  "stabilize_rel a x \<succeq> stabilize x"
  by (metis local.greater_equiv local.stabilize_rel_mono_left local.u_neutral stabilize_def)

lemma stabilize_rel_mono_right:
  "x \<succeq> a \<Longrightarrow> stabilize_rel b x \<succeq> stabilize_rel b a"
  using local.greater_def local.stabilize_rel_all_sum by blast

lemma already_stable: "stable x \<Longrightarrow> stabilize x = x"
  using local.already_stable_rel local.stable_def stabilize_def by force

lemma stabilize_rel_sum: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize_rel a b"
  by (simp add: local.stabilize_rel_sum_double stabilize_def)

lemma stabilize_is_stable: "stable (stabilize x)"
  by (simp add: local.stabilize_rel_is_stable_rel local.stable_def stabilize_def)

lemma stabilize_sum: "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
  using local.stabilize_rel_all_sum stabilize_def by auto


lemma decompose_stabilize_pure: "Some x = stabilize x \<oplus> |x|"
  by (simp add: local.stabilize_rel_sum_pure stabilize_def)



lemma stabilize_mono: "x \<succeq> a \<Longrightarrow> stabilize x \<succeq> stabilize a"
  using local.greater_equiv local.stabilize_sum by blast


lemma max_projection_prop_stable_rel_stabilize_rel:
  "max_projection_prop (stable_rel x) (stabilize_rel x)"
  apply (rule max_projection_propI)
  using local.greater_def local.stabilize_rel_sum_pure apply blast
  apply (simp add: local.stabilize_rel_is_stable_rel)
  by (metis local.already_stable_rel stabilize_rel_mono_right)

lemma max_projection_prop_stable_stabilize:
  "max_projection_prop stable stabilize"
  by (simp add: local.stable_def max_projection_prop_stable_rel_stabilize_rel stabilize_def)

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

lemma stabilize_rel_invo:
  "stabilize_rel x (stabilize_rel x a) = stabilize_rel x a"
  using local.already_stable_rel local.stabilize_rel_is_stable_rel by blast

definition pure_larger where
  "pure_larger a b \<longleftrightarrow> (\<exists>r. pure r \<and> Some a = b \<oplus> r)"

lemma pure_larger_stabilize:
  "pure_larger x (stabilize_rel y x)"
  using local.core_is_pure local.pure_def local.stabilize_rel_sum_pure pure_larger_def by blast

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

lemma neutral_smallest:
  "\<omega> \<succeq> u"
  using greater_equiv u_neutral by blast

lemma obtain_pure_remainder:
  assumes "a \<succeq> b"
  shows "\<exists>r. Some a = r \<oplus> b \<and> |r| = |a|"
  using assms local.commutative local.minus_core local.minus_equiv_def by auto

end



subsection \<open>Product\<close>


instantiation prod :: (sep_algebra, sep_algebra) sep_algebra
begin

definition stabilize_rel_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "stabilize_rel_prod x a = ( stabilize_rel (fst x) (fst a), stabilize_rel (snd x) (snd a) )"

definition stable_rel_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "stable_rel_prod x a \<longleftrightarrow> stable_rel (fst x) (fst a) \<and> stable_rel (snd x) (snd a)"

definition u_prod :: "'a \<times> 'b" where
  "u_prod = (u, u)"

instance
proof
  fix x a :: "'a :: sep_algebra \<times> 'b :: sep_algebra"
  show "Some x = stabilize_rel a x \<oplus> |x|"
    apply (rule plus_prodI)
    apply (simp add: core_def stabilize_rel_prod_def stabilize_rel_sum_pure)
    by (simp add: core_def stabilize_rel_prod_def stabilize_rel_sum_pure)
  show "Some x = x \<oplus> u"
    apply (rule plus_prodI)
    apply (simp add: u_neutral u_prod_def)
    by (simp add: u_neutral u_prod_def)
  show "stable_rel a (stabilize_rel a x)"
    by (simp add: stable_rel_prod_def stabilize_rel_is_stable_rel stabilize_rel_prod_def)
  assume "stable_rel a x"
  then show "stabilize_rel a x = x"
    by (simp add: stabilize_rel_prod_def already_stable_rel stable_rel_prod_def)
next
  fix a b x y :: "'a :: sep_algebra \<times> 'b :: sep_algebra"
  assume asm0: "Some x = a \<oplus> b"
  then have "Some (fst (stabilize_rel y x)) = fst (stabilize_rel y a) \<oplus> fst (stabilize_rel y b)"
    by (metis (mono_tags, lifting) SepAlgebra.stabilize_rel_prod_def fst_eqD plus_prodE stabilize_rel_all_sum)
  moreover have "Some (snd (stabilize_rel y x)) = snd (stabilize_rel y a) \<oplus> snd (stabilize_rel y b)"
    using asm0
    by (metis (mono_tags, lifting) SepAlgebra.stabilize_rel_prod_def plus_prodE snd_conv stabilize_rel_all_sum)
  ultimately show "Some (stabilize_rel y x) = stabilize_rel y a \<oplus> stabilize_rel y b"
    by (simp add: plus_prodIAlt)
  thm plus_prodIAlt
(*
  have "Some (fst (stabilize_rel u x)) = fst (stabilize_rel u a) \<oplus> fst (stabilize_rel a b)"
*)
  thm plus_prodI
  show "Some (stabilize_rel u x) = stabilize_rel u a \<oplus> stabilize_rel a b"
  proof (rule plus_prodI)
    show "Some (fst (stabilize_rel u x)) = fst (stabilize_rel u a) \<oplus> fst (stabilize_rel a b)"
      using asm0 stabilize_rel_sum_double[of "fst x"] plus_prodE[of a b x]
        SepAlgebra.u_prod_def fst_eqD stabilize_rel_prod_def[of u] stabilize_rel_prod_def[of a]
      by (metis (mono_tags))
    show "Some (snd (stabilize_rel u x)) = snd (stabilize_rel u a) \<oplus> snd (stabilize_rel a b)"
      using asm0 stabilize_rel_sum_double[of "snd x"] plus_prodE[of a b x]
        SepAlgebra.u_prod_def snd_eqD stabilize_rel_prod_def[of u] stabilize_rel_prod_def[of a]
      by (metis (mono_tags))
  qed
next
  fix a b x :: "'a :: sep_algebra \<times> 'b :: sep_algebra"
  assume "a \<succeq> b"
  then have "fst a \<succeq> fst b"
    by (simp add: greater_prod_eq)
  then have "stabilize_rel (fst a) (fst x) \<succeq> stabilize_rel (fst b) (fst x)"
    by (simp add: stabilize_rel_mono_left)
  then have "fst (stabilize_rel a x) \<succeq> fst (stabilize_rel b x)"
    by (simp add: stabilize_rel_prod_def)
  have "snd a \<succeq> snd b"
    using \<open>a \<succeq> b\<close> greater_prod_eq by blast
  then have "stabilize_rel (snd a) (snd x) \<succeq> stabilize_rel (snd b) (snd x)"
    by (simp add: stabilize_rel_mono_left)
  then have "snd (stabilize_rel a x) \<succeq> snd (stabilize_rel b x)"
    by (simp add: stabilize_rel_prod_def)
  then show "stabilize_rel a x \<succeq> stabilize_rel b x"
    by (simp add: \<open>fst (stabilize_rel a x) \<succeq> fst (stabilize_rel b x)\<close> greater_prod_eq)
qed

end

lemma stabilize_prod_def:
  "stabilize x = (stabilize (fst x), stabilize (snd x))"
  by (simp add: stabilize_def stabilize_rel_prod_def u_prod_def)

instantiation "fun" :: (type, sep_algebra) sep_algebra
begin


definition u_fun :: "'a \<Rightarrow> 'b :: sep_algebra" where
  "u_fun _ = u"

definition stabilize_rel_fun: "stabilize_rel_fun x f l = stabilize_rel (x l) (f l)"

definition stable_rel_fun: "stable_rel_fun x f \<longleftrightarrow> (\<forall>l. stable_rel (x l) (f l))"


instance 
proof
  fix x a :: "'a \<Rightarrow> 'b :: sep_algebra"
  show "Some x = stabilize_rel a x \<oplus> |x|"
    by (simp add: core_fun plus_funI stabilize_rel_fun stabilize_rel_sum_pure)
  show "Some x = x \<oplus> u"
    using plus_funI[of _ x u] u_fun_def u_neutral by fastforce
  show "stable_rel a (stabilize_rel a x)"
    by (simp add: stabilize_rel_fun stabilize_rel_is_stable_rel stable_rel_fun)
  assume "stable_rel a x"
  show "stabilize_rel a x = x"
  proof (rule ext)
    fix l show "stabilize_rel a x l = x l"
      by (metis \<open>stable_rel a x\<close> already_stable_rel stabilize_rel_fun stable_rel_fun)
  qed
next
  fix a b x y :: "'a \<Rightarrow> 'b :: sep_algebra"
  assume "Some x = a \<oplus> b"
  then show "Some (stabilize_rel y x) = stabilize_rel y a \<oplus> stabilize_rel y b"
    using plus_funE[of x a b] plus_funI[of "stabilize_rel y x" "stabilize_rel y a" "stabilize_rel y b"]
      stabilize_rel_all_sum stabilize_rel_fun[of y ]
    by fastforce
  show "Some (stabilize_rel u x) = stabilize_rel u a \<oplus> stabilize_rel a b"
    using  \<open>Some x = a \<oplus> b\<close> plus_funE[of x a b] plus_funI[of "stabilize_rel u x" "stabilize_rel u a" "stabilize_rel a b"]
      stabilize_rel_fun[of a] stabilize_rel_fun[of u] stabilize_rel_sum_double u_fun_def
    by fastforce
next
  fix a b x :: "'a \<Rightarrow> 'b :: sep_algebra"
  assume "a \<succeq> b"
  then show "stabilize_rel a x \<succeq> stabilize_rel b x"
    by (simp add: greaterE greaterI stabilize_rel_fun stabilize_rel_mono_left)
qed

end


context sep_algebra
begin

definition conj where
  "conj A B \<omega> \<longleftrightarrow> A \<omega> \<and> B \<omega>"

definition star where
  "star A B \<omega> \<longleftrightarrow> (\<exists>a b. A a \<and> B b \<and> Some \<omega> = a \<oplus> b)"

definition monotonic where
  "monotonic A \<longleftrightarrow> (\<forall>\<omega> \<omega>'. \<omega>' \<succeq> \<omega> \<and> A \<omega> \<longrightarrow> A \<omega>')"

definition non_overlapping where
  "non_overlapping A B \<longleftrightarrow> (\<forall>\<omega>. A \<omega> \<and> B \<omega> \<longrightarrow> (\<exists>a b. Some \<omega> = a \<oplus> b \<and> A a \<and> B b))"

lemma star_entails_and:
  assumes "star A B \<omega>"
      and "monotonic A"
      and "monotonic B"
    shows "conj A B \<omega>"
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) conj_def local.commutative local.greater_equiv monotonic_def star_def)
  

lemma and_entails_star:
  assumes "A \<omega>"
      and "B \<omega>"
      and "non_overlapping A B"
    shows "star A B \<omega>"
  using non_overlapping_def star_def[of A B \<omega>] assms(1) assms(2) assms(3) 
  by metis

end

end