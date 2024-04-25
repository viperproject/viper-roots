theory SepLogic
  imports SepAlgebra
begin

section \<open>Extending separation algebra with sets\<close>


subsection \<open>PCM\<close>

context pcm
begin
                                                         
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

definition under :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "under A \<omega> = { \<omega>' | \<omega>'. \<omega>' \<in> A \<and> \<omega> \<succeq> \<omega>'}"

lemma add_set_commm:
  "A \<otimes> B = B \<otimes> A"
proof -
  have "\<And>A B. A \<otimes> B \<subseteq> B \<otimes> A"
    using add_set_def local.commutative by fastforce
  then show ?thesis by blast
qed

lemma x_elem_set_product:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some x = a \<oplus> b)"
  using add_set_def by fastforce

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



lemma add_set_left_comm :
  "A \<otimes> (B \<otimes> C) = B \<otimes> (A \<otimes> C)"
  using add_set_asso add_set_commm by metis

lemmas add_setAC = add_set_asso add_set_commm add_set_left_comm

lemma add_set_ex_comm_r :
  "A \<otimes> (\<Union>x. B x) = (\<Union>x. A \<otimes> B x)"
  by (auto simp add:add_set_def)

lemma add_set_ex_comm_l :
  "(\<Union>x. A x) \<otimes> B  = (\<Union>x. A x \<otimes> B)"
  by (auto simp add:add_set_def)

lemma add_set_mono :
  assumes "A1 \<subseteq> A2"
  assumes "B1 \<subseteq> B2"
  shows "A1 \<otimes> B1 \<subseteq> A2 \<otimes> B2"
  using assms unfolding add_set_def by fastforce

lemma add_set_empty_l [simp] :
  "({} \<otimes> A) = {}"
  by (simp add:add_set_def)

lemma add_set_empty_r [simp] :
  "(A \<otimes> {}) = {}"
  by (simp add:add_set_def)

lemma star_to_singletonE :
  assumes "x \<in> A \<otimes> B"
  assumes "\<And> a. a \<in> A \<Longrightarrow> x \<in> {a} \<otimes> B \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp add:add_set_def)

lemma star_to_singletonI :
  assumes "a \<in> A"
  assumes "x \<in> {a} \<otimes> B"
  shows "x \<in> A \<otimes> B"
  using assms by (auto simp add:add_set_def)


lemma and_sep_comm :
  shows "(A \<inter> B) \<otimes> C = (A \<otimes> C) \<inter> (B \<otimes> C)"
  unfolding add_set_def
  oops

definition wand :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "--\<otimes>" 60) where
  "A --\<otimes> B = { x. \<forall> a b. a \<in> A \<longrightarrow> Some b = a \<oplus> x \<longrightarrow> b \<in> B}"

lemma wand_apply :
  "A \<otimes> (A --\<otimes> B) \<subseteq> B"
  unfolding add_set_def wand_def by (auto)

lemma wand_empty [simp] :
  "({} --\<otimes> B) = UNIV"
  unfolding wand_def by (auto)



definition up_close :: "'a set \<Rightarrow> 'a set" where
  "up_close A = A \<otimes> UNIV"

lemma up_close_sum : 
  "up_close A \<otimes> B = up_close (A \<otimes> B)"
  by (simp add:up_close_def add_setAC)

lemma up_close_empty [simp] :
  "up_close {} = {}"
  by (simp add:up_close_def)


lemma sep_and_pers :
  assumes "\<And> \<omega>. \<omega> \<in> B \<Longrightarrow> |\<omega>| \<in> B"
  (* probably B needs to be up_closed as well*)
  shows "A \<otimes> B = up_close (A \<inter> B)"
  using assms unfolding up_close_def
   apply (auto)
   sorry


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





subsection \<open>PCM with core\<close>

context pcm_with_core
begin

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

definition emp_core :: "'a set" where
  "emp_core = {a. pure a }"

definition corely :: "'a set \<Rightarrow> 'a set" where
  "corely A = A \<inter> emp_core"

definition up_close_core :: "'a set \<Rightarrow> 'a set" where
  "up_close_core A = A \<otimes> emp_core"

lemma up_close_core_sum : 
  "up_close_core A \<otimes> B = up_close_core (A \<otimes> B)"
  by (simp add:up_close_core_def add_setAC)

lemma up_close_core_empty [simp] :
  "up_close_core {} = {}"
  by (simp add:up_close_core_def)

lemma in_up_close_core_decompose:
  assumes "x \<in> up_close_core A"
  shows "\<exists>a p. a \<in> A \<and> pure p \<and> Some x = a \<oplus> p"
  using assms emp_core_def local.x_elem_set_product up_close_core_def by auto

lemma prove_in_up_close_core:
  assumes "Some x = a \<oplus> p"
      and "a \<in> A"
      and "pure p"
    shows "x \<in> up_close_core A"
  using assms(1) assms(2) assms(3) emp_core_def local.x_elem_set_product up_close_core_def by auto

lemma corely_eq_def:
  "corely A = Set.filter pure A" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    using corely_def emp_core_def by force
  show "?B \<subseteq> ?A"
    using corely_def emp_core_def by force
qed

lemma stabilize_in_up_close_core :
   "stabilize x \<in> up_close_core A \<longleftrightarrow> stabilize x \<in> A" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain a p where "a \<in> A" "Some (stabilize x) = a \<oplus> p" "pure p"
    using pcm_with_core_class.in_up_close_core_decompose by blast
  then show ?B
    using stabilize_is_stable stable_and_sum_pure_same by blast
next
  assume ?B
  moreover have "Some (stabilize x) = stabilize x \<oplus> |stabilize x|"
    by (simp add: pcm_with_core_class.core_is_smaller)
  ultimately show ?A
    by (simp add: pcm_class.pure_def pcm_with_core_class.core_is_pure pcm_with_core_class.prove_in_up_close_core)
qed

lemma stable_in_up_close_core [simp] :
  assumes "stable \<omega>"
  shows "\<omega> \<in> up_close_core A \<longleftrightarrow> \<omega> \<in> A"
  by (metis already_stable assms stabilize_in_up_close_core)

lemma up_close_core_id :
  "A \<subseteq> up_close_core A"
  apply (simp add:up_close_core_def emp_core_def)
  using emp_core_def local.core_is_smaller local.max_projection_prop_pure_core local.mpp_prop prove_in_up_close_core up_close_core_def by fastforce


lemma sep_and_corely :
  assumes "\<And> \<omega>. \<omega> \<in> B \<Longrightarrow> |\<omega>| \<in> B"
  assumes "up_closed B"
  assumes "A \<subseteq> B"
  shows "A \<otimes> corely B = up_close_core A" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (simp add: corely_def local.add_set_mono up_close_core_def)
  show "?B \<subseteq> ?A"
  proof
    fix x assume "x \<in> ?B"
    then obtain a p where "a \<in> A \<and> pure p \<and> Some x = a \<oplus> p"
      using in_up_close_core_decompose by blast
    then obtain ap where "Some ap = |a| \<oplus> p"
      by (metis local.compatible_smaller local.max_projection_prop_def local.max_projection_prop_pure_core)
    then have "ap \<in> B"
      by (metis \<open>a \<in> A \<and> pure p \<and> Some x = a \<oplus> p\<close> \<open>x \<in> up_close_core A\<close> assms(1) assms(2) assms(3) local.cancellative local.core_is_smaller local.core_sum local.in_set_sum local.max_projection_prop_pure_core local.mpp_invo local.pure_def local.up_closed_def option.inject subsetD up_close_core_def)
    then have "ap \<in> corely B"
      by (metis Int_iff \<open>Some ap = |a| \<oplus> p\<close> \<open>a \<in> A \<and> pure p \<and> Some x = a \<oplus> p\<close> corely_def emp_core_def local.max_projection_prop_pure_core local.mpp_prop local.pure_stable mem_Collect_eq)
    moreover have "Some x = a \<oplus> ap"
      by (metis \<open>Some ap = |a| \<oplus> p\<close> \<open>a \<in> A \<and> pure p \<and> Some x = a \<oplus> p\<close> local.asso1 local.core_is_smaller)
    ultimately show "x \<in> ?A"
      using \<open>a \<in> A \<and> pure p \<and> Some x = a \<oplus> p\<close> local.add_set_elem by blast
  qed
qed

lemma sep_and_corely1 :
  assumes "\<And> \<omega>. \<omega> \<in> B \<Longrightarrow> |\<omega>| \<in> B"
  assumes "up_closed B"
  shows "A \<otimes> corely B = up_close_core A \<inter> B"
  using assms
  unfolding corely_def up_close_core_def

  unfolding  add_set_def emp_core_def up_close_core_def up_close_def
  apply (auto)
  subgoal for x a b
    using greater_equiv up_closed_def by blast
  subgoal for x a b
    apply (rule exI[of _ a], safe)
    by (metis local.asso1 local.commutative local.core_is_pure local.max_projection_prop_pure_core local.minusI local.minus_equiv_def_any_elem local.mpp_smaller local.pure_def)
  done

(*
lemma sep_and_corely2 :
  assumes "\<And> \<omega>. \<omega> \<in> B \<Longrightarrow> |\<omega>| \<in> B"
  assumes "up_closed B"
  shows "A \<otimes> corely B = up_close_core (A \<inter> B)"
  using assms
  unfolding corely_def up_close_core_def

  unfolding  add_set_def emp_core_def up_close_core_def up_close_def
  apply (auto)
  subgoal for x a b
    sorry

    (* using greater_equiv up_closed_def by blast *)
  (* subgoal for x a b *)
    (* apply (rule exI[of _ a], safe) *)
    (* by (smt (verit, ccfv_threshold) asso1 core_is_smaller core_sum max_projection_prop_pure_core mpp_invo) *)
    oops
*)

end





subsection \<open>Separation algebra\<close>

context sep_algebra
begin

lemma stabilize_minus_pure :
  "stabilize (x \<ominus> |a| ) = stabilize x"
  by (metis commutative minus_default minus_equiv_def plus_pure_stabilize_eq)

definition emp :: "'a set" where
"emp = {a. \<exists> b. a = stabilize |b| }"

lemma emp_star_right_id [simp] :
  "A \<otimes> emp = A"
  apply (clarsimp simp add:emp_def add_set_def)
  using stabilize_core_emp stabilize_core_right_id by (fastforce)

lemma emp_star_left_id [simp] :
  "emp \<otimes> A = A"
  by (simp add:add_set_commm)

lemma wand_emp [simp] :
  "(emp --\<otimes> B) = B"
  unfolding wand_def emp_def apply (auto)
   apply (metis commutative stabilize_core_right_id)
  by (metis commutative stabilize_core_emp)

definition bool_to_assertion :: "bool \<Rightarrow> 'a set" ("\<llangle>_\<rrangle>" [0] 81) where
"bool_to_assertion b = (if b then emp else {})"

lemma bool_to_assertion_split :
  "P (\<llangle>Q\<rrangle>) = ((Q \<longrightarrow> P emp) \<and> (\<not> Q \<longrightarrow> P {}))"
  by (simp add:bool_to_assertion_def)

lemma bool_to_assertion_split_asm: "P (\<llangle>Q\<rrangle>) = (\<not> ((Q \<and> \<not> P emp) \<or> (\<not> Q \<and> \<not> P {})))"
  by (simplesubst bool_to_assertion_split) blast

lemmas bool_to_assertion_splits = bool_to_assertion_split bool_to_assertion_split_asm

lemma bool_to_assertion_in [simp] :
  "\<omega> \<in> \<llangle>P\<rrangle> \<longleftrightarrow> P \<and> \<omega> \<in> emp"
  by (simp add:bool_to_assertion_def)

lemma bool_to_assertion_true [simp]:
  assumes "P"
  shows "\<llangle>P\<rrangle> = emp"
  using assms by (simp split:bool_to_assertion_splits)
  
lemma bool_to_assertion_false [simp]:
  assumes "\<not> P"
  shows "\<llangle>P\<rrangle> = {}"
  using assms by (simp split:bool_to_assertion_splits)
  









definition Stabilize :: "'a set \<Rightarrow> 'a set" where
  "Stabilize A = {\<omega>. stabilize \<omega> \<in> A}"

lemma in_Stabilize[simp] :
  "\<omega> \<in> Stabilize A \<longleftrightarrow> stabilize \<omega> \<in> A"
  by (simp add:Stabilize_def)

lemma Stabilize_filter_stable :
  "Set.filter sep_algebra_class.stable A \<subseteq> Stabilize A"
  by (auto simp add:Stabilize_def already_stable)

lemma Stabilize_star : 
  "Stabilize A \<otimes> Stabilize B \<subseteq> Stabilize (A \<otimes> B)"
  apply (simp add:Stabilize_def add_set_def)
  using stabilize_sum by blast

lemma Stabilize_UNIV [simp] : 
  "Stabilize UNIV = UNIV"
  by (simp add:Stabilize_def)

lemma Stabilize_empty [simp] : 
  "Stabilize {} = {}"
  by (simp add:Stabilize_def)

(* lemma Stabilize_emp [simp] :  *)
  (* "Stabilize emp = emp" *)
  (* unfolding emp_def Stabilize_def *)
  (* apply (simp; safe) *)
  
  (* by (auto) *)

lemma Stabilize_ex :
  "Stabilize (\<Union> x. A x) = (\<Union> x. Stabilize (A x))"
  by (auto simp add:Stabilize_def)

lemma Stabilize_up_close_core : 
  "Stabilize (up_close_core A) = Stabilize A" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    using local.in_up_close_core_decompose local.max_projection_prop_stable_stabilize local.mpp_prop local.stable_and_sum_pure_same by fastforce
  show "?B \<subseteq> ?A"
    using local.up_close_core_id by force
qed

definition Stable :: "'a set \<Rightarrow> bool" where
  "Stable A \<longleftrightarrow> (A \<subseteq> Stabilize A)"

lemma StableI :
  assumes "\<And> x. x \<in> A \<Longrightarrow> stabilize x \<in> A"
  shows "Stable A"
  using assms by (auto simp add:Stable_def)

lemma Stable_UNIV [simp] : 
  "Stable UNIV"
  by (simp add:Stable_def)

lemma Stable_emp [simp] : 
  "Stable emp"
  unfolding Stable_def Stabilize_def emp_def
  using already_stable stabilize_is_stable by blast

lemma Stable_emp_core [simp] :
  "Stable emp_core"
  unfolding Stable_def Stabilize_def emp_core_def
  using local.max_projection_prop_def local.max_projection_prop_stable_stabilize local.pure_smaller by force


lemma Stable_empty [simp] : 
  "Stable {}"
  by (simp add:Stable_def)

lemma Stable_bool_to_assertion [simp] : 
  "Stable (\<llangle>P\<rrangle>)"
  by (simp split:bool_to_assertion_splits)

lemma Stable_star :
  assumes "Stable A"
  assumes "Stable B"
  shows "Stable (A \<otimes> B)"
  unfolding Stable_def 
proof -
  have "A \<otimes> B \<subseteq> Stabilize A \<otimes> Stabilize B"
    using assms unfolding Stable_def by (rule add_set_mono)
  also have "... \<subseteq> Stabilize (A \<otimes> B)"
    by (rule Stabilize_star)
  finally show "A \<otimes> B \<subseteq> Stabilize (A \<otimes> B)" .
qed

lemma Stable_up_close :
  "Stable A \<Longrightarrow> Stable (up_close A)"
  apply (simp add: up_close_def)
  apply (rule Stable_star)
  by (simp_all)

lemma Stable_up_close_core :
  "Stable A \<Longrightarrow> Stable (up_close_core A)"
  apply (simp add: up_close_core_def)
  apply (rule Stable_star)
  by (simp_all)

lemma Stable_up_close_core_rev :
  "Stable (up_close_core A) \<Longrightarrow> Stable A"
  apply (simp add:Stable_def Stabilize_up_close_core)
  using up_close_core_id by blast

lemma Stable_up_close_core_eq :
  "Stable (up_close_core A) = Stable A"
  using Stable_up_close_core Stable_up_close_core_rev by blast

lemma Stable_ex :
  assumes "\<And> x. Stable (A x)"
  shows "Stable (\<Union> x. A x)"
  using assms unfolding Stable_def by (auto simp add:Stabilize_ex)

lemma Stable_singleton [simp] :
  "Stable {\<omega>} = stable \<omega>"
  unfolding Stable_def Stabilize_def
  by (metis already_stable bot.extremum in_Stabilize insertI1 insert_subset singletonD Stabilize_def stabilize_is_stable)

lemma split_star_singleton_stabilize :
  "{\<omega>} = {stabilize \<omega>} \<otimes> {|\<omega>|}"
  by (simp add:sum_then_singleton[symmetric] decompose_stabilize_pure)

lemma star_to_singleton_stableE :
  assumes "x \<in> A \<otimes> B"
  assumes "stable x"
  assumes "Stable A"
  assumes "\<And> a. a \<in> A \<Longrightarrow> stable a \<Longrightarrow> x \<in> {a} \<otimes> B \<Longrightarrow> P"
  shows "P"
proof -
  obtain a where "a \<in> A" "x \<in> {a} \<otimes> B"
    using star_to_singletonE assms by blast
  from \<open>x \<in> {a} \<otimes> B\<close> have "x \<in> up_close_core ({stabilize a} \<otimes> B)" 
    (* This proof is a lot more painful than it should be. *)
    apply (simp add:split_star_singleton_stabilize[of "a"])
    apply (simp add:add_set_commm[of "{stabilize a}"] add_set_asso)
    apply (simp add:up_close_core_def add_set_commm[of _ emp_core])
    apply (simp add:emp_core_def)
    apply (rule set_mp[OF add_set_mono])
      prefer 3 apply (assumption)
    apply (simp add: local.max_projection_prop_pure_core local.mpp_prop)
    by blast
  show "?thesis"
    apply (rule assms(4)[of "stabilize a"])
    subgoal using assms Stable_def \<open>a \<in> A\<close> in_Stabilize by blast
    subgoal by (simp add: stabilize_is_stable)
    using \<open>x \<in> up_close_core ({stabilize a} \<otimes> B)\<close> assms
    using local.in_up_close_core_decompose local.stable_and_sum_pure_same by blast
qed

lemma Stable_star_singleton :
  assumes "Stable A"
  assumes "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> stable \<omega> \<Longrightarrow> Stable ({\<omega>} \<otimes> B)"
  shows "Stable (A \<otimes> B)"
proof (rule StableI)
  fix x assume "x \<in> A \<otimes> B"
  (* TODO: use star_to_singleton_stableE to simplify this proof? *)
  then obtain a where "x \<in> {a} \<otimes> B" "a \<in> A" using star_to_singletonE by blast
  then have "Stable ({stabilize a} \<otimes> B)" using stabilize_is_stable Stable_def assms in_Stabilize by blast
  from \<open>x \<in> {a} \<otimes> B\<close> have "x \<in> up_close_core ({stabilize a} \<otimes> B)"
    (* This proof is a lot more painful than it should be. *)
    apply (simp add:split_star_singleton_stabilize[of "a"])
    apply (simp add:add_set_commm[of "{stabilize a}"] add_set_asso)
    apply (simp add:up_close_core_def add_set_commm[of _ emp_core])
    apply (simp add:emp_core_def)
    apply (rule set_mp[OF add_set_mono])
      prefer 3 apply (assumption)
    apply (simp add: local.core_is_pure local.pure_def)
    by blast
  then have "stabilize x \<in> {stabilize a} \<otimes> B" 
    using Stable_def \<open>Stable ({stabilize a} \<otimes> B)\<close>
    using Stabilize_up_close_core Stable_up_close_core
    by (metis in_Stabilize subsetD)
  show "stabilize x \<in> A \<otimes> B"
    apply (rule star_to_singletonI[of "stabilize a"])
    using assms(1) \<open>a \<in> A\<close> Stable_def apply (fastforce)
    by (rule \<open>stabilize (x) \<in> {stabilize a} \<otimes> B\<close>)
qed


(*
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
*)

end

end