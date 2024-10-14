theory AbstractSemanticsProperties
  imports AbstractSemantics
begin

context typed_state
begin


lemma exists_assertI:
  assumes "v0 \<in> ty"
      and "get_store \<omega> x = Some v0"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
      and "assign_var_state x (Some v) \<omega> \<in> A"
    shows "\<omega> \<in> exists_assert \<Delta> x A"
  using assms
  unfolding exists_assert_def assign_var_state_def by fast

lemma exists_assertE:
  assumes "\<omega> \<in> exists_assert \<Delta> x A"
  shows "\<exists>v0 v ty. v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (assign_var_state x (Some v) \<omega>) \<in> A"
  using assms
  unfolding exists_assert_def assign_var_state_def
  by blast

lemma stabilize_assign_var:
  "stabilize (assign_var_state x v \<omega>) = assign_var_state x v (stabilize \<omega>)"
  unfolding assign_var_state_def by auto

lemma self_framing_exists_assert:
  assumes "self_framing A"
  shows "self_framing (exists_assert \<Delta> x A)"
proof (rule self_framingI)
  fix \<omega>
  show "\<omega> \<in> exists_assert \<Delta> x A \<longleftrightarrow> stabilize \<omega> \<in> exists_assert \<Delta> x A" (is "?A \<longleftrightarrow> ?B")
  proof
    assume "\<omega> \<in> exists_assert \<Delta> x A"
    then obtain v v0 ty where r: "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (assign_var_state x (Some v) \<omega>) \<in> A"
      unfolding exists_assert_def assign_var_state_def by blast
    then have "get_store (stabilize \<omega>) x = Some v0 \<and> set_store (stabilize \<omega>) ((get_store (stabilize \<omega>))(x \<mapsto> v)) = stabilize (assign_var_state x (Some v) \<omega>)"
      by (simp add: assign_var_state_def)
    then show ?B
      by (smt (verit, ccfv_SIG) \<open>\<omega> \<in> exists_assert \<Delta> x A\<close> assms exists_assertI r self_framing_def stabilize_assign_var typed_state.exists_assertE typed_state_axioms typed_then_stabilize_typed)

  next
    assume asm1: ?B
    then obtain v v0 ty where r: "v0 \<in> ty" "get_store (stabilize \<omega>) x = Some v0"
      "variables \<Delta> x = Some ty" "v \<in> ty" "assign_var_state x (Some v) (stabilize \<omega>) \<in> A"
      by (metis exists_assertE)
    show ?A
      using r(1)
    proof (rule exists_assertI)
      show "get_store \<omega> x = Some v0"
        using r(2) by auto
      show "assign_var_state x (Some v) \<omega> \<in> A"
        by (metis assms in_Stabilize r(5) self_framing_eq stabilize_assign_var)
    qed (simp_all add: r)
  qed
qed

lemma store_typed_update:
  assumes "store_typed vars \<sigma>"
      and "vars x = Some ty"
      and "v \<in> ty"
    shows "store_typed vars (\<sigma>(x \<mapsto> v))"
  by (simp add: assms(1) assms(2) assms(3) store_typed_insert)


lemma typed_store_update:
  assumes "typed_store \<Delta> \<sigma>"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
    shows "typed_store \<Delta> (\<sigma>(x \<mapsto> v))"
  unfolding typed_store_def
  by (meson assms(1) assms(2) assms(3) store_typed_update typed_store_def)


(*

definition equal_on_set :: "var set \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "equal_on_set S \<sigma>1 \<sigma>2 \<longleftrightarrow> (\<forall>x \<in> S. \<sigma>1 x = \<sigma>2 x)"

definition overapprox_fv :: "('v, 'c) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> var set \<Rightarrow> bool" where
  "overapprox_fv \<Delta> A S \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2 \<gamma>. typed_store \<Delta> \<sigma>1 \<and> typed_store \<Delta> \<sigma>2 \<and> equal_on_set S \<sigma>1 \<sigma>2 \<longrightarrow> ((Ag \<sigma>1, \<gamma>) \<in> A \<longleftrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A))"


definition free_vars where
  "free_vars A = (\<Inter>S \<in> {S. overapprox_fv \<Delta> A S \<and> S \<subseteq> dom (variables \<Delta>)}. S)"
*)

lemma fvaA_atrue_empty[simp]:
  "free_vars \<Delta> UNIV = {}"
proof -
  have "overapprox_fv \<Delta> UNIV {}"
    unfolding overapprox_fv_def
    by blast
  then show ?thesis unfolding free_vars_def by blast
qed



(* Free variables *)


section \<open>Free variables\<close>

definition finite_context where
  "finite_context \<Delta> \<longleftrightarrow> (finite (dom (variables \<Delta>)))"

lemma equal_on_setI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<sigma>1 x = \<sigma>2 x"
  shows "equal_on_set S \<sigma>1 \<sigma>2"
  using assms equal_on_set_def by blast


lemma equal_on_set_inter:
  assumes "equal_on_set S' \<sigma>1 \<sigma>2"
      and "S \<subseteq> S'"
    shows "equal_on_set S \<sigma>1 \<sigma>2"
  by (meson assms(1) assms(2) equal_on_set_def in_mono)

lemma equal_on_set_symmetric:
  "equal_on_set S \<sigma>1 \<sigma>2 \<longleftrightarrow> equal_on_set S \<sigma>2 \<sigma>1"
  using equal_on_set_def 
  by metis

lemma overapprox_fvI:
  assumes "\<And>\<sigma>1 \<sigma>2 \<gamma>. typed \<Delta> (Ag \<sigma>1, \<gamma>) \<Longrightarrow> typed \<Delta> (Ag \<sigma>2, \<gamma>) \<Longrightarrow> equal_on_set S \<sigma>1 \<sigma>2 \<Longrightarrow> (Ag \<sigma>1, \<gamma>) \<in> A \<Longrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A"
  shows "overapprox_fv \<Delta> A S"
  using assms equal_on_set_symmetric overapprox_fv_def by blast

lemma overapprox_fvE:
  assumes "overapprox_fv \<Delta> A S"
      and "equal_on_set S \<sigma>1 \<sigma>2"
      and "(Ag \<sigma>1, \<gamma>) \<in> A"
      and "typed \<Delta> (Ag \<sigma>1, \<gamma>)"
      and "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
    shows "(Ag \<sigma>2, \<gamma>) \<in> A"
  using assms overapprox_fv_def by blast

lemma intermediate_equal_set:
  assumes "equal_on_set (S1 \<inter> S2) \<sigma>1 \<sigma>2"
      and "typed_store \<Delta> \<sigma>1"
      and "typed_store \<Delta> \<sigma>2"
  shows "\<exists>\<sigma>3. equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2 \<and> typed_store \<Delta> \<sigma>3"
proof -
  let ?\<sigma>3 = "(\<lambda>x. if x \<in> S1 then \<sigma>1 x else \<sigma>2 x)"
  have "equal_on_set S1 \<sigma>1 ?\<sigma>3"
    by (simp add: equal_on_set_def)
  moreover have "equal_on_set S2 ?\<sigma>3 \<sigma>2" (* Needs a case split on x *)
    by (smt (verit) IntI agreement.sel assms equal_on_set_def)
  moreover have "typed_store \<Delta> ?\<sigma>3"
    apply (rule typed_storeI)
     apply (smt (verit, del_insts) Collect_cong assms(2) assms(3) dom_def mem_Collect_eq store_typed_def typed_store_def)
    apply (case_tac "x \<in> S1")
     apply (meson assms(2) store_typed_def typed_store_def)
    by (meson assms(3) store_typed_def typed_store_def)
  ultimately show ?thesis
    by blast
qed


lemma stable_by_intersection_overapprox_fv:
  assumes "overapprox_fv \<Delta> A S1"
      and "overapprox_fv \<Delta> A S2"
    shows "overapprox_fv \<Delta> A (S1 \<inter> S2)"
proof (rule overapprox_fvI)
  fix \<sigma>1 \<sigma>2 \<gamma>
  assume asm0: "equal_on_set (S1 \<inter> S2) \<sigma>1 \<sigma>2" "(Ag \<sigma>1, \<gamma>) \<in> A" "typed \<Delta> (Ag \<sigma>1, \<gamma>)" "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
  then obtain \<sigma>3 where "equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2" "typed_store \<Delta> \<sigma>3"
    unfolding typed_def
    using intermediate_equal_set[of S1 S2 \<sigma>1 \<sigma>2]
    by (metis agreement.sel fst_conv get_store_def)
  then have "(Ag \<sigma>3, \<gamma>) \<in> A"
    by (metis agreement.sel asm0(2) asm0(3) assms(1) fst_conv get_abs_state_def get_store_def overapprox_fvE snd_conv typed_state.typed_def typed_state_axioms)
  then show "(Ag \<sigma>2, \<gamma>) \<in> A"
    by (metis \<open>equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2\<close> \<open>typed_store \<Delta> \<sigma>3\<close> agreement.sel asm0(4) assms(2) fst_conv get_abs_state_def get_store_def overapprox_fvE snd_conv typed_state.typed_def typed_state_axioms)
qed

lemma finite_family_property_aux:
  assumes "finite F"
      and "\<And>S. S \<in> F \<Longrightarrow> P S"
      and "\<And>S1 S2. P S1 \<Longrightarrow> P S2 \<Longrightarrow> P (S1 \<inter> S2)"
      and "card F = n + 1"
    shows "P (\<Inter>S \<in> F. S)"
  using assms
proof (induct n arbitrary: F)
  case 0
  then show ?case
    by (metis Inf_empty Inf_insert One_nat_def Suc_eq_plus1 card_1_singletonE image_ident inf_top.right_neutral insert_iff)
next
  case (Suc n)
  then obtain S where "S \<in> F"
    by (metis One_nat_def Suc_eq_plus1 card_le_Suc0_iff_eq le_add1 not_less_eq_eq plus_1_eq_Suc)
  then have "P (\<Inter>S \<in> (F - {S}). S)"
    using Suc(1)[of "F - {S}"]
    using Suc.prems(1) Suc.prems(2) Suc.prems(4) assms(3) by auto
  then show ?case
    by (metis Inf_insert Suc.prems(2) \<open>S \<in> F\<close> assms(3) image_ident insert_Diff)
qed

lemma finite_family_property:
  assumes "finite F"
      and "\<And>S. S \<in> F \<Longrightarrow> P S"
      and "\<And>S1 S2. P S1 \<Longrightarrow> P S2 \<Longrightarrow> P (S1 \<inter> S2)"
      and "F \<noteq> {}"
    shows "P (\<Inter>S \<in> F. S)"
proof -
  have "card F \<ge> 1"
    by (simp add: Suc_leI assms(1) assms(4) card_gt_0_iff)
  then show ?thesis
    by (metis add.commute assms(1) assms(2) assms(3) finite_family_property_aux le_Suc_ex)
qed


lemma family_of_sets_included_in_finite_set_is_finite:
  assumes "finite S"
      and "\<And>S'. S' \<in> F \<Longrightarrow> S' \<subseteq> S"
    shows "finite F"
  by (meson Sup_least assms(1) assms(2) finite_UnionD finite_subset)

lemma free_vars_exists_finite:
  assumes "finite S"
      and "overapprox_fv \<Delta> A S"
    shows "overapprox_fv \<Delta> A (free_vars \<Delta> A)"
proof -
  let ?F = "{S'. S' \<subseteq> S \<and> overapprox_fv \<Delta> A S'}"

  have "overapprox_fv \<Delta> A (\<Inter>S\<in>?F. S)"
    using finite_family_property[of ?F "overapprox_fv \<Delta> A"]
    by (metis (mono_tags, lifting) assms dual_order.refl empty_iff family_of_sets_included_in_finite_set_is_finite mem_Collect_eq stable_by_intersection_overapprox_fv)
  moreover have "\<And>S'. overapprox_fv \<Delta> A S' \<Longrightarrow> (\<Inter>S\<in>?F. S) \<subseteq> S'"
  proof -
    fix S' assume "overapprox_fv \<Delta> A S'"
    then have "S \<inter> S' \<in> ?F"
      by (simp add: assms(2) stable_by_intersection_overapprox_fv)
    then show "(\<Inter>S\<in>?F. S) \<subseteq> S'"
      by blast
  qed
  ultimately show ?thesis
    by (smt (verit, best) INT_greatest Inf_lower free_vars_def image_ident mem_Collect_eq subset_antisym)
qed

lemma typed_and_equal_store:
  assumes "typed_store \<Delta> \<sigma>1"
      and "typed_store \<Delta> \<sigma>2"
      and "equal_on_set (dom (variables \<Delta>)) \<sigma>1 \<sigma>2"
    shows "\<sigma>1 = \<sigma>2"
  apply (rule ext)
  apply (case_tac "x \<in> dom (variables \<Delta>)")
   apply (meson assms(3) equal_on_set_def)
  by (metis assms(1) assms(2) domIff store_typed_def typed_store_def)

lemma finite_context_then_fv_works:
  assumes "finite_context \<Delta>"
  shows "\<exists>V. finite V \<and> overapprox_fv \<Delta> S V"
proof -
  have "overapprox_fv \<Delta> S (dom (variables \<Delta>))"
  proof (rule overapprox_fvI)
    fix \<sigma>1 \<sigma>2 \<gamma>
    assume asm0: "typed \<Delta> (Ag \<sigma>1, \<gamma>)" "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
      "equal_on_set (dom (variables \<Delta>)) \<sigma>1 \<sigma>2" "(Ag \<sigma>1, \<gamma>) \<in> S"
    then have "\<sigma>1 = \<sigma>2"
      by (metis agreement.sel fst_conv get_store_def typed_and_equal_store typed_def)
    then show "(Ag \<sigma>2, \<gamma>) \<in> S"
      using asm0(4) by blast
  qed
  then show ?thesis
    using assms finite_context_def by blast
qed

lemma free_vars_overapprox_wf_context:
  assumes "finite_context \<Delta>"
  shows "overapprox_fv \<Delta> A (free_vars \<Delta> A)"
  by (meson assms free_vars_exists_finite finite_context_then_fv_works)

lemma free_vars_agree:
  assumes "equal_on_set (free_vars \<Delta> A) \<sigma>1 \<sigma>2"
      and "finite_context \<Delta>"
      and "typed \<Delta> (Ag \<sigma>1, \<gamma>)"
      and "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
    shows "((Ag \<sigma>1, \<gamma>) \<in> A \<longleftrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A)"
  using assms(1) assms(2) assms(3) assms(4) free_vars_overapprox_wf_context overapprox_fv_def by blast

lemma free_varsE:
  assumes "equal_on_set (free_vars \<Delta> A) \<sigma>1 \<sigma>2"
      and "(Ag \<sigma>1, \<gamma>) \<in> A"
      and "finite_context \<Delta>"
      and "typed \<Delta> (Ag \<sigma>1, \<gamma>)"
      and "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
    shows "(Ag \<sigma>2, \<gamma>) \<in> A"
  using assms(1) assms(2) assms(3) assms(4) assms(5) free_vars_agree by blast

end








context semantics
begin

section \<open>Properties of the semantics: States are always wf_state\<close>


lemma red_seq_equiv:
  "(\<exists>S1. red_stmt \<Delta> C1 \<omega> S1 \<and> sequential_composition \<Delta> S1 C2 S2) \<longleftrightarrow> red_stmt \<Delta> (Seq C1 C2) \<omega> S2" (is "?A \<longleftrightarrow> ?B")
proof
  assume "red_stmt \<Delta> (Seq C1 C2) \<omega> S2"
  then show ?A
    by (meson red_stmt_Seq_elim)
next
  assume ?A
  then show ?B
    by (meson RedSeq)
qed

thm red_stmt_sequential_composition.inducts(1)[of \<Delta> C \<omega> S "\<lambda>\<Delta> C \<omega> S. P \<omega> \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<omega>')" "\<lambda>\<Delta> S C S'. (\<forall>\<omega>\<in>S. P \<omega>) \<longrightarrow> (\<forall>\<omega>\<in>S'. P \<omega>)"]

lemma red_stmt_induct_simple [consumes 3, case_names Inhale Exhale Custom Havoc LocalAssign Label]:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "P \<Delta> \<omega>"
      and "\<omega>' \<in> S"
      and "\<And>(A :: ('v, 'a) abs_state assertion) \<omega>' \<omega> \<Delta> a.
        rel_stable_assertion \<omega> A \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>a (A :: ('v, 'a) abs_state assertion) \<omega> \<omega>' \<Delta>. a \<in> A \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> C \<omega> S \<omega>'. P \<Delta> \<omega> \<Longrightarrow> red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> x ty \<omega> v. variables \<Delta> x = Some ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> e \<omega> v x ty. variables \<Delta> x = Some ty \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> l \<omega>. P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_abs_state \<omega>))))"
  shows "P \<Delta> \<omega>'"
  using assms(1)
proof -
  have "P \<Delta> \<omega> \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')"
    using assms(1)
  proof (induct rule: red_stmt_sequential_composition.inducts(1)[of \<Delta> C \<omega> S "\<lambda>\<Delta> C \<omega> S. P \<Delta> \<omega> \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')" "\<lambda>\<Delta> S C S'. (\<forall>\<omega>\<in>S. P \<Delta> \<omega>) \<longrightarrow> (\<forall>\<omega>\<in>S'. P \<Delta> \<omega>)"])
    case (RedInhale \<omega> A \<Delta>)
    then show ?case using assms
      by (smt (verit, ccfv_SIG) member_filter singletonD x_elem_set_product)
  next
    case (RedExhale a A \<omega> \<omega>' \<Delta>)
    then show ?case using assms(5) by blast
  next
    case (RedLocalAssign \<Delta> x ty e \<omega> v)
    then show ?case
      using assms(8) by (simp)
  next
    case (RedHavoc \<Delta> x ty \<omega>)
    then show ?case
      by (auto simp add: assms(7))
  next
    case (RedCustom \<Delta> C \<omega> S)
    then show ?case
      using assms(6) by blast
  qed (blast+)
  then show ?thesis
    using assms(2) assms(3) by blast
qed


lemma stable_snd:
  fixes \<omega> :: "('d agreement \<times> 'f agreement) \<times> ('e :: sep_algebra)"
  shows "stable \<omega> \<longleftrightarrow> (stable (snd \<omega>))"
  using stable_prod_def stable_agreement_def
  by metis

lemma red_stable:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "stable \<omega>"
      and "\<omega>' \<in> S"
    shows "stable \<omega>'"
  using assms
proof (induct rule: red_stmt_induct_simple)
  case (Custom \<Delta> C \<omega> S \<omega>')
  then show ?case using red_custom_stable[of \<Delta> C \<omega> S \<omega>'] by simp
next
  case (Havoc \<Delta> x ty \<omega> v)
  then show "sep_algebra_class.stable (assign_var_state x (Some v) \<omega>)"
    by (metis (no_types, lifting) assign_var_state_def max_projection_prop_stable_stabilize mppI mpp_smaller set_store_stabilize stabilize_is_stable succ_refl)
next
  case (LocalAssign \<Delta> e \<omega> v x)
  then show ?case
    by (metis already_stable assign_var_state_def set_store_stabilize stabilize_is_stable)
qed (blast)

lemma red_well_typed:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "typed_store \<Delta> (get_store \<omega>)"
      and "\<omega>' \<in> S"
    shows "typed_store \<Delta> (get_store \<omega>')"
  using assms
proof (induct rule: red_stmt_induct_simple)
  case (Custom \<Delta> C \<omega> S \<omega>')
  then show ?case using red_custom_typed_store
    by blast
next
  case (Inhale A \<omega>' \<omega> \<Delta>)
  then show ?case
    by (simp add: full_add_charact(1))
next
  case (Exhale a A \<omega> \<omega>' \<Delta>)
  then show ?case
    by (simp add: full_add_charact(1))
next
  case (Havoc \<Delta> x ty \<omega> v)
  show ?case
  proof (rule typed_storeI)
    show "dom (variables \<Delta>) = dom (get_store (assign_var_state x (Some v) \<omega>))"
      by (metis Havoc.hyps(1) Havoc.hyps(2) assign_var_state_def dom_fun_upd get_store_set_store insert_dom option.discI typed_store_def store_typed_def)
    fix x' v' ty' assume asm0: "get_store (assign_var_state x (Some v) \<omega>) x' = Some v'" "variables \<Delta> x' = Some ty'"
    then show "v' \<in> ty'"
      by (metis Havoc.hyps(1) Havoc.hyps(2) Havoc.hyps(3) assign_var_state_def fun_upd_other fun_upd_same get_store_set_store option.inject typed_store_def store_typed_def)
  qed
next
  case (LocalAssign \<Delta> e \<omega> v x ty)
  then show "typed_store \<Delta> (get_store (assign_var_state x (Some v) \<omega>))"
    unfolding typed_store_def store_typed_def assign_var_state_def by auto
qed (auto)

lemma red_stmt_induct_simple_wf [consumes 4, case_names Inhale Exhale Custom Havoc LocalAssign Label]:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "P \<Delta> \<omega>"
      and "wf_abs_stmt \<Delta> C"
      and "\<omega>' \<in> S"
      and "\<And>(A :: ('v, 'a) abs_state assertion) \<omega>' \<omega> \<Delta> a.
        rel_stable_assertion \<omega> A \<Longrightarrow> stable \<omega>' \<Longrightarrow> typed \<Delta> \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> wf_assertion A \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>a (A :: ('v, 'a) abs_state assertion) \<omega> \<omega>' \<Delta>. a \<in> A \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> wf_assertion A \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> S \<omega> \<omega>' C. P \<Delta> \<omega> \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> x ty \<omega> v. variables \<Delta> x = Some ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> e \<omega> v x ty. variables \<Delta> x = Some ty \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> l \<omega>. P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_abs_state \<omega>))))"
  shows "P \<Delta> \<omega>'"
proof -
  have "P \<Delta> \<omega> \<and> wf_abs_stmt \<Delta> C \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')"
    using assms(1)
  proof (induct rule: red_stmt_sequential_composition.inducts(1)[of \<Delta> C \<omega> S "\<lambda>\<Delta> C \<omega> S. P \<Delta> \<omega> \<and> wf_abs_stmt \<Delta> C \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')" "\<lambda>\<Delta> S C S'. (\<forall>\<omega>\<in>S. P \<Delta> \<omega>) \<and> wf_abs_stmt \<Delta> C \<longrightarrow> (\<forall>\<omega>\<in>S'. P \<Delta> \<omega>)"])
    case (RedInhale \<omega> A \<Delta>)
    then show ?case using assms
      by (smt (verit, best) member_filter singletonD wf_abs_stmt.simps(2) x_elem_set_product)
  next
    case (RedExhale a A \<omega> \<omega>' \<Delta>)
    then show ?case
      by (simp add: assms(6))
  next
    case (RedLocalAssign \<Delta> x ty e \<omega> v)
    then show ?case
      using assms(8) by (simp)
  next
    case (RedHavoc \<Delta> x ty \<omega>)
    then show ?case
      by (auto simp add: assms(8))
  next
    case (RedIfTrue b \<omega> \<Delta> C1 S C2)
    then show ?case
      using wf_abs_stmt.simps(6) by blast
  next
    case (RedIfFalse b \<omega> \<Delta> C2 S C1)
    then show ?case 
      using wf_abs_stmt.simps(6) by blast
  next
    case (RedSeq \<Delta> C1 \<omega> S1 C2 S2)
    then show ?case by fastforce
  next
    case (RedCustom \<Delta> C \<omega> S)
    then show ?case
      using assms(7) wf_abs_stmt.simps(10) by blast
  qed (blast+)
  then show ?thesis
    using assms(2) assms(3) assms(4) by blast
qed


lemma red_typed_heap:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "wf_custom_state (custom_context \<Delta>) (get_abs_state \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "\<omega>' \<in> S"
    shows "wf_custom_state (custom_context \<Delta>) (get_abs_state \<omega>')"
  using assms
proof (induct rule: red_stmt_induct_simple_wf)
  case (Inhale A \<omega>' \<omega> \<Delta> a)
  then show ?case
    by (simp add: full_add_charact(2) typed_def wf_custom_state_sum wf_assertion_def)
next
  case (Exhale a A \<omega> \<omega>' \<Delta>)
  then show ?case using wf_custom_state_smaller
    using full_add_charact(2) greater_def by blast
next
  case (Custom \<Delta> S \<omega> \<omega>' C)
  then show ?case using red_wf_custom[of \<Delta> C \<omega> S \<omega>'] by blast
qed (auto simp add: typed_def assign_var_state_def)


lemma red_wf_state:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "wf_state \<Delta> \<omega>"
      and "\<omega>' \<in> S"
      and "wf_abs_stmt \<Delta> C"
    shows "wf_state \<Delta> \<omega>'"
  by (meson assms(1) assms(2) assms(3) assms(4) red_stable red_typed_heap red_well_typed typed_def wf_state_def)

lemma wf_setI:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> wf_state \<Delta> \<omega>"
    shows "wf_set \<Delta> S"
  using assms wf_set_def by metis


lemma wf_setI_3:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> stable \<omega>"
      and "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> typed \<Delta> \<omega>"
    shows "wf_set \<Delta> S"
  using assms wf_set_def wf_state_def
  by metis

lemma red_wf_set:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "wf_state \<Delta> \<omega>"
      and "wf_abs_stmt \<Delta> C"
    shows "wf_set \<Delta> S"
  by (meson assms(1) assms(2) assms(3) red_wf_state wf_set_def)


lemma wf_set_subset:
  assumes "wf_set \<Delta> S'"
      and "S \<subseteq> S'"
    shows "wf_set \<Delta> S"
  by (meson assms(1) assms(2) wf_set_def subsetD)



section \<open>Viper implies SL proof\<close>

lemma stable_assign_var_state:
  "stable \<omega> \<longleftrightarrow> stable (assign_var_state x v \<omega>)"
  by (metis agreement.exhaust assign_var_state_def get_abs_state_def get_abs_state_set_store stabilize_ag stabilize_is_stable stable_prod_def)

lemma stable_substitute_var:
  "stable \<omega> \<longleftrightarrow> stable (substitute_var_state x e \<omega>)"
  by (simp add: stable_assign_var_state substitute_var_state_def)

lemma wf_assertion_stabilize:
  assumes "wf_assertion A"
      and "stabilize \<omega> \<in> A"
    shows "\<omega> \<in> A"
  using assms wf_assertion_def pure_larger_stabilize by blast

lemma stabilize_substitute_var:
  assumes "e (stabilize \<omega>) \<noteq> None"
    and "wf_exp e"
    shows "stabilize (substitute_var_state x e \<omega>) = substitute_var_state x e (stabilize \<omega>)"
proof -
  obtain v where "e (stabilize \<omega>) = Some v"
    using assms(1) by blast
  then have "e \<omega> = Some v"
    by (meson assms(2) wf_exp_stabilize)
  then show ?thesis
    by (simp add: \<open>e (stabilize \<omega>) = Some v\<close> stabilize_assign_var substitute_var_state_def)
qed


lemma self_framing_post_substitute_var_assert:
  assumes "self_framing A"
      and "wf_exp e"
      and "framed_by_exp A e"
    shows "self_framing (post_substitute_var_assert x e A)"
proof (rule self_framingI)
  fix \<omega>
  show "\<omega> \<in> post_substitute_var_assert x e A \<longleftrightarrow> stabilize \<omega> \<in> post_substitute_var_assert x e A" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain a where "a \<in> A" "\<omega> = substitute_var_state x e a"
      using post_substitute_var_assert_def by blast
    then have "stabilize a \<in> A"
      by (meson assms(1) self_framing_def)

    then have "stabilize \<omega> = substitute_var_state x e (stabilize a)"
      by (metis \<open>\<omega> = substitute_var_state x e a\<close> assms(2) assms(3) framed_by_exp_def stabilize_substitute_var)
    then show ?Q
      by (simp add: \<open>stabilize a \<in> A\<close> post_substitute_var_assert_def)
  next
    assume ?Q
    then obtain a where "a \<in> A" "stabilize \<omega> = substitute_var_state x e a"
      using post_substitute_var_assert_def by auto
    then obtain v where "e a = Some v"
      by (meson assms(3) framed_by_exp_def not_Some_eq)
    then have "stabilize \<omega> = set_store a ((get_store a)(x \<mapsto> v))"
      by (simp add: \<open>stabilize \<omega> = substitute_var_state x e a\<close> assign_var_state_def substitute_var_state_def)
    then have "a = set_store (stabilize \<omega>) ((get_store (stabilize \<omega>))(x := get_store a x))"
      by (simp add: full_state_ext)

    let ?a = "set_store \<omega> ((get_store \<omega>)(x := get_store a x))"
    have "stabilize ?a = a"
      using \<open>a = set_store (stabilize \<omega>) ((get_store (stabilize \<omega>))(x := get_store a x))\<close> by fastforce
    then have "?a \<in> A"
      by (metis \<open>a \<in> A\<close> assms(1) self_framing_def)
    moreover have "\<omega> = set_store ?a ((get_store ?a)(x \<mapsto> v))"
      by (metis \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> \<open>stabilize \<omega> = set_store a ((get_store a)(x \<mapsto> v))\<close> full_state_ext get_abs_state_set_store get_store_set_store get_store_stabilize)
    ultimately show ?P
      by (smt (verit, best) \<open>e a = Some v\<close> assign_var_state_def \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> assms(2) image_eqI post_substitute_var_assert_def substitute_var_state_def wf_exp_stabilize)
  qed
qed

definition semi_typed where
  "semi_typed \<Delta> A \<longleftrightarrow> (\<forall>\<omega>\<in>A. typed \<Delta> (stabilize \<omega>))"

lemma semi_typedE:
  assumes "semi_typed \<Delta> A"
      and "\<omega> \<in> A"
    shows "typed \<Delta> (stabilize \<omega>)"
  using assms(1) assms(2) semi_typed_def by blast

lemma semi_typedI:
  assumes "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> typed \<Delta> (stabilize \<omega>)"
  shows "semi_typed \<Delta> A"
  by (simp add: assms semi_typed_def)

lemma semi_typed_star:
  assumes "semi_typed \<Delta> A"
      and "semi_typed \<Delta> B"
    shows "semi_typed \<Delta> (A \<otimes> B)"
proof (rule semi_typedI)
  fix \<omega> assume asm0: "\<omega> \<in> A \<otimes> B"
  then show "typed \<Delta> (stabilize \<omega>)"
    by (meson assms(1) assms(2) semi_typedE stabilize_sum typed_sum x_elem_set_product)
qed

lemma typed_set_stabilize_semi_typed:
  assumes "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> typed \<Delta> \<omega>"
  shows "semi_typed \<Delta> (Stabilize A)"
  apply (rule semi_typedI)
  by (simp add: assms)


lemma wf_set_after_union:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> wf_set \<Delta> (f \<omega>)"
  shows "wf_set \<Delta> (\<Union>\<omega>\<in>S. f \<omega>)"
  by (meson UN_iff assms wf_set_def)


lemma assign_var_state_inverse:
  assumes "\<omega> = assign_var_state x v \<alpha>"
  shows "\<alpha> = assign_var_state x (get_store \<alpha> x) \<omega>"
  by (simp add: assign_var_state_def assms full_state_ext)


lemma wf_state_then_value:
  assumes "variables \<Delta> x = Some ty"
      and "wf_state \<Delta> \<omega>"
    shows "\<exists>v \<in> ty. get_store \<omega> x = Some v"
  by (metis assms(1) assms(2) domD domI typed_def typed_store_def wf_state_def store_typed_def)


lemma Stabilize_ext:
    assumes "\<And>\<omega>. stable \<omega> \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> \<omega> \<in> B"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> \<omega> \<in> B \<Longrightarrow> \<omega> \<in> A"
    shows "Stabilize A = Stabilize B"
  using assms(1) assms(2) by force


lemma wf_exp_framed_by_typed:
  assumes "wf_exp b"
      and "framed_by_exp A b"
      and "self_framing A"
    shows "self_framing (A \<otimes> purify b)"
proof (rule self_framingI)
  fix \<omega>
  show "\<omega> \<in> A \<otimes> purify b \<longleftrightarrow> stabilize \<omega> \<in> A \<otimes> purify b" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain a r where "Some \<omega> = a \<oplus> r" "a \<in> A" "b r = Some True" "pure r"
      by (smt (verit, ccfv_SIG) mem_Collect_eq purify_def x_elem_set_product)
    then obtain r' where "Some r' = stabilize r \<oplus> |stabilize a|"
      by (metis (no_types, opaque_lifting) asso3 commutative core_is_smaller option.exhaust_sel stabilize_sum)
    then have "Some (stabilize \<omega>) = stabilize a \<oplus> r'"
      by (smt (verit) \<open>Some \<omega> = a \<oplus> r\<close> asso1 commutative core_is_smaller stabilize_sum)
    moreover have "stabilize a \<in> A"
      by (metis \<open>a \<in> A\<close> assms(3) self_framing_def)
    moreover have "pure r'"
      by (meson \<open>Some r' = stabilize r \<oplus> |stabilize a|\<close> \<open>pure r\<close> core_is_pure pure_def pure_stable stabilize_sum)
    then have "b r' \<noteq> None"
      by (metis (no_types, opaque_lifting) \<open>Some r' = stabilize r \<oplus> |stabilize a|\<close> assms(1) assms(2) calculation(2) framed_by_exp_def greater_equiv not_Some_eq wf_exp_def)
    then have "b r' = Some True"
      by (smt (verit, ccfv_SIG) \<open>Some \<omega> = a \<oplus> r\<close> \<open>b r = Some True\<close> assms(1) calculation(1) commutative greater_def option.exhaust wf_exp_def wf_exp_stabilize)
    ultimately have "r' \<in> purify b"
      by (simp add: \<open>pure r'\<close> purify_def)   
    then show ?Q
      using \<open>Some (stabilize \<omega>) = stabilize a \<oplus> r'\<close> \<open>stabilize a \<in> A\<close> x_elem_set_product by blast
  next
    assume ?Q
    then obtain a p where "Some (stabilize \<omega>) = a \<oplus> p" "a \<in> A" "pure p" "b p = Some True"
      by (smt (verit, best) CollectD purify_def x_elem_set_product)
    then obtain p' where "Some p' = p \<oplus> |\<omega>|"
      by (metis asso2 decompose_stabilize_pure option.exhaust_sel)
    then have "Some \<omega> = a \<oplus> p'"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> asso1 decompose_stabilize_pure)
    then have "b p' \<noteq> None"
      by (metis \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>b p = Some True\<close> assms(1) greater_def option.simps(3) wf_expE)
    then have "p' \<in> purify b"
      using wf_exp_combinedE[OF assms(1), of p True p']
      by (smt (verit, ccfv_SIG) \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>b p = Some True\<close> \<open>pure p\<close> core_stabilize_mono(1) greater_def max_projection_prop_def max_projection_prop_pure_core mem_Collect_eq pure_stable purify_def)
    then show ?P
      by (meson \<open>Some \<omega> = a \<oplus> p'\<close> \<open>a \<in> A\<close> x_elem_set_product)
  qed
qed


text \<open>fst \<omega> is the past (list of all past states), it represents the real choice. Indeed, imagine
1) {\<omega>1} --> {\<omega>'} --> {\<omega>1'}
2) {\<omega>2} --> {\<omega>'} --> {\<omega>2'}
--> {\<omega>1, \<omega>2} --> {\<omega>'} --> {\<omega>1', \<omega>2'}\<close>


lemma Viper_implies_SL_proof_aux:
  fixes f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "wf_set \<Delta> (snd ` SA)"
      and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
    shows "\<Delta> \<turnstile> [Stabilize (snd ` SA)] C [Stabilize (\<Union>\<omega>\<in>SA. f \<omega>)]"
  using assms
proof (induct C arbitrary: SA f)
  case (Seq C1 C2)
  let ?A = "Stabilize (snd ` SA)"
  let ?SB = "\<Union>\<omega>\<in>SA. f \<omega>"
  let ?B = "Stabilize ?SB"

  define f1 :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
    where "f1 = (\<lambda>\<omega>. SOME S1. red_stmt \<Delta> C1 (snd \<omega>) S1 \<and> sequential_composition \<Delta> S1 C2 (f \<omega>))"

  have r1: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C1 (snd \<omega>) (f1 \<omega>) \<and> sequential_composition \<Delta> (f1 \<omega>) C2 (f \<omega>)"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> SA"
    then have "red_stmt \<Delta> (C1 ;; C2) (snd \<omega>) (f \<omega>)"
      using Seq.prems(1) by presburger
    then obtain S1 where "red_stmt \<Delta> C1 (snd \<omega>) S1" "sequential_composition \<Delta> S1 C2 (f \<omega>)"
      by (meson red_stmt_Seq_elim)
    then show "red_stmt \<Delta> C1 (snd \<omega>) (f1 \<omega>) \<and> sequential_composition \<Delta> (f1 \<omega>) C2 (f \<omega>)"
      by (smt (verit) someI_ex f1_def)
  qed

  let ?R' = "Stabilize (\<Union>\<omega>\<in>SA. f1 \<omega>)"

  have "\<Delta> \<turnstile> [?A] C1 [?R']"
  proof (rule Seq(1))
    show "wf_abs_stmt \<Delta> C1"
      using Seq.prems(2) by auto
    fix \<omega> assume asm0: "\<omega> \<in> SA"
    then have "red_stmt \<Delta> C1 (snd \<omega>) (f1 \<omega>)"
      using r1 by auto
    moreover have "f1 \<omega> \<subseteq> (\<Union>\<omega>\<in>SA. f1 \<omega>)"
      using asm0(1) by auto
    ultimately show "red_stmt \<Delta> C1 (snd \<omega>) (f1 \<omega>)"
      by blast
    show "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
      using Seq.prems(4) by auto
  qed (simp add: Seq)

  let ?SR = "\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>"
  let ?R = "Stabilize (snd ` ?SR)"

  define pre_f2 where
    "pre_f2 = (\<lambda>\<omega>. SOME f2. (\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. f2 \<omega>'))"

  have pre_r2: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>f2. (\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. f2 \<omega>'))"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> SA"
    then have "sequential_composition \<Delta> (f1 \<omega>) C2 (f \<omega>)"
      using r1 by presburger
    then show "\<exists>f2. (\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. f2 \<omega>')"
    proof (rule sequential_composition_elim)
      fix ff assume asm1: "f \<omega> = \<Union> (ff ` f1 \<omega>)" "\<And>\<omega>'. \<omega>' \<in> f1 \<omega> \<Longrightarrow> red_stmt \<Delta> C2 \<omega>' (ff \<omega>')"
      let ?f2 = "\<lambda>\<omega>'. ff (snd \<omega>')"
      have "\<And>\<omega>'. \<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega> \<Longrightarrow> red_stmt \<Delta> C2 (snd \<omega>') (?f2 \<omega>')"
      proof -
        fix \<omega>' assume "\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>"
        then have "snd \<omega>' \<in> f1 \<omega>"
          by fastforce
        then have "red_stmt \<Delta> C2 (snd \<omega>') (ff (snd \<omega>'))"
          using asm1(2) by auto
        then show "red_stmt \<Delta> C2 (snd \<omega>') (?f2 \<omega>')"
          by meson
      qed
      moreover have "f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. ?f2 \<omega>')"
        by (simp add: UN_extend_simps(10) asm1(1))
      ultimately show "\<exists>f2. (\<forall>\<omega>'\<in>{snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = \<Union> (f2 ` ({snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
        by metis
    qed
  qed
  have r2: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (pre_f2 \<omega> \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. pre_f2 \<omega> \<omega>')"
  proof -
    fix \<omega> assume "\<omega> \<in> SA"
    then obtain f2 where "(\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. f2 \<omega>')"
      using pre_r2 by presburger
    show "(\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (pre_f2 \<omega> \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. pre_f2 \<omega> \<omega>')"
      unfolding pre_f2_def
    proof (rule someI_ex[of "\<lambda>f2. (\<forall>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. f2 \<omega>')"])
      show "\<exists>f2. (\<forall>\<omega>'\<in>{snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = \<Union> (f2 ` ({snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
        using \<open>\<And>thesis. (\<And>f2. (\<forall>\<omega>' \<in>{snd \<omega> # fst \<omega>} \<times> f1 \<omega>. red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')) \<and> f \<omega> = \<Union> (f2 ` ({snd \<omega> # fst \<omega>} \<times> f1 \<omega>)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by fastforce
    qed
  qed

  define f2 where "f2 = (\<lambda>\<omega>'. pre_f2 (tl (fst \<omega>'), hd (fst \<omega>')) \<omega>')"

  have "\<Delta> \<turnstile> [?R] C2 [Stabilize (\<Union> (f2 ` ?SR))]"
  proof (rule Seq(2))
    fix \<omega>' assume "\<omega>' \<in> (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>)"
    then obtain \<omega> where "\<omega> \<in> SA" "fst \<omega>' = snd \<omega> # fst \<omega>" "snd \<omega>' \<in> f1 \<omega>"
      by fastforce
    then have "red_stmt \<Delta> C2 (snd \<omega>') (pre_f2 \<omega> \<omega>') \<and> f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. pre_f2 \<omega> \<omega>')"
      by (metis (no_types, lifting) insertI1 mem_Sigma_iff prod.collapse r2)
    moreover have "pre_f2 \<omega> \<omega>' = f2 \<omega>'"
      by (simp add: \<open>fst \<omega>' = snd \<omega> # fst \<omega>\<close> f2_def)
    ultimately show "red_stmt \<Delta> C2 (snd \<omega>') (f2 \<omega>')"
      by auto
  next
    show "wf_abs_stmt \<Delta> C2"
      using Seq.prems(2) by auto
    show "wf_set \<Delta> (snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
    proof (rule wf_setI)
      fix \<omega>' assume "\<omega>' \<in> snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>)"
      then obtain \<omega> where "\<omega> \<in> SA" "\<omega>' \<in> f1 \<omega>"
        by fastforce
      then have "red_stmt \<Delta> C1 (snd \<omega>) (f1 \<omega>)"
        using r1 by blast
      moreover have "wf_state \<Delta> (snd \<omega>)"
        using Seq.prems(3) \<open>\<omega> \<in> SA\<close> wf_set_def by blast
      ultimately have r: "wf_set \<Delta> (f1 \<omega>)" 
        using red_wf_set
        using Seq.prems(2) wf_abs_stmt.simps(7) by blast
      then show "wf_state \<Delta> \<omega>'"
        using wf_set_def \<open>\<omega>' \<in> f1 \<omega>\<close> by blast
    qed
    show "\<And>\<alpha>. \<alpha> \<in> (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>) \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
      by (metis (no_types, lifting) \<open>wf_set \<Delta> (snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))\<close> image_eqI wf_set_def wf_state_def)
  qed

  moreover have "snd ` ?SR = (\<Union>\<omega>\<in>SA. f1 \<omega>)"
  proof
    show "snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>) \<subseteq> \<Union> (f1 ` SA)"
      by auto
    show "\<Union> (f1 ` SA) \<subseteq> snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>)"
    proof
      fix x assume "x \<in> \<Union> (f1 ` SA)"
      then obtain \<omega> where "\<omega> \<in> SA" "x \<in> f1 \<omega>"
        by blast
      then have "x \<in> snd ` ({snd \<omega> # fst \<omega>} \<times> f1 \<omega>)"
        by simp
      then show "x \<in> snd ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>)"
        using \<open>\<omega> \<in> SA\<close> by blast
    qed
  qed
  then have "?R = ?R'"
      by presburger

  moreover have "(\<Union>\<omega>\<in>SA. f \<omega>) = \<Union> (f2 ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
  proof
    have rr: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = (\<Union>\<omega>' \<in> f1 \<omega>. pre_f2 \<omega> (snd \<omega> # fst \<omega>, \<omega>'))"
    proof -
      fix \<omega>
      assume "\<omega> \<in> SA"
      then have "f \<omega> = (\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. pre_f2 \<omega> \<omega>')"
        using r2 by presburger
      moreover have "(\<Union>\<omega>' \<in> {snd \<omega> # fst \<omega>} \<times> f1 \<omega>. pre_f2 \<omega> \<omega>') = (\<Union>\<omega>' \<in> f1 \<omega>. pre_f2 \<omega> (snd \<omega> # fst \<omega>, \<omega>'))" by blast
      ultimately show "f \<omega> = (\<Union>\<omega>' \<in> f1 \<omega>. pre_f2 \<omega> (snd \<omega> # fst \<omega>, \<omega>'))"
        by presburger
    qed
    show "\<Union> (f ` SA) \<subseteq> \<Union> (f2 ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
    proof
      fix x assume "x \<in> \<Union> (f ` SA)"
      then obtain \<omega> where "x \<in> f \<omega>" "\<omega> \<in> SA"
        by blast
      then have "x \<in> (\<Union>\<omega>' \<in> f1 \<omega>. pre_f2 \<omega> (snd \<omega> # fst \<omega>, \<omega>'))"
        using rr by blast
      then obtain \<omega>' where "\<omega>' \<in> f1 \<omega>" "x \<in> pre_f2 \<omega> (snd \<omega> # fst \<omega>, \<omega>')"
        by blast
      then have "x \<in> f2 (snd \<omega> # fst \<omega>, \<omega>')"
        by (simp add: f2_def)
      then show "x \<in> \<Union> (f2 ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
        using \<open>\<omega> \<in> SA\<close> \<open>\<omega>' \<in> f1 \<omega>\<close> by blast
    qed
    show "\<Union> (f2 ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>)) \<subseteq> \<Union> (f ` SA)"
    proof
      fix x assume "x \<in> \<Union> (f2 ` (\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>))"
      then obtain \<omega> \<omega>' where "x \<in> f2 (snd \<omega> # fst \<omega>, \<omega>')" "\<omega>' \<in> f1 \<omega>" "\<omega> \<in> SA"
        by blast
      then have "x \<in> f \<omega>"
        using f2_def rr by auto
      then show "x \<in> \<Union> (f ` SA)"
        using \<open>\<omega> \<in> SA\<close> by blast
    qed
  qed
  then have "?B = Stabilize (\<Union> (f2 ` ?SR))"
    by presburger

  ultimately show "\<Delta> \<turnstile> [?A] C1 ;; C2 [?B]"
    using RuleSeq \<open>\<Delta> \<turnstile> [Stabilize (snd ` SA)] C1 [Stabilize (\<Union> (f1 ` SA))]\<close> by force
next
  case (If b C1 C2)
  let ?S1 = "Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA"
  let ?S2 = "Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA"

  have "SA = ?S1 \<union> ?S2"
  proof
    show "?S1 \<union> ?S2 \<subseteq> SA"
      by (simp add: Set.filter_def)
    show "SA \<subseteq> ?S1 \<union> ?S2"
    proof
      fix \<omega> assume "\<omega> \<in> SA"
      then have "red_stmt \<Delta> (abs_stmt.If b C1 C2) (snd \<omega>) (f \<omega>)"
        using If.prems(1) by blast
      then obtain v where "b (snd \<omega>) = Some v"
        by blast
      then show "\<omega> \<in> ?S1 \<union> ?S2"
        by (simp add: \<open>\<omega> \<in> SA\<close>)
    qed
  qed

  let ?A1 = "Stabilize (snd ` ?S1)"
  let ?B1 = "Stabilize (\<Union> (f ` ?S1))"

  have "\<Delta> \<turnstile> [Stabilize (snd ` ?S1)] C1 [Stabilize (\<Union> (f ` ?S1))]"
  proof (rule If(1))
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<Longrightarrow> red_stmt \<Delta> C1 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
    show "wf_abs_stmt \<Delta> C1"
      using If.prems(2) wf_abs_stmt.simps(6) by blast
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)"
      by (metis (no_types, lifting) If.prems(3) \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono inf_sup_ord(3) wf_set_subset)
    show "\<And>\<alpha>. \<alpha> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
      by (simp add: If.prems(4))
  qed

  have "framed_by_exp (Stabilize (snd ` SA)) b"
  proof (rule framed_by_expI)
    fix \<omega> assume "\<omega> \<in> (Stabilize (snd ` SA))"
    then have "stabilize \<omega> \<in> snd ` SA"
      using in_Stabilize by blast
    then show "b \<omega> \<noteq> None"
      by (smt (verit, ccfv_SIG) If.prems(1) If.prems(2) imageE max_projection_prop_def max_projection_prop_stable_stabilize option.distinct(1) red_stmt_If_elim wf_abs_stmt.simps(6) wf_expE)
  qed

  have "?A1 = Stabilize (snd ` SA) \<otimes> purify b"
  proof (rule self_framing_ext)

    show "self_framing (Stabilize (snd ` SA) \<otimes> purify b)"
      using If(4) Stabilize_self_framing \<open>framed_by_exp (Stabilize (snd ` SA)) b\<close> semantics.wf_exp_framed_by_typed semantics_axioms wf_abs_stmt.simps(6) by blast

    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A1"
    then have "b (stabilize \<omega>) = Some True"
      by fastforce
    show "\<omega> \<in> Stabilize (snd ` SA) \<otimes> purify b"
    proof -
      have "\<omega> \<in> Stabilize (snd ` SA)"
        by (metis (no_types, lifting) UnI1 \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> asm0(2) image_Un in_Stabilize)
      moreover have "b |\<omega>| = Some True"
        using wf_exp_coreE[of b \<omega>]
        using If.prems(2) \<open>b (stabilize \<omega>) = Some True\<close> already_stable asm0(1) by fastforce
      moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
        by (simp add: core_is_smaller)
      ultimately show ?thesis
        by (smt (verit) CollectI max_projection_prop_def max_projection_prop_pure_core purify_def typed_smaller x_elem_set_product)
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize (snd ` SA) \<otimes> purify b"
    then have "\<omega> \<in> Stabilize (snd ` SA) \<and> b \<omega> = Some True"
      by (smt (verit, best) CollectD If.prems(2) add_set_commm in_set_sum purify_def wf_abs_stmt.simps(6)  stable_and_sum_pure_same wf_exp_def x_elem_set_product)
    then show "\<omega> \<in> ?A1"
      using already_stable asm0(1) by force
  qed (simp_all)

  let ?A2 = "Stabilize (snd ` ?S2)"
  let ?B2 = "Stabilize (\<Union> (f ` ?S2))"


  have "?A2 = Stabilize (snd ` SA) \<otimes> purify (negate b)"
  proof (rule self_framing_ext)
    show "self_framing (Stabilize (snd ` SA) \<otimes> purify (negate b))"
      using If.prems(2) Stabilize_self_framing \<open>framed_by_exp (Stabilize (snd ` SA)) b\<close> framed_by_negate semantics.wf_abs_stmt.simps(6) semantics_axioms wf_exp_framed_by_typed wf_exp_negate by blast

    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A2"
    then have "b (stabilize \<omega>) = Some False" by fastforce
    show "\<omega> \<in> Stabilize (snd ` SA) \<otimes> purify (negate b)"
    proof -
      have "\<omega> \<in> Stabilize (snd ` SA)"
        using asm0(2) by auto
      moreover have "b |\<omega>| = Some False"
        using wf_exp_coreE[of b \<omega>]
        by (metis If.prems(2) \<open>b (stabilize \<omega>) = Some False\<close> already_stable asm0(1) wf_abs_stmt.simps(6) )
      ultimately have "|\<omega>| \<in> purify (negate b)"
        using negate_def[of b "|\<omega>|"]
        by (smt (verit, ccfv_SIG) CollectI max_projection_prop_def max_projection_prop_pure_core option.discI option.sel purify_def )
      moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
        by (simp add: core_is_smaller)
      ultimately show ?thesis
        using \<open>\<omega> \<in> Stabilize (snd ` SA)\<close> x_elem_set_product by blast
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize (snd ` SA) \<otimes> purify (negate b)"
    then obtain a p where "pure p" "b p = Some False" "Some \<omega> = a \<oplus> p" "a \<in> Stabilize (snd ` SA)"
      by (smt (verit, best) CollectD negate_def option.discI option.exhaust_sel purify_def x_elem_set_product)

    then have "\<omega> \<in> Stabilize (snd ` SA) \<and> b \<omega> = Some False"
      by (metis If.prems(2) asm0(1) greater_equiv stable_and_sum_pure_same wf_abs_stmt.simps(6) wf_expE)
    then show "\<omega> \<in> ?A2"
      using already_stable asm0(1) by force
  qed (simp_all)

  have "\<Delta> \<turnstile> [?A2] C2 [?B2]"
  proof (rule If(2))
    show "wf_abs_stmt \<Delta> C2"
      using If.prems(2) by auto
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA)"
      by (metis (no_types, lifting) If.prems(3) \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono inf_sup_ord(4) wf_set_subset)
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA \<Longrightarrow> red_stmt \<Delta> C2 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
    show "\<And>\<alpha>. \<alpha> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
      by (simp add: If.prems(4))
  qed


  moreover have "\<Delta> \<turnstile> [Stabilize (snd ` SA)] abs_stmt.If b C1 C2 [?B1 \<union> ?B2]"
    using RuleIf \<open>Stabilize (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA) = Stabilize (snd ` SA) \<otimes> purify (negate b)\<close> \<open>Stabilize (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA) = Stabilize (snd ` SA) \<otimes> purify b\<close> \<open>\<Delta> \<turnstile> [Stabilize (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)] C1 [Stabilize (\<Union> (f ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))]\<close> \<open>framed_by_exp (Stabilize (snd ` SA)) b\<close> calculation by auto

  moreover have "?B1 \<union> ?B2 = Stabilize (\<Union> (f ` SA))"
  proof (rule self_framing_ext)
    show "self_framing (?B1 \<union> ?B2)"
      using Stabilize_self_framing self_framing_union by blast
    fix \<omega> :: "('v, 'a) abs_state" assume "stable \<omega>"
    show "\<omega> \<in> ?B1 \<union> ?B2 \<Longrightarrow>  \<omega> \<in> Stabilize (\<Union> (f ` SA))"
      by force
    show "\<omega> \<in> Stabilize (\<Union> (f ` SA)) \<Longrightarrow> \<omega> \<in> ?B1 \<union> ?B2"
      using \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close>
      by auto
  qed (simp_all)
  ultimately show ?case
    by argo
next
  case (Inhale P)

  let ?A = "Stabilize (snd ` SA)"

  have "\<And>\<omega>. \<omega> \<in> ?A \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> rel_stable_assertion \<omega> P"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> ?A" "stable \<omega>"
    then obtain x where "x \<in> SA" "snd x = \<omega>"
      using already_stable
      by fastforce
    then have "red_stmt \<Delta> (Inhale P) \<omega> (f x)"
      by (metis Inhale.prems(1))
    then show "rel_stable_assertion \<omega> P"
      by force
  qed
  then have "self_framing (?A \<otimes> P)"
    using Stabilize_self_framing framed_byI self_framing_star by blast

  moreover have r: "framed_by ?A (Set.filter (typed \<Delta> \<circ> stabilize) P)"
  proof (rule framed_byI)
    fix \<omega> assume asm0: "\<omega> \<in> ?A" "sep_algebra_class.stable \<omega>"
    then have r: "rel_stable_assertion \<omega> P"
      using \<open>\<And>\<omega>. \<lbrakk>\<omega> \<in> Stabilize (snd ` SA); sep_algebra_class.stable \<omega>\<rbrakk> \<Longrightarrow> rel_stable_assertion \<omega> P\<close> by blast
    show "rel_stable_assertion \<omega> (Set.filter (typed \<Delta> \<circ> stabilize) P)"
      unfolding rel_stable_assertion_def
    proof (rule stable_set_filter_stabilize)
      show "{\<omega>} \<otimes> P \<subseteq> Stabilize ({\<omega>} \<otimes> P)"
        using Stable_def r rel_stable_assertion_def by blast
      show "Stabilize ({\<omega>} \<otimes> P) \<subseteq> {\<omega>} \<otimes> P"
      proof
        fix x assume "x \<in> Stabilize ({\<omega>} \<otimes> P)"
        then obtain p where "p \<in> P" "Some (stabilize x) = \<omega> \<oplus> p"
          by (smt (verit, best) in_Stabilize singletonD x_elem_set_product)
        then obtain p' where "Some p' = p \<oplus> |x|"
          by (metis asso2 decompose_stabilize_pure option.exhaust_sel)
        then have "p' \<in> P"
          using wf_assertionE[of P p' p]
          using Inhale.prems(2) \<open>p \<in> P\<close> core_is_pure pure_def pure_larger_def semantics.wf_abs_stmt.simps(2) semantics_axioms by blast
        then show "x \<in> {\<omega>} \<otimes> P"
          by (metis (no_types, lifting) \<open>Some (stabilize x) = \<omega> \<oplus> p\<close> \<open>Some p' = p \<oplus> |x|\<close> asso1 decompose_stabilize_pure singletonI x_elem_set_product)
      qed
      show "{\<omega>} \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P = Set.filter (typed \<Delta> \<circ> stabilize) ({\<omega>} \<otimes> P)" (is "?A = ?B")
      proof
        show "{\<omega>} \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P \<subseteq> Set.filter (typed \<Delta> \<circ> stabilize) ({\<omega>} \<otimes> P)"
        proof
          fix x assume "x \<in> ?A"
          then obtain p where "p \<in> P" "typed \<Delta> (stabilize p)" "Some x = \<omega> \<oplus> p"
            using in_singleton_star by force
          then have "typed \<Delta> (stabilize x)"
            by (meson Inhale.prems(3) asm0(1) in_Stabilize stabilize_sum typed_sum wf_set_def wf_state_def)
          then show "x \<in> ?B"
            by (simp add: \<open>Some x = \<omega> \<oplus> p\<close> \<open>p \<in> P\<close> is_in_set_sum)
        qed
        show "Set.filter (typed \<Delta> \<circ> stabilize) ({\<omega>} \<otimes> P) \<subseteq> {\<omega>} \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P"
        proof
          fix x assume "x \<in> ?B"
          then obtain p where "p \<in> P" "Some x = \<omega> \<oplus> p" "typed \<Delta> (stabilize x)"
            by (metis comp_apply in_singleton_star member_filter)
          then have "typed \<Delta> (stabilize p)"
            using greater_equiv stabilize_mono typed_smaller by blast
          then show "x \<in> ?A"
            using \<open>Some x = \<omega> \<oplus> p\<close> \<open>p \<in> P\<close> is_in_set_sum by fastforce
        qed
      qed
    qed
  qed


  have "\<Delta> \<turnstile> [?A] Inhale P [?A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P]"
    apply (rule RuleInhale)
    apply auto[1]
    using \<open>\<And>\<omega>. \<lbrakk>\<omega> \<in> Stabilize (snd ` SA); sep_algebra_class.stable \<omega>\<rbrakk> \<Longrightarrow> rel_stable_assertion \<omega> P\<close> framed_byI by blast
  moreover have "self_framing (?A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P)"
    using Stabilize_self_framing r self_framing_star by blast
  moreover have "Set.filter sep_algebra_class.stable (snd ` SA) \<subseteq> ?A"
    using Stabilize_filter_stable by blast

  moreover have "Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega>) (?A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P) = \<Union> (f ` SA)"
  proof
    show "Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega>) (?A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P) \<subseteq> \<Union> (f ` SA)"
    proof
      fix \<omega> assume "\<omega> \<in> Set.filter stable (?A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P)"
      then obtain a p where asm0: "stable \<omega>" "Some \<omega> = a \<oplus> p" "a \<in> ?A" "p \<in> Set.filter (typed \<Delta> \<circ> stabilize) P" "a \<in> Stabilize (snd ` SA)"
        by (smt (verit, ccfv_threshold) mem_Collect_eq member_filter add_set_def)
      then have "Some \<omega> = stabilize a \<oplus> p"
        using stabilize_sum_result_stable by blast
      moreover obtain l where "l \<in> SA" "snd l = stabilize a"
        using asm0(3) by auto
      then have "red_stmt \<Delta> (Inhale P) (stabilize a) (f l)"
        by (metis Inhale.prems(1))
      then have "f l = Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>)  ({stabilize a} \<otimes> P) \<and> rel_stable_assertion (stabilize a) P"
        using red_stmt_Inhale_elim by blast
      then have "\<omega> \<in> f l"
        by (smt (verit, best) Inhale.prems(4) \<open>l \<in> SA\<close> \<open>snd l = stabilize a\<close> already_stable asm0(1) asm0(2) asm0(4) calculation comp_apply is_in_set_sum member_filter stabilize_sum typed_sum)
(*
        by (metis (no_types, lifting) Inhale.prems(3) asm0(1) asm0(3) asm0(4) calculation in_Stabilize is_in_set_sum member_filter typed_sum wf_set_def wf_state_def)
*)
      then show "\<omega> \<in> \<Union> (f ` SA)"
        using \<open>l \<in> SA\<close> by blast
    qed
    show "\<Union> (f ` SA) \<subseteq> Set.filter stable (Stabilize (snd ` SA) \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P)"
    proof 
      fix \<omega> assume "\<omega> \<in> \<Union> (f ` SA)"
      then obtain x where "x \<in> SA" "\<omega> \<in> f x"
        by blast
      then have "red_stmt \<Delta> (Inhale P) (snd x) (f x)"
        using Inhale.prems(1) by blast
      then show "\<omega> \<in> Set.filter stable (Stabilize (snd ` SA) \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P)"
      proof (rule red_stmt_Inhale_elim)
        assume "f x = Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({snd x} \<otimes> P)"
        then obtain p where "p \<in> P" "Some \<omega> = snd x \<oplus> p" "(\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) \<omega>"
          by (smt (verit, ccfv_SIG) \<open>\<omega> \<in> f x\<close> member_filter singletonD x_elem_set_product)
        then have "typed \<Delta> p"
          using greater_equiv typed_smaller by blast
        then have "\<omega> \<in> Stabilize (snd ` SA) \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P"
          by (smt (verit, ccfv_threshold) Inhale.prems(3) \<open>Some \<omega> = snd x \<oplus> p\<close> \<open>p \<in> P\<close> \<open>x \<in> SA\<close> already_stable comp_apply image_iff in_Stabilize member_filter typed_then_stabilize_typed wf_set_def wf_state_def x_elem_set_product)
        then show "\<omega> \<in> Set.filter stable (Stabilize (snd ` SA) \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P)"
          by (simp add: \<open>sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>\<close>)
      qed
    qed
  qed
  ultimately show ?case
    by (metis (no_types, lifting) Stabilize_ext member_filter self_framing_eq)
next
  case (Exhale P)

  let ?A = "Stabilize (\<Union> (f ` SA))"
  let ?B = "Stabilize (snd ` SA)"

  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>a \<omega>'. f \<omega> = {\<omega>'} \<and> a \<in> P \<and> Some (snd \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>')"
  proof -
    fix \<omega> assume "\<omega> \<in> SA"
    then have "red_stmt \<Delta> (Exhale P) (snd \<omega>) (f \<omega>)"
      using Exhale.prems(1) by blast
    then show "\<exists>a \<omega>'. f \<omega> = {\<omega>'} \<and> a \<in> P \<and> Some (snd \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>'"
      using red_stmt_Exhale_elim
      by blast
  qed

  then have "wf_set \<Delta> (\<Union> (f ` SA))"
    by (metis (no_types, lifting) Exhale.prems(1) Exhale.prems(2) Exhale.prems(3) image_insert insertCI mk_disjoint_insert red_wf_set wf_set_after_union wf_set_def)

  moreover have "entails ?B (?A \<otimes> P)"
  proof (rule entailsI)
    fix \<omega> assume "\<omega> \<in> Stabilize (snd ` SA)"
    then have "stabilize \<omega> \<in> snd ` SA"
      using in_Stabilize by blast
    then obtain x where asm0: "x \<in> SA" "stabilize \<omega> = snd x"
      by blast
    then obtain a \<omega>' where "f x = {\<omega>'} \<and> a \<in> P \<and> Some (stabilize \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>'"
      using r by metis
    moreover obtain \<omega>'' where "Some \<omega>'' = \<omega>' \<oplus> |\<omega>|"
      by (metis asso3 calculation commutative decompose_stabilize_pure not_Some_eq) (* long *)
    then have "stabilize \<omega>'' = stabilize \<omega>'" using pure_larger_stabilize_same[of \<omega>'' \<omega>']
      using core_is_pure pure_def pure_larger_def by blast
    then have "\<omega>'' \<in> Stabilize (\<Union> (f ` SA))"
      using already_stable asm0(1) calculation by fastforce
    moreover have "Some \<omega> = \<omega>'' \<oplus> a"
      by (metis (no_types, lifting) \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> asso1 calculation(1) commutative decompose_stabilize_pure)
    ultimately show "\<omega> \<in> Stabilize (\<Union> (f ` SA)) \<otimes> P"
      using x_elem_set_product by blast
  qed

  moreover show "\<Delta> \<turnstile> [?B] Exhale P [?A]"
  proof (rule RuleExhale)
    show "entails (Stabilize (snd ` SA)) (Stabilize (\<Union> (f ` SA)) \<otimes> P)"
      using calculation(2) by simp
  qed (simp_all)
next
  case (Assert P)
  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>} \<and> snd \<omega> \<in> P"
    using Assert.prems(1) by blast
  moreover have "entails (Stabilize (snd ` SA)) P"
  proof (rule entailsI)
    fix \<omega> assume "\<omega> \<in> Stabilize (snd ` SA)"
    then have "stabilize \<omega> \<in> snd ` SA"
      using in_Stabilize by blast
    then have "stabilize \<omega> \<in> P"
      using r by force
    then show "\<omega> \<in> P" using wf_assertion_stabilize Assert(2)
      using \<open>stabilize \<omega> \<in> snd ` SA\<close> wf_abs_stmt.simps(4) by blast
  qed
  moreover have "\<Union> (f ` SA) = snd ` SA"
  proof
    show "\<Union> (f ` SA) \<subseteq> snd ` SA"
      using r by auto
    show "snd ` SA \<subseteq> \<Union> (f ` SA)"
      using r by auto
  qed
  ultimately show ?case
    by (simp add: RuleAssert)
next
  case (LocalAssign x e)

  let ?ty = "the (variables \<Delta> x)"
  let ?A = "post_substitute_var_assert x e (Stabilize (snd ` SA))"

  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>v. variables \<Delta> x = Some ?ty \<and> e (snd \<omega>) = Some v \<and> v \<in> ?ty
  \<and> f \<omega> = { assign_var_state x (Some v) (snd \<omega>) })"
    using LocalAssign.prems(1) by fastforce

  have "\<Delta> \<turnstile> [Stabilize (snd ` SA)] abs_stmt.LocalAssign x e [?A]"
  proof (rule RuleLocalAssign)
    show "framed_by_exp (Stabilize (snd ` SA)) e"
    proof (rule framed_by_expI)
      fix \<omega> assume "\<omega> \<in> Stabilize (snd ` SA)"
      then have "stabilize \<omega> \<in> snd ` SA"
        using in_Stabilize by blast
      then obtain v where "variables \<Delta> x = Some ?ty \<and> e (stabilize \<omega>) = Some v \<and> v \<in> ?ty"
        using r by fastforce
      moreover have "wf_exp e"
        using LocalAssign(2) by auto
      ultimately have "e \<omega> = Some v"
        by (meson max_projection_prop_stable_stabilize mpp_smaller wf_expE)
      then show "e \<omega> \<noteq> None" by simp
    qed
  qed (simp)
  moreover have "?A = Stabilize (\<Union> (f ` SA))" (is "?A = ?B")
  proof (rule self_framing_ext)
    show "self_framing (post_substitute_var_assert x e (Stabilize (snd ` SA)))"
      using LocalAssign.prems(2) calculation self_framing_post_substitute_var_assert by auto

    fix \<omega> assume asm0: "stable \<omega>" "\<omega> \<in> post_substitute_var_assert x e (Stabilize (snd ` SA))"
    then obtain \<omega>' where "\<omega>' \<in> Stabilize (snd ` SA)" "\<omega> = assign_var_state x (e \<omega>') \<omega>'"
      using post_substitute_var_assert_def substitute_var_state_def
      using image_iff by fastforce
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' = snd \<alpha>"
      by (meson image_iff in_Stabilize)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> e (stabilize \<omega>') = Some v \<and> v \<in> ?ty
  \<and> f \<alpha> = {assign_var_state x (Some v) (stabilize \<omega>')}"
      using r by presburger
    moreover have "stable \<omega>'"
      using \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> asm0(1) stable_assign_var_state by blast
    then show "\<omega> \<in> Stabilize (\<Union> (f ` SA))"
      by (metis (no_types, lifting) UnI1 Union_image_insert \<open>\<alpha> \<in> SA\<close> \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> already_stable calculation image_insert insert_image stabilize_assign_var in_Stabilize  singletonI)
  next
    fix \<omega> assume "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize (\<Union> (f ` SA))"
    then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega> \<in> f \<alpha>"
      by (metis UN_E already_stable in_Stabilize)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> e (snd \<alpha>) = Some v \<and> v \<in> ?ty
  \<and> f \<alpha> = {assign_var_state x (Some v) (snd \<alpha>) }"
      using r by blast
    then have "\<omega> = assign_var_state x (Some v) (snd \<alpha>)"
      using \<open>\<omega> \<in> f \<alpha>\<close> by blast
    then have "\<omega> = substitute_var_state x e (snd \<alpha>)"
      using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> e (snd \<alpha>) = Some v \<and> v \<in> the (variables \<Delta> x) \<and> f \<alpha> = {assign_var_state x (Some v) (snd \<alpha>)}\<close> substitute_var_state_def
      by metis
    moreover have "snd \<alpha> \<in> Stabilize (snd ` SA)"
      by (metis (no_types, lifting) LocalAssign.prems(3) \<open>\<alpha> \<in> SA\<close> already_stable image_insert insertI1 mk_disjoint_insert wf_state_def  in_Stabilize wf_set_def)
    ultimately show "\<omega> \<in> post_substitute_var_assert x e (Stabilize (snd ` SA))"
      using post_substitute_var_assert_def by fast
  qed (simp_all)
  ultimately show "\<Delta> \<turnstile> [Stabilize (snd ` SA)] abs_stmt.LocalAssign x e [Stabilize (\<Union> (f ` SA))]"
    by argo
next
  case Skip
  then have "\<Delta> \<turnstile> [Stabilize (snd ` SA)] Skip [Stabilize (snd ` SA)]"
    using RuleSkip by simp
  moreover have "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>}"
    using Skip.prems(1) by blast
  ultimately show ?case
    by (metis (no_types, lifting) SUP_cong UNION_singleton_eq_range)
next
  case (Havoc x)

  let ?ty = "the (variables \<Delta> x)"
  let ?A = "Stabilize (snd ` SA)"
  let ?B = "exists_assert \<Delta> x ?A"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (variables \<Delta> x = Some ?ty \<and> f \<alpha> = { assign_var_state x (Some v) (snd \<alpha>) |v. v \<in> ?ty})"
    using Havoc by fastforce
(*
    ?\<omega>7 \<in> SA \<Longrightarrow> red_stmt \<Delta> (abs_stmt.Havoc x) (snd ?\<omega>7) (f ?\<omega>7)
    wf_abs_stmt \<Delta> (abs_stmt.Havoc x)
    wf_set \<Delta> (snd ` SA)
*)
  have "\<Delta> \<turnstile> [?A] abs_stmt.Havoc x [?B]"
    by (rule RuleHavoc) simp
  moreover have "?B = Stabilize (\<Union> (f ` SA))"
  proof (rule self_framing_ext)
    show "self_framing (exists_assert \<Delta> x (Stabilize (snd ` SA)))"
      using Stabilize_self_framing self_framing_exists_assert by blast
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> exists_assert \<Delta> x (Stabilize (snd ` SA))"
    then obtain v0 v ty where asm1: "v0 \<in> ty" "get_store \<omega> x = Some v0" "variables \<Delta> x = Some ty"
      "v \<in> ty" "assign_var_state x (Some v) \<omega> \<in> ?A" using exists_assertE[of \<omega> \<Delta> x] by meson
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize (assign_var_state x (Some v) \<omega>) = snd \<alpha>"
      using in_Stabilize[of _] by blast
    then have "assign_var_state x (Some v) \<omega> = snd \<alpha>"
      by (metis already_stable asm0(1) stable_assign_var_state)
    then have "\<omega> = assign_var_state x (Some v0) (snd \<alpha>)"
      by (metis asm1(2) assign_var_state_inverse)
    then have "stabilize \<omega> \<in> f \<alpha>"
      using \<open>\<alpha> \<in> SA\<close> already_stable asm0(1) asm1(1) asm1(3) r by auto
    then show "\<omega> \<in> Stabilize (\<Union> (f ` SA))"
      using \<open>\<alpha> \<in> SA\<close> asm0(2) in_Stabilize[of _] by blast
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize (\<Union> (f ` SA))"
    then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega> \<in> f \<alpha>"
      by (metis UN_E already_stable in_Stabilize)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)" "v \<in> ?ty"
      using r by blast
    then have "wf_state \<Delta> (snd \<alpha>)"
      using Havoc.prems(3) \<open>\<alpha> \<in> SA\<close> wf_set_def by blast
    then obtain v' where "get_store (snd \<alpha>) x = Some v'" "v' \<in> ?ty"
      using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> wf_state_then_value by blast
    show "\<omega> \<in> exists_assert \<Delta> x (Stabilize (snd ` SA))"
      using \<open>v \<in> ?ty\<close>
    proof (rule exists_assertI)
      show "get_store \<omega> x = Some v"
        by (simp add: \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> assign_var_state_def)
      show "variables \<Delta> x = Some (the (variables \<Delta> x))"
        using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> by blast
      show "assign_var_state x (Some v') \<omega> \<in> Stabilize (snd ` SA)"
        by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>get_store (snd \<alpha>) x = Some v'\<close> \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> \<open>wf_state \<Delta> (snd \<alpha>)\<close> already_stable insertI1 insert_image assign_var_state_inverse in_Stabilize wf_state_def )
    qed (simp_all add: \<open>v' \<in> ?ty\<close>)
  qed (simp_all)
  ultimately show "\<Delta> \<turnstile> [Stabilize (snd ` SA)] abs_stmt.Havoc x [Stabilize (\<Union> (f ` SA))]"
    by argo
next
  case (Assume P)
  then have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (stable_on (snd \<omega>) P \<and> f \<omega> = {snd \<omega>} \<inter> P)"
    by fastforce

  let ?A = "Stabilize (snd ` SA)"

  have "\<Delta> \<turnstile> [?A] Assume P [?A \<inter> P]"
  proof (rule RuleAssume)
    show "self_framing_on (Stabilize (snd ` SA)) P"
      unfolding self_framing_on_def
    proof
      fix \<omega> assume asm0: "\<omega> \<in> Stabilize (snd ` SA)"
      show "(stabilize \<omega> \<in> P) = (\<omega> \<in> P)"
      proof
        show "stabilize \<omega> \<in> P \<Longrightarrow> \<omega> \<in> P"
          using wf_assertionE[of P \<omega> "stabilize \<omega>"] \<open>wf_abs_stmt \<Delta> (abs_stmt.Assume P)\<close>
          using wf_abs_stmt.simps(5) wf_assertion_stabilize by blast
        assume "\<omega> \<in> P"
        then have "stable_on \<omega> P"
          by (meson Assume(2) semantics.wf_abs_stmt.simps(5) semantics_axioms typed_state.stable_onI typed_state.wf_assertion_def typed_state_axioms)
        then show "stabilize \<omega> \<in> P"
          unfolding stable_on_def
          by (metis (no_types, lifting) RangeE \<open>\<omega> \<in> P\<close> asm0 in_Stabilize prod.sel(2) pure_larger_stabilize r snd_eq_Range stable_on_def)
      qed
    qed
  qed (simp_all)
  moreover have "?A \<inter> P = Stabilize (\<Union> (f ` SA))" (is "?A \<inter> P = ?B")
  proof
    show "?A \<inter> P \<subseteq> ?B"
    proof
      fix \<omega> assume "\<omega> \<in> ?A \<inter> P"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        using in_Stabilize[of \<omega>] by auto
      then have "stable_on (snd \<alpha>) P \<and> f \<alpha> = {snd \<alpha>} \<inter> P" using r by blast
      then have "f \<alpha> = {stabilize \<omega>}"
        by (metis Assume.prems(1) IntD2 \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize (snd ` SA) \<inter> P\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> pure_larger_stabilize semantics.red_stmt_Assume_elim semantics_axioms stable_on_def)
      then show "\<omega> \<in> ?B"
        using \<open>\<alpha> \<in> SA\<close> by auto
    qed
    show "?B \<subseteq> ?A \<inter> P"
    proof
      fix \<omega> assume "\<omega> \<in> ?B"
      then obtain \<alpha> where "stabilize \<omega> \<in> f \<alpha>" "\<alpha> \<in> SA"
        by auto
      then show "\<omega> \<in> ?A \<inter> P"
        by (metis (no_types, lifting) Int_iff image_eqI in_Stabilize pure_larger_stabilize r singletonD stable_on_def)
    qed
  qed
  ultimately show "\<Delta> \<turnstile> [Stabilize (snd ` SA)] abs_stmt.Assume P [Stabilize (\<Union> (f ` SA))]" by argo
next
  case (Custom C)
  then show ?case using SL_proof_custom[of SA \<Delta> C f]
    by (meson RuleCustom Stabilize_self_framing red_stmt_Custom_elim wf_abs_stmt.simps(10))
qed




theorem Viper_implies_SL_proof:
  assumes "verifies_set \<Delta> A C"
      and "wf_abs_stmt \<Delta> C"
      and "self_framing A"
      and "semi_typed \<Delta> A"
    shows "\<exists>B. \<Delta> \<turnstile> [A] C [B]"
proof -
  define SA :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) set" where "SA = { ([], \<omega>) |\<omega>. stable \<omega> \<and> typed \<Delta> \<omega> \<and> \<omega> \<in> A}"
  define f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
    where "f = (\<lambda>\<omega>. SOME S. red_stmt \<Delta> C (snd \<omega>) S)"

  have "wf_set \<Delta> (snd ` SA)"
  proof (rule wf_setI)
    fix \<omega> assume "\<omega> \<in> snd ` SA"
    then show "wf_state \<Delta> \<omega>"
      using SA_def wf_state_def by fastforce
  qed
  moreover have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
  proof -
    fix \<alpha> :: "('v, 'a) abs_state list \<times> ('v, 'a) abs_state" assume "\<alpha> \<in> SA"
    then have "snd \<alpha> \<in> A \<and> stable (snd \<alpha>) \<and> typed \<Delta> (snd \<alpha>)"
      using SA_def by force
    then have "\<exists>S. red_stmt \<Delta> C (snd \<alpha>) S"
      using assms(1) verifies_set_def by (simp add: verifies_def)
    then show "red_stmt \<Delta> C (snd \<alpha>) (f \<alpha>)" using someI_ex f_def
      by metis
  qed

  let ?A = "Stabilize (snd ` SA)"
  let ?B = "Stabilize (\<Union>\<omega>\<in>SA. f \<omega>)"

  have "\<Delta> \<turnstile> [?A] C [?B]"
  proof (rule Viper_implies_SL_proof_aux)
    show "wf_set \<Delta> (snd ` SA)"
      using SA_def calculation by blast
    show "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      by (simp add: \<open>\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)\<close>)
    show "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> typed \<Delta> (snd \<alpha>)"
      by (metis Range.intros calculation prod.collapse snd_eq_Range wf_set_def wf_state_def)
  qed (simp add: assms(2))

  moreover have "?A = A"
  proof (rule self_framing_ext)

    show "self_framing A"
      by (simp add: assms(3))

    fix \<omega> :: "('v, 'a) abs_state" assume asm0: "sep_algebra_class.stable \<omega>"
    show "\<omega> \<in> A \<Longrightarrow> \<omega> \<in> ?A"
    proof -
      assume asm1: "\<omega> \<in> A"
      then have "([], \<omega>) \<in> SA"
        by (metis (mono_tags, lifting) CollectI SA_def already_stable asm0 assms(4) semi_typedE)
      then show "\<omega> \<in> ?A"
        by (simp add: Range.intros already_stable asm0 snd_eq_Range)
    qed
    assume asm1: "\<omega> \<in> ?A"
    then have "\<omega> \<in> snd ` SA"
      by (simp add: already_stable asm0)
    then show "\<omega> \<in> A"
      using SA_def by force
  qed (simp_all)
  ultimately show ?thesis
    by force
qed


lemma entails_refl:
  "entails A A"
  by (simp add: entailsI)

(*
lemma free_vars_subset:
  assumes "\<And>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed \<Delta> (Ag \<sigma>1, \<gamma>) \<and> typed \<Delta> (Ag \<sigma>2, \<gamma>) \<and> equal_on_set V \<sigma>1 \<sigma>2 \<Longrightarrow> (Ag \<sigma>1, \<gamma>) \<in> A \<Longrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A"
      and "V \<subseteq> dom (variables \<Delta>)"
     shows "free_vars A \<subseteq> V"
proof -
  have "overapprox_fv \<Delta> A V"
    sledgehammer

    by (smt (verit, del_insts) assms equal_on_set_def overapprox_fv_def)
  then show ?thesis
    by (simp add: Inf_lower free_vars_def assms(2))
qed
*)

lemma entails_trans:
  assumes "entails A B"
      and "entails B C"
    shows "entails A C"
  by (meson assms(1) assms(2) dual_order.trans entails_def)




lemma get_store_Ag_simplifies[simp]:
  "get_store (Ag \<sigma>, \<gamma>) = \<sigma>"
  by (simp add: get_store_def)

lemma set_store_Ag_simplies[simp]:
  "set_store (\<alpha>, \<gamma>) \<sigma> = (Ag \<sigma>, \<gamma>)"  
  by (simp add: get_abs_state_def set_store_def)



lemma free_vars_subset:
  assumes "\<And>\<sigma>1 \<sigma>2 \<tau> \<gamma>. equal_on_set V \<sigma>1 \<sigma>2 \<Longrightarrow> typed \<Delta> (Ag \<sigma>1, \<gamma>) \<Longrightarrow> typed \<Delta> (Ag \<sigma>2, \<gamma>) \<Longrightarrow> (Ag \<sigma>1, \<gamma>) \<in> A \<Longrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A"
      and "finite V"
     shows "free_vars \<Delta> A \<subseteq> V \<and> overapprox_fv \<Delta> A V"
proof -
  have "overapprox_fv \<Delta> A V"
    by (simp add: assms(1) overapprox_fvI)
  then show ?thesis
    by (simp add: Inf_lower free_vars_def assms(2))
qed


lemma exists_assert_no_in_fv:
  assumes "finite_context \<Delta>"
  shows "free_vars \<Delta> (exists_assert \<Delta> x A) \<subseteq> free_vars \<Delta> A - {x} \<and> overapprox_fv \<Delta> (exists_assert \<Delta> x A) (free_vars \<Delta> A - {x})"
proof (rule free_vars_subset)
  have "finite (free_vars \<Delta> A)"
    by (metis Inf_lower assms finite_context_then_fv_works free_vars_def image_ident mem_Collect_eq rev_finite_subset)
  then show "finite (free_vars \<Delta> A - {x})"
    by simp

  fix \<sigma>1 \<sigma>2 \<gamma>
  assume asm0: "equal_on_set (free_vars \<Delta> A - {x}) \<sigma>1 \<sigma>2"
         "(Ag \<sigma>1, \<gamma>) \<in> exists_assert \<Delta> x A" "typed \<Delta> (Ag \<sigma>1, \<gamma>)" "typed \<Delta> (Ag \<sigma>2, \<gamma>)"
  then obtain v0 v ty where r: "v0 \<in> ty" "get_store (Ag \<sigma>1, \<gamma>) x = Some v0" "variables \<Delta> x = Some ty" "v \<in> ty"
    "(set_store (Ag \<sigma>1, \<gamma>) ((get_store (Ag \<sigma>1, \<gamma>))(x \<mapsto> v))) \<in> A"
    by (metis assign_var_state_def exists_assertE)
  then have "(Ag (\<sigma>1(x \<mapsto> v)), \<gamma>) \<in> A"
    by (smt (verit) assign_var_state_def assign_var_state_inverse get_abs_state_set_store get_store_set_store prod.inject set_store_def)
  moreover have "equal_on_set (free_vars \<Delta> A) (\<sigma>1(x \<mapsto> v)) (\<sigma>2(x \<mapsto> v))"
    using asm0(1) equal_on_set_def[of "free_vars \<Delta> A" "\<sigma>1(x \<mapsto> v)" "\<sigma>2(x \<mapsto> v)"]
    by (simp add: equal_on_set_def)

  then have "(Ag (\<sigma>2(x \<mapsto> v)), \<gamma>) \<in> A"
  proof (rule free_varsE)
    show "(Ag (\<sigma>1(x \<mapsto> v)), \<gamma>) \<in> A"
      using calculation by blast
    show "typed \<Delta> (Ag (\<sigma>1(x \<mapsto> v)), \<gamma>)"
      by (metis asm0(3) get_abs_state_set_store get_store_Ag_simplifies r(3) r(4) set_store_Ag_simplies typed_state.typed_def typed_state_axioms typed_store_update)
    show "typed \<Delta> (Ag (\<sigma>2(x \<mapsto> v)), \<gamma>)"
      by (metis asm0(4) assign_var_state_def get_store_Ag_simplifies r(3) r(4) set_store_Ag_simplies typed_assign_var)
  qed (simp_all add: assms(1))
  then have "set_store (Ag \<sigma>2, \<gamma>) ((get_store (Ag \<sigma>2, \<gamma>))(x \<mapsto> v)) \<in> A"
    by simp
  moreover obtain v0' where "get_store (Ag \<sigma>2, \<gamma>) x = Some v0'"
    using asm0(4) r(3) store_typed_lookup typed_state.typed_def typed_state_axioms typed_store_def by blast
  then have "v0' \<in> ty"
    using asm0(4) r(3) store_typed_lookup typed_state.typed_def typed_state_axioms typed_store_def by fastforce
  then show "(Ag \<sigma>2, \<gamma>) \<in> exists_assert \<Delta> x A"
    by (metis \<open>get_store (Ag \<sigma>2, \<gamma>) x = Some v0'\<close> assign_var_state_def calculation(2) in_exists_assert r(3) r(4))
qed

(*
lemma exists_assert_entails:
  assumes "typed_assertion \<Delta> A"
      and "variables \<Delta> x \<noteq> None"
  shows "entails A (exists_assert \<Delta> x A)"
proof (rule entailsI)
  fix \<omega> assume asm0: "\<omega> \<in> A"
  then have "typed \<Delta> \<omega>"
    using assms(1) typed_assertion_def by blast
  then obtain v0 ty v where "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty" "(set_store \<omega> ((get_store \<omega>)(x \<mapsto> v))) \<in> A"
    by (smt (verit, best) asm0 assms(2) domD domIff full_state_ext fun_upd_triv get_abs_state_set_store get_store_set_store typed_def typed_store_def store_typed_def)
  then show "\<omega> \<in> exists_assert \<Delta> x A"
    by (metis \<open>typed \<Delta> \<omega>\<close> assign_var_state_def exists_assertI)
qed
*)

definition entails_typed where
  "entails_typed \<Delta> A B \<longleftrightarrow> (\<forall>\<omega>. \<omega> \<in> A \<and> typed \<Delta> \<omega> \<longrightarrow> \<omega> \<in> B)"

lemma entails_typedI:
  assumes "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> \<omega> \<in> B"
  shows "entails_typed \<Delta> A B"
  using assms entails_typed_def by blast

lemma entails_typedE:
  assumes "entails_typed \<Delta> A B"
      and "\<omega> \<in> A"
      and "typed \<Delta> \<omega>"
    shows "\<omega> \<in> B"
  using assms(1) assms(2) assms(3) entails_typed_def by blast

lemma entails_typed_trans:
  assumes "entails_typed \<Delta> A B"
      and "entails_typed \<Delta> B C"
    shows "entails_typed \<Delta> A C"
  by (meson assms(1) assms(2) entails_typed_def)

lemma entails_typed_refl:
  "entails_typed \<Delta> A A"
  unfolding entails_typed_def by simp

lemma SL_proof_Havoc_elim_entails:
  assumes "\<Delta> \<turnstile> [A] Havoc x [B]"
      and "variables \<Delta> x \<noteq> None"
      and "finite_context \<Delta>"
    shows "entails_typed \<Delta> A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - {x}"
proof -
  have "entails_typed \<Delta> A (exists_assert \<Delta> x A)"
  proof (rule entails_typedI)
    fix \<omega> assume asm0: "\<omega> \<in> A" "typed \<Delta> \<omega>"
    then obtain v0 ty v where "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty" "(set_store \<omega> ((get_store \<omega>)(x \<mapsto> v))) \<in> A"
    by (smt (verit, best) asm0 assms(2) domD domIff full_state_ext fun_upd_triv get_abs_state_set_store get_store_set_store typed_def typed_store_def store_typed_def)
  then show "\<omega> \<in> exists_assert \<Delta> x A"
    by (metis assign_var_state_def exists_assertI)
  qed
  then show ?thesis
    using assms(1) assms(3) exists_assert_no_in_fv by blast
qed

lemma assign_var_state_sum:
  assumes "Some a = b \<oplus> c"
  shows "Some (assign_var_state x v a) = assign_var_state x v b \<oplus> assign_var_state x v c"
  by (smt (verit) add_defined_lift assign_var_state_def assms commutative full_add_charact(1) full_add_charact(2) set_store_def)


lemma exists_wf_assertion: (* Useless? *)
  assumes "wf_assertion A"
  shows "wf_assertion (exists_assert \<Delta> x A)"
proof (rule wf_assertionI)
  fix x' xa
  assume asm0: "pure_larger x' xa" "xa \<in> exists_assert \<Delta> x A" 
  then obtain v0 v ty where r: "v0 \<in> ty \<and> get_store xa x = Some v0 \<and> variables \<Delta> x = Some ty"
      "v \<in> ty \<and> assign_var_state x (Some v) xa \<in> A"
    using exists_assertE[of xa \<Delta> x A] by blast
  moreover have "pure_larger (assign_var_state x (Some v) x') (assign_var_state x (Some v) xa)"
  proof -
    obtain p where "pure p" "Some x' = xa \<oplus> p"
      using asm0(1) pure_larger_def by blast
    then have "Some (assign_var_state x (Some v) x') = assign_var_state x (Some v) xa \<oplus> assign_var_state x (Some v) p"
      using assign_var_state_sum by blast
    then show ?thesis
      using \<open>pure p\<close> assign_var_state_sum pure_def pure_larger_def by blast
  qed
  then have "assign_var_state x (Some v) x' \<in> A"
    using wf_assertionE[OF assms(1)] r(2) by blast
  then show "x' \<in> exists_assert \<Delta> x A"
    by (metis (no_types, lifting) asm0(1) full_add_charact(1) in_exists_assert pure_larger_def r(1) r(2))
qed


lemma SL_proof_Havoc_list_elim:
  assumes "\<Delta> \<turnstile> [A] havoc_list l [B]"
      and "wf_abs_stmt \<Delta> (havoc_list l)"
      and "finite_context \<Delta>"
  shows "self_framing A \<and> self_framing B \<and> entails_typed \<Delta> A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - (set l)"
  using assms
proof (induct l arbitrary: A B)
  case Nil
  then show ?case using SL_proof_Skip_elim
    using entails_typed_refl by force
next
  case (Cons x l)
  then obtain R where r: "\<Delta> \<turnstile> [A] Havoc x [R]" "\<Delta> \<turnstile> [R] havoc_list l [B]"
    by (metis SL_proof_Seq_elim havoc_list.simps(2))
  then have "R = exists_assert \<Delta> x A"
    by blast
  then have "self_framing B \<and> entails_typed \<Delta> R B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> R - set l"
    using Cons r by simp
  moreover have "variables \<Delta> x \<noteq> None"
    using Cons.prems(2) by force

  then have "entails_typed \<Delta> R B \<and> free_vars \<Delta> R \<subseteq> free_vars \<Delta> A - {x}"
    by (simp add: Cons.prems(3) SL_proof_Havoc_elim_entails calculation r(1))
  ultimately show "self_framing A \<and> self_framing B \<and> entails_typed \<Delta> A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - set (x # l)"
    by (smt (verit, ccfv_SIG) Cons.prems(3) DiffD2 DiffI Diff_subset SL_proof_Havoc_elim_entails \<open>variables \<Delta> x \<noteq> None\<close> entails_typed_trans insert_iff list.simps(15) r(1) SL_proof_Havoc_elim subset_eq)
qed


lemma stabilize_rel:
  assumes "Some \<omega> = a \<oplus> p"
  shows "\<exists>p'. Some \<omega> = stabilize a \<oplus> p' \<and> Some p' = p \<oplus> |\<omega>|"
proof -
  obtain p' where "Some p' = p \<oplus> |\<omega>|"
    using assms minus_equiv_def_any_elem by blast
  then show ?thesis
    by (smt (verit, ccfv_SIG) assms asso1 decompose_stabilize_pure greater_equiv plus_pure_stabilize_eq smaller_than_core stabilize_sum)
qed

lemma state_in_purify_add:
  assumes "\<omega> \<in> A"
      and "Some True = b \<omega>"
      and "wf_exp b"
      and "typed \<Delta> \<omega>"
    shows "\<omega> \<in> A \<otimes> purify b"
proof -
  have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
    by (simp add: core_is_smaller)
  moreover have "|\<omega>| \<in> purify b"
    by (smt (verit, ccfv_threshold) CollectI assms(2) assms(3) assms(4) max_projection_prop_def max_projection_prop_pure_core purify_def  typed_core wf_exp_def)
  ultimately show ?thesis
    using assms(1) x_elem_set_product by blast
qed




section \<open>Reciprocal\<close>

theorem SL_proof_implies_Viper:
  assumes "\<Delta> \<turnstile> [A] C [B]"
      and "\<omega> \<in> A"
      and "wf_abs_stmt \<Delta> C"
      and "stable \<omega>"
      and "typed \<Delta> \<omega>"
    shows "\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> B"
  using assms
proof (induct arbitrary: \<omega> rule: SL_proof.induct)
  case (RuleSkip \<Delta> T)
  then show ?case
    using RedSkip by blast
next
  case (RuleSeq \<Delta> A C1 R C2 B)
  then obtain S1 where S1_def: "red_stmt \<Delta> C1 \<omega> S1" "S1 \<subseteq> R"
    using wf_abs_stmt.simps(7) by blast
  let ?f = "\<lambda>\<omega>. SOME S2. red_stmt \<Delta> C2 \<omega> S2 \<and> S2 \<subseteq> B"
  have r: "\<And>\<omega>. \<omega> \<in> S1 \<Longrightarrow> red_stmt \<Delta> C2 \<omega> (?f \<omega>) \<and> (?f \<omega>) \<subseteq> B"
  proof -
    fix \<omega>'
    assume "\<omega>' \<in> S1"
    then obtain S2 where "red_stmt \<Delta> C2 \<omega>' S2 \<and> S2 \<subseteq> B"
      by (metis RuleSeq.hyps(4) RuleSeq.prems(2) RuleSeq.prems(3) RuleSeq.prems(4) S1_def(1) S1_def(2) red_wf_state subsetD wf_abs_stmt.simps(7) wf_state_def)
    then show "red_stmt \<Delta> C2 \<omega>' (?f \<omega>') \<and> (?f \<omega>') \<subseteq> B"
      using someI by (metis (mono_tags))
  qed
  let ?S2 = "Union (?f ` S1)"
  have "red_stmt \<Delta> (C1 ;; C2) \<omega> ?S2"
  proof (rule RedSeq[OF S1_def(1), of C2])
    show "sequential_composition \<Delta> S1 C2 ?S2"
      using SeqComp by (simp add: r)
  qed
  moreover have "?S2 \<subseteq> B"
    by (simp add: SUP_least r)
  ultimately show ?case by meson
next
  case (RuleInhale A P \<Delta>)
  moreover have "red_stmt \<Delta> (abs_stmt.Inhale P) \<omega> (Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> P))"
  proof (rule RedInhale[of \<omega> P \<Delta>])
    show "rel_stable_assertion \<omega> P"
      using calculation(2) calculation(3) calculation(5) framed_by_def by blast
  qed
  moreover have "Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> P) \<subseteq> A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P"
  proof
    fix x assume asm0: "x \<in> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> P)"
    then obtain p where "sep_algebra_class.stable x \<and> typed \<Delta> x" "p \<in> P" "Some x = \<omega> \<oplus> p"
      using in_singleton_star by force
    then have "typed \<Delta> (stabilize p)"
      using greater_equiv stabilize_sum_of_stable typed_state.typed_smaller typed_state_axioms by blast
    then show "x \<in> A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P"
      using \<open>Some x = \<omega> \<oplus> p\<close> \<open>p \<in> P\<close> calculation(3) x_elem_set_product by fastforce
  qed
  ultimately show "\<exists>S. red_stmt \<Delta> (abs_stmt.Inhale P) \<omega> S \<and> S \<subseteq> A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P"
    by meson
next
  case (RuleExhale B A P \<Delta>)
  then obtain a p where "a \<in> A" "p \<in> P" "Some \<omega> = a \<oplus> p"
    by (meson entails_def subsetD x_elem_set_product)
  then obtain p' where "Some p' = p \<oplus> |\<omega>|" "Some \<omega> = stabilize a \<oplus> p'"
    using stabilize_rel by blast
  then have "red_stmt \<Delta> (abs_stmt.Exhale P) \<omega> {stabilize a}"
    using RedExhale[of p' P \<omega> "stabilize a" \<Delta>]
    by (meson RuleExhale.prems(3) \<open>Some \<omega> = a \<oplus> p\<close> \<open>p \<in> P\<close> RedExhale stabilize_is_stable stabilize_sum_result_stable)
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.Exhale P) \<omega> S \<and> S \<subseteq> A"
    by (meson RuleExhale.hyps(3) \<open>a \<in> A\<close> bot.extremum insert_subsetI self_framing_def)
next
  case (RuleAssert A P \<Delta>)
  then have "red_stmt \<Delta> (abs_stmt.Assert P) \<omega> {\<omega>}"
    using RedAssertTrue[of \<omega> P \<Delta>] by (meson entails_def subset_iff)
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.Assert P) \<omega> S \<and> S \<subseteq> A"
    by (meson RuleAssert.prems(1) empty_subsetI insert_subsetI)
next
  case (RuleAssume A P \<Delta>)
  then have "(\<forall>\<omega>\<in>A. (stabilize \<omega> \<in> P) = (\<omega> \<in> P))"
    using self_framing_on_def by blast
(*
  self_framing_on A P = (\<forall>\<omega>\<in>A. (stabilize \<omega> \<in> P) = (\<omega> \<in> P))
*)
  moreover have asm0: "stable_on \<omega> P"
  proof (rule stable_onI)
    fix x assume "pure_larger x \<omega>"
    then have "x \<in> A"
      by (metis RuleAssume.hyps(1) RuleAssume.prems(1) in_Stabilize pure_larger_stabilize_same self_framing_eq)
    then show "(\<omega> \<in> P) = (x \<in> P)"
      by (metis RuleAssume.prems(1) \<open>\<forall>\<omega>\<in>A. (stabilize \<omega> \<in> P) = (\<omega> \<in> P)\<close> \<open>pure_larger x \<omega>\<close> pure_larger_stabilize_same)
  qed
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.Assume P) \<omega> S \<and> S \<subseteq> A \<inter> P"
  proof (cases "\<omega> \<in> P")
    case True
    then show ?thesis
      by (meson IntI RedAssumeTrue RuleAssume.prems(1) asm0 empty_subsetI insert_subsetI)
  next
    case False
    then show ?thesis
      using RedAssumeFalse asm0 by blast
  qed
next
  case (RuleHavoc A \<Delta> x)
  then obtain ty where ty_def: "variables \<Delta> x = Some ty"
    by auto
  then have "red_stmt \<Delta> (abs_stmt.Havoc x) \<omega> {assign_var_state x (Some v) \<omega> |v. v \<in> ty}"
    using RedHavoc by blast
  moreover have "{assign_var_state x (Some v) \<omega> |v. v \<in> ty} \<subseteq> exists_assert \<Delta> x A"
  proof
    fix \<omega>' assume "\<omega>' \<in> {assign_var_state x (Some v) \<omega> |v. v \<in> ty}"
    then obtain v where "v \<in> ty" "\<omega>' = assign_var_state x (Some v) \<omega>"
      by blast
    moreover obtain v0 where "v0 \<in> ty" "get_store \<omega> x = Some v0"
      using RuleHavoc.prems(3) RuleHavoc.prems(4) semantics.wf_state_then_value semantics_axioms ty_def wf_state_def by blast
    ultimately show "\<omega>' \<in> exists_assert \<Delta> x A"
      using exists_assertI[of v ty \<omega>' x \<Delta> v0 A]
      by (metis RuleHavoc.prems(1) assign_var_state_def assign_var_state_inverse fun_upd_same get_store_set_store ty_def)
  qed
  ultimately show "\<exists>S. red_stmt \<Delta> (abs_stmt.Havoc x) \<omega> S \<and> S \<subseteq> exists_assert \<Delta> x A"
    by meson
next
  case (RuleLocalAssign A e \<Delta> x)
  then obtain ty where ty_def: "variables \<Delta> x = Some ty"
    by auto
  moreover obtain v where "e \<omega> = Some v"
    by (meson RuleLocalAssign.hyps(2) RuleLocalAssign.prems(1) domD domIff framed_by_exp_def)
  ultimately have "red_stmt \<Delta> (abs_stmt.LocalAssign x e) \<omega> {assign_var_state x (Some v) \<omega>}"
    using RedLocalAssign[of \<Delta> x ty e \<omega> v]
    by (metis RuleLocalAssign.prems(2) option.sel typed_exp_def wf_abs_stmt.simps(8))
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.LocalAssign x e) \<omega> S \<and> S \<subseteq> post_substitute_var_assert x e A"
    by (metis (no_types, lifting) RuleLocalAssign.prems(1) image_insert insert_iff mk_disjoint_insert post_substitute_var_assert_def red_stmt_Assign_elim singletonD subsetI substitute_var_state_def)
next
  case (RuleIf A b \<Delta> C1 B1 C2 B2)
  then have ty: "typed \<Delta> \<omega>"
    by blast
  show "\<exists>S. red_stmt \<Delta> (abs_stmt.If b C1 C2) \<omega> S \<and> S \<subseteq> B1 \<union> B2"
  proof (cases "b \<omega> = Some True")
    case True
    moreover have "\<exists>S. red_stmt \<Delta> C1 \<omega> S \<and> S \<subseteq> B1"
    proof (rule RuleIf(4))
      show "\<omega> \<in> A \<otimes> purify b"
        using RuleIf.prems(1) RuleIf.prems(2) ty calculation state_in_purify_add[of \<omega> A b \<Delta>]
        by fastforce
      show "wf_abs_stmt \<Delta> C1"
        using RuleIf.prems(2) by auto
    qed (simp_all add: RuleIf)
    ultimately show ?thesis
      using RedIfTrue[of b \<omega> \<Delta> C1 _ C2] by blast
  next
    case False
    then have "b \<omega> = Some False"
      by (metis (mono_tags, lifting) RuleIf.hyps(2) RuleIf.prems(1) framed_by_exp_def option.exhaust)
    moreover have "\<exists>S. red_stmt \<Delta> C2 \<omega> S \<and> S \<subseteq> B2"
    proof (rule RuleIf(6))
      show "\<omega> \<in> A \<otimes> purify (negate b)"
        by (smt (verit, del_insts) RuleIf.hyps(2) RuleIf.prems(1) RuleIf.prems(2) ty calculation framed_by_exp_def negate_def option.sel state_in_purify_add wf_abs_stmt.simps(6)  wf_exp_negate)
      show "wf_abs_stmt \<Delta> C2"
        using RuleIf.prems(2) by auto
    qed (simp_all add: RuleIf)
    ultimately show ?thesis
      using RedIfFalse[of b \<omega> \<Delta> C2 _ C1] by blast
  qed
next
  case (RuleCustom A B \<Delta> C)
  then show ?case using red_wf_complete[OF \<open>SL_Custom \<Delta> A C B\<close>]
    by (meson RedCustom wf_abs_stmt.simps(10))
qed

lemma greater_singletonI:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "{\<omega>'} \<ggreater> {\<omega>}"
  using assms greater_set_singleton by blast

thm red_stmt_sequential_composition.inducts(1)[of \<Delta> C \<omega> S
"\<lambda>\<Delta> C \<omega> S. \<forall>\<omega>'. \<omega>' \<succeq> \<omega> \<longrightarrow> wf_abs_stmt \<Delta> C \<longrightarrow> (\<exists>S'. red_stmt \<Delta> C \<omega>' S' \<and> S' \<ggreater> S)"
"\<lambda>\<Delta> S1 C S2. \<forall>S1'. S1' \<ggreater> S1 \<longrightarrow> (\<exists>S2'. sequential_composition \<Delta> S1' C S2' \<and> S2' \<ggreater> S2)"]

thm red_stmt_sequential_composition.inducts

lemma assign_state_larger:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "assign_var_state x (Some v) \<omega>' \<succeq> assign_var_state x (Some v) \<omega>"
  apply (rule greater_prodI)
   apply (meson assign_var_state_sum assms greater_equiv greater_prod_eq)
  by (meson assign_var_state_sum assms greater_def greater_prod_eq)


definition mono_custom where
  "mono_custom \<Delta> \<longleftrightarrow> (\<forall>C \<omega> \<omega>' S. \<omega>' \<succeq> \<omega> \<and> red_custom_stmt \<Delta> C \<omega> S \<longrightarrow> (\<exists>S'. red_custom_stmt \<Delta> C \<omega>' S' \<and> S' \<ggreater> S))"

fun no_assert_assume where
  "no_assert_assume (Assert _) \<longleftrightarrow> False"
| "no_assert_assume (Assume _) \<longleftrightarrow> False"
| "no_assert_assume (C1;; C2) \<longleftrightarrow> no_assert_assume C1 \<and> no_assert_assume C2"
| "no_assert_assume (If _ C1 C2) \<longleftrightarrow> no_assert_assume C1 \<and> no_assert_assume C2"
| "no_assert_assume _ \<longleftrightarrow> True"


abbreviation all_stable where
  "all_stable S \<equiv> (\<forall>\<omega>\<in>S. stable \<omega>)"


lemma monotonicity:
  assumes "wf_abs_stmt \<Delta> C"
      and "mono_custom \<Delta>"
      and "no_assert_assume C"
    shows "red_stmt \<Delta> C \<omega> S \<Longrightarrow> (\<forall>\<omega>'. stable \<omega>' \<and> \<omega>' \<succeq> \<omega> \<longrightarrow> (\<exists>S'. red_stmt \<Delta> C \<omega>' S' \<and> S' \<ggreater> S))"
      and "sequential_composition \<Delta> S1 C S2 \<Longrightarrow> (\<forall>S1'. all_stable S1' \<and> S1' \<ggreater> S1 \<longrightarrow> (\<exists>S2'. sequential_composition \<Delta> S1' C S2' \<and> S2' \<ggreater> S2))"
  using assms
proof (induct rule: red_stmt_sequential_composition.inducts)
  case (SeqComp S1 \<Delta> C f S2)
  show "\<forall>S1'. all_stable S1' \<and> S1' \<ggreater> S1 \<longrightarrow> (\<exists>S2'. sequential_composition \<Delta> S1' C S2' \<and> S2' \<ggreater> S2)"
  proof clarify
    fix S1' 
    let ?f1 = "\<lambda>\<omega>1'. (SOME S'. \<exists>\<omega>1 \<in> S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1)"

    assume asm0: "all_stable S1'" "S1' \<ggreater> S1"
    then have "\<And>\<omega>1'. \<omega>1' \<in> S1' \<Longrightarrow> (\<exists>\<omega>1\<in>S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1))"
      by (simp add: SeqComp.hyps(1) greater_set_def)
    moreover have r: "\<And>\<omega>1'. \<omega>1' \<in> S1' \<Longrightarrow> (\<exists>\<omega>1 \<in> S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' (?f1 \<omega>1') \<and> (?f1 \<omega>1') \<ggreater> f \<omega>1)"
      subgoal for \<omega>1'
        apply (rule someI_ex[of "\<lambda>S'. \<exists>\<omega>1 \<in> S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1"])
        by (meson SeqComp.hyps(2) SeqComp.prems(1) SeqComp.prems(2) SeqComp.prems(3) asm0 calculation)
      done
    let ?S2 = "\<Union> (?f1 ` S1')"
    have "sequential_composition \<Delta> S1' C ?S2"
      by (metis (no_types, lifting) r red_stmt_sequential_composition.SeqComp)
    moreover have "?S2 \<ggreater> S2"
    proof (rule greater_setI)
      fix a assume asm0: "a \<in> (\<Union>\<omega>1'\<in>S1'. SOME S'. \<exists>\<omega>1 \<in> S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1)"
      then obtain \<omega>1' where "\<omega>1'\<in>S1'" "a \<in> ?f1 \<omega>1'"
        by blast
      then obtain \<omega>1 where "\<omega>1 \<in> S1 \<and> \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' (?f1 \<omega>1') \<and> (?f1 \<omega>1') \<ggreater> f \<omega>1"
        using r by blast
      then obtain b where "b \<in> f \<omega>1" "a \<succeq> b"
        using \<open>a \<in> (SOME S'. \<exists>\<omega>1\<in>S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1)\<close> greater_set_def by blast
      then show "\<exists>b\<in>S2. a \<succeq> b"
        using SeqComp.hyps(3) \<open>\<omega>1 \<in> S1 \<and> \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' (SOME S'. \<exists>\<omega>1\<in>S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1) \<and> (SOME S'. \<exists>\<omega>1\<in>S1. \<omega>1' \<succeq> \<omega>1 \<and> red_stmt \<Delta> C \<omega>1 (f \<omega>1) \<and> red_stmt \<Delta> C \<omega>1' S' \<and> S' \<ggreater> f \<omega>1) \<ggreater> f \<omega>1\<close> by blast
    qed
    ultimately show "\<exists>S2'. sequential_composition \<Delta> S1' C S2' \<and> S2' \<ggreater> S2"
      by meson
  qed
next
  case (RedSkip \<Delta> \<omega>)
  then show ?case
    using greater_singletonI red_stmt_sequential_composition.RedSkip by blast
next
  case (RedInhale \<omega> A \<Delta>)
  have "\<And>\<omega>''. sep_algebra_class.stable \<omega>'' \<Longrightarrow> \<omega>'' \<succeq> \<omega> \<Longrightarrow> (\<exists>S'. red_stmt \<Delta> (abs_stmt.Inhale A) \<omega>'' S' \<and> S' \<ggreater> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A))"
  proof -
    fix \<omega>'' assume asm0: "sep_algebra_class.stable \<omega>''" "\<omega>'' \<succeq> \<omega>"
    then obtain r where "Some \<omega>'' = \<omega> \<oplus> r"
      using greater_def by blast
    then have "Some \<omega>'' = \<omega> \<oplus> stabilize r"
      by (metis (no_types, lifting) asm0(1) commutative stabilize_sum_result_stable)

    have "rel_stable_assertion \<omega>'' A"
    proof (rule rel_stable_assertionI)
      fix \<omega>' a assume asm1: "a \<in> A" "Some \<omega>' = \<omega>'' \<oplus> a"
      then obtain x where "Some x = \<omega> \<oplus> a"
        using asm0 compatible_smaller by blast
      then obtain a' where "Some (stabilize x) = \<omega> \<oplus> a' \<and> a' \<in> A"
        using rel_stable_assertionE[OF RedInhale(1), of x a]
        using asm1 by blast
      then have "Some (stabilize \<omega>') = stabilize x \<oplus> stabilize r"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>'' = \<omega> \<oplus> r\<close> \<open>Some x = \<omega> \<oplus> a\<close> asm1(2) asso1 commutative stabilize_sum)
      then have "Some (stabilize \<omega>') = \<omega>'' \<oplus> a'"
        by (metis (no_types, opaque_lifting) \<open>Some (stabilize x) = \<omega> \<oplus> a' \<and> a' \<in> A\<close> \<open>Some \<omega>'' = \<omega> \<oplus> stabilize r\<close> asso1 commutative)
      then show "\<exists>a'\<in>A. Some (stabilize \<omega>') = \<omega>'' \<oplus> a'"
        using \<open>Some (stabilize x) = \<omega> \<oplus> a' \<and> a' \<in> A\<close> by blast
    qed
    then have "red_stmt \<Delta> (abs_stmt.Inhale A) \<omega>'' (Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>''} \<otimes> A))"
      using red_stmt_sequential_composition.RedInhale[of \<omega>'' A \<Delta>] by blast
    moreover have "Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>''} \<otimes> A) \<ggreater> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)"
    proof (rule greater_setI)
      fix x assume "x \<in> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>''} \<otimes> A)"
      then obtain a where "sep_algebra_class.stable x \<and> typed \<Delta> x" "Some x = \<omega>'' \<oplus> a" "a \<in> A"
        using in_singleton_star by force      
      then obtain y where "Some y = \<omega> \<oplus> a"
        using asm0(2) compatible_smaller by blast
      then obtain a' where "Some (stabilize y) = \<omega> \<oplus> a' \<and> a' \<in> A"        
        using RedInhale.hyps \<open>a \<in> A\<close> rel_stable_assertionE by blast
      then have "typed \<Delta> (stabilize y)"
        using \<open>Some x = \<omega>'' \<oplus> a\<close> \<open>Some y = \<omega> \<oplus> a\<close> \<open>sep_algebra_class.stable x \<and> typed \<Delta> x\<close> addition_bigger asm0(2) typed_smaller typed_then_stabilize_typed by blast
      then have "stabilize y \<in> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)"
        by (simp add: \<open>Some (stabilize y) = \<omega> \<oplus> a' \<and> a' \<in> A\<close> is_in_set_sum)
      then show "\<exists>b\<in>Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A). x \<succeq> b"
        by (meson \<open>Some x = \<omega>'' \<oplus> a\<close> \<open>Some y = \<omega> \<oplus> a\<close> \<open>sep_algebra_class.stable x \<and> typed \<Delta> x\<close> addition_bigger asm0(2) core_stabilize_mono(2) stabilize_sum stabilize_sum_of_stable)
    qed
    ultimately show "\<exists>S'. red_stmt \<Delta> (abs_stmt.Inhale A) \<omega>'' S' \<and> S' \<ggreater> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)"
      by meson
  qed
  then show "\<forall>\<omega>'. sep_algebra_class.stable \<omega>' \<and> \<omega>' \<succeq> \<omega> \<longrightarrow>
             (\<exists>S'. red_stmt \<Delta> (abs_stmt.Inhale A) \<omega>' S' \<and> S' \<ggreater> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A))"
    by blast
next
  case (RedExhale a A \<omega> \<omega>' \<Delta>)
  have "\<And>\<omega>''. sep_algebra_class.stable \<omega>'' \<Longrightarrow> \<omega>'' \<succeq> \<omega> \<Longrightarrow> (\<exists>S'. red_stmt \<Delta> (abs_stmt.Exhale A) \<omega>'' S' \<and> S' \<ggreater> {\<omega>'})"
  proof -
    fix \<omega>'' assume "sep_algebra_class.stable \<omega>''" "\<omega>'' \<succeq> \<omega>"
    then obtain r where "Some \<omega>'' = \<omega> \<oplus> r" unfolding greater_def by blast
    then obtain y where "Some y = \<omega>' \<oplus> stabilize r"
      by (metis (no_types, opaque_lifting) RedExhale.hyps(2) RedExhale.hyps(3) already_stable compatible_smaller greater_def stabilize_sum)
    then have "Some \<omega>'' = y \<oplus> a"
      using RedExhale.hyps(2)
        stabilize_sum_result_stable[OF _ \<open>sep_algebra_class.stable \<omega>''\<close>, of r \<omega>] commutative[of r \<omega>]
      by (metis (no_types, lifting) \<open>Some \<omega>'' = \<omega> \<oplus> r\<close> asso1 commutative)
    then have "red_stmt \<Delta> (abs_stmt.Exhale A) \<omega>'' {y}"
      using red_stmt_sequential_composition.RedExhale[of a A \<omega>'' y]
      using RedExhale.hyps(1) RedExhale.hyps(3) \<open>Some y = \<omega>' \<oplus> stabilize r\<close> stabilize_is_stable stable_sum by blast
    then show "\<exists>S'. red_stmt \<Delta> (abs_stmt.Exhale A) \<omega>'' S' \<and> S' \<ggreater> {\<omega>'}"
      by (metis \<open>Some y = \<omega>' \<oplus> stabilize r\<close> commutative greater_equiv greater_singletonI)
  qed
  then show "\<forall>\<omega>''. sep_algebra_class.stable \<omega>'' \<and> \<omega>'' \<succeq> \<omega> \<longrightarrow> (\<exists>S'. red_stmt \<Delta> (abs_stmt.Exhale A) \<omega>'' S' \<and> S' \<ggreater> {\<omega>'})" by simp
next
  case (RedIfTrue b \<omega> \<Delta> C1 S C2)
  then show ?case
    apply simp
    using wf_expE[of b _ \<omega> True]
    by (meson red_stmt_sequential_composition.RedIfTrue)
next
  case (RedIfFalse b \<omega> \<Delta> C2 S C1)
  then show ?case
    apply simp
    using wf_expE[of b _ \<omega> False]
    by (meson red_stmt_sequential_composition.RedIfFalse)
next
  case (RedSeq \<Delta> C1 \<omega> S1 C2 S2)
  then show ?case
    by (metis no_assert_assume.simps(3) red_stable red_stmt_sequential_composition.RedSeq wf_abs_stmt.simps(7))
next
  case (RedLocalAssign \<Delta> x ty e \<omega> v)
  then show ?case
    apply simp
    using wf_expE[of e _ \<omega> v]
    by (meson assign_state_larger greater_set_singleton red_stmt_sequential_composition.RedLocalAssign)
next
  case (RedHavoc \<Delta> x ty \<omega>)
  have "\<And>\<omega>'. \<omega>' \<succeq> \<omega> \<Longrightarrow> {assign_var_state x (Some v) \<omega>' |v. v \<in> ty} \<ggreater> {assign_var_state x (Some v) \<omega> |v. v \<in> ty}"
  proof -
    fix \<omega>' assume asm0: "\<omega>' \<succeq> \<omega>"
    show "{assign_var_state x (Some v) \<omega>' |v. v \<in> ty} \<ggreater> {assign_var_state x (Some v) \<omega> |v. v \<in> ty}"
    proof (rule greater_setI)
      fix a assume "a \<in> {assign_var_state x (Some v) \<omega>' |v. v \<in> ty}"
      then obtain v where "a = assign_var_state x (Some v) \<omega>'" "v \<in> ty"
        by blast
      then have "a \<succeq> assign_var_state x (Some v) \<omega>"
        by (simp add: asm0 assign_state_larger)
      then show "\<exists>b\<in>{assign_var_state x (Some v) \<omega> |v. v \<in> ty}. a \<succeq> b"
        using \<open>v \<in> ty\<close> by blast
    qed
  qed
  then show "\<forall>\<omega>'. sep_algebra_class.stable \<omega>' \<and> \<omega>' \<succeq> \<omega> \<longrightarrow> (\<exists>S'. red_stmt \<Delta> (abs_stmt.Havoc x) \<omega>' S' \<and> S' \<ggreater> {assign_var_state x (Some v) \<omega> |v. v \<in> ty})"
    using RedHavoc.hyps red_stmt_sequential_composition.RedHavoc by blast
next
  case (RedCustom \<Delta> C \<omega> S)
  then show ?case unfolding mono_custom_def
    by (meson red_stmt_sequential_composition.RedCustom)
qed (simp_all)

lemma inhale_c_exhale_verifies_simplifies:
  assumes "\<And>\<omega>. sep_algebra_class.stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> |\<omega>| \<in> A"
      and "verifies_set \<Delta> P (Inhale A;; C;; Exhale B)"
    shows "verifies_set \<Delta> P C"
proof (rule verifies_setI)
  fix \<omega> assume "\<omega> \<in> P" "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  then obtain S where "red_stmt \<Delta> ((Inhale A;; C);; Exhale B) \<omega> S"
    using assms(2) verifies_def verifies_set_def by fastforce
  then show "verifies \<Delta> C \<omega>"
    apply (rule red_stmt_Seq_elim)
    apply (erule red_stmt_Seq_elim)
    apply (erule red_stmt_Inhale_elim)
  proof -
    fix S0 S1 assume "sequential_composition \<Delta> S0 C S1"
      "S0 = Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)"
    then have "|\<omega>| \<in> A"
      by (simp add: \<open>sep_algebra_class.stable \<omega>\<close> \<open>typed \<Delta> \<omega>\<close> assms(1))
    then have "\<omega> \<in> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)"
      by (simp add: \<open>sep_algebra_class.stable \<omega>\<close> \<open>typed \<Delta> \<omega>\<close> core_is_smaller is_in_set_sum)
    then show "verifies \<Delta> C \<omega>"
      using \<open>S0 = Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A)\<close> \<open>sequential_composition \<Delta> S0 C S1\<close> verifies_def by blast
  qed
qed


lemma wf_abs_stmt_havoc_list:
  assumes "set l \<subseteq> dom (variables \<Delta>)"
  shows "wf_abs_stmt \<Delta> (havoc_list l)"
  using assms by (induct l) simp_all


end

end
