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
      and "typed \<Delta> \<omega>"
    shows "\<omega> \<in> exists_assert \<Delta> x A"
  using assms exists_assert_def assign_var_state_def by fast

lemma exists_assertE:
  assumes "\<omega> \<in> exists_assert \<Delta> x A"
  shows "\<exists>v0 v ty. typed \<Delta> \<omega> \<and> v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (assign_var_state x (Some v) \<omega>) \<in> A"
  using assms exists_assert_def assign_var_state_def by auto

lemma stabilize_assign_var:
  "stabilize (assign_var_state x v \<omega>) = assign_var_state x v (stabilize \<omega>)"
  unfolding assign_var_state_def by auto

lemma self_framing_exists_assert:
  assumes "self_framing_typed \<Delta> A"
      and "typed_assertion \<Delta> A"
  shows "self_framing_typed \<Delta> (exists_assert \<Delta> x A)"
proof (rule self_framing_typedI)
  fix \<omega>
  assume asm0: "typed \<Delta> \<omega>"
  show "\<omega> \<in> exists_assert \<Delta> x A \<longleftrightarrow> stabilize \<omega> \<in> exists_assert \<Delta> x A" (is "?A \<longleftrightarrow> ?B")
  proof
    assume "\<omega> \<in> exists_assert \<Delta> x A"
    then obtain v v0 ty where r: "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (assign_var_state x (Some v) \<omega>) \<in> A"
      unfolding exists_assert_def assign_var_state_def by blast
    then have "get_store (stabilize \<omega>) x = Some v0 \<and> set_store (stabilize \<omega>) ((get_store (stabilize \<omega>))(x \<mapsto> v)) = stabilize (assign_var_state x (Some v) \<omega>)"
      by (simp add: assign_var_state_def)
    then show ?B
      by (smt (verit, del_insts) asm0 assms(1) exists_assertI r self_framing_typed_def stabilize_assign_var typed_assign_var typed_then_stabilize_typed)
  next
    assume asm1: ?B
    then obtain v v0 ty where r: "typed \<Delta> (stabilize \<omega>)" "v0 \<in> ty" "get_store (stabilize \<omega>) x = Some v0"
      "variables \<Delta> x = Some ty" "v \<in> ty" "assign_var_state x (Some v) (stabilize \<omega>) \<in> A"      
      by (metis exists_assertE)
    show ?A
      using r(2)
    proof (rule exists_assertI)
      show "get_store \<omega> x = Some v0"
        using r(3) by auto
      show "assign_var_state x (Some v) \<omega> \<in> A"
        using asm0 assms(1) r(4) r(5) r(6) self_framing_typed_altE stabilize_assign_var typed_assign_var by metis
    qed (simp_all add: r asm0)
  qed
qed


lemma typed_assertion_exists_assert:
  assumes "typed_assertion \<Delta> A"
  shows "typed_assertion \<Delta> (exists_assert \<Delta> x A)"
proof (rule typed_assertionI)
  fix \<omega> assume "\<omega> \<in> exists_assert \<Delta> x A"
    then obtain v v0 ty where r: "typed \<Delta> \<omega>" "v0 \<in> ty" "get_store \<omega> x = Some v0"
      "variables \<Delta> x = Some ty" "v \<in> ty" "assign_var_state x (Some v) \<omega> \<in> A"      
      by (metis exists_assertE)
  then show "typed \<Delta> \<omega>"
    by auto
qed


lemma typed_union:
  assumes "typed_assertion \<Delta> A"
      and "typed_assertion \<Delta> B"
    shows "typed_assertion \<Delta> (A \<union> B)"
  using assms(1) assms(2) typed_assertion_def by blast

lemma typed_intersection:
  assumes "typed_assertion \<Delta> A"
  shows "typed_assertion \<Delta> (A \<inter> B)"
  by (meson assms inf.cobounded1 typed_subset)


lemma self_framing_star_alt:
  assumes "self_framing_typed \<Delta> A"
      and "framed_by_alt A P"
      and "wf_assertion \<Delta> A"
    shows "self_framing_typed \<Delta> (A \<otimes> P)"
proof (rule self_framing_typedI)
  fix \<omega> assume asm0: "typed \<Delta> \<omega>"
  show "(\<omega> \<in> A \<otimes> P) = (stabilize \<omega> \<in> A \<otimes> P)"
  proof
    assume "\<omega> \<in> A \<otimes> P"
    then obtain a p where "a \<in> A" "p \<in> P" "Some \<omega> = a \<oplus> p"
      by (meson x_elem_set_product)
    then obtain \<omega>' where "Some \<omega>' = stabilize a \<oplus> p"
      by (metis asso3 commutative decompose_stabilize_pure option.exhaust_sel)
    then have "rel_stable_assertion_alt (stabilize a) P"
      using \<open>a \<in> A\<close> assms(1) assms(2) framed_by_alt_def
      by (metis (no_types, lifting) assms(3) self_framing_typed_def stabilize_is_stable typed_assertionE wf_assertion_def)
    then have "stabilize \<omega>' \<in> {stabilize a} \<otimes> P"
      by (meson Stable_def \<open>Some \<omega>' = stabilize a \<oplus> p\<close> \<open>p \<in> P\<close> in_Stabilize is_in_set_sum rel_stable_assertion_alt_def subsetD)
    moreover have "stabilize \<omega>' = stabilize \<omega>"
      by (metis (no_types, lifting) \<open>Some \<omega> = a \<oplus> p\<close> \<open>Some \<omega>' = stabilize a \<oplus> p\<close> already_stable option.inject stabilize_is_stable stabilize_sum)
    ultimately show "stabilize \<omega> \<in> A \<otimes> P"
      by (metis \<open>a \<in> A\<close> assms(1) assms(3) star_to_singletonI typed_assertionE typed_state.self_framing_typed_def typed_state.wf_assertion_def typed_state_axioms)
  next
    assume "stabilize \<omega> \<in> A \<otimes> P"
    then obtain a p where "a \<in> A" "p \<in> P" "Some (stabilize \<omega>) = a \<oplus> p"
      by (meson x_elem_set_product)
    then obtain a' where "Some a' = a \<oplus> |\<omega>|"
      by (metis (mono_tags, opaque_lifting) asso2 commutative decompose_stabilize_pure option.exhaust_sel)
    then have "Some \<omega> = a' \<oplus> p"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> asso1 commutative decompose_stabilize_pure)
    then have "a' \<in> A" using wf_assertionE[OF assms(3), of a' a]
      by (metis \<open>Some a' = a \<oplus> |\<omega>|\<close> \<open>a \<in> A\<close> asm0 assms(1) assms(3) plus_pure_stabilize_eq typed_state.self_framing_typedE typed_state.self_framing_typed_altE typed_state.typed_assertionE typed_state.typed_core typed_state.typed_sum typed_state_axioms wf_assertion_def)
    then show "\<omega> \<in> A \<otimes> P"
      using \<open>Some \<omega> = a' \<oplus> p\<close> \<open>p \<in> P\<close> x_elem_set_product by blast
  qed
qed


lemma self_framing_typed_star:
  assumes "self_framing_typed \<Delta> A"
      and "framed_by A P" (* TODO: should this be changed as well? *)
    shows "self_framing_typed \<Delta> (A \<otimes> P)"
proof (rule self_framing_typedI)
  fix \<omega>
  assume asm0: "typed \<Delta> \<omega>"
  show "\<omega> \<in> A \<otimes> P \<longleftrightarrow> stabilize \<omega> \<in> A \<otimes> P" (is "?A \<longleftrightarrow> ?B")
  proof
    assume ?A
    then obtain a p where "a \<in> A" "p \<in> P" "Some \<omega> = a \<oplus> p"
      by (meson x_elem_set_product)
    then have "stabilize a \<in> A"
      using asm0 assms(1) greater_def self_framing_typedE typed_smaller by blast
    moreover have "Some (stabilize \<omega>) = stabilize a \<oplus> stabilize p"
      by (simp add: \<open>Some \<omega> = a \<oplus> p\<close> stabilize_sum)
    then have "|stabilize a| ## stabilize p"
      by (meson core_stabilize_mono(1) defined_comm greater_def greater_equiv smaller_compatible smaller_compatible_core)
    then obtain pp where "Some pp = |stabilize a| \<oplus> stabilize p"
      by (metis defined_def not_Some_eq)
    then have "Some (stabilize \<omega>) = stabilize a \<oplus> pp"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = stabilize a \<oplus> stabilize p\<close> asso1 core_is_smaller)
    moreover have "(p \<in> P) = (pp \<in> P)"
    proof (rule rel_stable_assertionE[of "stabilize a" P p pp])
      show "rel_stable_assertion (stabilize a) P"
        using assms(2) framed_by_def stabilize_is_stable \<open>stabilize a \<in> A\<close> by blast
      show "stabilize a ## p"
        by (metis \<open>Some \<omega> = a \<oplus> p\<close> asso2 commutative decompose_stabilize_pure defined_def not_None_eq)
      show "pure_larger pp (stabilize p)"
        by (metis \<open>Some pp = |stabilize a| \<oplus> stabilize p\<close> commutative core_is_pure pure_def pure_larger_def)
      show "pp \<succeq> |stabilize a|"
        using \<open>Some pp = |stabilize a| \<oplus> stabilize p\<close> greater_def by auto
    qed
    ultimately show ?B
      using \<open>p \<in> P\<close> x_elem_set_product by blast
  next
    assume ?B
    then obtain a p where "a \<in> A" "p \<in> P" "Some (stabilize \<omega>) = a \<oplus> p"
      by (meson x_elem_set_product)
    moreover obtain aa where "Some aa = a \<oplus> |\<omega>|"
      by (metis (mono_tags, opaque_lifting) asso2 calculation(3) commutative decompose_stabilize_pure option.exhaust_sel)
    then have "Some \<omega> = aa \<oplus> p"
      by (metis (no_types, lifting) asso1 calculation(3) commutative decompose_stabilize_pure)
    moreover have "aa \<in> A"
      by (metis (no_types, lifting) \<open>Some aa = a \<oplus> |\<omega>|\<close> asm0 assms(1) calculation(1) calculation(4) greater_def plus_pure_stabilize_eq self_framing_typedE self_framing_typed_altE typed_smaller)
    ultimately show ?A
      using x_elem_set_product by blast
  qed
qed


lemma typed_store_update:
  assumes "typed_store \<Delta> \<sigma>"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
    shows "typed_store \<Delta> (\<sigma>(x \<mapsto> v))"
  unfolding typed_store_def
  using assms(1) assms(2) assms(3)
  by (smt (verit, ccfv_SIG) dom_fun_upd fun_upd_other fun_upd_same insert_dom option.discI option.inject typed_store_def)


end








context semantics
begin

\<comment>\<open>Results needed:
1. If state starts stable, then it stays stable
\<close>

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
      by (metis Havoc.hyps(1) Havoc.hyps(2) assign_var_state_def dom_fun_upd get_store_set_store insert_dom option.discI typed_store_def)
    fix x' v' ty' assume asm0: "get_store (assign_var_state x (Some v) \<omega>) x' = Some v'" "variables \<Delta> x' = Some ty'"
    then show "v' \<in> ty'"
      by (metis Havoc.hyps(1) Havoc.hyps(2) Havoc.hyps(3) assign_var_state_def fun_upd_other fun_upd_same get_store_set_store option.inject typed_store_def)
  qed
next
  case (LocalAssign \<Delta> e \<omega> v x ty)
  then show "typed_store \<Delta> (get_store (assign_var_state x (Some v) \<omega>))"
    unfolding typed_store_def assign_var_state_def by auto
qed (auto)

lemma red_stmt_induct_simple_wf [consumes 4, case_names Inhale Exhale Custom Havoc LocalAssign Label]:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "P \<Delta> \<omega>"
      and "wf_abs_stmt \<Delta> C"
      and "\<omega>' \<in> S"
      and "\<And>(A :: ('v, 'a) abs_state assertion) \<omega>' \<omega> \<Delta> a.
        rel_stable_assertion \<omega> A \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> wf_assertion \<Delta> A \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>a (A :: ('v, 'a) abs_state assertion) \<omega> \<omega>' \<Delta>. a \<in> A \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> wf_assertion \<Delta> A \<Longrightarrow> P \<Delta> \<omega>'"
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
    by (simp add: full_add_charact(2) typed_assertion_def typed_def wf_custom_state_sum wf_assertion_def)
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
  assumes "wf_assertion \<Delta> A"
      and "stabilize \<omega> \<in> A"
      and "typed \<Delta> \<omega>"
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
  assumes "self_framing_typed \<Delta> A"
      and "wf_exp e"
      and "framed_by_exp A e"
      and "typed_assertion \<Delta> A"
    shows "self_framing_typed \<Delta> (post_substitute_var_assert x e A)"
proof (rule self_framing_typedI)
  fix \<omega>
  assume asm0: "typed \<Delta> \<omega>"
  show "\<omega> \<in> post_substitute_var_assert x e A \<longleftrightarrow> stabilize \<omega> \<in> post_substitute_var_assert x e A" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain a where "a \<in> A" "\<omega> = substitute_var_state x e a"
      using post_substitute_var_assert_def by blast
    then have "stabilize a \<in> A"
      by (meson assms(1) assms(4) self_framing_typed_def typed_assertion_def)

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
      by (metis \<open>a \<in> A\<close> asm0 assms(1) assms(4) get_abs_state_set_store get_store_stabilize self_framing_typed_def typed_assertion_def typed_def)
    moreover have "\<omega> = set_store ?a ((get_store ?a)(x \<mapsto> v))"
      by (metis \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> \<open>stabilize \<omega> = set_store a ((get_store a)(x \<mapsto> v))\<close> full_state_ext get_abs_state_set_store get_store_set_store get_store_stabilize)
    ultimately show ?P
      by (smt (verit, best) \<open>e a = Some v\<close> assign_var_state_def \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> assms(2) image_eqI post_substitute_var_assert_def substitute_var_state_def wf_exp_stabilize)
  qed
qed

lemma typed_assertion_post_substitute_var_assert:
  assumes "typed_assertion \<Delta> A"
      and "framed_by_exp A e"
      and "variables \<Delta> x = Some ty"
      and "typed_exp ty e"
    shows "typed_assertion \<Delta> (post_substitute_var_assert x e A)"
    by (smt (verit, ccfv_threshold) assms framed_by_expE image_iff post_substitute_var_assert_def substitute_var_state_def typed_assertion_def typed_assign_var typed_exp_def)



lemma proofs_are_self_framing_and_typed:
  assumes "\<Delta> \<turnstile> [P] C [Q]"
      and "wf_abs_stmt \<Delta> C"
  shows "self_framing_and_typed \<Delta> P \<and> self_framing_and_typed \<Delta> Q"
  using assms
proof (induct rule: SL_proof.induct)
  case (RuleInhale \<Delta> A P)
  then show ?case
    by (simp add: self_framing_typed_star typed_star wf_assertion_def)
next
  case (RuleIf A b \<Delta> C1 B1 C2 B2)
  then show ?case
    by (simp add: self_framing_typed_def typed_union)
next
  case (RuleHavoc A \<Delta> x)
  then show ?case
    using self_framing_exists_assert typed_assertion_exists_assert by blast
next
  case (RuleLocalAssign A e \<Delta> x)
  then show ?case
    by (meson self_framing_post_substitute_var_assert typed_assertion_post_substitute_var_assert wf_abs_stmt.simps(8) )
next
  case (RuleAssume A P \<Delta>)
  then show ?case
    by (smt (verit) Int_iff self_framing_on_def self_framing_typed_def typed_intersection)
qed (simp_all)

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
  by (metis assms(1) assms(2) domD domI typed_def typed_store_def wf_state_def)


lemma self_framing_typed_Stabilize_typed_ext:
    assumes "\<And>\<omega>. stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> \<omega> \<in> B"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> typed \<Delta> \<omega>  \<Longrightarrow> \<omega> \<in> B \<Longrightarrow> \<omega> \<in> A"
    shows "Stabilize_typed \<Delta> A = Stabilize_typed \<Delta> B"
  by (smt (verit, ccfv_SIG) Stabilize_typed_def already_stable assms(1) assms(2) in_Stabilize member_filter self_framing_Stabilize_typed self_framing_typed_ext typed_Stabilize_typed)


lemma wf_exp_framed_by_typed:
  assumes "wf_exp b"
      and "framed_by_exp A b"
      and "self_framing_typed \<Delta> A"
    shows "self_framing_typed \<Delta> (A \<otimes> pure_typed \<Delta> b)"
proof (rule self_framing_typedI)
  fix \<omega>
  assume asm0: "typed \<Delta> \<omega>"
  show "\<omega> \<in> A \<otimes> pure_typed \<Delta> b \<longleftrightarrow> stabilize \<omega> \<in> A \<otimes> pure_typed \<Delta> b" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain a r where "Some \<omega> = a \<oplus> r" "a \<in> A" "b r = Some True" "pure r" "typed \<Delta> r"
      by (smt (verit, ccfv_SIG) mem_Collect_eq pure_typed_def x_elem_set_product)
    then obtain r' where "Some r' = stabilize r \<oplus> |stabilize a|"
      by (metis (no_types, opaque_lifting) asso3 commutative core_is_smaller option.exhaust_sel stabilize_sum)
    then have "Some (stabilize \<omega>) = stabilize a \<oplus> r'"
      by (smt (verit) \<open>Some \<omega> = a \<oplus> r\<close> asso1 commutative core_is_smaller stabilize_sum)
    moreover have "stabilize a \<in> A"
      by (metis \<open>Some \<omega> = a \<oplus> r\<close> \<open>a \<in> A\<close> asm0 assms(3) commutative greater_equiv self_framing_typedE typed_smaller)
    moreover have "pure r'"
      by (meson \<open>Some r' = stabilize r \<oplus> |stabilize a|\<close> \<open>pure r\<close> core_is_pure pure_def pure_stable stabilize_sum)
    then have "b r' \<noteq> None"
      by (metis (no_types, opaque_lifting) \<open>Some r' = stabilize r \<oplus> |stabilize a|\<close> assms(1) assms(2) calculation(2) framed_by_exp_def greater_equiv not_Some_eq wf_exp_def)
    then have "b r' = Some True"
      by (smt (verit, ccfv_SIG) \<open>Some \<omega> = a \<oplus> r\<close> \<open>b r = Some True\<close> assms(1) calculation(1) commutative greater_def option.exhaust wf_exp_def wf_exp_stabilize)
    moreover have "typed \<Delta> r'"
      by (metis asm0 calculation(1) commutative greater_def typed_smaller typed_then_stabilize_typed)
    ultimately have "r' \<in> pure_typed \<Delta> b"
      by (simp add: \<open>pure r'\<close> pure_typed_def)   
    then show ?Q
      using \<open>Some (stabilize \<omega>) = stabilize a \<oplus> r'\<close> \<open>stabilize a \<in> A\<close> x_elem_set_product by blast
  next
    assume ?Q
    then obtain a p where "Some (stabilize \<omega>) = a \<oplus> p" "a \<in> A" "pure p" "b p = Some True" "typed \<Delta> p"
      by (smt (verit, best) CollectD pure_typed_def x_elem_set_product)
    then obtain p' where "Some p' = p \<oplus> |\<omega>|"
      by (metis asso2 decompose_stabilize_pure option.exhaust_sel)
    then have "Some \<omega> = a \<oplus> p'"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> asso1 decompose_stabilize_pure)
    then have "b p' \<noteq> None"
      by (metis \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>b p = Some True\<close> assms(1) greater_def option.simps(3) wf_expE)
    then have "p' \<in> pure_typed \<Delta> b"
      using wf_exp_combinedE[OF assms(1), of p True p']
      by (smt (verit, ccfv_threshold) CollectI \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> \<open>Some \<omega> = a \<oplus> p'\<close> \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>b p = Some True\<close> \<open>pure p\<close> asm0 asso1 commutative core_stabilize_mono(1) greater_equiv max_projection_prop_def max_projection_prop_pure_core minusI pure_typed_def  stabilize_is_stable stable_and_sum_pure_same typed_core)
    then show ?P
      by (meson \<open>Some \<omega> = a \<oplus> p'\<close> \<open>a \<in> A\<close> x_elem_set_product)
  qed
qed

lemma stabilize_typed_elem:
  "\<omega> \<in> Stabilize_typed \<Delta> A \<longleftrightarrow> typed \<Delta> \<omega> \<and> stabilize \<omega> \<in> A"
  using Stabilize_typed_def 
  by fastforce


text \<open>fst \<omega> is the past (list of all past states), it represents the real choice. Indeed, imagine
1) {\<omega>1} --> {\<omega>'} --> {\<omega>1'}
2) {\<omega>2} --> {\<omega>'} --> {\<omega>2'}
--> {\<omega>1, \<omega>2} --> {\<omega>'} --> {\<omega>1', \<omega>2'}\<close>


lemma Viper_implies_SL_proof_aux:
  fixes f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "wf_set \<Delta> (snd ` SA)"
    shows "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] C [Stabilize_typed \<Delta> (\<Union>\<omega>\<in>SA. f \<omega>)]"
  using assms
proof (induct C arbitrary: SA f)
  case (Seq C1 C2)
  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"
  let ?SB = "\<Union>\<omega>\<in>SA. f \<omega>"
  let ?B = "Stabilize_typed \<Delta> ?SB"

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

  let ?R' = "Stabilize_typed \<Delta> (\<Union>\<omega>\<in>SA. f1 \<omega>)"

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
  qed (simp add: Seq)

  let ?SR = "\<Union>\<omega>\<in>SA. {snd \<omega> # fst \<omega>} \<times> f1 \<omega>"
  let ?R = "Stabilize_typed \<Delta> (snd ` ?SR)"

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

  have "\<Delta> \<turnstile> [?R] C2 [Stabilize_typed \<Delta> (\<Union> (f2 ` ?SR))]"
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
  then have "?B = Stabilize_typed \<Delta> (\<Union> (f2 ` ?SR))"
    by presburger

  ultimately show "\<Delta> \<turnstile> [?A] C1 ;; C2 [?B]"
    using RuleSeq \<open>\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] C1 [Stabilize_typed \<Delta> (\<Union> (f1 ` SA))]\<close> by force
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

  let ?A1 = "Stabilize_typed \<Delta> (snd ` ?S1)"
  let ?B1 = "Stabilize_typed \<Delta> (\<Union> (f ` ?S1))"

  have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` ?S1)] C1 [Stabilize_typed \<Delta> (\<Union> (f ` ?S1))]"
  proof (rule If(1))
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<Longrightarrow> red_stmt \<Delta> C1 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
    show "wf_abs_stmt \<Delta> C1"
      using If.prems(2) wf_abs_stmt.simps(6) by blast
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)"
      by (metis (no_types, lifting) If.prems(3) \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono inf_sup_ord(3) wf_set_subset)
  qed

  have "framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b"
  proof (rule framed_by_expI)
    fix \<omega> assume "\<omega> \<in> (Stabilize_typed \<Delta> (snd ` SA))"
    then have "stabilize \<omega> \<in> snd ` SA"
      using stabilize_typed_elem by blast
    then show "b \<omega> \<noteq> None"
      by (smt (verit, ccfv_SIG) If.prems(1) If.prems(2) imageE max_projection_prop_def max_projection_prop_stable_stabilize option.distinct(1) red_stmt_If_elim wf_abs_stmt.simps(6) wf_expE)
  qed

  have "?A1 = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b"
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> ?A1"
      using self_framing_Stabilize_typed by blast
    show "self_framing_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b)"
      by (metis (mono_tags, lifting) If.prems(2) \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> self_framing_Stabilize_typed wf_abs_stmt.simps(6) wf_exp_framed_by_typed)
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))"
      using typed_Stabilize_typed by blast
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b)"
      by (simp add: typed_assertion_pure_typed typed_star)
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A1" "typed \<Delta> \<omega>"
    then have "b (stabilize \<omega>) = Some True"
      using stabilize_typed_elem[of \<omega> \<Delta> ] 
      by fastforce
    show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b"
    proof -
      have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        by (metis (no_types, lifting) UnI1 \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> asm0(2) image_Un in_Stabilize member_filter Stabilize_typed_def)
      moreover have "b |\<omega>| = Some True"
        using wf_exp_coreE[of b \<omega>]
        using If.prems(2) \<open>b (stabilize \<omega>) = Some True\<close> already_stable asm0(1) by fastforce
      moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
        by (simp add: core_is_smaller)
      ultimately show ?thesis
        by (smt (verit) CollectI asm0(3) max_projection_prop_def max_projection_prop_pure_core pure_typed_def typed_smaller x_elem_set_product)
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b"
    then have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<and> b \<omega> = Some True"
      by (smt (verit, best) CollectD If.prems(2) add_set_commm in_set_sum pure_typed_def wf_abs_stmt.simps(6)  stable_and_sum_pure_same wf_exp_def x_elem_set_product)
    then show "\<omega> \<in> ?A1"
      by (smt (verit, ccfv_threshold) already_stable asm0(1) image_iff member_filter stabilize_typed_elem)
  qed

  let ?A2 = "Stabilize_typed \<Delta> (snd ` ?S2)"
  let ?B2 = "Stabilize_typed \<Delta> (\<Union> (f ` ?S2))"


  have "?A2 = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)"
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> ?A2"
      using self_framing_Stabilize_typed by blast
    show "self_framing_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b))"
      using If.prems(2) \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> framed_by_negate self_framing_Stabilize_typed wf_exp_framed_by_typed  wf_abs_stmt.simps(6) wf_exp_negate by blast
    
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA))"
      using typed_Stabilize_typed by blast
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b))"
      by (simp add: typed_assertion_pure_typed typed_star)
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A2" "typed \<Delta> \<omega>"
    then have "b (stabilize \<omega>) = Some False"
      using stabilize_typed_elem[of \<omega> \<Delta>] by fastforce
    show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)"
    proof -
      have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        using asm0(2) stabilize_typed_elem[of \<omega> \<Delta>]
        by auto
      moreover have "b |\<omega>| = Some False"
        using wf_exp_coreE[of b \<omega>]
        by (metis If.prems(2) \<open>b (stabilize \<omega>) = Some False\<close> already_stable asm0(1) wf_abs_stmt.simps(6) )
      moreover have "typed \<Delta> |\<omega>|"
        by (simp add: asm0(3) typed_core)
      ultimately have "|\<omega>| \<in> pure_typed \<Delta> (negate b)"
        using negate_def[of b "|\<omega>|"]
        by (smt (verit, ccfv_SIG) CollectI max_projection_prop_def max_projection_prop_pure_core option.discI option.sel pure_typed_def )
      moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
        by (simp add: core_is_smaller)
      ultimately show ?thesis
        using \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)\<close> x_elem_set_product by blast
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)"
      "typed \<Delta> \<omega>"
    then obtain a p where "pure p" "b p = Some False" "Some \<omega> = a \<oplus> p" "a \<in> Stabilize_typed \<Delta> (snd ` SA)"
      by (smt (verit, best) CollectD negate_def option.discI option.exhaust_sel pure_typed_def x_elem_set_product)

    then have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<and> b \<omega> = Some False"
      by (metis If.prems(2) asm0(1) greater_equiv stable_and_sum_pure_same wf_abs_stmt.simps(6) wf_expE)
    then show "\<omega> \<in> ?A2"
      by (smt (verit, ccfv_threshold) already_stable asm0(1) image_iff member_filter stabilize_typed_elem)
  qed

  have "\<Delta> \<turnstile> [?A2] C2 [?B2]"
  proof (rule If(2))
    show "wf_abs_stmt \<Delta> C2"
      using If.prems(2) by auto
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA)"
      by (metis (no_types, lifting) If.prems(3) \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono inf_sup_ord(4) wf_set_subset)
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA \<Longrightarrow> red_stmt \<Delta> C2 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
  qed

  moreover have "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA))"
    using typed_Stabilize_typed by auto
  moreover have "typed_assertion \<Delta> ?B1"
    using typed_Stabilize_typed by auto
  moreover have "typed_assertion \<Delta> ?B2"
    using typed_Stabilize_typed by auto

  moreover have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.If b C1 C2 [?B1 \<union> ?B2]"
    by (metis \<open>Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA) = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)\<close> \<open>Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA) = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b\<close> \<open>\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)] C1 [Stabilize_typed \<Delta> (\<Union> (f ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))]\<close> \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> calculation(1) calculation(2) RuleIf self_framing_Stabilize_typed)

  moreover have "?B1 \<union> ?B2 = Stabilize_typed \<Delta> (\<Union> (f ` SA))"
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> (?B1 \<union> ?B2)"
      using If.prems(2) calculation(5) proofs_are_self_framing_and_typed by presburger
    show "self_framing_typed \<Delta> (Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
      using self_framing_Stabilize_typed by blast
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
      using typed_Stabilize_typed by blast
    show "typed_assertion \<Delta> (?B1 \<union> ?B2)"
      using calculation(3) calculation(4) typed_union by blast

    fix \<omega> :: "('v, 'a) abs_state" assume "stable \<omega>" "typed \<Delta> \<omega>"
    show "\<omega> \<in> ?B1 \<union> ?B2 \<Longrightarrow>  \<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      using stabilize_typed_elem[of \<omega> \<Delta>]
      by force
    show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<Longrightarrow> \<omega> \<in> ?B1 \<union> ?B2"
      using \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> stabilize_typed_elem[of \<omega> \<Delta>]
      by auto
  qed
  ultimately show ?case
    by argo
next
  case (Inhale P)

  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"

  have "\<And>\<omega>. \<omega> \<in> ?A \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> rel_stable_assertion \<omega> P"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> ?A" "stable \<omega>"
    then obtain x where "x \<in> SA" "snd x = \<omega>"
      using already_stable stabilize_typed_elem[of \<omega> \<Delta>]
      by fastforce
    then have "red_stmt \<Delta> (Inhale P) \<omega> (f x)"
      by (metis Inhale.prems(1))
    then show "rel_stable_assertion \<omega> P"
      by force
  qed
  then have r: "framed_by ?A P"
    using framed_by_def by blast
  have "\<Delta> \<turnstile> [?A] Inhale P [?A \<otimes> P]"
  proof (rule RuleInhale)
    show "self_framing_and_typed \<Delta> ?A"
      using self_framing_Stabilize_typed typed_Stabilize_typed by blast
  qed (simp add: r)
  moreover have "self_framing_and_typed \<Delta> (?A \<otimes> P)"
    using Inhale.prems(2) calculation proofs_are_self_framing_and_typed by presburger
  moreover have "Set.filter sep_algebra_class.stable (snd ` SA) \<subseteq> ?A"
    by (smt (verit) Inhale.prems(3) Stabilize_filter_stable member_filter Stabilize_typed_def wf_state_def  subsetD subsetI wf_set_def)

  moreover have "Set.filter sep_algebra_class.stable (?A \<otimes> P) = \<Union> (f ` SA)"
  proof
    show "Set.filter sep_algebra_class.stable (?A \<otimes> P) \<subseteq> \<Union> (f ` SA)"
    proof
      fix \<omega> assume "\<omega> \<in> Set.filter sep_algebra_class.stable (?A \<otimes> P)"
      then obtain a p where asm0: "stable \<omega>" "Some \<omega> = a \<oplus> p" "a \<in> ?A" "p \<in> P" "a \<in> Stabilize_typed \<Delta> (snd ` SA)"
        by (smt (verit, ccfv_threshold) mem_Collect_eq member_filter add_set_def)
      then have "Some \<omega> = stabilize a \<oplus> p"
        using stabilize_sum_result_stable by blast
      moreover obtain l where "l \<in> SA" "snd l = stabilize a"
        using asm0(3) stabilize_typed_elem[of _ \<Delta>] by auto
      then have "red_stmt \<Delta> (Inhale P) (stabilize a) (f l)"
        by (metis Inhale.prems(1))
      then have "f l = Set.filter sep_algebra_class.stable ({stabilize a} \<otimes> P) \<and> rel_stable_assertion (stabilize a) P"
        using red_stmt_Inhale_elim by blast
      then have "\<omega> \<in> f l"
        by (simp add: asm0(1) asm0(4) asm0(5) calculation is_in_set_sum)
      then show "\<omega> \<in> \<Union> (f ` SA)"
        using \<open>l \<in> SA\<close> by blast
    qed
    show "\<Union> (f ` SA) \<subseteq> Set.filter sep_algebra_class.stable (Stabilize_typed \<Delta> (snd ` SA) \<otimes> P)"
    proof 
      fix \<omega> assume "\<omega> \<in> \<Union> (f ` SA)"
      then obtain x where "x \<in> SA" "\<omega> \<in> f x"
        by blast
      then have "red_stmt \<Delta> (Inhale P) (snd x) (f x)"
        using Inhale.prems(1) by blast
      then show "\<omega> \<in> Set.filter sep_algebra_class.stable (Stabilize_typed \<Delta> (snd ` SA) \<otimes> P)"
      proof (rule red_stmt_Inhale_elim)
        assume "f x = Set.filter sep_algebra_class.stable ({snd x} \<otimes> P)"
        then obtain p where "p \<in> P" "Some \<omega> = snd x \<oplus> p" "stable \<omega>"
          by (smt (verit, ccfv_SIG) \<open>\<omega> \<in> f x\<close> member_filter singletonD x_elem_set_product)
        then show "\<omega> \<in> Set.filter sep_algebra_class.stable (Stabilize_typed \<Delta> (snd ` SA) \<otimes> P)"
          by (metis (no_types, lifting) Inhale.prems(3) \<open>\<omega> \<in> f x\<close> \<open>f x = Set.filter sep_algebra_class.stable ({snd x} \<otimes> P)\<close> \<open>x \<in> SA\<close> calculation(3) insertCI insert_image member_filter wf_set_def star_to_singletonI subsetD wf_state_def)
      qed
    qed
  qed
  ultimately show ?case
    by (smt (verit, best) Stabilize_def already_stable mem_Collect_eq member_filter self_framing_typed_ext Stabilize_typed_def self_framing_Stabilize_typed  typed_Stabilize_typed)
next
  case (Exhale P)

  let ?A = "Stabilize_typed \<Delta> (\<Union> (f ` SA))"
  let ?B = "Stabilize_typed \<Delta> (snd ` SA)"

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
    fix \<omega> assume "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
    then have "stabilize \<omega> \<in> snd ` SA"
      using stabilize_typed_elem by blast
    then obtain x where asm0: "x \<in> SA" "stabilize \<omega> = snd x"
      by blast
    then obtain a \<omega>' where "f x = {\<omega>'} \<and> a \<in> P \<and> Some (stabilize \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>'"
      using r by metis
    moreover obtain \<omega>'' where "Some \<omega>'' = \<omega>' \<oplus> |\<omega>|"
      by (metis asso3 calculation commutative decompose_stabilize_pure not_Some_eq) (* long *)
    then have "stabilize \<omega>'' = stabilize \<omega>'" using pure_larger_stabilize_same[of \<omega>'' \<omega>']
      using core_is_pure pure_def pure_larger_def by blast
    moreover have "typed \<Delta> \<omega>''"
      by (meson \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)\<close> calculation(1) greater_def stabilize_typed_elem typed_core typed_smaller typed_state_then_stabilize_typed  typed_sum)
    then have "\<omega>'' \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      by (metis UN_upper already_stable asm0(1) calculation(1) calculation(2) insert_subset stabilize_typed_elem )
    moreover have "Some \<omega> = \<omega>'' \<oplus> a"
      by (metis (no_types, lifting) \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> asso1 calculation(1) commutative decompose_stabilize_pure)
    ultimately show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<otimes> P"
      using x_elem_set_product by blast
  qed

  moreover show "\<Delta> \<turnstile> [?B] Exhale P [?A]"
  proof (rule RuleExhale)
    show "self_framing_and_typed \<Delta> (Stabilize_typed \<Delta> (\<Union> (f ` SA)))"      
      using self_framing_Stabilize_typed typed_Stabilize_typed by blast
    show "self_framing_and_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA))"
      using self_framing_Stabilize_typed typed_Stabilize_typed by blast
    show "entails (Stabilize_typed \<Delta> (snd ` SA)) (Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<otimes> P)"
      using calculation(2) by simp
  qed
next
  case (Assert P)
  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>} \<and> snd \<omega> \<in> P"
    using Assert.prems(1) by blast
  moreover have "entails (Stabilize_typed \<Delta> (snd ` SA)) P"
  proof (rule entailsI)
    fix \<omega> assume "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
    then have "stabilize \<omega> \<in> snd ` SA \<and> typed \<Delta> \<omega>"
      using stabilize_typed_elem by blast
    then have "stabilize \<omega> \<in> P"
      using r by force
    then show "\<omega> \<in> P" using wf_assertion_stabilize Assert(2)
      using \<open>stabilize \<omega> \<in> snd ` SA \<and> typed \<Delta> \<omega>\<close> wf_abs_stmt.simps(4) by blast
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
  let ?A = "post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"

  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>v. variables \<Delta> x = Some ?ty \<and> e (snd \<omega>) = Some v \<and> v \<in> ?ty
  \<and> f \<omega> = { assign_var_state x (Some v) (snd \<omega>) })"
    using LocalAssign.prems(1) by fastforce

  have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.LocalAssign x e [?A]"
  proof (rule RuleLocalAssign)
    show "framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) e"
    proof (rule framed_by_expI)
      fix \<omega> assume "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
      then have "stabilize \<omega> \<in> snd ` SA"
        using stabilize_typed_elem by blast
      then obtain v where "variables \<Delta> x = Some ?ty \<and> e (stabilize \<omega>) = Some v \<and> v \<in> ?ty"
        using r by fastforce
      moreover have "wf_exp e"
        using LocalAssign(2) by auto
      ultimately have "e \<omega> = Some v"
        by (meson max_projection_prop_stable_stabilize mpp_smaller wf_expE)
      then show "e \<omega> \<noteq> None" by simp
    qed
  qed (simp)
  moreover have "?A = Stabilize_typed \<Delta> (\<Union> (f ` SA))" (is "?A = ?B")
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> (post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA)))"
      using LocalAssign.prems(2) calculation proofs_are_self_framing_and_typed by blast
    show "typed_assertion \<Delta> (post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA)))"
      using LocalAssign.prems(2) calculation proofs_are_self_framing_and_typed by blast

    fix \<omega> assume asm0: "stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"
    then obtain \<omega>' where "\<omega>' \<in> Stabilize_typed \<Delta> (snd ` SA)" "\<omega> = assign_var_state x (e \<omega>') \<omega>'"
      using post_substitute_var_assert_def substitute_var_state_def by fastforce
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' = snd \<alpha>"
      by (meson image_iff stabilize_typed_elem)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> e (stabilize \<omega>') = Some v \<and> v \<in> ?ty
  \<and> f \<alpha> = {assign_var_state x (Some v) (stabilize \<omega>')}"
      using r by presburger
    moreover have "stable \<omega>'"
      using \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> asm0(1) stable_assign_var_state by blast
    then show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      by (metis (no_types, lifting) UnI1 Union_image_insert \<open>\<alpha> \<in> SA\<close> \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> already_stable asm0(2) calculation image_insert insert_image stabilize_assign_var stabilize_typed_elem  singletonI)
  next
    fix \<omega> assume "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
    then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega> \<in> f \<alpha>"
      by (metis UN_E already_stable stabilize_typed_elem)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> e (snd \<alpha>) = Some v \<and> v \<in> ?ty
  \<and> f \<alpha> = {assign_var_state x (Some v) (snd \<alpha>) }"
      using r by blast
    then have "\<omega> = assign_var_state x (Some v) (snd \<alpha>)"
      using \<open>\<omega> \<in> f \<alpha>\<close> by blast
    then have "\<omega> = substitute_var_state x e (snd \<alpha>)"
      using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> e (snd \<alpha>) = Some v \<and> v \<in> the (variables \<Delta> x) \<and> f \<alpha> = {assign_var_state x (Some v) (snd \<alpha>)}\<close> substitute_var_state_def
      by metis
    moreover have "snd \<alpha> \<in> Stabilize_typed \<Delta> (snd ` SA)"
      by (metis (no_types, lifting) LocalAssign.prems(3) \<open>\<alpha> \<in> SA\<close> already_stable image_insert insertI1 mk_disjoint_insert wf_state_def  stabilize_typed_elem wf_set_def)
    ultimately show "\<omega> \<in> post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"
      using post_substitute_var_assert_def by fast
  qed (simp_all)
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.LocalAssign x e [Stabilize_typed \<Delta> (\<Union> (f ` SA))]"
    by argo
next
  case Skip
  then have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] Skip [Stabilize_typed \<Delta> (snd ` SA)]"
    using RuleSkip self_framing_Stabilize_typed  typed_Stabilize_typed by blast
  moreover have "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>}"
    using Skip.prems(1) by blast
  ultimately show ?case
    by (metis (no_types, lifting) SUP_cong UNION_singleton_eq_range)
next
  case (Havoc x)

  let ?ty = "the (variables \<Delta> x)"
  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"
  let ?B = "exists_assert \<Delta> x ?A"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (variables \<Delta> x = Some ?ty \<and> f \<alpha> = { assign_var_state x (Some v) (snd \<alpha>) |v. v \<in> ?ty})"
    using Havoc by fastforce
(*
    ?\<omega>7 \<in> SA \<Longrightarrow> red_stmt \<Delta> (abs_stmt.Havoc x) (snd ?\<omega>7) (f ?\<omega>7)
    wf_abs_stmt \<Delta> (abs_stmt.Havoc x)
    wf_set \<Delta> (snd ` SA)
*)
  have "\<Delta> \<turnstile> [?A] abs_stmt.Havoc x [?B]"
  proof (rule RuleHavoc)
    show "self_framing_and_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA))"
      using self_framing_Stabilize_typed typed_Stabilize_typed by auto
  qed
  moreover have "?B = Stabilize_typed \<Delta> (\<Union> (f ` SA))"
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> (exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)))"
      using Havoc.prems(2) calculation proofs_are_self_framing_and_typed by presburger
    show "typed_assertion \<Delta> (exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)))"
      using Havoc.prems(2) calculation proofs_are_self_framing_and_typed by presburger
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA))"
    then obtain v0 v ty where asm1: "v0 \<in> ty" "get_store \<omega> x = Some v0" "variables \<Delta> x = Some ty"
      "v \<in> ty" "assign_var_state x (Some v) \<omega> \<in> ?A" using exists_assertE[of \<omega> \<Delta> x] by meson
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize (assign_var_state x (Some v) \<omega>) = snd \<alpha>"
      using stabilize_typed_elem[of _ \<Delta>] by blast
    then have "assign_var_state x (Some v) \<omega> = snd \<alpha>"
      by (metis already_stable asm0(1) stable_assign_var_state)
    then have "\<omega> = assign_var_state x (Some v0) (snd \<alpha>)"
      by (metis asm1(2) assign_var_state_inverse)
    then have "stabilize \<omega> \<in> f \<alpha>"
      using \<open>\<alpha> \<in> SA\<close> already_stable asm0(1) asm1(1) asm1(3) r by auto
    then show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      using \<open>\<alpha> \<in> SA\<close> asm0(2) stabilize_typed_elem[of _ \<Delta>] by blast
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
    then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega> \<in> f \<alpha>"
      by (metis UN_E already_stable stabilize_typed_elem)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)" "v \<in> ?ty"
      using r by blast
    then have "wf_state \<Delta> (snd \<alpha>)"
      using Havoc.prems(3) \<open>\<alpha> \<in> SA\<close> wf_set_def by blast
    then obtain v' where "get_store (snd \<alpha>) x = Some v'" "v' \<in> ?ty"
      using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> wf_state_then_value by blast
    show "\<omega> \<in> exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA))"
      using \<open>v \<in> ?ty\<close>
    proof (rule exists_assertI)
      show "typed \<Delta> \<omega>"
        by (simp add: asm0(2))
      show "get_store \<omega> x = Some v"
        by (simp add: \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> assign_var_state_def)
      show "variables \<Delta> x = Some (the (variables \<Delta> x))"
        using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> by blast
      show "assign_var_state x (Some v') \<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>get_store (snd \<alpha>) x = Some v'\<close> \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> \<open>wf_state \<Delta> (snd \<alpha>)\<close> already_stable insertI1 insert_image assign_var_state_inverse stabilize_typed_elem wf_state_def )
    qed (simp_all add: \<open>v' \<in> ?ty\<close>)
  qed (simp_all)
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.Havoc x [Stabilize_typed \<Delta> (\<Union> (f ` SA))]"
    by argo
next
  case (Assume P)
  then have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (stable_on (snd \<omega>) P \<and> f \<omega> = {snd \<omega>} \<inter> P)"
    by fastforce

  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"

  have "\<Delta> \<turnstile> [?A] Assume P [?A \<inter> P]"
  proof (rule RuleAssume)
    show "self_framing_on (Stabilize_typed \<Delta> (snd ` SA)) P"
      unfolding self_framing_on_def
    proof
      fix \<omega> assume asm0: "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
      then show "(stabilize \<omega> \<in> P) = (\<omega> \<in> P)"
        by (metis (no_types, lifting) RangeE prod.sel(2) pure_larger_stabilize r snd_eq_Range stabilize_typed_elem stable_on_def)
    qed
  qed (simp_all)
  moreover have "?A \<inter> P = Stabilize_typed \<Delta> (\<Union> (f ` SA))" (is "?A \<inter> P = ?B")
  proof
    show "?A \<inter> P \<subseteq> ?B"
    proof
      fix \<omega> assume "\<omega> \<in> ?A \<inter> P"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        using stabilize_typed_elem[of \<omega> \<Delta>] by blast
      then have "stable_on (snd \<alpha>) P \<and> f \<alpha> = {snd \<alpha>} \<inter> P" using r by blast
      then have "f \<alpha> = {stabilize \<omega>}"
        by (metis (no_types, lifting) Assume.prems(1) IntD2 \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> P\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> pure_larger_stabilize red_stmt_Assume_elim stable_on_def)
      then show "\<omega> \<in> ?B"
        using \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> P\<close> \<open>stable_on (snd \<alpha>) P \<and> f \<alpha> = {snd \<alpha>} \<inter> P\<close> r stabilize_typed_elem[of _ \<Delta>] by auto
    qed
    show "?B \<subseteq> ?A \<inter> P"
    proof
      fix \<omega> assume "\<omega> \<in> ?B"
      then obtain \<alpha> where "stabilize \<omega> \<in> f \<alpha>" "\<alpha> \<in> SA"
        using stabilize_typed_elem[of _ \<Delta>] by auto
      then show "\<omega> \<in> ?A \<inter> P"
        using stabilize_typed_elem[of \<omega> \<Delta>] wf_assertion_stabilize[of \<Delta>]
        by (metis (no_types, lifting) Assume.prems(2) Int_iff \<open>\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))\<close> image_iff r singletonD wf_abs_stmt.simps(5))
    qed
  qed
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.Assume P [Stabilize_typed \<Delta> (\<Union> (f ` SA))]" by argo
next
  case (Custom C)
  then show ?case using SL_proof_custom[of SA \<Delta> C f]
    by (meson RuleCustom red_stmt_Custom_elim self_framing_Stabilize_typed wf_state_def  typed_Stabilize_typed wf_abs_stmt.simps(10) wf_set_def)
qed




theorem Viper_implies_SL_proof:
  assumes "verifies_set \<Delta> A C"
      and "wf_abs_stmt \<Delta> C"
      and "self_framing_and_typed \<Delta> A"
      and "typed_assertion \<Delta> A"
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

  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"
  let ?B = "Stabilize_typed \<Delta> (\<Union>\<omega>\<in>SA. f \<omega>)"

  have "\<Delta> \<turnstile> [?A] C [?B]"
  proof (rule Viper_implies_SL_proof_aux)
    show "wf_set \<Delta> (snd ` SA)"
      using SA_def calculation by blast
    show "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      by (simp add: \<open>\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)\<close>)
  qed (simp add: assms(2))

  moreover have "?A = A"
  proof (rule self_framing_typed_ext)

    show "self_framing_typed \<Delta>  A"
      by (simp add: assms(3))
    show "typed_assertion \<Delta> A"
      by (simp add: assms(4))

    fix \<omega> :: "('v, 'a) abs_state" assume asm0: "sep_algebra_class.stable \<omega>"
    show "\<omega> \<in> A \<Longrightarrow> \<omega> \<in> ?A"
    proof -
      assume asm1: "\<omega> \<in> A"
      then have "([], \<omega>) \<in> SA"
        using SA_def asm0 assms(4) typed_assertion_def by force
      then show "\<omega> \<in> ?A"
        by (metis Range.intros already_stable asm0 asm1 assms(4) typed_assertion_def  snd_eq_Range stabilize_typed_elem)
    qed
    assume asm1: "\<omega> \<in> ?A"
    then have "\<omega> \<in> snd ` SA"
      by (simp add: already_stable asm0 stabilize_typed_elem)
    then show "\<omega> \<in> A"
      using SA_def by force
  qed (simp_all)
  ultimately show ?thesis
    by force
qed


lemma entails_refl:
  "entails A A"
  by (simp add: entailsI)


lemma free_vars_subset:
  assumes "\<And>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed_store \<Delta> \<sigma>1 \<and> typed_store \<Delta> \<sigma>2 \<and> equal_on_set V \<sigma>1 \<sigma>2 \<Longrightarrow> (Ag \<sigma>1, \<gamma>) \<in> A \<Longrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A"
  shows "free_vars \<Delta> A \<subseteq> V"
proof -
  have "overapprox_fv \<Delta> A V"
    by (smt (verit, del_insts) assms equal_on_set_def overapprox_fv_def)
  then show ?thesis
    by (simp add: Inf_lower free_vars_def)
qed

lemma entails_trans:
  assumes "entails A B"
      and "entails B C"
    shows "entails A C"
  by (meson assms(1) assms(2) dual_order.trans entails_def)



lemma free_varsE:
  assumes "equal_on_set (free_vars \<Delta> A) \<sigma>1 \<sigma>2"
      and "typed_store \<Delta> \<sigma>1"
      and "typed_store \<Delta> \<sigma>2"
      and "(Ag \<sigma>1, \<gamma>) \<in> A"
 (*     and "finite (dom (variables \<Delta>))" *)
    shows "(Ag \<sigma>2, \<gamma>) \<in> A"
  sorry (* TODO: Free variables *)

lemma get_store_Ag_simplifies[simp]:
  "get_store (Ag \<sigma>, \<gamma>) = \<sigma>"
  by (simp add: get_store_def)

lemma set_store_Ag_simplies[simp]:
  "set_store (\<alpha>, \<gamma>) \<sigma> = (Ag \<sigma>, \<gamma>)"  
  by (simp add: get_abs_state_def set_store_def)




lemma exists_assert_no_in_fv:
  "free_vars \<Delta> (exists_assert \<Delta> x A) \<subseteq> free_vars \<Delta> A - {x}"
proof (rule free_vars_subset)
  fix \<sigma>1 \<sigma>2 \<gamma>
  assume asm0: "typed_store \<Delta> \<sigma>1 \<and> typed_store \<Delta> \<sigma>2 \<and> equal_on_set (free_vars \<Delta> A - {x}) \<sigma>1 \<sigma>2"
         "(Ag \<sigma>1, \<gamma>) \<in> exists_assert \<Delta> x A"
  then obtain v0 v ty where r: "v0 \<in> ty" "get_store (Ag \<sigma>1, \<gamma>) x = Some v0" "variables \<Delta> x = Some ty" "v \<in> ty"
    "(set_store (Ag \<sigma>1, \<gamma>) ((get_store (Ag \<sigma>1, \<gamma>))(x \<mapsto> v))) \<in> A" "typed \<Delta> (Ag \<sigma>1, \<gamma>)"
    by (metis assign_var_state_def exists_assertE)
  then have "(Ag (\<sigma>1(x \<mapsto> v)), \<gamma>) \<in> A"
    by (smt (verit) assign_var_state_def assign_var_state_inverse get_abs_state_set_store get_store_set_store prod.inject set_store_def)
  moreover have "equal_on_set (free_vars \<Delta> A) (\<sigma>1(x \<mapsto> v)) (\<sigma>2(x \<mapsto> v))"
    using asm0(1) equal_on_set_def[of "free_vars \<Delta> A" "\<sigma>1(x \<mapsto> v)" "\<sigma>2(x \<mapsto> v)"]
    by (simp add: equal_on_set_def)

  then have "(Ag (\<sigma>2(x \<mapsto> v)), \<gamma>) \<in> A"
    by (rule free_varsE) (simp_all add: asm0 r typed_store_update calculation)
  then have "set_store (Ag \<sigma>2, \<gamma>) ((get_store (Ag \<sigma>2, \<gamma>))(x \<mapsto> v)) \<in> A"
    by (simp add: get_abs_state_def set_store_def)
  moreover obtain v0' where "get_store (Ag \<sigma>2, \<gamma>) x = Some v0'"
    by (metis agreement.exhaust_sel agreement.inject asm0(1) domD domI get_store_def prod.sel(1) r(3) typed_store_def)
  then have "v0' \<in> ty"
    by (metis agreement.exhaust_sel agreement.inject asm0(1) get_store_def prod.sel(1) r(3) typed_store_def)
  ultimately show "(Ag \<sigma>2, \<gamma>) \<in> exists_assert \<Delta> x A"
    unfolding exists_assert_def
    by (smt (verit) \<open>get_store (Ag \<sigma>2, \<gamma>) x = Some v0'\<close> asm0(1) asm0(2) assign_var_state_def get_store_Ag_simplifies mem_Collect_eq r(3) r(4) exists_assertE  set_store_Ag_simplies set_store_def snd_conv typed_def)
qed


lemma exists_assert_entails:
  assumes "typed_assertion \<Delta> A"
      and "variables \<Delta> x \<noteq> None"
  shows "entails A (exists_assert \<Delta> x A)"
proof (rule entailsI)
  fix \<omega> assume asm0: "\<omega> \<in> A"
  then have "typed \<Delta> \<omega>"
    using assms(1) typed_assertion_def by blast
  then obtain v0 ty v where "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty" "(set_store \<omega> ((get_store \<omega>)(x \<mapsto> v))) \<in> A"
    by (smt (verit, best) asm0 assms(2) domD domIff full_state_ext fun_upd_triv get_abs_state_set_store get_store_set_store typed_def typed_store_def)
  then show "\<omega> \<in> exists_assert \<Delta> x A"
    by (metis \<open>typed \<Delta> \<omega>\<close> assign_var_state_def exists_assertI)
qed

lemma SL_proof_Havoc_elim_entails:
  assumes "\<Delta> \<turnstile> [A] Havoc x [B]"
      and "typed_assertion \<Delta> A"
      and "variables \<Delta> x \<noteq> None"
  shows "entails A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - {x}"
  using assms exists_assert_entails exists_assert_no_in_fv by force



lemma SL_proof_Havoc_list_elim:
  assumes "\<Delta> \<turnstile> [A] havoc_list l [B]"
      and "wf_abs_stmt \<Delta> (havoc_list l)"
  shows "self_framing_and_typed \<Delta> A \<and> self_framing_and_typed \<Delta> B \<and> entails A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - (set l)"
  using assms
proof (induct l arbitrary: A B)
  case Nil
  then show ?case using SL_proof_Skip_elim
    using entails_refl by force
next
  case (Cons x l)
  then obtain R where r: "\<Delta> \<turnstile> [A] Havoc x [R]" "\<Delta> \<turnstile> [R] havoc_list l [B]"
    by (metis SL_proof_Seq_elim havoc_list.simps(2))
  moreover have "self_framing_and_typed \<Delta> B \<and> entails R B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> R - set l"
    using Cons calculation(2) by simp
  moreover have "typed_assertion \<Delta> A"
    using r(1) by force
  moreover have "variables \<Delta> x \<noteq> None"
    using Cons.prems(2) by force

  then have "entails A R \<and> free_vars \<Delta> R \<subseteq> free_vars \<Delta> A - {x}"
    using calculation SL_proof_Havoc_elim_entails by presburger

  ultimately show "self_framing_and_typed \<Delta> A \<and> self_framing_and_typed \<Delta> B \<and> entails A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - set (x # l)"
    by (metis Cons.prems(1) Cons.prems(2) Diff_empty Diff_insert0 Diff_mono dual_order.eq_iff dual_order.trans list.simps(15) entails_trans proofs_are_self_framing_and_typed subset_Diff_insert)
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

lemma state_in_pure_typed_add:
  assumes "\<omega> \<in> A"
      and "Some True = b \<omega>"
      and "wf_exp b"
      and "typed \<Delta> \<omega>"
    shows "\<omega> \<in> A \<otimes> pure_typed \<Delta> b"
proof -
  have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
    by (simp add: core_is_smaller)
  moreover have "|\<omega>| \<in> pure_typed \<Delta> b"
    by (smt (verit, ccfv_threshold) CollectI assms(2) assms(3) assms(4) max_projection_prop_def max_projection_prop_pure_core pure_typed_def  typed_core wf_exp_def)
  ultimately show ?thesis
    using assms(1) x_elem_set_product by blast
qed




section \<open>Reciprocal\<close>

theorem SL_proof_implies_Viper:
  assumes "\<Delta> \<turnstile> [A] C [B]"
      and "\<omega> \<in> A"
      and "wf_abs_stmt \<Delta> C"
      and "stable \<omega>"
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
      by (meson RuleSeq.hyps(4) RuleSeq.prems(2) RuleSeq.prems(3) S1_def(1) S1_def(2) in_mono red_stable wf_abs_stmt.simps(7) )
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
  case (RuleInhale \<Delta> A P)
  moreover have "red_stmt \<Delta> (abs_stmt.Inhale P) \<omega> (Set.filter sep_algebra_class.stable ({\<omega>} \<otimes> P))"
  proof (rule RedInhale[of \<omega> P \<Delta>])
    show "rel_stable_assertion \<omega> P"
      using calculation(2) calculation(3) calculation(5) framed_by_def by blast
  qed
  moreover have "Set.filter sep_algebra_class.stable ({\<omega>} \<otimes> P) \<subseteq> A \<otimes> P"
    by (metis calculation(3) member_filter star_to_singletonI subsetI)
  ultimately show "\<exists>S. red_stmt \<Delta> (abs_stmt.Inhale P) \<omega> S \<and> S \<subseteq> A \<otimes> P" by meson
next
  case (RuleExhale \<Delta> B A P)
  then obtain a p where "a \<in> A" "p \<in> P" "Some \<omega> = a \<oplus> p"
    by (meson entails_def subsetD x_elem_set_product)
  then obtain p' where "Some p' = p \<oplus> |\<omega>|" "Some \<omega> = stabilize a \<oplus> p'"
    using stabilize_rel by blast
  then have "red_stmt \<Delta> (abs_stmt.Exhale P) \<omega> {stabilize a}"
    using RedExhale[of p' P \<omega> "stabilize a" \<Delta>]
    by (meson RuleExhale.prems(3) \<open>Some \<omega> = a \<oplus> p\<close> \<open>p \<in> P\<close> RedExhale stabilize_is_stable stabilize_sum_result_stable)
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.Exhale P) \<omega> S \<and> S \<subseteq> A"
    by (meson RuleExhale.hyps(3) \<open>a \<in> A\<close> empty_subsetI insert_subset self_framing_typed_def typed_assertion_def)
next
  case (RuleAssert \<Delta> A P)
  then have "red_stmt \<Delta> (abs_stmt.Assert P) \<omega> {\<omega>}"
    using RedAssertTrue[of \<omega> P \<Delta>] by (meson entails_def subset_iff)
  then show "\<exists>S. red_stmt \<Delta> (abs_stmt.Assert P) \<omega> S \<and> S \<subseteq> A"
    by (meson RuleAssert.prems(1) empty_subsetI insert_subsetI)
next
  case (RuleAssume \<Delta> A P)
  moreover have asm0: "stable_on \<omega> P"
    unfolding stable_on_def sorry
(*
  proof
    sorry

    by (metis (no_types, lifting) already_stable pure_larger_stabilize_same self_framing_on_def self_framing_typed_altE typed_assertion_def wf_abs_stmt.simps(5) stable_on_def wf_assertion_def) 
(* long *)
*)
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
  case (RuleHavoc \<Delta> A x)
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
      by (meson RuleHavoc.hyps RuleHavoc.prems(1) RuleHavoc.prems(3) wf_state_then_value  ty_def typed_assertion_def wf_state_def)
    ultimately show "\<omega>' \<in> exists_assert \<Delta> x A"
      using exists_assertI[of v ty \<omega>' x \<Delta> v0 A]
      by (metis RuleHavoc.hyps RuleHavoc.prems(1) assign_var_state_def assign_var_state_inverse fun_upd_same get_store_set_store ty_def typed_assertion_def typed_assign_var)
  qed
  ultimately show "\<exists>S. red_stmt \<Delta> (abs_stmt.Havoc x) \<omega> S \<and> S \<subseteq> exists_assert \<Delta> x A"
    by meson
next
  case (RuleLocalAssign \<Delta> A e x)
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
  case (RuleIf \<Delta> A b C1 B1 C2 B2)
  then have ty: "typed \<Delta> \<omega>"
    by (meson typed_assertion_def)
  show "\<exists>S. red_stmt \<Delta> (abs_stmt.If b C1 C2) \<omega> S \<and> S \<subseteq> B1 \<union> B2"
  proof (cases "b \<omega> = Some True")
    case True
    moreover have "\<exists>S. red_stmt \<Delta> C1 \<omega> S \<and> S \<subseteq> B1"
    proof (rule RuleIf(4))
      show "\<omega> \<in> A \<otimes> pure_typed \<Delta> b"
        using RuleIf.prems(1) RuleIf.prems(2) ty calculation state_in_pure_typed_add[of \<omega> A b \<Delta>]
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
      show "\<omega> \<in> A \<otimes> pure_typed \<Delta> (negate b)"
        by (smt (verit, del_insts) RuleIf.hyps(2) RuleIf.prems(1) RuleIf.prems(2) ty calculation framed_by_exp_def negate_def option.sel state_in_pure_typed_add wf_abs_stmt.simps(6)  wf_exp_negate)
      show "wf_abs_stmt \<Delta> C2"
        using RuleIf.prems(2) by auto
    qed (simp_all add: RuleIf)
    ultimately show ?thesis
      using RedIfFalse[of b \<omega> \<Delta> C2 _ C1] by blast
  qed
next
  case (RuleCustom \<Delta> A B C)
  then have "typed_store \<Delta> (get_store \<omega>)"
    by (simp add: typed_assertion_def typed_def typed_store_def)
  then show ?case using red_wf_complete[OF \<open>SL_Custom \<Delta> A C B\<close>]
    by (meson RedCustom RuleCustom.hyps(1) RuleCustom.prems(1) RuleCustom.prems(2) RuleCustom.prems(3) typed_assertion_def typed_def wf_abs_stmt.simps(10))
qed





end

end
