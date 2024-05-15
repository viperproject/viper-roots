theory AbstractSemanticsProperties
  imports AbstractSemantics
begin

context semantics
begin

\<comment>\<open>Results needed:
1. If state starts stable, then it stays stable
\<close>

section \<open>Properties of the semantics: States are always wf_state\<close>

(*
lemma equiv_compo_singleton:
  "red_stmt \<Delta> s \<omega> (b) \<longleftrightarrow> sequential_composition \<Delta> {\<omega>} s b" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?B \<Longrightarrow> ?A"
    by (smt ccpo_Sup_singleton image_empty image_insert sequential_composition.cases singletonI)
  moreover have "?A \<Longrightarrow> ?B"
  proof -
    assume ?A
    then obtain f where "f \<omega> = b"
      by simp
    show ?B
    proof (rule SeqComp)
      show "\<And>\<omega>'. \<omega>' \<in> {\<omega>} \<Longrightarrow> red_stmt \<Delta> s \<omega>' (f \<omega>')"
        using \<open>f \<omega> = b\<close> \<open>red_stmt \<Delta> s \<omega> (b)\<close> by blast
      show "b = \<Union> (f ` {\<omega>})"
        using \<open>f \<omega> = b\<close> by blast
    qed
  qed
  ultimately show ?thesis by blast
qed
*)

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

(*
      and "\<And>\<Delta> r \<omega> hl e v ty. r \<omega> = Some hl \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> has_write_perm (get_state \<omega>) hl
  \<Longrightarrow> heap_locs \<Delta> hl = Some ty \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_state \<omega> (set_value (get_state \<omega>) hl v))"
*)
      and "\<And>\<Delta> C \<omega> S \<omega>'. red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> x ty \<omega> v. variables \<Delta> x = Some ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> e \<omega> v x ty. variables \<Delta> x = Some ty \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> l \<omega>. P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_state \<omega>))))"
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
(*
    case (RedFieldAssign r \<omega> hl e v \<Delta> ty)
    then show ?case
      using assms(6) by auto
  next
*)
    case (RedLocalAssign \<Delta> x ty e \<omega> v)
    then show ?case
      using assms(8) by (simp)
  next
    case (RedHavoc \<Delta> x ty \<omega>)
    then show ?case
      by (auto simp add: assms(7))
  next
(*
    case (RedLabel \<Delta> l \<omega>)
    then show ?case
      using assms(9) by blast
*)
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
(*
  case (FieldAssign \<Delta> r \<omega> hl e v)
  then show ?case
    by (metis get_state_def get_state_set_state set_value_stable stable_snd)
next
*)
  case (Custom \<Delta> C \<omega> S \<omega>')
  then show ?case sorry (* TODO *)
next
  case (Havoc \<Delta> x ty \<omega> v)
  then show "sep_algebra_class.stable (assign_var_state x (Some v) \<omega>)"
    by (metis (no_types, lifting) assign_var_state_def max_projection_prop_stable_stabilize mppI mpp_smaller set_store_stabilize stabilize_is_stable succ_refl)
next
  case (LocalAssign \<Delta> e \<omega> v x)
  then show ?case
    by (metis already_stable assign_var_state_def set_store_stabilize stabilize_is_stable)
(*
next
  case (Label \<Delta> l \<omega>)
  then show ?case
    by (metis get_state_def get_state_set_trace stable_snd)
*)
qed (blast)

lemma typed_storeI:
  assumes "dom (variables \<Delta>) = dom \<sigma>"
      and "\<And>x v ty. \<sigma> x = Some v \<Longrightarrow> variables \<Delta> x = Some ty \<Longrightarrow> v \<in> ty"
    shows "typed_store \<Delta> \<sigma>"
  using assms(1) assms(2) typed_store_def by auto

lemma red_well_typed:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "typed_store \<Delta> (get_store \<omega>)"
      and "\<omega>' \<in> S"
    shows "typed_store \<Delta> (get_store \<omega>')"
  using assms
proof (induct rule: red_stmt_induct_simple)
  case (Custom \<Delta> C \<omega> S \<omega>')
  then show ?case sorry (* TODO *)
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
      using Havoc.hyps(1) Havoc.hyps(2) typed_store_def assign_var_state_def by auto
    fix x' v' ty' assume asm0: "get_store (assign_var_state x (Some v) \<omega>) x' = Some v'" "variables \<Delta> x' = Some ty'"
    then show "v' \<in> ty'"
      by (metis Havoc.hyps(1) Havoc.hyps(2) Havoc.hyps(3) assign_var_state_def fun_upd_other fun_upd_same get_store_set_store option.inject typed_store_def)
  qed
next
  case (LocalAssign \<Delta> e \<omega> v x ty)
  then show "typed_store \<Delta> (get_store (assign_var_state x (Some v) \<omega>))"
    using typed_store_def assign_var_state_def by auto
qed (auto)

lemma red_stmt_induct_simple_wf [consumes 4, case_names Inhale Exhale Custom Havoc LocalAssign Label]:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "P \<Delta> \<omega>"
      and "wf_abs_stmt \<Delta> C"
      and "\<omega>' \<in> S"
      and "\<And>(A :: ('v, 'a) abs_state assertion) \<omega>' \<omega> \<Delta> a.
        rel_stable_assertion \<omega> A \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> wf_assertion \<Delta> A \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>a (A :: ('v, 'a) abs_state assertion) \<omega> \<omega>' \<Delta>. a \<in> A \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> wf_assertion \<Delta> A \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> S \<omega> \<omega>' C. wf_custom_stmt \<Delta> C \<Longrightarrow> red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> P \<Delta> \<omega>'"
(*
      and "\<And>\<Delta> r \<omega> hl e v ty. r \<omega> = Some hl \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> has_write_perm (get_state \<omega>) hl
  \<Longrightarrow> heap_locs \<Delta> hl = Some ty \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_state \<omega> (set_value (get_state \<omega>) hl v))"
*)
      and "\<And>\<Delta> x ty \<omega> v. variables \<Delta> x = Some ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> e \<omega> v x ty. variables \<Delta> x = Some ty \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (assign_var_state x (Some v) \<omega>)"
      and "\<And>\<Delta> l \<omega>. P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_state \<omega>))))"
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
(*
    case (RedFieldAssign r \<omega> hl e v \<Delta> ty)
    then show ?case
      using assms(7) by auto
  next
*)
    case (RedLocalAssign \<Delta> x ty e \<omega> v)
    then show ?case
      using assms(8) by (simp)
  next
    case (RedHavoc \<Delta> x ty \<omega>)
    then show ?case
      by (auto simp add: assms(8))
  next
(*
    case (RedLabel \<Delta> l \<omega>)
    then show ?case
      using assms(10) by blast
  next
*)
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
      using assms(7) wf_abs_stmt.simps(11) by blast
  qed (blast+)
  then show ?thesis
    using assms(2) assms(3) assms(4) by blast
qed


lemma red_typed_heap:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "wf_custom_state (custom_context \<Delta>) (get_state \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "\<omega>' \<in> S"
    shows "wf_custom_state (custom_context \<Delta>) (get_state \<omega>')"
  using assms
proof (induct rule: red_stmt_induct_simple_wf)
  case (Inhale A \<omega>' \<omega> \<Delta> a)
  then show ?case
    by (simp add: full_add_charact(2) typed_assertion_def typed_def wf_custom_state_sum wf_assertion_def)
next
  case (Exhale a A \<omega> \<omega>' \<Delta>)
  then show ?case using wf_custom_state_smaller
    using full_add_charact(2) greater_def by blast
(*
next
  case (FieldAssign \<Delta> r \<omega> hl e v)
  then show ?case
    by (simp add: typed_def well_typed_heap_update)
*)
next
  case (Custom \<Delta> S \<omega> \<omega>' C)
  then show ?case sorry (* TODO *)
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
  using assms wf_set_def wf_state_def
  by metis


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
  by (metis agreement.exhaust assign_var_state_def get_state_def get_state_set_store stabilize_ag stabilize_is_stable stable_prod_def)

lemma stable_substitute_var:
  "stable \<omega> \<longleftrightarrow> stable (substitute_var_state x e \<omega>)"
  by (simp add: stable_assign_var_state substitute_var_state_def)

lemma wf_assertion_stabilize:
  assumes "wf_assertion \<Delta> A"
      and "stabilize \<omega> \<in> A"
    shows "\<omega> \<in> A"
  using assms wf_assertion_def pure_larger_stabilize by blast

lemma stabilize_assign_var:
  "stabilize (assign_var_state x v \<omega>) = assign_var_state x v (stabilize \<omega>)"
  using assign_var_state_def by auto

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

lemma self_framing_typedE:
  assumes "self_framing_typed \<Delta> A"
      and "typed \<Delta> a"
      and "a \<in> A"
    shows "stabilize a \<in> A"
  using assms(1) assms(2) assms(3) self_framing_typed_def by blast

lemma self_framing_typed_altE:
  assumes "self_framing_typed \<Delta> A"
      and "typed \<Delta> a"
      and "stabilize a \<in> A"
    shows "a \<in> A"
  using assms(1) assms(2) assms(3) self_framing_typed_def by blast

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
      by (metis \<open>a \<in> A\<close> asm0 assms(1) assms(4) get_state_set_store get_store_stabilize self_framing_typed_def typed_assertion_def typed_def)
    moreover have "\<omega> = set_store ?a ((get_store ?a)(x \<mapsto> v))"
      by (metis \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> \<open>stabilize \<omega> = set_store a ((get_store a)(x \<mapsto> v))\<close> full_state_ext get_state_set_store get_store_set_store get_store_stabilize)
    ultimately show ?P
      by (smt (verit, best) \<open>e a = Some v\<close> assign_var_state_def \<open>stabilize (set_store \<omega> ((get_store \<omega>)(x := get_store a x))) = a\<close> assms(2) image_eqI post_substitute_var_assert_def substitute_var_state_def wf_exp_stabilize)
  qed
qed



(*
lemma self_framing_conj_framed_by_exp:
  assumes "framed_by_exp A b"
      and "self_framing A"
      and "framed_by_exp A b"
      and "wf_exp b"
    shows "self_framing (A \<inter> pure_typed \<Delta> b)"
  by (smt (verit, del_insts) Int_Collect assms(1) assms(2) assms(4) pure_typed \<Delta>_def self_framing_def wf_exp_framed_by_stabilize)
*)



(*

    wf_abs_stmt \<Delta> (abs_stmt.If b C1 C2)
    (?c \<in> ?A \<inter> ?B) = (?c \<in> ?A \<and> ?c \<in> ?B)
    self_framing (Stabilize_typed \<Delta> ?S)
    framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b
    (?a \<in> Collect ?P) = ?P ?a
    pure_typed \<Delta> ?b = {\<omega> |\<omega>. ?b \<omega> = Some True}
    self_framing ?A = (\<forall>\<omega>. (\<omega> \<in> ?A) = (stabilize \<omega> \<in> ?A))
    wf_abs_stmt ?\<Delta> (abs_stmt.If ?b ?C1.0 ?C2.0) = (wf_exp ?b \<and> wf_abs_stmt ?\<Delta> ?C1.0 \<and> wf_abs_stmt ?\<Delta> ?C2.0)
    wf_exp ?e \<Longrightarrow> framed_by_exp ?A ?e \<Longrightarrow> ?\<omega> \<in> ?A \<Longrightarrow> self_framing ?A \<Longrightarrow> (?e ?\<omega> = Some ?b) = (?e (stabilize ?\<omega>) = Some ?b)

goal (1 subgoal):
 1. self_framing (Stabilize_typed \<Delta> (snd ` SA) \<inter> pure_typed \<Delta> b)
*)


lemma typed_assertion_post_substitute_var_assert:
  assumes "typed_assertion \<Delta> A"
      and "framed_by_exp A e"
      and "variables \<Delta> x = Some ty"
      and "typed_exp ty e"
    shows "typed_assertion \<Delta> (post_substitute_var_assert x e A)"
    by (smt (verit, ccfv_threshold) assms framed_by_expE image_iff post_substitute_var_assert_def substitute_var_state_def typed_assertion_def typed_assign_var typed_exp_def)


lemma exists_assertI:
  assumes "v0 \<in> ty"
      and "get_store \<omega> x = Some v0"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
      and "assign_var_state x (Some v) \<omega> \<in> A"
      and "typed \<Delta> \<omega>"
    shows "\<omega> \<in> exists_assert \<Delta> x A"
  using assms exists_assert_def assign_var_state_def by auto

lemma exists_assertE:
  assumes "\<omega> \<in> exists_assert \<Delta> x A"
  shows "\<exists>v0 v ty. typed \<Delta> \<omega> \<and> v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (assign_var_state x (Some v) \<omega>) \<in> A"
  using assms exists_assert_def assign_var_state_def by auto

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
      using exists_assert_def assign_var_state_def by auto
    then have "get_store (stabilize \<omega>) x = Some v0 \<and> set_store (stabilize \<omega>) ((get_store (stabilize \<omega>))(x \<mapsto> v)) = stabilize (assign_var_state x (Some v) \<omega>)"
      by (simp add: assign_var_state_def)
    then show ?B
      by (metis (mono_tags, lifting) asm0 assms(1) exists_assertI r self_framing_typed_def stabilize_assign_var typed_assign_var typed_then_stabilize_typed)
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
        using asm0 assms(1) r(4) r(5) r(6) self_framing_typed_altE stabilize_assign_var typed_assign_var by auto
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


(*
lemma self_framing_if:
  assumes "framed_by_exp A b"
      and "self_framing (A \<otimes> pure_typed \<Delta> b)"
      and "self_framing (A \<otimes> pure_typed \<Delta> (negate b))"
      and "wf_exp b"
    shows "self_framing A"
proof (rule self_framingI)
  fix \<omega>
  show "\<omega> \<in> A \<longleftrightarrow> stabilize \<omega> \<in> A" (is "?A \<longleftrightarrow> ?B")
  proof
    assume ?A
    then show ?B
    proof (cases "b \<omega> = Some True")
      case True
      then have "\<omega> \<in> A \<otimes> pure_typed \<Delta> b"
        by (simp add: \<open>\<omega> \<in> A\<close> assms(4) in_star_pure_stab)
      then show ?thesis
        by (smt (verit, del_insts) CollectD assms(2) prove_in_up_close_core pure_typed \<Delta>_def self_framing_def stabilize_is_stable stable_in_up_close_core x_elem_set_product)
    next
      case False
      then have "negate b \<omega> = Some True"
        by (smt (verit, del_insts) \<open>\<omega> \<in> A\<close> assms(1) option.exhaust option.sel framed_by_exp_def negate_def)
      then show ?thesis
        by (meson \<open>\<omega> \<in> A\<close> assms(3) assms(4) in_star_pure_stab negate_sat_equiv prove_in_up_close_core self_framing_def stabilize_is_stable stable_in_up_close_core wf_exp_negate x_elem_set_product)
    qed
  next
    assume ?B
    then show ?A
    proof (cases "b (stabilize \<omega>) = Some True")
      case True
      then have "stabilize \<omega> \<in> A \<otimes> pure_typed \<Delta> b"
        by (simp add: \<open>stabilize \<omega> \<in> A\<close> assms(4) in_star_pure_stab)
      then have "\<omega> \<in> A \<otimes> pure_typed \<Delta> b"
        using assms(2) self_framing_def by blast



      then show ?thesis sorry (* IN COMMENT *)
      
      by (smt (verit, best) Int_Collect Int_iff assms(1) assms(2) assms(3) framed_by_expE negate_sat_equiv pure_typed \<Delta>_def self_framing_def)
  qed
qed
*)


(*
lemma extract_from_points_to:
  assumes "\<omega> \<in> A \<otimes> points_to r"
  shows "\<exists>a p hl. Some \<omega> = a \<oplus> p \<and> a \<in> A \<and> r p = Some hl \<and> has_write_perm_only (get_state p) hl"
proof -
  obtain a p where "Some \<omega> = a \<oplus> p \<and> a \<in> A \<and> p \<in> points_to r"
    by (meson assms x_elem_set_product)
  then show ?thesis
    by (smt (verit, best) mem_Collect_eq points_to_def)
qed

lemma self_framing_points_to:
  assumes "self_framing A"
      and "framed_by_exp A r"
      and "wf_exp r"
    shows "self_framing (A \<otimes> points_to r)"
proof (rule self_framingI)
  fix \<omega> show "\<omega> \<in> A \<otimes> points_to r \<longleftrightarrow> stabilize \<omega> \<in> A \<otimes> points_to r" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain a p hl where "Some \<omega> = a \<oplus> p" "a \<in> A" "r p = Some hl" "has_write_perm_only (get_state p) hl"
      using extract_from_points_to by blast
    then obtain p' where "Some p' = |stabilize a| \<oplus> stabilize p"
      by (metis (no_types, opaque_lifting) asso3 commutative core_is_smaller option.exhaust_sel stabilize_sum)
    then have "Some (stabilize \<omega>) = stabilize a \<oplus> p'"
      by (smt (verit) \<open>Some \<omega> = a \<oplus> p\<close> asso1 core_is_smaller stabilize_sum)
    moreover have "stabilize a \<in> A"
      using \<open>a \<in> A\<close> assms(1) self_framing_def by blast
    ultimately have "r p' = Some hl" 
    proof -
      obtain v where "r (stabilize a) = Some v"
        using framed_by_expE[OF assms(2) \<open>stabilize a \<in> A\<close>] by blast
      then have "v = hl"
        by (metis (no_types, lifting) \<open>Some \<omega> = a \<oplus> p\<close> \<open>r p = Some hl\<close> assms(3) commutative greater_equiv option.inject wf_expE wf_exp_stabilize)
      then show ?thesis
        by (metis (no_types, lifting) \<open>Some p' = |stabilize a| \<oplus> stabilize p\<close> \<open>r (stabilize a) = Some v\<close> assms(3) commutative greater_equiv wf_exp_def)
    qed
    moreover have "has_write_perm_only (get_state p') hl"
      using has_perm_only_stabilize
      by (metis (no_types, opaque_lifting) \<open>Some p' = |stabilize a| \<oplus> stabilize p\<close> \<open>has_write_perm_only (get_state p) hl\<close> commutative core_charact(2) decompose_stabilize_pure full_add_charact(2) plus_pure_stabilize_eq)
    ultimately show ?Q
      by (metis (mono_tags, lifting) \<open>Some (stabilize \<omega>) = stabilize a \<oplus> p'\<close> \<open>stabilize a \<in> A\<close> mem_Collect_eq points_to_def x_elem_set_product)
  next
    assume ?Q
    then obtain a p hl where "Some (stabilize \<omega>) = a \<oplus> p" "a \<in> A" "r p = Some hl" "has_write_perm_only (get_state p) hl"
      using extract_from_points_to by blast
    then obtain p' where "Some p' = p \<oplus> |\<omega>|"
      by (metis (no_types, opaque_lifting) asso2 core_option.elims decompose_stabilize_pure)
    then have "r p' = Some hl"
      by (meson \<open>r p = Some hl\<close> assms(3) greater_def wf_expE)
    moreover have "has_write_perm_only (get_state p') hl"
      by (metis \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>has_write_perm_only (get_state p) hl\<close> core_charact(2) full_add_charact(2) has_perm_only_stabilize plus_pure_stabilize_eq)
    moreover have "Some \<omega> = a \<oplus> p'"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> \<open>Some p' = p \<oplus> |\<omega>|\<close> asso1 decompose_stabilize_pure)
    ultimately show ?P
      by (metis (mono_tags, lifting) \<open>a \<in> A\<close> mem_Collect_eq points_to_def x_elem_set_product)
  qed
qed

lemma self_framing_post_field_assign:
  assumes "self_framing A"
      and "framed_by_exp A r"
      and "framed_by_exp (A \<otimes> points_to r) b"
      and "framed_by_exp (A \<otimes> points_to r \<otimes> pure_typed \<Delta> b) e"
    shows "self_framing (A \<otimes> pure_post_field_assign r e b)"
  sorry (* IN COMMENT *)
*)


(*

definition framed_by where
  "framed_by A B \<longleftrightarrow> (\<forall>\<omega> \<in> A. stable \<omega> \<longrightarrow> rel_stable_assertion \<omega> B)"

definition framed_by_exp where
  "framed_by_exp A e \<longleftrightarrow> (\<forall>\<omega> \<in> A. e \<omega> \<noteq> None)"
*)

lemma typed_union:
  assumes "typed_assertion \<Delta> A"
      and "typed_assertion \<Delta> B"
    shows "typed_assertion \<Delta> (A \<union> B)"
  using assms(1) assms(2) typed_assertion_def by auto

lemma typed_intersection:
  assumes "typed_assertion \<Delta> A"
  shows "typed_assertion \<Delta> (A \<inter> B)"
  by (meson assms inf.cobounded1 typed_subset)

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
      by (metis (no_types, lifting) \<open>Some aa = a \<oplus> |\<omega>|\<close> asm0 assms(1) calculation(1) calculation(4) greater_def plus_pure_stabilize_eq semantics.self_framing_typedE semantics.self_framing_typed_altE semantics_axioms typed_smaller)
    ultimately show ?A
      using x_elem_set_product by blast
  qed
qed


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
    by (meson self_framing_post_substitute_var_assert semantics.typed_assertion_post_substitute_var_assert semantics.wf_abs_stmt.simps(8) semantics_axioms)
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

lemma self_framing_typed_ext:
  assumes "self_framing_typed \<Delta> A"
      and "self_framing_typed \<Delta> B"
      and "typed_assertion \<Delta> A"
      and "typed_assertion \<Delta> B"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> \<omega> \<in> B"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> typed \<Delta> \<omega>  \<Longrightarrow> \<omega> \<in> B \<Longrightarrow> \<omega> \<in> A"
    shows "A = B"
proof -
  have "\<And>\<omega>. \<omega> \<in> A \<longleftrightarrow> \<omega> \<in> B"
    by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) self_framing_typedE self_framing_typed_altE semantics.typed_assertion_def semantics_axioms stabilize_is_stable)
  then show ?thesis by blast
qed

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
      by (metis \<open>Some \<omega> = a \<oplus> r\<close> \<open>a \<in> A\<close> asm0 assms(3) commutative greater_equiv semantics.self_framing_typedE semantics_axioms typed_smaller)
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
      by (smt (verit, ccfv_threshold) CollectI \<open>Some (stabilize \<omega>) = a \<oplus> p\<close> \<open>Some \<omega> = a \<oplus> p'\<close> \<open>Some p' = p \<oplus> |\<omega>|\<close> \<open>b p = Some True\<close> \<open>pure p\<close> asm0 asso1 commutative core_stabilize_mono(1) greater_equiv max_projection_prop_def max_projection_prop_pure_core minusI semantics.pure_typed_def semantics_axioms stabilize_is_stable stable_and_sum_pure_same typed_core)
    then show ?P
      by (meson \<open>Some \<omega> = a \<oplus> p'\<close> \<open>a \<in> A\<close> x_elem_set_product)
  qed
qed

lemma stabilize_typed_elem:
  "\<omega> \<in> Stabilize_typed \<Delta> A \<longleftrightarrow> typed \<Delta> \<omega> \<and> stabilize \<omega> \<in> A"
  using Stabilize_typed_def by auto




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
        using Seq.prems(3) \<open>\<omega> \<in> SA\<close> wf_set_def by force
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
      by (metis (no_types, lifting) If.prems(3) Un_upper1 \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono wf_set_subset)
  qed

  have "framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b"
  proof (rule framed_by_expI)
    fix \<omega> assume "\<omega> \<in> (Stabilize_typed \<Delta> (snd ` SA))"
    then have "stabilize \<omega> \<in> snd ` SA"
      using stabilize_typed_elem by blast
    then show "b \<omega> \<noteq> None"
      by (smt (verit, ccfv_SIG) If.prems(1) If.prems(2) imageE max_projection_prop_def max_projection_prop_stable_stabilize option.distinct(1) red_stmt_If_elim wf_abs_stmt.simps(6) wf_expE)
  qed

(*
  have rtrue: "Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b = Set.filter (\<lambda>\<omega>. b \<omega> = Some True) (Stabilize_typed \<Delta> (snd ` SA))"
    sledgehammer

    using If.prems(2) Stabilize_self_framing pure_typed_eq wf_abs_stmt.simps(6) by blast
  moreover have rfalse: "Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b) = Set.filter (\<lambda>\<omega>. negate b \<omega> = Some True) (Stabilize_typed \<Delta> (snd ` SA))"
  proof (rule pure_typed \<Delta>_eq[of "negate b" "Stabilize_typed \<Delta> (snd ` SA)"])
    show "wf_exp (negate b)"
      using If.prems(2) wf_abs_stmt.simps(6) wf_exp_negate by blast
    show "self_framing (Stabilize_typed \<Delta> (snd ` SA))"
      using Stabilize_self_framing by blast
  qed
*)



  have "?A1 = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b"
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> ?A1"
      using self_framing_Stabilize_typed by blast
    show "self_framing_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b)"
      by (metis (mono_tags, lifting) If.prems(2) \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> self_framing_Stabilize_typed wf_abs_stmt.simps(6) wf_exp_framed_by_typed)
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))"
      using typed_Stabilize_typed by blast
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b)"
      by (simp add: typed_Stabilize_typed typed_assertion_pure_typed typed_star)
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A1" "typed \<Delta> \<omega>"
    then have "b (stabilize \<omega>) = Some True"
      using stabilize_typed_elem by auto
    show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b"
    proof -
      have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        by (metis (no_types, lifting) UnI1 \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> asm0(2) image_Un in_Stabilize member_filter semantics.Stabilize_typed_def semantics_axioms)
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
      by (smt (verit, best) CollectD If.prems(2) add_set_commm in_set_sum pure_typed_def semantics.wf_abs_stmt.simps(6) semantics_axioms stable_and_sum_pure_same wf_exp_def x_elem_set_product)
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
      using If.prems(2) \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> framed_by_negate self_framing_Stabilize_typed semantics.wf_exp_framed_by_typed semantics_axioms wf_abs_stmt.simps(6) wf_exp_negate by blast
    
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA))"
      using typed_Stabilize_typed by blast
    show "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b))"
      by (simp add: typed_Stabilize_typed typed_assertion_pure_typed typed_star)
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A2" "typed \<Delta> \<omega>"
    then have "b (stabilize \<omega>) = Some False"
      using stabilize_typed_elem by auto
    show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)"
    proof -
      have "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        using asm0(2) stabilize_typed_elem by auto
      moreover have "b |\<omega>| = Some False"
        using wf_exp_coreE[of b \<omega>]
        by (metis If.prems(2) \<open>b (stabilize \<omega>) = Some False\<close> already_stable asm0(1) semantics.wf_abs_stmt.simps(6) semantics_axioms)
      moreover have "typed \<Delta> |\<omega>|"
        by (simp add: asm0(3) typed_core)
      ultimately have "|\<omega>| \<in> pure_typed \<Delta> (negate b)"
        using negate_def[of b "|\<omega>|"]
        by (smt (verit, ccfv_SIG) CollectI max_projection_prop_def max_projection_prop_pure_core option.discI option.sel semantics.pure_typed_def semantics_axioms)
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
(*
  have "?A2 = Stabilize_typed \<Delta> (snd ` SA) \<inter> pure_typed \<Delta> (negate b)"
  proof (rule self_framing_ext)
    show "self_framing ?A2"
      using Stabilize_self_framing by blast
    show "self_framing (Stabilize_typed \<Delta> (snd ` SA) \<inter> pure_typed \<Delta> (negate b))"

      using If(4) Stabilize_self_framing \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> framed_by_negate self_framing_conj_framed_by_exp wf_abs_stmt.simps(6) wf_exp_negate by blast

    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> ?A2"
    show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> pure_typed \<Delta> (negate b)"
    proof
      show "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)"
        using asm0(2) Stabilize_def by auto
      have "stabilize \<omega> \<in> snd ` ?S2"
        using asm0(2) Stabilize_def by blast
      then have "stabilize \<omega> \<in> pure_typed \<Delta> (negate b)"
        using negate_sat_equiv by fastforce
      then show "\<omega> \<in> pure_typed \<Delta> (negate b)"
        by (simp add: already_stable asm0(1))
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> pure_typed \<Delta> (negate b)"
    then have "\<omega> \<in> snd ` SA \<and> b \<omega> = Some False"
      by (metis IntD1 IntD2 already_stable in_Stabilize_typed \<Delta> negate_sat_equiv)
    then show "\<omega> \<in> ?A2"
      by (smt (verit, del_insts) already_stable asm0(1) image_iff in_Stabilize_typed \<Delta> member_filter)
  qed
*)
  moreover have "typed_assertion \<Delta> (Stabilize_typed \<Delta> (snd ` SA))"
    using typed_Stabilize_typed by auto
  moreover have "typed_assertion \<Delta> ?B1"
    using typed_Stabilize_typed by auto
  moreover have "typed_assertion \<Delta> ?B2"
    using typed_Stabilize_typed by auto


  moreover have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.If b C1 C2 [?B1 \<union> ?B2]"
    by (metis \<open>Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA) = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> (negate b)\<close> \<open>Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA) = Stabilize_typed \<Delta> (snd ` SA) \<otimes> pure_typed \<Delta> b\<close> \<open>\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)] C1 [Stabilize_typed \<Delta> (\<Union> (f ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))]\<close> \<open>framed_by_exp (Stabilize_typed \<Delta> (snd ` SA)) b\<close> calculation(1) calculation(2) semantics.RuleIf semantics.self_framing_Stabilize_typed semantics_axioms)

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
      using stabilize_typed_elem by auto
    show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<Longrightarrow> \<omega> \<in> ?B1 \<union> ?B2"
      using \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> stabilize_typed_elem by auto
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
      using already_stable stabilize_typed_elem by fastforce
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
    by (smt (verit) Inhale.prems(3) Stabilize_filter_stable member_filter semantics.Stabilize_typed_def semantics.wf_state_def semantics_axioms subsetD subsetI wf_set_def)

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
        using asm0(3) stabilize_typed_elem by auto
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
    by (smt (verit, best) Stabilize_def already_stable mem_Collect_eq member_filter self_framing_typed_ext semantics.Stabilize_typed_def semantics.self_framing_Stabilize_typed semantics_axioms typed_Stabilize_typed)
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
      by (meson \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)\<close> calculation(1) greater_def semantics.stabilize_typed_elem semantics.typed_core semantics.typed_smaller semantics.typed_state_then_stabilize_typed semantics_axioms typed_sum)
    then have "\<omega>'' \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      by (metis UN_upper already_stable asm0(1) calculation(1) calculation(2) insert_subset semantics.stabilize_typed_elem semantics_axioms)
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
    then show "\<omega> \<in> P" using wf_assertion_stabilize Assert(2) by simp
  qed
  moreover have "\<Union> (f ` SA) = snd ` SA"
  proof
    show "\<Union> (f ` SA) \<subseteq> snd ` SA"
      using r by auto
    show "snd ` SA \<subseteq> \<Union> (f ` SA)"
      using r by auto
  qed
  ultimately show ?case
    by (simp add: self_framing_Stabilize_typed semantics.RuleAssert semantics_axioms typed_Stabilize_typed)
next
  case (LocalAssign x e)

  let ?ty = "the (variables \<Delta> x)"
  let ?A = "post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"

  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>v. variables \<Delta> x = Some ?ty \<and> e (snd \<omega>) = Some v \<and> v \<in> ?ty
  \<and> f \<omega> = { assign_var_state x (Some v) (snd \<omega>) })"
    using LocalAssign.prems(1) by fastforce

  have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.LocalAssign x e [?A]"
  proof (rule RuleLocalAssign)
    show "self_framing_and_typed \<Delta> (Stabilize_typed \<Delta> (snd ` SA))"
      using self_framing_Stabilize_typed typed_Stabilize_typed by blast
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
  qed
  moreover have "?A = Stabilize_typed \<Delta> (\<Union> (f ` SA))" (is "?A = ?B")
  proof (rule self_framing_typed_ext)
    show "self_framing_typed \<Delta> (post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA)))"
      using LocalAssign.prems(2) calculation proofs_are_self_framing_and_typed by blast
    show "typed_assertion \<Delta> (post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA)))"
      using LocalAssign.prems(2) calculation proofs_are_self_framing_and_typed by blast

    fix \<omega> assume asm0: "stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"
    then obtain \<omega>' where "\<omega>' \<in> Stabilize_typed \<Delta> (snd ` SA)" "\<omega> = assign_var_state x (e \<omega>') \<omega>'"
      using post_substitute_var_assert_def substitute_var_state_def by auto
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' = snd \<alpha>"
      by (meson image_iff stabilize_typed_elem)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> e (stabilize \<omega>') = Some v \<and> v \<in> ?ty
  \<and> f \<alpha> = {assign_var_state x (Some v) (stabilize \<omega>')}"
      using r by presburger
    moreover have "stable \<omega>'"
      using \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> asm0(1) stable_assign_var_state by auto
    then show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      by (metis (no_types, lifting) UnI1 Union_image_insert \<open>\<alpha> \<in> SA\<close> \<open>\<omega> = assign_var_state x (e \<omega>') \<omega>'\<close> already_stable asm0(2) calculation image_insert insert_image semantics.stabilize_assign_var semantics.stabilize_typed_elem semantics_axioms singletonI)
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
      using \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> e (snd \<alpha>) = Some v \<and> v \<in> the (variables \<Delta> x) \<and> f \<alpha> = {assign_var_state x (Some v) (snd \<alpha>)}\<close> substitute_var_state_def by presburger
    moreover have "snd \<alpha> \<in> Stabilize_typed \<Delta> (snd ` SA)"
      by (metis (no_types, lifting) LocalAssign.prems(3) \<open>\<alpha> \<in> SA\<close> already_stable image_insert insertI1 mk_disjoint_insert semantics.wf_state_def semantics_axioms stabilize_typed_elem wf_set_def)
    ultimately show "\<omega> \<in> post_substitute_var_assert x e (Stabilize_typed \<Delta> (snd ` SA))"
      using post_substitute_var_assert_def by fast
  qed (simp_all)
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.LocalAssign x e [Stabilize_typed \<Delta> (\<Union> (f ` SA))]"
    by argo
next
  case Skip
  then have "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] Skip [Stabilize_typed \<Delta> (snd ` SA)]"
    using RuleSkip semantics.self_framing_Stabilize_typed semantics_axioms typed_Stabilize_typed by blast
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
      using self_framing_Stabilize_typed typed_Stabilize_typed by presburger
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
      using stabilize_typed_elem by auto
    then have "assign_var_state x (Some v) \<omega> = snd \<alpha>"
      by (metis already_stable asm0(1) stable_assign_var_state)
    then have "\<omega> = assign_var_state x (Some v0) (snd \<alpha>)"
      by (metis asm1(2) assign_var_state_inverse)
    then have "stabilize \<omega> \<in> f \<alpha>"
      using \<open>\<alpha> \<in> SA\<close> already_stable asm0(1) asm1(1) asm1(3) r by auto
    then show "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      using \<open>\<alpha> \<in> SA\<close> asm0(2) stabilize_typed_elem by auto
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>" "\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))"
    then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega> \<in> f \<alpha>"
      by (metis UN_E already_stable stabilize_typed_elem)
    then obtain v where "variables \<Delta> x = Some ?ty \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)" "v \<in> ?ty"
      using r by blast
    then have "wf_state \<Delta> (snd \<alpha>)"
      using Havoc.prems(3) \<open>\<alpha> \<in> SA\<close> wf_set_def by auto
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
        by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>get_store (snd \<alpha>) x = Some v'\<close> \<open>variables \<Delta> x = Some (the (variables \<Delta> x)) \<and> \<omega> = assign_var_state x (Some v) (snd \<alpha>)\<close> \<open>wf_state \<Delta> (snd \<alpha>)\<close> already_stable insertI1 insert_image semantics.assign_var_state_inverse semantics.stabilize_typed_elem semantics.wf_state_def semantics_axioms)
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
        using stabilize_typed_elem by auto
      then have "stable_on (snd \<alpha>) P \<and> f \<alpha> = {snd \<alpha>} \<inter> P" using r by blast
      then have "f \<alpha> = {stabilize \<omega>}"
        by (metis (no_types, lifting) Assume.prems(1) IntD2 \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> P\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> pure_larger_stabilize red_stmt_Assume_elim stable_on_def)
      then show "\<omega> \<in> ?B"
        using \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA) \<inter> P\<close> \<open>stable_on (snd \<alpha>) P \<and> f \<alpha> = {snd \<alpha>} \<inter> P\<close> r stabilize_typed_elem by auto
    qed
    show "?B \<subseteq> ?A \<inter> P"
    proof
      fix \<omega> assume "\<omega> \<in> ?B"
      then obtain \<alpha> where "stabilize \<omega> \<in> f \<alpha>" "\<alpha> \<in> SA"
        using stabilize_typed_elem by auto
      then show "\<omega> \<in> ?A \<inter> P"
        using Assume.prems(2) Int_iff \<open>\<omega> \<in> Stabilize_typed \<Delta> (\<Union> (f ` SA))\<close> image_insert r stabilize_typed_elem wf_assertion_stabilize by auto
    qed
  qed
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.Assume P [Stabilize_typed \<Delta> (\<Union> (f ` SA))]" by argo
next
  case (Custom C)
  then show ?case sorry (* TODO *)
next
  case (Scope x1a x2a C)
  then show ?case sorry
qed




lemma Viper_implies_SL_proof:
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
      using SA_def wf_state_def by force
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
        by (metis Range.intros already_stable asm0 asm1 assms(4) semantics.typed_assertion_def semantics_axioms snd_eq_Range stabilize_typed_elem)
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

(*
definition overapprox_fv :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> var set \<Rightarrow> bool" where
  "overapprox_fv \<Delta> A S \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed_store \<Delta> \<sigma>1 \<and> typed_store \<Delta> \<sigma>2 \<and> equal_on_set S \<sigma>1 \<sigma>2 \<longrightarrow> ((Ag \<sigma>1, \<gamma>) \<in> A \<longleftrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A))"


definition free_vars where
  "free_vars \<Delta> A = (\<Inter>S \<in> {S. overapprox_fv \<Delta> A S}. S)"
*)
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
(*    and "finite (dom (variables \<Delta>))" *)
    shows "(Ag \<sigma>2, \<gamma>) \<in> A"
  sorry

lemma get_store_Ag_simplifies[simp]:
  "get_store (Ag \<sigma>, \<gamma>) = \<sigma>"
  by (simp add: get_store_def)

lemma set_store_Ag_simplies[simp]:
  "set_store (\<alpha>, \<gamma>) \<sigma> = (Ag \<sigma>, \<gamma>)"  
  by (simp add: get_state_def set_store_def)


lemma typed_store_update:
  assumes "typed_store \<Delta> \<sigma>"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
    shows "typed_store \<Delta> (\<sigma>(x \<mapsto> v))"
  using assms(1) assms(2) assms(3) typed_store_def by auto


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
    by (smt (verit) assign_var_state_def assign_var_state_inverse get_state_set_store get_store_set_store prod.inject set_store_def)
  moreover have "equal_on_set (free_vars \<Delta> A) (\<sigma>1(x \<mapsto> v)) (\<sigma>2(x \<mapsto> v))"
    using asm0(1) equal_on_set_def by force
  then have "(Ag (\<sigma>2(x \<mapsto> v)), \<gamma>) \<in> A"
    by (rule free_varsE) (simp_all add: asm0 r typed_store_update calculation)
  then have "set_store (Ag \<sigma>2, \<gamma>) ((get_store (Ag \<sigma>2, \<gamma>))(x \<mapsto> v)) \<in> A"
    by (simp add: get_state_def set_store_def)
  moreover obtain v0' where "get_store (Ag \<sigma>2, \<gamma>) x = Some v0'"
    by (metis agreement.exhaust_sel agreement.inject asm0(1) domD domI get_store_def prod.sel(1) r(3) typed_store_def)
  then have "v0' \<in> ty"
    by (metis agreement.exhaust_sel agreement.inject asm0(1) get_store_def prod.sel(1) r(3) typed_store_def)
  ultimately show "(Ag \<sigma>2, \<gamma>) \<in> exists_assert \<Delta> x A"
    unfolding exists_assert_def
    by (smt (verit) \<open>get_store (Ag \<sigma>2, \<gamma>) x = Some v0'\<close> asm0(1) asm0(2) assign_var_state_def get_store_Ag_simplifies mem_Collect_eq r(3) r(4) semantics.exists_assertE semantics_axioms set_store_Ag_simplies set_store_def snd_conv typed_def)
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
    by (smt (verit, best) asm0 assms(2) domD domIff full_state_ext fun_upd_triv get_state_set_store get_store_set_store typed_def typed_store_def)
  then show "\<omega> \<in> exists_assert \<Delta> x A"
    by (metis \<open>typed \<Delta> \<omega>\<close> assign_var_state_def exists_assertI)
qed


lemma SL_proof_Havoc_elim:
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
    using SL_proof_Havoc_elim[OF r(1)] calculation by simp
  ultimately show "self_framing_and_typed \<Delta> A \<and> self_framing_and_typed \<Delta> B \<and> entails A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - set (x # l)"
    by (metis (no_types, lifting) semantics.SL_proof_Havoc_elim Diff_insert2 Diff_mono dual_order.refl entails_trans list.simps(15) semantics_axioms subset_trans)
qed





















lemma SL_proof_implies_Viper:
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
  case (RuleInhale A P uv)
  then show ?case sorry
next
  case (RuleExhale B A P uw)
  then show ?case sorry
next
  case (RuleAssert A P ux)
  then show ?case sorry
next
  case (RuleAssume A P uy)
  then show ?case sorry
next
  case (RuleHavoc A \<Delta> x)
  then show ?case sorry
next
  case (RuleLocalAssign A e uz x)
  then show ?case sorry
next
  case (RuleSeq \<Delta> A C1 R C2 B)
  then show ?case sorry
next
  case (RuleIf A b \<Delta> C1 B1 C2 B2)
  then show ?case sorry
next
  case (RuleCustom A B \<Delta> C)
  then show ?case sorry
qed





  case (RuleSkip \<Delta> T)
  then show ?case
    using RedSkip by blast
next
  case (RuleInhale A P \<Delta>)
  then have "WdInhale P \<omega>"
    using framed_by_def by fastforce
  then have "red_stmt \<Delta> (Inhale P) \<omega> (Set.filter stable ({\<omega>} \<otimes> P))"
    using RedInhale by auto
  moreover have "{\<omega>} \<otimes> P \<subseteq> \<langle>astar A P\<rangle>"
  proof
    fix \<omega>' assume "\<omega>' \<in> {\<omega>} \<otimes> P"
    then obtain p where "p \<in> P" "Some \<omega>' = \<omega> \<oplus> p"
      by (metis (no_types, lifting) singletonD x_elem_set_product)
    then show "\<omega>' \<in> \<langle>astar A P\<rangle>"
      by (smt (verit, del_insts) RuleInhale.prems(1) inh_def mem_Collect_eq astar_def)
  qed
  ultimately show "\<exists>S. red_stmt \<Delta> (Inhale P) \<omega> S \<and> S \<subseteq> \<langle>astar A P\<rangle>"
    by (metis (no_types, lifting) member_filter subset_iff)
next
  case (RuleExhale A P \<Delta>)
(*
self_framing A
    framed_by A P
    \<omega> \<in> \<langle>astar A P\<rangle>
*)
  then obtain \<omega>' a where "a \<in> P" "Some \<omega> = \<omega>' \<oplus> a" "\<omega>' \<in> \<langle>A\<rangle>"
    by (smt (verit) inh_def mem_Collect_eq astar_def)
  then obtain \<omega>'' where "Some \<omega>'' = \<omega>' \<oplus> |\<omega>|"
    by (metis commutative minus_equiv_def_any_elem)
  let ?\<omega>' = "stabilize \<omega>''"
  have "stable ?\<omega>'"
    by (simp add: stabilize_is_stable)
  moreover have "Some \<omega> = \<omega>'' \<oplus> a"
    by (smt (verit) \<open>Some \<omega> = \<omega>' \<oplus> a\<close> \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> asso1 commutative core_is_smaller)
  then have "Some \<omega> = ?\<omega>' \<oplus> a"
    sorry
  ultimately have "red_stmt \<Delta> (Exhale P) \<omega> {?\<omega>'}"
    using \<open>a \<in> P\<close> full_add_charact(1) RedExhale by blast
  moreover have "?\<omega>' \<in> \<langle>A\<rangle>"
    sorry
  ultimately show "\<exists>S. red_stmt \<Delta> (Exhale P) \<omega> S \<and> S \<subseteq> \<langle>A\<rangle>"
    by (meson empty_subsetI insert_subsetI)
next
  case (RuleSeq \<Delta> A C1 R C2 B)
  then obtain SA where "red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>"
    using wf_abs_stmt.simps(6) by blast
  let ?f = "\<lambda>x. (SOME Sx. red_stmt \<Delta> C2 x Sx \<and> Sx \<subseteq> \<langle>B\<rangle>)"
  have r: "\<And>x. x \<in> SA \<Longrightarrow> red_stmt \<Delta> C2 x (?f x) \<and> ?f x \<subseteq> \<langle>B\<rangle>"
  proof -
    fix x assume "x \<in> SA"
    show "red_stmt \<Delta> C2 x (?f x) \<and> ?f x \<subseteq> \<langle>B\<rangle>"
    proof (rule someI_ex)
      show "\<exists>xa. red_stmt \<Delta> C2 x xa \<and> xa \<subseteq> \<langle>B\<rangle>"
        using RuleSeq.hyps(4) RuleSeq.prems(2) RuleSeq.prems(3) \<open>red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>\<close> \<open>x \<in> SA\<close> red_stable wf_abs_stmt.simps(6) by blast
    qed
  qed
  let ?S = "Union (?f ` SA)"
  have "sequential_composition \<Delta> SA C2 ?S"
    using SeqComp r by presburger
  then have "red_stmt \<Delta> (Seq C1 C2) \<omega> ?S"
    by (meson RedSeq \<open>red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>\<close>)
  moreover have "?S \<subseteq> \<langle>B\<rangle>"
    using r by blast
  ultimately show "\<exists>S. red_stmt \<Delta> (Seq C1 C2) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
    by meson
next
(*
  case (RuleFrame F \<Delta> A C B)
  then obtain a f where "Some \<omega> = a \<oplus> f" "a \<in> \<langle>A\<rangle>" "f \<in> \<langle>F\<rangle>" "stable \<omega>"
    by (smt (verit, best) inh_def mem_Collect_eq astar_def)
  then obtain aa ff where aa_ff: "ff \<in> \<langle>F\<rangle>" "stable ff" "Some \<omega> = aa \<oplus> ff" "stable aa" "aa \<in> \<langle>A\<rangle>" "dom_vars ff \<inter> modif C = {}" sorry
  then obtain S where "red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>"
    using RuleFrame.hyps(3) RuleFrame.prems(2) by presburger
  then have "Some \<omega> = aa \<oplus> (fst \<omega>, get_state ff)"
    by (metis Pair_inject \<open>Some \<omega> = aa \<oplus> ff\<close> commutative full_add_charact(1) full_state_ext get_state_def get_store_def prod.collapse)
  then obtain S' where r: "red_stmt \<Delta> C \<omega> S' \<and> S' \<subseteq> S \<otimes> UNIV \<times> {get_state ff}"
    using frame_rule_aux(1)[of \<Delta> C aa S "get_state ff" \<omega>]
    by (metis RuleFrame.prems(2) \<open>red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>\<close> \<open>sep_algebra_class.stable aa\<close> \<open>sep_algebra_class.stable ff\<close> get_state_def stable_snd)

  moreover have "S' \<subseteq> \<langle>astar B F\<rangle>"
  proof
    fix \<omega>' assume "\<omega>' \<in> S'"
    then have "\<omega>' \<in> S \<otimes> UNIV \<times> {get_state ff}"
      using calculation by auto
    then obtain b s where "Some \<omega>' = b \<oplus> (s, get_state ff)" "b \<in> S"
      by (smt (verit, best) Sigma_cong get_state_def in_univ prod.collapse x_elem_set_product)
    then have "s = fst \<omega>' \<and> b \<in> \<langle>B\<rangle>"
      by (metis \<open>red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>\<close> commutative fst_conv full_add_charact(1) full_state_ext get_state_def get_store_def snd_conv subsetD)
    moreover have "(s, get_state ff) \<in> \<langle>F\<rangle>"
    proof -
      have "\<And>x. is_free_var F x \<Longrightarrow> the_ag s x = get_store ff x"
      proof -
        fix x :: string
        assume "is_free_var F x"
        then have "x \<notin> modif C"
          using RuleFrame.hyps(4) free_var_def by fastforce
        then have "get_store \<omega> x = get_store \<omega>' x"
          using \<open>\<omega>' \<in> S'\<close> r only_modif_can_be_modified by blast
        then show "the_ag s x = get_store ff x"
          by (metis aa_ff(3) calculation full_add_charact(1) full_add_defined get_store_def)
      qed
      then show ?thesis
        by (metis aa_ff(1) get_state_def get_store_def inh_def mem_Collect_eq prod.collapse same_on_free_var(2))
    qed
    ultimately show "\<omega>' \<in> \<langle>astar B F\<rangle>"
      by (smt (verit) \<open>Some \<omega>' = b \<oplus> (s, get_state ff)\<close> inh_def mem_Collect_eq astar_def)
  qed
  ultimately show ?case
    by blast
*)
next
(*
  case (RuleConsPre \<Delta> A' A T C B)
  then show ?case
    by (meson entails_def subsetD)
next
  case (RuleConsPost B B' \<Delta> A C)
(*
    entails B B'
    self_framing B'
     \<Delta> \<turnstile> [A] C [B]
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> wf_abs_stmt \<Delta> C \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> C ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    \<omega> \<in> \<langle>A\<rangle>
    wf_abs_stmt \<Delta> C
    sep_algebra_class.stable \<omega>
*)
  then obtain S where "red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
    by presburger
  then show "\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B'\<rangle>"
    by (meson RuleConsPost.hyps(1) dual_order.trans entails_def)
next
*)
  case (RuleFieldAssign A r e \<Delta>)
  then show ?case sorry
next
  case (RuleAssert A P \<Delta>)
  then show ?case sorry
next
  case (RuleHavoc A x \<Delta>)
  then show ?case sorry
(*
next
  case (RuleEquiv)
  then show ?case sorry
*)
qed













lemma Test: "True"
  by simp



















(*

next



  case (FieldAssign r e)
(*
| RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; has_write_perm (get_state \<omega>) hl; heap_locs \<Delta> hl = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_stmt \<Delta> (FieldAssign r e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) hl v)}"
*)
  then have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (\<exists>hl v ty. r (snd \<alpha>) = Some hl \<and> e (snd \<alpha>) = Some v \<and> has_write_perm (get_state (snd \<alpha>)) hl
  \<and> heap_locs \<Delta> hl = Some ty \<and> v \<in> ty \<and> f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) hl v)} )"
    by blast

  define eval_r :: "('v, 'a) abs_state \<Rightarrow> 'r" where "eval_r = (\<lambda>\<omega>. SOME v. r \<omega> = Some v)"
  then have eval_r_prop: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> r (snd \<omega>) = Some (eval_r (snd \<omega>))"
    using r by force

  define get_ptr :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state"
    where "get_ptr = (\<lambda>\<alpha>. SOME ptr. has_write_perm_only (get_state ptr) (the (r (snd \<alpha>))) \<and> snd \<alpha> \<succeq> ptr)"
  have get_ptr_prop: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> has_write_perm_only (get_state (get_ptr \<alpha>)) (the (r (snd \<alpha>))) \<and> snd \<alpha> \<succeq> (get_ptr \<alpha>)"
    sorry

  define get_rm where "get_rm = (\<lambda>\<alpha>. stabilize (snd \<alpha> \<ominus> get_ptr \<alpha>))"
(*
  define get_rm where "get_rm = (\<lambda>\<alpha>. stabilize (snd \<alpha> \<ominus> get_ptr \<alpha>))"
*)
  have get_rm_prop: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> Some (snd \<alpha>) = get_rm \<alpha> \<oplus> get_ptr \<alpha>"
    by (smt (z3) FieldAssign.prems(3) commutative get_ptr_prop get_rm_def image_insert insertCI minus_equiv_def mk_disjoint_insert stabilize_sum_result_stable wf_set_def wf_state_def)


  let ?A = "Stabilize_typed \<Delta> (get_rm ` SA)"
  let ?b = "\<lambda>\<omega>. if (\<exists>\<omega>' \<in> snd ` SA. \<omega> \<succeq> |\<omega>'| ) then Some True else None"
(*  let ?b = "\<lambda>\<omega>. if (\<exists>\<omega>' \<in> snd ` SA. |\<omega>| \<succeq> |\<omega>'| ) then Some True else None" *)

(* not this,
|\<omega>| \<in> snd ` SA then Some True else Some False"
rather if \<exists>\<omega>' \<in> snd ` SA such that |\<omega>'| = |\<omega>|...
TODO: Think about it
*)

  have "\<Delta> \<turnstile> [?A \<otimes> points_to r \<otimes> pure_typed \<Delta> ?b] abs_stmt.FieldAssign r e [?A \<otimes> pure_post_field_assign r e ?b]"
  proof (rule RuleFieldAssign)
    show "self_framing (Stabilize_typed \<Delta> (get_rm ` SA))"
      using Stabilize_self_framing by blast
    show "wf_exp ?b"
    proof (rule wf_expI)
      fix a show "\<And>a. (if \<exists>\<omega>'\<in>snd ` SA. a \<succeq> |\<omega>'| then Some True else None) = (if \<exists>\<omega>'\<in>snd ` SA. |a| \<succeq> |\<omega>'| then Some True else None)"
        by (metis (no_types, lifting) max_projection_prop_def max_projection_prop_pure_core succ_trans)
      show "\<And>b v. a \<succeq> b \<and> (if \<exists>\<omega>'\<in>snd ` SA. b \<succeq> |\<omega>'| then Some True else None) = Some v \<Longrightarrow> (if \<exists>\<omega>'\<in>snd ` SA. a \<succeq> |\<omega>'| then Some True else None) = Some v"
        by (meson core_stabilize_mono(1) option.distinct(1) succ_trans)
    qed

    show "framed_by_exp (Stabilize_typed \<Delta> (get_rm ` SA)) r"
    proof (rule framed_by_expI)
      fix \<omega> assume "\<omega> \<in> Stabilize_typed \<Delta> (get_rm ` SA)"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> \<succeq> |snd \<alpha>|"
        using get_ptr_prop get_rm_def minus_equiv_def by fastforce
      moreover have "r (snd \<alpha>) \<noteq> None"
        by (simp add: calculation(1) eval_r_prop)
      ultimately show "r \<omega> \<noteq> None" using wf_exp_def[of r]
        by (smt (verit, ccfv_SIG) FieldAssign.prems(2) r wf_abs_stmt.simps(9) wf_exp_stabilize)
    qed

    show "framed_by_exp (Stabilize_typed \<Delta> (get_rm ` SA) \<otimes> points_to r) ?b"
    proof (rule framed_by_expI)
      fix \<omega> assume "\<omega> \<in> Stabilize_typed \<Delta> (get_rm ` SA) \<otimes> points_to r"
      then obtain \<alpha> \<omega>' ptr where "\<alpha> \<in> SA" "stabilize \<omega>' = get_rm \<alpha>" "Some \<omega> = \<omega>' \<oplus> ptr" "ptr \<in> points_to r"
        by (meson image_iff in_Stabilize_typed \<Delta> x_elem_set_product)
      then have "Some (snd \<alpha>) = get_rm \<alpha> \<oplus> get_ptr \<alpha>"   
        using get_rm_prop by blast
      then have "get_ptr \<alpha> = ptr"
        sorry
      then have "\<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'|"
        sorry

      then have "stabilize \<omega>' = stabilize (snd \<alpha> \<ominus> get_ptr \<alpha>)"
        using get_rm_def by force

        using get_rm_def by blast
      then have "|\<omega>| \<succeq> |snd \<alpha>|"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega> = \<omega>' \<oplus> ptr\<close> core_stabilize_mono(1) greater_def max_projection_prop_def max_projection_prop_stable_stabilize minus_core succ_trans)
      then show "(if \<exists>\<omega>'\<in>snd ` SA. |\<omega>| \<succeq> |\<omega>'| then Some True else None) \<noteq> None"
        using \<open>\<alpha> \<in> SA\<close> by auto
    qed

    show "framed_by_exp (Stabilize_typed \<Delta> (get_rm ` SA) \<otimes> points_to r \<otimes> pure_typed \<Delta> ?b) e"
    proof (rule framed_by_expI)
      fix \<omega> assume "\<omega> \<in> (Stabilize_typed \<Delta> (get_rm ` SA) \<otimes> points_to r) \<otimes> pure_typed \<Delta> (\<lambda>\<omega>. if \<exists>\<omega>'\<in>snd ` SA. |\<omega>| \<succeq> |\<omega>'| then Some True else None)"
      then obtain p where "\<omega> \<succeq> p" "p \<in> pure_typed \<Delta> ?b"
        using add_set_commm in_set_sum by blast
      then obtain \<omega>' where "\<omega>'\<in>snd ` SA" "|p| \<succeq> |\<omega>'|" "pure p"
        by (smt (verit, ccfv_threshold) mem_Collect_eq option.distinct(1) pure_typed \<Delta>_def)
      then obtain \<alpha> where "\<alpha> \<in> SA" "\<omega>' = snd \<alpha>"
        by blast
      then have "e (snd \<alpha>) \<noteq> None" using r by fast
      then have "e p \<noteq> None" using wf_exp_def[of e]
        by (metis FieldAssign.prems(2) \<open>\<alpha> \<in> SA\<close> \<open>\<omega>' = snd \<alpha>\<close> \<open>|p| \<succeq> |\<omega>'|\<close> r wf_abs_stmt.simps(9))
      then show "e \<omega> \<noteq> None" using wf_exp_def[of e]
        using FieldAssign.prems(2) \<open>\<omega> \<succeq> p\<close> wf_abs_stmt.simps(9) by blast
    qed
  qed
  moreover have "Stabilize_typed \<Delta> (snd ` SA) = ?A \<otimes> points_to r \<otimes> pure_typed \<Delta> ?b" (is "?P = ?Q")
  proof
    show "?P \<subseteq> ?Q"
    proof
      fix \<omega> assume "\<omega> \<in> ?P"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by auto
      then have "Some (stabilize \<omega>) = get_rm \<alpha> \<oplus> get_ptr \<alpha>"
        using get_rm_prop by presburger
(*
      then have "Some (stabilize \<omega>) = get_rm \<alpha> \<oplus> get_ptr \<alpha>"
        using stabilize_is_stable stabilize_sum_result_stable by blast
*)
      moreover have "get_ptr \<alpha> \<in> points_to r"
        sorry
      moreover have "get_rm \<alpha> \<in> ?A"
        by (simp add: \<open>\<alpha> \<in> SA\<close> already_stable get_rm_def stabilize_is_stable)

      moreover have "Some \<omega> = stabilize \<omega> \<oplus> |\<omega>|"
        using decompose_stabilize_pure by auto
      moreover have "\<exists>\<omega>'\<in>snd ` SA. |\<omega>| \<succeq> |\<omega>'|"
        by (meson \<open>\<omega> \<in> Stabilize_typed \<Delta> (snd ` SA)\<close> calculation(4) core_sum greater_def in_Stabilize)
      then have "\<exists>\<omega>'\<in>snd ` SA. ||\<omega>|| \<succeq> |\<omega>'|"
        by (metis (no_types, lifting) calculation(4) minusI minus_core succ_refl)

      then have "|\<omega>| \<in> pure_typed \<Delta> ?b"        
        by (simp add: core_is_pure pure_typed \<Delta>_def pure_def)
      ultimately show "\<omega> \<in> ?Q"
        by (meson x_elem_set_product)
    qed
    show "?Q \<subseteq> ?P" sorry
  qed

  moreover have "Stabilize_typed \<Delta> (\<Union> (f ` SA)) = ?A \<otimes> pure_post_field_assign r e ?b"
    sorry

  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] abs_stmt.FieldAssign r e [Stabilize_typed \<Delta> (\<Union> (f ` SA))]" by argo
next




(* TODO: Split snd ` SA into [?A \<otimes> points_to r \<otimes> pure_typed \<Delta> ?b] *)



(*
b = |\<omega>| ?

*)





  thm RuleFieldAssign[of _ r _ e \<Delta>]


  show ?case
  proof (cases "depends_on_ag_store_only r \<and> depends_on_ag_store_only e")
    case True
    
    

    moreover have r_ptr: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow>
    (\<exists>\<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr \<omega> \<and> has_write_perm_only (get_ptr \<omega>) hl \<and> stable (get_ptr \<omega>))"
    proof -
      fix \<omega> assume "\<omega> \<in> SA"
      show "\<exists>\<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr \<omega> \<and> has_write_perm_only (get_ptr \<omega>) hl \<and> stable (get_ptr \<omega>)"
        unfolding get_ptr_def
      proof (rule someI_ex)
        obtain x \<sigma> \<gamma> hl v where "snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> x \<and> has_write_perm_only x hl"
          using \<open>\<omega> \<in> SA\<close> r by meson
        then have "has_write_perm_only (stabilize x) hl" sorry
(* TODO: Add *)

        then show "\<exists>x \<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> x \<and> has_write_perm_only x hl \<and> sep_algebra_class.stable x"
          sorry
          (* by (metis (mono_tags, lifting) \<open>snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> x \<and> has_write_perm_only x hl\<close> max_projection_prop_def max_projection_prop_stable_stabilize succ_trans) *)
      qed
    qed
    define get_rem where "get_rem = (\<lambda>\<omega>. SOME x. \<exists>\<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v
    \<and> Some (\<sigma>, \<gamma>) = x \<oplus> (\<sigma>, get_ptr \<omega>) \<and> stable x \<and> fst x = \<sigma>)"
    moreover have r_get_rem: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow>
    (\<exists>\<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> Some (\<sigma>, \<gamma>) = get_rem \<omega> \<oplus> (\<sigma>, get_ptr \<omega>) \<and> stable (get_rem \<omega>) \<and> fst (get_rem \<omega>) = \<sigma>  )"
    proof -
      fix \<omega> assume "\<omega> \<in> SA"
      show "\<exists>\<sigma> \<gamma> hl v.
              snd \<omega> = (\<sigma>, \<gamma>) \<and>
              f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> Some (\<sigma>, \<gamma>) = get_rem \<omega> \<oplus> (\<sigma>, get_ptr \<omega>) \<and> stable (get_rem \<omega>) \<and> fst (get_rem \<omega>) = \<sigma>"
        unfolding get_rem_def
      proof (rule someI_ex)
        obtain \<sigma> \<gamma> hl v where "snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr \<omega> \<and> has_write_perm_only (get_ptr \<omega>) hl"
          using \<open>\<omega> \<in> SA\<close> r_ptr by meson
        then obtain x where "Some \<gamma> = x \<oplus> get_ptr \<omega>"
          using greater_equiv by blast
        moreover have "stable \<gamma>" using \<open>\<omega> \<in> SA\<close> \<open>wf_set \<Delta> (snd ` SA)\<close> wf_set_def
          by (metis \<open>snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr \<omega> \<and> has_write_perm_only (get_ptr \<omega>) hl\<close> imageI snd_conv stable_snd wf_state_def)
        ultimately have "Some \<gamma> = stabilize x \<oplus> get_ptr \<omega>"
          using stabilize_sum_result_stable by blast
        then show "\<exists>x \<sigma> \<gamma> hl v.
       snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> Some (\<sigma>, \<gamma>) = x \<oplus> (\<sigma>, get_ptr \<omega>) \<and> sep_algebra_class.stable x \<and> fst x = \<sigma>"
          sorry
(*
          using \<open>snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr \<omega> \<and> has_write_perm_only (get_ptr \<omega>) hl\<close> add_defined_lift stabilize_is_stable stable_snd
          *)
      qed
    qed
    
    let ?SA = "(stabilize \<circ> get_rem) ` SA"
    
    let ?A = "Stabilize_typed \<Delta> ?SA"


    have "framed_by_exp ?A r" sorry

    moreover have "framed_by_exp ?A e" sorry

    moreover have "self_framing ?A"
      using Stabilize_self_framing by auto
(* points_to_r is also self_framing *)
    
    ultimately have "\<Delta> \<turnstile> [?A \<otimes> points_to r] FieldAssign r e [?A \<otimes> points_to_value r e]"
      using True RuleFieldAssignHeapIndep by blast
    
    moreover have "Stabilize_typed \<Delta> (snd ` SA) = ?A \<otimes> points_to r"
    proof (rule self_framing_ext)
      show "self_framing (Stabilize_typed \<Delta> (snd ` SA))"
        using Stabilize_self_framing by auto
    
      show "self_framing (?A \<otimes> points_to r)"
        using calculation proofs_are_self_framing by presburger
    
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "Stabilize_typed \<Delta> (snd ` SA) \<omega>"
      then obtain x where "x \<in> SA" "snd x = \<omega>"
        using already_stable Stabilize_def by fastforce
      then obtain \<sigma> \<gamma> hl v where "snd x = (\<sigma>, \<gamma>)" "f x = {(\<sigma>, set_value \<gamma> hl v)}" "r (\<sigma>, \<gamma>) = Some hl"
        "e (\<sigma>, \<gamma>) = Some v" "Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)" "stable (get_rem x)" "fst (get_rem x) = \<sigma>"
        using r_get_rem by blast
    
      show "(Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) \<otimes> points_to r) \<omega>"
      proof (rule sat_starI)
        show "Some \<omega> = get_rem x \<oplus> (\<sigma>, get_ptr x)"
          using \<open>Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)\<close> \<open>snd x = (\<sigma>, \<gamma>)\<close> \<open>snd x = \<omega>\<close> by auto
        show "Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) (get_rem x)"
          using \<open>x \<in> SA\<close> Stabilize_def by auto
    
        show "points_to r (\<sigma>, get_ptr x)"
        proof (rule points_toI)
          show "has_write_perm_only (get_state (\<sigma>, get_ptr x)) hl"
            by (smt (verit, ccfv_SIG) \<open>r (\<sigma>, \<gamma>) = Some hl\<close> \<open>snd x = (\<sigma>, \<gamma>)\<close> \<open>x \<in> SA\<close> get_state_def option.inject r_ptr snd_eqD)
          show "r (\<sigma>, get_ptr x) = Some hl"
            by (metis (no_types, lifting) True \<open>r (\<sigma>, \<gamma>) = Some hl\<close> depends_on_ag_store_only_def)
        qed
      qed
    next
      fix \<omega>
      assume asm0: "sep_algebra_class.stable \<omega>" "(Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) \<otimes> points_to r) \<omega>"
      then obtain a ptr where "Some \<omega> = a \<oplus> ptr" "stabilize a \<in> (stabilize \<circ> get_rem) ` SA" "points_to r ptr"
        using Stabilize_def astar_def by auto
      then obtain x where "x \<in> SA" "stabilize a = stabilize (get_rem x)"
        by auto
    
      then obtain \<sigma> \<gamma> hl v where "snd x = (\<sigma>, \<gamma>)" "f x = {(\<sigma>, set_value \<gamma> hl v)}" "r (\<sigma>, \<gamma>) = Some hl"
        "e (\<sigma>, \<gamma>) = Some v" "Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)" "stable (get_rem x)" "fst (get_rem x) = \<sigma>"
        using r_get_rem by fast
      then have "\<sigma> = fst \<omega>" sorry
(*
        by (metis Pair_inject \<open>Some \<omega> = a \<oplus> ptr\<close> \<open>stabilize a = stabilize (get_rem x)\<close> agreement.expand full_add_charact(1) get_store_def stabilize_state_equiv)
*)
      then have "r \<omega> = Some hl"
        by (metis (no_types, lifting) True \<open>r (\<sigma>, \<gamma>) = Some hl\<close> depends_on_ag_store_only_def prod.exhaust_sel)    

      moreover have "fst ptr = \<sigma>"
        sorry
(*
        by (metis \<open>\<sigma> = fst \<omega>\<close> agreement.collapse get_store_def get_trace_def greater_charact neutral_smallest prod.collapse)
*)

      moreover have "stabilize ptr = stabilize (\<sigma>, get_ptr x)"
      proof (rule points_to_two)
        show "wf_exp r"
          using FieldAssign.prems(2) by auto

        show "r ptr = r (\<sigma>, get_ptr x)"
          by (metis (no_types, lifting) True calculation(2) depends_on_ag_store_only_def prod.exhaust_sel)
        show "fst ptr = fst (\<sigma>, get_ptr x)"
          by (simp add: calculation(2))
        show "points_to r ptr"
          using \<open>points_to r ptr\<close> by auto
        show "points_to r (\<sigma>, get_ptr x)"
          sorry
(*
          by (smt (verit, ccfv_threshold) True \<open>snd x = (\<sigma>, \<tau>, \<gamma>)\<close> \<open>x \<in> SA\<close> depends_on_ag_store_only_def r_ptr points_toI snd_conv)
*)
      qed


      moreover have "Some (snd x) = get_rem x \<oplus> (fst \<omega>, get_ptr x)"
        using \<open>Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)\<close> \<open>\<sigma> = fst \<omega>\<close> \<open>snd x = (\<sigma>, \<gamma>)\<close> by auto
      ultimately have "stabilize (snd x) = stabilize \<omega>"
        by (metis (no_types, lifting) \<open>Some \<omega> = a \<oplus> ptr\<close> \<open>\<sigma> = fst \<omega>\<close> \<open>stabilize a = stabilize (get_rem x)\<close> option.sel stabilize_sum)
      then show "Stabilize_typed \<Delta> (snd ` SA) \<omega>"
        by (metis (no_types, lifting) FieldAssign.prems(3) \<open>x \<in> SA\<close> already_stable Stabilize_def Stabilize_equal image_eqI member_filter)
    qed
    
    moreover have "Stabilize_typed \<Delta> (\<Union> (f ` SA)) = ?A \<otimes> points_to_value r e"
    proof (rule self_framing_ext)
      show "self_framing (Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
        using Stabilize_self_framing by auto
      show "self_framing (Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) \<otimes> points_to_value r e)"
        sorry
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<omega>"
      then obtain x where "x \<in> SA" "\<omega> \<in> f x"
        using already_stable Stabilize_def by fastforce
      then obtain \<sigma> \<gamma> hl v ptr
        where "snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl"
        using r by metis
      then have "\<omega> = (\<sigma>, set_value \<gamma> hl v)"
        using \<open>\<omega> \<in> f x\<close> by blast
      moreover have "Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)"
        using \<open>snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl\<close> \<open>x \<in> SA\<close> r_get_rem by fastforce

      moreover have "Some (set_value \<gamma> hl v) = set_value (get_ptr x) hl v \<oplus> snd (get_rem x)"
      proof (rule frame_preserving_writing_orig)
        show "Some \<gamma> = get_ptr x \<oplus> snd (get_rem x)"
          by (metis calculation(2) commutative plus_prodE snd_conv)
        show "sep_algebra_class.stable (snd (get_rem x))"
          using \<open>x \<in> SA\<close> r_get_rem stable_snd by blast
        show "has_write_perm_only (get_ptr x) hl"
          using \<open>snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl\<close> \<open>x \<in> SA\<close> r_ptr by fastforce
      qed
      then have "Some (\<sigma>, set_value \<gamma> hl v) = (\<sigma>, set_value (get_ptr x) hl v) \<oplus> get_rem x"
        by (metis (no_types, lifting) calculation(2) commutative fst_eqD plus_prodE plus_prodI snd_eqD)

      moreover have "points_to_value r e (\<sigma>, set_value (get_ptr x) hl v)"
      proof (rule points_to_valueI)
        show "r (\<sigma>, set_value (get_ptr x) hl v) = Some hl"
          by (metis True \<open>snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl\<close> depends_on_ag_store_only_def)
        show "e (\<sigma>, set_value (get_ptr x) hl v) = Some v"
          by (metis True \<open>snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl\<close> depends_on_ag_store_only_def)
        show "has_write_perm_only (get_state (\<sigma>, set_value (get_ptr x) hl v)) hl"
          sorry (* TODO: Add axiom, maybe pure larger (related)... *)

        show "has_value (get_state (\<sigma>, set_value (get_ptr x) hl v)) hl v"
          by (smt (verit, del_insts) \<open>snd x = (\<sigma>, \<gamma>) \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl\<close> \<open>x \<in> SA\<close> get_state_def option.sel r_ptr set_value_then_has_value snd_conv)
      qed

      moreover have "stable (get_rem x) \<and> stable (\<sigma>, get_ptr x)"
        by (smt (verit) \<open>x \<in> SA\<close> r_get_rem r_ptr snd_conv stable_snd)

      moreover have "Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) (get_rem x)"
        by (simp add: \<open>x \<in> SA\<close> Stabilize_def)


      ultimately show "(Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) \<otimes> points_to_value r e) \<omega>"
        by (simp add: commutative sat_starI)
    next
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "(Stabilize_typed \<Delta> ((stabilize \<circ> get_rem) ` SA) \<otimes> points_to_value r e) \<omega>"
      then obtain a ptr where "Some \<omega> = a \<oplus> ptr" "stabilize a \<in> ((stabilize \<circ> get_rem) ` SA)" "points_to_value r e ptr"
        using Stabilize_def astar_def by fastforce
      then obtain x where "x \<in> SA" "stabilize a = stabilize (get_rem x)"
        by force
      then obtain \<sigma> \<gamma> hl v where rr: "snd x = (\<sigma>, \<gamma>)  \<and> f x = {(\<sigma>, set_value \<gamma> hl v)} \<and>
   r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> get_ptr x \<and> has_write_perm_only (get_ptr x) hl \<and> sep_algebra_class.stable (get_ptr x)"
        using r_ptr by presburger
      moreover obtain v' hl' where "r ptr = Some hl' \<and> e ptr = Some v' \<and> has_write_perm_only (snd ptr) hl' \<and> has_value (snd ptr) hl' v'"
        by (metis \<open>points_to_value r e ptr\<close> get_state_def points_to_value_def)
      moreover have "fst ptr = \<sigma>"
        sorry
(*
        by (metis (mono_tags, opaque_lifting) agreement.exhaust_sel fst_conv get_store_def get_trace_def greater_charact neutral_smallest prod.exhaust_sel)
*)
      ultimately have "hl = hl' \<and> v = v'"
        by (metis (no_types, lifting) True depends_on_ag_store_only_def option.sel prod.exhaust_sel)
      moreover have "Some (\<sigma>, \<gamma>) = (\<sigma>, get_ptr x) \<oplus> get_rem x"
        by (smt (verit, best) \<open>x \<in> SA\<close> commutative fst_conv r_get_rem rr)
      then have "Some (\<sigma>, set_value \<gamma> hl v) = (\<sigma>, set_value (get_ptr x) hl v) \<oplus> get_rem x"
      proof -
        have "Some (set_value \<gamma> hl v) = set_value (get_ptr x) hl v \<oplus> snd (get_rem x)"
          by (smt (verit, ccfv_threshold) \<open>Some (\<sigma>, \<gamma>) = (\<sigma>, get_ptr x) \<oplus> get_rem x\<close> \<open>x \<in> SA\<close> frame_preserving_writing_orig plus_prodE r_get_rem rr snd_conv stable_snd)
        then show ?thesis
          by (metis \<open>Some (\<sigma>, \<gamma>) = (\<sigma>, get_ptr x) \<oplus> get_rem x\<close> fst_eqD plus_prodE plus_prodIAlt snd_eqD)
      qed
      moreover have "stabilize ptr = stabilize (\<sigma>, set_value (get_ptr x) hl v)"
      proof (rule points_to_value_same)
        show "wf_exp r"          
          using FieldAssign.prems(2) by auto
        show "r ptr = r (\<sigma>, set_value (get_ptr x) hl v)"
          by (metis True \<open>r ptr = Some hl' \<and> e ptr = Some v' \<and> has_write_perm_only (snd ptr) hl' \<and> has_value (snd ptr) hl' v'\<close> calculation(1) depends_on_ag_store_only_def rr)
        show "e ptr = e (\<sigma>, set_value (get_ptr x) hl v)"
          by (metis True \<open>r ptr = Some hl' \<and> e ptr = Some v' \<and> has_write_perm_only (snd ptr) hl' \<and> has_value (snd ptr) hl' v'\<close> calculation(1) depends_on_ag_store_only_def rr)
        show "points_to_value r e ptr"
          by (simp add: \<open>points_to_value r e ptr\<close>)

        show "points_to_value r e (\<sigma>, set_value (get_ptr x) hl v)"
        proof (rule points_to_valueI)
          show "r (\<sigma>, set_value (get_ptr x) hl v) = Some hl"
            using \<open>r ptr = Some hl' \<and> e ptr = Some v' \<and> has_write_perm_only (snd ptr) hl' \<and> has_value (snd ptr) hl' v'\<close> \<open>r ptr = r (\<sigma>, set_value (get_ptr x) hl v)\<close> calculation(1) by presburger
          show "e (\<sigma>, set_value (get_ptr x) hl v) = Some v"
            using \<open>e ptr = e (\<sigma>, set_value (get_ptr x) hl v)\<close> \<open>r ptr = Some hl' \<and> e ptr = Some v' \<and> has_write_perm_only (snd ptr) hl' \<and> has_value (snd ptr) hl' v'\<close> calculation(1) by auto
          show "has_write_perm_only (get_state (\<sigma>, set_value (get_ptr x) hl v)) hl"
            sorry (* TODO: Add axiom *)
          show "has_value (get_state (\<sigma>, set_value (get_ptr x) hl v)) hl v"
            by (simp add: get_state_def rr set_value_then_has_value)
        qed

        show "fst ptr = fst (\<sigma>, set_value (get_ptr x) hl v)"
          by (simp add: \<open>fst ptr = \<sigma>\<close>)
      qed

      ultimately have "stabilize \<omega> = stabilize (\<sigma>, set_value \<gamma> hl v)"
        by (metis (mono_tags, lifting) \<open>Some \<omega> = a \<oplus> ptr\<close> \<open>stabilize a = stabilize (get_rem x)\<close> commutative option.sel stabilize_sum)
      moreover have "stable (\<sigma>, set_value \<gamma> hl v)"
        sorry
(* TODO: Add axiom *)



      then show "Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<omega>"
        by (metis (no_types, lifting) UN_I \<open>x \<in> SA\<close> already_stable Stabilize_def calculation rr singletonI)
    qed
   
    
    ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] FieldAssign r e [Stabilize_typed \<Delta> (\<Union> (f ` SA))]"
      by presburger



  qed
next
  case (Havoc x)
    (*
wf_set \<Delta> (snd ` SA)
\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>ty \<sigma> \<gamma>. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<and> \<Delta> x = Some ty)


\<exists>A B.  \<Delta> \<turnstile> [A] Havoc x [B] \<and>
          Set.filter sep_algebra_class.stable (\<langle>A\<rangle>) = snd ` SA \<and> Set.filter sep_algebra_class.stable (\<langle>B\<rangle>) = \<Union> (f ` SA)

*)
  moreover obtain ty where "variables \<Delta> x = Some ty"
    using calculation(2) by auto
  (* ultimately have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>\<sigma> \<tau> \<gamma>. snd \<omega> = ((\<sigma>, \<gamma>) \<and> f \<omega> = {((upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty})" *)
    (* by fastforce *)
  let ?A = "Stabilize_typed \<Delta> (snd ` SA)"
  have "\<Delta> \<turnstile> [?A] Havoc x [exists_assert \<Delta> x ?A]"
    by (simp add: RuleHavoc Stabilize_self_framing)
  moreover have "Stabilize_typed \<Delta> (\<Union> (f ` SA)) = exists_assert \<Delta> x ?A"
  proof (rule self_framing_ext)
    show "self_framing (Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
      by (simp add: Stabilize_self_framing)
    show "self_framing (exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)))"
      using calculation proofs_are_self_framing by presburger
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<omega>"
    then obtain xx where "xx \<in> SA" "\<omega> \<in> f xx"
      using already_stable Stabilize_def by fastforce
    moreover have "wf_state \<Delta> (snd xx)"
      by (meson Havoc.prems(3) calculation(1) image_iff wf_set_def)
    then obtain v0 where "v0 \<in> ty" "get_store (snd xx) x = Some v0"
      by (metis (mono_tags, lifting) \<open>variables \<Delta> x = Some ty\<close> domD domI typed_store_def wf_state_def)
    (* moreover obtain \<sigma> \<tau> \<gamma> where "snd xx = ((\<sigma>, \<gamma>) \<and> f xx = {((upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty}" *)
      (* using calculation(1) r by presburger *)
    (* then obtain v where "v \<in> ty" "((upd_ag_partial_map \<sigma> x (Some v), \<gamma>) = \<omega>" *)
      (* using calculation(2) by auto *)
    (* then have "Stabilize_typed \<Delta> (snd ` SA) ((upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v0), \<gamma>)" *)
      (*
      by (metis (no_types, lifting) \<open>snd xx = ((\<sigma>, \<gamma>) \<and> f xx = {((upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty}\<close> already_stable asm0(1) Stabilize_def calculation(1) calculation(4) fst_conv image_eqI snd_conv stable_snd upd_ag_partial_map_invo upd_ag_partial_map_refl)
*)


    show "exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)) \<omega>"
    proof (rule exists_assertI)
      show "variables \<Delta> x = Some ty"
        by (simp add: \<open>variables \<Delta> x = Some ty\<close>)
      show "Stabilize_typed \<Delta> (snd ` SA) (Ag ((get_store \<omega>)(x \<mapsto> v0)), Ag (get_trace \<omega>)), snd \<omega>)"
        sorry
        (* by (metis \<open>((upd_ag_partial_map \<sigma> x (Some v), \<gamma>) = \<omega>\<close> \<open>Stabilize_typed \<Delta> (snd ` SA) ((upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v0), \<gamma>)\<close> agreement.collapse fst_eqD get_store_def get_trace_def upd_ag_partial_map_def sndI) *)
      show "v0 \<in> ty"
        sorry
        (* by (simp add: calculation(3)) *)
      show "get_store \<omega> x = Some v0"
        sorry
        (* by (metis calculation(4) full_add_defined option.distinct(1) u_neutral) *)
      show "v0 \<in> ty"
        sorry
        (* by (simp add: calculation(3)) *)
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)) \<omega>"

    thm exists_assert_def[of \<Delta> x "Stabilize_typed \<Delta> (snd ` SA)" \<omega>]
    then obtain v v0 where "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> Stabilize_typed \<Delta> (snd ` SA) (Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)"
      using exists_assert_def[of \<Delta> x "Stabilize_typed \<Delta> (snd ` SA)" \<omega>] \<open>variables \<Delta> x = Some ty\<close> by auto
    then have "(Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>) \<in> snd ` SA"
      by (metis already_stable asm0(1) Stabilize_def get_state_def snd_conv stable_snd)
    then obtain xx where "xx \<in> SA" "snd xx = (Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)"
      by force
(*
    then obtain \<sigma> \<gamma> where "snd xx = (\<sigma>, \<gamma>)" "f xx = {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty}"
      using r by meson
*)
(*
    moreover have "snd \<omega> = get_state \<omega>"
      using \<open>snd xx = (upd_ag_partial_map (fst \<omega>) x (Some v), snd \<omega>)\<close> calculation(1) by fastforce
*)
    then have "\<omega> \<in> f xx"
      sorry
      (* by (smt (z3) \<open>v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> Stabilize_typed \<Delta> (snd ` SA) (Ag (get_store \<omega>(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)\<close> agreement.exhaust_sel agreement.sel fst_conv fun_upd_triv fun_upd_upd get_state_def get_store_def get_trace_def mem_Collect_eq prod.collapse r snd_conv upd_ag_partial_map_def) *)
    then show "Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<omega>"
      by (metis (no_types, opaque_lifting) UN_iff \<open>xx \<in> SA\<close> already_stable asm0(1) Stabilize_def)
  qed
  ultimately show "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] Havoc x [Stabilize_typed \<Delta> (\<Union> (f ` SA))]"
    by simp
next
  case (Scope x1a x2a C)
  then show ?case sorry
next
  case (Assume A)
  then show ?case sorry
next
  case (Label l)
  then show ?case sorry
qed
*)



(*

lemma has_write_perm_mono:
  assumes "a \<succeq> b"
      and "has_write_perm b hl"
    shows "has_write_perm a hl"
  using assms(1) assms(2) has_write_perm_def succ_trans by blast

lemma frame_preserving_writing:
  assumes "Some x = a \<oplus> b"
      and "stable a"
      and "stable b"
      and "has_write_perm a hl"
    shows "Some (set_value x hl v) = set_value a hl v \<oplus> b"
proof -
  obtain r1 r2 where "Some a = r1 \<oplus> r2" "has_write_perm_only r1 hl"
    using assms(4) has_write_perm_def minus_exists by blast
  then obtain br where "Some br = stabilize r2 \<oplus> b"
    by (metis assms(1) asso2 defined_def max_projection_prop_def max_projection_prop_stable_stabilize option.exhaust_sel smaller_compatible)
  then have "Some x = r1 \<oplus> br"
    by (metis \<open>Some a = r1 \<oplus> r2\<close> assms(1) assms(2) asso1 commutative stabilize_sum_result_stable)
  moreover have "stable br"
    using \<open>Some br = stabilize r2 \<oplus> b\<close> assms(3) stabilize_is_stable stable_sum by blast
  then have "Some (set_value x hl v) = set_value r1 hl v \<oplus> br"
    by (meson \<open>has_write_perm_only r1 hl\<close> calculation frame_preserving_writing_orig)
  then show "Some (set_value x hl v) = set_value a hl v \<oplus> b"    
    by (smt (verit, ccfv_threshold) \<open>Some a = r1 \<oplus> r2\<close> \<open>Some br = stabilize r2 \<oplus> b\<close> \<open>has_write_perm_only r1 hl\<close> assms(2) asso1 commutative frame_preserving_writing_orig stabilize_is_stable stabilize_sum_result_stable)
qed
*)

(*
lemma in_inh:
  assumes "A \<omega>"
    shows "\<omega> \<in> \<langle>A\<rangle>"
  by (simp add: assms(1) inh_def)
*)

lemma ag_store_ext:
  assumes "\<And>x. the_ag \<sigma>1 x = the_ag \<sigma>2 x"
  shows "\<sigma>1 = \<sigma>2"
proof (rule agreement.expand)
  show "the_ag \<sigma>1 = the_ag \<sigma>2" using ext assms by blast
qed

lemma rel_stable_assertionI:
  assumes "\<And>x a. \<omega> ## a \<Longrightarrow> pure_larger x (stabilize a) \<Longrightarrow> x \<succeq> |\<omega>| \<Longrightarrow> (a \<in> A \<longleftrightarrow> x \<in> A)"
  shows "rel_stable_assertion \<omega> A"
  by (simp add: assms rel_stable_assertion_def)



(*
lemma stable_assertion_equiv:
  "self_framing A \<longleftrightarrow> rel_stable_assertion u A" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis (no_types, lifting) pure_larger_stabilize_same rel_stable_assertionI self_framing_def)
  show "rel_stable_assertion u A \<Longrightarrow> self_framing A"
    sorry
(*
    by (smt (verit, del_insts) asso1 commutative core_is_smaller defined_def greater_equiv option.discI pure_larger_stabilize pure_larger_stabilize_same rel_stable_assertion_def self_framing_def stabilize_def u_neutral)
*)
qed
*)


section \<open>Assertions\<close>

subsection \<open>General concepts\<close>

(*
definition self_framing :: "('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "self_framing A \<longleftrightarrow> (\<forall>\<omega>. WdInhale A \<omega> \<and> (A \<omega> \<longleftrightarrow> A (stabilize \<omega>)))"
*)


lemma framed_byI:
  assumes "\<And>\<omega> b x. \<omega> \<in> A \<Longrightarrow> stable \<omega> \<Longrightarrow> b ## \<omega> \<Longrightarrow> pure_larger x (stabilize b) \<Longrightarrow> x \<succeq> |\<omega>| \<Longrightarrow> (b \<in> B \<longleftrightarrow> x \<in> B)"
  shows "framed_by A B"
  by (simp add: assms defined_comm framed_by_def rel_stable_assertion_def)



lemma wf_exp_bisE:
  assumes "wf_exp e"
  shows "e a = e |a|"
  by (meson assms wf_exp_def)





lemma wf_exp_altE:
  assumes "wf_exp e"
      and "a \<succeq> b \<or> b \<succeq> a"
      and "e a = Some v1"
      and "e b = Some v2"
    shows "v1 = v2"
  using assms(1) assms(2) assms(3) assms(4) wf_expE by fastforce


lemma wf_exp_coreE:
  assumes "wf_exp e"
      and "|a| = |b|"
    shows "e a = e b"
  by (metis assms(1) assms(2) wf_exp_def)


(*
lemma equivI:
  assumes "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> \<omega> \<in> B"
      and "\<And>\<omega>. \<omega> \<in> B \<Longrightarrow> \<omega> \<in> A"
    shows "equiv A B"
  using assms
  by (simp add: local.equiv_def subsetI subset_antisym)

*)


lemma entails_self_framingI:
  assumes "\<And>\<omega>. stable \<omega> \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> \<omega> \<in> B"
      and "self_framing A"
      and "self_framing B"
    shows "entails A B"
  by (metis assms(1) assms(2) assms(3) entailsI self_framing_def stabilize_is_stable)





section \<open>Free variables\<close>

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
  using equal_on_set_def by fastforce

(*
lemma overapprox_fvI:
  assumes "\<And>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed_store \<Delta> \<sigma>1 \<Longrightarrow> typed_store \<Delta> \<sigma>2 \<Longrightarrow> equal_on_set S \<sigma>1 \<sigma>2 \<Longrightarrow> A (Ag \<sigma>1, \<gamma>) \<Longrightarrow> A (Ag \<sigma>2, \<gamma>)"
  shows "overapprox_fv \<Delta> A S"
  using assms equal_on_set_symmetric overapprox_fv_def by blast
*)

lemma intermediate_equal_set:
  assumes "equal_on_set (S1 \<inter> S2) \<sigma>1 \<sigma>2"
      and "typed_store \<Delta> \<sigma>1"
      and "typed_store \<Delta> \<sigma>2"
  shows "\<exists>\<sigma>3. typed_store \<Delta> \<sigma>3 \<and> equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2"
proof -
  let ?\<sigma>3 = "(\<lambda>x. if x \<in> S1 then \<sigma>1 x else \<sigma>2 x)"
  have "equal_on_set S1 \<sigma>1 ?\<sigma>3"
    by (simp add: equal_on_set_def)
  moreover have "equal_on_set S2 ?\<sigma>3 \<sigma>2" (* Needs a case split on x *)
    by (smt (verit) IntI agreement.sel assms equal_on_set_def)
  moreover have "typed_store \<Delta> ?\<sigma>3"
  proof (rule typed_storeI)
    show "dom (variables \<Delta>) = dom (\<lambda>x. if x \<in> S1 then \<sigma>1 x else \<sigma>2 x)" (is "?A = ?B")
    proof
      show "?A \<subseteq> ?B"
        by (smt (verit, best) agreement.sel assms(2) assms(3) domIff subsetI typed_store_def)
      show "?B \<subseteq> ?A"
        by (smt (verit) agreement.sel assms(2) assms(3) domIff subsetI typed_store_def)
    qed
    show "\<And>x v ty. (\<lambda>x. if x \<in> S1 then \<sigma>1 x else \<sigma>2 x) x = Some v \<Longrightarrow> variables \<Delta> x = Some ty \<Longrightarrow> v \<in> ty"
      by (smt (verit, best) agreement.sel assms(2) assms(3) typed_store_def)
  qed
  ultimately show ?thesis by blast
qed


(*
lemma stable_by_intersection_overapprox_fv:
  assumes "overapprox_fv \<Delta> A S1"
      and "overapprox_fv \<Delta> A S2"
    shows "overapprox_fv \<Delta> A (S1 \<inter> S2)"
proof (rule overapprox_fvI)
  fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
  assume asm0: "equal_on_set (S1 \<inter> S2) \<sigma>1 \<sigma>2" "A (Ag \<sigma>1, \<gamma>)" "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2"
  then obtain \<sigma>3 where "equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2" "typed_store \<Delta> \<sigma>3"
    using intermediate_equal_set by blast
  then show "A (Ag \<sigma>2, \<gamma>)"
    by (meson asm0(2) asm0(3) asm0(4) assms(1) assms(2) overapprox_fv_def) (* long *)
qed

lemma overapprox_fv_dom:
  "overapprox_fv \<Delta> A (dom (variables \<Delta>))"
proof (rule overapprox_fvI)
  fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
  assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (dom (variables \<Delta>)) \<sigma>1 \<sigma>2" "A (Ag \<sigma>1, \<gamma>)"
  have "\<sigma>1 = \<sigma>2"
  proof (rule ext)
    fix x show "\<sigma>1 x = \<sigma>2 x"
      apply (cases "x \<in> dom (variables \<Delta>)")      
      using asm0(3) equal_on_set_def apply auto[1]
      by (metis asm0(1) asm0(2) domIff typed_store_def)
  qed
  then show "A (Ag \<sigma>2, \<gamma>)"
    using agreement.expand asm0(4) by blast
qed
*)

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


(*
text \<open>Works only if (dom \<Delta>) is finite.\<close>
lemma counter_ex1:
  assumes "dom \<Delta> = UNIV"
      and "(v :: 'v) \<noteq> v'"
      and "\<And>x. \<Delta> x = Some {v, v'}"
(* can be generalized to an infinite set on which we have at least two vars *)
  shows "\<exists>A. \<not> overapprox_fv \<Delta> A (free_vars \<Delta> A)"
proof -
  define A :: "('v, 'a) abs_state assertion" where "A = (\<lambda>\<omega>. (\<exists>S. \<not> finite S \<and> (\<forall>x \<in> S. get_store \<omega> x = Some v)))"

  have "\<And>x. overapprox_fv \<Delta> A (UNIV - {x})"
  proof -
    fix x show "overapprox_fv \<Delta> A (UNIV - {x})"
    proof (rule overapprox_fvI)
      fix \<sigma>1 \<sigma>2 \<gamma>
      assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (UNIV - {x}) \<sigma>1 \<sigma>2" "A (\<sigma>1, \<gamma>)"
      then obtain S where "\<not> finite S \<and> (\<forall>x \<in> S. the_ag \<sigma>1 x = Some v)"
        sorry
(*
        by (metis A_def fst_conv get_store_def)
*)
      let ?S = "S - {x}"
      have "\<not> finite ?S \<and> (\<forall>x \<in> ?S. the_ag \<sigma>1 x = Some v)"
        by (simp add: \<open>infinite S \<and> (\<forall>x\<in>S. the_ag \<sigma>1 x = Some v)\<close>)
      then have "\<And>x. x \<in> ?S \<Longrightarrow> the_ag \<sigma>2 x = Some v"
        by (metis DiffD2 DiffI asm0(3) equal_on_set_def iso_tuple_UNIV_I)
      then show "A (\<sigma>2, \<gamma>)"
        sorry 
(*
        by (metis A_def \<open>infinite (S - {x}) \<and> (\<forall>x\<in>S - {x}. the_ag \<sigma>1 x = Some v)\<close> fst_eqD get_store_def)
*)
    qed
  qed
  moreover have "(\<Inter>(x :: var). (UNIV - {x})) \<subseteq> {}"
  proof
    fix y assume "y \<in> (\<Inter>(x :: var). (UNIV - {x}))"
    then have "y \<in> UNIV - {y}"
      by blast
    then show "y \<in> {}" by blast
  qed
  then have "free_vars \<Delta> A \<subseteq> {}"
    using calculation free_vars_def by fastforce
  moreover have "\<not> overapprox_fv \<Delta> A {}"
  proof -
    obtain \<gamma> :: 'a where "True" by simp
    let ?\<omega> = "(Ag (\<lambda>x. Some v), \<gamma>)"
    let ?\<omega>' = "(Ag (\<lambda>x. Some v'), \<gamma>)"
    have "A ?\<omega>" sorry
(*
      by (metis A_def agreement.sel fst_conv get_store_def infinite_UNIV_nat)
*)
    moreover have "\<not> A ?\<omega>'"
      sorry
(*
      by (metis A_def agreement.sel assms(2) finite_nat_set_iff_bounded_le fst_conv get_store_def option.sel)
*)
    moreover have "equal_on_set {} (Ag (\<lambda>x. Some v)) (Ag (\<lambda>x. Some v'))"
      using equal_on_set_def by auto
    moreover have "typed_store \<Delta> (Ag (\<lambda>x. Some v)) \<and> typed_store \<Delta> (Ag (\<lambda>x. Some v'))"
      using assms(3) typed_store_def by auto
    ultimately show ?thesis
      using overapprox_fv_def by blast
  qed
  ultimately show ?thesis
    by (metis bot.extremum_unique)
qed

lemma counter_ex2:
  assumes "\<not> finite S"
      and "\<And>x. x \<in> S \<Longrightarrow> (\<exists>V. \<Delta> x = Some V \<and> at_least_two_elems V)"
      and "\<And>x V. \<Delta> x = Some V \<Longrightarrow> V \<noteq> {}"
  shows "\<exists>A. \<not> overapprox_fv \<Delta> A (free_vars \<Delta> A)"
proof -
  define f1 where "f1 = (\<lambda>x. SOME v. (\<exists>V. \<Delta> x = Some V \<and> v \<in> V))"
  define f2 where "f2 = (\<lambda>x. SOME v. (\<exists>V. \<Delta> x = Some V \<and> v \<in> V \<and> v \<noteq> f1 x))"

  have rr: "\<And>x V. \<Delta> x = Some V \<Longrightarrow> f1 x \<in> V"
  proof -
    fix x V assume "\<Delta> x = Some V"
    then have "\<exists>v. (\<exists>V. \<Delta> x = Some V \<and> v \<in> V)"
      using assms(3) by auto
    then show "f1 x \<in> V" unfolding f1_def 
      using someI_ex[of "\<lambda>v. \<exists>V. \<Delta> x = Some V \<and> v \<in> V"]
      by (simp add: \<open>\<Delta> x = Some V\<close>)
  qed

  have r: "\<And>x. x \<in> S \<Longrightarrow> (\<exists>V. \<Delta> x = Some V \<and> f1 x \<in> V \<and> f2 x \<in> V \<and> f1 x \<noteq> f2 x)"
  proof -
    fix x assume asm0: "x \<in> S"
    then obtain V where "\<Delta> x = Some V \<and> at_least_two_elems V"
      using assms(2) by blast
    then have "f1 x \<in> V" unfolding f1_def 
      using someI_ex[of "\<lambda>v. \<exists>V. \<Delta> x = Some V \<and> v \<in> V"] at_least_two_elems
      by force
    then obtain v' where "v' \<in> V" "v' \<noteq> f1 x"
      by (metis \<open>\<Delta> x = Some V \<and> at_least_two_elems V\<close> at_least_two_elems)
    then have "\<Delta> x = Some V \<and> f2 x \<in> V \<and> f2 x \<noteq> f1 x"
      unfolding f2_def using someI_ex[of "\<lambda>v. \<exists>V. \<Delta> x = Some V \<and> v \<in> V \<and> v \<noteq> f1 x"]
      using \<open>\<Delta> x = Some V \<and> at_least_two_elems V\<close> by auto
    then show "\<exists>V. \<Delta> x = Some V \<and> f1 x \<in> V \<and> f2 x \<in> V \<and> f1 x \<noteq> f2 x"
      using \<open>f1 x \<in> V\<close> by fastforce
  qed

  define A :: "('v, 'a) abs_state assertion" where "A = (\<lambda>\<omega>. (\<exists>S'. \<not> finite S' \<and> S' \<subseteq> S \<and> (\<forall>x \<in> S'. get_store \<omega> x = Some (f1 x))))"

  have "\<And>x. overapprox_fv \<Delta> A (UNIV - {x})"
  proof -
    fix x show "overapprox_fv \<Delta> A (UNIV - {x})"
    proof (rule overapprox_fvI)
      fix \<sigma>1 \<sigma>2 \<gamma>
      assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (UNIV - {x}) \<sigma>1 \<sigma>2" "A (\<sigma>1, \<gamma>)"
      then obtain S' where "\<not> finite S' \<and> S' \<subseteq> S \<and> (\<forall>x \<in> S'. the_ag \<sigma>1 x = Some (f1 x))"
        sorry
(*
        by (metis A_def fst_conv get_store_def)
*)
      let ?S = "S' - {x}"
      have "\<not> finite ?S \<and> ?S \<subseteq> S \<and> (\<forall>x \<in> ?S. the_ag \<sigma>1 x = Some (f1 x))"
        using \<open>infinite S' \<and> S' \<subseteq> S \<and> (\<forall>x\<in>S'. the_ag \<sigma>1 x = Some (f1 x))\<close> by auto
      then have "\<And>x. x \<in> ?S \<Longrightarrow> the_ag \<sigma>2 x = Some (f1 x)"
        by (metis DiffD2 DiffI asm0(3) equal_on_set_def iso_tuple_UNIV_I)
      then show "A (\<sigma>2, \<gamma>)" sorry
(*
        by (metis A_def \<open>infinite (S' - {x}) \<and> S' - {x} \<subseteq> S \<and> (\<forall>x\<in>S' - {x}. the_ag \<sigma>1 x = Some (f1 x))\<close> fst_conv get_store_def)
*)
    qed
  qed
  moreover have "(\<Inter>(x :: var). (UNIV - {x})) \<subseteq> {}"
  proof
    fix y assume "y \<in> (\<Inter>(x :: var). (UNIV - {x}))"
    then have "y \<in> UNIV - {y}"
      by blast
    then show "y \<in> {}" by blast
  qed
  then have "free_vars \<Delta> A \<subseteq> {}"
    using calculation free_vars_def by fastforce
  moreover have "S \<subseteq> dom \<Delta>"
    by (meson assms(2) domI subsetI)
  moreover have "\<not> overapprox_fv \<Delta> A {}"
  proof -
    obtain \<gamma> :: 'a where "True" by simp

    let ?\<omega> = "(Ag (\<lambda>x. if x \<in> dom \<Delta> then Some (f1 x) else None), \<gamma>)"
    let ?\<omega>' = "(Ag (\<lambda>x. if x \<in> S then Some (f2 x) else if x \<in> dom \<Delta> then Some (f1 x) else None), \<gamma>)"
    have "A ?\<omega>"
    proof -
      have "\<not> finite S \<and> S \<subseteq> S \<and> (\<forall>x \<in> S. get_store ?\<omega> x = Some (f1 x))"
        sorry
(*
        by (smt (verit, ccfv_threshold) agreement.sel assms(1) calculation(3) dual_order.refl fst_conv get_store_def in_mono)
*)
      then show ?thesis
        using A_def by blast
    qed
    moreover have "\<not> A ?\<omega>'"
    proof (rule ccontr)
      assume "\<not> \<not> A ?\<omega>'"
      then obtain S' where "\<not> finite S' \<and> S' \<subseteq> S \<and> (\<forall>x \<in> S'. get_store ?\<omega>' x = Some (f1 x))"
        using A_def by blast
      moreover have "\<And>x. x \<in> S' \<Longrightarrow> get_store ?\<omega>' x = Some (f2 x)"
        sorry
(*
        by (smt (verit, best) agreement.sel calculation fst_conv get_store_def in_mono)
*)
      ultimately show False
        by (metis (no_types, lifting) bot.extremum_uniqueI finite.emptyI option.inject r subset_iff)
    qed

    moreover have "equal_on_set {} (Ag (\<lambda>x. if x \<in> dom \<Delta> then Some (f1 x) else None))
  (Ag (\<lambda>x. if x \<in> S then Some (f2 x) else if x \<in> dom \<Delta> then Some (f1 x) else None))"
      using equal_on_set_def by auto
    moreover have "typed_store \<Delta> (Ag (\<lambda>x. if x \<in> dom \<Delta> then Some (f1 x) else None))"
    proof (rule typed_storeI)
      show "dom \<Delta> = dom (the_ag (Ag (\<lambda>x. if x \<in> dom \<Delta> then Some (f1 x) else None)))"
        by (smt (verit, best) agreement.sel domIff option.distinct(1) subset_antisym subset_eq)
      fix x v ty show "the_ag (Ag (\<lambda>x. if x \<in> dom \<Delta> then Some (f1 x) else None)) x = Some v \<Longrightarrow> \<Delta> x = Some ty \<Longrightarrow> v \<in> ty"
        by (metis (mono_tags, lifting) agreement.sel domI option.sel rr)
    qed
    moreover have "typed_store \<Delta> (Ag (\<lambda>x. if x \<in> S then Some (f2 x) else if x \<in> dom \<Delta> then Some (f1 x) else None))"
    proof (rule typed_storeI)
      show "dom \<Delta> = dom (the_ag (Ag (\<lambda>x. if x \<in> S then Some (f2 x) else if x \<in> dom \<Delta> then Some (f1 x) else None)))"
        by (smt (verit, ccfv_SIG) agreement.sel domIff option.distinct(1) r subset_antisym subset_eq)
      fix x v ty
      show "the_ag (Ag (\<lambda>x. if x \<in> S then Some (f2 x) else if x \<in> dom \<Delta> then Some (f1 x) else None)) x = Some v \<Longrightarrow> \<Delta> x = Some ty \<Longrightarrow> v \<in> ty"
        by (smt (verit) agreement.sel domI option.sel r rr)
    qed
    ultimately show ?thesis
      using overapprox_fv_def by blast
  qed
  ultimately show ?thesis
    by (metis bot.extremum_unique)
qed
*)

lemma no_typable_ag_store:
  assumes "variables \<Delta> x = Some {}"
  shows "\<not> typed_store \<Delta> \<sigma>"
  by (metis assms domD domI empty_iff typed_store_def)

(*
lemma domain_must_be_typable:
  assumes "variables \<Delta> x = Some {}"
  shows "free_vars \<Delta> A = {} \<and> overapprox_fv \<Delta> A {}"
  by (metis Inf_lower assms bot.extremum_uniqueI free_vars_def image_ident mem_Collect_eq no_typable_ag_store overapprox_fvI)
*)

lemma free_vars_upper_bound:
  assumes "overapprox_fv \<Delta> A S"
  shows "free_vars \<Delta> A \<subseteq> S"
  by (simp add: Inf_lower assms free_vars_def)


(*
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
    by (metis (mono_tags, lifting) Inf_greatest free_vars_def free_vars_upper_bound image_ident mem_Collect_eq subset_antisym)
qed

lemma finite_more_than_one_choice_OK:
  assumes "finite { x |x V. variables \<Delta> x = Some V \<and> at_least_two_elems V}"
  shows "overapprox_fv \<Delta> A (free_vars \<Delta> A)"
proof -
  let ?S = "{ x |x V. variables \<Delta> x = Some V \<and> at_least_two_elems V}"
  have "overapprox_fv \<Delta> A ?S"
  proof (rule overapprox_fvI)
    fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
    assume asm: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set ?S \<sigma>1 \<sigma>2" "A (Ag \<sigma>1, \<gamma>)"
    have "\<sigma>1 = \<sigma>2"
    proof (rule ext)
      fix x show "\<sigma>1 x = \<sigma>2 x"
      proof (cases "x \<in> ?S")
        case True
        then show ?thesis using asm(3) equal_on_set_def by auto
      next
        case False
        then have "x \<notin> ?S"
          by blast
        then show ?thesis
        proof (cases "x \<in> dom (variables \<Delta>)")
          case True
          then obtain V where "variables \<Delta> x = Some V" "\<not> at_least_two_elems V"
            using False by blast
          moreover obtain a b where "\<sigma>1 x = Some a" "\<sigma>2 x = Some b"
            by (metis True asm(1) asm(2) domIff not_None_eq typed_store_def)
          ultimately show ?thesis
            by (metis asm(1) asm(2) at_least_two_elems typed_store_def)
        next
          case False
          then show ?thesis
            by (metis asm(1) asm(2) domIff typed_store_def)
        qed
      qed
    qed
    then show "A (Ag \<sigma>2, \<gamma>)"
      using agreement.expand asm(4) by auto
  qed
  then show ?thesis
    using assms free_vars_exists_finite by blast
qed

lemma finite_dom_fv_works:
  assumes "finite (dom (variables \<Delta>))"
  shows "overapprox_fv \<Delta> A (free_vars \<Delta> A)"
  using assms free_vars_exists_finite overapprox_fv_dom by auto
*)

lemma exists_minimum_then_its_free_vars:
  assumes "overapprox_fv \<Delta> A S"
      and "\<And>S'. overapprox_fv \<Delta> A S' \<Longrightarrow> S \<subseteq> S'"
    shows "S = free_vars \<Delta> A"
  using assms(1) assms(2) free_vars_def by auto

(*
theorem free_vars_works_iff:
  "finite { x |x V. \<Delta> x = Some V \<and> at_least_two_elems V} \<or> (\<exists>x. \<Delta> x = Some {})
\<longleftrightarrow> (\<forall>A. \<exists>S. overapprox_fv \<Delta> A S \<and> (\<forall>S'. overapprox_fv \<Delta> A S' \<longrightarrow> S \<subseteq> S'))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A then show ?B
  proof (cases "\<exists>x. \<Delta> x = Some {}")
    case True
    then show ?thesis
      using domain_must_be_typable by blast
  next
    case False
    then have "finite { x |x V. \<Delta> x = Some V \<and> at_least_two_elems V}" using \<open>?A\<close> by simp
    then show ?thesis using finite_more_than_one_choice_OK free_vars_upper_bound by blast
  qed
next
  assume asm0: ?B
  show ?A
  proof (rule ccontr)
    assume asm1: "\<not> (finite { x |x V. \<Delta> x = Some V \<and> at_least_two_elems V} \<or> (\<exists>x. \<Delta> x = Some {}))"
    have "\<exists>A. \<not> overapprox_fv \<Delta> A (free_vars \<Delta> A)"
    proof (rule counter_ex2)
      show "\<And>x. x \<in> { x |x V. \<Delta> x = Some V \<and> at_least_two_elems V} \<Longrightarrow> \<exists>V. \<Delta> x = Some V \<and> at_least_two_elems V"
        by auto
      show "infinite { x |x V. \<Delta> x = Some V \<and> at_least_two_elems V}"
        using asm1 by simp
      show "\<And>x V. \<Delta> x = Some V \<Longrightarrow> V \<noteq> {}" using asm1
        by blast
    qed
    then obtain A where "\<not> overapprox_fv \<Delta> A (free_vars \<Delta> A)"
      by blast
    then obtain S where "overapprox_fv \<Delta> A S \<and> (\<forall>S'. overapprox_fv \<Delta> A S' \<longrightarrow> S \<subseteq> S')"
      using asm0 by blast
    then have "S = free_vars \<Delta> A"
      by (simp add: exists_minimum_then_its_free_vars)
    then show False
      using \<open>\<not> overapprox_fv \<Delta> A (free_vars \<Delta> A)\<close> \<open>overapprox_fv \<Delta> A S \<and> (\<forall>S'. overapprox_fv \<Delta> A S' \<longrightarrow> S \<subseteq> S')\<close> by auto
  qed
qed
*)



subsection \<open>wf_assertion\<close>


lemma wf_assertionI:
  assumes "\<And>x' x. pure_larger x' x \<and> A x \<Longrightarrow> A x'"
  shows "wf_assertion A"
  using assms wf_assertion_def by blast

lemma wf_assertionE:
  assumes "wf_assertion A"
  and "pure_larger x' x"
  and "A x"
shows "A x'"
  using assms(1) assms(2) assms(3) wf_assertion_def 
  by metis


lemma rel_stable_assertion_mono:
  assumes "\<omega>' \<succeq> \<omega>"
      and "rel_stable_assertion \<omega> A"
      and "wf_assertion A"
    shows "rel_stable_assertion \<omega>' A"
proof (rule rel_stable_assertionI)
  fix x a assume asm0: "\<omega>' ## a" "pure_larger x (stabilize a)" "x \<succeq> |\<omega>'|"
  then have "\<omega> ## a \<and> pure_larger x (stabilize a) \<and> x \<succeq> |\<omega>|"    
    using assms(1) core_stabilize_mono(1) smaller_compatible succ_trans by blast
  then show "A a = A x"
    using assms(2) rel_stable_assertionE by blast
qed


(* By induction (assuming it's finite) *)
lemma same_on_free_var:
  assumes "\<And>x. x \<in> free_vars \<Delta> A \<Longrightarrow> the_ag s1 x = the_ag s2 x"
      and "wf_assertion A"
      and "finite (dom (variables \<Delta>))"
    shows "A ((s1, \<phi>) \<longleftrightarrow> A ((s2, \<phi>)"
  sorry
(*
  by (metis (full_types) option.distinct(1) plus_agreement_def u_neutral)
*)

lemma self_framing_same_stable:
  assumes "self_framing A"
      and "self_framing B"
      and "Set.filter stable (\<langle>A\<rangle>) = Set.filter stable (\<langle>B\<rangle>)"
    shows "A = B"
  using assms(1-2)
proof (rule self_framing_ext)
  fix \<omega> :: "('v, 'a) abs_state" assume asm0: "sep_algebra_class.stable \<omega>"
  then show "A \<omega> \<Longrightarrow> B \<omega>"
    by (metis assms(3) inh_def mem_Collect_eq member_filter)
  show "B \<omega> \<Longrightarrow> A \<omega>"
    by (metis asm0 assms(3) inh_def mem_Collect_eq member_filter)
qed

lemma self_framing_sat_stabilize:
  assumes "self_framing A"
  shows "A a \<longleftrightarrow> A (stabilize a)"
  using assms self_framing_def by blast


lemma self_framing_wfI:
  assumes "wf_assertion A"
      and "\<And>\<omega>. A \<omega> \<Longrightarrow> A (stabilize \<omega>)"
    shows "self_framing A"
proof (rule self_framingI)
  fix \<omega> show "A \<omega> = A (stabilize \<omega>)"    
    sorry
(*
    by (metis assms(1) assms(2) pure_larger_stabilize stabilize_def wf_assertionE)
*)
qed





subsection \<open>Assertion connectives\<close>


lemma wf_negate:
  assumes "wf_exp b"
  shows "wf_exp (negate b)"
proof (rule wf_expI)
  fix a show "negate b a = negate b |a|"
    by (metis assms negate_def wf_exp_def)
  fix ba v
  assume asm0: "a \<succeq> ba \<and> negate b ba = Some v"
  then show "negate b a = Some v"
    by (smt (verit, best) assms negate_def option.exhaust_sel wf_expE)
qed

lemma framed_by_negate:
  assumes "framed_by_exp A b"
  shows "framed_by_exp A (negate b)"
  by (metis assms framed_by_exp_def negate_def option.distinct(1))


lemma sat_starI:
  assumes "Some \<omega> = a \<oplus> b"
      and "A a"
      and "B b"
    shows "(A \<otimes> B) \<omega>"
  using assms(1) assms(2) assms(3) astar_def by blast

lemma sat_starE:
  assumes "(A \<otimes> B) \<omega>"
  shows "\<exists>a b. Some \<omega> = a \<oplus> b \<and> A a \<and> B b"
  using assms(1) astar_def by blast

lemma sat_starE_ag_store:
  assumes "(A \<otimes> B) \<omega>"
  shows "\<exists>a b. Some \<omega> = (fst \<omega>, a) \<oplus> (fst \<omega>, b) \<and> A (fst \<omega>, a) \<and> B (fst \<omega>, b)"
proof -
  obtain a b where "Some \<omega> = a \<oplus> b \<and> A a \<and> B b"
    using assms sat_starE by blast
  then show ?thesis
    sorry
(*
    by (metis (no_types, opaque_lifting) agreement.expand get_store_def greater_charact neutral_smallest prod.exhaust_sel)
*)
qed

lemma sat_star_equiv:
  "(A \<otimes> B) \<omega> \<longleftrightarrow> (\<exists>a b. Some (get_state \<omega>) = a \<oplus> b \<and> A (fst \<omega>, a) \<and> B (fst \<omega>, b))" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis full_add_charact(2) get_state_def sat_starE_ag_store snd_conv)
  show "?B \<Longrightarrow> ?A"
    by (smt (z3) agreement.exhaust_sel fst_conv get_state_def get_store_def get_trace_def option.discI option.sel plus_state_def prod.collapse sat_starI snd_conv)
qed

lemma astar_inh:
  "\<langle>A \<otimes> B\<rangle> = \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
proof
  show "\<langle>A \<otimes> B\<rangle> \<subseteq> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
  proof
    fix x assume "x \<in> \<langle>A \<otimes> B\<rangle>"
    then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
      by (metis astar_def inh_def mem_Collect_eq)
    then show "x \<in> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
      by (meson in_inh x_elem_set_product)
  qed
  show "\<langle>A\<rangle> \<otimes> \<langle>B\<rangle> \<subseteq> \<langle>A \<otimes> B\<rangle>"
  proof
    fix x assume "x \<in> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
    then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
      by (metis (mono_tags, lifting) inh_def mem_Collect_eq x_elem_set_product)
    then show "x \<in> \<langle>A \<otimes> B\<rangle>"
      by (simp add: in_inh sat_starI)
  qed
qed





(*
assumes A is self-framing
A frames B iff A * B is self-framing
*)

lemma sat_conjI:
  assumes "A \<omega>"
      and "B \<omega>"
    shows "(A \<inter> B) \<omega>"
  by (simp add: aconj_def assms(1) assms(2))

lemma sat_conjE:
  assumes "(A \<inter> B) \<omega>"
    shows "A \<omega> \<and> B \<omega>"
  using aconj_def assms 
  by simp

lemma astar_conj:
  "\<langle>A \<inter> B\<rangle> = \<langle>A\<rangle> \<inter> \<langle>B\<rangle>"
  sorry

lemma wf_conj:
  assumes "wf_assertion A"
      and "wf_exp b"
      and "framed_by_exp A b"
    shows "wf_assertion (A \<inter> (pure_typed \<Delta> b))"
proof (rule wf_assertionI)
  fix x x' assume "pure_larger x' x \<and> (A \<inter> pure_typed \<Delta> b) x"
  then have "A x' \<and> b x = Some True"
    by (metis assms(1) pure_typed \<Delta>_def sat_conjE wf_assertionE)
  then have "b x' = Some True"
    by (meson \<open>pure_larger x' x \<and> (A \<inter> pure_typed \<Delta> b) x\<close> assms(2) greater_equiv pure_larger_sum succ_refl wf_expE)
  then show "(A \<inter> pure_typed \<Delta> b) x'"
    by (simp add: \<open>A x' \<and> b x = Some True\<close> pure_typed \<Delta>_def sat_conjI)
qed


lemma self_framing_conj:
  assumes "wf_assertion A"
      and "wf_exp b"
      and "framed_by_exp A b"
      and "self_framing A"
    shows "self_framing (A \<inter> (pure_typed \<Delta> b))"
proof (rule self_framingI)
  fix \<omega> show "(A \<inter> pure_typed \<Delta> b) \<omega> = (A \<inter> pure_typed \<Delta> b) (stabilize \<omega>)"
    by (metis (no_types, lifting) aconj_def assms(2) assms(3) assms(4) pure_typed \<Delta>_def self_framing_sat_stabilize wf_exp_framed_by_stabilize)
qed

lemma wf_star:
  assumes "wf_assertion A"
      and "wf_assertion B"
    shows "wf_assertion (A \<otimes> B)"
proof (rule wf_assertionI)
  fix x' x assume asm0: "pure_larger x' x \<and> (A \<otimes> B) x"
  then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
    using astar_def by auto
  then obtain a' where "pure_larger a' a" "Some x' = a' \<oplus> b"
    using asm0 pure_larger_sum by blast
  moreover have "A a'"
    using \<open>A a\<close> assms(1) calculation(1) wf_assertionE by blast
  ultimately show "(A \<otimes> B) x'"
    using \<open>B b\<close> sat_starI by auto
qed

section \<open>Minimal stuff\<close>

lemma points_toI:
  assumes "r \<omega> = Some hl" 
      and "has_write_perm_only (get_state \<omega>) hl"
    shows "points_to r \<omega>"
  using assms(1) assms(2) points_to_def by blast

lemma points_to_valueI:
  assumes "r \<omega> = Some hl"
      and "e \<omega> = Some v"
      and "has_write_perm_only (get_state \<omega>) hl"
      and "has_value (get_state \<omega>) hl v"
    shows "points_to_value r e \<omega>"
  using assms(1) assms(2) assms(3) assms(4) points_to_value_def by blast

lemma points_to_value_same:
  assumes "wf_exp r"
      and "r a = r b"
      and "e a = e b"
      and "points_to_value r e a"
      and "points_to_value r e b"
      and "fst a = fst b"
    shows "stabilize a = stabilize b"
  sorry
(* TODO *)


lemma points_to_two:
  assumes "wf_exp r"
      and "r a = r b"
      and "points_to r a"
      and "points_to r b"
      and "fst a = fst b"
    shows "stabilize a = stabilize b"
proof -
  obtain hla where "r a = Some hla \<and> has_write_perm_only (get_state a) hla"
    using assms(3) points_to_def by blast
  moreover obtain hlb where "r b = Some hlb \<and> has_write_perm_only (get_state b) hlb"
    using assms(4) points_to_def by blast
  moreover have "stabilize (get_state a) = stabilize (get_state b)"
  proof (rule has_write_perm_only_same)
    show "has_write_perm_only (get_state a) hla"      
      by (simp add: \<open>r a = Some hla \<and> has_write_perm_only (get_state a) hla\<close>)
    show "has_write_perm_only (get_state b) hla"
      using assms(2) calculation(1) calculation(2) by force
  qed
  ultimately show ?thesis sorry
(*
    by (simp add: assms(5) stabilize_prod_def)
*)
qed

lemma true_necessary_condition_from_framed_by:
  assumes "self_framing A"
    and "\<And>a x b. a ## b \<Longrightarrow> stable a \<Longrightarrow> A a \<Longrightarrow> Some x = stabilize b \<oplus> |a| \<Longrightarrow> (B b \<longleftrightarrow> B x)"
      and "wf_assertion (A \<otimes> B)"
    shows "self_framing (A \<otimes> B)"
  using assms(3)
proof (rule self_framing_wfI)
  fix \<omega>
  assume asm0: "(A \<otimes> B) \<omega>"
  then obtain a b where "Some \<omega> = a \<oplus> b" "A a" "B b"
    using astar_def by auto
  then have "Some (stabilize \<omega>) = stabilize a \<oplus> stabilize b"
    using stabilize_sum by blast
  moreover obtain b' where "Some b' = stabilize b \<oplus> |stabilize a|"
    using commutative[of "stabilize a" "stabilize b"]
    sorry
(*
    by (metis asso3 calculation commutative option.distinct(1) option.exhaust_sel stabilize_rel_sum_pure)
*)
  then have "Some (stabilize \<omega>) = stabilize a \<oplus> b'"
    by (smt (verit) asso1 calculation commutative core_is_smaller)
  then have "A (stabilize a)"
    using \<open>A a\<close> assms(1) self_framing_sat_stabilize by blast
  moreover have "stabilize a ## b"
    by (metis \<open>Some \<omega> = a \<oplus> b\<close> defined_def max_projection_prop_def max_projection_prop_stable_stabilize option.distinct(1) smaller_compatible)
  then have "B b'"
    using \<open>B b\<close> \<open>Some b' = stabilize b \<oplus> |stabilize a|\<close> assms(2) calculation(2) stabilize_is_stable by blast
  ultimately show "(A \<otimes> B) (stabilize \<omega>)"
    using \<open>Some (stabilize \<omega>) = stabilize a \<oplus> b'\<close> sat_starI by blast
qed


lemma framed_by_self_framing_one_direction:
  assumes "wf_assertion A"
      and "wf_assertion B"
      and "self_framing A \<and> framed_by A B"
    shows "self_framing (A \<otimes> B)"
proof (rule true_necessary_condition_from_framed_by)
  show "wf_assertion (A \<otimes> B)"
    using assms(1) assms(2) wf_star by blast
  show "self_framing A"
    by (simp add: assms(3))
  fix a x b assume "a ## b" "stable a" "A a" "Some x = stabilize b \<oplus> |a|"
  then show "B b = B x"
    using framed_by_def[of A B] inh_def[of A] rel_stable_assertionE[of a B b x]
    by (metis (mono_tags, lifting) assms(3) greater_equiv in_inh max_projection_prop_def max_projection_prop_pure_core pure_larger_def)
qed

(*
lemma wf_assertion_Stabilize:
  "wf_assertion (Stabilize_typed \<Delta> S)"
proof (rule wf_assertionI)
  fix x' x
  assume "pure_larger x' x \<and> (Stabilize_typed \<Delta> S) x"
  then have "stabilize x \<in> S"
    by (simp add: Stabilize_def)
  moreover have "stabilize x' = stabilize x"
    using \<open>pure_larger x' x \<and> (Stabilize_typed \<Delta> S) x\<close> pure_larger_stabilize_same by blast
  ultimately show "(Stabilize_typed \<Delta> S) x'"
    by (simp add: Stabilize_def)
qed
*)






section \<open>Something else\<close>


lemma subset_sequential_composition:
  assumes "sequential_composition \<Delta> S1' C S2'"
      and "S1 \<subseteq> S1'"
    shows "\<exists>S2. S2 \<subseteq> S2' \<and> sequential_composition \<Delta> S1 C S2"
  using assms(1)
proof (rule sequential_composition_elim)
  fix f assume asm0: "S2' = \<Union> (f ` S1')" "\<And>\<omega>. \<omega> \<in> S1' \<Longrightarrow> red_stmt \<Delta> C \<omega> (f \<omega>)"
  then have "sequential_composition \<Delta> S1 C (\<Union> (f ` S1))"
    by (meson SeqComp assms(2) subsetD)
  then show "\<exists>S2\<subseteq>S2'. sequential_composition \<Delta> S1 C S2"
    by (metis Union_mono asm0(1) assms(2) image_mono)
qed

lemma empty_sequential_composition:
  assumes "sequential_composition \<Delta> {} C S"
    shows "S = {}"
  using assms(1)
proof (rule sequential_composition_elim)
  fix f show "S = \<Union> (f ` {}) \<Longrightarrow> (\<And>\<omega>. \<omega> \<in> {} \<Longrightarrow> red_stmt \<Delta> C \<omega> (f \<omega>)) \<Longrightarrow> S = {}"
    by blast
qed

lemma ag_store_add_keep_val:
  assumes "Some c = a \<oplus> b"
      and "get_store a x = Some v"
    shows "get_store c x = Some v"
  by (simp add: assms(1) assms(2) full_add_charact(1))

lemma only_modified_can_be_modified_aux:
  shows "red_stmt \<Delta> C \<omega> S \<Longrightarrow> x \<notin> modif C \<Longrightarrow> (\<And>\<omega>'. \<omega>' \<in> S \<Longrightarrow> get_store \<omega> x = get_store \<omega>' x)"
    and "sequential_composition \<Delta> S C S' \<Longrightarrow> x \<notin> modif C \<Longrightarrow> (\<And>\<omega>1 \<omega>2. \<omega>1 \<in> S \<Longrightarrow> \<omega>2 \<in> S \<Longrightarrow> get_store \<omega>1 x = get_store \<omega>2 x)
  \<Longrightarrow> (\<And>\<omega> \<omega>'. \<omega> \<in> S \<Longrightarrow> \<omega>' \<in> S' \<Longrightarrow> get_store \<omega> x = get_store \<omega>' x)"
proof (induct rule: red_stmt_sequential_composition.inducts)
  case (RedExhale a A \<omega> \<omega>' \<Delta>)
  then show ?case
    by (simp add: full_add_charact(1))
next
  case (RedInhale \<omega> A \<Delta>)
  then obtain a where "Some \<omega>' = \<omega> \<oplus> a" "a \<in> \<langle>A\<rangle>" "stable \<omega>'"
    by (metis (no_types, lifting) member_filter singletonD x_elem_set_product)
  then show ?case
  proof (cases "get_store \<omega> x")
    case None
    then show ?thesis
      by (simp add: \<open>Some \<omega>' = \<omega> \<oplus> a\<close> full_add_charact(1))
  next
    case (Some aa)
    then show ?thesis
      by (simp add: \<open>Some \<omega>' = \<omega> \<oplus> a\<close> ag_store_add_keep_val)
  qed
next
  case (RedHavoc \<Delta> y ty \<omega>)
  then have "x \<noteq> y"
    by auto
  then obtain v where "\<omega>' = set_store \<omega> ((get_store \<omega>)(y := Some v))"
    using RedHavoc.prems(2) by blast
  then have "((get_store \<omega>)(y := Some v)) x = (get_store \<omega>) x"
    by (simp add: \<open>x \<noteq> y\<close>)
  then show "get_store \<omega> x = get_store \<omega>' x"
    by (simp add: \<open>\<omega>' = set_store \<omega> ((get_store \<omega>)(y := Some v))\<close>)
next
  case (SeqComp S \<Delta> C f S')
  then obtain \<omega>'' where "\<omega>'' \<in> S" "\<omega>' \<in> f \<omega>''"
    by blast
  then have "get_store \<omega>'' x = get_store \<omega>' x"
    using SeqComp.hyps(2) SeqComp.prems(1) SeqComp.prems(3) by blast
  then show "get_store \<omega> x = get_store \<omega>' x"
      using SeqComp.prems(2) SeqComp.prems(3) \<open>\<omega>'' \<in> S\<close> by presburger
next
  case (RedSeq \<Delta> C1 \<omega> S1 C2 S2)
  then obtain \<omega>1 where "\<omega>1 \<in> S1" by blast
  then show ?case
    by (metis RedSeq.hyps(2) RedSeq.hyps(4) RedSeq.prems(1) RedSeq.prems(2) Un_iff modif.simps(3))
next
  case (RedLocalAssign e \<sigma> \<gamma> v \<Delta> x)
  then show ?case sorry
qed (auto)

lemma only_modif_can_be_modified:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "x \<notin> modif C"
      and "\<omega>' \<in> S"
    shows "get_store \<omega> x = get_store \<omega>' x"
  using assms(1) assms(2) assms(3) only_modified_can_be_modified_aux(1) by blast

(* TODO:
- Add right dep_stable hypothesis
- prove frame for havoc and write...
- r might contain variables that are forgotten? so, probably not the one that needs to change?
*)


(*
because:
- r is stable
- has_write_perm hl (get_state \<omega>')
*)

lemma in_univ:
  "\<omega> \<in> univ r \<longleftrightarrow> (get_state \<omega> = r)"
  by (simp add: get_state_def mem_Times_iff)

lemma sum_in_univ:
  assumes "Some \<omega>' = \<omega> \<oplus> (s, r)"
  shows "\<omega>' \<in> {\<omega>} \<otimes> UNIV \<times> {r}"
  using add_set_elem assms by blast


(*
lemma frame_rule_aux:
  shows "red_stmt \<Delta> C \<omega> S \<Longrightarrow> wf_abs_stmt \<Delta> C \<Longrightarrow> stable \<omega> \<Longrightarrow> (\<And>\<omega>' r s \<tau>. stable r \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> (s, \<tau>, r) \<Longrightarrow> (\<exists>S'. red_stmt \<Delta> C \<omega>' S' \<and> S' \<subseteq> S \<otimes> (univ r)))"
    and "sequential_composition \<Delta> S C S' \<Longrightarrow> wf_abs_stmt \<Delta> C \<Longrightarrow> (\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> stable \<omega>) \<Longrightarrow> (\<And>r. stable r \<Longrightarrow> (\<exists>S''. sequential_composition \<Delta> (S \<otimes> (univ r)) C S'' \<and> S'' \<subseteq> S' \<otimes> (univ r)))"
proof (induct rule: red_stmt_sequential_composition.inducts)
  case (SeqComp S \<Delta> C f S')

  let ?g = "\<lambda>x. (SOME y. y \<in> S \<and> Some (get_state x) = (get_state y) \<oplus> r \<and> get_store y = get_store x \<and> get_trace y = get_trace x)"
  let ?f = "\<lambda>x. (SOME S'. red_stmt \<Delta> C x S' \<and> S' \<subseteq> f (?g x) \<otimes> (univ r))"

  have r1: "\<And>x. x \<in> S \<otimes> (univ r) \<Longrightarrow> ?g x \<in> S \<and> Some (get_state x) = get_state (?g x) \<oplus> r \<and> get_store (?g x) = get_store x \<and> get_trace (?g x) = get_trace x"
  proof -
    fix x assume "x \<in> S \<otimes> (univ r)"
    then obtain xs xr where "Some x = xs \<oplus> xr" "xs \<in> S" "xr \<in> univ r"
      by (meson x_elem_set_product)
    then have "get_state xr = r"
      by (simp add: in_univ)
    show "?g x \<in> S \<and> Some (get_state x) = get_state (?g x) \<oplus> r \<and> get_store (?g x) = get_store x \<and> get_trace (?g x) = get_trace x"
    proof (rule someI_ex)
      show "\<exists>xa. xa \<in> S \<and> Some (get_state x) = get_state xa \<oplus> r \<and> get_store xa = get_store x \<and> get_trace xa = get_trace x"
        by (metis \<open>Some x = xs \<oplus> xr\<close> \<open>get_state xr = r\<close> \<open>xs \<in> S\<close> full_add_charact(2) full_add_defined option.discI u_neutral)
    qed
  qed
  have r2: "\<And>x. x \<in> S \<otimes> (univ r) \<Longrightarrow> red_stmt \<Delta> C x (?f x) \<and> ?f x \<subseteq> f (?g x) \<otimes> (univ r)"
  proof -
    fix x assume asm0: "x \<in> S \<otimes> (univ r)"
    show "red_stmt \<Delta> C x (?f x) \<and> ?f x \<subseteq> f (?g x) \<otimes> (univ r)"
    proof (rule someI_ex)
      have "\<exists>S'. red_stmt \<Delta> C x S' \<and> S' \<subseteq> f (?g x) \<otimes> (univ r)"
      proof (rule SeqComp.hyps(2))
        show "?g x \<in> S"
          using asm0 r1 by blast
        have "Some (get_state x) = get_state (?g x) \<oplus> r"
          using asm0 r1 by blast
        moreover have "Some (fst x) = fst (?g x) \<oplus> fst x"
          by (metis (no_types, lifting) asm0 defined_def get_store_comp plus_agreement_def r1)
        ultimately show "Some x = ?g x \<oplus> (Ag (get_store x), Ag (get_trace x), r)"
          sorry
(*
          by (simp add: get_state_def plus_prodI)
*)
        show "sep_algebra_class.stable (?g x)"
          by (simp add: SeqComp.prems(2) \<open>(?g x) \<in> S\<close>)
      qed ((insert SeqComp; blast)+)
      then show "\<exists>xa. red_stmt \<Delta> C x xa \<and> xa \<subseteq> f (?g x) \<otimes> (univ r)"
        by force
    qed
  qed

  let ?S = "\<Union>\<omega>\<in>S \<otimes> (univ r). ?f \<omega>"

  have "sequential_composition \<Delta> (S \<otimes> (univ r)) C ?S"
  proof (rule red_stmt_sequential_composition.SeqComp)
    fix \<omega> assume asm0: "\<omega> \<in> S \<otimes> (univ r)"
    then show "red_stmt \<Delta> C \<omega> (?f \<omega>)"
      using r2 by blast
  qed (blast)
  moreover have "?S \<subseteq> S' \<otimes> (univ r)"
  proof
    fix y assume "y \<in> (\<Union>\<omega>\<in>S \<otimes> (univ r). ?f \<omega>)"
    then obtain \<omega> where \<omega>_def: "\<omega> \<in> S \<otimes> (univ r)" "y \<in> ?f \<omega>"
      by blast
    then have "?f \<omega> \<subseteq> f (?g \<omega>) \<otimes> (univ r)"
      using r2 by blast
    moreover have "f (?g \<omega>) \<subseteq> S'"
      by (metis (no_types, lifting) SeqComp.hyps(3) UN_I \<open>\<omega> \<in> S \<otimes> (univ r)\<close> r1 subsetI)
    then have "f (?g \<omega>) \<otimes> (univ r) \<subseteq> S' \<otimes> (univ r)"
      by (meson subset_iff x_elem_set_product)
    ultimately show "y \<in> S' \<otimes> (univ r)"
      using \<omega>_def by blast
  qed
  ultimately show "\<exists>S''. sequential_composition \<Delta> (S \<otimes> (univ r)) C S'' \<and> S'' \<subseteq> S' \<otimes> (univ r)" 
    by meson
next
  case (RedSkip \<Delta> \<omega>)
  then show "\<exists>S'. red_stmt \<Delta> Skip \<omega>' S' \<and> S' \<subseteq> {\<omega>} \<otimes> local.univ r"
    sorry (*
    by (metis bot.extremum insert_subsetI red_stmt_sequential_composition.RedSkip sum_in_univ)
*)
next
  case (RedAssertTrue \<omega> A \<Delta> E)
  then show ?case sorry (*
  then show "\<exists>S'. red_stmt \<Delta> (abs_stmt.Assert \<omega>) E S' \<and> S' \<subseteq> {A} \<otimes> UNIV \<times> {r}" sorry
*)
(*
    \<omega> A
    rel_stable_assertion A \<omega>
    wf_abs_stmt \<Delta> (Assert \<omega>)
    sep_algebra_class.stable A
    sep_algebra_class.stable r
    Some \<omega>' = A \<oplus> (s, r)
*)
(* TODO: Restrict to monotonic case *)
(*
  then show "\<exists>S'. red_stmt \<Delta> (Assert \<omega>) \<omega>' S' \<and> S' \<subseteq> {A} \<otimes> UNIV \<times> {r}" sorry
*)
next
  case (RedInhale \<omega> A \<Delta> \<omega>')
(*
    rel_stable_assertion \<omega> A
    wf_abs_stmt \<Delta> (Inhale A)
    sep_algebra_class.stable \<omega>
    sep_algebra_class.stable r
    Some \<omega>' = \<omega> \<oplus> (s, r)
*)
  then have "\<omega>' \<succeq> \<omega>"
    using greater_def by blast
  then  have "rel_stable_assertion \<omega>' A"
    using RedInhale.hyps RedInhale.prems(1) rel_stable_assertion_mono wf_abs_stmt.simps(2) by blast
  then have "red_stmt \<Delta> (Inhale A) \<omega>' (Set.filter stable ({\<omega>'} \<otimes> \<langle>A\<rangle>))"
    using red_stmt_sequential_composition.RedInhale by auto
  moreover have "{\<omega>'} \<subseteq> {\<omega>} \<otimes> (univ r)" sorry
(*
    by (simp add: RedInhale.prems(4) sum_in_univ)
*)
  then have "{\<omega>'} \<otimes> \<langle>A\<rangle> \<subseteq> {\<omega>} \<otimes> \<langle>A\<rangle> \<otimes> (univ r)"
    by (smt (verit, del_insts) add_set_asso add_set_commm insert_subset singletonD subsetI x_elem_set_product)
  moreover have "Set.filter stable ({\<omega>'} \<otimes> \<langle>A\<rangle>) \<subseteq> Set.filter stable ({\<omega>} \<otimes> \<langle>A\<rangle>) \<otimes> (univ r)"
  proof
    fix x assume "x \<in> Set.filter stable ({\<omega>'} \<otimes> \<langle>A\<rangle>)"
    then obtain a where "stable x" "Some x = \<omega>' \<oplus> a" "a \<in> \<langle>A\<rangle>"
      by (metis (no_types, lifting) member_filter singletonD x_elem_set_product)    
    then obtain xx where "Some xx = \<omega> \<oplus> a"
      using \<open>\<omega>' \<succeq> \<omega>\<close> compatible_smaller by blast
    then have "Some (stabilize xx) = \<omega> \<oplus> stabilize a"
      using stabilize_sum already_stable RedInhale.prems(2) by fastforce
    moreover obtain a' where "Some a' = stabilize a \<oplus> |\<omega>|"
      by (metis (no_types, opaque_lifting) calculation commutative compatible_smaller max_projection_prop_def max_projection_prop_pure_core)
    ultimately have "Some (stabilize xx) = \<omega> \<oplus> a'"
      by (metis (no_types, lifting) asso1 commutative core_is_smaller)
    moreover have "a' \<in> \<langle>A\<rangle>"
      using inh_def[of A] rel_stable_assertionE[of \<omega> A a a']
      by (metis (no_types, lifting) RedInhale.hyps \<open>Some a' = stabilize a \<oplus> |\<omega>|\<close> \<open>Some xx = \<omega> \<oplus> a\<close> \<open>a \<in> \<langle>A\<rangle>\<close> defined_def greater_equiv max_projection_prop_def max_projection_prop_pure_core mem_Collect_eq option.simps(3) pure_larger_def)
    ultimately have "stabilize xx \<in> Set.filter stable ({\<omega>} \<otimes> \<langle>A\<rangle>)"
      by (simp add: is_in_set_sum stabilize_is_stable)
    moreover have "Some x = xx \<oplus> (Ag (get_store \<omega>'), Ag (get_trace \<omega>'), r)"
      sorry
(*
      by (smt (verit) RedInhale.prems(4) \<open>Some x = \<omega>' \<oplus> a\<close> \<open>Some xx = \<omega> \<oplus> a\<close> asso1 commutative fst_conv full_add_charact(1) full_state_ext get_state_def get_store_def snd_conv)
*)
    then have "Some x = stabilize xx \<oplus> (Ag (get_store \<omega>'), Ag (get_trace \<omega>'), r)"
      sorry
(*
      using \<open>sep_algebra_class.stable x\<close> stabilize_sum_result_stable by blast
*)
    ultimately show "x \<in> Set.filter stable ({\<omega>} \<otimes> \<langle>A\<rangle>) \<otimes> (univ r)"
      using x_elem_set_product by fastforce
  qed

  ultimately show "\<exists>S'. red_stmt \<Delta> (Inhale A) \<omega>' S' \<and> S' \<subseteq> Set.filter stable ({\<omega>} \<otimes> \<langle>A\<rangle>) \<otimes> (UNIV \<times> {r})"
    by meson
next
  case (RedExhale a A \<omega> \<omega>1 \<Delta> \<omega>')
  then obtain x where "Some x = \<omega>1 \<oplus> (s, r)"
    by (metis (no_types, opaque_lifting) asso2 commutative not_None_eq)
  moreover have "stable x"
    by (metis RedExhale.hyps(3) RedExhale.prems(3) calculation snd_conv stable_snd stable_sum)
  then have "red_stmt \<Delta> (Exhale A) \<omega>' {x}"
    by (metis (no_types, opaque_lifting) RedExhale.hyps(1) RedExhale.hyps(2) RedExhale.prems(4) asso1 calculation commutative red_stmt_sequential_composition.RedExhale)
  then show ?case
    by (metis calculation(1) empty_subsetI insert_subsetI sum_in_univ)
next
  case (RedIfTrue b \<omega> \<Delta> C1 S C2)
  then have "\<exists>S'. red_stmt \<Delta> C1 \<omega>' S' \<and> S' \<subseteq> S \<otimes> (univ r)"
    using RedIfTrue(3)[of r \<omega>'] by fastforce
  then obtain S' where "red_stmt \<Delta> C1 \<omega>' S' \<and> S' \<subseteq> S \<otimes> (univ r)"
    by blast
  moreover have "b \<omega>' = Some True" sorry
(*
    by (meson RedIfTrue.hyps(1) RedIfTrue.prems(1) RedIfTrue.prems(2) greater_def wf_expE wf_abs_stmt.simps(5))
*)
  ultimately show ?case
    using red_stmt_sequential_composition.RedIfTrue by blast
next
  case (RedIfFalse b \<omega> \<Delta> C2 S C1)
  then have "\<exists>S'. red_stmt \<Delta> C2 \<omega>' S' \<and> S' \<subseteq> S \<otimes> (univ r)"
    using RedIfFalse(3)[of r \<omega>'] by fastforce
  moreover have "b \<omega>' = Some False" sorry
(*
    by (meson RedIfFalse.hyps(1) RedIfFalse.prems(1) RedIfFalse.prems(4) greater_def wf_expE wf_abs_stmt.simps(5))
*)
  ultimately show ?case
    using red_stmt_sequential_composition.RedIfFalse by blast
next
  case (RedSeq \<Delta> C1 \<omega> S1 C2 S2)
  then obtain S' where "red_stmt \<Delta> C1 \<omega>' S' \<and> S' \<subseteq> S1 \<otimes> (univ r)"
    using RedSeq(2)[of r \<omega>'] by fastforce
  moreover have "\<And>\<omega>. \<omega> \<in> S1 \<Longrightarrow> stable \<omega>"
    using RedSeq.prems(2) local.RedSeq(1) red_stable by blast
  ultimately obtain S'' where "sequential_composition \<Delta> (S1 \<otimes> (univ r)) C2 S'' \<and> S'' \<subseteq> S2 \<otimes> (univ r)"
    using RedSeq.hyps(4) RedSeq.prems(1) RedSeq.prems(3) by fastforce
  then show "\<exists>S'. red_stmt \<Delta> (Seq C1 C2) \<omega>' S' \<and> S' \<subseteq> S2 \<otimes> (univ r)"
    by (smt (z3) \<open>\<And>thesis. (\<And>S'. red_stmt \<Delta> C1 \<omega>' S' \<and> S' \<subseteq> S1 \<otimes> UNIV \<times> {r} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> order_trans red_seq_equiv subset_sequential_composition)
next
(*  case (RedLocalAssign e \<sigma> \<gamma> v \<Delta> x) *)
  case (RedLocalAssign \<Delta> x ty e \<sigma> \<gamma> v \<omega>')

  have "get_store \<omega>' = the_ag \<sigma>"
  proof (rule ext)
    fix l show "get_store \<omega>' l = the_ag \<sigma> l"
      by (metis RedLocalAssign.prems(4) fst_conv full_add_charact(1) get_store_def)
  qed
  then have "e \<omega>' = Some v"
    by (meson RedLocalAssign.hyps RedLocalAssign.prems(1) RedLocalAssign.prems(4) greater_def wf_expE wf_abs_stmt.simps(8))
  then have "red_stmt \<Delta> (LocalAssign x e) \<omega>' {(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>')}"
    by (metis RedLocalAssign.hyps(1) RedLocalAssign.hyps(3) \<open>get_store \<omega>' = the_ag \<sigma>\<close> agreement.exhaust_sel get_state_def get_store_def prod.collapse red_stmt_sequential_composition.RedLocalAssign)
  then have "(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>') \<in> {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>)} \<otimes> (univ r)"
    by (metis RedLocalAssign.prems(4) add_defined_lift full_add_charact(2) get_state_def snd_conv sum_in_univ) (* long *)
  then show "\<exists>S'. red_stmt \<Delta> (LocalAssign x e) \<omega>' S' \<and> S' \<subseteq> {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>)} \<otimes> (univ r)"
    by (meson \<open>red_stmt \<Delta> (LocalAssign x e) \<omega>' {(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>')}\<close> empty_subsetI insert_subsetI)
next
  case (RedHavoc \<Delta> x ty \<sigma> \<gamma>)

  have "get_store \<omega>' = the_ag \<sigma>"
  proof (rule ext)
    fix l show "get_store \<omega>' l = the_ag \<sigma> l"
      by (metis RedHavoc.prems(4) fst_conv full_add_charact(1) get_store_def)
  qed
  then have "red_stmt \<Delta> (Havoc x) (\<sigma>, get_state \<omega>') {(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>') |v. v \<in> ty}"
    by (simp add: RedHavoc.hyps red_stmt_sequential_composition.RedHavoc)
  moreover have "{(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>') |v. v \<in> ty} \<subseteq> {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<otimes> (univ r)"
  proof
    fix xa assume asm0: "xa \<in> {(upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>') |v. v \<in> ty}"
    then obtain v where "v \<in> ty" "xa = (upd_ag_partial_map \<sigma> x (Some v), get_state \<omega>')"
      by blast
    moreover have "Some (get_state \<omega>') = \<gamma> \<oplus> r"
      by (metis RedHavoc.prems(4) get_state_def plus_prodE snd_conv)
    ultimately show "xa \<in> {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<otimes> (univ r)"
      using add_defined_lift x_elem_set_product by fastforce
  qed
  moreover have "(\<sigma>, get_state \<omega>') = \<omega>'"
    by (metis \<open>get_store \<omega>' = the_ag \<sigma>\<close> agreement.expand get_state_def get_store_def surjective_pairing)
  ultimately show ?case
    by (metis (no_types, lifting))
next
  case (RedFieldAssign ref \<sigma> \<gamma> hl e v \<Delta> \<omega>')
  then have "ref \<omega>' = Some hl \<and> e \<omega>' = Some v"
    by (meson greater_def wf_abs_stmt.simps(9) wf_expE)
  then have "has_write_perm hl (get_state \<omega>')"
    by (metis (no_types, opaque_lifting) RedFieldAssign.hyps(3) RedFieldAssign.prems(4) get_state_def greater_charact greater_def has_write_perm_mono snd_conv)
  then have "red_stmt \<Delta> (FieldAssign ref e) \<omega>' {(fst \<omega>', set_value (get_state \<omega>') hl v)}"
    by (metis \<open>ref \<omega>' = Some hl \<and> e \<omega>' = Some v\<close> get_state_def prod.collapse red_stmt_sequential_composition.RedFieldAssign)
  moreover have "Some (set_value (get_state \<omega>') hl v) = set_value \<gamma> hl v \<oplus> r"
    by (metis RedFieldAssign.hyps(3) RedFieldAssign.prems(2) RedFieldAssign.prems(3) RedFieldAssign.prems(4) get_state_def plus_prodE frame_preserving_writing snd_conv stable_snd)
  moreover have "\<sigma> = fst \<omega>'"
    by (metis RedFieldAssign.prems(4) add_defined_lift fst_conv full_add_charact(1) full_state_ext get_state_def plus_prodE snd_conv)
  then have "(fst \<omega>', set_value (get_state \<omega>') hl v) \<in> {(\<sigma>, set_value \<gamma> hl v)} \<otimes> (univ r)"
    using add_defined_lift calculation(2) sum_in_univ by blast
  ultimately show "\<exists>S'. red_stmt \<Delta> (FieldAssign ref e) \<omega>' S' \<and> S' \<subseteq> {(\<sigma>, set_value \<gamma> hl v)} \<otimes> (univ r)"
    by (meson empty_subsetI insert_subsetI)
qed
*)

lemma exists_assertI:
  assumes "v0 \<in> ty"
      and "get_store \<omega> x = Some v0"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
      and "A (Ag ((get_store \<omega>)(x := Some v)), Ag (get_trace \<omega>)), snd \<omega>)"
    shows "exists_assert \<Delta> x A \<omega>"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) exists_assert_def get_state_def)


section \<open>SL Proof\<close>



section \<open>Real big proof\<close>




lemma prove_equality_snd_Stabilize:
  assumes "wf_set \<Delta> S"
  shows "Set.filter (wf_state \<Delta>) (\<langle>Stabilize_typed \<Delta> S\<rangle>) = S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (smt (verit, ccfv_SIG) already_stable Stabilize_def mem_Collect_eq member_filter inh_def subsetI wf_state_def)
  show "?B \<subseteq> ?A"
    by (smt (verit, ccfv_SIG) already_stable Stabilize_def assms in_inh member_filter subsetI wf_set_def wf_state_def)
qed

lemma Stabilize_only:
  assumes "self_framing A"
  shows "Stabilize_typed \<Delta> (\<langle>A\<rangle>) = A"
  using assms same_Stabilize_typed \<Delta> by auto


lemma stabilize_state_equiv:
  "stabilize (\<omega> :: ('v, 'a) abs_state) = (fst \<omega>, stabilize (snd \<omega>))"
  by (metis already_stable fst_conv snd_conv stabilize_is_stable stabilize_prod_def stable_snd)

lemma finite_dom_free_varsE:
  assumes "finite (dom (variables \<Delta>))"
      and "equal_on_set (free_vars \<Delta> A) \<sigma>1 \<sigma>2"
      and "A (Ag \<sigma>1, \<gamma>)"
    shows "A (Ag \<sigma>2, \<gamma>)"
  sorry
(*
  by (metis (mono_tags, lifting) agreement.exhaust_sel assms(3) commutative fst_conv full_add_charact(1) get_store_def u_neutral)
*)

lemma free_vars_exists_assert:
  assumes "finite (dom (variables \<Delta>))"
      and "x \<in> dom (variables \<Delta>)"
  shows "free_vars \<Delta> (exists_assert \<Delta> x A) \<subseteq> free_vars \<Delta> A - {x}"
proof (rule free_vars_upper_bound)
  show "overapprox_fv \<Delta> (exists_assert \<Delta> x A) (free_vars \<Delta> A - {x})"
  proof (rule overapprox_fvI)
    fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
    assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (free_vars \<Delta> A - {x}) \<sigma>1 \<sigma>2" "exists_assert \<Delta> x A (Ag \<sigma>1, \<gamma>)"
    moreover obtain ty where "Some ty = variables \<Delta> x"
      using assms(2) by force
    ultimately obtain v where "A (Ag (\<sigma>1(x := Some v)), \<gamma>)" "v \<in> ty" using exists_assert_def
      by (smt (verit, ccfv_threshold) agreement.exhaust_sel agreement.sel fst_conv get_state_def get_store_def get_trace_def option.sel snd_conv)
    moreover have "equal_on_set (free_vars \<Delta> A) (\<sigma>1(x := Some v)) (\<sigma>2(x := Some v))"
    proof (rule equal_on_setI)
      fix xa assume asm1: "xa \<in> free_vars \<Delta> A"
      then show "(\<sigma>1(x \<mapsto> v)) xa = (\<sigma>2(x \<mapsto> v)) xa"
      proof (cases "xa = x")
        case True
        then show ?thesis
          by (simp)
      next
        case False
        then show ?thesis
          by (metis (full_types) DiffI asm0(3) asm1 equal_on_set_def fun_upd_apply singletonD)
      qed
    qed
    moreover obtain v0 where "v0 \<in> ty" "\<sigma>2 x = Some v0"
      using \<open>Some ty = variables \<Delta> x\<close> asm0(2) assms(2) typed_store_def by auto
    ultimately show "exists_assert \<Delta> x A (Ag \<sigma>2, \<gamma>)"
      by (smt (verit, best) \<open>Some ty = variables \<Delta> x\<close> agreement.exhaust_sel agreement.sel assms(1) exists_assertI finite_dom_free_varsE fst_conv get_store_def get_trace_def snd_conv)
  qed
qed


(*
lemma havoc_case:
  assumes "wf_set \<Delta> (snd ` SA)"
(* set is well-typed *)
      and "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>ty \<sigma> \<gamma>. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<and> \<Delta> x = Some ty)"
    shows "entails (Stabilize_typed \<Delta> (\<Union>\<omega>\<in>SA. f \<omega>)) (exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)))"
proof (rule entailsI)
  fix \<omega>' assume asm0: "Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<omega>'"
  then obtain \<omega> where "\<omega> \<in> SA" "stabilize \<omega>' \<in> f \<omega>" using Stabilize_def by auto
  then obtain ty \<sigma> \<gamma> where r: "snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<and> \<Delta> x = Some ty"
    using assms(2) by meson
  then obtain v where "v \<in> ty" "stabilize \<omega>' = (upd_ag_partial_map \<sigma> x (Some v), \<gamma>)"
    using \<open>stabilize \<omega>' \<in> f \<omega>\<close> by blast
  moreover have "typed_store \<Delta> \<sigma>" using wf_set_def[of \<Delta> "snd ` SA"] wf_state_def[of \<Delta> "snd \<omega>"] r \<open>\<omega> \<in> SA\<close>
    using assms(1) by auto
  moreover obtain v' where "the_ag \<sigma> x = Some v'"
    by (metis (mono_tags, lifting) calculation(3) domD domI r typed_store_def)

  moreover have "upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v') = \<sigma>"
  proof (rule ag_store_ext)
    fix xa show "the_ag (upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v')) xa = the_ag \<sigma> xa"
      by (metis calculation(4) upd_ag_partial_map_invo upd_ag_partial_map_refl)
  qed
  ultimately show "exists_assert \<Delta> x (Stabilize_typed \<Delta> (snd ` SA)) \<omega>'"
    using exists_assert_def[of _ x "Stabilize_typed \<Delta> (snd ` SA)" \<omega>']
      Stabilize_def[of "snd ` SA" "(upd_ag_partial_map (fst \<omega>') x (Some v), snd \<omega>')"]
    by (metis (mono_tags, opaque_lifting) \<open>\<omega> \<in> SA\<close> agreement.exhaust_sel fst_conv full_add_defined get_store_def image_iff option.distinct(1) prod.exhaust_sel r u_neutral)
qed
*)

lemma Stabilize_equal:
  assumes "wf_set \<Delta> S"
  shows "Set.filter stable (\<langle>Stabilize_typed \<Delta> S\<rangle>) = S"
proof
  show "Set.filter stable (\<langle>Stabilize_typed \<Delta> S\<rangle>) \<subseteq> S"
    by (metis (no_types, lifting) already_stable Stabilize_def inh_def mem_Collect_eq member_filter subsetI)
  show "S \<subseteq> Set.filter sep_algebra_class.stable (\<langle>Stabilize_typed \<Delta> S\<rangle>)"
    by (metis assms member_filter prove_equality_snd_Stabilize_typed \<Delta> subsetI wf_state_def)
qed


text \<open>fst \<omega> is the past (list of all past states), it represents the real choice. Indeed, imagine
1) {\<omega>1} --> {\<omega>'} --> {\<omega>1'}
2) {\<omega>2} --> {\<omega>'} --> {\<omega>2'}
--> {\<omega>1, \<omega>2} --> {\<omega>'} --> {\<omega>1', \<omega>2'}
How do we express the latter with a choice only on the last state?\<close>



(*
lemma Viper_implies_SL_proof_aux:
  fixes f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "wf_set \<Delta> (snd ` SA)"
    shows "\<Delta> \<turnstile> [Stabilize_typed \<Delta> (snd ` SA)] C [Stabilize_typed \<Delta> (\<Union>\<omega>\<in>SA. f \<omega>)]"
  using assms
proof (induct C arbitrary: SA f)
*)

lemma Viper_implies_SL_proof:
  assumes "verifies_rel \<Delta> A C"
      and "wf_abs_stmt \<Delta> C"
      and "self_framing A"
    shows "\<exists>B. \<Delta> \<turnstile> [A] C [B]"
proof -
  define SA :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) set" where "SA = { ([], \<omega>) |\<omega>. stable \<omega> \<and> A \<omega>}"
  define f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
    where "f = (\<lambda>\<omega>. SOME S. red_stmt \<Delta> C (snd \<omega>) S)"
  have "wf_set \<Delta> (snd ` {([], \<omega>) |\<omega>. sep_algebra_class.stable \<omega> \<and> A \<omega>})"
  proof (rule wf_setI)
    fix x assume "x \<in> snd ` {([], \<omega>) |\<omega>. sep_algebra_class.stable \<omega> \<and> A \<omega>}"
    then show "sep_algebra_class.stable x \<and> typed_store \<Delta> (get_store x)"
      sorry
  qed
  moreover have "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
  proof -
    fix \<omega> :: "('v, 'a) abs_state list \<times> ('v, 'a) abs_state" assume "\<omega> \<in> SA"
    then have "snd \<omega> \<in> \<langle>A\<rangle> \<and> stable (snd \<omega>)"
      using in_inh SA_def by force
    then have "\<exists>S. red_stmt \<Delta> C (snd \<omega>) S"
      using assms(1) verifies_rel_def by blast
    then show "red_stmt \<Delta> C (snd \<omega>) (f \<omega>)" using someI_ex f_def
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
  proof (rule self_framing_ext)
    show "self_framing ?A"
      by (meson calculation(2) proofs_are_self_framing)
    show "self_framing A"
      by (simp add: assms(3))
    fix \<omega> :: "('v, 'a) abs_state" assume asm0: "sep_algebra_class.stable \<omega>"
    show "A \<omega> \<Longrightarrow> ?A \<omega>"
    proof -
      assume asm1: "A \<omega>"
      then have "([], \<omega>) \<in> SA"
        using SA_def asm0 by blast
      then show "?A \<omega>"
        by (metis already_stable asm0 Stabilize_def image_eqI snd_conv)
    qed
    assume asm1: "?A \<omega>"
    then have "\<omega> \<in> snd ` SA"
      by (simp add: already_stable asm0 Stabilize_def)
    then show "A \<omega>" using SA_def by force
  qed
  ultimately show ?thesis
    by force
qed




lemma RuleCons:
  assumes "entails A' A"
      and "self_framing A'"
      and "\<Delta> \<turnstile> [A] C [B]"
      and "entails B B'"
      and "self_framing B'"
    shows "\<Delta> \<turnstile> [A'] C [B']"
  sorry

lemma self_framing_true:
  "self_framing atrue"
  by (simp add: atrue_def self_framing_def)

lemma parallel_encoding:
  assumes "verifies_rel \<Delta> A C"
      and "C = (C1 ;; Exhale (astar P1 P2) ;; havoc_list l) ;; (Inhale (astar Q1 Q2);; C2 ;; Exhale B)" (is "C = ?C1 ;; ?C2")
      and "self_framing A"
      and "wf_abs_stmt \<Delta> C"
    shows "\<exists>F. \<Delta> \<turnstile> [A] C1 [F \<otimes> P2 \<otimes> P1] \<and> \<Delta> \<turnstile> [F \<otimes> Q1 \<otimes> Q2] C2 [B] \<and> set l \<inter> free_var F = {}"
proof -

  obtain D where triple: "\<Delta> \<turnstile> [A] ?C1 ;; ?C2 [D]"
    by (metis Viper_implies_SL_proof assms(1) assms(2) assms(3) assms(4))
  then obtain F where F_def: "\<Delta> \<turnstile> [A] ?C1 [F]" "\<Delta> \<turnstile> [F] ?C2 [D]"
    by (meson SL_proof_Seq_elim)
  then obtain FF where "\<Delta> \<turnstile> [A] (C1 ;; Exhale (astar P1 P2)) [FF]" "\<Delta> \<turnstile> [FF] havoc_list l [F]" (* "entails FF F" "free_var F \<subseteq> free_var FF - set l" *)
    by (meson SL_proof_Seq_elim)
  then obtain FFF where "\<Delta> \<turnstile> [A] C1 [FFF]" "\<Delta> \<turnstile> [FFF] Exhale (P1 \<otimes> P2) [FF]"
    by (meson SL_proof_Seq_elim)
  then have "entails FFF (FF \<otimes> (P1 \<otimes> P2))"
    using SL_proof_Exhale_elim by blast
  thm SL_proof_Inhale_elim
  moreover obtain E where "\<Delta> \<turnstile> [F \<otimes> (Q1 \<otimes> Q2)] C2 [E]"  "\<Delta> \<turnstile> [E] Exhale B [D]"
    using SL_proof_Inhale_elim SL_proof_Seq_elim F_def
    by (metis (full_types)) (* long *)

(*
    by (metis SL_proof_Exhale_elim SL_proof_Seq_elim)
*)
  have r1: "\<Delta> \<turnstile> [A] C1 [(F \<otimes> P2) \<otimes> P1]"
  proof (rule RuleCons)
    show "self_framing ((F \<otimes> P2) \<otimes> P1)"
      sorry
    show "entails ((FF \<otimes> P2) \<otimes> P1) (F \<otimes> P2 \<otimes> P1)"
      sorry
    show "entails A A"
      by (simp add: entails_refl)
    show "\<Delta> \<turnstile> [A] C1 [FF \<otimes> P2 \<otimes> P1]"
      sorry
(*
      using \<open>\<Delta> \<turnstile> [A] C1 [FF \<otimes> P2 \<otimes> P1] \<and> \<Delta> \<turnstile> [FF \<otimes> P2 \<otimes> P1] Exhale P1 [FF \<otimes> P2] \<and> framed_by FF P2 \<and> framed_by (FF \<otimes> P2) P1\<close> by blast
*)
    show "self_framing A"
      by (simp add: assms(3))
  qed
  have "\<Delta> \<turnstile> [F] Inhale Q1 ;; Inhale Q2 ;; C2 [atrue \<otimes> B] \<and> framed_by atrue B"
    sorry
(*
    by (metis SL_proof_Exhale_elim SL_proof_Seq_elim)
*)
  then have "\<Delta> \<turnstile> [(F \<otimes> Q1) \<otimes> Q2] C2 [atrue \<otimes> B] \<and> framed_by F Q1 \<and> framed_by (F \<otimes> Q1) Q2"
    by force
  have r2: "\<Delta> \<turnstile> [(F \<otimes> Q1) \<otimes> Q2] C2 [B]"
  proof (rule RuleCons)
    show "entails (F \<otimes> Q1 \<otimes> Q2) ((F \<otimes> Q1) \<otimes> Q2)"
      by (simp add: entails_refl)
    show "self_framing (F \<otimes> Q1 \<otimes> Q2)" sorry
    show "\<Delta> \<turnstile> [F \<otimes> Q1 \<otimes> Q2] C2 [atrue \<otimes> B]"
      using \<open>\<Delta> \<turnstile> [F \<otimes> Q1 \<otimes> Q2] C2 [atrue \<otimes> B] \<and> framed_by F Q1 \<and> framed_by (F \<otimes> Q1) Q2\<close> by blast
    show "entails (atrue \<otimes> B) B"
      sorry
    show "self_framing B"
      sorry
  qed
  then show ?thesis sorry
(*
    using \<open>free_var F \<subseteq> free_var FF - set l\<close> r1 by auto
*)
qed


(*
lemma RuleCons:
  assumes "entails A' A"
      and "self_framing A'"
      and "\<Delta> \<turnstile> [A] C [B]"
      and "entails B B'"
      and "self_framing B'"
    shows "\<Delta> \<turnstile> [A'] C [B']"
  using RuleConsPost RuleConsPre assms(1) assms(2) assms(3) assms(4) assms(5) by blast


lemma self_framing_points_to:
  assumes "self_framing A"
      and "framed_by_exp A r"
    shows "self_framing (astar A (points_to r))"
  sorry

lemma self_framing_points_to_value:
  assumes "self_framing A"
      and "framed_by_exp A r"
      and "framed_by_exp A e"
    shows "self_framing (astar A (points_to_value r e))"
  sorry


lemma self_framing_framed_by:
  assumes "self_framing A"
  shows "framed_by B A"
  by (meson assms framed_by_def self_framing_def)

lemma SL_proof_self_framing:
  assumes "\<Delta> \<turnstile> [A] C [B]"
      and "wf_abs_stmt \<Delta> C"
  shows "self_framing A \<and> self_framing B"
  using assms
proof (induct rule: SL_proof.induct)
  case (RuleIf \<Delta> A C1 B C2 b)
  then show ?case sorry
next
  case (RuleAssert A P va vb)
  then show ?case
    using framed_by_self_framing wf_abs_stmt.simps(4) by blast
next
  case (RuleSkip uu uv)
  then show ?case
    by (simp add: self_framing_true)
next
  case (RuleInhale A P uw ux)
  then show ?case
    by (simp add: framed_by_self_framing)
next
  case (RuleExhale A uy uz P)
  then show ?case
    by (simp add: framed_by_self_framing)
next
  case (RuleSeq \<Delta> A C1 R C2 B)
  then show ?case
    using wf_abs_stmt.simps(6) by blast
next
(*
  case (RuleFrame F \<Delta> A C B)
  then show ?case
    by (meson framed_by_self_framing self_framing_def self_framing_framed_by wf_assertion_def)
next
*)
  case (RuleFieldAssign A r e \<Delta>)
  then show ?case
    using self_framing_points_to self_framing_points_to_value by blast
qed (blast+)


lemma inclusion_star:
  assumes "\<langle>A\<rangle> \<subseteq> \<langle>A'\<rangle>"
      and "\<langle>B\<rangle> \<subseteq> \<langle>B'\<rangle>"
    shows "\<langle>A\<rangle> \<otimes> \<langle>B\<rangle> \<subseteq> \<langle>A'\<rangle> \<otimes> \<langle>B'\<rangle>"
  by (meson assms(1) assms(2) subsetD subsetI x_elem_set_product)


section \<open>Big proof\<close>

lemma SL_proof_implies_Viper:
  assumes "\<Delta> \<turnstile> [A] C [B]"
      and "\<omega> \<in> \<langle>A\<rangle>"
      and "wf_abs_stmt \<Delta> C"
      and "stable \<omega>"
    shows "\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
  using assms
proof (induct arbitrary: \<omega> rule: SL_proof.induct)
  case (RuleIf \<Delta> A C1 B C2 b)
  then show ?case sorry
next
  case (RuleSkip \<Delta> T)
  then show ?case
    using RedSkip by blast
next
  case (RuleInhale A P \<Delta>)
  then have "WdInhale P \<omega>"
    using framed_by_def by fastforce
  then have "red_stmt \<Delta> (Inhale P) \<omega> (Set.filter stable ({\<omega>} \<otimes> P))"
    using RedInhale by auto
  moreover have "{\<omega>} \<otimes> P \<subseteq> \<langle>astar A P\<rangle>"
  proof
    fix \<omega>' assume "\<omega>' \<in> {\<omega>} \<otimes> P"
    then obtain p where "p \<in> P" "Some \<omega>' = \<omega> \<oplus> p"
      by (metis (no_types, lifting) singletonD x_elem_set_product)
    then show "\<omega>' \<in> \<langle>astar A P\<rangle>"
      by (smt (verit, del_insts) RuleInhale.prems(1) inh_def mem_Collect_eq astar_def)
  qed
  ultimately show "\<exists>S. red_stmt \<Delta> (Inhale P) \<omega> S \<and> S \<subseteq> \<langle>astar A P\<rangle>"
    by (metis (no_types, lifting) member_filter subset_iff)
next
  case (RuleExhale A P \<Delta>)
(*
self_framing A
    framed_by A P
    \<omega> \<in> \<langle>astar A P\<rangle>
*)
  then obtain \<omega>' a where "a \<in> P" "Some \<omega> = \<omega>' \<oplus> a" "\<omega>' \<in> \<langle>A\<rangle>"
    by (smt (verit) inh_def mem_Collect_eq astar_def)
  then obtain \<omega>'' where "Some \<omega>'' = \<omega>' \<oplus> |\<omega>|"
    by (metis commutative minus_equiv_def_any_elem)
  let ?\<omega>' = "stabilize \<omega>''"
  have "stable ?\<omega>'"
    by (simp add: stabilize_is_stable)
  moreover have "Some \<omega> = \<omega>'' \<oplus> a"
    by (smt (verit) \<open>Some \<omega> = \<omega>' \<oplus> a\<close> \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> asso1 commutative core_is_smaller)
  then have "Some \<omega> = ?\<omega>' \<oplus> a"
    sorry
  ultimately have "red_stmt \<Delta> (Exhale P) \<omega> {?\<omega>'}"
    using \<open>a \<in> P\<close> full_add_charact(1) RedExhale by blast
  moreover have "?\<omega>' \<in> \<langle>A\<rangle>"
    sorry
  ultimately show "\<exists>S. red_stmt \<Delta> (Exhale P) \<omega> S \<and> S \<subseteq> \<langle>A\<rangle>"
    by (meson empty_subsetI insert_subsetI)
next
  case (RuleSeq \<Delta> A C1 R C2 B)
  then obtain SA where "red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>"
    using wf_abs_stmt.simps(6) by blast
  let ?f = "\<lambda>x. (SOME Sx. red_stmt \<Delta> C2 x Sx \<and> Sx \<subseteq> \<langle>B\<rangle>)"
  have r: "\<And>x. x \<in> SA \<Longrightarrow> red_stmt \<Delta> C2 x (?f x) \<and> ?f x \<subseteq> \<langle>B\<rangle>"
  proof -
    fix x assume "x \<in> SA"
    show "red_stmt \<Delta> C2 x (?f x) \<and> ?f x \<subseteq> \<langle>B\<rangle>"
    proof (rule someI_ex)
      show "\<exists>xa. red_stmt \<Delta> C2 x xa \<and> xa \<subseteq> \<langle>B\<rangle>"
        using RuleSeq.hyps(4) RuleSeq.prems(2) RuleSeq.prems(3) \<open>red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>\<close> \<open>x \<in> SA\<close> red_stable wf_abs_stmt.simps(6) by blast
    qed
  qed
  let ?S = "Union (?f ` SA)"
  have "sequential_composition \<Delta> SA C2 ?S"
    using SeqComp r by presburger
  then have "red_stmt \<Delta> (Seq C1 C2) \<omega> ?S"
    by (meson RedSeq \<open>red_stmt \<Delta> C1 \<omega> SA \<and> SA \<subseteq> \<langle>R\<rangle>\<close>)
  moreover have "?S \<subseteq> \<langle>B\<rangle>"
    using r by blast
  ultimately show "\<exists>S. red_stmt \<Delta> (Seq C1 C2) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
    by meson
next
(*
  case (RuleFrame F \<Delta> A C B)
  then obtain a f where "Some \<omega> = a \<oplus> f" "a \<in> \<langle>A\<rangle>" "f \<in> \<langle>F\<rangle>" "stable \<omega>"
    by (smt (verit, best) inh_def mem_Collect_eq astar_def)
  then obtain aa ff where aa_ff: "ff \<in> \<langle>F\<rangle>" "stable ff" "Some \<omega> = aa \<oplus> ff" "stable aa" "aa \<in> \<langle>A\<rangle>" "dom_vars ff \<inter> modif C = {}" sorry
  then obtain S where "red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>"
    using RuleFrame.hyps(3) RuleFrame.prems(2) by presburger
  then have "Some \<omega> = aa \<oplus> (fst \<omega>, get_state ff)"
    by (metis Pair_inject \<open>Some \<omega> = aa \<oplus> ff\<close> commutative full_add_charact(1) full_state_ext get_state_def get_store_def prod.collapse)
  then obtain S' where r: "red_stmt \<Delta> C \<omega> S' \<and> S' \<subseteq> S \<otimes> UNIV \<times> {get_state ff}"
    using frame_rule_aux(1)[of \<Delta> C aa S "get_state ff" \<omega>]
    by (metis RuleFrame.prems(2) \<open>red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>\<close> \<open>sep_algebra_class.stable aa\<close> \<open>sep_algebra_class.stable ff\<close> get_state_def stable_snd)

  moreover have "S' \<subseteq> \<langle>astar B F\<rangle>"
  proof
    fix \<omega>' assume "\<omega>' \<in> S'"
    then have "\<omega>' \<in> S \<otimes> UNIV \<times> {get_state ff}"
      using calculation by auto
    then obtain b s where "Some \<omega>' = b \<oplus> (s, get_state ff)" "b \<in> S"
      by (smt (verit, best) Sigma_cong get_state_def in_univ prod.collapse x_elem_set_product)
    then have "s = fst \<omega>' \<and> b \<in> \<langle>B\<rangle>"
      by (metis \<open>red_stmt \<Delta> C aa S \<and> S \<subseteq> \<langle>B\<rangle>\<close> commutative fst_conv full_add_charact(1) full_state_ext get_state_def get_store_def snd_conv subsetD)
    moreover have "(s, get_state ff) \<in> \<langle>F\<rangle>"
    proof -
      have "\<And>x. is_free_var F x \<Longrightarrow> the_ag s x = get_store ff x"
      proof -
        fix x :: string
        assume "is_free_var F x"
        then have "x \<notin> modif C"
          using RuleFrame.hyps(4) free_var_def by fastforce
        then have "get_store \<omega> x = get_store \<omega>' x"
          using \<open>\<omega>' \<in> S'\<close> r only_modif_can_be_modified by blast
        then show "the_ag s x = get_store ff x"
          by (metis aa_ff(3) calculation full_add_charact(1) full_add_defined get_store_def)
      qed
      then show ?thesis
        by (metis aa_ff(1) get_state_def get_store_def inh_def mem_Collect_eq prod.collapse same_on_free_var(2))
    qed
    ultimately show "\<omega>' \<in> \<langle>astar B F\<rangle>"
      by (smt (verit) \<open>Some \<omega>' = b \<oplus> (s, get_state ff)\<close> inh_def mem_Collect_eq astar_def)
  qed
  ultimately show ?case
    by blast
*)
next
(*
  case (RuleConsPre \<Delta> A' A T C B)
  then show ?case
    by (meson entails_def subsetD)
next
  case (RuleConsPost B B' \<Delta> A C)
(*
    entails B B'
    self_framing B'
     \<Delta> \<turnstile> [A] C [B]
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> wf_abs_stmt \<Delta> C \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> C ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    \<omega> \<in> \<langle>A\<rangle>
    wf_abs_stmt \<Delta> C
    sep_algebra_class.stable \<omega>
*)
  then obtain S where "red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
    by presburger
  then show "\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B'\<rangle>"
    by (meson RuleConsPost.hyps(1) dual_order.trans entails_def)
next
*)
  case (RuleFieldAssign A r e \<Delta>)
  then show ?case sorry
next
  case (RuleAssert A P \<Delta>)
  then show ?case sorry
next
  case (RuleHavoc A x \<Delta>)
  then show ?case sorry
(*
next
  case (RuleEquiv)
  then show ?case sorry
*)
qed




lemma sequential_compo_obtain_subset:
  assumes "sequential_composition \<Delta> S C S'"
      and "\<omega> \<in> S"
    shows "\<exists>S''. S'' \<subseteq> S' \<and> red_stmt \<Delta> C \<omega> S''"
  using assms(1) assms(2) by blast

definition self_framing_closure where
  "self_framing_closure S = \<lparr> = (\<lambda>\<omega>. stabilize \<omega> \<in> S), WdInhale = (\<lambda>_. True) \<rparr>"

lemma Viper_implies_SL_proof_concl:
  assumes "\<And>\<omega>. (\<exists>S. red_stmt \<Delta> C \<omega> S)"
      and "wf_abs_stmt \<Delta> C"
  shows "\<Delta> \<turnstile> [atrue] C [atrue]"
  sorry




lemma general_concurrency:
  assumes "\<And>\<omega>. A \<omega> \<Longrightarrow> (\<exists>S. red_stmt \<Delta> ((C1 ;; Exhale P ;; Havoc x) ;; (Inhale Q ;; C2)) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>)"
      and "wf_abs_stmt \<Delta> (C1 ;; Exhale P ;; Havoc x ;; (Inhale Q ;; C2))"

(*
(*  assumes "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P ;; Havoc x) ;; (Inhale Q ;; C' ;; Exhale B)) \<omega> S" *)
  assumes "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P) ;; (Inhale Q ;; C' ;; Exhale B)) \<omega> S"
*)

(* shows "\<exists>F. \<Delta> \<turnstile> [A] C [astar P F] \<and> x \<notin> free_var F \<and> \<Delta> \<turnstile> [astar Q F] C' [B]" *)
  shows "\<exists>F. \<Delta> \<turnstile> [A] C1 [astar F P] \<and> \<Delta> \<turnstile> [astar F Q] C2 [B]"

proof -
  let ?C1 = "C1 ;; Exhale P ;; Havoc x"
  let ?C2 = "Inhale Q ;; C2"
  have r0: "\<Delta> \<turnstile> [A] ?C1 ;; ?C2 [B]"
    sorry
(*
    using Viper_implies_SL_proof_concl assms(1) assms(2) by blast
*)
  then obtain F where "\<Delta> \<turnstile> [A] ?C1 [F]" "\<Delta> \<turnstile> [F] ?C2 [B]"
    using SL_proof_Seq_elim[of \<Delta> A ?C1 ?C2 B] by auto
  then have 2: "\<Delta> \<turnstile> [astar F Q] C2 [B]"
    by blast
  moreover obtain R where "\<Delta> \<turnstile> [A] C1 ;; Exhale P [R]" "\<Delta> \<turnstile> [R] Havoc x [F]"
    by (meson SL_proof_Seq_elim \<open>\<Delta> \<turnstile> [A] C1 ;; Exhale P ;; Havoc x [F]\<close>)
  then have "\<Delta> \<turnstile> [A] C1 [astar R P] \<and> entails R F \<and> x \<notin> free_var F"
    by blast

  then show ?thesis sorry
(*
Here I can use the Cons Rule 
Same for frame rule
*)
qed





(*  obtain SF where "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P) ;; Havoc x) \<omega> SF" *)
  obtain SF where "red_stmt \<Delta> (Inhale A ;; C ;; Exhale P) \<omega> SF"
    "sequential_composition \<Delta> SF (Inhale Q ;; C' ;; Exhale B) S"
    by (meson assms red_stmt_Seq_elim)
  let ?F = "self_framing_closure SF"
(*
theorem Viper_implies_SL_proof_more_precise:
 sequential_composition ??\<Delta> ?E ?SA ?C ?SB \<Longrightarrow> wf_abs_stmt \<Delta> ?C \<Longrightarrow>  ?Pr, ?\<Delta> \<turnstile> [self_framing_closure ?SA] ?C [self_framing_closure ?SB]
*)


  have "\<Delta> \<turnstile> [A] C [astar P ?F]"
  proof (rule 


lemma Viper_implies_SL_proof_more_precise:
  assumes "sequential_composition \<Delta> SA C SB"
      and "wf_abs_stmt \<Delta> C"
  shows "\<Delta> \<turnstile> [self_framing_closure SA] C [self_framing_closure SB]"
  using assms
proof (induct C arbitrary: SA SB)
  case (Inhale P)
(*
    sequential_composition \<Delta> SA (Inhale P) SB
    wf_abs_stmt \<Delta> (Inhale P)
*)
  show "\<Delta> \<turnstile> [self_framing_closure SA] Inhale P [self_framing_closure SB]"
    using Inhale(1)
  proof (rule sequential_composition_elim)
    fix f assume asm0: "SB = \<Union> (f ` SA)" "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> (Inhale P) \<omega> (f \<omega>)"
    have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = Set.filter stable ({\<omega>} \<otimes> P)"
      using asm0(2) by blast
    moreover have "SB = Set.filter stable (SA \<otimes> P)"
      sorry

    show "\<Delta> \<turnstile> [self_framing_closure SA] Inhale P [self_framing_closure SB]"
    proof (rule RuleEquiv)
      show "\<Delta> \<turnstile> [self_framing_closure SA] Inhale P [astar (self_framing_closure SA) P]"
      proof (rule RuleInhale)
        show "self_framing (self_framing_closure SA)"
          by (metis select_convs(2) self_framingI self_framing_closure_def)
        show "framed_by (self_framing_closure SA) P"
        proof (rule framed_byI)
          fix \<omega> assume "\<omega> \<in> \<langle>self_framing_closure SA\<rangle>"
          then have "stabilize \<omega> \<in> SA"
            by (metis inh_def mem_Collect_eq self_framing_closure_def)
          then have "red_stmt \<Delta> (Inhale P) (stabilize \<omega>) (f (stabilize \<omega>))"
            using asm0(2) by auto
          then have "WdInhale P (stabilize \<omega>)"
            by blast
          then show "WdInhale P \<omega>"
            using Inhale.prems(2) max_projection_prop_stable_stabilize mpp_smaller wf_assertionE wf_abs_stmt.simps(2) by blast
        qed
      qed
      show "equiv (astar (self_framing_closure SA) P) (self_framing_closure SB)"
      proof (rule equivI)
        fix \<omega> assume asm1: "(astar (self_framing_closure SA) P) \<omega>"
        then obtain a p where "Some \<omega> = a \<oplus> p" "stabilize a \<in> SA" "p \<in> P"
          by (smt (verit, best) in_inh astar_def self_framing_closure_def)

        then have "Some (stabilize \<omega>) = stabilize a \<oplus> p" sorry
        then have "stabilize \<omega> \<in> SB"
          by (metis (no_types, lifting) UN_iff \<open>p \<in> P\<close> \<open>stabilize a \<in> SA\<close> asm0(1) is_in_set_sum member_filter r stabilize_is_stable)
        then show "(self_framing_closure SB) \<omega>"
          by (metis self_framing_closure_def)
      next
        fix \<omega> assume asm1: "(self_framing_closure SB) \<omega>"
        then have "stabilize \<omega> \<in> SB"
          by (metis self_framing_closure_def)
        then obtain a p where "a \<in> SA" "p \<in> P" "Some (stabilize \<omega>) = a \<oplus> p"
          by (metis (no_types, lifting) \<open>SB = Set.filter sep_algebra_class.stable (SA \<otimes> P)\<close> member_filter x_elem_set_product)

        then obtain aa where "Some aa = stabilize a \<oplus> |\<omega>|"
          by (metis (no_types, opaque_lifting) asso2 commutative core_is_smaller option.exhaust_sel stabilize_is_smaller)
        moreover have "Some \<omega> = stabilize \<omega> \<oplus> |\<omega>|" sorry (* Should be an axiom *)

        ultimately have "Some \<omega> = aa \<oplus> p" 
          sorry
(* should be provable *)

        moreover have "stabilize aa = stabilize a" sorry (* comes from stabilize def *)
        then have "(self_framing_closure SA) aa"
          by (metis (no_types, lifting) \<open>a \<in> SA\<close> select_convs(2) self_framing_closure_def self_framing_sat_stabilize self_framingI stabilize_is_stable already_stable)

        ultimately show "(astar (self_framing_closure SA) P) \<omega>"
          by (smt (verit, del_insts) \<open>p \<in> P\<close> inh_def mem_Collect_eq astar_def)
      qed
      show "local.equiv (self_framing_closure SA) (self_framing_closure SA)"
        by (simp add: local.equiv_def)
      show "self_framing (self_framing_closure SA)"
        using Inhale.prems(2) SL_proof_self_framing \<open>\<Delta> \<turnstile> [self_framing_closure SA] Inhale P [astar (self_framing_closure SA) P]\<close> by blast
      show "self_framing (self_framing_closure SB)"
        by (simp add: self_framingI self_framing_closure_def)
    qed
  qed
next
  case (Exhale x)
  then show ?case sorry
next
  case (Assert x)
  then show ?case sorry
next
  case (If x1a C1 C2)
  then show ?case sorry
next
  case (Seq C1 C2)
  then show ?case sorry
next
  case (LocalAssign x1a x2a)
  then show ?case sorry
next
  case (FieldAssign x1a x2a)
  then show ?case sorry
next
  case (Havoc x)
  then show ?case sorry
next
  case (MethodCall x1a x2a x3a)
  then show ?case sorry
next
  case (While x1a x2a C)
  then show ?case sorry
next
  case (Scope x1a x2a C)
  then show ?case sorry
next
  case Skip
  then show ?case sorry
qed







lemma general_concurrency:   
(*  assumes "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P ;; Havoc x) ;; (Inhale Q ;; C' ;; Exhale B)) \<omega> S" *)
  assumes "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P) ;; (Inhale Q ;; C' ;; Exhale B)) \<omega> S"

(* shows "\<exists>F. \<Delta> \<turnstile> [A] C [astar P F] \<and> x \<notin> free_var F \<and> \<Delta> \<turnstile> [astar Q F] C' [B]" *)
  shows "\<exists>F. \<Delta> \<turnstile> [A] C [astar P F] \<and> \<Delta> \<turnstile> [astar Q F] C' [B]"

proof -
(*  obtain SF where "red_stmt \<Delta> ((Inhale A ;; C ;; Exhale P) ;; Havoc x) \<omega> SF" *)
  obtain SF where "red_stmt \<Delta> (Inhale A ;; C ;; Exhale P) \<omega> SF"
    "sequential_composition \<Delta> SF (Inhale Q ;; C' ;; Exhale B) S"
    by (meson assms red_stmt_Seq_elim)
  let ?F = "self_framing_closure SF"
(*
theorem Viper_implies_SL_proof_more_precise:
 sequential_composition ??\<Delta> ?E ?SA ?C ?SB \<Longrightarrow> wf_abs_stmt \<Delta> ?C \<Longrightarrow>  ?Pr, ?\<Delta> \<turnstile> [self_framing_closure ?SA] ?C [self_framing_closure ?SB]
*)


  have "\<Delta> \<turnstile> [A] C [astar P ?F]"
  proof (rule 

(* Ignoring the Havoc for the moment *)

(*
| RedHavoc: "\<Delta> x = Some ty \<Longrightarrow> red_stmt \<Delta> (Havoc x) (\<sigma>, \<gamma>) ({(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty})"
*)
 

lemma Viper_implies_SL_proof:
  assumes "\<And>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> stable \<omega> \<Longrightarrow> (\<exists>S. red_stmt \<Delta> C \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>)"
      and "wf_abs_stmt \<Delta> C"
      and "self_framing A"
      and "self_framing B"
  shows "\<Delta> \<turnstile> [A] C [B]"
  using assms
proof (induct C arbitrary: A B)
  case (Assert P)
  then show ?case sorry
next
  case (Inhale P)
(*
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Inhale P) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    wf_abs_stmt \<Delta> (Inhale P)
    self_framing A
    self_framing B
*)
  show "\<Delta> \<turnstile> [A] Inhale P [B]"
  proof (rule RuleConsPost)
    show "\<Delta> \<turnstile> [A] Inhale P [astar A P]"
    proof (rule RuleInhale)
      show "self_framing A"
        by (simp add: Inhale.prems(3))
      show "framed_by A P"
      proof (rule framed_byI)
        fix \<omega> assume asm0: "\<omega> \<in> \<langle>A\<rangle>"
        then have "stabilize \<omega> \<in> \<langle>A\<rangle>"
          by (metis Inhale.prems(3) inh_def mem_Collect_eq self_framing_sat_stabilize)
        then obtain S where "red_stmt \<Delta> (Inhale P) (stabilize \<omega>) S"
          by (meson Inhale.prems(1) stabilize_is_stable)
        then show "WdInhale P \<omega>"
          by (metis atrue_def select_convs(2) red_stmt_Inhale_elim stabilize_is_smaller stabilize_is_stable already_stable wd_charact)
      qed
    qed
    show "self_framing B"
      using Inhale.prems(4) by auto
    show "entails (astar A P) B"
    proof (rule entailsI)
      fix \<omega> assume "(astar A P) \<omega>"
      then obtain a p where "Some \<omega> = a \<oplus> p" "A a" "P p"
        using astar_def by fastforce

(*
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Inhale P) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>

*)
      then obtain S where "red_stmt \<Delta> (Inhale P) (stabilize a) S \<and> S \<subseteq> \<langle>B\<rangle>"
        by (meson Inhale.prems(1) Inhale.prems(3) in_inh self_framing_sat_stabilize stabilize_is_stable)
      then have "Set.filter stable ({stabilize a} \<otimes> P) \<subseteq> \<langle>B\<rangle>"
        by blast
(* Should come from:
- P is framed by A
*)
      moreover obtain pp where "Some (stabilize \<omega>) = stabilize a \<oplus> pp" "pp \<in> P"
        sorry
      then have "stabilize \<omega> \<in> Set.filter stable ({stabilize a} \<otimes> P)"
        by (simp add: is_in_set_sum stabilize_is_stable)
      then have "B (stabilize \<omega>)"
        using calculation inh_def by fastforce
      then show "B \<omega>"
        using Inhale.prems(4) self_framing_sat_stabilize by auto
    qed
  qed
next
  case (Exhale P)
(*
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Exhale P) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    wf_abs_stmt \<Delta> (Exhale P)
    self_framing A
    self_framing B

| RedExhale: "\<lbrakk> a \<in> \<langle>A\<rangle> ; Some \<omega> = \<omega>' \<oplus> a ; stable \<omega>'; get_store \<omega> = get_store \<omega>' \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Exhale A) \<omega> {\<omega>'}"

*)
  let ?remaining = "\<lambda>\<omega>. SOME \<omega>'. \<exists>a \<in> P. Some \<omega> = \<omega>' \<oplus> a \<and> stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>"
  have remaining_prop: "\<And>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow>
  (\<exists>a \<in> P. Some \<omega> = ?remaining \<omega> \<oplus> a \<and> stable (?remaining \<omega>) \<and> get_store \<omega> = get_store (?remaining \<omega>) \<and> ?remaining \<omega> \<in> \<langle>B\<rangle>)"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> \<langle>A\<rangle>" "sep_algebra_class.stable \<omega>"
    then obtain S where "red_stmt \<Delta> (Exhale P) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
      using Exhale.prems(1) by presburger

    then obtain a \<omega>' where "a \<in> P" "Some \<omega> = \<omega>' \<oplus> a" "stable \<omega>'" "get_store \<omega> = get_store \<omega>'" "\<omega>' \<in> S"
      by auto
    then show "\<exists>a \<in> P. Some \<omega> = ?remaining \<omega> \<oplus> a \<and> stable (?remaining \<omega>) \<and> get_store \<omega> = get_store (?remaining \<omega>) \<and> ?remaining \<omega> \<in> \<langle>B\<rangle>"
      using someI_ex[of "\<lambda>\<omega>'. \<exists>a \<in> P. Some \<omega> = \<omega>' \<oplus> a \<and> stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>"]
      using \<open>red_stmt \<Delta> (Exhale P) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>\<close> by blast
  qed

  let ?A = "\<lparr> = (\<lambda>\<omega>'. \<exists>\<omega> \<in> \<langle>A\<rangle>. stable \<omega> \<and> \<omega>' = ?remaining \<omega>), WdInhale = (\<lambda>_. True) \<rparr>"

  have sfA: "self_framing ?A"
    using self_framing_def by fastforce

  show "\<Delta> \<turnstile> [A] Exhale P [B]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile> [astar ?A P] Exhale P [?A]"
    proof (rule RuleExhale)
      show "self_framing ?A" using sfA by simp
      show "framed_by ?A P"
      proof (rule framed_byI)
        fix \<omega>' assume "\<omega>' \<in> ?A"
        then obtain \<omega> where "\<omega> \<in> \<langle>A\<rangle>" "stable \<omega>" "\<omega>' = ?remaining \<omega>"
          using inh_def
          by (smt (verit) mem_Collect_eq)
        then show "WdInhale P \<omega>'" (* Unclear why? *)
          sorry
      qed
    qed
    show "self_framing A" using Exhale by blast
    show "self_framing B" using Exhale by blast
    show "entails A (astar ?A P)"
    proof (rule entailsI)
      fix \<omega> assume asm0: "A \<omega>"
      let ?\<omega> = "stabilize \<omega>"
      have "A ?\<omega>"
        using Exhale.prems(3) asm0 self_framing_sat_stabilize by blast
      then obtain p where "p \<in> P" "Some (stabilize \<omega>) = ?remaining ?\<omega> \<oplus> p" "stable (?remaining ?\<omega>)"
        "get_store ?\<omega> = get_store (?remaining ?\<omega>)" "?remaining ?\<omega> \<in> \<langle>B\<rangle>"
        using remaining_prop stabilize_is_stable inh_def
        by (smt (verit, best) Eps_cong in_inh)
      moreover have "?A (?remaining ?\<omega>)"
        using \<open>A (stabilize \<omega>)\<close> in_inh stabilize_is_stable by fastforce
      ultimately have "(astar ?A P) ?\<omega>"
        by (smt (verit) inh_def mem_Collect_eq astar_def)
      moreover have "framed_by ?A P"
      proof (rule framed_byI)
        fix \<omega>
        assume "\<omega> \<in> ?A"
        let ?\<omega> = "stabilize \<omega>"
        show "WdInhale P \<omega>" sorry
(* Unclear why *)
      qed
      ultimately show "(astar ?A P) \<omega>"
        using Exhale.prems(2) SL_proof_self_framing \<open>\<Delta> \<turnstile> [astar \<lparr>= \<lambda>\<omega>'. \<exists>\<omega>\<in>\<langle>A\<rangle>. sep_algebra_class.stable \<omega> \<and> \<omega>' = (SOME \<omega>'. \<exists>a\<in>P. Some \<omega> = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>), WdInhale = \<lambda>_. True\<rparr> P] Exhale P [\<lparr>= \<lambda>\<omega>'. \<exists>\<omega>\<in>\<langle>A\<rangle>. sep_algebra_class.stable \<omega> \<and> \<omega>' = (SOME \<omega>'. \<exists>a\<in>P. Some \<omega> = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>), WdInhale = \<lambda>_. True\<rparr>]\<close> self_framing_sat_stabilize by blast
    qed
    show "entails ?A B" sorry

  qed
next
  case (If b C1 C2)
  show ?case
  proof (rule RuleIf)
    show "\<Delta> \<turnstile> [astar (pure_typed \<Delta> b) A] C1 [B]" sorry
    show "\<Delta> \<turnstile> [astar (pure_typed \<Delta>_not b) A] C2 [B]" sorry
  qed
next
  case (Seq C1 C2)
(*
    (\<And>\<omega>. \<omega> \<in> \<langle>?A7\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> \<exists>S. red_stmt \<Delta> C1 \<omega> S \<and> S \<subseteq> \<langle>?B7\<rangle>) \<Longrightarrow>
    wf_abs_stmt \<Delta> C1 \<Longrightarrow> self_framing ?A7 \<Longrightarrow> self_framing ?B7 \<Longrightarrow>  \<Delta> \<turnstile> [?A7] C1 [?B7]
    (\<And>\<omega>. \<omega> \<in> \<langle>?A7\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> \<exists>S. red_stmt \<Delta> C2 \<omega> S \<and> S \<subseteq> \<langle>?B7\<rangle>) \<Longrightarrow>
    wf_abs_stmt \<Delta> C2 \<Longrightarrow> self_framing ?A7 \<Longrightarrow> self_framing ?B7 \<Longrightarrow>  \<Delta> \<turnstile> [?A7] C2 [?B7]
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Seq C1 C2) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    wf_abs_stmt \<Delta> (Seq C1 C2)
    self_framing A
    self_framing B
*)
  let ?r = "\<lambda>\<omega>. SOME S. red_stmt \<Delta> C1 \<omega> S \<and> (\<exists>S'. sequential_composition \<Delta> S C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"
  have r_prop: "\<And>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> red_stmt \<Delta> C1 \<omega> (?r \<omega>) \<and> (\<exists>S'. sequential_composition \<Delta> (?r \<omega>) C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> \<langle>A\<rangle>" "sep_algebra_class.stable \<omega>"
    then obtain S' where "red_stmt \<Delta> (Seq C1 C2) \<omega> S' \<and> S' \<subseteq> \<langle>B\<rangle>"
      using Seq.prems(1) by presburger
    then obtain S where "red_stmt \<Delta> C1 \<omega> S \<and> sequential_composition \<Delta> S C2 S'"
      by (meson red_stmt_Seq_elim)
    then have "red_stmt \<Delta> C1 \<omega> S \<and> (\<exists>S'. sequential_composition \<Delta> S C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"
      by (meson \<open>red_stmt \<Delta> (Seq C1 C2) \<omega> S' \<and> S' \<subseteq> \<langle>B\<rangle>\<close>)
    then show "red_stmt \<Delta> C1 \<omega> (?r \<omega>) \<and> (\<exists>S'. sequential_composition \<Delta> (?r \<omega>) C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"
      using someI_ex[of "\<lambda>S. red_stmt \<Delta> C1 \<omega> S \<and> (\<exists>S'. sequential_composition \<Delta> S C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"]
      by meson
  qed
  define r where "r = ?r"
  let ?R = "\<lparr> = (\<lambda>\<omega>'. \<exists>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<and> stable \<omega> \<and> \<omega>' \<in> r \<omega>), WdInhale = (\<lambda>_. True) \<rparr>"

  have r_cons: "\<And>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> r \<omega> \<subseteq> \<langle>?R\<rangle>"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> \<langle>A\<rangle>" "sep_algebra_class.stable \<omega>"
    then have "red_stmt \<Delta> C1 \<omega> (r \<omega>) \<and> (\<exists>S'. sequential_composition \<Delta> (r \<omega>) C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>)"
      using r_prop r_def by blast
    then show "r \<omega> \<subseteq> \<langle>?R\<rangle>"
      by (metis (no_types, lifting) asm0(1) asm0(2) in_inh subsetI)
  qed

  have sfR: "self_framing ?R"
    by (simp add: self_framing_def)

(*
?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Seq C1 C2) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
*)
  show "\<Delta> \<turnstile> [A] Seq C1 C2 [B]"
  proof (rule RuleSeq)
    show "\<Delta> \<turnstile> [A] C1 [?R]"
    proof (rule Seq(1))
      fix \<omega>
      assume asm0: "\<omega> \<in> \<langle>A\<rangle>" "sep_algebra_class.stable \<omega>"
      then show "\<exists>S. red_stmt \<Delta> C1 \<omega> S \<and> S \<subseteq> \<langle>?R\<rangle>"
        using r_cons r_def r_prop by blast
    next
      show "wf_abs_stmt \<Delta> C1"
        using Seq.prems(2) by auto
      show "self_framing ?R"
        using sfR by blast
    qed (simp add: Seq.prems)
    show "\<Delta> \<turnstile> [?R] C2 [B]"
    proof (rule Seq(2))
      fix \<omega>'
      assume asm0: "\<omega>' \<in> \<langle>?R\<rangle>" "sep_algebra_class.stable \<omega>'"
      then obtain \<omega> where "stable \<omega>" "\<omega> \<in> \<langle>A\<rangle>" "\<omega>' \<in> r \<omega>"
        by (smt (verit, del_insts) inh_def mem_Collect_eq)
      then obtain S' where "sequential_composition \<Delta> (?r \<omega>) C2 S' \<and> S' \<subseteq> \<langle>B\<rangle>"
        using r_prop by presburger
      then show "\<exists>S. red_stmt \<Delta> C2 \<omega>' S \<and> S \<subseteq> \<langle>B\<rangle>"
        by (metis (no_types, lifting) \<open>\<omega>' \<in> r \<omega>\<close> r_def sequential_compo_obtain_subset subset_iff)
    next
      show "wf_abs_stmt \<Delta> C2"
        using Seq.prems(2) by auto
      show "self_framing B"
        by (simp add: Seq.prems(4))
      show "self_framing ?R"
        using sfR by blast
    qed
  qed
next
  case (LocalAssign x1a x2a)
  then show ?case sorry
next
  case (FieldAssign x1a x2a)
  then show ?case sorry
next
  case (Havoc x)
(*
    ?\<omega>7 \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable ?\<omega>7 \<Longrightarrow> \<exists>S. red_stmt \<Delta> (Havoc x) ?\<omega>7 S \<and> S \<subseteq> \<langle>B\<rangle>
    wf_abs_stmt \<Delta> (Havoc x)
    self_framing A
    self_framing B
*)
(*
| RedHavoc: "\<Delta> x = Some ty \<Longrightarrow> red_stmt \<Delta> (Havoc x) (\<sigma>, \<gamma>) ({(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty})"
*)
(* We need A such that... *)

  show "\<Delta> \<turnstile> [A] Havoc x [B]"
  proof (rule RuleConsPre)
next
  case (MethodCall x1a x2a x3a)
  then show ?case sorry
next
  case (While x1a x2a C)
  then show ?case sorry
next
  case (Scope x1a x2a C)
  then show ?case sorry
next
  case Skip
  show "\<Delta> \<turnstile> [A] Skip [B]"
  proof (rule RuleConsPost)
    show "\<Delta> \<turnstile> [A] Skip [A]"
      using RuleSkip Skip.prems(3) by auto
    show "entails A B"
    proof (rule entailsI)
      fix \<omega> assume asm0: "A \<omega>"
      then have "A (stabilize \<omega>)"
        using Skip.prems(3) self_framing_sat_stabilize by blast
      then obtain S where "red_stmt \<Delta> Skip (stabilize \<omega>) S \<and> S \<subseteq> \<langle>B\<rangle>"
        by (meson Skip.prems(1) in_inh stabilize_is_stable)
      then have "stabilize \<omega> \<in> \<langle>B\<rangle>"
        by blast
      then show "B \<omega>"
        by (metis Skip.prems(4) inh_def mem_Collect_eq self_framing_sat_stabilize)
    qed
  qed (auto simp add: Skip)
qed









lemma Viper_implies_SL_proof:
  assumes "\<And>\<omega>. \<omega> \<in> inh \<Delta> A \<Longrightarrow> (\<exists>S. red_stmt \<Delta> Modular C \<omega> S \<and> S \<subseteq> inh \<Delta> B)"
  shows "\<Delta> \<turnstile> A C B"
  using assms
proof (induct C arbitrary: A B)
  case Skip
  have "inh \<Delta> A \<subseteq> inh \<Delta> B"
  proof (rule subsetI)
    fix x assume "x \<in> inh \<Delta> A"
    then obtain S where "red_stmt \<Delta> Modular Skip x S \<and> S \<subseteq> inh \<Delta> B"
      using Skip by presburger
    then show "x \<in> inh \<Delta> B"using red_stmt_Skip_elim
      by blast
  qed
  show "\<Delta> \<turnstile> {A} Skip {B}"
  proof (rule RuleConsPre)
    show "entails \<Delta> A B"
      using \<open>inh \<Delta> A \<subseteq> inh \<Delta> B\<close> entails_def by auto
  qed (insert RuleSkip; blast)
next
  case (Inhale x)
  then show ?case sorry
next
  case (Exhale x)
  then show ?case sorry
next
  case (Assert x)
  then show ?case sorry
next
  case (Assume x)
  then show ?case sorry
next
  case (If x1a C1 C2)
  then show ?case sorry
next
  case (Seq C1 C2)
  then show ?case sorry
next
  case (LocalAssign x1a x2a)
  then show ?case sorry
next
  case (FieldAssign x1a x2a x3a)
  then show ?case sorry
next
  case (Havoc x)
  then show ?case sorry
next
  case (MethodCall x1a x2a x3a)
  then show ?case sorry
next
  case (While x1a x2a C)
  then show ?case sorry
next
  case (Unfold x1a x2a x3a)
  then show ?case sorry
next
  case (Fold x1a x2a x3a)
  then show ?case sorry
next
  case (Package x1a x2a)
  then show ?case sorry
next
  case (Apply x1a x2a)
  then show ?case sorry
next
  case (Label x)
  then show ?case sorry
next
  case (Scope x1a C)
  then show ?case sorry
qed



(*

datatype stmt =

\<comment>\<open>Assertions\<close>
  Inhale assertion | Exhale assertion | Assert assertion | Assume assertion
\<comment>\<open>assume A not valid in the theoretical semantics\<close>

\<comment>\<open>Control structures\<close>
| If pure_exp stmt stmt | Seq stmt stmt

\<comment>\<open>Assignments\<close>
| LocalAssign var pure_exp | FieldAssign pure_exp field_ident pure_exp | Havoc var

\<comment>\<open>Calls and loops\<close>
| MethodCall "var list" method_ident "var list" (* y := m(x) *)
| While pure_exp assertion stmt (* While (b) invariant I {s} *)

\<comment>\<open>Verifier directives\<close>
| Unfold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Fold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Package assertion assertion
| Apply assertion assertion

\<comment>\<open>Misc\<close>
| Label label | Scope "vtyp list" stmt | Skip
*)


*)

end

end
