theory FrontEndTranslation
  imports CSL_IDF
begin

type_synonym v_stmt = "(int equi_state, int val, int custom) abs_stmt"

definition semantify_exp :: "ParImp.exp \<Rightarrow> (int equi_state, int val) AbstractSemantics.exp" where
  "semantify_exp e \<omega> = Some (VInt (edenot e (get_store \<omega>)))"

definition semantify_bexp :: "ParImp.bexp \<Rightarrow> (int equi_state) AbstractSemantics.bexp" where
  "semantify_bexp b \<omega> = (if (bdenot b (get_store \<omega>)) then Some True else Some False)"

definition semantify_addr :: "var \<Rightarrow> (int equi_state, address) AbstractSemantics.exp" where
  "semantify_addr x \<omega> = (if (\<exists>l. get_store \<omega> x = Some (VRef (Address l)))
  then Some (SOME l. get_store \<omega> x = Some (VRef (Address l)))
  else None)"

lemma semantify_addr_equiv:
  "semantify_addr x \<omega> = Some l \<longleftrightarrow> get_store \<omega> x = Some (VRef (Address l))"
  using semantify_addr_def by auto

lemma convert_proof_assign:
  assumes "ConcreteSemantics.SL_proof \<Delta> A (abs_stmt.LocalAssign x (semantify_exp e)) B"
  shows "\<Delta> \<turnstile>CSL [A] Cassign x e [B]"
proof -
  have "B = ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A"
    using ConcreteSemantics.SL_proof_LocalAssign_elim assms
    by fast
  moreover have "\<Delta> \<turnstile>CSL [A] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
  proof (rule RuleCons)
    show "A \<subseteq> sub_pre x e (ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A)"
      unfolding sub_pre_def ConcreteSemantics.post_substitute_var_assert_def ConcreteSemantics.substitute_var_state_def TypedEqui.assign_var_state_def
    proof (clarify)
      fix a aa b
      assume asm0: "(a, aa, b) \<in> A"
      moreover have "a = Ag (the_ag a)" by simp
      moreover have "(Ag ((the_ag a)(x \<mapsto> VInt (edenot e (the_ag a)))), aa, b) \<in> (\<lambda>\<omega>. set_store \<omega> ((get_store \<omega>)(x := semantify_exp e \<omega>))) ` A"
        by (metis (no_types, lifting) ConcreteSemantics.set_store_Ag_simplies asm0 calculation(2) get_simps_unfolded(1) image_iff semantify_exp_def)
      ultimately show "\<exists>s \<tau> \<omega>. (a, aa, b) = (Ag s, \<tau>, \<omega>) \<and> (Ag (s(x \<mapsto> VInt (edenot e s))), \<tau>, \<omega>) \<in> (\<lambda>\<omega>. set_store \<omega> ((get_store \<omega>)(x := semantify_exp e \<omega>))) ` A"
        by blast
    qed
    show "\<Delta> \<turnstile>CSL [sub_pre x e (ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A)] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
      by (simp add: RuleAssign)
  qed (simp)
  ultimately show ?thesis by auto
qed

lemma convert_proof_skip:
  assumes "ConcreteSemantics.SL_proof \<Delta> A Skip B"
  shows "\<Delta> \<turnstile>CSL [A] Cskip [B]"
  using RuleSkip assms by blast

lemma conjunct_with_true_entails:
  assumes "TypedEqui.typed_assertion \<Delta> P"
  shows "P \<subseteq> atrue \<Delta> \<otimes> P"
proof
  fix \<omega> assume "\<omega> \<in> P"
  then have "Some \<omega> = |\<omega>| \<oplus> \<omega>"
    by (simp add: commutative core_is_smaller)
  moreover have "|\<omega>| \<in> atrue \<Delta>"
    by (metis CollectI TypedEqui.typed_core TypedEqui.typed_state_axioms \<open>\<omega> \<in> P\<close> assms TypedEqui.atrue_def typed_state.typed_assertionE)
  ultimately show "\<omega> \<in> atrue \<Delta> \<otimes> P"
    using \<open>\<omega> \<in> P\<close> x_elem_set_product by blast
qed

(*
definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" where
  "make_semantic_assertion \<Delta> F A = well_typedly \<Delta> F (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
*)


fun wf_stmt where
  "wf_stmt \<Gamma> F \<Delta> (Cseq C1 C2) \<longleftrightarrow> wf_stmt \<Gamma> F \<Delta> C1 \<and> wf_stmt \<Gamma> F \<Delta> C2"
| "wf_stmt \<Gamma> F \<Delta> (Calloc r e) \<longleftrightarrow> r \<notin> fvE e"

| "wf_stmt \<Gamma> F \<Delta> ({P1} C1 {Q1} || {P2} C2 {Q2}) \<longleftrightarrow>
  disjoint (fvC C1 \<union> fvA \<Delta> ((make_semantic_assertion \<Gamma> F Q1) \<otimes> atrue \<Delta>)) (wrC C2) \<and> disjoint (fvC C2 \<union> fvA \<Delta> ((make_semantic_assertion \<Gamma> F Q2) \<otimes> atrue \<Delta>)) (wrC C1) \<and>
  TypedEqui.self_framing_typed \<Delta> (make_semantic_assertion \<Gamma> F P1) \<and> TypedEqui.typed_assertion \<Delta> (make_semantic_assertion \<Gamma> F P1) \<and>
  TypedEqui.self_framing_typed \<Delta> (make_semantic_assertion \<Gamma> F P2) \<and> TypedEqui.typed_assertion \<Delta> (make_semantic_assertion \<Gamma> F P2) \<and>
  wf_stmt \<Gamma> F \<Delta> C1 \<and> wf_stmt \<Gamma> F \<Delta> C2"

| "wf_stmt \<Gamma> F \<Delta> (Cif b C1 C2) \<longleftrightarrow> wf_stmt \<Gamma> F \<Delta> C1 \<and> wf_stmt \<Gamma> F \<Delta> C2"

| "wf_stmt \<Gamma> F \<Delta> (Cwhile b I C) \<longleftrightarrow> TypedEqui.self_framing_typed \<Delta> (make_semantic_assertion \<Gamma> F I)
                              \<and> TypedEqui.typed_assertion \<Delta> (make_semantic_assertion \<Gamma> F I) \<and> wf_stmt \<Gamma> F \<Delta> C"

| "wf_stmt \<Gamma> F \<Delta> _ \<longleftrightarrow> True"

lemma atrue_self_framing_and_typed[simp]:
  "TypedEqui.typed_assertion \<Delta> (atrue \<Delta>)"
  "TypedEqui.self_framing_typed \<Delta> (atrue \<Delta>)"
  using TypedEqui.typed_assertionI TypedEqui.atrue_def apply blast
  by (simp add: TypedEqui.self_framing_typedI TypedEqui.typed_state_then_stabilize_typed TypedEqui.atrue_def)

lemma convert_proof_alloc:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (Havoc r;; Inhale (full_ownership_with_val r e)) Q"
      and "well_typed_cmd \<Delta> (Calloc r e)"
      and "wf_stmt \<Gamma> F \<Delta> (Calloc r e)"
      and "TypedEqui.wf_context \<Delta>"
  shows "\<Delta> \<turnstile>CSL [P] Calloc r e [Q]"
proof (rule RuleCons)

  have asm0: "ConcreteSemantics.SL_proof \<Delta> P (Havoc r) (TypedEqui.exists_assert \<Delta> r P)
  \<and> ConcreteSemantics.SL_proof \<Delta> (TypedEqui.exists_assert \<Delta> r P) (Inhale (full_ownership_with_val r e)) Q
  \<and> TypedEqui.self_framing_typed \<Delta> P"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim assms(1))
  then have "Q = TypedEqui.exists_assert \<Delta> r P \<otimes> full_ownership_with_val r e"
    by blast

  show "\<Delta> \<turnstile>CSL [atrue \<Delta> \<otimes> TypedEqui.exists_assert \<Delta> r P] Calloc r e [full_ownership_with_val r e \<otimes> TypedEqui.exists_assert \<Delta> r P]"
  proof (rule RuleFrame)
    have "r \<notin> fvE e"
      using assms(3) by auto
    then show "\<Delta> \<turnstile>CSL [atrue \<Delta>] Calloc r e [full_ownership_with_val r e]"
      using RuleAlloc[of r e] by simp
    show "disjoint (fvA \<Delta> (TypedEqui.exists_assert \<Delta> r P)) (wrC (Calloc r e))"
      by (metis (no_types, lifting) ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.exists_assert_no_in_fv asm0 assms(4) disjoint_def disjoint_iff singletonD subset_Diff_insert wrC.simps(5))
    show "TypedEqui.self_framing_typed \<Delta> (atrue \<Delta>)"
      using TypedEqui.self_framing_typed_def TypedEqui.atrue_def
      using TypedEqui.typed_state_then_stabilize_typed by blast
    show "TypedEqui.self_framing_typed \<Delta> (TypedEqui.exists_assert \<Delta> r P)"
      using asm0 by fastforce
    show "TypedEqui.typed_assertion \<Delta> (TypedEqui.exists_assert \<Delta> r P)"
      using asm0 by fastforce
    show "TypedEqui.typed_assertion \<Delta> (atrue \<Delta>)"
      using TypedEqui.typed_assertion_def TypedEqui.atrue_def by blast
  qed

  moreover have "TypedEqui.typed_assertion \<Delta> P \<and> variables \<Delta> r \<noteq> None"
  proof
    show "TypedEqui.typed_assertion \<Delta> P"
      using asm0 by blast
    show "variables \<Delta> r \<noteq> None"
      using assms(2) by auto
  qed
  then have "entails P (TypedEqui.exists_assert \<Delta> r P)"
    using ConcreteSemantics.SL_proof_Havoc_elim_entails[of \<Delta> P r "TypedEqui.exists_assert \<Delta> r P"]    
    using ConcreteSemantics.exists_assert_entails by blast

  then show "P \<subseteq> atrue \<Delta> \<otimes> TypedEqui.exists_assert \<Delta> r P"
    by (meson TypedEqui.typed_assertion_exists_assert \<open>TypedEqui.typed_assertion \<Delta> P \<and> variables \<Delta> r \<noteq> None\<close> conjunct_with_true_entails dual_order.trans entails_def)
  show "full_ownership_with_val r e \<otimes> TypedEqui.exists_assert \<Delta> r P \<subseteq> Q"
    by (simp add: \<open>Q = TypedEqui.exists_assert \<Delta> r P \<otimes> full_ownership_with_val r e\<close> add_set_commm)
qed

lemma helper_exhale_encoding:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (Exhale (Stabilize A)) Q"
  shows "P \<subseteq> TypedEqui.Stabilize_typed \<Delta> A \<otimes> Q"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize A)" "TypedEqui.self_framing_typed \<Delta> P"
    "TypedEqui.typed_assertion \<Delta> P" "TypedEqui.self_framing_typed \<Delta> Q"
    "TypedEqui.typed_assertion \<Delta> Q"
  show "P \<subseteq> TypedEqui.Stabilize_typed \<Delta> A \<otimes> Q"
  proof
    fix \<omega> assume asm1: "\<omega> \<in> P"
    then obtain q a where "q \<in> Q" "a \<in> Stabilize A" "Some \<omega> = q \<oplus> a"
      by (meson asm0(1) entails_def subsetD x_elem_set_product)
    moreover have "TypedEqui.typed \<Delta> a"
      using TypedEqui.typed_state_axioms asm0(3) asm1 calculation(3) greater_equiv typed_state.typed_assertionE typed_state.typed_smaller by blast
    then have "stabilize a \<in> A"
      using calculation(2) by auto
    thm TypedEqui.Stabilize_typed_def Stabilize_def

    then show "\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> A \<otimes> Q"
      by (metis (no_types, lifting) ConcreteSemantics.stabilize_typed_elem \<open>TypedEqui.typed \<Delta> a\<close> calculation(1) calculation(3) commutative x_elem_set_product)
  qed
qed

lemma convert_proof_free:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (Exhale (Stabilize (full_ownership r))) Q"
  shows "\<Delta> \<turnstile>CSL [P] Cfree r [Q \<otimes> atrue \<Delta>]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize (full_ownership r))" "TypedEqui.self_framing_typed \<Delta> P"
    "TypedEqui.typed_assertion \<Delta> P" "TypedEqui.self_framing_typed \<Delta> Q" "TypedEqui.typed_assertion \<Delta> Q"
  show "\<Delta> \<turnstile>CSL [P] Cfree r [Q \<otimes> atrue \<Delta>]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile>CSL [TypedEqui.Stabilize_typed \<Delta> (full_ownership r) \<otimes> Q] Cfree r [TypedEqui.Stabilize_typed \<Delta> (atrue \<Delta>) \<otimes> Q]"
    proof (rule RuleFrame)
      show "\<Delta> \<turnstile>CSL [TypedEqui.Stabilize_typed \<Delta> (full_ownership r)] Cfree r [TypedEqui.Stabilize_typed \<Delta> (atrue \<Delta>)]"
        by (simp add: RuleFree RuleStabilizeTyped)
    qed (simp_all add: asm0)
    show "P \<subseteq> TypedEqui.Stabilize_typed \<Delta> (full_ownership r) \<otimes> Q"
      by (simp add: assms helper_exhale_encoding)
    show "TypedEqui.Stabilize_typed \<Delta> (atrue \<Delta>) \<otimes> Q \<subseteq> Q \<otimes> atrue \<Delta>"
      by (metis TypedEqui.typed_Stabilize_typed TypedEqui.typed_assertion_def add_set_commm add_set_mono TypedEqui.atrue_def mem_Collect_eq subsetI)
  qed
qed

lemma in_Stabilize_typed:
  assumes "stabilize \<omega> \<in> A"
      and "TypedEqui.typed \<Delta> \<omega>"
    shows "\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> A"
  using ConcreteSemantics.stabilize_typed_elem assms(1) assms(2) by blast


lemma larger_mask_full:
  assumes "\<omega>' \<succeq> \<omega>"
      and "get_m \<omega> l = 1"
    shows "get_m \<omega>' l = 1"
  by (metis (no_types, lifting) assms(1) assms(2) get_m_additive get_vm_bound greater_def nle_le pos_perm_class.sum_larger)

lemma greater_equiI:
  assumes "get_m a \<succeq> get_m b"
      and "get_h a \<succeq> get_h b"
      and "get_store a = get_store b"
      and "get_trace a = get_trace b"
    shows "a \<succeq> b"
  apply (rule greater_prodI)
   apply (metis ag_store_greater agreement.exhaust_sel assms(3) get_store_def)
  apply (rule greater_prodI)
  apply (metis assms(4) fst_conv greater_Ag set_state_def set_state_get_state snd_conv)
proof -
  have "Rep_virtual_state (snd (snd a)) \<succeq> Rep_virtual_state (snd (snd b))"
    by (metis assms(1) assms(2) get_state_def get_vh_def get_vm_def greater_prodI)
  then show "snd (snd a) \<succeq> snd (snd b)"
    using wf_greater_preserve
    by (metis Rep_virtual_state_inverse get_vh_def get_vm_def vstate_wf_ppos wf_mask_simple_get_vm wf_pre_virtual_state_def)
qed


lemma in_times_atrue:
  assumes "TypedEqui.typed \<Delta> \<omega>'"
      and "\<omega>' \<succeq> \<omega>"
      and "\<omega> \<in> A"
    shows "\<omega>' \<in> A \<otimes> atrue \<Delta>"
proof -
  obtain r where "Some \<omega>' = \<omega> \<oplus> r"
    using assms(2) greater_def by blast
  then have "r \<in> atrue \<Delta>"
    using TypedEqui.typed_smaller assms(1) TypedEqui.atrue_def greater_equiv by blast
  then show ?thesis
    using \<open>Some \<omega>' = \<omega> \<oplus> r\<close> assms(3) x_elem_set_product by blast
qed

lemma convert_proof_write:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e))) Q"
  shows "\<Delta> \<turnstile>CSL [P] Cwrite r e [Q \<otimes> atrue \<Delta>]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Custom_elim)
  assume asm0: "SL_Custom \<Delta> P (custom.FieldAssign (semantify_addr r) field_val (semantify_exp e)) Q"
  "TypedEqui.self_framing_typed \<Delta> P" "TypedEqui.typed_assertion \<Delta> P" "TypedEqui.self_framing_typed \<Delta> Q"
  "TypedEqui.typed_assertion \<Delta> Q"
  show "\<Delta> \<turnstile>CSL [P] Cwrite r e [Q \<otimes> atrue \<Delta>]"
    using asm0(1)
  proof (rule SL_custom_FieldAssign)
    assume asm1: "Q = update_value \<Delta> P (semantify_addr r) field_val (semantify_exp e)"
      "TypedEqui.self_framing_typed \<Delta> P" "entails P {\<omega>. \<exists>l. get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l}"
      "framed_by_exp P (semantify_addr r)" "framed_by_exp P (semantify_exp e)"
    show "\<Delta> \<turnstile>CSL [P] Cwrite r e [Q \<otimes> atrue \<Delta>]"
    proof (rule RuleCons)
      let ?F = "TypedEqui.Stabilize_typed \<Delta> { remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
      show "\<Delta> \<turnstile>CSL [TypedEqui.Stabilize_typed \<Delta> (full_ownership r) \<otimes> ?F] Cwrite r e [TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e) \<otimes> ?F]"
      proof (rule RuleFrame)
        show "\<Delta> \<turnstile>CSL [TypedEqui.Stabilize_typed \<Delta> (full_ownership r)] Cwrite r e [TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e)]"
          by (simp add: RuleStabilizeTyped RuleWrite)
      qed (simp_all)
      show "P \<subseteq> TypedEqui.Stabilize_typed \<Delta> (full_ownership r) \<otimes> ?F"
      proof
        fix \<omega> assume "\<omega> \<in> P"
        then obtain l where "get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l"          
          by (smt (verit) CollectD asm1(3) entails_def subsetD)
        then have "Some \<omega> = remove_only \<omega> (l, field_val) \<oplus> set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))"
          using split_remove_only_owns_only by blast
        moreover have "set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))) \<in> TypedEqui.Stabilize_typed \<Delta> (full_ownership r)"
        proof (rule in_Stabilize_typed)
          show "TypedEqui.typed \<Delta> (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))))"
            using TypedEqui.typed_state_axioms \<open>\<omega> \<in> P\<close> asm0(3) calculation greater_equiv typed_state.typed_assertionE typed_state.typed_smaller by blast
          show "stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))) \<in> full_ownership r"
            apply (rule in_full_ownership[of _ _ l])
            using \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> semantify_addr_equiv apply auto[1]
            by (smt (verit, best) \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> add.commute add.right_neutral calculation fun_upd_apply get_m_additive get_m_stabilize remove_only_charact(2))
        qed
        moreover have "remove_only \<omega> (l, field_val) \<in> ?F"
        proof (rule in_Stabilize_typed)
          have "stabilize (remove_only \<omega> (l, field_val)) = remove_only (stabilize \<omega>) (l, field_val)"
            by (simp add: remove_only_stabilize)
          then show "stabilize (remove_only \<omega> (l, field_val)) \<in> {remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
            by (smt (verit, ccfv_threshold) AbstractSemantics.get_store_stabilize CollectI TypedEqui.self_framing_typedE TypedEqui.typed_state_axioms \<open>\<omega> \<in> P\<close> \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> asm0(3) asm1(2) semantify_addr_equiv typed_state.typed_assertionE)
          show "TypedEqui.typed \<Delta> (remove_only \<omega> (l, field_val))"
            by (meson TypedEqui.typed_assertion_def TypedEqui.typed_state_axioms \<open>\<omega> \<in> P\<close> asm0(3) calculation(1) greater_def typed_state.typed_smaller)
        qed
        ultimately show "\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (full_ownership r) \<otimes> ?F"
          using commutative x_elem_set_product by fastforce
      qed
      show "TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e) \<otimes> ?F \<subseteq> Q \<otimes> atrue \<Delta>"
      proof
        fix \<omega>' assume "\<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e) \<otimes> ?F"
        then obtain ptr f where r: "Some \<omega>' = ptr \<oplus> f" "ptr \<in> TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e)" "f \<in> ?F"
          by (meson x_elem_set_product)
        then obtain l where "get_store (stabilize ptr) r = Some (VRef (Address l)) \<and> get_m (stabilize ptr) (l, field_val) = 1
  \<and> get_h (stabilize ptr) (l, field_val) = Some (VInt (edenot e (get_store (stabilize ptr))))"
          by (smt (verit, ccfv_SIG) CollectD ConcreteSemantics.stabilize_typed_elem full_ownership_with_val_def)
        then have "get_store ptr r = Some (VRef (Address l)) \<and> get_m ptr (l, field_val) = 1
  \<and> get_h ptr (l, field_val) = Some (VInt (edenot e (get_store ptr)))"
          by (simp add: stabilize_value_persists)
        then have "get_store \<omega>' r = Some (VRef (Address l)) \<and> get_m \<omega>' (l, field_val) = 1
  \<and> get_h \<omega>' (l, field_val) = Some (VInt (edenot e (get_store \<omega>')))"
          using r(1) greater_charact larger_mask_full
          by (metis (no_types, lifting) in_set_sum is_in_set_sum r(3) read_helper singletonD state_add_iff)

        moreover obtain \<omega> l' where "stabilize f = remove_only \<omega> (l', field_val)" "\<omega> \<in> P" "semantify_addr r \<omega> = Some l'"
          by (smt (verit) CollectD ConcreteSemantics.stabilize_typed_elem r(3))
        then have "l = l'"
          by (metis (no_types, lifting) AbstractSemantics.get_store_stabilize \<open>get_store (stabilize ptr) r = Some (VRef (Address l)) \<and> get_m (stabilize ptr) (l, field_val) = 1 \<and> get_h (stabilize ptr) (l, field_val) = Some (VInt (edenot e (get_store (stabilize ptr))))\<close> full_add_defined get_address_simp get_store_set_state option.distinct(1) r(1) remove_only_def semantify_addr_equiv)

        moreover have "\<omega>' \<succeq> update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>')))"
        proof (rule greater_equiI)
          show "get_m \<omega>' \<succeq> get_m (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))))"
          proof (rule greaterI)
            fix la show "get_m \<omega>' la \<succeq> get_m (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>')))) la"
              apply (cases "(l, field_val) = la")
               apply (smt (verit) CollectD \<open>\<omega> \<in> P\<close> \<open>semantify_addr r \<omega> = Some l'\<close> asm1(3) calculation(1) calculation(2) entails_def get_state_set_state get_vh_vm_set_value(2) option.sel subsetD succ_refl)
              by (smt (verit, ccfv_threshold) \<open>stabilize f = remove_only \<omega> (l', field_val)\<close> calculation(2) fun_plus_iff fun_upd_apply get_m_stabilize get_state_set_state get_vh_vm_set_value(2) get_vm_additive greater_equiv r(1) remove_only_charact(2) state_add_iff)
          qed
          show "get_h \<omega>' \<succeq> get_h (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))))"
          proof (rule greaterI)
            fix la show "get_h \<omega>' la \<succeq> get_h (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>')))) la"
              apply (cases "(l, field_val) = la")
              using calculation(1) succ_refl apply fastforce
              apply (cases "get_h (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>')))) la")
               apply (simp add: greater_equiv)
              by (metis (no_types, opaque_lifting) \<open>stabilize f = remove_only \<omega> (l', field_val)\<close> calculation(2) fun_upd_other get_state_set_state get_vh_vm_set_value(1) greater_equiv greater_state_has_greater_parts(3) r(1) read_field.simps read_field_mono remove_only_charact(1) stabilize_value_persists succ_refl)
          qed
          show "get_store \<omega>' = get_store (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))))"
            by (metis (no_types, lifting) AbstractSemantics.get_store_stabilize \<open>stabilize f = remove_only \<omega> (l', field_val)\<close> full_add_charact(1) full_add_defined get_store_set_state r(1) remove_only_def)
          show "get_trace \<omega>' = get_trace (update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))))"
            by (metis \<open>stabilize f = remove_only \<omega> (l', field_val)\<close> get_trace_set_state get_trace_stabilize greater_equiv greater_state_has_greater_parts(2) r(1) remove_only_def)
        qed
        moreover have "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) \<in> Q"
          using \<open>l = l'\<close>
          by (smt (verit, ccfv_SIG) AbstractSemantics.get_store_stabilize ConcreteSemantics.stabilize_typed_elem \<open>\<omega> \<in> P\<close> \<open>get_store ptr r = Some (VRef (Address l)) \<and> get_m ptr (l, field_val) = 1 \<and> get_h ptr (l, field_val) = Some (VInt (edenot e (get_store ptr)))\<close> \<open>semantify_addr r \<omega> = Some l'\<close> \<open>stabilize f = remove_only \<omega> (l', field_val)\<close> asm1(1) full_add_charact(1) full_add_defined get_store_set_state in_update_value r(1) r(2) remove_only_def semantify_exp_def snd_conv typed_get_vh)
        ultimately show "\<omega>' \<in> Q \<otimes> atrue \<Delta>"
          by (meson TypedEqui.typed_assertionE TypedEqui.typed_state_axioms \<open>\<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (full_ownership_with_val r e) \<otimes> TypedEqui.Stabilize_typed \<Delta> {remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}\<close> in_times_atrue typed_state.typed_Stabilize_typed typed_state.typed_star)
      qed
    qed
  qed
qed


definition semantify_heap_loc :: "var \<Rightarrow> (int equi_state, int val) AbstractSemantics.exp" where
  "semantify_heap_loc r \<omega> =
  (if (\<exists>l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_h \<omega> (l, field_val) = Some v)
  then Some (the (get_h \<omega> (SOME l. get_store \<omega> r = Some (VRef (Address l)), field_val)))
  else None)"

lemma convert_proof_read:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (LocalAssign x (semantify_heap_loc r)) Q"
      and "custom_context \<Delta> = type_ctxt_heap"
  shows "\<Delta> \<turnstile>CSL [P] Cread x r [Q]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_LocalAssign_elim)
  assume asm0: "Q = ConcreteSemantics.post_substitute_var_assert x (semantify_heap_loc r) P"
    "framed_by_exp P (semantify_heap_loc r)"
    "TypedEqui.self_framing_typed \<Delta> P" "TypedEqui.typed_assertion \<Delta> P"

  have r: "\<And>\<omega>. \<omega> \<in> P \<Longrightarrow> (\<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0
  \<and> (\<exists>v. get_h \<omega> (l, field_val) = Some (VInt v)))"
  proof -
    fix \<omega>
    assume asm1: "\<omega> \<in> P"
    then obtain l v0 where "get_store \<omega> r = Some (VRef (Address l))" "get_h \<omega> (l, field_val) = Some v0"
      by (metis asm0(2) framed_by_exp_def semantify_heap_loc_def)
    then obtain v where "v0 = VInt v"
      using TypedEqui.typed_assertionE[OF asm0(4) asm1] TypedEqui.typed_def[of \<Delta> \<omega>] well_typedE(1)[of "custom_context \<Delta>" "get_abs_state \<omega>"]
      Instantiation.well_typed_heapE[of "custom_context \<Delta>" "get_state \<omega>" "(l, field_val)" v0]
      by (smt (verit, best) CollectD assms(2) option.sel snd_conv snd_get_abs_state type_ctxt_heap_def vints_def)
    moreover have "stabilize \<omega> \<in> P"
      using TypedEqui.self_framing_typedE TypedEqui.typed_state_axioms \<open>\<omega> \<in> P\<close> asm0(3) asm0(4) typed_state.typed_assertionE by blast
    then have "get_h (stabilize \<omega>) (l, field_val) = Some (VInt v)"
      by (metis (no_types, lifting) AbstractSemantics.get_store_stabilize \<open>get_h \<omega> (l, field_val) = Some v0\<close> \<open>get_store \<omega> r = Some (VRef (Address l))\<close> asm0(2) calculation framed_by_exp_def get_address_simp semantify_heap_loc_def stabilize_value_persists)
    then have "get_m \<omega> (l, field_val) > 0"
      using EquiSemAuxLemma.gr_0_is_ppos stable_virtual_state_def by fastforce
    then show "(\<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0
  \<and> (\<exists>v. get_h \<omega> (l, field_val) = Some (VInt v)))"
      by (simp add: \<open>get_h \<omega> (l, field_val) = Some v0\<close> \<open>get_store \<omega> r = Some (VRef (Address l))\<close> calculation)
  qed

  show "\<Delta> \<turnstile>CSL [P] Cread x r [Q]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile>CSL [P] Cread x r [read_result P x r]"
    proof (rule RuleRead)
      show "P \<subseteq> read_perm r" (* Should come from framed_by_exp *)
        using r
        unfolding read_perm_def by (simp add: subsetI)
    qed
    show "read_result P x r \<subseteq> Q"
    proof
      fix \<omega>' assume "\<omega>' \<in> read_result P x r"
      then obtain \<omega> l where "\<omega>' = TypedEqui.assign_var_state x (get_h \<omega> (l, field_val)) \<omega>"
          "\<omega> \<in> P" "get_store \<omega> r = Some (VRef (Address l))"
        unfolding read_result_def by blast
      moreover have "get_h \<omega> (l, field_val) = (if (\<exists>l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_h \<omega> (l, field_val) = Some v)
            then Some (the (get_h \<omega> (SOME l. get_store \<omega> r = Some (VRef (Address l)), field_val))) else None)"
        by (simp add: calculation(3))
      ultimately show "\<omega>' \<in> Q" using asm0(1)
        unfolding ConcreteSemantics.post_substitute_var_assert_def ConcreteSemantics.substitute_var_state_def
          semantify_heap_loc_def
        by (smt (verit, best) Eps_cong image_iff)
    qed
  qed (simp)
qed



fun translate (* :: "cmd \<Rightarrow> (v_stmt \<times> v_stmt set)" *) where
  "translate \<Gamma> F Cskip = (Skip, {})"
| "translate \<Gamma> F (Cassign x e) = (LocalAssign x (semantify_exp e), {})"

| "translate \<Gamma> F (Calloc r e) = ((Havoc r;; Inhale (full_ownership_with_val r e)), {})"
| "translate \<Gamma> F (Cfree r) = (Exhale (Stabilize (full_ownership r)), {})"
| "translate \<Gamma> F (Cwrite r e) = (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e)), {})"
| "translate \<Gamma> F (Cread x r) = (LocalAssign x (semantify_heap_loc r), {})"

| "translate \<Gamma> F (Cseq C1 C2) = (let r1 = translate \<Gamma> F C1 in let r2 = translate \<Gamma> F C2 in
  (fst r1;; fst r2, snd r1 \<union> snd r2))"

| "translate \<Gamma> F (Cif b C1 C2) = (If (semantify_bexp b) (fst (translate \<Gamma> F C1)) (fst (translate \<Gamma> F C2)), snd (translate \<Gamma> F C1) \<union> snd (translate \<Gamma> F C2))"

| "translate \<Gamma> F ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (make_semantic_assertion \<Gamma> F P1 \<otimes> make_semantic_assertion \<Gamma> F P2);;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion \<Gamma> F Q1 \<otimes> make_semantic_assertion \<Gamma> F Q2)),
  let r1 = translate \<Gamma> F C1 in let r2 = translate \<Gamma> F C2 in
  { (Inhale (make_semantic_assertion \<Gamma> F P1);; fst r1;; Exhale (make_semantic_assertion \<Gamma> F Q1)),
  (Inhale (make_semantic_assertion \<Gamma> F P2);; fst r2;; Exhale (make_semantic_assertion \<Gamma> F Q2)) } \<union> snd r1 \<union> snd r2)"

| "translate \<Gamma> F (Cwhile b I C) = (Exhale (make_semantic_assertion \<Gamma> F I);;
  ConcreteSemantics.havoc_list (wrL C);; Inhale ((make_semantic_assertion \<Gamma> F I) \<inter> assertify_bexp (Bnot b)),
  { Inhale ((make_semantic_assertion \<Gamma> F I) \<inter> assertify_bexp b);; fst (translate \<Gamma> F C);; Exhale (make_semantic_assertion \<Gamma> F I) } \<union> snd (translate \<Gamma> F C))"

lemma CSL_weaken_post_atrue:
  assumes "\<Delta> \<turnstile>CSL [P] C [Q]"
      and "TypedEqui.typed_assertion \<Delta> Q"
  shows "\<Delta> \<turnstile>CSL [P] C [Q \<otimes> atrue \<Delta>]"
  using assms(1)
proof (rule RuleCons)
  show "Q \<subseteq> Q \<otimes> atrue \<Delta>"
    using add_set_commm assms(2) conjunct_with_true_entails by blast
qed (simp)

lemma CSL_add_atrue:
  assumes "\<Delta> \<turnstile>CSL [P] C [Q]"
      and "TypedEqui.self_framing_typed \<Delta> P"
      and "TypedEqui.typed_assertion \<Delta> P"
      and "TypedEqui.wf_context \<Delta>"
    shows "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>]"
  by (rule RuleFrame) (simp_all add: assms)


definition proof_obligations_valid where
  "proof_obligations_valid \<Delta> S \<longleftrightarrow> (\<forall>Cv \<in> S. \<exists>B. ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>) Cv B)"

lemma proof_obligations_valid_union:
  "proof_obligations_valid \<Delta> (S1 \<union> S2) \<longleftrightarrow> proof_obligations_valid \<Delta> S1 \<and> proof_obligations_valid \<Delta> S2"
  by (meson Un_iff proof_obligations_valid_def)

definition invariant_translate where
  "invariant_translate \<Gamma> F \<Delta> P C Q \<longleftrightarrow>
  ((proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C)) \<and> ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F C)) Q) \<longrightarrow> \<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>])"

lemma invariant_translateE:
  assumes "invariant_translate \<Gamma> F \<Delta> P C Q"
      and "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C))"
      and "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F C)) Q"
    shows "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>]"
  using assms(1) assms(2) assms(3) invariant_translate_def by blast


lemma invariant_translateI:
  assumes "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C)) \<Longrightarrow> ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F C)) Q
    \<Longrightarrow> \<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>]"
  shows "invariant_translate \<Gamma> F \<Delta> P C Q"
  using assms invariant_translate_def proof_obligations_valid_def by blast

lemma invariant_translate_simpler:
  assumes "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F C)) Q \<Longrightarrow> \<Delta> \<turnstile>CSL [P] C [Q]"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C))"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P C Q"
  by (simp add: CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms invariant_translateI)

corollary invariant_translate_skip:
  assumes "TypedEqui.wf_context \<Delta>"
  shows "invariant_translate \<Gamma> F \<Delta> P Cskip Q"
  using convert_proof_skip invariant_translate_simpler assms by fastforce

corollary invariant_translate_assign:
  assumes "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F (Cassign x e)))"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cassign x e) Q"
  using convert_proof_assign invariant_translate_simpler assms by fastforce

corollary invariant_translate_alloc:
  assumes "well_typed_cmd \<Delta> (Calloc r e)"
      and "wf_stmt \<Gamma> F \<Delta> (Calloc r e)"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F (Calloc r e)))"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P (Calloc r e) Q"
  using assms cmd.distinct(37) convert_proof_alloc invariant_translate_simpler by fastforce

lemma atrue_twice_same:
  "atrue \<Delta> \<otimes> atrue \<Delta> \<subseteq> atrue \<Delta>"
  unfolding TypedEqui.atrue_def add_set_def
  by (smt (z3) Collect_mono_iff TypedEqui.typed_sum mem_Collect_eq)

lemma atrue_twice_equal:
  "atrue \<Delta> \<otimes> atrue \<Delta> = atrue \<Delta>"
proof
  show "atrue \<Delta> \<subseteq> atrue \<Delta> \<otimes> atrue \<Delta>"
  proof
    fix x assume "x \<in> atrue \<Delta>"
    then have "Some x = x \<oplus> |x|"
      using core_is_smaller by blast
    then have "|x| \<in> atrue \<Delta>"
      using TypedEqui.typed_core \<open>x \<in> atrue \<Delta>\<close> TypedEqui.atrue_def by blast
    then show "x \<in> atrue \<Delta> \<otimes> atrue \<Delta>"
      using \<open>Some x = x \<oplus> |x|\<close> \<open>x \<in> atrue \<Delta>\<close> x_elem_set_product by blast
  qed
qed (simp add: atrue_twice_same)


corollary invariant_translate_free:
  assumes "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F (Cfree r)))"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cfree r) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F (Cfree r))) Q"
  then have "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cfree r [(Q \<otimes> atrue \<Delta>) \<otimes> atrue \<Delta>]"
    using RuleFrame[OF convert_proof_free]
    by (metis CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms convert_proof_free fst_eqD translate.simps(4))
  then show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cfree r [Q \<otimes> atrue \<Delta>]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_write:
  assumes "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F (Cwrite r e)))"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cwrite r e) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F (Cwrite r e))) Q"
  then have "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cwrite r e [(Q \<otimes> atrue \<Delta>) \<otimes> atrue \<Delta>]"
    using RuleFrame[OF convert_proof_write]
    by (metis CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms convert_proof_write fst_eqD translate.simps(5))
  then show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cwrite r e [Q \<otimes> atrue \<Delta>]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_read:
  assumes "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F (Cread x r)))"
      and "TypedEqui.wf_context \<Delta>"
      and "custom_context \<Delta> = type_ctxt_heap"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cread x r) Q"
  using convert_proof_read invariant_translate_simpler assms by fastforce


lemma invariant_translate_seq:
  assumes "\<And>R. invariant_translate \<Gamma> F \<Delta> P C1 R"
      and "\<And>R. invariant_translate \<Gamma> F \<Delta> R C2 Q"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cseq C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F (Cseq C1 C2)))"
    "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F (Cseq C1 C2))) Q"
  then obtain R where r: "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F C1)) R"
      "ConcreteSemantics.SL_proof \<Delta> R (fst (translate \<Gamma> F C2)) Q"
    by (metis ConcreteSemantics.SL_proof_Seq_elim fst_eqD translate.simps(7))
  show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cseq C1 C2 [Q \<otimes> atrue \<Delta>]"
  proof (rule RuleSeq)
    show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C1 [R \<otimes> atrue \<Delta>]"
      using assms(1)[of R] r
      unfolding invariant_translate_def
      by (metis asm0(1) proof_obligations_valid_union snd_conv translate.simps(7))
    show "\<Delta> \<turnstile>CSL [R \<otimes> atrue \<Delta>] C2 [Q \<otimes> atrue \<Delta>]"
    proof (rule RuleCons)
      show "\<Delta> \<turnstile>CSL [R \<otimes> atrue \<Delta>] C2 [(Q \<otimes> atrue \<Delta>) \<otimes> atrue \<Delta>]"
          using assms(2)[of R] asm0
          unfolding invariant_translate_def proof_obligations_valid_def
          by (metis (no_types, lifting) Un_iff add_set_asso atrue_twice_equal r(2) snd_conv translate.simps(7))
      show "Q \<otimes> atrue \<Delta> \<otimes> atrue \<Delta> \<subseteq> Q \<otimes> atrue \<Delta>"
        by (simp add: add_set_asso add_set_mono atrue_twice_same)
    qed (simp)
  qed
qed


lemma invariant_translate_inhale_exhale_get_proof:
  assumes "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C Q"
      and "ConcreteSemantics.SL_proof \<Delta> P (Inhale A;; fst (translate \<Gamma> F C);; Exhale B) Q"
      and "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C))"
    shows "\<Delta> \<turnstile>CSL [P \<otimes> A \<otimes> atrue \<Delta>] C [Q \<otimes> B \<otimes> atrue \<Delta>]"
  using assms(2)
proof (rule ConcreteSemantics.SL_proof_Seq_elim)
  fix R1 assume asm0: "ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Inhale A ;; fst (translate \<Gamma> F C)) R1"
    "ConcreteSemantics.SL_proof \<Delta> R1 (abs_stmt.Exhale B) Q"
  then have "entails R1 (Q \<otimes> B)" by auto
  show "\<Delta> \<turnstile>CSL [P \<otimes> A \<otimes> atrue \<Delta>] C [Q \<otimes> B \<otimes> atrue \<Delta>]"
  proof (rule ConcreteSemantics.SL_proof_Seq_elim[OF asm0(1)])
    fix R0 assume asm1: "ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Inhale A) R0"
          "ConcreteSemantics.SL_proof \<Delta> R0 (fst (translate \<Gamma> F C)) R1"
    then have "ConcreteSemantics.SL_proof \<Delta> (P \<otimes> A) (fst (translate \<Gamma> F C)) R1"
      by auto
    show "\<Delta> \<turnstile>CSL [P \<otimes> A \<otimes> atrue \<Delta>] C [Q \<otimes> B \<otimes> atrue \<Delta>]"
    proof (rule RuleCons)
      show "\<Delta> \<turnstile>CSL [P \<otimes> A \<otimes> atrue \<Delta>] C [R1 \<otimes> atrue \<Delta>]"
        using \<open>ConcreteSemantics.SL_proof \<Delta> (P \<otimes> A) (fst (translate \<Gamma> F C)) R1\<close> assms(1) assms(3) invariant_translate_def by blast
      show "R1 \<otimes> atrue \<Delta> \<subseteq> Q \<otimes> B \<otimes> atrue \<Delta>"
        by (meson \<open>entails R1 (Q \<otimes> B)\<close> add_set_mono entails_def order_refl)
    qed (simp)
  qed
qed


lemma drop_conjunct_entails:
  assumes "TypedEqui.typed_assertion \<Delta> A"
  shows "A \<otimes> B \<otimes> atrue \<Delta> \<subseteq> B \<otimes> atrue \<Delta>"
  by (smt (verit) TypedEqui.typed_assertion_def add_set_asso add_set_commm add_set_def assms TypedEqui.atrue_def atrue_twice_equal mem_Collect_eq subsetI)


(*
| "translate \<Gamma> F ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (P1 \<otimes> P2);; ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (Q1 \<otimes> Q2)),
  let r1 = translate \<Gamma> F C1 in let r2 = translate \<Gamma> F C2 in
  { (Inhale P1;; fst r1;; Exhale Q1), (Inhale P2;; fst r2;; Exhale Q2) } \<union> snd r1 \<union> snd r2)"
*)


lemma typed_self_framing_star:
  assumes "TypedEqui.self_framing_typed \<Delta> A"
      and "TypedEqui.self_framing_typed \<Delta> B"
    shows "TypedEqui.self_framing_typed \<Delta> (A \<otimes> B)"
proof (rule TypedEqui.self_framing_typedI)
  fix \<omega> assume asm0: "TypedEqui.typed \<Delta> \<omega>"
  show "(\<omega> \<in> A \<otimes> B) = (stabilize \<omega> \<in> A \<otimes> B)"
  proof
    assume "\<omega> \<in> A \<otimes> B"
    then obtain a b where "Some \<omega> = a \<oplus> b" "a \<in> A" "b \<in> B"
      by (meson x_elem_set_product)
    then show "stabilize \<omega> \<in> A \<otimes> B"
      by (metis (no_types, lifting) TypedEqui.typed_state_axioms asm0 assms(1) assms(2) greater_def greater_equiv stabilize_sum typed_state.self_framing_typedE typed_state.typed_smaller x_elem_set_product)
  next
    assume "stabilize \<omega> \<in> A \<otimes> B"
    then obtain a b where "Some (stabilize \<omega>) = a \<oplus> b" "a \<in> A" "b \<in> B"
      by (meson x_elem_set_product)
    then obtain b' where "Some b' = b \<oplus> |\<omega>|"
      by (metis (no_types, opaque_lifting) asso2 decompose_stabilize_pure option.exhaust_sel)
    then have "stabilize b' = stabilize b"
      using plus_pure_stabilize_eq by blast
    moreover have "TypedEqui.typed \<Delta> b'"
      by (smt (verit, ccfv_SIG) TypedEqui.typed_state_axioms \<open>Some (stabilize \<omega>) = a \<oplus> b\<close> \<open>Some b' = b \<oplus> |\<omega>|\<close> addition_bigger asm0 commutative decompose_stabilize_pure greater_def typed_state.typed_smaller)
    ultimately have "b' \<in> B"
      by (metis (no_types, lifting) TypedEqui.typed_smaller TypedEqui.typed_state_axioms \<open>Some b' = b \<oplus> |\<omega>|\<close> \<open>b \<in> B\<close> assms(2) commutative greater_equiv typed_state.self_framing_typed_def)
    then show "\<omega> \<in> A \<otimes> B"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> b\<close> \<open>Some b' = b \<oplus> |\<omega>|\<close> \<open>a \<in> A\<close> asso1 decompose_stabilize_pure x_elem_set_product)
  qed
qed



lemma self_framing_typed_star_atrue:
  assumes "TypedEqui.self_framing_typed \<Delta> P"
  shows "TypedEqui.self_framing_typed \<Delta> (P \<otimes> atrue \<Delta>)"
  by (simp add: assms typed_self_framing_star)

lemma typed_assertion_star_atrue:
  assumes "TypedEqui.typed_assertion \<Delta> P"
  shows "TypedEqui.typed_assertion \<Delta> (P \<otimes> atrue \<Delta>)"
  by (simp add: TypedEqui.typed_star assms)




lemma invariant_translate_parallel:
  assumes "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C1 Q"
      and "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C2 Q"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      and "wf_stmt \<Gamma> F \<Delta> ({P1} C1 {Q1} || {P2} C2 {Q2})"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P ({P1} C1 {Q1} || {P2} C2 {Q2}) Q"
proof (rule invariant_translateI)
  let ?P1 = "make_semantic_assertion \<Gamma> F P1"
  let ?P2 = "make_semantic_assertion \<Gamma> F P2"
  let ?Q1 = "make_semantic_assertion \<Gamma> F Q1"
  let ?Q2 = "make_semantic_assertion \<Gamma> F Q2"

  assume asm0: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F {P1} C1 {Q1} || {P2} C2 {Q2}))"
    "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F {P1} C1 {Q1} || {P2} C2 {Q2})) Q"
  then have r0: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C1)) \<and> proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C2))"
    using proof_obligations_valid_union
    unfolding translate.simps by (metis sndI)
  moreover obtain B1 where B1_def: "ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>)
    (Inhale (make_semantic_assertion \<Gamma> F P1);; fst (translate \<Gamma> F C1);; Exhale (make_semantic_assertion \<Gamma> F Q1)) B1"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover obtain B2 where B2_def: "ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>)
  (Inhale (make_semantic_assertion \<Gamma> F P2);; fst (translate \<Gamma> F C2);; Exhale (make_semantic_assertion \<Gamma> F Q2)) B2"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover have main: "ConcreteSemantics.SL_proof \<Delta> P (Exhale (make_semantic_assertion \<Gamma> F P1 \<otimes> make_semantic_assertion \<Gamma> F P2);;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion \<Gamma> F Q1 \<otimes> make_semantic_assertion \<Gamma> F Q2)) Q"
    using asm0 by simp
  then obtain R0 R1 where R_defs:
    "ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Exhale (make_semantic_assertion \<Gamma> F P1 \<otimes> make_semantic_assertion \<Gamma> F P2)) R0"
    "ConcreteSemantics.SL_proof \<Delta> R0 (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2)) R1"
    "ConcreteSemantics.SL_proof \<Delta> R1 (abs_stmt.Inhale (make_semantic_assertion \<Gamma> F Q1 \<otimes> make_semantic_assertion \<Gamma> F Q2)) Q"
    by (meson ConcreteSemantics.SL_proof_Seq_elim)
  then have P_Q_R_rels:
    "entails P (R0 \<otimes> (make_semantic_assertion \<Gamma> F P1 \<otimes> make_semantic_assertion \<Gamma> F P2))
  \<and> Q = R1 \<otimes> (make_semantic_assertion \<Gamma> F Q1 \<otimes> make_semantic_assertion \<Gamma> F Q2)" by auto
  moreover have "entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - (set (wrL C1 @ wrL C2))"
    using ConcreteSemantics.SL_proof_Havoc_list_elim R_defs(2) assms(3) assms(5) by blast
(* R1 is the frame! *)

  show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> atrue \<Delta>]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile>CSL [((?P1 \<otimes> atrue \<Delta>) \<otimes> (?P2 \<otimes> atrue \<Delta>)) \<otimes> R1] {P1} C1 {Q1} || {P2} C2 {Q2} [((?Q1 \<otimes> atrue \<Delta>) \<otimes> (?Q2 \<otimes> atrue \<Delta>)) \<otimes> R1]"
    proof (rule RuleFrame)
      show "\<Delta> \<turnstile>CSL [?P1 \<otimes> atrue \<Delta> \<otimes> (?P2 \<otimes> atrue \<Delta>)] {P1} C1 {Q1} || {P2} C2 {Q2} [?Q1 \<otimes> atrue \<Delta> \<otimes> (?Q2 \<otimes> atrue \<Delta>)]"
      proof (rule RulePar)
        show "\<Delta> \<turnstile>CSL [?P1 \<otimes> atrue \<Delta>] C1 [?Q1 \<otimes> atrue \<Delta>]"
        proof (rule RuleCons)
          show "\<Delta> \<turnstile>CSL [atrue \<Delta> \<otimes> ?P1 \<otimes> atrue \<Delta>] C1 [B1 \<otimes> ?Q1 \<otimes> atrue \<Delta>]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(1) B1_def]
            using r0 by blast
          show "B1 \<otimes> ?Q1 \<otimes> atrue \<Delta> \<subseteq> ?Q1 \<otimes> atrue \<Delta>"
            using B1_def drop_conjunct_entails by blast
          show "?P1 \<otimes> atrue \<Delta> \<subseteq> atrue \<Delta> \<otimes> ?P1 \<otimes> atrue \<Delta>"
            using add_set_asso assms(4) conjunct_with_true_entails typed_assertion_star_atrue wf_stmt.simps(3) by blast
        qed
        show "\<Delta> \<turnstile>CSL [?P2 \<otimes> atrue \<Delta>] C2 [?Q2 \<otimes> atrue \<Delta>]"
        proof (rule RuleCons)
          show "\<Delta> \<turnstile>CSL [atrue \<Delta> \<otimes> ?P2 \<otimes> atrue \<Delta>] C2 [B2 \<otimes> ?Q2 \<otimes> atrue \<Delta>]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(2) B2_def]
            using r0 by blast
          show "B2 \<otimes> ?Q2 \<otimes> atrue \<Delta> \<subseteq> ?Q2 \<otimes> atrue \<Delta>"
            using B2_def drop_conjunct_entails by blast
          show "?P2 \<otimes> atrue \<Delta> \<subseteq> atrue \<Delta> \<otimes> ?P2 \<otimes> atrue \<Delta>"
            using add_set_asso add_set_left_comm atrue_twice_equal
            by (metis (no_types, opaque_lifting) order_refl)
        qed
        show "disjoint (fvC C1 \<union> fvA \<Delta> (?Q1 \<otimes> atrue \<Delta>)) (wrC C2)"
          using assms(4) by auto
        show "disjoint (fvC C2 \<union> fvA \<Delta> (?Q2 \<otimes> atrue \<Delta>)) (wrC C1)"
          using assms(4) by auto
        show "TypedEqui.self_framing_typed \<Delta> (?P1 \<otimes> atrue \<Delta>)"
          using assms(4) self_framing_typed_star_atrue wf_stmt.simps(3) by blast
        show "TypedEqui.self_framing_typed \<Delta> (?P2 \<otimes> atrue \<Delta>)"
          using assms(4) self_framing_typed_star_atrue by auto
        show "TypedEqui.typed_assertion \<Delta> (?P1 \<otimes> atrue \<Delta>)"
          using assms(4) typed_assertion_star_atrue by auto
        show "TypedEqui.typed_assertion \<Delta> (?P2 \<otimes> atrue \<Delta>)"
          using assms(4) typed_assertion_star_atrue by auto
      qed
      show "disjoint (fvA \<Delta> R1) (wrC {P1} C1 {Q1} || {P2} C2 {Q2})"
        by (metis (mono_tags, opaque_lifting) Diff_subset_conv Orderings.order_eq_iff \<open>entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - set (wrL C1 @ wrL C2)\<close> bot.extremum disjoint_minus disjoint_simps(2) disjoint_simps(3) sup.order_iff wrC.simps(7) wrC.simps(8) wrL.simps(7) wrL_wrC_same)
      show "TypedEqui.self_framing_typed \<Delta> (?P1 \<otimes> atrue \<Delta> \<otimes> (?P2 \<otimes> atrue \<Delta>))"
        by (meson assms(4) self_framing_typed_star_atrue typed_self_framing_star wf_stmt.simps(3))
      show "TypedEqui.typed_assertion \<Delta> (?P1 \<otimes> atrue \<Delta> \<otimes> (?P2 \<otimes> atrue \<Delta>))"
        using TypedEqui.typed_star assms(4) typed_assertion_star_atrue wf_stmt.simps(3) by blast
      show "TypedEqui.self_framing_typed \<Delta> R1"
        using R_defs(3) by blast
      show "TypedEqui.typed_assertion \<Delta> R1"
        using R_defs(3) by force
    qed
    show "P \<otimes> atrue \<Delta> \<subseteq> ?P1 \<otimes> atrue \<Delta> \<otimes> (?P2 \<otimes> atrue \<Delta>) \<otimes> R1"
    proof -
      have "P \<otimes> atrue \<Delta> \<subseteq> (R0 \<otimes> (?P1 \<otimes> ?P2)) \<otimes> atrue \<Delta>"
        by (metis P_Q_R_rels add_set_mono atrue_twice_equal atrue_twice_same entails_def)
      also have "... \<subseteq> R1 \<otimes> ((?P1 \<otimes> ?P2) \<otimes> atrue \<Delta>)"
        using \<open>entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - set (wrL C1 @ wrL C2)\<close> add_set_asso add_set_mono entails_def by blast
      also have "... \<subseteq> ?P1 \<otimes> atrue \<Delta> \<otimes> (?P2 \<otimes> atrue \<Delta>) \<otimes> R1"
        using add_set_commm add_set_left_comm atrue_twice_equal
        by (smt (verit, del_insts) dual_order.refl)
      finally show ?thesis by simp
    qed
    show "?Q1 \<otimes> atrue \<Delta> \<otimes> (?Q2 \<otimes> atrue \<Delta>) \<otimes> R1 \<subseteq> Q \<otimes> atrue \<Delta>"
      by (metis (no_types, lifting) Orderings.order_eq_iff P_Q_R_rels add_set_asso add_set_commm atrue_twice_equal)
  qed
qed

(*
Maybe prove? Need to prove that assertions are wf...
lemma translation_wf:
  assumes "wf_stmt \<Gamma> F \<Delta> C"
      and "well_typed_cmd \<Delta> C"
    shows "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C))"
  using assms
proof (induct C)
  case (Cseq C1 C2)
  then show ?case
    by (metis ConcreteSemantics.wf_abs_stmt.simps(7) fst_eqD translate.simps(7) well_typed_cmd_aux.simps(2) wf_stmt.simps(1))
next
  ...
qed (simp_all)
*)

lemma invariant_translate_if:
  assumes "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C1 Q"
      and "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C2 Q"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cif b C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F (Cif b C1 C2)))"
    "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F (Cif b C1 C2))) Q"

  show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cif b C1 C2 [Q \<otimes> atrue \<Delta>]"
  proof (rule ConcreteSemantics.SL_proof_If_elim)
    show "ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.If (semantify_bexp b) (fst (translate \<Gamma> F C1)) (fst (translate \<Gamma> F C2))) Q"
      by (metis asm0(2) fst_eqD translate.simps(8))
    fix B1 B2 assume asm1: "Q = B1 \<union> B2" "framed_by_exp P (semantify_bexp b)"
       "ConcreteSemantics.SL_proof \<Delta> (P \<otimes> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)) (fst (translate \<Gamma> F C1)) B1"
       "ConcreteSemantics.SL_proof \<Delta> (P \<otimes> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b))) (fst (translate \<Gamma> F C2)) B2"
       "TypedEqui.self_framing_typed \<Delta> P" "TypedEqui.typed_assertion \<Delta> P"
    show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cif b C1 C2 [Q \<otimes> atrue \<Delta>]"
    proof (rule RuleIf)
      show "\<Delta> \<turnstile>CSL [(P \<otimes> atrue \<Delta>) \<inter> assertify_bexp b] C1 [Q \<otimes> atrue \<Delta>]"
      proof (rule RuleCons)
        show "\<Delta> \<turnstile>CSL [(P \<otimes> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)) \<otimes> atrue \<Delta>] C1 [B1 \<otimes> atrue \<Delta>]"
          by (metis asm0(1) asm1(3) assms(1) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B1 \<otimes> atrue \<Delta> \<subseteq> Q \<otimes> atrue \<Delta>"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> atrue \<Delta>) \<inter> assertify_bexp b \<subseteq> (P \<otimes> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)) \<otimes> atrue \<Delta>"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> atrue \<Delta>) \<inter> assertify_bexp b"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot b (get_store \<omega>)"
            using in_set_sum[of \<omega> P "atrue \<Delta>"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "|p| \<in> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)"
            unfolding ConcreteSemantics.pure_typed_def semantify_bexp_def
            by (smt (verit, ccfv_SIG) ConcreteSemantics.get_store_Ag_simplifies TypedEqui.typed_assertionE TypedEqui.typed_core asm1(6) full_add_charact(1) full_core_def max_projection_prop_pure_core mem_Collect_eq mpp_prop)
          then have "p \<in> P \<otimes> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.pure_typed \<Delta> (semantify_bexp b)) \<otimes> atrue \<Delta>"
            using TypedEqui.typed_state_axioms \<open>Some \<omega> = p \<oplus> r\<close> \<open>\<omega> \<in> (P \<otimes> atrue \<Delta>) \<inter> assertify_bexp b\<close> asm1(6) greater_def in_times_atrue typed_assertion_star_atrue typed_state.typed_assertionE by blast
        qed
      qed

      show "\<Delta> \<turnstile>CSL [(P \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b)] C2 [Q \<otimes> atrue \<Delta>]"
      proof (rule RuleCons)
        show "\<Delta> \<turnstile>CSL [(P \<otimes> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b))) \<otimes> atrue \<Delta>] C2 [B2 \<otimes> atrue \<Delta>]"
          by (metis asm0(1) asm1(4) assms(2) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B2 \<otimes> atrue \<Delta> \<subseteq> Q \<otimes> atrue \<Delta>"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b) \<subseteq> P \<otimes> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b)) \<otimes> atrue \<Delta>"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b)"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot (Bnot b) (get_store \<omega>)"
            using in_set_sum[of \<omega> P "atrue \<Delta>"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "\<not> bdenot b (get_store |p| )"
            by (simp add: core_charact(1) full_add_charact(1))
          then have "|p| \<in> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b))"
            unfolding ConcreteSemantics.pure_typed_def semantify_bexp_def negate_def
            by (smt (verit, del_insts) CollectD CollectI TypedEqui.typed_assertionE TypedEqui.typed_core \<open>p \<in> P\<close> asm1(2) asm1(6) core_charact(1) core_in_emp_core emp_core_def framed_by_exp_def option.collapse semantify_bexp_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b))"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.pure_typed \<Delta> (negate (semantify_bexp b))) \<otimes> atrue \<Delta>"
            by (meson TypedEqui.typed_intersection TypedEqui.typed_state_axioms \<open>Some \<omega> = p \<oplus> r\<close> \<open>\<omega> \<in> (P \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b)\<close> asm1(6) atrue_self_framing_and_typed(1) greater_def in_times_atrue typed_state.typed_assertionE typed_state.typed_star)
        qed
      qed
    qed
  qed
qed

lemma intersect_and_star:
  "(I \<otimes> R) \<inter> assertify_bexp b \<subseteq> (I \<inter> assertify_bexp b) \<otimes> R"
proof
  fix \<omega> assume "\<omega> \<in> (I \<otimes> R) \<inter> assertify_bexp b"
  then obtain i r where "bdenot b (get_store \<omega>)" "Some \<omega> = i \<oplus> r" "i \<in> I" "r \<in> R"
    by (metis (no_types, lifting) CollectD IntD1 IntD2 assertify_bexp_def x_elem_set_product)
  then have "i \<in> I \<inter> assertify_bexp b"
    by (simp add: full_add_charact(1) in_assertify_bexp)
  then show "\<omega> \<in> (I \<inter> assertify_bexp b) \<otimes> R"
    using \<open>Some \<omega> = i \<oplus> r\<close> \<open>r \<in> R\<close> x_elem_set_product by blast
qed


lemma invariant_translate_while:
  assumes "\<And>P Q. invariant_translate \<Gamma> F \<Delta> P C Q"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (ConcreteSemantics.havoc_list (wrL C))"
      and "wf_stmt \<Gamma> F \<Delta> (Cwhile b I C)"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P (Cwhile b I C) Q"
proof (rule invariant_translateI)
  let ?I = "make_semantic_assertion \<Gamma> F I"
  assume asm0: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F (Cwhile b I C)))"
    "ConcreteSemantics.SL_proof \<Delta> P (fst (translate \<Gamma> F (Cwhile b I C))) Q"
  then have r1: "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C))"
    using proof_obligations_valid_union by fastforce
  moreover obtain B where B_def: "ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>) (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Gamma> F C);; Exhale ?I) B"
    by (metis (no_types, lifting) asm0(1) insertCI proof_obligations_valid_def proof_obligations_valid_union snd_eqD translate.simps(10))
  moreover obtain R0 R1 where R_defs: "entails P (R0 \<otimes> ?I)" "Q = R1 \<otimes> (?I \<inter> assertify_bexp (Bnot b))"
    "ConcreteSemantics.SL_proof \<Delta> R0 (ConcreteSemantics.havoc_list (wrL C)) R1"
    using asm0(2) by auto
  moreover have "entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - (set (wrL C))"
    using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) assms(4) by blast

  (* R1 is the frame *)

  show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] Cwhile b I C [Q \<otimes> atrue \<Delta>]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile>CSL [(?I \<otimes> atrue \<Delta>) \<otimes> R1] Cwhile b I C [((?I \<otimes> atrue \<Delta>) \<inter> (assertify_bexp (Bnot b))) \<otimes> R1]"
    proof (rule RuleFrame)
      show "\<Delta> \<turnstile>CSL [?I \<otimes> atrue \<Delta>] Cwhile b I C [(?I \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b)]"
      proof (rule RuleWhile)
        show "\<Delta> \<turnstile>CSL [(?I \<otimes> atrue \<Delta>) \<inter> assertify_bexp b] C [?I \<otimes> atrue \<Delta>]"
        proof (rule RuleCons)
          show "\<Delta> \<turnstile>CSL [atrue \<Delta> \<otimes> ?I \<inter> assertify_bexp b \<otimes> atrue \<Delta>] C [B \<otimes> ?I \<otimes> atrue \<Delta>]"
            using invariant_translate_inhale_exhale_get_proof[OF _ B_def]
            using assms(1) r1 by blast
          show "B \<otimes> ?I \<otimes> atrue \<Delta> \<subseteq> ?I \<otimes> atrue \<Delta>"
            using B_def drop_conjunct_entails by blast
          show "(?I \<otimes> atrue \<Delta>) \<inter> assertify_bexp b \<subseteq> atrue \<Delta> \<otimes> (?I \<inter> assertify_bexp b) \<otimes> atrue \<Delta>"
            by (metis (no_types, lifting) add_set_asso add_set_commm atrue_twice_equal intersect_and_star)
        qed
      qed
      show "disjoint (fvA \<Delta> R1) (wrC (Cwhile b I C))"
        using \<open>entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - set (wrL C)\<close> disjoint_def wrL_wrC_same by fastforce
      show "TypedEqui.self_framing_typed \<Delta> (?I \<otimes> atrue \<Delta>)"
        using assms(3) self_framing_typed_star_atrue by auto
      show "TypedEqui.self_framing_typed \<Delta> R1"
        using ConcreteSemantics.proofs_are_self_framing_and_typed assms(2) calculation(5) by blast
      show "TypedEqui.typed_assertion \<Delta> (?I \<otimes> atrue \<Delta>)"
        using assms(3) typed_assertion_star_atrue by auto
      show "TypedEqui.typed_assertion \<Delta> R1"
        using ConcreteSemantics.proofs_are_self_framing_and_typed assms(2) calculation(5) by blast
    qed
    have "P \<subseteq> R1 \<otimes> ?I"
      by (meson \<open>entails R0 R1 \<and> fvA \<Delta> R1 \<subseteq> fvA \<Delta> R0 - set (wrL C)\<close> add_set_mono calculation(3) entails_def equalityD1 subset_trans)
    then show "P \<otimes> atrue \<Delta> \<subseteq> ?I \<otimes> atrue \<Delta> \<otimes> R1"
      by (smt (verit, best) add_set_asso add_set_commm add_set_mono atrue_twice_equal atrue_twice_same)
    show "(?I \<otimes> atrue \<Delta>) \<inter> assertify_bexp (Bnot b) \<otimes> R1 \<subseteq> Q \<otimes> atrue \<Delta>"
      by (smt (verit, del_insts) add_set_asso add_set_commm add_set_mono calculation(4) intersect_and_star subsetI)
  qed
qed


lemma invariant_translate_induct:
  assumes "wf_stmt \<Gamma> F \<Delta> C"
      and "well_typed_cmd \<Delta> C"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
      and "TypedEqui.wf_context \<Delta>"
    shows "invariant_translate \<Gamma> F \<Delta> P C Q"
  using assms
proof (induct C arbitrary: P Q)
  case (Cseq C1 C2)
  then show ?case
    by (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff fst_eqD invariant_translate_seq snd_conv translate.simps(7) well_typed_cmd_aux.simps(2) wf_stmt.simps(1))
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  let ?P1 = "make_semantic_assertion \<Gamma> F P1"
  let ?P2 = "make_semantic_assertion \<Gamma> F P2"
  let ?Q1 = "make_semantic_assertion \<Gamma> F Q1"
  let ?Q2 = "make_semantic_assertion \<Gamma> F Q2"
  show ?case
  proof (rule invariant_translate_parallel[of _ _ \<Delta> C1 C2 P1 Q1 P2 Q2 P])
    show "ConcreteSemantics.wf_abs_stmt \<Delta> (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      using Cpar.prems(3) by fastforce
    show "wf_stmt \<Gamma> F \<Delta> {P1} C1 {Q1} || {P2} C2 {Q2}"
      using Cpar.prems(1) by blast
    fix P Q
    show "invariant_translate \<Gamma> F \<Delta> P C1 Q"
    proof (rule Cpar(1))
      have "ConcreteSemantics.wf_abs_stmt \<Delta> (Inhale ?P1;; fst (translate \<Gamma> F C1);; Exhale ?Q1)"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C1))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd \<Delta> C1"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Gamma> F \<Delta> C1"
        using Cpar.prems(1) by auto
    qed (simp add: Cpar)
    show "invariant_translate \<Gamma> F \<Delta> P C2 Q"
    proof (rule Cpar(2))
      have "ConcreteSemantics.wf_abs_stmt \<Delta> (Inhale ?P2;; fst (translate \<Gamma> F C2);; Exhale ?Q2)"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C2))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd \<Delta> C2"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Gamma> F \<Delta> C2"
        using Cpar.prems(1) by auto
    qed (simp add: Cpar)
  qed (simp add: Cpar)
next
  case (Cif b C1 C2)
  show ?case
  proof (rule invariant_translate_if[of _ _ \<Delta> C1 C2 P b ])
    fix P Q
    show "invariant_translate \<Gamma> F \<Delta> P C1 Q"
    proof (rule Cif(1))
      show "wf_stmt \<Gamma> F \<Delta> C1"
        using Cif.prems(1) by auto
      show "well_typed_cmd \<Delta> C1"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C1))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed (simp add: Cif)
    show "invariant_translate \<Gamma> F \<Delta> P C2 Q"
    proof (rule Cif(2))
      show "wf_stmt \<Gamma> F \<Delta> C2"
        using Cif.prems(1) by auto
      show "well_typed_cmd \<Delta> C2"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C2))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed (simp add: Cif)
  qed
next
  case (Cwhile b I C)
  let ?I = "make_semantic_assertion \<Gamma> F I"
  show ?case
  proof (rule invariant_translate_while)
    show "ConcreteSemantics.wf_abs_stmt \<Delta> (ConcreteSemantics.havoc_list (wrL C))"
      using Cwhile.prems(3) by force
    show "wf_stmt \<Gamma> F \<Delta> (Cwhile b I C)"
      using Cwhile.prems(1) by auto
    fix P Q show "invariant_translate \<Gamma> F \<Delta> P C Q"
    proof (rule Cwhile(1)[of P Q])
      show "wf_stmt \<Gamma> F \<Delta> C"
        using Cwhile.prems(1) by auto
      show "well_typed_cmd \<Delta> C"
        using Cwhile.prems(2) by auto
      have "ConcreteSemantics.wf_abs_stmt \<Delta> (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Gamma> F C);; Exhale ?I)"
        using Cwhile.prems(4) by fastforce
      then show "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C))" by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
        using Cwhile.prems(4) by auto
    qed (simp add: Cwhile)
  qed (simp add: Cwhile)
qed (simp_all add: invariant_translate_skip invariant_translate_free invariant_translate_alloc invariant_translate_seq
      invariant_translate_write invariant_translate_read invariant_translate_assign)


theorem sound_translation:
  assumes "wf_stmt \<Gamma> F \<Delta> C"
      and "well_typed_cmd \<Delta> C"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> (fst (translate \<Gamma> F C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt \<Delta> Cv"
      and "TypedEqui.wf_assertion \<Delta> P \<and> TypedEqui.wf_assertion \<Delta> Q"
      and "ConcreteSemantics.self_framing_and_typed \<Delta> P \<and> TypedEqui.typed_assertion \<Delta> P"

      and "ConcreteSemantics.verifies_set \<Delta> (atrue \<Delta>) (Inhale P;; fst (translate \<Gamma> F C);; Exhale Q)"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> F C) \<Longrightarrow> ConcreteSemantics.verifies_set \<Delta> (atrue \<Delta>) Cv"

      and "TypedEqui.wf_context \<Delta>"
    shows "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>]"
proof -
  obtain B where "ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>) (Inhale P;; fst (translate \<Gamma> F C);; Exhale Q) B"
    by (metis ConcreteSemantics.Viper_implies_SL_proof ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(3) ConcreteSemantics.wf_abs_stmt.simps(7) assms(3) assms(5) assms(7) atrue_self_framing_and_typed(1) atrue_self_framing_and_typed(2))
  then obtain B' where "ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta> \<otimes> P) (fst (translate \<Gamma> F C)) B'" "entails B' (B \<otimes> Q)"
    by blast


  show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta>] C [Q \<otimes> atrue \<Delta>]"
  proof (rule RuleCons)
    show "\<Delta> \<turnstile>CSL [P \<otimes> atrue \<Delta> \<otimes> atrue \<Delta>] C [B' \<otimes> atrue \<Delta>]"
    proof (rule invariant_translateE[of _ _ \<Delta> "P \<otimes> atrue \<Delta>" C])
      show "ConcreteSemantics.SL_proof \<Delta> (P \<otimes> atrue \<Delta>) (fst (translate \<Gamma> F C)) B'"
        by (metis \<open>ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta> \<otimes> P) (fst (translate \<Gamma> F C)) B'\<close> add_set_commm)
      show "invariant_translate \<Gamma> F \<Delta> (P \<otimes> atrue \<Delta>) C B'"
        by (simp add: assms(1) assms(2) assms(3) assms(4) assms(9) invariant_translate_induct)
      show "proof_obligations_valid \<Delta> (snd (translate \<Gamma> F C))"
        unfolding proof_obligations_valid_def
      proof clarify
        fix Cv assume "Cv \<in> snd (translate \<Gamma> F C)"
        then show "\<exists>B. ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>) Cv B"
          by (simp add: ConcreteSemantics.Viper_implies_SL_proof assms(4) assms(8))
      qed
    qed
    show "P \<otimes> atrue \<Delta> \<subseteq> P \<otimes> atrue \<Delta> \<otimes> atrue \<Delta>"
      by (simp add: add_set_asso atrue_twice_equal)
    show "B' \<otimes> atrue \<Delta> \<subseteq> Q \<otimes> atrue \<Delta>"
      by (smt (verit, ccfv_SIG) ConcreteSemantics.proofs_are_self_framing_and_typed ConcreteSemantics.semantics_axioms \<open>ConcreteSemantics.SL_proof \<Delta> (atrue \<Delta>) (abs_stmt.Inhale P ;; fst (translate \<Gamma> F C) ;; abs_stmt.Exhale Q) B\<close> \<open>entails B' (B \<otimes> Q)\<close> add_set_mono assms(3) assms(5) atrue_twice_equal drop_conjunct_entails entails_def order.trans semantics.wf_abs_stmt.simps(2) semantics.wf_abs_stmt.simps(3) semantics.wf_abs_stmt.simps(7))
  qed
qed


end