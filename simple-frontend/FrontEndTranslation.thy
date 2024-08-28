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

lemma RuleCons:
  assumes "\<Delta> \<turnstile>CSL [P] C [Q]"
      and "P' \<subseteq> P"
      and "Q \<subseteq> Q'"
    shows "\<Delta> \<turnstile>CSL [P'] C [Q']"
  using RuleConsTyped assms(1) assms(2) assms(3) subset_entails by blast

lemma convert_proof_assign:
  assumes "ConcreteSemantics.SL_proof tcfe A (abs_stmt.LocalAssign x (semantify_exp e)) B"
  shows "tcfe \<turnstile>CSL [A] Cassign x e [B]"
proof -
  have "B = ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A"
    using ConcreteSemantics.SL_proof_LocalAssign_elim assms
    by fast
  moreover have "tcfe \<turnstile>CSL [A] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
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
    show "tcfe \<turnstile>CSL [sub_pre x e (ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A)] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
      by (simp add: RuleAssign)
  qed (simp)
  ultimately show ?thesis by auto
qed

lemma convert_proof_skip:
  assumes "ConcreteSemantics.SL_proof tcfe A Skip B"
  shows "tcfe \<turnstile>CSL [A] Cskip [B]"
  using RuleSkip assms by blast

lemma conjunct_with_true_entails:
  "(P :: ('a :: pcm_with_core) set) \<subseteq> UNIV \<otimes> P"
proof
  fix \<omega> assume "\<omega> \<in> P"
  then have "Some \<omega> = |\<omega>| \<oplus> \<omega>"
    by (simp add: commutative core_is_smaller)
  then show "\<omega> \<in> UNIV \<otimes> P"
    using \<open>\<omega> \<in> P\<close> x_elem_set_product by blast
qed

(*
definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" where
  "make_semantic_assertion tcfe F A = well_typedly tcfe F (\<langle>type_ctxt_front_end, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
*)


abbreviation tcfe :: "(int val, char list \<Rightarrow> int val set option) abs_type_context" where
  "tcfe \<equiv> type_ctxt_front_end"

fun wf_stmt where
  "wf_stmt \<Gamma> F (Cseq C1 C2) \<longleftrightarrow> wf_stmt \<Gamma> F C1 \<and> wf_stmt \<Gamma> F C2"
| "wf_stmt \<Gamma> F (Calloc r e) \<longleftrightarrow> r \<notin> fvE e"

| "wf_stmt \<Gamma> F ({P1} C1 {Q1} || {P2} C2 {Q2}) \<longleftrightarrow>
  disjoint
  (fvC C1 \<union> fvA tcfe ((make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1) \<otimes> UNIV)) (wrC C2)
  \<and> disjoint (fvC C2 \<union> fvA tcfe ((make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2) \<otimes> UNIV)) (wrC C1) \<and>
  self_framing (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1)
  \<and> self_framing (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2) \<and>
  wf_stmt \<Gamma> F C1 \<and> wf_stmt \<Gamma> F C2"

| "wf_stmt \<Gamma> F (Cif b C1 C2) \<longleftrightarrow> wf_stmt \<Gamma> F C1 \<and> wf_stmt \<Gamma> F C2"

| "wf_stmt \<Gamma> F (Cwhile b I C) \<longleftrightarrow> self_framing (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I)
                              \<and> wf_stmt \<Gamma> F C"

| "wf_stmt \<Gamma> F _ \<longleftrightarrow> True"

lemma atrue_self_framing_and_typed[simp]:
  "self_framing UNIV"
  by (simp add: self_framing_def)

(*
lemma wf_context_type_context[simp]:
  "TypedEqui.wf_context tcfe"
  unfolding TypedEqui.wf_context_def
proof -
  have "dom (variables tcfe) \<subseteq> {x. x < undefined}"
    by (metis CollectI abs_type_context.select_convs(1) domIff subsetI type_ctxt_front_end_def type_ctxt_store_def)
  then show "finite (dom (variables tcfe))"
    by (simp add: finite_subset)
qed
*)

(*
Set.filter (typed \<Delta> \<circ> stabilize) P
*)

lemma tcfe_is_finite:
  "TypedEqui.finite_context tcfe"
  unfolding TypedEqui.finite_context_def type_ctxt_front_end_def type_ctxt_store_def
  by (metis (mono_tags, lifting) abs_type_context.select_convs(1) domIff finite_nat_set_iff_bounded)



abbreviation inhalify where
  "inhalify P \<equiv> Set.filter (typed tcfe \<circ> stabilize) P"

abbreviation stab_inhalify where
  "stab_inhalify P \<equiv> inhalify (Stabilize P)"

abbreviation t_entails where
  "t_entails \<equiv> ConcreteSemantics.entails_typed tcfe"

lemma conjunct_with_true_t_entails:
  "t_entails P (UNIV \<otimes> P)"
  by (simp add: conjunct_with_true_entails subset_entails)


(*
| RuleStabilizeTyped: "\<Delta> \<turnstile>CSL [P] C [Q] \<Longrightarrow> \<Delta> \<turnstile>CSL [Stabilize P] C [Stabilize Q]"
*)

lemma convert_proof_alloc:
  assumes "ConcreteSemantics.SL_proof tcfe P (Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))) Q"
      and "well_typed_cmd tcfe (Calloc r e)"
      and "wf_stmt \<Gamma> type_ctxt_front_end_syntactic (Calloc r e)"
  shows "tcfe \<turnstile>CSL [P] Calloc r e [Q]"
proof (rule RuleConsTyped)

  have asm0: "ConcreteSemantics.SL_proof tcfe P (Havoc r) (TypedEqui.exists_assert tcfe r P)
  \<and> ConcreteSemantics.SL_proof tcfe (TypedEqui.exists_assert tcfe r P) (Inhale (Stabilize (full_ownership_with_val r e))) Q
  \<and> self_framing P"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim assms(1))
  then have "Q = TypedEqui.exists_assert tcfe r P \<otimes> inhalify (Stabilize (full_ownership_with_val r e))"
    by blast

  show "tcfe \<turnstile>CSL [UNIV \<otimes> TypedEqui.exists_assert tcfe r P] Calloc r e [inhalify (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert tcfe r P]"
  proof (rule RuleFrame)
    have "r \<notin> fvE e"
      using assms(3) by auto
    then have "tcfe \<turnstile>CSL [UNIV] Calloc r e [full_ownership_with_val r e]"
      using RuleAlloc[of r e] by simp
    then show "tcfe \<turnstile>CSL [UNIV] Calloc r e [inhalify (Stabilize (full_ownership_with_val r e))]"
      using RuleStabilizeTyped by (metis RuleInhalify Stabilize_UNIV)

    show "disjoint (fvA tcfe (TypedEqui.exists_assert tcfe r P)) (wrC (Calloc r e))"
      using ConcreteSemantics.exists_assert_no_in_fv disjoint_def
      using tcfe_is_finite by fastforce

    show "self_framing (TypedEqui.exists_assert tcfe r P)"
      using asm0 by fastforce
  qed (simp)
  then have "t_entails P (TypedEqui.exists_assert tcfe r P)"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim_entails asm0 assms(2) option.simps(3) tcfe_is_finite well_typed_cmd_aux.simps(6))

  then show "t_entails P (UNIV \<otimes> TypedEqui.exists_assert tcfe r P)"
    using ConcreteSemantics.entails_typed_trans conjunct_with_true_t_entails by blast
  
  show "t_entails (inhalify (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert tcfe r P) Q"
    by (simp add: ConcreteSemantics.entails_typed_refl \<open>Q = TypedEqui.exists_assert tcfe r P \<otimes> inhalify (Stabilize (full_ownership_with_val r e))\<close> add_set_commm)
qed

lemma helper_exhale_encoding:
  assumes "ConcreteSemantics.SL_proof tcfe P (Exhale (Stabilize A)) Q"
  shows "P \<subseteq> Stabilize A \<otimes> Q"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize A)" "self_framing P" "self_framing Q"
  show "P \<subseteq> Stabilize A \<otimes> Q"
  proof
    fix \<omega> assume asm1: "\<omega> \<in> P"
    then obtain q a where "q \<in> Q" "a \<in> Stabilize A" "Some \<omega> = q \<oplus> a"
      by (meson asm0(1) entails_def subsetD x_elem_set_product)
    then have "stabilize a \<in> A"
      by force
    then show "\<omega> \<in> Stabilize A \<otimes> Q"
      by (metis (no_types, lifting) \<open>\<And>thesis. (\<And>q a. \<lbrakk>q \<in> Q; a \<in> Stabilize A; Some \<omega> = q \<oplus> a\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> add_set_commm x_elem_set_product)
  qed  
qed

lemma convert_proof_free:
  assumes "ConcreteSemantics.SL_proof tcfe P (Exhale (Stabilize (full_ownership r))) Q"
  shows "tcfe \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize (full_ownership r))" "self_framing P" "self_framing Q"
  show "tcfe \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "tcfe \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> Q] Cfree r [Stabilize (UNIV) \<otimes> Q]"
    proof (rule RuleFrame)
      show "tcfe \<turnstile>CSL [Stabilize (full_ownership r)] Cfree r [Stabilize (UNIV)]"
        using RuleFree RuleStabilizeTyped by blast
    qed (simp_all add: asm0)
    show "P \<subseteq> Stabilize (full_ownership r) \<otimes> Q"
      by (simp add: assms helper_exhale_encoding)
    show "Stabilize (UNIV) \<otimes> Q \<subseteq> Q \<otimes> UNIV"
      by (simp add: add_set_commm)
  qed
qed

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
  assumes "TypedEqui.typed tcfe \<omega>'"
      and "\<omega>' \<succeq> \<omega>"
      and "\<omega> \<in> A"
    shows "\<omega>' \<in> A \<otimes> UNIV"
proof -
  obtain r where "Some \<omega>' = \<omega> \<oplus> r"
    using assms(2) greater_def by blast
  then have "r \<in> UNIV"
    using TypedEqui.typed_smaller assms(1) greater_equiv by blast
  then show ?thesis
    using \<open>Some \<omega>' = \<omega> \<oplus> r\<close> assms(3) x_elem_set_product by blast
qed

lemma in_StabilizeI:
  assumes "stabilize \<omega> \<in> A"
  shows "\<omega> \<in> Stabilize A"
  by (simp add: assms)

lemma convert_proof_write:
  assumes "ConcreteSemantics.SL_proof tcfe P (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e))) Q"
  shows "tcfe \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Custom_elim)
  assume asm0: "SL_Custom tcfe P (custom.FieldAssign (semantify_addr r) field_val (semantify_exp e)) Q"
  "self_framing P" "self_framing Q"
  show "tcfe \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    using asm0(1)
  proof (rule SL_custom_FieldAssign)
    assume asm1: "Q = update_value tcfe P (semantify_addr r) field_val (semantify_exp e)"
      "self_framing P" "entails P {\<omega>. \<exists>l. get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l}"
      "framed_by_exp P (semantify_addr r)" "framed_by_exp P (semantify_exp e)"
    show "tcfe \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    proof (rule RuleCons)
      let ?F = "Stabilize { remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
      show "tcfe \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> ?F] Cwrite r e [Stabilize (full_ownership_with_val r e) \<otimes> ?F]"
      proof (rule RuleFrame)
        show "tcfe \<turnstile>CSL [Stabilize (full_ownership r)] Cwrite r e [Stabilize (full_ownership_with_val r e)]"
          by (simp add: RuleStabilizeTyped RuleWrite)
      qed (simp_all)
      show "P \<subseteq> Stabilize (full_ownership r) \<otimes> ?F"
      proof
        fix \<omega> assume "\<omega> \<in> P"
        then obtain l where "get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l"          
          by (smt (verit) CollectD asm1(3) entails_def subsetD)
        then have "Some \<omega> = remove_only \<omega> (l, field_val) \<oplus> set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))"
          using split_remove_only_owns_only by blast
        moreover have "set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))) \<in> Stabilize (full_ownership r)"        
        proof (rule in_StabilizeI)
          show "stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))) \<in> full_ownership r"
            apply (rule in_full_ownership[of _ _ l])
            using \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> semantify_addr_equiv apply auto[1]
            by (smt (verit, best) \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> add.commute add.right_neutral calculation fun_upd_apply get_m_additive get_m_stabilize remove_only_charact(2))
        qed
        moreover have "remove_only \<omega> (l, field_val) \<in> ?F"
        proof (rule in_StabilizeI)
          have "stabilize (remove_only \<omega> (l, field_val)) = remove_only (stabilize \<omega>) (l, field_val)"
            by (simp add: remove_only_stabilize)
          then show "stabilize (remove_only \<omega> (l, field_val)) \<in> {remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
            by (smt (verit, best) AbstractSemantics.get_store_stabilize CollectI \<open>\<omega> \<in> P\<close> \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> asm1(2) self_framing_def semantify_addr_equiv)
        qed
        ultimately show "\<omega> \<in> Stabilize (full_ownership r) \<otimes> ?F"
          using commutative x_elem_set_product by fastforce
      qed
      show "Stabilize (full_ownership_with_val r e) \<otimes> ?F \<subseteq> Q \<otimes> UNIV"
      proof
        fix \<omega>' assume "\<omega>' \<in> Stabilize (full_ownership_with_val r e) \<otimes> ?F"
        then obtain ptr f where r: "Some \<omega>' = ptr \<oplus> f" "ptr \<in> Stabilize (full_ownership_with_val r e)" "f \<in> ?F"
          by (meson x_elem_set_product)
        then obtain l where "get_store (stabilize ptr) r = Some (VRef (Address l)) \<and> get_m (stabilize ptr) (l, field_val) = 1
  \<and> get_h (stabilize ptr) (l, field_val) = Some (VInt (edenot e (get_store (stabilize ptr))))"
          using full_ownership_with_val_def by auto
        then have "get_store ptr r = Some (VRef (Address l)) \<and> get_m ptr (l, field_val) = 1
  \<and> get_h ptr (l, field_val) = Some (VInt (edenot e (get_store ptr)))"
          by (simp add: stabilize_value_persists)
        then have "get_store \<omega>' r = Some (VRef (Address l)) \<and> get_m \<omega>' (l, field_val) = 1
  \<and> get_h \<omega>' (l, field_val) = Some (VInt (edenot e (get_store \<omega>')))"
          using r(1) larger_mask_full
          by (metis (no_types, lifting) in_set_sum is_in_set_sum r(3) read_helper singletonD state_add_iff)

        moreover obtain \<omega> l' where "stabilize f = remove_only \<omega> (l', field_val)" "\<omega> \<in> P" "semantify_addr r \<omega> = Some l'"
          using r(3) by auto
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

        moreover have "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) \<in> update_value tcfe P (semantify_addr r) field_val (semantify_exp e)"
          using \<open>\<omega> \<in> P\<close> \<open>semantify_addr r \<omega> = Some l'\<close> semantify_exp_def
        proof (rule in_update_value)
          show "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) = update_heap_val \<omega> (l', field_val) (VInt (edenot e (get_store \<omega>)))"
            by (metis calculation(2) calculation(3) get_store_set_state greater_charact)
          show "typed_value tcfe field_val (VInt (edenot e (get_store \<omega>)))"
          proof (rule typed_valueI)
            fix ty assume "custom_context tcfe field_val = Some ty"
            then show "VInt (edenot e (get_store \<omega>)) \<in> ty"
              using \<open>l = l'\<close> AbstractSemantics.get_store_stabilize 
            \<open>get_store ptr r = Some (VRef (Address l)) \<and> get_m ptr (l, field_val) = 1 \<and> get_h ptr (l, field_val) = Some (VInt (edenot e (get_store ptr)))\<close>
             \<open>stabilize f = remove_only \<omega> (l', field_val)\<close>  full_add_charact(1)
            full_add_defined get_store_set_state in_update_value r(1) r(2) remove_only_def  snd_conv typed_get_vh
              by (smt (verit) CollectI abs_type_context.select_convs(2) option.sel type_ctxt_front_end_def type_ctxt_heap_def vints_def)
          qed
        qed
        ultimately show "\<omega>' \<in> Q \<otimes> UNIV"
          using asm1(1) greater_def x_elem_set_product by blast
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
  assumes "ConcreteSemantics.SL_proof tcfe P (LocalAssign x (semantify_heap_loc r)) Q"
  shows "tcfe \<turnstile>CSL [P] Cread x r [Q]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_LocalAssign_elim)
  assume asm0: "Q = ConcreteSemantics.post_substitute_var_assert x (semantify_heap_loc r) P"
    "framed_by_exp P (semantify_heap_loc r)"
    "self_framing P"

  have r: "\<And>\<omega>. \<omega> \<in> P \<Longrightarrow> (\<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0
  \<and> (\<exists>v0. get_h \<omega> (l, field_val) = Some v0))"
  proof -
    fix \<omega>
    assume asm1: "\<omega> \<in> P"
    then obtain l v0 where "get_store \<omega> r = Some (VRef (Address l))" "get_h \<omega> (l, field_val) = Some v0"
      by (metis asm0(2) framed_by_exp_def semantify_heap_loc_def)
(*
    then obtain v where "v0 = VInt v"
      sorry
      using TypedEqui.typed_assertionE[OF asm0(4) asm1] TypedEqui.typed_def[of tcfe \<omega>] well_typedE(1)[of "custom_context tcfe" "get_abs_state \<omega>"]
      Instantiation.well_typed_heapE[of "custom_context tcfe" "get_state \<omega>" "(l, field_val)" v0]
      by (smt (verit, del_insts) CollectD abs_type_context.select_convs(2) option.sel snd_conv snd_get_abs_state type_ctxt_front_end_def type_ctxt_heap_def vints_def)
*)
    then have "stabilize \<omega> \<in> P"
      using asm0(3) asm1 self_framingE by blast
    then have "get_h (stabilize \<omega>) (l, field_val) = Some v0"
      by (metis (no_types, lifting) AbstractSemantics.get_store_stabilize \<open>get_h \<omega> (l, field_val) = Some v0\<close> \<open>get_store \<omega> r = Some (VRef (Address l))\<close> asm0(2) framed_by_exp_def get_address_simp semantify_heap_loc_def stabilize_value_persists)
    then have "get_m \<omega> (l, field_val) > 0"
      using EquiSemAuxLemma.gr_0_is_ppos stable_virtual_state_def by fastforce
    then show "(\<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0
  \<and> (\<exists>v0. get_h \<omega> (l, field_val) = Some v0))"
      using \<open>get_h \<omega> (l, field_val) = Some v0\<close> \<open>get_store \<omega> r = Some (VRef (Address l))\<close> by blast
  qed

  show "tcfe \<turnstile>CSL [P] Cread x r [Q]"
  proof (rule RuleCons)
    show "tcfe \<turnstile>CSL [P] Cread x r [read_result P x r]"
    proof (rule RuleRead)
      show "P \<subseteq> read_perm r" (* Should come from framed_by_exp *)
        using r
        unfolding read_perm_def 
        sorry
        by (simp add: subsetI)
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

abbreviation make_semantic_wf where
  "make_semantic_wf \<Gamma> P \<equiv> Stabilize (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P)"

fun translate (* :: "cmd \<Rightarrow> (v_stmt \<times> v_stmt set)" *) where
  "translate \<Gamma> Cskip = (Skip, {})"
| "translate \<Gamma> (Cassign x e) = (LocalAssign x (semantify_exp e), {})"

| "translate \<Gamma> (Calloc r e) = ((Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))), {})"
| "translate \<Gamma> (Cfree r) = (Exhale (Stabilize (full_ownership r)), {})"
| "translate \<Gamma> (Cwrite r e) = (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e)), {})"
| "translate \<Gamma> (Cread x r) = (LocalAssign x (semantify_heap_loc r), {})"

| "translate \<Gamma> (Cseq C1 C2) = (let r1 = translate \<Gamma> C1 in let r2 = translate \<Gamma> C2 in
  (fst r1;; fst r2, snd r1 \<union> snd r2))"

| "translate \<Gamma> (Cif b C1 C2) = (If (semantify_bexp b) (fst (translate \<Gamma> C1)) (fst (translate \<Gamma> C2)), snd (translate \<Gamma> C1) \<union> snd (translate \<Gamma> C2))"

| "translate \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2);;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)),
  let r1 = translate \<Gamma> C1 in let r2 = translate \<Gamma> C2 in
  { (Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1);; fst r1;; Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1)),
  (Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2);; fst r2;; Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)) } \<union> snd r1 \<union> snd r2)"

| "translate \<Gamma> (Cwhile b I C) = (Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I);;
  ConcreteSemantics.havoc_list (wrL C);; Inhale ((make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I) \<inter> assertify_bexp (Bnot b)),
  { Inhale ((make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I) \<inter> assertify_bexp b);; fst (translate \<Gamma> C);; Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I) } \<union> snd (translate \<Gamma> C))"

lemma CSL_weaken_post_atrue:
  assumes "tcfe \<turnstile>CSL [P] C [Q]"
      and 
  shows "tcfe \<turnstile>CSL [P] C [Q \<otimes> UNIV]"
  using assms(1)
proof (rule RuleCons)
  show "Q \<subseteq> Q \<otimes> UNIV"
    using add_set_commm assms(2) conjunct_with_true_entails by blast
qed (simp)

lemma CSL_add_atrue:
  assumes "tcfe \<turnstile>CSL [P] C [Q]"
      and "self_framing P"
      and "TypedEqui.typed_assertion tcfe P"
      and "TypedEqui.wf_context tcfe"
    shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  by (rule RuleFrame) (simp_all add: assms)


definition proof_obligations_valid where
  "proof_obligations_valid S \<longleftrightarrow> (\<forall>Cv \<in> S. \<exists>B. ConcreteSemantics.SL_proof tcfe (UNIV) Cv B)"

lemma proof_obligations_valid_union:
  "proof_obligations_valid (S1 \<union> S2) \<longleftrightarrow> proof_obligations_valid S1 \<and> proof_obligations_valid S2"
  by (meson Un_iff proof_obligations_valid_def)

definition invariant_translate where
  "invariant_translate \<Gamma> P C Q \<longleftrightarrow>
  ((proof_obligations_valid (snd (translate \<Gamma> C)) \<and> ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C)) Q) \<longrightarrow> tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV])"

lemma invariant_translateE:
  assumes "invariant_translate \<Gamma> P C Q"
      and "proof_obligations_valid (snd (translate \<Gamma> C))"
      and "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C)) Q"
    shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  using assms(1) assms(2) assms(3) invariant_translate_def by blast


lemma invariant_translateI:
  assumes "proof_obligations_valid (snd (translate \<Gamma> C)) \<Longrightarrow> ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C)) Q
    \<Longrightarrow> tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  shows "invariant_translate \<Gamma> P C Q"
  using assms invariant_translate_def proof_obligations_valid_def by blast

lemma invariant_translate_simpler:
  assumes "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C)) Q \<Longrightarrow> tcfe \<turnstile>CSL [P] C [Q]"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C))"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P C Q"
  by (simp add: CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms invariant_translateI)

corollary invariant_translate_skip:
  assumes "TypedEqui.wf_context tcfe"
  shows "invariant_translate \<Gamma> P Cskip Q"
  using convert_proof_skip invariant_translate_simpler assms  
  by (metis ConcreteSemantics.wf_abs_stmt.simps(1) fst_eqD translate.simps(1))

corollary invariant_translate_assign:
  assumes "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> (Cassign x e)))"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P (Cassign x e) Q"
  using convert_proof_assign invariant_translate_simpler assms
  by (metis fst_eqD translate.simps(2))


corollary invariant_translate_alloc:
  assumes "well_typed_cmd tcfe (Calloc r e)"
      and "wf_stmt \<Gamma> type_ctxt_front_end_syntactic (Calloc r e)"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> (Calloc r e)))"
    shows "invariant_translate \<Gamma> P (Calloc r e) Q"
  using assms cmd.distinct(37) convert_proof_alloc invariant_translate_simpler
  by (metis fst_eqD translate.simps(3) wf_context_type_context)

lemma atrue_twice_same:
  "UNIV \<otimes> UNIV \<subseteq> UNIV"
  unfolding add_set_def
  by (smt (z3) Collect_mono_iff TypedEqui.typed_sum mem_Collect_eq)

lemma atrue_twice_equal:
  "UNIV \<otimes> UNIV = UNIV"
proof
  show "UNIV \<subseteq> UNIV \<otimes> UNIV"
  proof
    fix x assume "x \<in> UNIV"
    then have "Some x = x \<oplus> |x|"
      using core_is_smaller by blast
    then have "|x| \<in> UNIV"
      using TypedEqui.typed_core \<open>x \<in> UNIV\<close> by blast
    then show "x \<in> UNIV \<otimes> UNIV"
      using \<open>Some x = x \<oplus> |x|\<close> \<open>x \<in> UNIV\<close> x_elem_set_product by blast
  qed
qed (simp add: atrue_twice_same)


corollary invariant_translate_free:
  assumes "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> (Cfree r)))"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P (Cfree r) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> (Cfree r))) Q"
  then have "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cfree r [(Q \<otimes> UNIV) \<otimes> UNIV]"
    using RuleFrame[OF convert_proof_free]
    by (metis CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms convert_proof_free fst_eqD translate.simps(4))
  then show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cfree r [Q \<otimes> UNIV]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_write:
  assumes "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> (Cwrite r e)))"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P (Cwrite r e) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> (Cwrite r e))) Q"
  then have "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cwrite r e [(Q \<otimes> UNIV) \<otimes> UNIV]"
    using RuleFrame[OF convert_proof_write]
    by (metis CSL_add_atrue ConcreteSemantics.proofs_are_self_framing_and_typed assms convert_proof_write fst_eqD translate.simps(5))
  then show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cwrite r e [Q \<otimes> UNIV]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_read:
  assumes "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> (Cread x r)))"
      and "TypedEqui.wf_context tcfe"
      and "custom_context tcfe = type_ctxt_heap"
    shows "invariant_translate \<Gamma> P (Cread x r) Q"
  using convert_proof_read invariant_translate_simpler assms
  by (metis fst_eqD translate.simps(6))


lemma invariant_translate_seq:
  assumes "\<And>R. invariant_translate \<Gamma> P C1 R"
      and "\<And>R. invariant_translate \<Gamma> R C2 Q"
    shows "invariant_translate \<Gamma> P (Cseq C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid (snd (translate \<Gamma> (Cseq C1 C2)))"
    "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> (Cseq C1 C2))) Q"
  then obtain R where r: "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> C1)) R"
      "ConcreteSemantics.SL_proof tcfe R (fst (translate \<Gamma> C2)) Q"
    by (metis ConcreteSemantics.SL_proof_Seq_elim fst_eqD translate.simps(7))
  show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cseq C1 C2 [Q \<otimes> UNIV]"
  proof (rule RuleSeq)
    show "tcfe \<turnstile>CSL [P \<otimes> UNIV] C1 [R \<otimes> UNIV]"
      using assms(1)[of R] r
      unfolding invariant_translate_def
      by (metis asm0(1) proof_obligations_valid_union snd_conv translate.simps(7))
    show "tcfe \<turnstile>CSL [R \<otimes> UNIV] C2 [Q \<otimes> UNIV]"
    proof (rule RuleCons)
      show "tcfe \<turnstile>CSL [R \<otimes> UNIV] C2 [(Q \<otimes> UNIV) \<otimes> UNIV]"
          using assms(2)[of R] asm0
          unfolding invariant_translate_def proof_obligations_valid_def
          by (metis (no_types, lifting) Un_iff add_set_asso atrue_twice_equal r(2) snd_conv translate.simps(7))
      show "Q \<otimes> UNIV \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
        by (simp add: add_set_asso add_set_mono atrue_twice_same)
    qed (simp)
  qed
qed


lemma invariant_translate_inhale_exhale_get_proof:
  assumes "\<And>P Q. invariant_translate \<Gamma> P C Q"
      and "ConcreteSemantics.SL_proof tcfe P (Inhale A;; fst (translate \<Gamma> C);; Exhale B) Q"
      and "proof_obligations_valid (snd (translate \<Gamma> C))"
    shows "tcfe \<turnstile>CSL [P \<otimes> A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
  using assms(2)
proof (rule ConcreteSemantics.SL_proof_Seq_elim)
  fix R1 assume asm0: "ConcreteSemantics.SL_proof tcfe P (abs_stmt.Inhale A ;; fst (translate \<Gamma> C)) R1"
    "ConcreteSemantics.SL_proof tcfe R1 (abs_stmt.Exhale B) Q"
  then have "entails R1 (Q \<otimes> B)" by auto
  show "tcfe \<turnstile>CSL [P \<otimes> A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
  proof (rule ConcreteSemantics.SL_proof_Seq_elim[OF asm0(1)])
    fix R0 assume asm1: "ConcreteSemantics.SL_proof tcfe P (abs_stmt.Inhale A) R0"
          "ConcreteSemantics.SL_proof tcfe R0 (fst (translate \<Gamma> C)) R1"
    then have "ConcreteSemantics.SL_proof tcfe (P \<otimes> A) (fst (translate \<Gamma> C)) R1"
      by auto
    show "tcfe \<turnstile>CSL [P \<otimes> A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
    proof (rule RuleCons)
      show "tcfe \<turnstile>CSL [P \<otimes> A \<otimes> UNIV] C [R1 \<otimes> UNIV]"
        using \<open>ConcreteSemantics.SL_proof tcfe (P \<otimes> A) (fst (translate \<Gamma> C)) R1\<close> assms(1) assms(3) invariant_translate_def by blast
      show "R1 \<otimes> UNIV \<subseteq> Q \<otimes> B \<otimes> UNIV"
        by (meson \<open>entails R1 (Q \<otimes> B)\<close> add_set_mono entails_def order_refl)
    qed (simp)
  qed
qed


lemma drop_conjunct_entails:
  assumes "TypedEqui.typed_assertion tcfe A"
  shows "A \<otimes> B \<otimes> UNIV \<subseteq> B \<otimes> UNIV"
  by (smt (verit) add_set_asso add_set_commm add_set_def assms atrue_twice_equal mem_Collect_eq subsetI)


(*
| "translate \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (P1 \<otimes> P2);; ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (Q1 \<otimes> Q2)),
  let r1 = translate \<Gamma> C1 in let r2 = translate \<Gamma> C2 in
  { (Inhale P1;; fst r1;; Exhale Q1), (Inhale P2;; fst r2;; Exhale Q2) } \<union> snd r1 \<union> snd r2)"
*)


lemma typed_self_framing_star:
  assumes "self_framing A"
      and "self_framing B"
    shows "self_framing (A \<otimes> B)"
proof (rule TypedEqui.self_framing_typedI)
  fix \<omega>
  assume asm0: "typed tcfe \<omega>"
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
    moreover have "TypedEqui.typed tcfe b'"
      by (smt (verit, ccfv_SIG) TypedEqui.typed_state_axioms \<open>Some (stabilize \<omega>) = a \<oplus> b\<close> \<open>Some b' = b \<oplus> |\<omega>|\<close> addition_bigger asm0 commutative decompose_stabilize_pure greater_def typed_state.typed_smaller)
    ultimately have "b' \<in> B"
      by (metis (no_types, lifting) TypedEqui.typed_smaller TypedEqui.typed_state_axioms \<open>Some b' = b \<oplus> |\<omega>|\<close> \<open>b \<in> B\<close> assms(2) commutative greater_equiv typed_state.self_framing_typed_def)
    then show "\<omega> \<in> A \<otimes> B"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> b\<close> \<open>Some b' = b \<oplus> |\<omega>|\<close> \<open>a \<in> A\<close> asso1 decompose_stabilize_pure x_elem_set_product)
  qed
qed



lemma self_framing_typed_star_atrue:
  assumes "self_framing P"
  shows "self_framing (P \<otimes> UNIV)"
  by (simp add: assms typed_self_framing_star)

lemma typed_assertion_star_atrue:
  assumes "TypedEqui.typed_assertion tcfe P"
  shows "TypedEqui.typed_assertion tcfe (P \<otimes> UNIV)"
  by (simp add: TypedEqui.typed_star assms)




lemma invariant_translate_parallel:
  assumes "\<And>P Q. invariant_translate \<Gamma> P C1 Q"
      and "\<And>P Q. invariant_translate \<Gamma> P C2 Q"
      and "ConcreteSemantics.wf_abs_stmt tcfe (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      and "wf_stmt \<Gamma> F ({P1} C1 {Q1} || {P2} C2 {Q2})"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P ({P1} C1 {Q1} || {P2} C2 {Q2}) Q"
proof (rule invariant_translateI)
  let ?P1 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1"
  let ?P2 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2"
  let ?Q1 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1"
  let ?Q2 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2"

  assume asm0: "proof_obligations_valid (snd (translate \<Gamma> {P1} C1 {Q1} || {P2} C2 {Q2}))"
    "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> {P1} C1 {Q1} || {P2} C2 {Q2})) Q"
  then have r0: "proof_obligations_valid (snd (translate \<Gamma> C1)) \<and> proof_obligations_valid (snd (translate \<Gamma> C2))"
    using proof_obligations_valid_union
    unfolding translate.simps by (metis sndI)
  moreover obtain B1 where B1_def: "ConcreteSemantics.SL_proof tcfe (UNIV)
    (Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1);; fst (translate \<Gamma> C1);; Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1)) B1"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover obtain B2 where B2_def: "ConcreteSemantics.SL_proof tcfe (UNIV)
  (Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2);; fst (translate \<Gamma> C2);; Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)) B2"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover have main: "ConcreteSemantics.SL_proof tcfe P (Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2);;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)) Q"
    using asm0 by simp
  then obtain R0 R1 where R_defs:
    "ConcreteSemantics.SL_proof tcfe P (abs_stmt.Exhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2)) R0"
    "ConcreteSemantics.SL_proof tcfe R0 (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2)) R1"
    "ConcreteSemantics.SL_proof tcfe R1 (abs_stmt.Inhale (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)) Q"
    by (meson ConcreteSemantics.SL_proof_Seq_elim)
  then have P_Q_R_rels:
    "entails P (R0 \<otimes> (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2))
  \<and> Q = R1 \<otimes> (make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1 \<otimes> make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2)" by auto
  moreover have r: "ConcreteSemantics.self_framing_and_typed tcfe R0 \<and>
    ConcreteSemantics.self_framing_and_typed tcfe R1 \<and> entails R0 R1 \<and> fvA tcfe R1 \<subseteq> fvA tcfe R0 - set (wrL C1 @ wrL C2)"
    using ConcreteSemantics.SL_proof_Havoc_list_elim[OF R_defs(2) assms(3) assms(5)] by blast

(* R1 is the frame! *)

  show "tcfe \<turnstile>CSL [P \<otimes> UNIV] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "tcfe \<turnstile>CSL [((?P1 \<otimes> UNIV) \<otimes> (?P2 \<otimes> UNIV)) \<otimes> R1] {P1} C1 {Q1} || {P2} C2 {Q2} [((?Q1 \<otimes> UNIV) \<otimes> (?Q2 \<otimes> UNIV)) \<otimes> R1]"
    proof (rule RuleFrame)
      show "tcfe \<turnstile>CSL [?P1 \<otimes> UNIV \<otimes> (?P2 \<otimes> UNIV)] {P1} C1 {Q1} || {P2} C2 {Q2} [?Q1 \<otimes> UNIV \<otimes> (?Q2 \<otimes> UNIV)]"
      proof (rule RulePar)
        show "tcfe \<turnstile>CSL [?P1 \<otimes> UNIV] C1 [?Q1 \<otimes> UNIV]"
        proof (rule RuleCons)
          show "tcfe \<turnstile>CSL [UNIV \<otimes> ?P1 \<otimes> UNIV] C1 [B1 \<otimes> ?Q1 \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(1) B1_def]
            using r0 by blast
          show "B1 \<otimes> ?Q1 \<otimes> UNIV \<subseteq> ?Q1 \<otimes> UNIV"
            using B1_def drop_conjunct_entails by blast
          show "?P1 \<otimes> UNIV \<subseteq> UNIV \<otimes> ?P1 \<otimes> UNIV"
            by (metis (no_types, lifting) add_set_asso add_set_commm atrue_twice_equal order_refl)
        qed
        show "tcfe \<turnstile>CSL [?P2 \<otimes> UNIV] C2 [?Q2 \<otimes> UNIV]"
        proof (rule RuleCons)
          show "tcfe \<turnstile>CSL [UNIV \<otimes> ?P2 \<otimes> UNIV] C2 [B2 \<otimes> ?Q2 \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(2) B2_def]
            using r0 by blast
          show "B2 \<otimes> ?Q2 \<otimes> UNIV \<subseteq> ?Q2 \<otimes> UNIV"
            using B2_def drop_conjunct_entails by blast
          show "?P2 \<otimes> UNIV \<subseteq> UNIV \<otimes> ?P2 \<otimes> UNIV"
            using add_set_asso add_set_left_comm atrue_twice_equal
            by (metis (no_types, opaque_lifting) order_refl)
        qed
        show "disjoint (fvC C1 \<union> fvA tcfe (?Q1 \<otimes> UNIV)) (wrC C2)"
          using assms(4) by auto
        show "disjoint (fvC C2 \<union> fvA tcfe (?Q2 \<otimes> UNIV)) (wrC C1)"
          using assms(4) by auto
        show "self_framing (?P1 \<otimes> UNIV)"
          using assms(4) typed_self_framing_star by fastforce
        show "self_framing (?P2 \<otimes> UNIV)"
          using assms(4) self_framing_typed_star_atrue by auto
        show "TypedEqui.typed_assertion tcfe (?P1 \<otimes> UNIV)"
          using assms(4) typed_assertion_star_atrue by auto
        show "TypedEqui.typed_assertion tcfe (?P2 \<otimes> UNIV)"
          using assms(4) typed_assertion_star_atrue by auto
      qed
      show "disjoint (fvA tcfe R1) (wrC {P1} C1 {Q1} || {P2} C2 {Q2})"
        by (metis (mono_tags, opaque_lifting) Diff_subset_conv Orderings.order_eq_iff r bot.extremum disjoint_minus disjoint_simps(2) disjoint_simps(3) sup.order_iff wrC.simps(7) wrC.simps(8) wrL.simps(7) wrL_wrC_same)
      show "self_framing (?P1 \<otimes> UNIV \<otimes> (?P2 \<otimes> UNIV))"
        by (meson assms(4) self_framing_typed_star_atrue typed_self_framing_star wf_stmt.simps(3))
      show "TypedEqui.typed_assertion tcfe (?P1 \<otimes> UNIV \<otimes> (?P2 \<otimes> UNIV))"
        using TypedEqui.typed_star assms(4) typed_assertion_star_atrue by auto
      show "self_framing R1"
        using R_defs(3) by blast
      show "TypedEqui.typed_assertion tcfe R1"
        using R_defs(3) by force
    qed
    show "P \<otimes> UNIV \<subseteq> ?P1 \<otimes> UNIV \<otimes> (?P2 \<otimes> UNIV) \<otimes> R1"
    proof -
      have "P \<otimes> UNIV \<subseteq> (R0 \<otimes> (?P1 \<otimes> ?P2)) \<otimes> UNIV"
        by (metis P_Q_R_rels add_set_mono atrue_twice_equal atrue_twice_same entails_def)
      also have "... \<subseteq> R1 \<otimes> ((?P1 \<otimes> ?P2) \<otimes> UNIV)"
        using r add_set_asso add_set_mono entails_def by blast
      also have "... \<subseteq> ?P1 \<otimes> UNIV \<otimes> (?P2 \<otimes> UNIV) \<otimes> R1"
        using add_set_commm add_set_left_comm atrue_twice_equal
        by (smt (verit, del_insts) dual_order.refl)
      finally show ?thesis by simp
    qed
    show "?Q1 \<otimes> UNIV \<otimes> (?Q2 \<otimes> UNIV) \<otimes> R1 \<subseteq> Q \<otimes> UNIV"
      by (metis (no_types, lifting) Orderings.order_eq_iff P_Q_R_rels add_set_asso add_set_commm atrue_twice_equal)
  qed
qed

(*
Maybe prove? Need to prove that assertions are wf...
lemma translation_wf:
  assumes "wf_stmt \<Gamma> F C"
      and "well_typed_cmd tcfe C"
    shows "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C))"
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
  assumes "\<And>P Q. invariant_translate \<Gamma> P C1 Q"
      and "\<And>P Q. invariant_translate \<Gamma> P C2 Q"
    shows "invariant_translate \<Gamma> P (Cif b C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid (snd (translate \<Gamma> (Cif b C1 C2)))"
    "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> (Cif b C1 C2))) Q"

  show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cif b C1 C2 [Q \<otimes> UNIV]"
  proof (rule ConcreteSemantics.SL_proof_If_elim)
    show "ConcreteSemantics.SL_proof tcfe P (abs_stmt.If (semantify_bexp b) (fst (translate \<Gamma> C1)) (fst (translate \<Gamma> C2))) Q"
      by (metis asm0(2) fst_eqD translate.simps(8))
    fix B1 B2 assume asm1: "Q = B1 \<union> B2" "framed_by_exp P (semantify_bexp b)"
       "ConcreteSemantics.SL_proof tcfe (P \<otimes> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)) (fst (translate \<Gamma> C1)) B1"
       "ConcreteSemantics.SL_proof tcfe (P \<otimes> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b))) (fst (translate \<Gamma> C2)) B2"
       "self_framing P" "TypedEqui.typed_assertion tcfe P"
    show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cif b C1 C2 [Q \<otimes> UNIV]"
    proof (rule RuleIf)
      show "tcfe \<turnstile>CSL [(P \<otimes> UNIV) \<inter> assertify_bexp b] C1 [Q \<otimes> UNIV]"
      proof (rule RuleCons)
        show "tcfe \<turnstile>CSL [(P \<otimes> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)) \<otimes> UNIV] C1 [B1 \<otimes> UNIV]"
          by (metis asm0(1) asm1(3) assms(1) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B1 \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> UNIV) \<inter> assertify_bexp b \<subseteq> (P \<otimes> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)) \<otimes> UNIV"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp b"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot b (get_store \<omega>)"
            using in_set_sum[of \<omega> P "UNIV"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "|p| \<in> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)"
            unfolding ConcreteSemantics.pure_typed_def semantify_bexp_def
            by (smt (verit, ccfv_SIG) ConcreteSemantics.get_store_Ag_simplifies TypedEqui.typed_assertionE TypedEqui.typed_core asm1(6) full_add_charact(1) full_core_def max_projection_prop_pure_core mem_Collect_eq mpp_prop)
          then have "p \<in> P \<otimes> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.pure_typed tcfe (semantify_bexp b)) \<otimes> UNIV"
            using TypedEqui.typed_state_axioms \<open>Some \<omega> = p \<oplus> r\<close> \<open>\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp b\<close> asm1(6) greater_def in_times_atrue typed_assertion_star_atrue typed_state.typed_assertionE by blast
        qed
      qed

      show "tcfe \<turnstile>CSL [(P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)] C2 [Q \<otimes> UNIV]"
      proof (rule RuleCons)
        show "tcfe \<turnstile>CSL [(P \<otimes> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b))) \<otimes> UNIV] C2 [B2 \<otimes> UNIV]"
          by (metis asm0(1) asm1(4) assms(2) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B2 \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b) \<subseteq> P \<otimes> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b)) \<otimes> UNIV"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot (Bnot b) (get_store \<omega>)"
            using in_set_sum[of \<omega> P "UNIV"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "\<not> bdenot b (get_store |p| )"
            by (simp add: core_charact(1) full_add_charact(1))
          then have "|p| \<in> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b))"
            unfolding ConcreteSemantics.pure_typed_def semantify_bexp_def negate_def
            by (smt (verit, del_insts) CollectD CollectI TypedEqui.typed_assertionE TypedEqui.typed_core \<open>p \<in> P\<close> asm1(2) asm1(6) core_charact(1) core_in_emp_core emp_core_def framed_by_exp_def option.collapse semantify_bexp_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b))"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.pure_typed tcfe (negate (semantify_bexp b))) \<otimes> UNIV"
            by (meson TypedEqui.typed_intersection TypedEqui.typed_state_axioms \<open>Some \<omega> = p \<oplus> r\<close> \<open>\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)\<close> asm1(6) atrue_self_framing_and_typed(1) greater_def in_times_atrue typed_state.typed_assertionE typed_state.typed_star)
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
  assumes "\<And>P Q. invariant_translate \<Gamma> P C Q"
      and "ConcreteSemantics.wf_abs_stmt tcfe (ConcreteSemantics.havoc_list (wrL C))"
      and "wf_stmt \<Gamma> F (Cwhile b I C)"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P (Cwhile b I C) Q"
proof (rule invariant_translateI)
  let ?I = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I"
  assume asm0: "proof_obligations_valid (snd (translate \<Gamma> (Cwhile b I C)))"
    "ConcreteSemantics.SL_proof tcfe P (fst (translate \<Gamma> (Cwhile b I C))) Q"
  then have r1: "proof_obligations_valid (snd (translate \<Gamma> C))"
    using proof_obligations_valid_union by fastforce
  moreover obtain B where B_def: "ConcreteSemantics.SL_proof tcfe (UNIV) (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Gamma> C);; Exhale ?I) B"
    by (metis (no_types, lifting) asm0(1) insertCI proof_obligations_valid_def proof_obligations_valid_union snd_eqD translate.simps(10))
  moreover obtain R0 R1 where R_defs: "entails P (R0 \<otimes> ?I)" "Q = R1 \<otimes> (?I \<inter> assertify_bexp (Bnot b))"
    "ConcreteSemantics.SL_proof tcfe R0 (ConcreteSemantics.havoc_list (wrL C)) R1"
    using asm0(2) by auto
  moreover have "entails R0 R1 \<and> fvA tcfe R1 \<subseteq> fvA tcfe R0 - (set (wrL C))"
    using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) assms(4) by blast

  (* R1 is the frame *)

  show "tcfe \<turnstile>CSL [P \<otimes> UNIV] Cwhile b I C [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "tcfe \<turnstile>CSL [(?I \<otimes> UNIV) \<otimes> R1] Cwhile b I C [((?I \<otimes> UNIV) \<inter> (assertify_bexp (Bnot b))) \<otimes> R1]"
    proof (rule RuleFrame)
      show "tcfe \<turnstile>CSL [?I \<otimes> UNIV] Cwhile b I C [(?I \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)]"
      proof (rule RuleWhile)
        show "tcfe \<turnstile>CSL [(?I \<otimes> UNIV) \<inter> assertify_bexp b] C [?I \<otimes> UNIV]"
        proof (rule RuleCons)
          show "tcfe \<turnstile>CSL [UNIV \<otimes> ?I \<inter> assertify_bexp b \<otimes> UNIV] C [B \<otimes> ?I \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF _ B_def]
            using assms(1) r1 by blast
          show "B \<otimes> ?I \<otimes> UNIV \<subseteq> ?I \<otimes> UNIV"
            using B_def drop_conjunct_entails by blast
          show "(?I \<otimes> UNIV) \<inter> assertify_bexp b \<subseteq> UNIV \<otimes> (?I \<inter> assertify_bexp b) \<otimes> UNIV"
            by (metis (no_types, lifting) add_set_asso add_set_commm atrue_twice_equal intersect_and_star)
        qed
      qed
      show "disjoint (fvA tcfe R1) (wrC (Cwhile b I C))"
        using \<open>entails R0 R1 \<and> fvA tcfe R1 \<subseteq> fvA tcfe R0 - set (wrL C)\<close> disjoint_def wrL_wrC_same by fastforce
      show "self_framing (?I \<otimes> UNIV)"
        using assms(3) self_framing_typed_star_atrue by auto
      show "self_framing R1"
        using ConcreteSemantics.proofs_are_self_framing_and_typed assms(2) calculation(5) by blast
      show "TypedEqui.typed_assertion tcfe (?I \<otimes> UNIV)"
        using assms(3) typed_assertion_star_atrue by auto
      show "TypedEqui.typed_assertion tcfe R1"
        using ConcreteSemantics.proofs_are_self_framing_and_typed assms(2) calculation(5) by blast
    qed
    have "P \<subseteq> R1 \<otimes> ?I"
      by (meson \<open>entails R0 R1 \<and> fvA tcfe R1 \<subseteq> fvA tcfe R0 - set (wrL C)\<close> add_set_mono calculation(3) entails_def equalityD1 subset_trans)
    then show "P \<otimes> UNIV \<subseteq> ?I \<otimes> UNIV \<otimes> R1"
      by (smt (verit, best) add_set_asso add_set_commm add_set_mono atrue_twice_equal atrue_twice_same)
    show "(?I \<otimes> UNIV) \<inter> assertify_bexp (Bnot b) \<otimes> R1 \<subseteq> Q \<otimes> UNIV"
      by (smt (verit, del_insts) add_set_asso add_set_commm add_set_mono calculation(4) intersect_and_star subsetI)
  qed
qed


lemma invariant_translate_induct:
  assumes "wf_stmt \<Gamma> F C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_context tcfe"
    shows "invariant_translate \<Gamma> P C Q"
  using assms
proof (induct C arbitrary: P Q)
  case (Cseq C1 C2)
  then show ?case
    by (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff fst_eqD invariant_translate_seq snd_conv translate.simps(7) well_typed_cmd_aux.simps(2) wf_stmt.simps(1))
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  let ?P1 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P1"
  let ?P2 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic P2"
  let ?Q1 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q1"
  let ?Q2 = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic Q2"
  show ?case
  proof (rule invariant_translate_parallel)
    show "ConcreteSemantics.wf_abs_stmt tcfe (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      using Cpar.prems(3) by fastforce
    show "wf_stmt \<Gamma> F {P1} C1 {Q1} || {P2} C2 {Q2}"
      using Cpar.prems(1) by blast
    fix P Q
    show "invariant_translate \<Gamma> P C1 Q"
    proof (rule Cpar(1))
      have "ConcreteSemantics.wf_abs_stmt tcfe (Inhale ?P1;; fst (translate \<Gamma> C1);; Exhale ?Q1)"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C1))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tcfe C1"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Gamma> F C1"
        using Cpar.prems(1) by auto
    qed (simp add: Cpar)
    show "invariant_translate \<Gamma> P C2 Q"
    proof (rule Cpar(2))
      have "ConcreteSemantics.wf_abs_stmt tcfe (Inhale ?P2;; fst (translate \<Gamma> C2);; Exhale ?Q2)"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C2))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tcfe C2"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Gamma> F C2"
        using Cpar.prems(1) by auto
    qed (simp add: Cpar)
  qed (simp add: Cpar)
next
  case (Cif b C1 C2)
  show ?case
  proof (rule invariant_translate_if)
    fix P Q
    show "invariant_translate \<Gamma> P C1 Q"
    proof (rule Cif(1))
      show "wf_stmt \<Gamma> F C1"
        using Cif.prems(1) by auto
      show "well_typed_cmd tcfe C1"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C1))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed (simp add: Cif)
    show "invariant_translate \<Gamma> P C2 Q"
    proof (rule Cif(2))
      show "wf_stmt \<Gamma> F C2"
        using Cif.prems(1) by auto
      show "well_typed_cmd tcfe C2"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C2))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed (simp add: Cif)
  qed
next
  case (Cwhile b I C)
  let ?I = "make_semantic_assertion \<Gamma> type_ctxt_front_end_syntactic I"
  show ?case
  proof (rule invariant_translate_while)
    show "ConcreteSemantics.wf_abs_stmt tcfe (ConcreteSemantics.havoc_list (wrL C))"
      using Cwhile.prems(3) by force
    show "wf_stmt \<Gamma> F (Cwhile b I C)"
      using Cwhile.prems(1) by auto
    fix P Q show "invariant_translate \<Gamma> P C Q"
    proof (rule Cwhile(1)[of P Q])
      show "wf_stmt \<Gamma> F C"
        using Cwhile.prems(1) by auto
      show "well_typed_cmd tcfe C"
        using Cwhile.prems(2) by auto
      have "ConcreteSemantics.wf_abs_stmt tcfe (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Gamma> C);; Exhale ?I)"
        using Cwhile.prems(4) by fastforce
      then show "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C))" by force
      show "\<And>Cv. Cv \<in> snd (translate \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
        using Cwhile.prems(4) by auto
    qed (simp add: Cwhile)
  qed (simp add: Cwhile)
qed (simp_all add: invariant_translate_skip invariant_translate_free invariant_translate_alloc invariant_translate_seq
      invariant_translate_write invariant_translate_read invariant_translate_assign)


theorem sound_translation:
  assumes "wf_stmt \<Gamma> F C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Gamma> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_assertion tcfe P \<and> TypedEqui.wf_assertion tcfe Q"
      and "ConcreteSemantics.verifies_set tcfe (UNIV) (Inhale P;; fst (translate \<Gamma> C);; Exhale Q)"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> C) \<Longrightarrow> ConcreteSemantics.verifies_set tcfe (UNIV) Cv"

    shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
proof -
  obtain B where "ConcreteSemantics.SL_proof tcfe (UNIV) (Inhale P;; fst (translate \<Gamma> C);; Exhale Q) B"
    by (metis ConcreteSemantics.Viper_implies_SL_proof ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(3) ConcreteSemantics.wf_abs_stmt.simps(7) assms(3) assms(5) assms(6) atrue_self_framing_and_typed(1) atrue_self_framing_and_typed(2))
  then obtain B' where "ConcreteSemantics.SL_proof tcfe (UNIV \<otimes> P) (fst (translate \<Gamma> C)) B'" "entails B' (B \<otimes> Q)"
    by blast


  show "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "tcfe \<turnstile>CSL [P \<otimes> UNIV \<otimes> UNIV] C [B' \<otimes> UNIV]"
    proof (rule invariant_translateE[of _ "P \<otimes> UNIV" C])
      show "ConcreteSemantics.SL_proof tcfe (P \<otimes> UNIV) (fst (translate \<Gamma> C)) B'"
        by (metis \<open>ConcreteSemantics.SL_proof tcfe (UNIV \<otimes> P) (fst (translate \<Gamma> C)) B'\<close> add_set_commm)
      show "invariant_translate \<Gamma> (P \<otimes> UNIV) C B'"
        by (meson assms(1) assms(2) assms(3) assms(4) invariant_translate_induct wf_context_type_context)
      show "proof_obligations_valid (snd (translate \<Gamma> C))"
        unfolding proof_obligations_valid_def
      proof clarify
        fix Cv assume "Cv \<in> snd (translate \<Gamma> C)"
        then show "\<exists>B. ConcreteSemantics.SL_proof tcfe (UNIV) Cv B"
          by (simp add: ConcreteSemantics.Viper_implies_SL_proof assms(4) assms(7))
      qed
    qed
    show "P \<otimes> UNIV \<subseteq> P \<otimes> UNIV \<otimes> UNIV"
      by (simp add: add_set_asso atrue_twice_equal)
    show "B' \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
      by (smt (verit, ccfv_SIG) ConcreteSemantics.proofs_are_self_framing_and_typed ConcreteSemantics.semantics_axioms \<open>ConcreteSemantics.SL_proof tcfe (UNIV) (abs_stmt.Inhale P ;; fst (translate \<Gamma> C) ;; abs_stmt.Exhale Q) B\<close> \<open>entails B' (B \<otimes> Q)\<close> add_set_mono assms(3) assms(5) atrue_twice_equal drop_conjunct_entails entails_def order.trans semantics.wf_abs_stmt.simps(2) semantics.wf_abs_stmt.simps(3) semantics.wf_abs_stmt.simps(7))
  qed
qed


end