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
  using RuleConsTyped assms subset_entails 
  by blast

lemma convert_proof_assign:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) A (abs_stmt.LocalAssign x (semantify_exp e)) B"
  shows "(tcfe tys) \<turnstile>CSL [A] Cassign x e [B]"
proof -
  have "B = ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A"
    using ConcreteSemantics.SL_proof_LocalAssign_elim assms
    by fast
  moreover have "(tcfe tys) \<turnstile>CSL [A] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
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
    show "(tcfe tys) \<turnstile>CSL [sub_pre x e (ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A)] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
      by (simp add: RuleAssign)
  qed (simp)
  ultimately show ?thesis by auto
qed

lemma convert_proof_skip:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) A Skip B"
  shows "(tcfe tys) \<turnstile>CSL [A] Cskip [B]"
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
definition make_semantic_assertion_untyped :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" where
  "make_semantic_assertion_untyped (tcfe tys) F A = well_typedly (tcfe tys) F (\<langle>type_ctxt_front_end, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
*)


abbreviation tcfe :: "vtyp list \<Rightarrow> (int val, char list \<Rightarrow> int val set option) abs_type_context" where
  "tcfe \<equiv> type_ctxt_front_end"

abbreviation inhalify where
  "inhalify tys P \<equiv> Set.filter (typed (tcfe tys) \<circ> stabilize) P"

lemma self_framing_then_self_framing_inhalify:
  assumes "self_framing P"
  shows "self_framing (inhalify tys P)"
proof (rule self_framingI)
  fix \<omega> show "(\<omega> \<in> inhalify tys P) = (stabilize \<omega> \<in> inhalify tys P)"
    using assms self_framingE self_framing_invE test_self_framing by blast
qed


(* Parameters
- tys: A list of vtyps for the variables of the program
- F???
 *)

text \<open>The following checks:
1) Whether all provided annotations (loop invariants, pre- and postconditions for parallel compositions)
are self-framing.
2) The pre- and postconditions for parallel compositions do not refer to variables modified by the other thread.
3) r cannot appear in e in \<^term>\<open>Calloc r e\<close>. \<close>

fun wf_stmt where
  "wf_stmt tys \<Gamma> (Cseq C1 C2) \<longleftrightarrow> wf_stmt tys \<Gamma> C1 \<and> wf_stmt tys \<Gamma> C2"
| "wf_stmt tys \<Gamma> (Calloc r e) \<longleftrightarrow> r \<notin> fvE e"

| "wf_stmt tys \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2}) \<longleftrightarrow>
  disjoint
  (fvC C1 \<union> fvA (tcfe tys) (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1) \<otimes> UNIV)) (wrC C2)
  \<and> disjoint (fvC C2 \<union> fvA (tcfe tys) (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2) \<otimes> UNIV)) (wrC C1) \<and>
  self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1) \<and>
  self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2) \<and>
  self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1) \<and>
  self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2) \<and>
  wf_stmt tys \<Gamma> C1 \<and> wf_stmt tys \<Gamma> C2"

| "wf_stmt tys \<Gamma> (Cif b C1 C2) \<longleftrightarrow> wf_stmt tys \<Gamma> C1 \<and> wf_stmt tys \<Gamma> C2"

| "wf_stmt tys \<Gamma> (Cwhile b I C) \<longleftrightarrow> self_framing (make_semantic_assertion_untyped \<Gamma> (tcfes tys) I)
                              \<and> wf_stmt tys \<Gamma> C"

| "wf_stmt tys \<Gamma> _ \<longleftrightarrow> True"


definition atrue where
  "atrue tys = inhalify tys UNIV"

lemma atrue_self_framing_and_typed[simp]:
  "self_framing UNIV"
  by (simp add: self_framing_def)

(*
lemma wf_context_type_context[simp]:
  "TypedEqui.wf_context (tcfe tys)"
  unfolding TypedEqui.wf_context_def
proof -
  have "dom (variables (tcfe tys)) \<subseteq> {x. x < undefined}"
    by (metis CollectI abs_type_context.select_convs(1) domIff subsetI type_ctxt_front_end_def type_ctxt_store_def)
  then show "finite (dom (variables (tcfe tys)))"
    by (simp add: finite_subset)
qed
*)

(*
Set.filter (typed \<Delta> \<circ> stabilize) P
*)

lemma tcfe_is_finite:
  "TypedEqui.finite_context (tcfe tys)"
  unfolding TypedEqui.finite_context_def type_ctxt_front_end_def type_ctxt_store_def
  by (metis (mono_tags, lifting) abs_type_context.select_convs(1) domIff finite_nat_set_iff_bounded)



abbreviation stab_inhalify where
  "stab_inhalify tys P \<equiv> inhalify tys (Stabilize P)"

abbreviation t_entails where
  "t_entails tys \<equiv> ConcreteSemantics.entails_typed (tcfe tys)"

lemma conjunct_with_true_t_entails:
  "t_entails tys P (UNIV \<otimes> P)"
  by (simp add: conjunct_with_true_entails subset_entails)

lemma conjunct_with_stabilize_emp_t_entails:
  "t_entails tys P (Stabilize emp \<otimes> P)"
  unfolding ConcreteSemantics.entails_typed_def
  by (metis (no_types, opaque_lifting) Stable_def Stable_emp add_set_commm add_set_mono emp_star_right_id subset_iff)


lemma convert_proof_alloc:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))) Q"
      and "well_typed_cmd tys (Calloc r e)"
      and "wf_stmt tys \<Gamma> (Calloc r e)"
  shows "(tcfe tys) \<turnstile>CSL [P] Calloc r e [Q]"
proof (rule RuleConsTyped)

  have asm0: "ConcreteSemantics.SL_proof (tcfe tys) P (Havoc r) (TypedEqui.exists_assert (tcfe tys) r P)
  \<and> ConcreteSemantics.SL_proof (tcfe tys) (TypedEqui.exists_assert (tcfe tys) r P) (Inhale (Stabilize (full_ownership_with_val r e))) Q
  \<and> self_framing P"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim assms(1))
  then have "Q = TypedEqui.exists_assert (tcfe tys) r P \<otimes> inhalify tys (Stabilize (full_ownership_with_val r e))"
    by blast

  show "(tcfe tys) \<turnstile>CSL [Stabilize emp \<otimes> TypedEqui.exists_assert (tcfe tys) r P] Calloc r e [inhalify tys (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert (tcfe tys) r P]"
  proof (rule RuleFrame)
    have "r \<notin> fvE e"
      using assms(3) by auto
    then have "(tcfe tys) \<turnstile>CSL [emp] Calloc r e [full_ownership_with_val r e]"
      using RuleAlloc[of r e] by simp
    then show "(tcfe tys) \<turnstile>CSL [Stabilize emp] Calloc r e [inhalify tys (Stabilize (full_ownership_with_val r e))]"
      using RuleStabilizeTyped by (metis RuleInhalify)

    show "disjoint (fvA (tcfe tys) (TypedEqui.exists_assert (tcfe tys) r P)) (wrC (Calloc r e))"
      using ConcreteSemantics.exists_assert_no_in_fv disjoint_def
      using tcfe_is_finite by fastforce

    show "self_framing (TypedEqui.exists_assert (tcfe tys) r P)"
      using asm0 by fastforce
  qed (simp)
  then have "variables (tcfe tys) r \<noteq> None"
    using assms(2)
    unfolding type_ctxt_front_end_def type_ctxt_store_def by simp
  then have "t_entails tys P (TypedEqui.exists_assert (tcfe tys) r P)"
    using ConcreteSemantics.SL_proof_Havoc_elim_entails[of "tcfe tys" P r "TypedEqui.exists_assert (FrontEndTranslation.tcfe tys) r P"]
    using asm0 tcfe_is_finite by presburger

  then show "t_entails tys P (Stabilize emp \<otimes> TypedEqui.exists_assert (tcfe tys) r P)"
    using ConcreteSemantics.entails_typed_trans conjunct_with_stabilize_emp_t_entails by blast

  show "t_entails tys (inhalify tys (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert (tcfe tys) r P) Q"
    by (simp add: ConcreteSemantics.entails_typed_refl \<open>Q = TypedEqui.exists_assert (tcfe tys) r P \<otimes> inhalify tys (Stabilize (full_ownership_with_val r e))\<close> add_set_commm)
qed

lemma helper_exhale_encoding:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (Exhale (Stabilize A)) Q"
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
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (Exhale (Stabilize (full_ownership r))) Q"
  shows "(tcfe tys) \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize (full_ownership r))" "self_framing P" "self_framing Q"
  show "(tcfe tys) \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "(tcfe tys) \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> Q] Cfree r [Stabilize (UNIV) \<otimes> Q]"
    proof (rule RuleFrame)
      show "(tcfe tys) \<turnstile>CSL [Stabilize (full_ownership r)] Cfree r [Stabilize (UNIV)]"
        using RuleFree RuleStabilizeTyped by blast
    qed (simp_all add: asm0)
    show "P \<subseteq> Stabilize (full_ownership r) \<otimes> Q"
      using assms helper_exhale_encoding by auto
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
  assumes "TypedEqui.typed (tcfe tys) \<omega>'"
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
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e))) Q"
  shows "(tcfe tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Custom_elim)
  assume asm0: "SL_Custom (tcfe tys) P (custom.FieldAssign (semantify_addr r) field_val (semantify_exp e)) Q"
  "self_framing P" "self_framing Q"
  show "(tcfe tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    using asm0(1)
  proof (rule SL_custom_FieldAssign)
    assume asm1: "Q = update_value (tcfe tys) P (semantify_addr r) field_val (semantify_exp e)"
      "self_framing P" "entails P {\<omega>. \<exists>l. get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l}"
      "framed_by_exp P (semantify_addr r)" "framed_by_exp P (semantify_exp e)"
    show "(tcfe tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    proof (rule RuleConsTyped)


      let ?F = "Stabilize { remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
      show "(tcfe tys) \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> ?F] Cwrite r e [Stabilize (full_ownership_with_val r e) \<otimes> ?F]"
      proof (rule RuleFrame)
        show "(tcfe tys) \<turnstile>CSL [Stabilize (full_ownership r)] Cwrite r e [Stabilize (full_ownership_with_val r e)]"
          by (simp add: RuleStabilizeTyped RuleWrite)
      qed (simp_all)
      
      show "ConcreteSemantics.entails_typed (tcfe tys) P (Stabilize (full_ownership r) \<otimes> ?F)"
      proof (rule ConcreteSemantics.entails_typedI)
        fix \<omega> assume "\<omega> \<in> P" "typed (tcfe tys) \<omega>"
        then obtain l where "get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l"          
          by (smt (verit) CollectD asm1(3) entails_def subsetD)
        then have "Some \<omega> = remove_only \<omega> (l, field_val) \<oplus> set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))"
          using split_remove_only_owns_only by blast
        moreover obtain v' where "get_h \<omega> (l, field_val) = Some v'"
          by (metis EquiSemAuxLemma.gr_0_is_ppos \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> not_gr_0 vstate_wf_Some zero_neq_one)
        then obtain v where "v' = VInt v"
          by (smt (verit, best) \<open>typed (tcfe tys) \<omega>\<close> abs_type_context.select_convs(2) mem_Collect_eq snd_conv type_ctxt_front_end_def type_ctxt_heap_def typed_get_vh vints_def)

        
        moreover have "set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))) \<in> Stabilize (full_ownership r)"
        proof (rule in_StabilizeI)
          show "stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))) \<in> full_ownership r"
            apply (rule in_full_ownership[of _ _ l])
            using \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> semantify_addr_equiv apply auto[1]
          proof (rule virtual_state_ext)
            show "get_m (stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))))) =
    get_vm (acc_virt (l, field_val) (Abs_preal 1) (VInt v))"
              apply (rule ext)
              apply (case_tac "x = (l, field_val)")
              apply (metis (no_types, lifting) \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> acc_virt_get_vm add_0 calculation(1) fun_upd_same get_m_additive get_m_stabilize inf.idem one_preal.abs_eq pperm_pnone_pgt remove_only_charact(1) vstate_wf_imp)
              apply simp
              by (smt (verit, best) PosReal.padd_cancellative add_0 calculation(1) commutative fun_upd_apply get_m_additive get_state_set_state remove_only_charact(2))
            show "get_h (stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))))) =
    get_vh (acc_virt (l, field_val) (Abs_preal 1) (VInt v))"
              apply (rule ext)
              apply (case_tac "x = (l, field_val)")
               apply simp_all
              apply (smt (z3) EquiSemAuxLemma.gr_0_is_ppos \<open>get_h \<omega> (l, field_val) = Some v'\<close> \<open>get_m (stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))))) = get_vm (acc_virt (l, field_val) (Abs_preal 1) (VInt v))\<close> acc_virt_get_vm calculation(1) calculation(2) get_state_set_state get_state_stabilize get_vh_Some_greater greater_equiv inf.idem one_preal.abs_eq option.exhaust pperm_pnone_pgt stabilize_value_persists vstate_wf_ppos zero_neq_one)
              by (metis (no_types, lifting) EquiSemAuxLemma.gr_0_is_ppos \<open>get_m (stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))))) = get_vm (acc_virt (l, field_val) (Abs_preal 1) (VInt v))\<close> acc_virt_get_vm get_m_stabilize get_state_set_state pperm_pgt_pnone stabilize_is_stable stable_virtual_state_def vstate_stabilize_structure(1))
          qed
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
      have "Stabilize (full_ownership_with_val r e) \<otimes> ?F \<subseteq> Q \<otimes> UNIV"
      proof
        fix \<omega>' assume "\<omega>' \<in> Stabilize (full_ownership_with_val r e) \<otimes> ?F"
        then obtain ptr f where r: "Some \<omega>' = ptr \<oplus> f" "ptr \<in> Stabilize (full_ownership_with_val r e)" "f \<in> ?F"
          by (meson x_elem_set_product)
        then obtain l where "get_state (stabilize ptr) = acc_virt (l, field_val) (Abs_preal 1) (VInt (edenot e (get_store ptr)))"
          "get_store ptr r = Some (VRef (Address l))"
          unfolding full_ownership_with_val_def
          by auto

        then have "get_store (stabilize ptr) r = Some (VRef (Address l)) \<and> get_m (stabilize ptr) (l, field_val) = 1
  \<and> get_h (stabilize ptr) (l, field_val) = Some (VInt (edenot e (get_store (stabilize ptr))))"
          by (simp add: one_preal.abs_eq)
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

        moreover have "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) \<in> update_value (tcfe tys) P (semantify_addr r) field_val (semantify_exp e)"
          using \<open>\<omega> \<in> P\<close> \<open>semantify_addr r \<omega> = Some l'\<close> semantify_exp_def
        proof (rule in_update_value)
          show "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) = update_heap_val \<omega> (l', field_val) (VInt (edenot e (get_store \<omega>)))"
            by (metis calculation(2) calculation(3) get_store_set_state greater_charact)
          show "typed_value (tcfe tys) field_val (VInt (edenot e (get_store \<omega>)))"
          proof (rule typed_valueI)
            fix ty assume "custom_context (tcfe tys) field_val = Some ty"
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
      then show "ConcreteSemantics.entails_typed (tcfe tys) (Stabilize (full_ownership_with_val r e) \<otimes> Stabilize {remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l})
     (Q \<otimes> UNIV)"
        using ConcreteSemantics.entails_typed_def by blast
    qed
  qed
qed


definition semantify_heap_loc :: "var \<Rightarrow> (int equi_state, int val) AbstractSemantics.exp" where
  "semantify_heap_loc r \<omega> =
  (if (\<exists>l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_h \<omega> (l, field_val) = Some (VInt v))
  then Some (the (get_h \<omega> (SOME l. get_store \<omega> r = Some (VRef (Address l)), field_val)))
  else None)"

lemma convert_proof_read:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (LocalAssign x (semantify_heap_loc r)) Q"
  shows "(tcfe tys) \<turnstile>CSL [P] Cread x r [Q]"
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

  show "(tcfe tys) \<turnstile>CSL [P] Cread x r [Q]"
  proof (rule RuleCons)
    show "(tcfe tys) \<turnstile>CSL [P] Cread x r [read_result P x r]"
    proof (rule RuleRead)
      show "P \<subseteq> read_perm r" (* Should come from framed_by_exp *)
        using r
        unfolding read_perm_def 
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
        by (smt (verit) ConcreteSemantics.post_substitute_var_assert_def ConcreteSemantics.substitute_var_state_def asm0(1) asm0(2) framed_by_exp_def image_iff option.sel semantify_addr_def semantify_addr_equiv semantify_heap_loc_def)
    qed
  qed (simp)
qed

(*
abbreviation make_semantic_wf where
  "make_semantic_wf \<Gamma> P \<equiv> Stabilize (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P)"
*)

fun translate (* :: "cmd \<Rightarrow> (v_stmt \<times> v_stmt set)" *) where
  "translate tys \<Gamma> Cskip = (Skip, {})"
| "translate tys \<Gamma> (Cassign x e) = (LocalAssign x (semantify_exp e), {})"

| "translate tys \<Gamma> (Calloc r e) = ((Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))), {})"
| "translate tys \<Gamma> (Cfree r) = (Exhale (Stabilize (full_ownership r)), {})"
| "translate tys \<Gamma> (Cwrite r e) = (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e)), {})"
| "translate tys \<Gamma> (Cread x r) = (LocalAssign x (semantify_heap_loc r), {})"

| "translate tys \<Gamma> (Cseq C1 C2) = (let r1 = translate tys \<Gamma> C1 in let r2 = translate tys \<Gamma> C2 in
  (fst r1;; fst r2, snd r1 \<union> snd r2))"

| "translate tys \<Gamma> (Cif b C1 C2) = (If (semantify_bexp b) (fst (translate tys \<Gamma> C1)) (fst (translate tys \<Gamma> C2)), snd (translate tys \<Gamma> C1) \<union> snd (translate tys \<Gamma> C2))"

| "translate tys \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1 \<otimes> make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2));;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1 \<otimes> make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2)),
  let r1 = translate tys \<Gamma> C1 in let r2 = translate tys \<Gamma> C2 in
  { (Inhale (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1);; fst r1;; Exhale (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1))),
  (Inhale (make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2);; fst r2;; Exhale (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2))) } \<union> snd r1 \<union> snd r2)"

| "translate tys \<Gamma> (Cwhile b I C) = (Exhale (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) I));;
  ConcreteSemantics.havoc_list (wrL C);; Inhale ((make_semantic_assertion_untyped \<Gamma> (tcfes tys) I) \<inter> assertify_bexp (Bnot b)),
  { Inhale ((make_semantic_assertion_untyped \<Gamma> (tcfes tys) I) \<inter> assertify_bexp b);; fst (translate tys \<Gamma> C);; Exhale (inhalify tys (make_semantic_assertion_untyped \<Gamma> (tcfes tys) I)) } \<union> snd (translate tys \<Gamma> C))"

(*
lemma CSL_weaken_post_atrue:
  assumes "(tcfe tys) \<turnstile>CSL [P] C [Q]"
  shows "(tcfe tys) \<turnstile>CSL [P] C [Q \<otimes> UNIV]"
  using assms(1)
proof (rule RuleCons)
  show "Q \<subseteq> Q \<otimes> UNIV"
    using add_set_commm assms(2) conjunct_with_true_entails by blast
qed (simp)
*)

lemma CSL_add_atrue:
  assumes "(tcfe tys) \<turnstile>CSL [P] C [Q]"
      and "self_framing P"
    shows "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  by (rule RuleFrame) (simp_all add: assms)


definition proof_obligations_valid where
  "proof_obligations_valid tys S \<longleftrightarrow> (\<forall>Cv \<in> S. \<exists>B. ConcreteSemantics.SL_proof (tcfe tys) (atrue tys) Cv B)"

lemma proof_obligations_valid_union:
  "proof_obligations_valid tys (S1 \<union> S2) \<longleftrightarrow> proof_obligations_valid tys S1 \<and> proof_obligations_valid tys S2"
  by (meson Un_iff proof_obligations_valid_def)

definition invariant_translate where
  "invariant_translate tys \<Gamma> P C Q \<longleftrightarrow>
  ((proof_obligations_valid tys (snd (translate tys \<Gamma> C)) \<and> ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q) \<longrightarrow> (tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV])"

lemma invariant_translateE:
  assumes "invariant_translate tys \<Gamma> P C Q"
      and "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
      and "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q"
    shows "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  using assms(1) assms(2) assms(3) invariant_translate_def by blast


lemma invariant_translateI:
  assumes "proof_obligations_valid tys (snd (translate tys \<Gamma> C)) \<Longrightarrow> ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q
    \<Longrightarrow> (tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  shows "invariant_translate tys \<Gamma> P C Q"
  using assms invariant_translate_def proof_obligations_valid_def by blast

lemma invariant_translate_simpler:
  assumes "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q \<Longrightarrow> (tcfe tys) \<turnstile>CSL [P] C [Q]"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))"
      and "self_framing P"
    shows "invariant_translate tys \<Gamma> P C Q"
proof (rule invariant_translateI)
  assume "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
     and "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C)) Q"
  then have "(tcfe tys) \<turnstile>CSL [P] C [Q]"
    using assms(1) by blast
  then show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
    by (simp add: CSL_add_atrue assms invariant_translateI)
qed

corollary invariant_translate_skip:
  "invariant_translate tys \<Gamma> P Cskip Q"
  using RuleSkip invariant_translate_def by auto

corollary invariant_translate_assign:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> (Cassign x e)))"
  shows "invariant_translate tys \<Gamma> P (Cassign x e) Q"
  using convert_proof_assign assms
  by (metis ConcreteSemantics.SL_proof_LocalAssign_elim invariant_translateI invariant_translate_simpler prod.collapse prod.inject translate.simps(2))


corollary invariant_translate_alloc:
  assumes "well_typed_cmd tys (Calloc r e)"
      and "wf_stmt tys \<Gamma> (Calloc r e)"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> (Calloc r e)))"
    shows "invariant_translate tys \<Gamma> P (Calloc r e) Q"
  using assms cmd.distinct(37) convert_proof_alloc
  by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim fst_eqD invariant_translateI invariant_translate_simpler translate.simps(3))


lemma atrue_twice_same:
  "UNIV \<otimes> UNIV \<subseteq> UNIV"
  unfolding add_set_def
  by auto

lemma atrue_twice_equal:
  "UNIV \<otimes> UNIV = (UNIV :: ('e :: pcm_with_core) set)"
proof
  show "(UNIV :: ('e :: pcm_with_core) set) \<subseteq> UNIV \<otimes> UNIV"
  proof
    fix x :: "('e :: pcm_with_core)" assume "x \<in> UNIV"
    then have "Some x = x \<oplus> |x|"
      using core_is_smaller by blast
    then have "|x| \<in> UNIV"
      using TypedEqui.typed_core \<open>x \<in> UNIV\<close> by blast
    then show "x \<in> UNIV \<otimes> UNIV"
      using \<open>Some x = x \<oplus> |x|\<close> \<open>x \<in> UNIV\<close> x_elem_set_product by blast
  qed
qed (simp add: atrue_twice_same)


corollary invariant_translate_free:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> (Cfree r)))"
    shows "invariant_translate tys \<Gamma> P (Cfree r) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> (Cfree r))) Q"
  then have "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cfree r [(Q \<otimes> UNIV) \<otimes> UNIV]"
    using RuleFrame[OF convert_proof_free]
    by (metis ConcreteSemantics.SL_proof_Exhale_elim atrue_self_framing_and_typed disjoint_simps(2) fst_eqD translate.simps(4) wrC.simps(6))
  then show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cfree r [Q \<otimes> UNIV]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_write:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> (Cwrite r e)))"
    shows "invariant_translate tys \<Gamma> P (Cwrite r e) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> (Cwrite r e))) Q"
  then have "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cwrite r e [(Q \<otimes> UNIV) \<otimes> UNIV]"
    using RuleFrame[OF convert_proof_write]
    by (metis ConcreteSemantics.SL_proof_Custom_elim atrue_self_framing_and_typed disjoint_simps(2) fst_eqD translate.simps(5) wrC.simps(4))
  then show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cwrite r e [Q \<otimes> UNIV]"
    by (simp add: add_set_asso atrue_twice_equal)
qed

corollary invariant_translate_read:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> (Cread x r)))"
    shows "invariant_translate tys \<Gamma> P (Cread x r) Q"
  using convert_proof_read assms
  by (metis ConcreteSemantics.SL_proof_LocalAssign_elim fst_eqD invariant_translateI invariant_translate_simpler translate.simps(6))


lemma invariant_translate_seq:
  assumes "\<And>R. invariant_translate tys \<Gamma> P C1 R"
      and "\<And>R. invariant_translate tys \<Gamma> R C2 Q"
    shows "invariant_translate tys \<Gamma> P (Cseq C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid tys (snd (translate tys \<Gamma> (Cseq C1 C2)))"
    "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> (Cseq C1 C2))) Q"
  then obtain R where r: "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> C1)) R"
      "ConcreteSemantics.SL_proof (tcfe tys) R (fst (translate tys \<Gamma> C2)) Q"
    by (metis ConcreteSemantics.SL_proof_Seq_elim fst_eqD translate.simps(7))
  show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cseq C1 C2 [Q \<otimes> UNIV]"
  proof (rule RuleSeq)
    show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C1 [R \<otimes> UNIV]"
      using assms(1)[of R] r
      unfolding invariant_translate_def
      by (metis asm0(1) proof_obligations_valid_union snd_conv translate.simps(7))
    show "(tcfe tys) \<turnstile>CSL [R \<otimes> UNIV] C2 [Q \<otimes> UNIV]"
    proof (rule RuleCons)
      show "(tcfe tys) \<turnstile>CSL [R \<otimes> UNIV] C2 [(Q \<otimes> UNIV) \<otimes> UNIV]"
          using assms(2)[of R] asm0
          unfolding invariant_translate_def proof_obligations_valid_def
          by (metis (no_types, lifting) Un_iff add_set_asso atrue_twice_equal r(2) snd_conv translate.simps(7))
      show "Q \<otimes> UNIV \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
        by (simp add: add_set_asso add_set_mono atrue_twice_same)
    qed (simp)
  qed
qed

(* Is this lemma 3? *)
lemma invariant_translate_inhale_exhale_get_proof:
  assumes "\<And>P Q. invariant_translate tys \<Gamma> P C Q"
      and "ConcreteSemantics.SL_proof (tcfe tys) P (Inhale A;; fst (translate tys \<Gamma> C);; Exhale B) Q"
      and "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
    shows "(tcfe tys) \<turnstile>CSL [P \<otimes> inhalify tys A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
  using assms(2)
proof (rule ConcreteSemantics.SL_proof_Seq_elim)
  fix R1 assume asm0: "ConcreteSemantics.SL_proof (tcfe tys) P (abs_stmt.Inhale A ;; fst (translate tys \<Gamma> C)) R1"
    "ConcreteSemantics.SL_proof (tcfe tys) R1 (abs_stmt.Exhale B) Q"
  then have "entails R1 (Q \<otimes> B)" by auto
  show "(tcfe tys) \<turnstile>CSL [P \<otimes> inhalify tys A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
  proof (rule ConcreteSemantics.SL_proof_Seq_elim[OF asm0(1)])
    fix R0 assume asm1: "ConcreteSemantics.SL_proof (tcfe tys) P (abs_stmt.Inhale A) R0"
          "ConcreteSemantics.SL_proof (tcfe tys) R0 (fst (translate tys \<Gamma> C)) R1"
    then have "ConcreteSemantics.SL_proof (tcfe tys) (P \<otimes> inhalify tys A) (fst (translate tys \<Gamma> C)) R1"
      by auto
    show "(tcfe tys) \<turnstile>CSL [P \<otimes> inhalify tys A \<otimes> UNIV] C [Q \<otimes> B \<otimes> UNIV]"
    proof (rule RuleCons)
      show "(tcfe tys) \<turnstile>CSL [P \<otimes> inhalify tys A \<otimes> UNIV] C [R1 \<otimes> UNIV]"
        using \<open>ConcreteSemantics.SL_proof (tcfe tys) (P \<otimes> inhalify tys A) (fst (translate tys \<Gamma> C)) R1\<close> assms(1) assms(3) invariant_translate_def by blast
      show "R1 \<otimes> UNIV \<subseteq> Q \<otimes> B \<otimes> UNIV"
        by (meson \<open>entails R1 (Q \<otimes> B)\<close> add_set_mono entails_def order_refl)
    qed (simp)
  qed
qed


lemma drop_conjunct_entails:
  "A \<otimes> B \<otimes> UNIV \<subseteq> B \<otimes> UNIV"
  by (metis add_set_asso add_set_left_comm add_set_mono equalityD1 top_greatest)


(*
| "translate tys \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (P1 \<otimes> P2);; ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (Q1 \<otimes> Q2)),
  let r1 = translate tys \<Gamma> C1 in let r2 = translate tys \<Gamma> C2 in
  { (Inhale P1;; fst r1;; Exhale Q1), (Inhale P2;; fst r2;; Exhale Q2) } \<union> snd r1 \<union> snd r2)"
*)


lemma typed_self_framing_star:
  assumes "self_framing A"
      and "self_framing B"
    shows "self_framing (A \<otimes> B)"
proof (rule self_framingI)
  fix \<omega>
  show "(\<omega> \<in> A \<otimes> B) = (stabilize \<omega> \<in> A \<otimes> B)"
  proof
    assume "\<omega> \<in> A \<otimes> B"
    then obtain a b where "Some \<omega> = a \<oplus> b" "a \<in> A" "b \<in> B"
      by (meson x_elem_set_product)
    then show "stabilize \<omega> \<in> A \<otimes> B"
      by (meson assms(1) assms(2) self_framingE stabilize_sum x_elem_set_product)
  next
    assume "stabilize \<omega> \<in> A \<otimes> B"
    then obtain a b where "Some (stabilize \<omega>) = a \<oplus> b" "a \<in> A" "b \<in> B"
      by (meson x_elem_set_product)
    then obtain b' where "Some b' = b \<oplus> |\<omega>|"
      by (metis (no_types, opaque_lifting) asso2 decompose_stabilize_pure option.exhaust_sel)
    then have "stabilize b' = stabilize b"
      using plus_pure_stabilize_eq by blast
    then have "b' \<in> B"
      by (metis \<open>b \<in> B\<close> assms(2) self_framing_def)
    then show "\<omega> \<in> A \<otimes> B"
      by (metis (no_types, lifting) \<open>Some (stabilize \<omega>) = a \<oplus> b\<close> \<open>Some b' = b \<oplus> |\<omega>|\<close> \<open>a \<in> A\<close> asso1 decompose_stabilize_pure x_elem_set_product)
  qed
qed



lemma self_framing_typed_star_atrue:
  assumes "self_framing P"
  shows "self_framing (P \<otimes> UNIV)"
  by (simp add: assms typed_self_framing_star)

lemma inhalify_distributes:
  "inhalify tys (A \<otimes> B) = inhalify tys A \<otimes> inhalify tys B" (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix x assume "x \<in> inhalify tys (A \<otimes> B)"
    then obtain a b where "typed (tcfe tys) (stabilize x)" "a \<in> A" "b \<in> B" "Some x = a \<oplus> b"
      by (metis (no_types, opaque_lifting) comp_def member_filter x_elem_set_product)
    then have "typed (tcfe tys) (stabilize a) \<and> typed (tcfe tys) (stabilize b)"
      using TypedEqui.typed_smaller greater_def greater_equiv stabilize_mono by blast
    then show "x \<in> ?Q"
      using \<open>Some x = a \<oplus> b\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> x_elem_set_product by fastforce
  qed
  show "?Q \<subseteq> ?P"
  proof
    fix x assume "x \<in> ?Q"
    then obtain a b where "typed (tcfe tys) (stabilize a) \<and> typed (tcfe tys) (stabilize b)" "a \<in> A" "b \<in> B" "Some x = a \<oplus> b"
      by (smt (z3) comp_apply member_filter x_elem_set_product)
    then show "x \<in> ?P"
      by (smt (verit, best) TypedEqui.typed_sum comp_apply member_filter stabilize_sum x_elem_set_product)
  qed
qed


lemma t_entails_add:
  assumes "t_entails tys A1 A2"
  assumes "t_entails tys B1 B2"
  shows "t_entails tys (A1 \<otimes> B1) (A2 \<otimes> B2)"
  by (smt (verit, best) ConcreteSemantics.entails_typed_def TypedEqui.typed_smaller assms(1) assms(2) greater_equiv in_set_sum is_in_set_sum singletonD x_elem_set_product)


lemma univ_t_entails_atrue:
  "t_entails tys UNIV (atrue tys)"
  by (simp add: ConcreteSemantics.entails_typedI TypedEqui.typed_state_then_stabilize_typed atrue_def)

lemma invariant_translate_parallel:
  assumes "\<And>P Q. invariant_translate tys \<Gamma> P C1 Q"
    and "\<And>P Q. invariant_translate tys \<Gamma> P C2 Q"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      and "wf_stmt tys \<Gamma> ({P1} C1 {Q1} || {P2} C2 {Q2})"
    shows "invariant_translate tys \<Gamma> P ({P1} C1 {Q1} || {P2} C2 {Q2}) Q"
proof (rule invariant_translateI)
  let ?P1 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1"
  let ?P2 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2"
  let ?Q1 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1"
  let ?Q2 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2"

  assume asm0: "proof_obligations_valid tys (snd (translate tys \<Gamma> {P1} C1 {Q1} || {P2} C2 {Q2}))"
    "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> {P1} C1 {Q1} || {P2} C2 {Q2})) Q"
  then have r0: "proof_obligations_valid tys (snd (translate tys \<Gamma> C1)) \<and> proof_obligations_valid tys (snd (translate tys \<Gamma> C2))"
    using proof_obligations_valid_union
    unfolding translate.simps by (metis sndI)
  moreover obtain B1 where B1_def: "ConcreteSemantics.SL_proof (tcfe tys) (atrue tys)
    (Inhale ?P1;; fst (translate tys \<Gamma> C1);; Exhale (inhalify tys ?Q1)) B1"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover obtain B2 where B2_def: "ConcreteSemantics.SL_proof (tcfe tys) (atrue tys)
  (Inhale ?P2;; fst (translate tys \<Gamma> C2);; Exhale (inhalify tys ?Q2)) B2"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover have main: "ConcreteSemantics.SL_proof (tcfe tys) P (Exhale (inhalify tys (?P1 \<otimes> ?P2));;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (?Q1 \<otimes> ?Q2)) Q"
    using asm0 by simp
  then obtain R0 R1 where R_defs:
    "ConcreteSemantics.SL_proof (tcfe tys) P (abs_stmt.Exhale (inhalify tys (?P1 \<otimes> ?P2))) R0"
    "ConcreteSemantics.SL_proof (tcfe tys) R0 (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2)) R1"
    "ConcreteSemantics.SL_proof (tcfe tys) R1 (abs_stmt.Inhale (?Q1 \<otimes> ?Q2)) Q"
    by (meson ConcreteSemantics.SL_proof_Seq_elim)
  then have P_Q_R_rels:
    "entails P (R0 \<otimes> inhalify tys (?P1 \<otimes> ?P2)) \<and> Q = R1 \<otimes> inhalify tys (?Q1 \<otimes> ?Q2)" by auto
  moreover have r: "self_framing R0 \<and>
    self_framing R1 \<and> t_entails tys R0 R1 \<and> fvA (tcfe tys) R1 \<subseteq> fvA (tcfe tys) R0 - set (wrL C1 @ wrL C2)"
    using ConcreteSemantics.SL_proof_Havoc_list_elim[OF R_defs(2) assms(3)]
    using tcfe_is_finite by fastforce

(* R1 is the frame! *)

  show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> UNIV]"
  proof (rule RuleConsTyped)
    show "(tcfe tys) \<turnstile>CSL [((inhalify tys ?P1 \<otimes> UNIV) \<otimes> (inhalify tys ?P2 \<otimes> UNIV)) \<otimes> R1] {P1} C1 {Q1} || {P2} C2 {Q2} [((inhalify tys ?Q1 \<otimes> UNIV) \<otimes> (inhalify tys ?Q2 \<otimes> UNIV)) \<otimes> R1]"
    proof (rule RuleFrame)
      show "(tcfe tys) \<turnstile>CSL [inhalify tys ?P1 \<otimes> UNIV \<otimes> (inhalify tys ?P2 \<otimes> UNIV)] {P1} C1 {Q1} || {P2} C2 {Q2} [inhalify tys ?Q1 \<otimes> UNIV \<otimes> (inhalify tys ?Q2 \<otimes> UNIV)]"
      proof (rule RulePar)
        show "(tcfe tys) \<turnstile>CSL [inhalify tys ?P1 \<otimes> UNIV] C1 [inhalify tys ?Q1 \<otimes> UNIV]"
        proof (rule RuleConsTyped)
          show "(tcfe tys) \<turnstile>CSL [(atrue tys) \<otimes> inhalify tys ?P1 \<otimes> UNIV] C1 [B1 \<otimes> inhalify tys ?Q1 \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(1) B1_def]
            using r0 by blast
          show "t_entails tys (inhalify tys ?P1 \<otimes> UNIV) ((atrue tys) \<otimes> inhalify tys ?P1 \<otimes> UNIV)"
            by (meson ConcreteSemantics.entails_typed_refl ConcreteSemantics.entails_typed_trans conjunct_with_true_t_entails t_entails_add univ_t_entails_atrue)
          show "t_entails tys (B1 \<otimes> inhalify tys ?Q1 \<otimes> UNIV) (inhalify tys ?Q1 \<otimes> UNIV)"
            by (simp add: drop_conjunct_entails subset_entails)
        qed
        show "(tcfe tys) \<turnstile>CSL [inhalify tys ?P2 \<otimes> UNIV] C2 [inhalify tys ?Q2 \<otimes> UNIV]"
        proof (rule RuleConsTyped)
          show "(tcfe tys) \<turnstile>CSL [(atrue tys) \<otimes> inhalify tys ?P2 \<otimes> UNIV] C2 [B2 \<otimes> inhalify tys ?Q2 \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(2) B2_def]
            using r0 by blast
          show "t_entails tys (B2 \<otimes> inhalify tys ?Q2 \<otimes> UNIV) (inhalify tys ?Q2 \<otimes> UNIV)"
            by (simp add: drop_conjunct_entails subset_entails)
          show "t_entails tys (inhalify tys ?P2 \<otimes> UNIV) ((atrue tys) \<otimes> inhalify tys ?P2 \<otimes> UNIV)"
            by (meson ConcreteSemantics.entails_typed_refl ConcreteSemantics.entails_typed_trans conjunct_with_true_t_entails t_entails_add univ_t_entails_atrue)
        qed
        show "disjoint (fvC C1 \<union> fvA (tcfe tys) (inhalify tys ?Q1 \<otimes> UNIV)) (wrC C2)"

          using assms(4) by auto
        show "disjoint (fvC C2 \<union> fvA (tcfe tys) (inhalify tys ?Q2 \<otimes> UNIV)) (wrC C1)"
          using assms(4) by auto
        show "self_framing (inhalify tys ?P1 \<otimes> UNIV)"
          using assms(4) self_framing_then_self_framing_inhalify self_framing_typed_star_atrue wf_stmt.simps(3) by blast
        show "self_framing (inhalify tys ?P2 \<otimes> UNIV)"
          using assms(4) self_framing_typed_star_atrue self_framing_then_self_framing_inhalify by auto
      qed
      show "disjoint (fvA (tcfe tys) R1) (wrC {P1} C1 {Q1} || {P2} C2 {Q2})"
        by (metis (mono_tags, opaque_lifting) Diff_subset_conv Orderings.order_eq_iff r bot.extremum disjoint_minus disjoint_simps(2) disjoint_simps(3) sup.order_iff wrC.simps(7) wrC.simps(8) wrL.simps(7) wrL_wrC_same)
      show "self_framing (inhalify tys ?P1 \<otimes> UNIV \<otimes> (inhalify tys ?P2 \<otimes> UNIV))"
        by (meson assms(4) self_framing_typed_star_atrue self_framing_then_self_framing_inhalify typed_self_framing_star wf_stmt.simps(3))
      show "self_framing R1"
        using R_defs(3) by blast
    qed
    show "t_entails tys (P \<otimes> UNIV) (inhalify tys ?P1 \<otimes> UNIV \<otimes> (inhalify tys ?P2 \<otimes> UNIV) \<otimes> R1)"
    proof -
      have "t_entails tys (P \<otimes> UNIV) ((R0 \<otimes> (inhalify tys ?P1 \<otimes> inhalify tys ?P2)) \<otimes> UNIV)"
        by (metis P_Q_R_rels add_set_mono atrue_twice_equal atrue_twice_same entails_def inhalify_distributes subset_entails)
      also have "t_entails tys (...) (R1 \<otimes> (inhalify tys (?P1 \<otimes> ?P2) \<otimes> UNIV))"
        using r add_set_asso
        by (simp add: ConcreteSemantics.entails_typed_refl add_set_commm add_set_left_comm inhalify_distributes t_entails_add)
      moreover have "t_entails tys (...) (inhalify tys ?P1 \<otimes> UNIV \<otimes> (inhalify tys ?P2 \<otimes> UNIV) \<otimes> R1)"
        using add_set_commm add_set_left_comm
        by (metis (no_types, opaque_lifting) conjunct_with_true_t_entails inhalify_distributes)
      ultimately show ?thesis
        using ConcreteSemantics.entails_typed_trans by blast
    qed
    show "t_entails tys (inhalify tys ?Q1 \<otimes> UNIV \<otimes> (inhalify tys ?Q2 \<otimes> UNIV) \<otimes> R1) (Q \<otimes> UNIV)"
      by (metis (no_types, lifting) ConcreteSemantics.entails_typedI P_Q_R_rels add_set_commm add_set_left_comm atrue_twice_equal inhalify_distributes)
  qed
qed

(*
Maybe prove? Need to prove that assertions are wf...
lemma translation_wf:
  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"
    shows "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))"
  using assms
proof (induct C)
  case (Cseq C1 C2)
  then show ?case
    by (metis ConcreteSemantics.wf_abs_stmt.simps(7) fst_eqD translate.simps(7) well_typed_cmd.simps(2) wf_stmt.simps(1))
next
  ...
qed (simp_all)
*)

lemma invariant_translate_if:
  assumes "\<And>P Q. invariant_translate tys \<Gamma> P C1 Q"
      and "\<And>P Q. invariant_translate tys \<Gamma> P C2 Q"
    shows "invariant_translate tys \<Gamma> P (Cif b C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid tys (snd (translate tys \<Gamma> (Cif b C1 C2)))"
    "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> (Cif b C1 C2))) Q"

  show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cif b C1 C2 [Q \<otimes> UNIV]"
  proof (rule ConcreteSemantics.SL_proof_If_elim)
    show "ConcreteSemantics.SL_proof (tcfe tys) P (abs_stmt.If (semantify_bexp b) (fst (translate tys \<Gamma> C1)) (fst (translate tys \<Gamma> C2))) Q"
      by (metis asm0(2) fst_eqD translate.simps(8))
    fix B1 B2 assume asm1: "Q = B1 \<union> B2" "framed_by_exp P (semantify_bexp b)"
       "ConcreteSemantics.SL_proof (tcfe tys) (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) (fst (translate tys \<Gamma> C1)) B1"
       "ConcreteSemantics.SL_proof (tcfe tys) (P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) (fst (translate tys \<Gamma> C2)) B2"
       "self_framing P"
    show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cif b C1 C2 [Q \<otimes> UNIV]"
    proof (rule RuleIf)
      show "(tcfe tys) \<turnstile>CSL [(P \<otimes> UNIV) \<inter> assertify_bexp b] C1 [Q \<otimes> UNIV]"
      proof (rule RuleCons)
        show "(tcfe tys) \<turnstile>CSL [(P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> UNIV] C1 [B1 \<otimes> UNIV]"
          by (metis asm0(1) asm1(3) assms(1) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B1 \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> UNIV) \<inter> assertify_bexp b \<subseteq> (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> UNIV"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp b"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot b (get_store \<omega>)"
            using in_set_sum[of \<omega> P "UNIV"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "|p| \<in> ConcreteSemantics.purify (semantify_bexp b)"
            unfolding ConcreteSemantics.purify_def semantify_bexp_def
            by (simp add: core_charact_equi(1) core_is_pure full_add_charact(1) pure_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.purify (semantify_bexp b)"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> UNIV"
            by (meson UNIV_I \<open>Some \<omega> = p \<oplus> r\<close> x_elem_set_product)
        qed
      qed

      show "(tcfe tys) \<turnstile>CSL [(P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)] C2 [Q \<otimes> UNIV]"
      proof (rule RuleCons)
        show "(tcfe tys) \<turnstile>CSL [(P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) \<otimes> UNIV] C2 [B2 \<otimes> UNIV]"
          by (metis asm0(1) asm1(4) assms(2) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B2 \<otimes> UNIV \<subseteq> Q \<otimes> UNIV"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b) \<subseteq> P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b)) \<otimes> UNIV"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot (Bnot b) (get_store \<omega>)"
            using in_set_sum[of \<omega> P "UNIV"] assertify_bexp_def
            by (smt (verit) Int_iff commutative greater_equiv mem_Collect_eq)
          then have "\<not> bdenot b (get_store |p| )"
            by (simp add: core_charact(1) full_add_charact(1))
          then have "|p| \<in> ConcreteSemantics.purify (negate (semantify_bexp b))"
            unfolding ConcreteSemantics.purify_def semantify_bexp_def negate_def
            by (simp add: core_is_pure pure_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) \<otimes> UNIV"
            by (meson UNIV_I \<open>Some \<omega> = p \<oplus> r\<close> x_elem_set_product)
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

lemma inhalify_intersection:
  "inhalify tys (A \<inter> B) = inhalify tys A \<inter> B"
  by auto

lemma t_entails_add_atrue:
  assumes "t_entails tys A B"
  shows "t_entails tys A ((atrue tys) \<otimes> B)"
  using ConcreteSemantics.entails_typed_trans assms conjunct_with_true_t_entails t_entails_add univ_t_entails_atrue by blast

lemma invariant_translate_while:
  assumes "\<And>P Q. invariant_translate tys \<Gamma> P C Q"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (ConcreteSemantics.havoc_list (wrL C))"
      and "wf_stmt tys \<Gamma> (Cwhile b I C)"
    shows "invariant_translate tys \<Gamma> P (Cwhile b I C) Q"
proof (rule invariant_translateI)
  let ?I = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) I"
  assume asm0: "proof_obligations_valid tys (snd (translate tys \<Gamma> (Cwhile b I C)))"
    "ConcreteSemantics.SL_proof (tcfe tys) P (fst (translate tys \<Gamma> (Cwhile b I C))) Q"
  then have r1: "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
    using proof_obligations_valid_union by fastforce
  moreover obtain B where B_def: "ConcreteSemantics.SL_proof (tcfe tys) (atrue tys) (Inhale (?I \<inter> assertify_bexp b);; fst (translate tys \<Gamma> C);; Exhale (inhalify tys ?I)) B"    
    using asm0(1) insertCI proof_obligations_valid_def proof_obligations_valid_union snd_eqD translate.simps(10)
    by (metis (no_types, lifting))
  moreover obtain R0 R1 where R_defs: "entails P (R0 \<otimes> inhalify tys ?I)" "Q = R1 \<otimes> inhalify tys (?I \<inter> assertify_bexp (Bnot b))"
    "ConcreteSemantics.SL_proof (tcfe tys) R0 (ConcreteSemantics.havoc_list (wrL C)) R1"
    using asm0(2) by auto
  moreover have "t_entails tys R0 R1 \<and> fvA (tcfe tys) R1 \<subseteq> fvA (tcfe tys) R0 - (set (wrL C))"
    using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) tcfe_is_finite by blast

  (* R1 is the frame *)

  show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] Cwhile b I C [Q \<otimes> UNIV]"
  proof (rule RuleConsTyped)
    show "(tcfe tys) \<turnstile>CSL [(inhalify tys ?I \<otimes> UNIV) \<otimes> R1] Cwhile b I C [((inhalify tys ?I \<otimes> UNIV) \<inter> (assertify_bexp (Bnot b))) \<otimes> R1]"
    proof (rule RuleFrame)
      show "(tcfe tys) \<turnstile>CSL [inhalify tys ?I \<otimes> UNIV] Cwhile b I C [(inhalify tys ?I \<otimes> UNIV) \<inter> assertify_bexp (Bnot b)]"
      proof (rule RuleWhile)
        show "(tcfe tys) \<turnstile>CSL [(inhalify tys ?I \<otimes> UNIV) \<inter> assertify_bexp b] C [inhalify tys ?I \<otimes> UNIV]"
        proof (rule RuleConsTyped)
          show "(tcfe tys) \<turnstile>CSL [(atrue tys) \<otimes> inhalify tys (?I \<inter> assertify_bexp b) \<otimes> UNIV] C [B \<otimes> inhalify tys ?I \<otimes> UNIV]"
            using invariant_translate_inhale_exhale_get_proof[OF _ B_def]
            using assms(1) r1 by blast
          show "t_entails tys (B \<otimes> inhalify tys ?I \<otimes> UNIV) (inhalify tys ?I \<otimes> UNIV)"
            by (simp add: drop_conjunct_entails subset_entails)

          show "t_entails tys ((inhalify tys ?I \<otimes> UNIV) \<inter> assertify_bexp b) ((atrue tys) \<otimes> inhalify tys (?I \<inter> assertify_bexp b) \<otimes> UNIV)"
            by (simp add: add_set_asso inhalify_intersection intersect_and_star subset_entails t_entails_add_atrue)
        qed
      qed
      show "disjoint (fvA (tcfe tys) R1) (wrC (Cwhile b I C))"
        using \<open>ConcreteSemantics.entails_typed (tcfe tys) R0 R1 \<and> fvA (tcfe tys) R1 \<subseteq> fvA (tcfe tys) R0 - set (wrL C)\<close> disjoint_def wrL_wrC_same by fastforce
      show "self_framing (inhalify tys ?I \<otimes> UNIV)"
        using assms(3) self_framing_typed_star_atrue self_framing_then_self_framing_inhalify by auto
      show "self_framing R1"
        using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) tcfe_is_finite by blast
    qed
    have "t_entails tys P (R1 \<otimes> inhalify tys ?I)"
    proof -
      have "t_entails tys P (R0 \<otimes> inhalify tys ?I)"
        by (meson calculation(3) entails_def subset_entails)
      moreover have "t_entails tys (R0 \<otimes> inhalify tys ?I) (R1 \<otimes> inhalify tys ?I)"
        by (simp add: ConcreteSemantics.entails_typed_refl \<open>ConcreteSemantics.entails_typed (tcfe tys) R0 R1 \<and> fvA (tcfe tys) R1 \<subseteq> fvA (tcfe tys) R0 - set (wrL C)\<close> t_entails_add)
      ultimately show ?thesis
        using ConcreteSemantics.entails_typed_trans by blast
    qed


    then show "t_entails tys (P \<otimes> UNIV) (inhalify tys ?I \<otimes> UNIV \<otimes> R1)"
      by (simp add: ConcreteSemantics.entails_typed_refl add_set_commm add_set_left_comm t_entails_add)

    show "t_entails tys ((inhalify tys ?I \<otimes> UNIV) \<inter> assertify_bexp (Bnot b) \<otimes> R1) (Q \<otimes> UNIV)"
      by (smt (verit, best) add_set_asso add_set_commm add_set_mono calculation(4) inhalify_intersection intersect_and_star subsetI subset_entails)

  qed
qed


lemma invariant_translate_induct:
  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))"
      and "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
    shows "invariant_translate tys \<Gamma> P C Q"
  using assms
proof (induct C arbitrary: P Q)
  case (Cseq C1 C2)
  then show ?case
    by (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff fst_eqD invariant_translate_seq snd_conv translate.simps(7) well_typed_cmd.simps(2) wf_stmt.simps(1))
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  let ?P1 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) P1"
  let ?P2 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) P2"
  let ?Q1 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q1"
  let ?Q2 = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) Q2"
  show ?case
  proof (rule invariant_translate_parallel)
    show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      using Cpar.prems(3) by simp
    show "wf_stmt tys \<Gamma> {P1} C1 {Q1} || {P2} C2 {Q2}"
      using Cpar.prems(1) by blast
    fix P Q
    show "invariant_translate tys \<Gamma> P C1 Q"
    proof (rule Cpar(1))
      have "ConcreteSemantics.wf_abs_stmt (tcfe tys) (Inhale ?P1;; fst (translate tys \<Gamma> C1);; Exhale (inhalify tys ?Q1))"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C1))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tys C1"
        using Cpar.prems(2) by auto
      show "wf_stmt tys \<Gamma> C1"
        using Cpar.prems(1) by auto
    qed
    show "invariant_translate tys \<Gamma> P C2 Q"
    proof (rule Cpar(2))
      have "ConcreteSemantics.wf_abs_stmt (tcfe tys) (Inhale ?P2;; fst (translate tys \<Gamma> C2);; Exhale (inhalify tys ?Q2))"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C2))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tys C2"
        using Cpar.prems(2) by auto
      show "wf_stmt tys \<Gamma> C2"
        using Cpar.prems(1) by auto
    qed
  qed
next
  case (Cif b C1 C2)
  show ?case
  proof (rule invariant_translate_if)
    fix P Q
    show "invariant_translate tys \<Gamma> P C1 Q"
    proof (rule Cif(1))
      show "wf_stmt tys \<Gamma> C1"
        using Cif.prems(1) by auto
      show "well_typed_cmd tys C1"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C1))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed
    show "invariant_translate tys \<Gamma> P C2 Q"
    proof (rule Cif(2))
      show "wf_stmt tys \<Gamma> C2"
        using Cif.prems(1) by auto
      show "well_typed_cmd tys C2"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C2))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed
  qed
next
  case (Cwhile b I C)
  let ?I = "make_semantic_assertion_untyped \<Gamma> (tcfes tys) I"
  show ?case
  proof (rule invariant_translate_while)
    show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (ConcreteSemantics.havoc_list (wrL C))"
      using Cwhile.prems(3) by simp
    show "wf_stmt tys \<Gamma> (Cwhile b I C)"
      using Cwhile.prems(1) by auto
    fix P Q show "invariant_translate tys \<Gamma> P C Q"
    proof (rule Cwhile(1)[of P Q])
      show "wf_stmt tys \<Gamma> C"
        using Cwhile.prems(1) by auto
      show "well_typed_cmd tys C"
        using Cwhile.prems(2) by auto
      have "ConcreteSemantics.wf_abs_stmt (tcfe tys) (Inhale (?I \<inter> assertify_bexp b);; fst (translate tys \<Gamma> C);; Exhale (inhalify tys ?I))"
        using Cwhile.prems(4) by fastforce
      then show "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))" by force
      show "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
        using Cwhile.prems(4) by auto
    qed
  qed
qed (simp_all add: invariant_translate_skip invariant_translate_free invariant_translate_alloc invariant_translate_seq
      invariant_translate_write invariant_translate_read invariant_translate_assign)


lemma atrue_semi_typed:
  "ConcreteSemantics.semi_typed (tcfe tys) (atrue tys)"
  by (metis ConcreteSemantics.semi_typedI atrue_def comp_apply member_filter)

(*
lemma self_framing_atrue:
  "self_framing (atrue tys)"
proof (rule self_framingI)
*)

lemma t_entails_inhalify:
  "t_entails tys P (inhalify tys P)"
  by (simp add: ConcreteSemantics.entails_typed_def TypedEqui.typed_state_then_stabilize_typed)


theorem sound_translation:
  assumes "wf_stmt tys \<Gamma> C"
      and "well_typed_cmd tys C"
      and "ConcreteSemantics.wf_abs_stmt (tcfe tys) (fst (translate tys \<Gamma> C))"
      and "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe tys) Cv"
      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"
      and "ConcreteSemantics.verifies_set (tcfe tys) (atrue tys) (Inhale P;; fst (translate tys \<Gamma> C);; Exhale Q)"
      and "\<And>Cv. Cv \<in> snd (translate tys \<Gamma> C) \<Longrightarrow> ConcreteSemantics.verifies_set (tcfe tys) (atrue tys) Cv"

    shows "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
proof -
  thm ConcreteSemantics.Viper_implies_SL_proof[OF assms(6) assms(4)]

  obtain B where "ConcreteSemantics.SL_proof (tcfe tys) (atrue tys) (Inhale P;; fst (translate tys \<Gamma> C);; Exhale Q) B"
    by (metis ConcreteSemantics.Viper_implies_SL_proof ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(3) ConcreteSemantics.wf_abs_stmt.simps(7) assms(3) assms(5) assms(6) atrue_def atrue_self_framing_and_typed atrue_semi_typed test_self_framing)


  then obtain B' where "ConcreteSemantics.SL_proof (tcfe tys) ((atrue tys) \<otimes> inhalify tys P) (fst (translate tys \<Gamma> C)) B'" "entails B' (B \<otimes> Q)"
    by blast


  show "(tcfe tys) \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  proof (rule RuleConsTyped)
    show "(tcfe tys) \<turnstile>CSL [inhalify tys P \<otimes> (atrue tys) \<otimes> UNIV] C [B' \<otimes> UNIV]"
    proof (rule invariant_translateE[of _ _ "inhalify tys P \<otimes> (atrue tys)" C])
      show "ConcreteSemantics.SL_proof (tcfe tys) (inhalify tys P \<otimes> (atrue tys)) (fst (translate tys \<Gamma> C)) B'"
        by (metis \<open>ConcreteSemantics.SL_proof (tcfe tys) ((atrue tys) \<otimes> inhalify tys P) (fst (translate tys \<Gamma> C)) B'\<close> add_set_commm)
      show "invariant_translate tys \<Gamma> (inhalify tys P \<otimes> (atrue tys)) C B'"


        by (meson assms(1) assms(2) assms(3) assms(4) invariant_translate_induct)
      show "proof_obligations_valid tys (snd (translate tys \<Gamma> C))"
        unfolding proof_obligations_valid_def
      proof clarify
        fix Cv assume "Cv \<in> snd (translate tys \<Gamma> C)"
        then show "\<exists>B. ConcreteSemantics.SL_proof (tcfe tys) (atrue tys) Cv B"
          using ConcreteSemantics.Viper_implies_SL_proof[of "tcfe tys" "atrue tys" Cv] assms(4) assms(7)
          by (metis atrue_def atrue_self_framing_and_typed atrue_semi_typed test_self_framing)
      qed
    qed
    show "t_entails tys (P \<otimes> UNIV) (inhalify tys P \<otimes> (atrue tys) \<otimes> UNIV)"
      by (simp add: ConcreteSemantics.entails_typed_refl add_set_asso t_entails_add t_entails_add_atrue t_entails_inhalify)
    show "t_entails tys (B' \<otimes> UNIV) (Q \<otimes> UNIV)"
      by (metis (no_types, lifting) \<open>entails B' (B \<otimes> Q)\<close> add_set_mono atrue_twice_equal drop_conjunct_entails dual_order.trans entails_def subset_entails)
  qed
qed


end