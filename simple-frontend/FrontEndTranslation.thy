theory FrontEndTranslation
  imports CSL_IDF
begin

type_synonym 'a v_stmt = "('a equi_state, 'a val, 'a custom) abs_stmt"

definition semantify_exp :: "ParImp.exp \<Rightarrow> ('a equi_state, 'a val) AbstractSemantics.exp" where
  "semantify_exp e \<omega> = Some (VInt (edenot e (get_store \<omega>)))"

definition semantify_bexp :: "ParImp.bexp \<Rightarrow> ('a equi_state) AbstractSemantics.bexp" where
  "semantify_bexp b \<omega> = (if (bdenot b (get_store \<omega>)) then Some True else Some False)"

definition semantify_addr :: "var \<Rightarrow> ('a equi_state, address) AbstractSemantics.exp" where
  "semantify_addr x \<omega> = (if (\<exists>l. get_store \<omega> x = Some (VRef (Address l)))
  then Some (SOME l. get_store \<omega> x = Some (VRef (Address l)))
  else None)"

lemma semantify_addr_equiv:
  "semantify_addr x \<omega> = Some l \<longleftrightarrow> get_store \<omega> x = Some (VRef (Address l))"
  unfolding semantify_addr_def by force

lemma RuleCons:
  assumes "\<Gamma> \<turnstile>CSL [P] C [Q]"
      and "P' \<subseteq> P"
      and "Q \<subseteq> Q'"
    shows "\<Gamma> \<turnstile>CSL [P'] C [Q']"
  using RuleConsTyped assms subset_entails 
  by blast

lemma convert_proof_assign:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) A (abs_stmt.LocalAssign x (semantify_exp e)) B"
  shows "tcfe \<Delta> tys \<turnstile>CSL [A] Cassign x e [B]"
proof -
  have "B = ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A"
    using ConcreteSemantics.SL_proof_LocalAssign_elim assms
    by fast
  moreover have "(tcfe \<Delta> tys) \<turnstile>CSL [A] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
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
    show "(tcfe \<Delta> tys) \<turnstile>CSL [sub_pre x e (ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A)] Cassign x e [ConcreteSemantics.post_substitute_var_assert x (semantify_exp e) A]"
      by (simp add: RuleAssign)
  qed (simp)
  ultimately show ?thesis by auto
qed

lemma convert_proof_skip:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) A Skip B"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [A] Cskip [B]"
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
  "make_semantic_assertion_untyped (tcfe \<Delta> tys) F A = well_typedly (tcfe \<Delta> tys) F (\<langle>type_ctxt_front_end, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
*)

(*
abbreviation tcfe :: "vtyp list \<Rightarrow> ('a val, char list \<Rightarrow> 'a val set option) abs_type_context" where
  "tcfe \<equiv> type_ctxt_front_end"
*)

abbreviation inhalify where
  "inhalify \<Delta> tys P \<equiv> Set.filter (typed (tcfe \<Delta> tys) \<circ> stabilize) P"

lemma self_framing_then_self_framing_inhalify:
  assumes "self_framing P"
  shows "self_framing (inhalify \<Delta> tys P)"
proof (rule self_framingI)
  fix \<omega> show "(\<omega> \<in> inhalify \<Delta> tys P) = (stabilize \<omega> \<in> inhalify \<Delta> tys P)"
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

definition no_trace where
  "no_trace \<omega> \<longleftrightarrow> get_trace \<omega> = Map.empty"

definition atrue where
  "atrue \<Delta> tys = Set.filter no_trace (inhalify \<Delta> tys UNIV)"

fun wf_stmt :: "('a, 'a virtual_state) interp \<Rightarrow> vtyp list \<Rightarrow> cmd \<Rightarrow> bool" 
  where
  "wf_stmt \<Delta> tys (Cseq C1 C2) \<longleftrightarrow> wf_stmt \<Delta> tys C1 \<and> wf_stmt \<Delta> tys C2"
| "wf_stmt \<Delta> tys (Calloc r e) \<longleftrightarrow> r \<notin> fvE e"

| "wf_stmt \<Delta> tys ({P1} C1 {Q1} || {P2} C2 {Q2}) \<longleftrightarrow>
  disjoint
  (fvC C1 \<union> fvA (tcfe \<Delta> tys) (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1) \<otimes> atrue \<Delta> tys)) (wrC C2)
  \<and> disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2) \<otimes> atrue \<Delta> tys)) (wrC C1) \<and>
  self_framing (make_semantic_assertion_untyped \<Delta> (tcfes tys) P1) \<and>
  self_framing (make_semantic_assertion_untyped \<Delta> (tcfes tys) P2) \<and>
  self_framing (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1) \<and>
  self_framing (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2) \<and>
  wf_stmt \<Delta> tys C1 \<and> wf_stmt \<Delta> tys C2"

| "wf_stmt \<Delta> tys (Cif b C1 C2) \<longleftrightarrow> wf_stmt \<Delta> tys C1 \<and> wf_stmt \<Delta> tys C2"

| "wf_stmt \<Delta> tys (Cwhile b I C) \<longleftrightarrow> self_framing (make_semantic_assertion_untyped \<Delta> (tcfes tys) I)
                              \<and> wf_stmt \<Delta> tys C"

| "wf_stmt \<Delta> tys _ \<longleftrightarrow> True"


(*
  "atrue \<Delta> tys = Set.filter no_trace (inhalify \<Delta> tys UNIV)"
*)

lemma atrue_self_framing_and_typed[simp]:
  "self_framing UNIV"
  by (simp add: self_framing_def)

(*
lemma wf_context_type_context[simp]:
  "TypedEqui.wf_context (tcfe \<Delta> tys)"
  unfolding TypedEqui.wf_context_def
proof -
  have "dom (variables (tcfe \<Delta> tys)) \<subseteq> {x. x < undefined}"
    by (metis CollectI abs_type_context.select_convs(1) domIff subsetI type_ctxt_front_end_def type_ctxt_store_def)
  then show "finite (dom (variables (tcfe \<Delta> tys)))"
    by (simp add: finite_subset)
qed
*)

(*
Set.filter (typed \<Delta> \<circ> stabilize) P
*)


abbreviation stab_inhalify where
  "stab_inhalify \<Delta> tys P \<equiv> inhalify \<Delta> tys (Stabilize P)"

abbreviation t_entails where
  "t_entails \<Delta> tys \<equiv> ConcreteSemantics.entails_typed (tcfe \<Delta> tys)"

lemma conjunct_with_true_t_entails:
  "t_entails \<Delta> tys P (UNIV \<otimes> P)"
  by (simp add: conjunct_with_true_entails subset_entails)

lemma conjunct_with_stabilize_emp_t_entails:
  "t_entails \<Delta> tys P (Stabilize emp \<otimes> P)"
  unfolding ConcreteSemantics.entails_typed_def
  by (metis (no_types, opaque_lifting) Stable_def Stable_emp add_set_commm add_set_mono emp_star_right_id subset_iff)


lemma convert_proof_alloc:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))) Q"
      and "well_typed_cmd tys (Calloc r e)"
      and "wf_stmt \<Delta> tys (Calloc r e)"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [P] Calloc r e [Q]"
proof (rule RuleConsTyped)

  have asm0: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Havoc r) (TypedEqui.exists_assert (tcfe \<Delta> tys) r P)
  \<and> ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (TypedEqui.exists_assert (tcfe \<Delta> tys) r P) (Inhale (Stabilize (full_ownership_with_val r e))) Q
  \<and> self_framing P"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim assms(1))
  then have "Q = TypedEqui.exists_assert (tcfe \<Delta> tys) r P \<otimes> inhalify \<Delta> tys (Stabilize (full_ownership_with_val r e))"
    by blast

  show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize emp \<otimes> TypedEqui.exists_assert (tcfe \<Delta> tys) r P] Calloc r e [inhalify \<Delta> tys (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert (tcfe \<Delta> tys) r P]"
  proof (rule RuleFrame)
    have "r \<notin> fvE e"
      using assms(3) by auto
    then have "(tcfe \<Delta> tys) \<turnstile>CSL [emp] Calloc r e [full_ownership_with_val r e]"
      using RuleAlloc[of r e] by simp
    then show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize emp] Calloc r e [inhalify \<Delta> tys (Stabilize (full_ownership_with_val r e))]"
      using RuleStabilizeTyped by (metis RuleInhalify)

    show "disjoint (fvA (tcfe \<Delta> tys) (TypedEqui.exists_assert (tcfe \<Delta> tys) r P)) (wrC (Calloc r e))"
      using ConcreteSemantics.exists_assert_no_in_fv disjoint_def
      by (metis boolean_algebra.conj_zero_right disjoint_insert(1) finite_context_simp subset_Diff_insert wrC.simps(5))

    show "self_framing (TypedEqui.exists_assert (tcfe \<Delta> tys) r P)"
      using asm0 by fastforce
  qed (simp)
  then have "variables (tcfe \<Delta> tys) r \<noteq> None"
    using assms(2)
    unfolding type_ctxt_front_end_def type_ctxt_store_def by simp
  then have "t_entails \<Delta> tys P (TypedEqui.exists_assert (tcfe \<Delta> tys) r P)"
    using ConcreteSemantics.SL_proof_Havoc_elim_entails[of "tcfe \<Delta> tys" P r "TypedEqui.exists_assert (tcfe \<Delta> tys) r P"]
    using asm0
    using finite_context_simp by blast

  then show "t_entails \<Delta> tys P (Stabilize emp \<otimes> TypedEqui.exists_assert (tcfe \<Delta> tys) r P)"
    using ConcreteSemantics.entails_typed_trans conjunct_with_stabilize_emp_t_entails by blast

  show "t_entails \<Delta> tys (inhalify \<Delta> tys (Stabilize (full_ownership_with_val r e)) \<otimes> TypedEqui.exists_assert (tcfe \<Delta> tys) r P) Q"
    by (simp add: ConcreteSemantics.entails_typed_refl \<open>Q = TypedEqui.exists_assert (tcfe \<Delta> tys) r P \<otimes> inhalify \<Delta> tys (Stabilize (full_ownership_with_val r e))\<close> add_set_commm)
qed

lemma helper_exhale_encoding:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Exhale (Stabilize A)) Q"
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
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Exhale (Stabilize (full_ownership r))) Q"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Exhale_elim)
  assume asm0: "entails P (Q \<otimes> Stabilize (full_ownership r))" "self_framing P" "self_framing Q"
  show "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cfree r [Q \<otimes> UNIV]"
  proof (rule RuleCons)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> Q] Cfree r [Stabilize (UNIV) \<otimes> Q]"
    proof (rule RuleFrame)
      show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize (full_ownership r)] Cfree r [Stabilize (UNIV)]"
        using RuleFree RuleStabilizeTyped by blast
    qed (simp_all add: asm0)
    show "P \<subseteq> Stabilize (full_ownership r) \<otimes> Q"
      using assms helper_exhale_encoding by meson
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
  assumes "TypedEqui.typed (tcfe \<Delta> tys) \<omega>'"
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
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e))) Q"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
  using assms(1)
proof (rule ConcreteSemantics.SL_proof_Custom_elim)
  assume asm0: "SL_Custom (tcfe \<Delta> tys) P (custom.FieldAssign (semantify_addr r) field_val (semantify_exp e)) Q"
  "self_framing P" "self_framing Q"
  show "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    using asm0(1)
  proof (rule SL_custom_FieldAssign)
    assume asm1: "Q = update_value (tcfe \<Delta> tys) P (semantify_addr r) field_val (semantify_exp e)"
      "self_framing P" "entails P {\<omega>. \<exists>l. get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l}"
      "framed_by_exp P (semantify_addr r)" "framed_by_exp P (semantify_exp e)"
    show "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cwrite r e [Q \<otimes> UNIV]"
    proof (rule RuleConsTyped)


      let ?F = "Stabilize { remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l}"
      show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize (full_ownership r) \<otimes> ?F] Cwrite r e [Stabilize (full_ownership_with_val r e) \<otimes> ?F]"
      proof (rule RuleFrame)
        show "(tcfe \<Delta> tys) \<turnstile>CSL [Stabilize (full_ownership r)] Cwrite r e [Stabilize (full_ownership_with_val r e)]"
          by (simp add: RuleStabilizeTyped RuleWrite)
      qed (simp_all)
      
      show "ConcreteSemantics.entails_typed (tcfe \<Delta> tys) P (Stabilize (full_ownership r) \<otimes> ?F)"
      proof (rule ConcreteSemantics.entails_typedI)
        fix \<omega> assume "\<omega> \<in> P" "typed (tcfe \<Delta> tys) \<omega>"
        then obtain l where "get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l"          
          by (smt (verit) CollectD asm1(3) entails_def subsetD)
        then have "Some \<omega> = remove_only \<omega> (l, field_val) \<oplus> set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))"
          using split_remove_only_owns_only by blast
        moreover obtain v' where "get_h \<omega> (l, field_val) = Some v'"
          by (metis EquiSemAuxLemma.gr_0_is_ppos \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> not_gr_0 vstate_wf_Some zero_neq_one)
        then obtain v where "v' = VInt v"
          by (smt (verit, best) \<open>typed (tcfe \<Delta> tys) \<omega>\<close> abs_type_context.select_convs(2) mem_Collect_eq snd_conv type_ctxt_front_end_def type_ctxt_heap_def typed_get_vh vints_def)

        
        moreover have "set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>))) \<in> Stabilize (full_ownership r)"
        proof (rule in_StabilizeI)
          show "stabilize (set_state \<omega> (Abs_virtual_state (concretize (\<lambda>l'. if (l, field_val) = l' then 1 else 0) (get_state \<omega>)))) \<in> full_ownership r"
            apply (rule in_full_ownership[of _ _ l])
            using \<open>get_m \<omega> (l, field_val) = 1 \<and> semantify_addr r \<omega> = Some l\<close> semantify_addr_equiv apply fastforce
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

        moreover have "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) \<in> update_value (tcfe \<Delta> tys) P (semantify_addr r) field_val (semantify_exp e)"
          using \<open>\<omega> \<in> P\<close> \<open>semantify_addr r \<omega> = Some l'\<close> semantify_exp_def
        proof (rule in_update_value)
          show "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>'))) = update_heap_val \<omega> (l', field_val) (VInt (edenot e (get_store \<omega>)))"
            by (metis calculation(2) calculation(3) get_store_set_state greater_charact)
          show "typed_value (tcfe \<Delta> tys) field_val (VInt (edenot e (get_store \<omega>)))"
          proof (rule typed_valueI)
            fix ty assume "custom_context (tcfe \<Delta> tys) field_val = Some ty"
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
      then show "ConcreteSemantics.entails_typed (tcfe \<Delta> tys) (Stabilize (full_ownership_with_val r e) \<otimes> Stabilize {remove_only \<omega> (l, field_val) |\<omega> l. \<omega> \<in> P \<and> semantify_addr r \<omega> = Some l})
     (Q \<otimes> UNIV)"
        using ConcreteSemantics.entails_typed_def by blast
    qed
  qed
qed


definition semantify_heap_loc :: "var \<Rightarrow> ('a equi_state, 'a val) AbstractSemantics.exp" where
  "semantify_heap_loc r \<omega> =
  (if (\<exists>l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_h \<omega> (l, field_val) = Some (VInt v))
  then Some (the (get_h \<omega> (SOME l. get_store \<omega> r = Some (VRef (Address l)), field_val)))
  else None)"

lemma convert_proof_read:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (LocalAssign x (semantify_heap_loc r)) Q"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cread x r [Q]"
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

  show "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cread x r [Q]"
  proof (rule RuleCons)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [P] Cread x r [read_result P x r]"
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

fun translate :: "('a, 'a virtual_state) interp \<Rightarrow> vtyp list \<Rightarrow> cmd \<Rightarrow> 'a v_stmt \<times> 'a v_stmt set"
  where
  "translate \<Delta> tys Cskip = (Skip, {})"
| "translate \<Delta> tys (Cassign x e) = (LocalAssign x (semantify_exp e), {})"

| "translate \<Delta> tys (Calloc r e) = ((Havoc r;; Inhale (Stabilize (full_ownership_with_val r e))), {})"
| "translate \<Delta> tys (Cfree r) = (Exhale (Stabilize (full_ownership r)), {})"
| "translate \<Delta> tys (Cwrite r e) = (Custom (FieldAssign (semantify_addr r) field_val (semantify_exp e)), {})"
| "translate \<Delta> tys (Cread x r) = (LocalAssign x (semantify_heap_loc r), {})"

| "translate \<Delta> tys (Cseq C1 C2) = (let r1 = translate \<Delta> tys C1 in let r2 = translate \<Delta> tys C2 in
  (fst r1;; fst r2, snd r1 \<union> snd r2))"

| "translate \<Delta> tys (Cif b C1 C2) = (If (semantify_bexp b) (fst (translate \<Delta> tys C1)) (fst (translate \<Delta> tys C2)), snd (translate \<Delta> tys C1) \<union> snd (translate \<Delta> tys C2))"

| "translate \<Delta> tys ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) P1 \<otimes> make_semantic_assertion_untyped \<Delta> (tcfes tys) P2));;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);;
  Inhale (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1 \<otimes> make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2)),
  let r1 = translate \<Delta> tys C1 in let r2 = translate \<Delta> tys C2 in
  { (Inhale (make_semantic_assertion_untyped \<Delta> (tcfes tys) P1);; fst r1;; Exhale (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1))),
  (Inhale (make_semantic_assertion_untyped \<Delta> (tcfes tys) P2);; fst r2;; Exhale (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2))) } \<union> snd r1 \<union> snd r2)"

| "translate \<Delta> tys (Cwhile b I C) = (Exhale (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) I));;
  ConcreteSemantics.havoc_list (wrL C);; Inhale ((make_semantic_assertion_untyped \<Delta> (tcfes tys) I) \<inter> assertify_bexp (Bnot b)),
  { Inhale ((make_semantic_assertion_untyped \<Delta> (tcfes tys) I) \<inter> assertify_bexp b);; fst (translate \<Delta> tys C);; Exhale (inhalify \<Delta> tys (make_semantic_assertion_untyped \<Delta> (tcfes tys) I)) } \<union> snd (translate \<Delta> tys C))"

(*
lemma CSL_weaken_post_atrue:
  assumes "(tcfe \<Delta> tys) \<turnstile>CSL [P] C [Q]"
  shows "(tcfe \<Delta> tys) \<turnstile>CSL [P] C [Q \<otimes> UNIV]"
  using assms(1)
proof (rule RuleCons)
  show "Q \<subseteq> Q \<otimes> UNIV"
    using add_set_commm assms(2) conjunct_with_true_entails by blast
qed (simp)
*)

lemma self_framing_atrue[simp]:
  "self_framing (atrue \<Delta> tys)"
  unfolding atrue_def no_trace_def
  apply (rule self_framingI)
  apply (rule)
   apply simp
  using TypedEqui.typed_state_then_stabilize_typed apply blast
  by (metis (no_types, lifting) atrue_self_framing_and_typed get_trace_stabilize member_filter self_framing_invE self_framing_then_self_framing_inhalify)



lemma fvA_atrue[simp]:
  "fvA (tcfe \<Delta> tys) (atrue \<Delta> tys) = {}"
proof -
  have "TypedEqui.overapprox_fv (tcfe \<Delta> tys) (atrue \<Delta> tys) {}"
    apply (rule TypedEqui.overapprox_fvI)
    unfolding atrue_def no_trace_def get_trace_def
    apply simp
    using TypedEqui.typed_state_then_stabilize_typed by blast
  then show ?thesis
    by (simp add: TypedEqui.equal_on_set_def TypedEqui.free_vars_def TypedEqui.overapprox_fv_def)
qed

lemma CSL_add_atrue:
  assumes "(tcfe \<Delta> tys) \<turnstile>CSL [P] C [Q]"
      and "self_framing P"
    shows "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  by (rule RuleFrame) (simp_all add: assms)


definition proof_obligations_valid where
  "proof_obligations_valid \<Delta> tys S \<longleftrightarrow> (\<forall>Cv \<in> S. \<exists>B. ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv B)"

lemma proof_obligations_valid_union:
  "proof_obligations_valid \<Delta> tys (S1 \<union> S2) \<longleftrightarrow> proof_obligations_valid \<Delta> tys S1 \<and> proof_obligations_valid \<Delta> tys S2"
  by (meson Un_iff proof_obligations_valid_def)

definition invariant_translate where
  "invariant_translate \<Delta> tys P C Q \<longleftrightarrow>
  ((proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C)) \<and> ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q) \<longrightarrow> (tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys])"

lemma invariant_translateE:
  assumes "invariant_translate \<Delta> tys P C Q"
      and "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
      and "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q"
    shows "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  using assms(1) assms(2) assms(3) invariant_translate_def by blast


lemma invariant_translateI:
  assumes "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C)) \<Longrightarrow> ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q
    \<Longrightarrow> (tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  shows "invariant_translate \<Delta> tys P C Q"
  using assms invariant_translate_def proof_obligations_valid_def by blast

lemma invariant_translate_simpler:
  assumes "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q \<Longrightarrow> (tcfe \<Delta> tys) \<turnstile>CSL [P] C [Q]"
      and "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))"
      and "self_framing P"
    shows "invariant_translate \<Delta> tys P C Q"
proof (rule invariant_translateI)
  assume "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
     and "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C)) Q"
  then have "(tcfe \<Delta> tys) \<turnstile>CSL [P] C [Q]"
    using assms(1) by blast
  then show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
    by (simp add: CSL_add_atrue assms invariant_translateI)
qed

corollary invariant_translate_skip:
  "invariant_translate \<Delta> tys P Cskip Q"
  using RuleSkip invariant_translate_def by fastforce

corollary invariant_translate_assign:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys (Cassign x e)))"
  shows "invariant_translate \<Delta> tys P (Cassign x e) Q"
  using convert_proof_assign assms
  by (metis ConcreteSemantics.SL_proof_LocalAssign_elim invariant_translateI invariant_translate_simpler prod.collapse prod.inject translate.simps(2))


corollary invariant_translate_alloc:
  assumes "well_typed_cmd tys (Calloc r e)"
      and "wf_stmt \<Delta> tys (Calloc r e)"
      and "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys (Calloc r e)))"
    shows "invariant_translate \<Delta> tys P (Calloc r e) Q"
  using assms cmd.distinct(37) convert_proof_alloc
  by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim fst_eqD invariant_translateI invariant_translate_simpler translate.simps(3))

lemma no_trace_then_sum_no_trace:
  assumes "Some x = a \<oplus> b"
      and "no_trace a"
      and "no_trace b"
    shows "no_trace x"
  using assms
  unfolding no_trace_def
  by (simp add: state_add_iff)

lemma no_trace_then_sum_no_trace_simpler:
  assumes "Some x = a \<oplus> b"
      and "no_trace b"
    shows "no_trace x"
  using assms
  unfolding no_trace_def
  by (metis state_add_iff)

lemma no_trace_then_core:
  assumes "no_trace x"
  shows "no_trace |x|"
  using assms unfolding no_trace_def
  by (simp add: core_charact_equi(3))

lemma in_starE:
  assumes "x \<in> A \<otimes> B"
      and "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> Some x = a \<oplus> b \<Longrightarrow> P"
    shows "P"
  by (meson assms(1) assms(2) x_elem_set_product)


lemma atrue_star_same[simp]:
  "atrue \<Delta> tys \<otimes> atrue \<Delta> tys = atrue \<Delta> tys"
proof
  show "atrue \<Delta> tys \<otimes> atrue \<Delta> tys \<subseteq> atrue \<Delta> tys"
    unfolding atrue_def
    apply rule
    apply (erule in_starE)
    apply simp
    using TypedEqui.typed_sum no_trace_then_sum_no_trace stabilize_sum by blast
  show "atrue \<Delta> tys \<subseteq> atrue \<Delta> tys \<otimes> atrue \<Delta> tys"
  proof 
    fix x assume "x \<in> atrue \<Delta> tys"
    then have "|x| \<in> atrue \<Delta> tys" unfolding atrue_def
      using no_trace_then_core
      apply simp
      apply (intro conjI)
      using TypedEqui.typed_smaller core_stabilize_mono(2) max_projection_prop_pure_core mpp_smaller apply blast
      by blast
    then show "x \<in> atrue \<Delta> tys \<otimes> atrue \<Delta> tys"
      using \<open>x \<in> atrue \<Delta> tys\<close> core_is_smaller x_elem_set_product by blast
  qed
qed


lemma t_entails_univ_atrue:
  "t_entails \<Delta> tys (UNIV \<otimes> atrue \<Delta> tys) (atrue \<Delta> tys)"
  apply (rule ConcreteSemantics.entails_typedI)
  apply (erule in_starE)
  unfolding atrue_def
  apply simp
  apply (intro conjI)
  using TypedEqui.typed_state_then_stabilize_typed apply blast
  using no_trace_then_sum_no_trace_simpler by blast



(*
lemma atrue_star_univ[simp]:
  "UNIV \<otimes> atrue \<Delta> tys = atrue \<Delta> tys"
proof
  show "UNIV \<otimes> atrue \<Delta> tys \<subseteq> atrue \<Delta> tys"
    unfolding atrue_def
    apply rule
    apply (erule in_starE)
    apply simp
    using TypedEqui.typed_sum no_trace_then_sum_no_trace_simpler stabilize_sum

    by blast
  show "atrue \<Delta> tys \<subseteq> atrue \<Delta> tys \<otimes> atrue \<Delta> tys"
  proof 
    fix x assume "x \<in> atrue \<Delta> tys"
    then have "|x| \<in> atrue \<Delta> tys" unfolding atrue_def
      using no_trace_then_core
      apply simp
      apply (intro conjI)
      using TypedEqui.typed_smaller core_stabilize_mono(2) max_projection_prop_pure_core mpp_smaller apply blast
      by blast
    then show "x \<in> atrue \<Delta> tys \<otimes> atrue \<Delta> tys"
      using \<open>x \<in> atrue \<Delta> tys\<close> core_is_smaller x_elem_set_product by blast
  qed
qed
*)

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


lemma t_entails_add:
  assumes "t_entails \<Delta> tys A1 A2"
  assumes "t_entails \<Delta> tys B1 B2"
  shows "t_entails \<Delta> tys (A1 \<otimes> B1) (A2 \<otimes> B2)"
  by (smt (verit, best) ConcreteSemantics.entails_typed_def TypedEqui.typed_smaller assms(1) assms(2) greater_equiv in_set_sum is_in_set_sum singletonD x_elem_set_product)


corollary invariant_translate_free:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys (Cfree r)))"
    shows "invariant_translate \<Delta> tys P (Cfree r) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys (Cfree r))) Q"
  then have "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cfree r [(Q \<otimes> UNIV) \<otimes> atrue \<Delta> tys]"
    by (metis CSL_add_atrue ConcreteSemantics.SL_proof_Exhale_elim convert_proof_free fst_eqD translate.simps(4))
  then show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cfree r [Q \<otimes> atrue \<Delta> tys]"
    apply (rule RuleConsTyped)
     apply (simp add: ConcreteSemantics.entails_typed_refl)
    by (simp add: ConcreteSemantics.entails_typed_refl add_set_asso t_entails_add t_entails_univ_atrue)
qed

corollary invariant_translate_write:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys (Cwrite r e)))"
    shows "invariant_translate \<Delta> tys P (Cwrite r e) Q"
proof (rule invariant_translateI)
  assume asm0: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys (Cwrite r e))) Q"
  then have "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cwrite r e [(Q \<otimes> UNIV) \<otimes> atrue \<Delta> tys]"
    by (metis CSL_add_atrue ConcreteSemantics.SL_proof_Custom_elim convert_proof_write fst_eqD translate.simps(5))
  then show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cwrite r e [Q \<otimes> atrue \<Delta> tys]"
    apply (rule RuleConsTyped)
     apply (simp add: ConcreteSemantics.entails_typed_refl)
    by (simp add: ConcreteSemantics.entails_typed_refl add_set_asso t_entails_add t_entails_univ_atrue)
qed

corollary invariant_translate_read:
  assumes "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys (Cread x r)))"
    shows "invariant_translate \<Delta> tys P (Cread x r) Q"
  using convert_proof_read assms ConcreteSemantics.SL_proof_LocalAssign_elim fst_eqD invariant_translateI invariant_translate_simpler
  by (metis translate.simps(6)) (* Long *)


lemma invariant_translate_seq:
  assumes "\<And>R. invariant_translate \<Delta> tys P C1 R"
      and "\<And>R. invariant_translate \<Delta> tys R C2 Q"
    shows "invariant_translate \<Delta> tys P (Cseq C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys (Cseq C1 C2)))"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys (Cseq C1 C2))) Q"
  then obtain R where r: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys C1)) R"
      "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R (fst (translate \<Delta> tys C2)) Q"
    by (metis ConcreteSemantics.SL_proof_Seq_elim fst_eqD translate.simps(7))
  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cseq C1 C2 [Q \<otimes> atrue \<Delta> tys]"
  proof (rule RuleSeq)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C1 [R \<otimes> atrue \<Delta> tys]"
      using assms(1)[of R] r
      unfolding invariant_translate_def
      by (metis asm0(1) proof_obligations_valid_union snd_conv translate.simps(7))
    show "(tcfe \<Delta> tys) \<turnstile>CSL [R \<otimes> atrue \<Delta> tys] C2 [Q \<otimes> atrue \<Delta> tys]"
      by (metis asm0(1) assms(2) invariant_translateE proof_obligations_valid_union r(2) sndI translate.simps(7))
  qed
qed

(* Is this lemma 3? *)
lemma invariant_translate_inhale_exhale_get_proof:
  assumes "\<And>P Q. invariant_translate \<Delta> tys P C Q"
      and "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Inhale A;; fst (translate \<Delta> tys C);; Exhale B) Q"
      and "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
    shows "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [Q \<otimes> B \<otimes> atrue \<Delta> tys]"
  using assms(2)
proof (rule ConcreteSemantics.SL_proof_Seq_elim)
  fix R1 assume asm0: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (abs_stmt.Inhale A ;; fst (translate \<Delta> tys C)) R1"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R1 (abs_stmt.Exhale B) Q"
  then have "entails R1 (Q \<otimes> B)" by auto
  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [Q \<otimes> B \<otimes> atrue \<Delta> tys]"
  proof (rule ConcreteSemantics.SL_proof_Seq_elim[OF asm0(1)])
    fix R0 assume asm1: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (abs_stmt.Inhale A) R0"
          "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R0 (fst (translate \<Delta> tys C)) R1"
    then have "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (P \<otimes> inhalify \<Delta> tys A) (fst (translate \<Delta> tys C)) R1"
      by auto
    show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [Q \<otimes> B \<otimes> atrue \<Delta> tys]"
    proof (rule RuleCons)
      show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> inhalify \<Delta> tys A \<otimes> atrue \<Delta> tys] C [R1 \<otimes> atrue \<Delta> tys]"
        using \<open>ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (P \<otimes> inhalify \<Delta> tys A) (fst (translate \<Delta> tys C)) R1\<close> assms(1) assms(3) invariant_translate_def by blast
      show "R1 \<otimes> atrue \<Delta> tys \<subseteq> Q \<otimes> B \<otimes> atrue \<Delta> tys"
        by (meson \<open>entails R1 (Q \<otimes> B)\<close> add_set_mono dual_order.refl entails_def)
    qed (simp)
  qed
qed

lemma drop_conjunct_t_entails:
  "t_entails \<Delta> tys (A \<otimes> B \<otimes> atrue \<Delta> tys) (B \<otimes> atrue \<Delta> tys)"
  apply (rule ConcreteSemantics.entails_typedI)
  apply (erule in_starE)+
proof -
  fix \<omega> a b aa ba
  assume asm0: "typed (tcfe \<Delta> tys) \<omega>" "b \<in> atrue \<Delta> tys"
    "Some \<omega> = a \<oplus> b" "aa \<in> A" "ba \<in> B" "Some a = aa \<oplus> ba"
  then obtain baa where "Some baa = b \<oplus> aa"
    by (metis (no_types, opaque_lifting) asso3 commutative not_Some_eq)
  then have "Some \<omega> = ba \<oplus> baa"
    using asm0(3) asm0(6) asso1 commutative by force
  moreover have "baa \<in> atrue \<Delta> tys"
    unfolding atrue_def
    by (metis (no_types, lifting) ConcreteSemantics.entails_typed_def \<open>Some baa = b \<oplus> aa\<close> add_set_commm asm0(1) asm0(2) atrue_def calculation greater_def in_times_atrue make_context_semantic_type_ctxt t_entails_univ_atrue well_typedly_plus(2))
  ultimately show "\<omega> \<in> B \<otimes> atrue \<Delta> tys"
    using asm0(5) x_elem_set_product by blast
qed


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
  "inhalify \<Delta> tys (A \<otimes> B) = inhalify \<Delta> tys A \<otimes> inhalify \<Delta> tys B" (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix x assume "x \<in> inhalify \<Delta> tys (A \<otimes> B)"
    then obtain a b where "typed (tcfe \<Delta> tys) (stabilize x)" "a \<in> A" "b \<in> B" "Some x = a \<oplus> b"
      by (metis (no_types, opaque_lifting) comp_def member_filter x_elem_set_product)
    then have "typed (tcfe \<Delta> tys) (stabilize a) \<and> typed (tcfe \<Delta> tys) (stabilize b)"
      using TypedEqui.typed_smaller greater_def greater_equiv stabilize_mono by blast
    then show "x \<in> ?Q"
      using \<open>Some x = a \<oplus> b\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> x_elem_set_product by fastforce
  qed
  show "?Q \<subseteq> ?P"
  proof
    fix x assume "x \<in> ?Q"
    then obtain a b where "typed (tcfe \<Delta> tys) (stabilize a) \<and> typed (tcfe \<Delta> tys) (stabilize b)" "a \<in> A" "b \<in> B" "Some x = a \<oplus> b"
      by (smt (z3) comp_apply member_filter x_elem_set_product)
    then show "x \<in> ?P"
      by (smt (verit, best) TypedEqui.typed_sum comp_apply member_filter stabilize_sum x_elem_set_product)
  qed
qed


(*
lemma univ_t_entails_atrue:
  "t_entails \<Delta> tys UNIV (atrue \<Delta> tys)"
  by (simp add: ConcreteSemantics.entails_typedI TypedEqui.typed_state_then_stabilize_typed atrue_def)
*)

lemma invariant_translate_parallel:
  assumes "\<And>P Q. invariant_translate \<Delta> tys P C1 Q"
    and "\<And>P Q. invariant_translate \<Delta> tys P C2 Q"
      and "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      and "wf_stmt \<Delta> tys ({P1} C1 {Q1} || {P2} C2 {Q2})"
    shows "invariant_translate \<Delta> tys P ({P1} C1 {Q1} || {P2} C2 {Q2}) Q"
proof (rule invariant_translateI)
  let ?P1 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) P1"
  let ?P2 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) P2"
  let ?Q1 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1"
  let ?Q2 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2"

  assume asm0: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys {P1} C1 {Q1} || {P2} C2 {Q2}))"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys {P1} C1 {Q1} || {P2} C2 {Q2})) Q"
  then have r0: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C1)) \<and> proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C2))"
    using proof_obligations_valid_union
    unfolding translate.simps by (metis sndI)
  moreover obtain B1 where B1_def: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (atrue \<Delta> tys)
    (Inhale ?P1;; fst (translate \<Delta> tys C1);; Exhale (inhalify \<Delta> tys ?Q1)) B1"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover obtain B2 where B2_def: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (atrue \<Delta> tys)
  (Inhale ?P2;; fst (translate \<Delta> tys C2);; Exhale (inhalify \<Delta> tys ?Q2)) B2"
    using asm0 unfolding translate.simps proof_obligations_valid_def
    by (metis Un_iff insertCI snd_eqD)
  moreover have main: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (Exhale (inhalify \<Delta> tys (?P1 \<otimes> ?P2));;
  ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (?Q1 \<otimes> ?Q2)) Q"
    using asm0 by simp
  then obtain R0 R1 where R_defs:
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (abs_stmt.Exhale (inhalify \<Delta> tys (?P1 \<otimes> ?P2))) R0"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R0 (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2)) R1"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R1 (abs_stmt.Inhale (?Q1 \<otimes> ?Q2)) Q"
    by (meson ConcreteSemantics.SL_proof_Seq_elim)
  then have P_Q_R_rels:
    "entails P (R0 \<otimes> inhalify \<Delta> tys (?P1 \<otimes> ?P2)) \<and> Q = R1 \<otimes> inhalify \<Delta> tys (?Q1 \<otimes> ?Q2)" by auto
  moreover have r: "self_framing R0 \<and>
    self_framing R1 \<and> t_entails \<Delta> tys R0 R1 \<and> fvA (tcfe \<Delta> tys) R1 \<subseteq> fvA (tcfe \<Delta> tys) R0 - set (wrL C1 @ wrL C2)"
    using ConcreteSemantics.SL_proof_Havoc_list_elim[OF R_defs(2) assms(3)]
    using finite_context_simp by fastforce

(* R1 is the frame! *)

  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> atrue \<Delta> tys]"
  proof (rule RuleConsTyped)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [((inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys) \<otimes> (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys)) \<otimes> R1] {P1} C1 {Q1} || {P2} C2 {Q2} [((inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys) \<otimes> (inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys)) \<otimes> R1]"
    proof (rule RuleFrame)
      show "(tcfe \<Delta> tys) \<turnstile>CSL [inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys)] {P1} C1 {Q1} || {P2} C2 {Q2} [inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys)]"
      proof (rule RulePar)
        show "(tcfe \<Delta> tys) \<turnstile>CSL [inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys] C1 [inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys]"
        proof (rule RuleConsTyped)
          show "(tcfe \<Delta> tys) \<turnstile>CSL [(atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys] C1 [B1 \<otimes> inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(1) B1_def]
            using r0 by blast
          show "t_entails \<Delta> tys (inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys) ((atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys)"
            by (smt (verit) ConcreteSemantics.entails_typed_refl add_set_asso add_set_commm atrue_star_same)
          show "t_entails \<Delta> tys (B1 \<otimes> inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys)"
            by (simp add: drop_conjunct_t_entails subset_entails)
        qed
        show "(tcfe \<Delta> tys) \<turnstile>CSL [inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys] C2 [inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys]"
        proof (rule RuleConsTyped)
          show "(tcfe \<Delta> tys) \<turnstile>CSL [(atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys] C2 [B2 \<otimes> inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys]"
            using invariant_translate_inhale_exhale_get_proof[OF assms(2) B2_def]
            using r0 by blast
          show "t_entails \<Delta> tys (B2 \<otimes> inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys)"
            by (simp add: drop_conjunct_t_entails subset_entails)
          show "t_entails \<Delta> tys (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys) ((atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys)"
            by (smt (verit) ConcreteSemantics.entails_typed_refl add_set_asso add_set_commm atrue_star_same)
        qed
        show "disjoint (fvC C1 \<union> fvA (tcfe \<Delta> tys) (inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys)) (wrC C2)"
          using assms(4) by auto
        show "disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) (inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys)) (wrC C1)"
          using assms(4) by auto
        show "self_framing (inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys)"
          by (meson assms(4) self_framing_atrue self_framing_then_self_framing_inhalify typed_self_framing_star wf_stmt.simps(3))
        show "self_framing (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys)"
          by (meson assms(4) self_framing_atrue self_framing_then_self_framing_inhalify typed_self_framing_star wf_stmt.simps(3))
      qed
      show "disjoint (fvA (tcfe \<Delta> tys) R1) (wrC {P1} C1 {Q1} || {P2} C2 {Q2})"
        by (metis (mono_tags, opaque_lifting) Diff_subset_conv Orderings.order_eq_iff r bot.extremum disjoint_minus disjoint_simps(2) disjoint_simps(3) sup.order_iff wrC.simps(7) wrC.simps(8) wrL.simps(7) wrL_wrC_same)
      show "self_framing (inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys))"
        by (meson assms(4) self_framing_atrue self_framing_then_self_framing_inhalify typed_self_framing_star wf_stmt.simps(3))
      show "self_framing R1"
        using R_defs(3) by blast
    qed
    show "t_entails \<Delta> tys (P \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys) \<otimes> R1)"
    proof -
      have "t_entails \<Delta> tys (P \<otimes> atrue \<Delta> tys) ((R0 \<otimes> (inhalify \<Delta> tys ?P1 \<otimes> inhalify \<Delta> tys ?P2)) \<otimes> atrue \<Delta> tys)"
        by (metis ConcreteSemantics.entails_typed_refl P_Q_R_rels entails_def inhalify_distributes subset_entails t_entails_add)
      also have "t_entails \<Delta> tys (...) (R1 \<otimes> (inhalify \<Delta> tys (?P1 \<otimes> ?P2) \<otimes> atrue \<Delta> tys))"
        using r add_set_asso
        by (simp add: ConcreteSemantics.entails_typed_refl add_set_commm add_set_left_comm inhalify_distributes t_entails_add)
      moreover have "t_entails \<Delta> tys (...) (inhalify \<Delta> tys ?P1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?P2 \<otimes> atrue \<Delta> tys) \<otimes> R1)"
        using add_set_commm add_set_left_comm
        by (smt (verit, ccfv_threshold) ConcreteSemantics.entails_typedI atrue_star_same inhalify_distributes)
      ultimately show ?thesis
        using ConcreteSemantics.entails_typed_trans by blast
    qed
    show "t_entails \<Delta> tys (inhalify \<Delta> tys ?Q1 \<otimes> atrue \<Delta> tys \<otimes> (inhalify \<Delta> tys ?Q2 \<otimes> atrue \<Delta> tys) \<otimes> R1) (Q \<otimes> atrue \<Delta> tys)"
      by (smt (z3) ConcreteSemantics.entails_typed_def P_Q_R_rels add_set_commm add_set_left_comm atrue_star_same inhalify_distributes)
  qed
qed

(*
Maybe prove? Need to prove that assertions are wf...
lemma translation_wf:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
    shows "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))"
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
  assumes "\<And>P Q. invariant_translate \<Delta> tys P C1 Q"
      and "\<And>P Q. invariant_translate \<Delta> tys P C2 Q"
    shows "invariant_translate \<Delta> tys P (Cif b C1 C2) Q"
proof (rule invariant_translateI)
  assume asm0: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys (Cif b C1 C2)))"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys (Cif b C1 C2))) Q"

  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cif b C1 C2 [Q \<otimes> atrue \<Delta> tys]"
  proof (rule ConcreteSemantics.SL_proof_If_elim)
    show "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (abs_stmt.If (semantify_bexp b) (fst (translate \<Delta> tys C1)) (fst (translate \<Delta> tys C2))) Q"
      by (metis asm0(2) fst_eqD translate.simps(8))
    fix B1 B2 assume asm1: "Q = B1 \<union> B2" "framed_by_exp P (semantify_bexp b)"
       "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) (fst (translate \<Delta> tys C1)) B1"
       "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) (fst (translate \<Delta> tys C2)) B2"
       "self_framing P"
    show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cif b C1 C2 [Q \<otimes> atrue \<Delta> tys]"
    proof (rule RuleIf)
      show "(tcfe \<Delta> tys) \<turnstile>CSL [(P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp b] C1 [Q \<otimes> atrue \<Delta> tys]"
      proof (rule RuleCons)
        show "(tcfe \<Delta> tys) \<turnstile>CSL [(P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> atrue \<Delta> tys] C1 [B1 \<otimes> atrue \<Delta> tys]"
          by (metis asm0(1) asm1(3) assms(1) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B1 \<otimes> atrue \<Delta> tys \<subseteq> Q \<otimes> atrue \<Delta> tys"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp b \<subseteq> (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> atrue \<Delta> tys"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp b"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot b (get_store \<omega>)" "r \<in> atrue \<Delta> tys"
            by (metis (no_types, lifting) IntE assertify_bexp_def mem_Collect_eq x_elem_set_product)
          then have "|p| \<in> ConcreteSemantics.purify (semantify_bexp b)"
            unfolding ConcreteSemantics.purify_def semantify_bexp_def
            by (simp add: core_charact_equi(1) core_is_pure full_add_charact(1) pure_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.purify (semantify_bexp b)"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.purify (semantify_bexp b)) \<otimes> atrue \<Delta> tys"
            using \<open>Some \<omega> = p \<oplus> r\<close> \<open>r \<in> atrue \<Delta> tys\<close> x_elem_set_product by blast
        qed
      qed

      show "(tcfe \<Delta> tys) \<turnstile>CSL [(P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp (Bnot b)] C2 [Q \<otimes> atrue \<Delta> tys]"
      proof (rule RuleCons)
        show "(tcfe \<Delta> tys) \<turnstile>CSL [(P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) \<otimes> atrue \<Delta> tys] C2 [B2 \<otimes> atrue \<Delta> tys]"
          by (metis asm0(1) asm1(4) assms(2) invariant_translateE proof_obligations_valid_union snd_conv translate.simps(8))
        show "B2 \<otimes> atrue \<Delta> tys \<subseteq> Q \<otimes> atrue \<Delta> tys"
          by (simp add: add_set_mono asm1(1))
        show "(P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp (Bnot b) \<subseteq> P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b)) \<otimes> atrue \<Delta> tys"
        proof
          fix \<omega> assume "\<omega> \<in> (P \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp (Bnot b)"
          then obtain p r where "Some \<omega> = p \<oplus> r" "p \<in> P" "bdenot (Bnot b) (get_store \<omega>)" "r \<in> atrue \<Delta> tys"
            by (metis (no_types, lifting) IntE assertify_bexp_def mem_Collect_eq x_elem_set_product)
          then have "\<not> bdenot b (get_store |p| )"
            by (simp add: core_charact(1) full_add_charact(1))
          then have "|p| \<in> ConcreteSemantics.purify (negate (semantify_bexp b))"
            unfolding ConcreteSemantics.purify_def semantify_bexp_def negate_def
            by (simp add: core_is_pure pure_def)
          then have "p \<in> P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))"
            using \<open>p \<in> P\<close> core_is_smaller x_elem_set_product by blast
          then show "\<omega> \<in> (P \<otimes> ConcreteSemantics.purify (negate (semantify_bexp b))) \<otimes> atrue \<Delta> tys"
            using \<open>Some \<omega> = p \<oplus> r\<close> \<open>r \<in> atrue \<Delta> tys\<close> x_elem_set_product by blast
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
  "inhalify \<Delta> tys (A \<inter> B) = inhalify \<Delta> tys A \<inter> B"
  by auto

(*
lemma t_entails_add_atrue:
  assumes "t_entails \<Delta> tys A B"
  shows "t_entails \<Delta> tys A ((atrue \<Delta> tys) \<otimes> B)"
  
*)
(*
  using ConcreteSemantics.entails_typed_trans assms conjunct_with_true_t_entails t_entails_add univ_t_entails_atrue by blast
*)

lemma invariant_translate_while:
  assumes "\<And>P Q. invariant_translate \<Delta> tys P C Q"
      and "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (ConcreteSemantics.havoc_list (wrL C))"
      and "wf_stmt \<Delta> tys (Cwhile b I C)"
    shows "invariant_translate \<Delta> tys P (Cwhile b I C) Q"
proof (rule invariant_translateI)
  let ?I = "make_semantic_assertion_untyped \<Delta> (tcfes tys) I"
  assume asm0: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys (Cwhile b I C)))"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) P (fst (translate \<Delta> tys (Cwhile b I C))) Q"
  then have r1: "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
    using proof_obligations_valid_union by fastforce
  moreover obtain B where B_def: "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (atrue \<Delta> tys) (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Delta> tys C);; Exhale (inhalify \<Delta> tys ?I)) B"    
    using asm0(1) insertCI proof_obligations_valid_def proof_obligations_valid_union snd_eqD translate.simps(10)
    by (metis (no_types, lifting))
  moreover obtain R0 R1 where R_defs: "entails P (R0 \<otimes> inhalify \<Delta> tys ?I)" "Q = R1 \<otimes> inhalify \<Delta> tys (?I \<inter> assertify_bexp (Bnot b))"
    "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) R0 (ConcreteSemantics.havoc_list (wrL C)) R1"
    using asm0(2) by auto
  moreover have "t_entails \<Delta> tys R0 R1 \<and> fvA (tcfe \<Delta> tys) R1 \<subseteq> fvA (tcfe \<Delta> tys) R0 - (set (wrL C))"
    using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) finite_context_simp by blast

  (* R1 is the frame *)

  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] Cwhile b I C [Q \<otimes> atrue \<Delta> tys]"
  proof (rule RuleConsTyped)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [(inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<otimes> R1] Cwhile b I C [((inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<inter> (assertify_bexp (Bnot b))) \<otimes> R1]"
    proof (rule RuleFrame)
      show "(tcfe \<Delta> tys) \<turnstile>CSL [inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys] Cwhile b I C [(inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp (Bnot b)]"
      proof (rule RuleWhile)
        show "(tcfe \<Delta> tys) \<turnstile>CSL [(inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp b] C [inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys]"
        proof (rule RuleConsTyped)
          show "(tcfe \<Delta> tys) \<turnstile>CSL [(atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys (?I \<inter> assertify_bexp b) \<otimes> atrue \<Delta> tys] C [B \<otimes> inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys]"
            using invariant_translate_inhale_exhale_get_proof[OF _ B_def]
            using assms(1) r1 by blast
          show "t_entails \<Delta> tys (B \<otimes> inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys)"
            by (simp add: drop_conjunct_t_entails subset_entails)

          show "t_entails \<Delta> tys ((inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp b) ((atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys (?I \<inter> assertify_bexp b) \<otimes> atrue \<Delta> tys)"
            by (smt (verit) add_set_asso add_set_commm atrue_star_same inhalify_intersection intersect_and_star subset_entails)
        qed
      qed
      show "disjoint (fvA (tcfe \<Delta> tys) R1) (wrC (Cwhile b I C))"
        using \<open>ConcreteSemantics.entails_typed (tcfe \<Delta> tys) R0 R1 \<and> fvA (tcfe \<Delta> tys) R1 \<subseteq> fvA (tcfe \<Delta> tys) R0 - set (wrL C)\<close> disjoint_def wrL_wrC_same by fastforce
      show "self_framing (inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys)"
        by (meson assms(3) self_framing_atrue self_framing_then_self_framing_inhalify typed_self_framing_star wf_stmt.simps(5))
      show "self_framing R1"
        using ConcreteSemantics.SL_proof_Havoc_list_elim assms(2) calculation(5) finite_context_simp by blast
    qed
    have "t_entails \<Delta> tys P (R1 \<otimes> inhalify \<Delta> tys ?I)"
    proof -
      have "t_entails \<Delta> tys P (R0 \<otimes> inhalify \<Delta> tys ?I)"
        by (meson calculation(3) entails_def subset_entails)
      moreover have "t_entails \<Delta> tys (R0 \<otimes> inhalify \<Delta> tys ?I) (R1 \<otimes> inhalify \<Delta> tys ?I)"
        by (simp add: ConcreteSemantics.entails_typed_refl \<open>ConcreteSemantics.entails_typed (tcfe \<Delta> tys) R0 R1 \<and> fvA (tcfe \<Delta> tys) R1 \<subseteq> fvA (tcfe \<Delta> tys) R0 - set (wrL C)\<close> t_entails_add)
      ultimately show ?thesis
        using ConcreteSemantics.entails_typed_trans by blast
    qed


    then show "t_entails \<Delta> tys (P \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys \<otimes> R1)"
      by (smt (verit, ccfv_threshold) ConcreteSemantics.entails_typed_refl add_set_asso add_set_commm t_entails_add)

    show "t_entails \<Delta> tys ((inhalify \<Delta> tys ?I \<otimes> atrue \<Delta> tys) \<inter> assertify_bexp (Bnot b) \<otimes> R1) (Q \<otimes> atrue \<Delta> tys)"
      by (smt (verit, best) add_set_asso add_set_commm add_set_mono calculation(4) inhalify_intersection intersect_and_star subsetI subset_entails)

  qed
qed


lemma invariant_translate_induct:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
      and "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
    shows "invariant_translate \<Delta> tys P C Q"
  using assms
proof (induct C arbitrary: P Q)
  case (Cseq C1 C2)
  then show ?case
    by (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff fst_eqD invariant_translate_seq snd_conv translate.simps(7) well_typed_cmd.simps(2) wf_stmt.simps(1))
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  let ?P1 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) P1"
  let ?P2 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) P2"
  let ?Q1 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) Q1"
  let ?Q2 = "make_semantic_assertion_untyped \<Delta> (tcfes tys) Q2"
  show ?case
  proof (rule invariant_translate_parallel)
    show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (ConcreteSemantics.havoc_list (wrL C1 @ wrL C2))"
      using Cpar.prems(3) by simp
    show "wf_stmt \<Delta> tys {P1} C1 {Q1} || {P2} C2 {Q2}"
      using Cpar.prems(1) by blast
    fix P Q
    show "invariant_translate \<Delta> tys P C1 Q"
    proof (rule Cpar(1))
      have "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (Inhale ?P1;; fst (translate \<Delta> tys C1);; Exhale (inhalify \<Delta> tys ?Q1))"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C1))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tys C1"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Delta> tys C1"
        using Cpar.prems(1) by auto
    qed
    show "invariant_translate \<Delta> tys P C2 Q"
    proof (rule Cpar(2))
      have "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (Inhale ?P2;; fst (translate \<Delta> tys C2);; Exhale (inhalify \<Delta> tys ?Q2))"
        by (metis Cpar.prems(4) Un_iff insertCI snd_eqD translate.simps(9))
      then show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C2))"
        by force
      show "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
        by (metis Cpar.prems(4) Un_iff snd_eqD translate.simps(9))
      show "well_typed_cmd tys C2"
        using Cpar.prems(2) by auto
      show "wf_stmt \<Delta> tys C2"
        using Cpar.prems(1) by auto
    qed
  qed
next
  case (Cif b C1 C2)
  show ?case
  proof (rule invariant_translate_if)
    fix P Q
    show "invariant_translate \<Delta> tys P C1 Q"
    proof (rule Cif(1))
      show "wf_stmt \<Delta> tys C1"
        using Cif.prems(1) by auto
      show "well_typed_cmd tys C1"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C1))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C1) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed
    show "invariant_translate \<Delta> tys P C2 Q"
    proof (rule Cif(2))
      show "wf_stmt \<Delta> tys C2"
        using Cif.prems(1) by auto
      show "well_typed_cmd tys C2"
        using Cif.prems(2) by auto
      show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C2))"
        using Cif.prems(3) by fastforce
      show "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C2) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
        by (metis Cif.prems(4) Un_iff snd_eqD translate.simps(8))
    qed
  qed
next
  case (Cwhile b I C)
  let ?I = "make_semantic_assertion_untyped \<Delta> (tcfes tys) I"
  show ?case
  proof (rule invariant_translate_while)
    show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (ConcreteSemantics.havoc_list (wrL C))"
      using Cwhile.prems(3) by simp
    show "wf_stmt \<Delta> tys (Cwhile b I C)"
      using Cwhile.prems(1) by auto
    fix P Q show "invariant_translate \<Delta> tys P C Q"
    proof (rule Cwhile(1)[of P Q])
      show "wf_stmt \<Delta> tys C"
        using Cwhile.prems(1) by auto
      show "well_typed_cmd tys C"
        using Cwhile.prems(2) by auto
      have "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Delta> tys C);; Exhale (inhalify \<Delta> tys ?I))"
        using Cwhile.prems(4) by fastforce
      then show "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))" by force
      show "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
        using Cwhile.prems(4) by auto
    qed
  qed
qed (simp_all add: invariant_translate_skip invariant_translate_free invariant_translate_alloc invariant_translate_seq
      invariant_translate_write invariant_translate_read invariant_translate_assign)


lemma atrue_semi_typed:
  "ConcreteSemantics.semi_typed (tcfe \<Delta> tys) (atrue \<Delta> tys)"
  by (metis ConcreteSemantics.semi_typedI atrue_def comp_apply member_filter)

(*
lemma self_framing_atrue:
  "self_framing (atrue \<Delta> tys)"
proof (rule self_framingI)
*)

lemma t_entails_inhalify:
  "t_entails \<Delta> tys P (inhalify \<Delta> tys P)"
  by (simp add: ConcreteSemantics.entails_typed_def TypedEqui.typed_state_then_stabilize_typed)




lemma simp_get_store_core[simp]:
  "get_store |a| = get_store a"
  by (simp add: core_charact(1))


lemma denot_mono:
  assumes "a \<succeq> b"
      and "Some (VInt (edenot e (get_store b))) = Some v"
    shows "Some (VInt (edenot e (get_store a))) = Some v"
  using assms
  apply (induct e)
    apply simp_all
  apply (simp add: greater_charact)
  by (simp add: greater_charact)

lemma wf_exp_semantify[simp]:
  "wf_exp (semantify_exp x2)"
  unfolding semantify_exp_def
  apply (rule wf_expI)
   apply simp
  using denot_mono by fast

lemma typed_exp_semantify_vints[simp]:
  "TypedEqui.typed_exp vints (semantify_exp x2)"
  unfolding TypedEqui.typed_exp_def semantify_exp_def
  by (simp add: vints_def)


lemma wf_exp_semantify_heap_loc[simp]:
  "wf_exp (semantify_heap_loc r)"
  unfolding semantify_heap_loc_def
  apply (rule wf_expI)
   apply simp_all
  apply (simp add: core_charact_equi(2) core_structure(2))
  by (smt (z3) get_address_simp get_vh_Some_greater greater_cover_store option.discI option.sel some_eq_imp)


lemma semantify_heap_loc_typed[simp]:
  "TypedEqui.typed_exp vints (semantify_heap_loc r)"
  unfolding semantify_heap_loc_def TypedEqui.typed_exp_def vints_def
  apply simp
  by force

lemma simplify_if_some_none:
  assumes "(if b then Some x else None) = Some y"
  shows "b \<and> x = y"
  using assms
  by (metis option.discI option.inject)

lemma wf_exp_semantify_addr[simp]:
  "wf_exp (semantify_addr x1)"
  unfolding semantify_addr_def
  apply (rule wf_expI)
  apply simp_all
  by (metis (mono_tags, lifting) Eps_cong greater_charact_equi simplify_if_some_none)

lemma type_ctxt_field_val[simp]:
  "type_ctxt_heap field_val = Some vints"
  unfolding type_ctxt_heap_def by auto

lemma in_dom_type_ctxt_store:
  assumes "x1 < length tys"
    shows "x1 \<in> dom (type_ctxt_store \<Delta> tys)"
  using assms unfolding type_ctxt_store_def by auto

lemma wf_assertion_stabilize[simp]:
  "TypedEqui.wf_assertion (Stabilize A)"
  apply (rule TypedEqui.wf_assertionI)
  by (simp add: pure_larger_stabilize_same)

lemma wf_exp_semantify_bexp[simp]:
  "wf_exp (semantify_bexp b)"
  unfolding semantify_bexp_def
  apply (rule wf_expI)
  apply simp
  by (metis greater_charact)

lemma well_typed_cmd_all_written_vars_def:
  assumes "well_typed_cmd tys C"
  shows "set (wrL C) \<subseteq> dom (type_ctxt_store \<Delta> tys)"
  using assms
  apply (induct C)
  unfolding type_ctxt_store_def
           apply simp_all
  by force+

lemma assertion_while_or_par_wf:
  assumes "well_typed_cmd tys C1 \<and> well_typed_cmd tys C2"
    shows "set (wrL C1 @ wrL C2) \<subseteq> dom (type_ctxt_store \<Delta> tys)"
  by (simp add: assms well_typed_cmd_all_written_vars_def)

lemma self_framing_inter[simp]:
  assumes "self_framing A"
  shows "self_framing (A \<inter> assertify_bexp b)"
proof (rule self_framingI)
  fix \<omega>   
  show "(\<omega> \<in> A \<inter> assertify_bexp b) = (stabilize \<omega> \<in> A \<inter> assertify_bexp b)"
  proof -
    have "\<omega> \<in> assertify_bexp b \<longleftrightarrow> stabilize \<omega> \<in> assertify_bexp b"
      by (simp add: assertify_bexp_def)
    then show ?thesis
      using assms self_framing_def by auto
  qed
qed


lemma wf_stmt_implies_wf_translation:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
  shows "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) (fst (translate \<Delta> tys C))"
  using assms
  apply (induct C)
           apply (simp_all add: type_ctxt_front_end_def type_ctxt_store_def)  
       apply (metis typed_exp_semantify_vints vints_def)
      apply (metis semantify_heap_loc_typed vints_def)
  apply (simp add: in_dom_type_ctxt_store)
  apply (simp add: Let_def)
  apply (rule conjI)
  apply (metis self_framing_eq test_self_framing typed_self_framing_star wf_assertion_stabilize)
   apply (rule conjI)
    apply (metis ConcreteSemantics.wf_abs_stmt_havoc_list abs_type_context.select_convs(1) assertion_while_or_par_wf)
  apply (metis self_framing_eq typed_self_framing_star wf_assertion_stabilize)
   apply (rule conjI)
   apply (metis self_framing_eq test_self_framing wf_assertion_stabilize)
   apply (rule conjI)
  apply (simp add: ConcreteSemantics.wf_abs_stmt_havoc_list well_typed_cmd_all_written_vars_def)
  by (metis self_framing_eq self_framing_inter wf_assertion_stabilize)




lemma wf_stmt_implies_wf_translation_snd:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"
      and "Cv \<in> snd (translate \<Delta> tys C)"
    shows "ConcreteSemantics.wf_abs_stmt (tcfe \<Delta> tys) Cv"
  using assms
  apply (induct C)
           apply (simp_all add: type_ctxt_front_end_def type_ctxt_store_def Let_def)
     apply metis
    apply (erule disjE)
     apply simp
  apply (rule conjI)
      apply (metis self_framing_eq wf_assertion_stabilize)
     apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
    apply (erule disjE)
     apply simp
  apply (rule conjI)
      apply (metis self_framing_eq wf_assertion_stabilize)
     apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
    apply (erule disjE)
     apply blast+
    apply (erule disjE)
  apply simp
   apply (rule conjI)+
  apply (metis self_framing_eq self_framing_inter wf_assertion_stabilize)
  apply (metis self_framing_eq test_self_framing type_ctxt_front_end_def wf_assertion_stabilize wf_stmt_implies_wf_translation)
  by blast

(*
definition remove_trace :: "'a equi_state \<Rightarrow> 'a equi_state"
  where
  "remove_trace \<omega> = set_trace \<omega> Map.empty"

lemma no_trace_remove_trace[simp]:
  "no_trace (remove_trace \<omega>)"
  by (simp add: no_trace_def remove_trace_def)

lemma remove_trace_stabilize[simp]:
  "stabilize (remove_trace \<omega>) = remove_trace (stabilize \<omega>)"
  unfolding remove_trace_def
  apply rule
  apply (simp add: set_trace_def stabilize_equi_state)
  by (simp add: set_trace_def stabilize_equi_state)

lemma stable_remove_trace[simp]:
  assumes "stable \<omega>"
  shows "stable (remove_trace \<omega>)"
  by (metis already_stable assms remove_trace_stabilize stabilize_is_stable)

lemma typed_remove_trace[simp]:
  assumes "typed \<Gamma> \<omega>"
  shows "typed \<Gamma> (remove_trace \<omega>)"
  using assms unfolding TypedEqui.typed_def remove_trace_def
  apply (intro conjI)
  apply simp
  by (simp add: fst_get_abs_state snd_get_abs_state well_typed_def)

definition indep_trace_exp where
  "indep_trace_exp e \<longleftrightarrow> (\<forall>\<omega>. e \<omega> = e (remove_trace \<omega>))"

definition indep_trace_assertion where
  "indep_trace_assertion A \<longleftrightarrow> (\<forall>\<omega>. \<omega> \<in> A \<longleftrightarrow> remove_trace \<omega> \<in> A)"

lemma remove_trace_star:
  assumes "Some x = a \<oplus> b"
  shows "Some (remove_trace x) = remove_trace a \<oplus> remove_trace b"


fun no_old_stmt where
  "no_old_stmt Skip \<longleftrightarrow> True"
| "no_old_stmt (C1;; C2) \<longleftrightarrow> no_old_stmt C1 \<and> no_old_stmt C2"
| "no_old_stmt (If b C1 C2) \<longleftrightarrow> indep_trace_exp b \<and> no_old_stmt C1 \<and> no_old_stmt C2"
| "no_old_stmt (Assert A) \<longleftrightarrow> indep_trace_assertion A"
| "no_old_stmt (Assume A) \<longleftrightarrow> indep_trace_assertion A"
| "no_old_stmt (Inhale A) \<longleftrightarrow> indep_trace_assertion A"
| "no_old_stmt (Exhale A) \<longleftrightarrow> indep_trace_assertion A"
| "no_old_stmt (LocalAssign x e) \<longleftrightarrow> indep_trace_exp e"
| "no_old_stmt (Havoc x) \<longleftrightarrow> True"
| "no_old_stmt (Custom (FieldAssign r f e)) \<longleftrightarrow> indep_trace_exp e"


lemma no_label_same_red_stmt:
  assumes "no_old_stmt C"
      and "ConcreteSemantics.no_assert_assume C"
    shows "ConcreteSemantics.red_stmt \<Gamma> C \<omega> S \<Longrightarrow> (\<forall>\<omega>'. \<omega> = remove_trace \<omega>' \<longrightarrow> (\<exists>S'. ConcreteSemantics.red_stmt \<Gamma> C \<omega>' S' \<and> S = remove_trace ` S'))"
      and "ConcreteSemantics.sequential_composition \<Delta> S1 C S2 \<Longrightarrow> (\<forall>S1'. S1 = remove_trace ` S1' \<longrightarrow>
  (\<exists>S2'. ConcreteSemantics.sequential_composition \<Delta> S1' C S2' \<and> S2 = remove_trace ` S2'))"
  using assms
proof (induct rule: ConcreteSemantics.red_stmt_sequential_composition.inducts)
  case (SeqComp S \<Delta> C f S')
  then show ?case 
next
  case (RedSkip \<Delta> \<omega>)
  then show ?case 
    using ConcreteSemantics.RedSkip by blast
next
  case (RedInhale \<omega> A \<Delta>)
  then show ?case 
next
  case (RedExhale a A \<omega> \<omega>' \<Delta>)
  then show ?case 
next
  case (RedIfTrue b \<omega> \<Delta> C1 S C2)
  then show ?case 
next
  case (RedIfFalse b \<omega> \<Delta> C2 S C1)
  then show ?case 
next
  case (RedSeq \<Delta> C1 \<omega> S1 C2 S2)
  then show ?case 
next
  case (RedLocalAssign \<Delta> x ty e \<omega> v)
  then show ?case 
next
  case (RedHavoc \<Delta> x ty \<omega>)
  then show ?case 
next
  case (RedCustom \<Delta> C \<omega> S)
  then show ?case 
qed (simp_all)



lemma no_label_same_verifies:
  assumes "ConcreteSemantics.verifies_set \<Gamma> (Set.filter no_trace (atrue \<Delta> tys)) C"
  shows "ConcreteSemantics.verifies_set \<Gamma> (atrue \<Delta> tys) C"
proof (rule ConcreteSemantics.verifies_setI)
  fix \<omega>
  assume asm0: "\<omega> \<in> atrue \<Delta> tys" "sep_algebra_class.stable \<omega>" "typed \<Gamma> \<omega>"
  then have "remove_trace \<omega> \<in> atrue \<Delta> tys"
    by (metis ConcreteSemantics.entails_typed_def ConcreteSemantics.semi_typedE UNIV_I already_stable atrue_semi_typed typed_remove_trace univ_t_entails_atrue)
  then show "ConcreteSemantics.verifies \<Gamma> C \<omega>"
    by (metis ConcreteSemantics.verifies_def ConcreteSemantics.verifies_set_def asm0(2) asm0(3) assms member_filter no_label_same_red_stmt no_trace_remove_trace stable_remove_trace typed_remove_trace)
qed
*)

theorem sound_translation:
  assumes "wf_stmt \<Delta> tys C"
      and "well_typed_cmd tys C"

      and "TypedEqui.wf_assertion P \<and> TypedEqui.wf_assertion Q"
      and ver_main: "ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) (Inhale P;; fst (translate \<Delta> tys C);; Exhale Q)"
      and ver_aux: "\<And>Cv. Cv \<in> snd (translate \<Delta> tys C) \<Longrightarrow> ConcreteSemantics.verifies_set (tcfe \<Delta> tys) (atrue \<Delta> tys) Cv"

    shows "tcfe \<Delta> tys \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
proof -

  obtain B where "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (atrue \<Delta> tys) (Inhale P;; fst (translate \<Delta> tys C);; Exhale Q) B"
    by (metis ConcreteSemantics.Viper_implies_SL_proof ConcreteSemantics.semantics_axioms ConcreteSemantics.wf_abs_stmt.simps(7) assms(1) assms(2) assms(3) atrue_semi_typed self_framing_atrue semantics.wf_abs_stmt.simps(2) semantics.wf_abs_stmt.simps(3) ver_main wf_stmt_implies_wf_translation)
  then obtain B' where "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) ((atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys P) (fst (translate \<Delta> tys C)) B'" "entails B' (B \<otimes> Q)"
    by blast

  show "(tcfe \<Delta> tys) \<turnstile>CSL [P \<otimes> atrue \<Delta> tys] C [Q \<otimes> atrue \<Delta> tys]"
  proof (rule RuleConsTyped)
    show "(tcfe \<Delta> tys) \<turnstile>CSL [inhalify \<Delta> tys P \<otimes> (atrue \<Delta> tys) \<otimes> atrue \<Delta> tys] C [B' \<otimes> atrue \<Delta> tys]"
    proof (rule invariant_translateE[of _ _ "inhalify \<Delta> tys P \<otimes> (atrue \<Delta> tys)" C])
      show "ConcreteSemantics.SL_proof (tcfe \<Delta> tys) (inhalify \<Delta> tys P \<otimes> (atrue \<Delta> tys)) (fst (translate \<Delta> tys C)) B'"
        by (metis \<open>ConcreteSemantics.SL_proof (tcfe \<Delta> tys) ((atrue \<Delta> tys) \<otimes> inhalify \<Delta> tys P) (fst (translate \<Delta> tys C)) B'\<close> add_set_commm)
      show "invariant_translate \<Delta> tys (inhalify \<Delta> tys P \<otimes> (atrue \<Delta> tys)) C B'"
        using assms(1) assms(2) invariant_translate_induct wf_stmt_implies_wf_translation wf_stmt_implies_wf_translation_snd by blast
      show "proof_obligations_valid \<Delta> tys (snd (translate \<Delta> tys C))"
        unfolding proof_obligations_valid_def
        apply clarify
        using ConcreteSemantics.Viper_implies_SL_proof assms(1) assms(2) atrue_semi_typed self_framing_atrue ver_aux wf_stmt_implies_wf_translation_snd by blast
      qed
      show "t_entails \<Delta> tys (P \<otimes> atrue \<Delta> tys) (inhalify \<Delta> tys P \<otimes> (atrue \<Delta> tys) \<otimes> atrue \<Delta> tys)"
        by (simp add: ConcreteSemantics.entails_typed_refl add_set_asso t_entails_add t_entails_inhalify)
      have "t_entails \<Delta> tys (B' \<otimes> atrue \<Delta> tys) ((B \<otimes> Q) \<otimes> atrue \<Delta> tys)"
        by (meson ConcreteSemantics.entails_typed_refl \<open>entails B' (B \<otimes> Q)\<close> entails_def subset_entails t_entails_add)
      then show "t_entails \<Delta> tys (B' \<otimes> atrue \<Delta> tys) (Q \<otimes> atrue \<Delta> tys)"
        using ConcreteSemantics.entails_typed_trans drop_conjunct_t_entails by blast
  qed
qed


lemma in_starI:
  assumes "Some x = a \<oplus> b"
      and "a \<in> A"
      and "b \<in> B"
    shows "x \<in> A \<otimes> B"
  using assms(1) assms(2) assms(3) x_elem_set_product by blast

lemma get_trace_core[simp]:
  "get_trace |\<omega>| = get_trace \<omega>"
  using core_charact_equi(3) by blast

lemma get_h_order_map_le:
  fixes a b :: "'a \<rightharpoonup> 'b val"
  assumes "a \<succeq> b"
  shows "map_le b a"
  unfolding map_le_def
  apply clarify
proof -
  fix l y assume asm0: "b l = Some y"
  then have "a l = Some y"
    by (metis assms greaterE greater_def option.simps(3) option_plus_None_r val_option_sum)
  then show "b l = a l"
    using asm0 by simp
qed


lemma assertify_star_same:
  assumes "\<And>s h h'. map_le h h' \<and> P (s, h) \<Longrightarrow> P (s, h')"
  shows "t_entails \<Delta> tys (assertify_state_exp P) (assertify_state_exp P \<otimes> atrue \<Delta> tys)"
  and "t_entails \<Delta> tys (assertify_state_exp P \<otimes> atrue \<Delta> tys) (assertify_state_exp P)"
  unfolding assertify_state_exp_def
   apply (rule ConcreteSemantics.entails_typedI)
  apply (intro in_starI)
     apply simp_all
    apply (subgoal_tac "Some \<omega> = \<omega> \<oplus> |\<omega>| ")
     apply assumption
  using core_is_smaller apply blast
  unfolding atrue_def no_trace_def apply simp
   apply (intro conjI)
  using TypedEqui.typed_core TypedEqui.typed_state_then_stabilize_typed apply blast
  apply (metis agreement.sel fst_conv get_trace_def snd_conv)
   apply (rule ConcreteSemantics.entails_typedI)
  apply (erule in_starE)
  apply simp
  apply (intro exI conjI)
   apply (subgoal_tac "\<omega> = (Ag (get_store \<omega>), Ag (\<lambda>x. None), get_state \<omega>)")
    apply assumption
   apply (metis set_state_def set_state_get_state state_add_iff)
  apply (elim exE)
  apply (rule assms(1))
  apply (intro conjI)
   apply (subgoal_tac "get_vh h \<subseteq>\<^sub>m get_h \<omega>")
    apply assumption
   defer
  apply (simp add: full_add_charact(1))
proof -
  fix \<omega> :: "'a equi_state"
  fix a b s h
  assume asm0: "Some \<omega> = a \<oplus> b" "a = (Ag s, Ag (\<lambda>x. None), h) \<and> P (concretize s h)"
  then have "get_h \<omega> \<succeq> get_h a"
    by (simp add: greater_heap_rule read_helper state_add_iff)
  then have "get_h a \<subseteq>\<^sub>m get_h \<omega>"
    using get_h_order_map_le[of "get_h \<omega>"] by blast
  then show "get_vh h \<subseteq>\<^sub>m get_h \<omega>"
    by (simp add: asm0(2))
qed
                                                
definition pure_virtual_state_heap :: "'a partial_heap \<Rightarrow> 'a virtual_state" where
  "pure_virtual_state_heap h = Abs_virtual_state (zero_mask, h)"

lemma get_vh_vm_pure_virtual_state[simp]:
  "get_vh (pure_virtual_state_heap h) = h"
  "get_vm (pure_virtual_state_heap h) = zero_mask"
proof -
  have "wf_pre_virtual_state (zero_mask, h)"
    apply (rule wf_pre_virtual_stateI)
    unfolding zero_mask_def
     apply (simp add: norm_preal(1))
    unfolding wf_mask_simple_def
    using all_pos by blast
  then show "get_vh (pure_virtual_state_heap h) = h"
    by (simp add: get_wf_easy pure_virtual_state_heap_def)
  show "get_vm (pure_virtual_state_heap h) = zero_mask"
    by (simp add: \<open>wf_pre_virtual_state (zero_mask, h)\<close> get_wf_easy pure_virtual_state_heap_def)
qed

lemma pure_pure_virtual_state_heap:
  "pure (pure_virtual_state_heap h)"
  by (metis core_is_smaller core_structure(2) get_vh_vm_pure_virtual_state(2) pure_def uu_neutral uu_simps(2) vstate_add_iff)

lemma sum_ag_simp[simp]:
  "Ag s \<oplus> Ag s = Some (Ag s)"
  by (simp add: plus_AgI)


lemma wf_assertion_assertify_implies_mono:
  fixes h h' :: "'a partial_heap"

  assumes "TypedEqui.wf_assertion (assertify_state_exp P)"
      and "map_le h h'"
      and "P (s, h)"
    shows "P (s, h')"
proof -
  have r: "Some h' = h \<oplus> h'"
    apply (rule plus_funI)
    apply (case_tac "h l")
     apply simp
    apply (subgoal_tac "h' l = Some a")
     apply (simp add: plus_val_id)
    by (metis assms(2) domI map_le_def)

  have "(Ag s, Ag (\<lambda>x. None), pure_virtual_state_heap h') \<in> assertify_state_exp P"
    apply (rule TypedEqui.wf_assertionE[OF assms(1), of _ "(Ag s, Ag (\<lambda>x. None), pure_virtual_state_heap h)"])
    unfolding pure_larger_def
     apply (rule exI[of _ "(Ag s, Ag (\<lambda>x. None), pure_virtual_state_heap h')"])
     apply (intro conjI)
      apply (meson pure_def pure_pure_virtual_state_heap sum_equi_states_easy)
     apply (intro plus_prodI)
       apply simp_all
     apply (intro compatible_virtual_state_implies_pre_virtual_state_rev)
     apply (intro plus_prodI)
      apply (metis get_vh_vm_pure_virtual_state(2) get_vm_def zero_mask_identity)
    using r
     apply (metis get_vh_def get_vh_vm_pure_virtual_state(1))
    unfolding assertify_state_exp_def
    using assms(3) by force
  then show ?thesis unfolding assertify_state_exp_def
    by simp
qed

lemma assertify_star_same_wf:
  assumes "TypedEqui.wf_assertion (assertify_state_exp P)"
  shows "t_entails \<Delta> tys (assertify_state_exp P) (assertify_state_exp P \<otimes> atrue \<Delta> tys)"
  and "t_entails \<Delta> tys (assertify_state_exp P \<otimes> atrue \<Delta> tys) (assertify_state_exp P)"
  apply (metis assertify_star_same(1) assms wf_assertion_assertify_implies_mono)
  by (metis assertify_star_same(2) assms wf_assertion_assertify_implies_mono)


corollary adequacy_with_star:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "(tcfe \<Delta> tys) \<turnstile>CSL [assertify_state_exp P \<otimes> atrue \<Delta> tys] C [assertify_state_exp Q \<otimes> atrue \<Delta> tys]"
      and "P \<sigma>"
      and "well_typed_cmd tys C"
      and "TypedEqui.typed_store (tcfe \<Delta> tys) (fst \<sigma>)"
      and "heap_typed type_ctxt_heap (snd \<sigma>)"
      and "TypedEqui.wf_assertion (assertify_state_exp P) \<and> TypedEqui.wf_assertion (assertify_state_exp Q)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  apply (rule adequacy[OF assms(1) _ _ assms(4-6)])
   defer
  using assms(3) apply assumption
  apply (rule RuleConsTyped[OF assms(2)])
  apply (simp add: assertify_star_same_wf(1) assms(7))
  using assertify_star_same_wf(2) assms(7) by blast

end