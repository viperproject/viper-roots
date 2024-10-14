theory SyntacticTranslation
  imports FrontEndTranslation
begin

section \<open>Refinement Calculus\<close>

(* C1 verifies more than C2 *)
(* If C2 verifies, then C1 verifies as well *)
(* C1 is more refined *)
definition verifies_more where
  "verifies_more \<Delta> C1 C2 \<longleftrightarrow> (\<forall>\<omega> S. stable \<omega> \<and> TypedEqui.typed \<Delta> \<omega> \<and> ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S
  \<longrightarrow> (\<exists>S'. S' \<subseteq> S \<and> ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S'))"

lemma verifies_moreI:
  assumes "\<And>\<omega> S'. stable \<omega> \<Longrightarrow> TypedEqui.typed \<Delta> \<omega> \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S'
  \<Longrightarrow> (\<exists>S. S \<subseteq> S' \<and> ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S)"
  shows "verifies_more \<Delta> C1 C2"
  by (simp add: assms verifies_more_def)

lemma verifies_moreE:
  assumes "verifies_more \<Delta> C1 C2"
      and "stable \<omega>"
      and "TypedEqui.typed \<Delta> \<omega>"
      and "ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S"
    shows "\<exists>S'. S' \<subseteq> S \<and> ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S'"
  by (metis assms(1) assms(2) assms(3) assms(4) verifies_more_def)

lemma verifies_sameI:
  assumes "\<And>\<omega> S. stable \<omega> \<Longrightarrow> TypedEqui.typed \<Delta> \<omega> \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S"
  shows "verifies_more \<Delta> C1 C2"
  using assms unfolding verifies_more_def by blast

lemma elim_seq_compo:
  assumes "ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> S"
      and "\<And>S1 f. ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S1 \<Longrightarrow> S = \<Union> (f ` S1) \<Longrightarrow> (\<And>\<omega>. \<omega> \<in> S1 \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2 \<omega> (f \<omega>)) \<Longrightarrow> P"
    shows "P"
  using assms ConcreteSemantics.red_stmt_Seq_elim ConcreteSemantics.sequential_composition_elim[of \<Delta> _ C2 S]
  by blast

lemma verifies_more_seq:
  assumes "verifies_more \<Delta> C1 C1'"
      and "verifies_more \<Delta> C2 C2'"
      and "ConcreteSemantics.wf_abs_stmt \<Delta> C1' \<or> ConcreteSemantics.wf_abs_stmt \<Delta> C1"
    shows "verifies_more \<Delta> (Seq C1 C2) (Seq C1' C2')"
proof (rule verifies_moreI)
  fix \<omega> S'
  assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  assume "ConcreteSemantics.red_stmt \<Delta> (C1' ;; C2') \<omega> S'"
  then show "\<exists>S. S \<subseteq> S' \<and> ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> S"
  proof (rule elim_seq_compo)
    fix S1' f assume asm1: "ConcreteSemantics.red_stmt \<Delta> C1' \<omega> S1'" "S' = \<Union> (f ` S1')"
      "\<And>\<omega>. \<omega> \<in> S1' \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2' \<omega> (f \<omega>)"
    then obtain S1 where "ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S1" "S1 \<subseteq> S1'"
      by (meson asm0(1) asm0(2) assms(1) verifies_moreE)

    let ?f = "\<lambda>\<omega>1. (SOME S2. S2 \<subseteq> f \<omega>1 \<and> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>1 S2)"
    have r: "\<And>\<omega>1. \<omega>1 \<in> S1 \<Longrightarrow> ?f \<omega>1 \<subseteq> f \<omega>1 \<and> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>1 (?f \<omega>1)"
    proof -
      fix \<omega>1 assume "\<omega>1 \<in> S1"
      then have "TypedEqui.typed \<Delta> \<omega>1 \<and> stable \<omega>1"
        apply (cases "ConcreteSemantics.wf_abs_stmt \<Delta> C1'")
        using ConcreteSemantics.red_wf_state TypedEqui.wf_state_def \<open>S1 \<subseteq> S1'\<close> asm0(1) asm0(2) asm1(1) apply blast
        using ConcreteSemantics.red_wf_state TypedEqui.wf_state_def \<open>ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S1\<close> asm0(1) asm0(2) assms(3) by blast
      then obtain S2 where "S2 \<subseteq> f \<omega>1" "ConcreteSemantics.red_stmt \<Delta> C2 \<omega>1 S2"
        by (meson \<open>S1 \<subseteq> S1'\<close> \<open>\<omega>1 \<in> S1\<close> asm1(3) assms(2) in_mono verifies_moreE)
      then show "?f \<omega>1 \<subseteq> f \<omega>1 \<and> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>1 (?f \<omega>1)"
        by (metis (mono_tags, lifting) someI2_ex)
    qed

    let ?S = "\<Union> (?f ` S1)"
    have "?S \<subseteq> S'"
      by (simp add: SUP_subset_mono \<open>S1 \<subseteq> S1'\<close> asm1(2) r)
    moreover have "ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> ?S"
      using \<open>ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S1\<close>
    proof (rule ConcreteSemantics.RedSeq)
      show "ConcreteSemantics.sequential_composition \<Delta> S1 C2 (\<Union>\<omega>1\<in>S1. SOME S2. S2 \<subseteq> f \<omega>1 \<and> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>1 S2)"
        by (metis (no_types, lifting) ConcreteSemantics.red_stmt_sequential_composition.intros(1) r)
    qed
    ultimately show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> S"
      by meson
  qed
qed

(* everything accepted by e' is also accepted by e *)
definition exp_refined_by where
  "exp_refined_by \<Delta> e e' = (\<forall>\<omega> v. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega> \<and> e' \<omega> = Some v \<longrightarrow> e \<omega> = Some v)"

lemma exp_refined_byI:
  assumes "\<And>\<omega> v. sep_algebra_class.stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> e' \<omega> = Some v \<Longrightarrow> e \<omega> = Some v"
  shows "exp_refined_by \<Delta> e e'"
  by (simp add: assms exp_refined_by_def)

lemma exp_refined_byE:
  assumes "exp_refined_by \<Delta> e e'"
      and "sep_algebra_class.stable \<omega>"
      and "typed \<Delta> \<omega>"
      and "e' \<omega> = Some v"
    shows "e \<omega> = Some v"
  by (meson assms(1) assms(2) assms(3) assms(4) exp_refined_by_def)

lemma exp_refined_by_refl[simp]:
  "exp_refined_by \<Delta> e e"
  using exp_refined_by_def by blast


lemma verifies_more_if:
  assumes "verifies_more \<Delta> C1 C1'"
      and "verifies_more \<Delta> C2 C2'"
      and "exp_refined_by \<Delta> b b'"
    shows "verifies_more \<Delta> (If b C1 C2) (If b' C1' C2')"
proof (rule verifies_moreI)
  fix \<omega> S'
  assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  assume "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.If b' C1' C2') \<omega> S'"
  then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.If b C1 C2) \<omega> S"
  proof (rule ConcreteSemantics.red_stmt_If_elim)
    assume "b' \<omega> = Some True" "ConcreteSemantics.red_stmt \<Delta> C1' \<omega> S'"
    then obtain S where "S \<subseteq> S'" "ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S"
      by (meson asm0(1) asm0(2) assms(1) verifies_moreE)
    moreover have "b \<omega> = Some True"
      using assms(3) unfolding exp_refined_by_def
      using \<open>b' \<omega> = Some True\<close> asm0(1) asm0(2) by blast
    ultimately show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.If b C1 C2) \<omega> S"
      by (meson ConcreteSemantics.RedIfTrue)
  next
    assume "b' \<omega> = Some False" "ConcreteSemantics.red_stmt \<Delta> C2' \<omega> S'"
    then obtain S where "S \<subseteq> S'" "ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S"
      by (meson asm0(1) asm0(2) assms(2) verifies_moreE)
    moreover have "b \<omega> = Some False"
      by (meson \<open>b' \<omega> = Some False\<close> asm0(1) asm0(2) assms(3) exp_refined_by_def)
    ultimately show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.If b C1 C2) \<omega> S"
      by (meson ConcreteSemantics.RedIfFalse)
  qed
qed


(* for havoc and skip *)
lemma verifies_more_refl[simp]:
  "verifies_more \<Delta> C C"
  using verifies_sameI by blast

lemma verifies_more_trans:
  assumes "verifies_more \<Delta> C1 C2"
      and "verifies_more \<Delta> C2 C3"
    shows "verifies_more \<Delta> C1 C3"
proof (rule verifies_moreI)
  fix \<omega> S3
  assume "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>" "ConcreteSemantics.red_stmt \<Delta> C3 \<omega> S3"
  then obtain S2 where "S2 \<subseteq> S3" "ConcreteSemantics.red_stmt \<Delta> C2 \<omega> S2"
    by (meson assms(2) verifies_moreE)
  then show "\<exists>S\<subseteq>S3. ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S"
    by (meson \<open>sep_algebra_class.stable \<omega>\<close> \<open>typed \<Delta> \<omega>\<close> assms(1) dual_order.trans verifies_moreE)
qed

lemma verifies_more_local_assign:
  assumes "exp_refined_by \<Delta> e e'"
  shows "verifies_more \<Delta> (LocalAssign x e) (LocalAssign x e')"
  apply (rule verifies_moreI)
  using assms unfolding exp_refined_by_def
  by (metis ConcreteSemantics.RedLocalAssign ConcreteSemantics.red_stmt_Assign_elim equalityE)

lemma verifies_more_exhale:
  assumes "\<And>a. typed \<Delta> a \<Longrightarrow> a \<in> A' \<Longrightarrow> a \<in> A"
(* Weaker than A' \<subseteq> A *)
(* assumes "\<And>\<omega>' \<omega> a. sep_algebra_class.stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> a \<in> A' \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> sep_algebra_class.stable \<omega>' \<Longrightarrow> a \<in> A" *)
  shows "verifies_more \<Delta> (Exhale A) (Exhale A')"
proof (rule verifies_moreI)
  fix \<omega> S'
  assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  assume "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Exhale A') \<omega> S'"
  then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Exhale A) \<omega> S"
  proof (rule ConcreteSemantics.red_stmt_Exhale_elim)
    fix a \<omega>'
    assume asm1: "S' = {\<omega>'}" "a \<in> A'" "Some \<omega> = \<omega>' \<oplus> a" "sep_algebra_class.stable \<omega>'"
    then have "a \<in> A" using assms(1)
      using TypedEqui.typed_smaller asm0(2) greater_equiv by blast
    then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Exhale A) \<omega> S"
      by (metis ConcreteSemantics.semantics_axioms asm1(1) asm1(3) asm1(4) dual_order.refl semantics.RedExhale)
  qed
qed


lemma verifies_more_inhale_complex:
  assumes "\<And>\<omega>. sep_algebra_class.stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> rel_stable_assertion \<omega> A' \<Longrightarrow> rel_stable_assertion \<omega> A"
      and "\<And>\<omega>' \<omega> a. sep_algebra_class.stable \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> 
sep_algebra_class.stable \<omega>' \<Longrightarrow> typed \<Delta> \<omega>' \<Longrightarrow> (\<exists>a' \<in> A'. Some \<omega>' = \<omega> \<oplus> a')"
  shows "verifies_more \<Delta> (Inhale A) (Inhale A')"
proof (rule verifies_moreI)
  fix \<omega> S'
  assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  assume "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Inhale A') \<omega> S'"
  then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Inhale A) \<omega> S"
  proof (rule ConcreteSemantics.red_stmt_Inhale_elim)
    assume asm1: "S' = Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A')"
      "rel_stable_assertion \<omega> A'"
    then have "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Inhale A) \<omega> (Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A))"
      by (simp add: ConcreteSemantics.RedInhale asm0(1) asm0(2) assms(1))
    moreover have "Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A) \<subseteq> Set.filter (\<lambda>\<omega>. sep_algebra_class.stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A')"
      by (smt (verit, ccfv_SIG) asm0(1) assms(2) member_filter singletonD subsetI x_elem_set_product)
    ultimately show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Inhale A) \<omega> S"
      by (metis (no_types, lifting) asm1(1))
  qed
qed

lemma verifies_more_inhale:
  assumes "\<And>\<omega>. sep_algebra_class.stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> rel_stable_assertion \<omega> A' \<Longrightarrow> rel_stable_assertion \<omega> A"
      and "\<And>a. typed \<Delta> a \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> A'"
(* Weaker than A \<subseteq> A' *)
    shows "verifies_more \<Delta> (Inhale A) (Inhale A')"
proof (rule verifies_more_inhale_complex)
  show "\<And>\<omega>' \<omega> a. sep_algebra_class.stable \<omega> \<Longrightarrow> a \<in> A \<Longrightarrow> Some \<omega>' = \<omega> \<oplus> a \<Longrightarrow> sep_algebra_class.stable \<omega>' \<Longrightarrow> typed \<Delta> \<omega>' \<Longrightarrow> \<exists>a'\<in>A'. Some \<omega>' = \<omega> \<oplus> a'"
    using TypedEqui.typed_smaller assms(2) greater_equiv by blast
qed (simp add: assms(1))

lemma verifies_more_field_assign:
  assumes "exp_refined_by \<Delta> r r'"
      and "exp_refined_by \<Delta> e e'"
  shows "verifies_more \<Delta> (Custom (FieldAssign r f e)) (Custom (FieldAssign r' f e'))"
proof (rule verifies_moreI)
  fix \<omega> S'
  assume asm0: "sep_algebra_class.stable \<omega>" "typed \<Delta> \<omega>"
  assume "ConcreteSemantics.red_stmt \<Delta> (Custom (custom.FieldAssign r' f e')) \<omega> S'"
  then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (Custom (custom.FieldAssign r f e)) \<omega> S"
  proof (rule ConcreteSemantics.red_stmt_Custom_elim)
    assume "red_custom_stmt \<Delta> (custom.FieldAssign r' f e') \<omega> S'"
    then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (Custom (custom.FieldAssign r f e)) \<omega> S"
    proof (rule red_custom_stmt_FieldAssign)
      fix hl v ty
      assume asm1: "S' = {update_heap_val \<omega> (hl, f) v}" "r' \<omega> = Some hl" "e' \<omega> = Some v" "get_m \<omega> (hl, f) = 1"
        "custom_context \<Delta> f = Some ty" "v \<in> ty"
      then have "r \<omega> = Some hl \<and> e \<omega> = Some v"
        using asm0(1) asm0(2) assms(1) assms(2) exp_refined_by_def by metis
      then show "\<exists>S\<subseteq>S'. ConcreteSemantics.red_stmt \<Delta> (Custom (custom.FieldAssign r f e)) \<omega> S"
        by (metis ConcreteSemantics.RedCustom Orderings.order_eq_iff RedFieldAssign asm1(1) asm1(4) asm1(5) asm1(6))
    qed
  qed
qed









section \<open>Syntactic Translation\<close>

(* Goal: Show that if syntactic translation verifies, then the "semantic" translation also verifies *)
(* verifies_more semantic syntactic *)
(* exp_refined_by semantic syntactic *)


fun translate_binop :: "int_binop \<Rightarrow> binop" where
  "translate_binop Add = binop.Add"
| "translate_binop Sub = binop.Sub"
| "translate_binop Mult = binop.Mult"

fun translate_exp where
  "translate_exp (Evar x) = Var x"
| "translate_exp (Elit l) = ELit (LInt l)"
| "translate_exp (Ebinop e1 op e2) = Binop (translate_exp e1) (translate_binop op) (translate_exp e2)"

fun translate_bexp where
  "translate_bexp (Beq e1 e2) = Binop (translate_exp e1) Eq (translate_exp e2)"
| "translate_bexp (Band e1 e2) = Binop (translate_bexp e1) And (translate_bexp e2)"
| "translate_bexp (Bnot b) = Unop Not (translate_bexp b)"

fun typed_exp where
  "typed_exp (Elit l) \<longleftrightarrow> True"
| "typed_exp (Evar x) \<longleftrightarrow> (x < undefined \<and> x mod 2 = 0)"
| "typed_exp (Ebinop e1 op e2) \<longleftrightarrow> typed_exp e1 \<and> typed_exp e2"

fun typed_bexp where
  "typed_bexp (Beq e1 e2) \<longleftrightarrow> typed_exp e1 \<and> typed_exp e2"
| "typed_bexp (Band b1 b2) \<longleftrightarrow> typed_bexp b1 \<and> typed_bexp b2"
| "typed_bexp (Bnot b) \<longleftrightarrow> typed_bexp b"

fun typed_stmt where
  "typed_stmt Cskip \<longleftrightarrow> True"
| "typed_stmt (Cassign x e) \<longleftrightarrow> typed_exp e"
| "typed_stmt (Cseq C1 C2) \<longleftrightarrow> typed_stmt C1 \<and> typed_stmt C2"
| "typed_stmt (Cif b C1 C2) \<longleftrightarrow> typed_bexp b \<and> typed_stmt C1 \<and> typed_stmt C2"
| "typed_stmt (Calloc r e) \<longleftrightarrow> typed_exp e"
| "typed_stmt (Cwrite r e) \<longleftrightarrow> typed_exp e"
| "typed_stmt (Cfree r) \<longleftrightarrow> True"
| "typed_stmt (Cread x r) \<longleftrightarrow> True"
| "typed_stmt (Cwhile b _ C) \<longleftrightarrow> typed_bexp b \<and> typed_stmt C"
| "typed_stmt ({_} C1 {_} || {_} C2 {_}) \<longleftrightarrow> typed_stmt C1 \<and> typed_stmt C2"

lemma exp_refined_by_int:
  assumes "typed_exp e"
  shows "exp_refined_by tcfe (semantify_exp e) (make_semantic_exp \<Delta> (translate_exp e))"
proof (rule exp_refined_byI)
  fix \<omega> v assume "sep_algebra_class.stable \<omega>" "typed tcfe \<omega>"
  then have asm0: "store_typed (variables tcfe) (get_store \<omega>)"
    using TypedEqui.typed_def TypedEqui.typed_store_def by blast

  have "typed_exp e \<Longrightarrow> make_semantic_exp \<Delta> (translate_exp e) \<omega> = Some v \<Longrightarrow> semantify_exp e \<omega> = Some v"
  proof (induct e arbitrary: v)
    case (Evar x)
    then have "variables tcfe x = Some vints"
      by (simp add: type_ctxt_front_end_def type_ctxt_store_def)
    then obtain v' where "get_store \<omega> x = Some v'" "v' \<in> vints"
      using asm0 store_typed_lookup by blast
    then show ?case
      by (smt (verit) CollectD Evar.prems(2) RedVar2Val_case edenot.simps(1) make_semantic_exp_Some option.sel semantify_exp_def translate_exp.simps(1) val.sel(1) vints_def)
  next
    case (Elit x)
    then show ?case
      by (metis RedLitInt2Val_case edenot.simps(2) make_semantic_exp_Some semantify_exp_def translate_exp.simps(2) val_of_lit.simps(2))
  next
    case (Ebinop e1 op e2)
    then show ?case
      by (cases "op"; clarsimp simp add:semantify_exp_def red_pure_simps; fastforce)
  qed
  then show "make_semantic_exp \<Delta> (translate_exp e) \<omega> = Some v \<Longrightarrow> semantify_exp e \<omega> = Some v" using assms by blast
qed



lemma and_then_log_and:
  assumes "eval_binop v1 And v2 = BinopNormal (VBool True)"
  shows "\<exists>v1' v2'. v1 = VBool v1' \<and> v2 = VBool v2' \<and> v1' \<and> v2'"
  apply (cases v1; cases v2)
  using assms by auto

lemma semantify_bexp_bnot:
  assumes "make_semantic_bexp \<Delta> (Unop Not b)  \<omega> = Some v"
  shows "make_semantic_bexp \<Delta> b \<omega> = Some (\<not> v)"
proof (cases "\<Delta> \<turnstile> \<langle>Unop Not b; \<omega>\<rangle> [\<Down>] Val (VBool True)")
  case True
  then show ?thesis
    apply (rule red_pure_elim(3))
    apply (smt (z3) True assms binop_result.inject binop_result.simps(4) eval_unop.elims make_semantic_bexp_Some unop.simps(1))
    by auto
  next
    case False
    then have "\<Delta> \<turnstile> \<langle>Unop Not b; \<omega>\<rangle> [\<Down>] Val (VBool False)"
      by (metis (full_types) assms make_semantic_bexp_Some)
    then show ?thesis
    proof (rule red_pure_elim(3))
      fix va v'
      assume "Val (VBool False) = Val v'" "\<Delta> \<turnstile> \<langle>b;\<omega>\<rangle> [\<Down>] Val va" "eval_unop unop.Not va = BinopNormal v'"
      then have "v' = VBool False \<and> va = VBool True"
        using eval_unop.elims by auto
      then show "make_semantic_bexp \<Delta> b \<omega> = Some (\<not> v)"
        by (metis (full_types) False \<open>\<Delta> \<turnstile> \<langle>b;\<omega>\<rangle> [\<Down>] Val va\<close> assms make_semantic_bexp_Some)
    qed (simp)
  qed

definition syntactic_translate_addr :: "var \<Rightarrow> pure_exp" where
  "syntactic_translate_addr r = Var r"

definition syntactic_translate_heap_loc :: "var \<Rightarrow> pure_exp" where
  "syntactic_translate_heap_loc r = FieldAcc (Var r) field_val"

lemma sound_translate_addr:
  "make_semantic_rexp \<Delta> (syntactic_translate_addr r) = semantify_addr r"
proof (rule ext)
  fix \<omega> show "make_semantic_rexp \<Delta> (syntactic_translate_addr r) \<omega> = semantify_addr r \<omega>"
    unfolding make_semantic_rexp_def semantify_addr_def syntactic_translate_addr_def
    by (smt (verit) Eps_cong RedVar RedVar2Val_case)
qed

lemma sound_translate_heap_loc:
  "make_semantic_exp \<Gamma> (syntactic_translate_heap_loc r) = semantify_heap_loc r"
proof (rule ext)
  fix \<omega> show "make_semantic_exp \<Gamma> (syntactic_translate_heap_loc r) \<omega> = semantify_heap_loc r \<omega>"
    unfolding make_semantic_exp_def syntactic_translate_heap_loc_def semantify_heap_loc_def
    by (smt (verit) RedAccField2Val_case RedVar RedVar2Val_case get_address_simp option.sel red_pure_simps(6) someI_ex)
qed

lemma make_semantic_star:
  "make_semantic_assertion_untyped \<Delta> F (A && B) = make_semantic_assertion_untyped \<Delta> F A \<otimes> make_semantic_assertion_untyped \<Delta> F B"
  by (simp add: make_semantic_assertion_gen_def)





section \<open>The Translation\<close>




fun translate_syn where
  "translate_syn \<Delta> F Cskip = (stmt.Skip, {})"
| "translate_syn \<Delta> F (Cassign x e) = (stmt.LocalAssign x (translate_exp e), {})"

| "translate_syn \<Delta> F (Calloc r e) = ((stmt.Seq (stmt.Havoc r)
  (stmt.Inhale (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1)))) && Atomic (Pure (Binop (FieldAcc (Var r) field_val) Eq (translate_exp e))))), {}))"

| "translate_syn \<Delta> F (Cfree r) = (stmt.Exhale (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1))))), {})"

| "translate_syn \<Delta> F (Cwrite r e) = (stmt.FieldAssign (syntactic_translate_addr r) field_val (translate_exp e), {})"

| "translate_syn \<Delta> F (Cread x r) = (stmt.LocalAssign x (syntactic_translate_heap_loc r), {})"

| "translate_syn \<Delta> F (Cseq C1 C2) = (let r1 = translate_syn \<Delta> F C1 in let r2 = translate_syn \<Delta> F C2 in
  (stmt.Seq (fst r1) (fst r2), snd r1 \<union> snd r2))"

| "translate_syn \<Delta> F (Cif b C1 C2) =
  (stmt.If (translate_bexp b) (fst (translate_syn \<Delta> F C1)) (fst (translate_syn \<Delta> F C2)), snd (translate_syn \<Delta> F C1) \<union> snd (translate_syn \<Delta> F C2))"

| "translate_syn \<Delta> F ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  (stmt.Seq (stmt.Seq
    (stmt.Exhale (P1 && P2))
    (n_havoc (wrL C1 @ wrL C2)))
    (stmt.Inhale (Q1 && Q2)),
  let r1 = translate_syn \<Delta> F C1 in let r2 = translate_syn \<Delta> F C2 in
  { stmt.Seq (stmt.Seq (stmt.Inhale P1) (fst r1)) (stmt.Exhale Q1),
    stmt.Seq (stmt.Seq (stmt.Inhale P2) (fst r2)) (stmt.Exhale Q2)}
    \<union> snd r1 \<union> snd r2)"

| "translate_syn \<Delta> F (Cwhile b I C) =
  (stmt.Seq (stmt.Seq (stmt.Exhale I) (n_havoc (wrL C))) (stmt.Inhale (I && Atomic (Pure (Unop Not (translate_bexp b))))),
  { stmt.Seq (stmt.Seq (stmt.Inhale (I && Atomic (Pure (translate_bexp b)))) (fst (translate_syn \<Delta> F C))) (stmt.Exhale I) }
  \<union> snd (translate_syn \<Delta> F C))"




(* We want verification of the latter to imply verification of the former *)
definition verifies_more_set:
  "verifies_more_set \<Delta> S1 S2 \<longleftrightarrow> (\<forall>C1 \<in> S1. \<exists>C2 \<in> S2. verifies_more \<Delta> C1 C2)"

lemma verifies_more_setI:
  assumes "\<And>C1. C1 \<in> S1 \<Longrightarrow> (\<exists>C2 \<in> S2. verifies_more \<Delta> C1 C2)"
  shows "verifies_more_set \<Delta> S1 S2"
  by (simp add: assms verifies_more_set)

lemma rel_stable_self_framing[simp]:
  assumes "sep_algebra_class.stable \<omega>"
      and "self_framing A"
  shows "rel_stable_assertion \<omega> A"
proof (rule rel_stable_assertionI)
  fix \<omega>' a
  assume asm0: "a \<in> A" "Some \<omega>' = \<omega> \<oplus> a"
  then show "\<exists>a'\<in>A. Some (stabilize \<omega>') = \<omega> \<oplus> a'"
    by (metis already_stable assms(1) assms(2) self_framingE stabilize_sum)
qed



lemma in_starE:
  assumes "x \<in> A \<otimes> B"
      and "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> Some x = a \<oplus> b \<Longrightarrow> P"
    shows "P"
  by (meson assms(1) assms(2) x_elem_set_product)


(*
definition red_pure_assert ::  "('a, 'a virtual_state) interp \<Rightarrow> pure_exp \<Rightarrow> 'a extended_val \<Rightarrow> 'a equi_state set" ("_ \<turnstile> ((\<langle>_\<rangle>) [\<Down>] _)" [51,0,0] 81) where
"red_pure_assert \<Delta> e r = corely {\<omega>. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r}"
*)

lemma red_pure_varE:
  assumes "\<Delta> \<turnstile> \<langle>Var r; \<omega>\<rangle> [\<Down>] Val v"
      and "get_store \<omega> r = Some v \<Longrightarrow> P"
    shows "P"
  using RedVar2Val_case assms(1) assms(2) by blast


lemma red_pure_litE:
  assumes "\<Delta> \<turnstile> \<langle>ELit (LPerm p); \<omega>\<rangle> [\<Down>] Val (VPerm p')"
      and "p = p' \<Longrightarrow> P"
    shows "P"
  using assms(1)
  apply (rule red_pure_elim)
  apply (simp add: assms(2))  
  by simp

(*
"emp = {a. \<exists> b. a = stabilize |b| }"
*)
lemma plus_emp_same:
  assumes "Some \<omega> = stabilize |x| \<oplus> y"
  shows "\<omega> = y"
  by (simp add: assms commutative stabilize_core_emp)

lemma in_emp_star_something:
  assumes "x \<in> \<llangle>P\<rrangle> \<otimes> A"
  shows "P \<and> x \<in> A"
  by (metis add_set_commm add_set_empty_l assms bool_to_assertion_false bool_to_assertion_true emp_star_right_id emptyE)

lemma in_something_star_emp:
  assumes "x \<in> A \<otimes> \<llangle>P\<rrangle>"
  shows "P \<and> x \<in> A"
  by (metis add_set_commm add_set_empty_l assms bool_to_assertion_false bool_to_assertion_true emp_star_right_id emptyE)


thm acc_heap_loc_starE

lemma elim_in_acc_one:
  assumes "b \<in> acc \<Delta> xb x field_val (Some 1)"
  shows "get_m b (the_address x, field_val) = 1 \<and> (\<exists>v. x = Address v) \<and> (\<exists>v. get_state b = acc_virt (the_address x, field_val) (Abs_preal 1) v)"
  using assms unfolding acc_def
proof -
  have "b \<in> (\<Union>pp. \<llangle>Some 1 = None \<or> pp = the (Some 1)\<rrangle> \<otimes> acc_heap_loc \<Delta> xb (the_address x, field_val) pp)"
    by (smt (verit) Instantiation.acc_def Sup.SUP_cong assms bool_to_assertion_false empty_iff option.distinct(1) option.inject)
  then obtain pp where "b \<in> \<llangle>pp = the (Some 1)\<rrangle> \<otimes> acc_heap_loc \<Delta> xb (the_address x, field_val) pp"
    by force
  then have "pp = 1 \<and> b \<in> acc_heap_loc \<Delta> xb (the_address x, field_val) pp"
    using in_emp_star_something by auto
  then have "get_m b (the_address x, field_val) = 1"
    unfolding acc_heap_loc_def
    apply simp
    using one_preal.abs_eq by auto
  moreover have "\<exists>v. x = Address v"
    by (smt (verit, best) Instantiation.acc_def assms bool_to_assertion_false empty_iff option.sel ref.exhaust_sel)
  ultimately show ?thesis
    by (smt (verit, best) CollectD \<open>pp = 1 \<and> b \<in> acc_heap_loc \<Delta> xb (the_address x, field_val) pp\<close> acc_heap_loc_def)
qed


lemma sum_with_emp_simplifies:
  assumes "b \<in> emp"
      and "Some x = a \<oplus> b"
    shows "x = a"
  using assms(1) assms(2) is_in_set_sum by fastforce

lemma addition_same_store:
  assumes "Some x = a \<oplus> b"
  shows "get_store x = get_store a \<and> get_store x = get_store b"
  by (metis assms full_add_charact(1) full_add_defined)


abbreviation tcfes where
  "tcfes \<equiv> type_ctxt_front_end_syntactic"

lemma corely_false [simp] :
  "corely {} = {}"
  by (simp add: corely_def)

lemma corely_addE : 
  assumes "a \<in> corely A \<otimes> B"
  assumes "up_closed A"
  assumes "|a| \<in> A \<Longrightarrow> a \<in> up_close_core B \<Longrightarrow> P"
  shows "P"
  apply (rule assms(3))
  subgoal
    using assms apply (auto simp add:corely_def add_set_def emp_core_def)
    by (metis commutative greater_equiv max_projection_propE(3) max_projection_prop_pure_core up_closed_def)
  subgoal
    using assms apply (auto simp add:corely_def add_set_def emp_core_def)
    by (metis commutative prove_in_up_close_core)
  done

lemma up_close_core_add_r :
 "up_close_core (A \<otimes> B) = A \<otimes> up_close_core B"
  by (simp add: add_set_asso up_close_core_def)

lemma up_close_core_id [simp] :
 "up_close_core (up_close_core A) = up_close_core A"
  unfolding up_close_core_def emp_core_def apply (auto simp add:add_set_def)
   apply (smt (verit, ccfv_SIG) asso1 core_is_pure core_is_smaller core_max core_sum pure_def)
  by (metis asso1 pure_def)

lemma in_up_close_core_stabilize :
  assumes "Stable A"
  shows "a \<in> up_close_core A \<longleftrightarrow> stabilize a \<in> A"
  apply (simp add:up_close_core_def emp_core_def add_set_def)
  apply (rule iffI)
   apply (meson Stable_up_close_core SyntacticTranslation.up_close_core_id assms prove_in_up_close_core self_framing_def stabilize_in_up_close_core up_closed_core_stable_self_framing)
  using core_in_emp_core decompose_stabilize_pure emp_core_def by blast


lemma verifies_more_free:
  assumes "a \<in> make_semantic_assertion_untyped \<Delta> tcfes (Atomic (Acc (Var r) field_val (PureExp (ELit WritePerm))))"
  shows "a \<in> Stabilize (full_ownership r)"
  using assms
  apply (clarsimp simp add:full_ownership_def make_semantic_assertion_gen_def)
  apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
  apply (clarsimp simp add: red_pure_assert_def red_pure_simps)
  apply (simp add:acc_def add_set_ex_comm_r split:bool_to_assertion_splits if_splits)
  apply (simp add:add_set_asso)
  apply (erule corely_addE)
  subgoal by (clarsimp simp add: up_closed_def greater_cover_store)
  apply (simp add:up_close_core_add_r core_charact)
  apply (erule corely_addE)
  subgoal by (clarsimp simp add: up_closed_def)
  apply (simp add:the_address_def split:ref.splits)
  apply (simp add:in_up_close_core_stabilize)
  by (auto simp add:acc_heap_loc_def type_ctxt_front_end_syntactic_def)

lemma in_starI:
  assumes "Some x = a \<oplus> b"
      and "a \<in> A"
      and "b \<in> B"
    shows "x \<in> A \<otimes> B"
  using assms(1) assms(2) assms(3) x_elem_set_product by blast



lemma get_vh_stabilize_implies_normal:
  assumes "get_vh (stabilize (get_state a)) hl = Some v"
  shows "get_h a hl = Some v"
  by (simp add: assms stabilize_value_persists)



definition eval_pure_exp where
  "eval_pure_exp \<Delta> e \<omega> = (SOME v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v)"

lemma eval_pure_exp_works:
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v"
  shows "eval_pure_exp \<Delta> e \<omega> = v"
  by (simp add: assms eval_pure_exp_def red_pure_val_unique(1) some_equality)

lemma equality_edenot:
  assumes "typed_exp e"
      and "typed tcfe a"
    shows "\<Delta> \<turnstile> \<langle>translate_exp e; a\<rangle> [\<Down>] Val (VInt (edenot e (get_store a)))"
  using assms
proof (induct e)
  case (Evar x)
  then have "x < undefined \<and> x mod 2 = 0" by simp
  moreover have "store_typed (variables tcfe) (get_store a)"
    using Evar.prems(2) TypedEqui.typed_def TypedEqui.typed_store_def by blast
  ultimately obtain v where "get_store a x = Some (VInt v)"
    by (smt (verit, ccfv_threshold) abs_type_context.select_convs(1) mem_Collect_eq store_typed_lookup type_ctxt_front_end_def type_ctxt_store_def vints_def)
  then show ?case
    by (simp add: RedVar)
next
  case (Elit x)
  then show ?case using RedLit 
    by (metis edenot.simps(2) translate_exp.simps(2) val_of_lit.simps(2))
next
  case (Ebinop e1 op e2)
  then show ?case
    apply simp
    apply (rule RedBinop)
      apply blast+
    by (cases op) simp_all
qed


lemma typed_exp_then_int_value:
  assumes "typed_exp e"
      and "typed tcfe a"
    shows "\<exists>v. \<Delta> \<turnstile> \<langle>translate_exp e;a\<rangle> [\<Down>] Val (VInt v)"
  using assms(1) assms(2) equality_edenot by blast


lemma typed_exp_then_value:
  assumes "typed_exp e"
      and "typed tcfe a"
    shows "\<exists>v. \<Delta> \<turnstile> \<langle>translate_exp e;a\<rangle> [\<Down>] Val v"
  using assms(1) assms(2) typed_exp_then_int_value by blast


lemma equality_bdenot:
  assumes "typed_bexp b"
      and "typed tcfe a"
    shows "\<Delta> \<turnstile> \<langle>translate_bexp b; a\<rangle> [\<Down>] Val (VBool (bdenot b (get_store a)))"
  using assms
proof (induct b)
  case (Beq e1 e2)
  then show ?case
    apply (auto simp add:red_pure_simps)
    using equality_edenot by (metis eval_binop.simps(1) eval_int_int.simps(1))
next
  case (Band b1 b2)
  then show ?case
    apply (auto simp add:red_pure_simps) by fastforce
next
  case (Bnot b)
  then show ?case
    by (auto simp add:red_pure_simps)
qed


lemma equality_bdenot_2:
  assumes "typed_bexp b"
      and "typed tcfe a"
      and "x = (bdenot b (get_store a))" 
    shows "\<Delta> \<turnstile> \<langle>translate_bexp b; a\<rangle> [\<Down>] Val (VBool x)"
  using assms equality_bdenot by blast

lemma sum_empty_and_same:
  "Some x = stabilize |x| \<oplus> x"
  by (simp add: commutative stabilize_core_right_id)


lemma empty_satisfies_star:
  assumes "stabilize |x| \<in> A"
      and "stabilize |x| \<in> B"
    shows "stabilize |x| \<in> A \<otimes> B"
  by (simp add: assms(1) assms(2) core_is_pure in_starI stabilize_sum)

lemma simp_get_store_core[simp]:
  "get_store |a| = get_store a"
  by (simp add: core_charact(1))


lemma in_bool_to_assertion_emp:
  assumes "P"
  shows "stabilize |x| \<in> \<llangle>P\<rrangle>"
  by (metis Stabilize_up_close_core Stable_def Stable_emp_core assms bool_to_assertion_true core_in_emp_core emp_star_left_id in_Stabilize in_mono up_close_core_def)

lemma add_setI_core_l :
  assumes "|a| \<in> A"
  assumes "a \<in> B"
  shows "a \<in> A \<otimes> B"
  using add_set_commm assms(1) assms(2) core_is_smaller in_starI by blast

lemma add_setI_core_r :
  assumes "a \<in> A"
  assumes "|a| \<in> B"
  shows "a \<in> A \<otimes> B"
  using add_set_commm assms(1) assms(2) core_is_smaller in_starI by blast

lemma core_in_corely [simp] :
  "|a| \<in> corely A \<longleftrightarrow> |a| \<in> A"
  by (simp add: core_in_emp_core corely_def)

lemma verifies_more_alloc:
  assumes "typed_exp e"
      and "r \<in> dom (variables tcfe)"
      and "typed tcfe a"
      and "a \<in> Stabilize (full_ownership_with_val r e)"
    shows "a \<in> make_semantic_assertion_untyped \<Delta> tcfes (Atomic (Acc (Var r) field_val (PureExp (ELit WritePerm))) && Atomic (Pure (Binop (FieldAcc (Var r) field_val) Eq (translate_exp e))))"
  using assms
  apply (clarsimp simp add:make_semantic_assertion_gen_def full_ownership_with_val_def)
  apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
  apply (simp add:red_pure_assert_def red_pure_simps)
  apply ((rule exI)+)
  apply (simp add:add_set_asso)
  apply (rule add_setI_core_l) apply (solves \<open>simp\<close>)
  apply (rule bool_to_assertion_intro)
   apply (auto simp add:type_ctxt_front_end_syntactic_def emp_def simp del: Product_Type.split_paired_Ex)
  apply (rule add_setI_core_l) apply (auto; metis prod.collapse)
  apply (rule bool_to_assertion_intro) apply (simp)
  apply (rule in_starI[where a="stabilize a" and b="|a|"])
  using decompose_stabilize_pure apply blast
  subgoal
    apply (simp add:acc_def acc_heap_loc_def)
    apply (rule exI)
    by (rule bool_to_assertion_intro; auto)
  subgoal
    apply (simp add:core_charact_equi core_structure)
    apply (rule exI, rule conjI, rule stabilize_value_persists)
     apply (simp)
    by (rule exI, rule conjI, rule equality_edenot; simp add:TypedEqui.typed_core)
  done

lemma verifies_more_translation_while_exhale:
  assumes "typed tcfe a"
      and "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I"
    shows "a \<in> inhalify (make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I)"
  using assms unfolding make_semantic_assertion_gen_def apply simp
  using TypedEqui.typed_state_then_stabilize_typed by blast

lemma verifies_more_inter_star_pure:
  assumes "typed tcfe a"
      and "typed_bexp b"
      and "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I \<inter> assertify_bexp b"
    shows "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (translate_bexp b)))"
  using assms apply (clarsimp simp add:make_semantic_assertion_gen_def assertify_bexp_def)
  apply (rule add_setI_core_r; simp?)
  apply (simp add:red_pure_assert_def)
  by (rule equality_bdenot_2; simp add:TypedEqui.typed_core)

lemma verifies_more_translation_while_inhale:
  assumes "typed tcfe a"
      and "typed_bexp b"
      and "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I \<inter> assertify_bexp (Bnot b)"
    shows "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (Unop unop.Not (translate_bexp b))))"
  using assms verifies_more_inter_star_pure
  by (metis translate_bexp.simps(3) typed_bexp.simps(3))


lemma verifies_more_translation_parallel_exhale:
  assumes "typed tcfe a"
      and "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic (P1 && P2)"
    shows "a \<in> inhalify
               (make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic P1 \<otimes> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic P2)"
  using assms unfolding make_semantic_assertion_gen_def apply simp
  using TypedEqui.typed_state_then_stabilize_typed by blast



lemma verifies_more_translation_parallel_inhale:
  assumes "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic Q1 \<otimes> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic Q2"
    shows "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic (Q1 && Q2)"
  using assms unfolding make_semantic_assertion_gen_def by simp


lemma verifies_more_while_snd_exhale:
  assumes "typed tcfe a"
      and "typed_bexp b"
      and "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I \<inter> assertify_bexp b"
    shows "a \<in> make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (translate_bexp b)))"
  using assms verifies_more_inter_star_pure by fastforce

lemma verifies_more_while_snd_exhale_bis:
  assumes "typed tcfe a"
      and "a \<in> make_semantic_assertion_untyped \<Delta> tcfes I"
    shows "a \<in> inhalify (make_semantic_assertion_untyped \<Delta> tcfes I)"
  using assms apply simp
  using TypedEqui.typed_state_then_stabilize_typed by blast

lemma n_havoc_same:
  "ConcreteSemantics.havoc_list l = compile False \<Delta> F (n_havoc l)"
  by (induct l) simp_all

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


lemma and_binop_false_lazy:
  assumes "eval_binop_lazy v And = Some b"
  shows "v = VBool False"
  apply (cases v) using assms by auto



lemma semantify_bexp_band:
  assumes "make_semantic_bexp \<Delta> (Binop (translate_bexp b1) And (translate_bexp b2)) \<omega> = Some v"
      and "typed_bexp b1 \<and> typed_bexp b2"
      and "typed tcfe \<omega>"
  shows "\<exists>v1 v2. v = (v1 \<and> v2) \<and> make_semantic_bexp \<Delta> (translate_bexp b1) \<omega> = Some v1 \<and> make_semantic_bexp \<Delta> (translate_bexp b2) \<omega> = Some v2"
proof (cases "\<Delta> \<turnstile> \<langle>Binop (translate_bexp b1) And (translate_bexp b2); \<omega>\<rangle> [\<Down>] Val (VBool True)")
  case True
  then show ?thesis
    apply (rule red_pure_elim(4))
    apply (metis (mono_tags, opaque_lifting) eval_binop_lazy.simps(2) eval_binop_lazy.simps(39) eval_binop_lazy_some_bool extended_val.inject option.inject option.simps(3))
    apply (metis (full_types) True and_then_log_and assms(1) extended_val.inject make_semantic_bexp_Some)
    by simp_all
next
  case False
  then have "(\<Delta> \<turnstile> \<langle>Binop (translate_bexp b1) And (translate_bexp b2); \<omega>\<rangle> [\<Down>] Val (VBool False))"
    by (metis (full_types) assms(1) make_semantic_bexp_Some)
  then show ?thesis
    apply (rule red_pure_elim(4))
        apply simp_all
  proof -
    fix v1 assume asm0: "\<Delta> \<turnstile> \<langle>translate_bexp b1;\<omega>\<rangle> [\<Down>] Val v1" "eval_binop_lazy v1 And = Some (VBool False)"
    then have "v1 = VBool False"
      using and_binop_false_lazy by blast
    then
    show "\<exists>v1 v2. v = (v1 \<and> v2) \<and> (\<Delta> \<turnstile> \<langle>translate_bexp b1;\<omega>\<rangle> [\<Down>] Val (VBool v1)) \<and> \<Delta> \<turnstile> \<langle>translate_bexp b2;\<omega>\<rangle> [\<Down>] Val (VBool v2)"
      by (metis False \<open>\<Delta> \<turnstile> \<langle>Binop (translate_bexp b1) And (translate_bexp b2);\<omega>\<rangle> [\<Down>] Val (VBool False)\<close> asm0(1) assms(1) assms(2) assms(3) equality_bdenot_2 make_semantic_bexp_def option.inject)
  next
    show "\<And>v1 v2.
       \<Delta> \<turnstile> \<langle>translate_bexp b1;\<omega>\<rangle> [\<Down>] Val v1 \<Longrightarrow>
       \<Delta> \<turnstile> \<langle>translate_bexp b2;\<omega>\<rangle> [\<Down>] Val v2 \<Longrightarrow>
       eval_binop v1 And v2 = BinopNormal (VBool False) \<Longrightarrow>
       \<exists>v1 v2. v = (v1 \<and> v2) \<and> (\<Delta> \<turnstile> \<langle>translate_bexp b1;\<omega>\<rangle> [\<Down>] Val (VBool v1)) \<and> \<Delta> \<turnstile> \<langle>translate_bexp b2;\<omega>\<rangle> [\<Down>] Val (VBool v2)"
      by (smt (z3) RedBinop assms(1) assms(2) assms(3) equality_bdenot_2 eval_binop.simps(3) eval_bool_bool.simps(4) make_semantic_bexp_Some)
  qed
qed

lemma vint_binop_eq:
  assumes "eval_binop v1 Eq v2 = BinopNormal (VBool v)"
  shows "v = (v1 = v2)"
  apply (cases v1; cases v2) using assms by auto


lemma semantify_bexp_beq:
  assumes "make_semantic_bexp \<Delta> (Binop (translate_exp e1) Eq (translate_exp e2)) \<omega> = Some v"
      and "typed_exp e1 \<and> typed_exp e2"
      and "typed tcfe \<omega>"

  shows "\<exists>v1 v2. v = (v1 = v2) \<and> make_semantic_exp \<Delta> (translate_exp e1) \<omega> = Some v1 \<and> make_semantic_exp \<Delta> (translate_exp e2) \<omega> = Some v2"
proof -
  obtain v1 v2 where "\<Delta> \<turnstile> \<langle>translate_exp e1; \<omega>\<rangle> [\<Down>] Val (VInt v1)" "\<Delta> \<turnstile> \<langle>translate_exp e2; \<omega>\<rangle> [\<Down>] Val (VInt v2)"
    by (meson assms(2) assms(3) typed_exp_then_int_value)
  moreover have "\<Delta> \<turnstile> \<langle>Binop (translate_exp e1) Eq (translate_exp e2);\<omega>\<rangle> [\<Down>] Val (VBool v)"
    using assms(1) by force
  then show ?thesis
    apply (rule red_pure_elim)
        apply simp_all
    apply (drule vint_binop_eq)
    by blast
qed

lemma bexp_refined_by:
  assumes "typed_bexp b"
  shows "exp_refined_by tcfe (semantify_bexp b) (make_semantic_bexp \<Delta> (translate_bexp b))"
proof (rule exp_refined_byI)
  fix \<omega> v assume asm0: "sep_algebra_class.stable \<omega>" "typed tcfe \<omega>"
  have "typed_bexp b \<Longrightarrow> make_semantic_bexp \<Delta> (translate_bexp b) \<omega> = Some v \<Longrightarrow> semantify_bexp b \<omega> = Some v"
  proof (induct b arbitrary: v)
    case (Beq e1 e2)
    then obtain v1 v2 where "v = (v1 = v2)" "make_semantic_exp \<Delta> (translate_exp e1) \<omega> = Some v1"
      "make_semantic_exp \<Delta> (translate_exp e2) \<omega> = Some v2"
      by (metis asm0(2) semantify_bexp_beq translate_bexp.simps(1) typed_bexp.simps(1))
    then have "semantify_exp e1 \<omega> = Some v1 \<and> semantify_exp e2 \<omega> = Some v2"
      by (meson Beq.prems(1) asm0(1) asm0(2) exp_refined_byE exp_refined_by_int typed_bexp.simps(1))
    then show ?case
      using \<open>\<And>thesis. (\<And>v1 v2. \<lbrakk>v = (v1 = v2); make_semantic_exp \<Delta> (translate_exp e1) \<omega> = Some v1; make_semantic_exp \<Delta> (translate_exp e2) \<omega> = Some v2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>make_semantic_exp \<Delta> (translate_exp e1) \<omega> = Some v1\<close> \<open>make_semantic_exp \<Delta> (translate_exp e2) \<omega> = Some v2\<close> semantify_bexp_def semantify_exp_def by auto
  next
    case (Band b1 b2)
    then obtain v1 v2 where "v = (v1 \<and> v2)" "make_semantic_bexp \<Delta> (translate_bexp b1) \<omega> = Some v1"
      "make_semantic_bexp \<Delta> (translate_bexp b2) \<omega> = Some v2"
      by (smt (z3) asm0(2) semantify_bexp_band translate_bexp.simps(2) typed_bexp.simps(2))
    then show ?case 
      by (smt (verit) Band.hyps(1) Band.hyps(2) Band.prems(1) bdenot.simps(2) semantify_bexp_def typed_bexp.simps(2))
  next
    case (Bnot b)
    then have "make_semantic_bexp \<Delta> (translate_bexp b) \<omega> = Some (\<not> v)"
      by (metis semantify_bexp_bnot translate_bexp.simps(3))
    then show ?case
      by (metis (full_types) Bnot.hyps Bnot.prems(1) bdenot.simps(3) semantify_bexp_def typed_bexp.simps(3))
  qed
  then show "make_semantic_bexp \<Delta> (translate_bexp b) \<omega> = Some v \<Longrightarrow> semantify_bexp b \<omega> = Some v" using assms by blast
qed






lemma translation_refinement_main:
  assumes "typed_stmt C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "wf_stmt \<Delta> tcfes C"
(* TODO: Understand the type contexts of verifies_more, translate, compile, translate_syn *)
  shows "verifies_more tcfe (fst (translate \<Delta> C)) (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)))"
  using assms
proof (induct C)
  case Cskip
  then show ?case by simp
next
  case (Cassign x e)
  then show ?case
    apply simp
    apply (rule verifies_more_local_assign[of tcfe "semantify_exp e" "make_semantic_exp \<Delta> (translate_exp e)" x])
    apply (rule exp_refined_by_int[of e \<Delta>])
    by simp
next
  case (Cread x1 x2)
  then show ?case
    by (simp add: sound_translate_heap_loc)
next
  case (Cwrite r e)
  then show ?case
    apply simp
    apply (rule verifies_more_field_assign)
    apply (simp add: sound_translate_addr)
    using exp_refined_by_int by blast
next
  case (Calloc r e)
  then show ?case
    apply simp
    apply (rule verifies_more_seq)
    apply simp_all
    apply (rule verifies_more_inhale)
     apply simp
    using verifies_more_alloc by blast
next
  case (Cfree r)
  then show ?case
    apply simp
    apply (rule verifies_more_exhale)
    using verifies_more_free by blast
next
  case (Cseq C1 C2)
  then show ?case
    apply simp
  proof -
    assume asm0: "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C1)) \<Longrightarrow> verifies_more tcfe (fst (translate \<Delta> C1)) (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C1)))"
      "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C2)) \<Longrightarrow> verifies_more tcfe (fst (translate \<Delta> C2)) (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C2)))"
      "typed_stmt C1 \<and> typed_stmt C2"
    have "verifies_more tcfe (fst (translate \<Delta> C1) ;; fst (translate \<Delta> C2))
     (Seq (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C1))) (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C2))))"
      apply (rule verifies_more_seq)
      using asm0
      apply (metis ConcreteSemantics.wf_abs_stmt.simps(7) Cseq.prems(2) fst_eqD translate.simps(7))
       apply (metis ConcreteSemantics.wf_abs_stmt.simps(7) Cseq.prems(2) asm0(2) fst_eqD translate.simps(7))
      by (metis ConcreteSemantics.wf_abs_stmt.simps(7) Cseq.prems(2) fst_eqD translate.simps(7))
    then show "verifies_more tcfe (fst (let r1 = translate \<Delta> C1; r2 = translate \<Delta> C2 in (fst r1 ;; fst r2, snd r1 \<union> snd r2)))
     (compile False \<Delta> tcfes (fst (let r1 = translate_syn \<Delta> tcfes C1; r2 = translate_syn \<Delta> tcfes C2 in (stmt.Seq (fst r1) (fst r2), snd r1 \<union> snd r2))))"
      by (metis compile.simps(3) fst_eqD)
  qed
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  then show ?case
    apply simp
    apply (rule verifies_more_seq)
    apply (rule verifies_more_seq)
    apply (rule verifies_more_exhale)
    using verifies_more_translation_parallel_exhale apply blast
    apply (metis n_havoc_same verifies_more_refl)
    apply auto[1]
     apply (rule verifies_more_inhale)
      apply (rule rel_stable_self_framing)
    apply simp
      apply (rule typed_self_framing_star)
       apply simp_all
    using verifies_more_translation_parallel_inhale by blast
next
  case (Cif b C1 C2)
  then show ?case
    apply simp
    apply (rule verifies_more_if)
    apply blast
    apply meson
    using bexp_refined_by by blast
next
  case (Cwhile b I C)
  then show ?case
    apply simp
    apply (rule verifies_more_seq)
      apply (rule verifies_more_seq)
    apply (rule verifies_more_exhale)    
    using verifies_more_translation_while_exhale apply blast
       apply (metis n_havoc_same verifies_more_refl)
    using ConcreteSemantics.wf_abs_stmt.simps(3) apply blast
     apply (rule verifies_more_inhale)
      apply (rule rel_stable_self_framing)
       apply simp_all
    by (meson IntI verifies_more_translation_while_inhale)
qed


lemma simplified_snd_if[simp]:
  "snd (translate \<Delta> (Cif b C1 C2)) = snd (translate \<Delta> C1) \<union> snd (translate \<Delta> C2)"
  by simp






lemma translation_refinement_snd:
  assumes "typed_stmt C"
      and "wf_stmt \<Delta> tcfes C"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "Csem \<in> snd (translate \<Delta> C)"
    shows "\<exists>Csyn \<in> snd (translate_syn \<Delta> tcfes C). verifies_more tcfe Csem (compile False \<Delta> tcfes Csyn)"
  using assms
proof (induct C arbitrary: )
  case (Cseq C1 C2)
  show ?case
  proof (cases "Csem \<in> snd (translate \<Delta> C1)")
    case True
    have "\<exists>Csyn\<in>snd (translate_syn \<Delta> tcfes C1). verifies_more tcfe Csem (compile False \<Delta> tcfes Csyn)"
      apply (rule Cseq(1))
      using Cseq.prems(1) apply fastforce
      using Cseq.prems(2) apply force
         apply (metis Cseq.prems(3) Un_iff snd_conv translate.simps(7))
        apply (metis ConcreteSemantics.wf_abs_stmt.simps(7) Cseq.prems(4) fst_eqD translate.simps(7))
      by (auto simp add: True Cseq)
    then show ?thesis
      by (metis Un_iff snd_conv translate_syn.simps(7))
  next
    case False
    have "\<exists>Csyn\<in>snd (translate_syn \<Delta> tcfes C2). verifies_more tcfe Csem (compile False \<Delta> tcfes Csyn)"
      apply (rule Cseq(2))
      using Cseq.prems(1) apply fastforce
      using Cseq.prems(2) apply force
         apply (metis Cseq.prems(3) Un_iff snd_conv translate.simps(7))
      apply (metis ConcreteSemantics.wf_abs_stmt.simps(7) Cseq.prems(4) fst_eqD translate.simps(7))
      by (metis Cseq.prems(5) False Un_iff snd_conv translate.simps(7))
    then show ?thesis
      by (metis Un_iff snd_conv translate_syn.simps(7))
  qed
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  then show ?case
    apply (cases "Csem \<in> snd (translate \<Delta> C1)")
     apply simp
     apply (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff insertCI)
    apply (cases "Csem \<in> snd (translate \<Delta> C2)")
     apply simp
     apply (metis (no_types, lifting) ConcreteSemantics.wf_abs_stmt.simps(7) Un_iff insertCI)

  proof -

    let ?P1 = "make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic P1"
    let ?Q1 = "make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic Q1"
    let ?P2 = "make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic P2"
    let ?Q2 = "make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic Q2"

    assume asm0: "typed_stmt ({P1} C1 {Q1} || {P2} C2 {Q2})" "wf_stmt \<Delta> tcfes ({P1} C1 {Q1} || {P2} C2 {Q2})"
      "\<And>Cv. Cv \<in> snd (translate \<Delta> {P1} C1 {Q1} || {P2} C2 {Q2}) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      "Csem \<in> snd (translate \<Delta> {P1} C1 {Q1} || {P2} C2 {Q2})" "Csem \<notin> snd (translate \<Delta> C1)"
    "Csem \<notin> snd (translate \<Delta> C2)" "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> {P1} C1 {Q1} || {P2} C2 {Q2}))"


    then have "Csem = (Inhale ?P1;; fst (translate \<Delta> C1);; Exhale (inhalify ?Q1)) \<or> Csem = (Inhale ?P2;; fst (translate \<Delta> C2);; Exhale (inhalify ?Q2))"
      using asm0 translate.simps(9)[of \<Delta> P1 C1 Q1 P2 C2 Q2]
      by (simp add: Let_def)


    moreover have "verifies_more tcfe (Inhale ?P1;; fst (translate \<Delta> C1);; Exhale (inhalify ?Q1)) (compile False \<Delta> tcfes (stmt.Seq (stmt.Seq (stmt.Inhale P1) (fst (translate_syn \<Delta> tcfes C1))) (stmt.Exhale Q1)))"
      apply simp
      apply (rule verifies_more_seq)
      apply (rule verifies_more_seq)
          apply (rule verifies_more_inhale)
      using asm0(2) apply fastforce
      using assms(5) apply blast
         apply (rule translation_refinement_main)
      using asm0 apply simp_all
         apply (simp add: Let_def)
      using asm0(7)
      apply (metis ConcreteSemantics.wf_abs_stmt.simps(7))
      using asm0
      apply (meson ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(7) insertCI)
       apply (simp add: Let_def)
       apply (rule verifies_more_exhale)
       apply (simp add: TypedEqui.typed_state_then_stabilize_typed)
      by (meson ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(7) insertI1)

    moreover have "verifies_more tcfe (Inhale ?P2;; fst (translate \<Delta> C2);; Exhale (inhalify ?Q2))
    (compile False \<Delta> tcfes (stmt.Seq (stmt.Seq (stmt.Inhale P2) (fst (translate_syn \<Delta> tcfes C2))) (stmt.Exhale Q2)))"
      apply simp
      apply (rule verifies_more_seq)
      apply (rule verifies_more_seq)
          apply (rule verifies_more_inhale)
      using asm0(2) apply fastforce
      using assms(5) apply blast
         apply (rule translation_refinement_main)
      using asm0 apply simp_all
         apply (simp add: Let_def)
      using asm0(7)
      apply (metis ConcreteSemantics.wf_abs_stmt.simps(7))
      using asm0
      apply (meson ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(7) insertCI)
       apply (simp add: Let_def)
       apply (rule verifies_more_exhale)
       apply (simp add: TypedEqui.typed_state_then_stabilize_typed)
      by (meson ConcreteSemantics.wf_abs_stmt.simps(2) ConcreteSemantics.wf_abs_stmt.simps(7) insertCI)
    ultimately show "\<exists>Csyn\<in>snd (translate_syn \<Delta> tcfes {P1} C1 {Q1} || {P2} C2 {Q2}). verifies_more tcfe Csem (compile False \<Delta> tcfes Csyn)"
      unfolding translate_syn.simps Let_def
      by force
  qed
next
  case (Cif b C1 C2)
  then show ?case
    apply (cases "Csem \<in> snd (translate \<Delta> C1)")
    apply simp
    using Cif(1) Cif.prems translate_syn.simps(8)[of \<Delta> tcfes b C1 C2]
     apply blast
    apply simp
    using Cif(2) Cif.prems translate_syn.simps(8)[of \<Delta> tcfes b C1 C2]
    by blast
next
  case (Cwhile b I C)
  then show ?case
    apply (cases "Csem \<in> snd (translate \<Delta> C)")
     apply simp
     apply fastforce
  proof -
    assume asm0: "typed_stmt (Cwhile b I C)" "wf_stmt \<Delta> tcfes (Cwhile b I C)"
    "\<And>Cv. Cv \<in> snd (translate \<Delta> (Cwhile b I C)) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
    "Csem \<in> snd (translate \<Delta> (Cwhile b I C))" "Csem \<notin> snd (translate \<Delta> C)"

    let ?I = "make_semantic_assertion_untyped \<Delta> type_ctxt_front_end_syntactic I"

    have r: "Csem = Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Delta> C);; Exhale (inhalify ?I)"
      using asm0 by simp

    have "verifies_more tcfe (Inhale (?I \<inter> assertify_bexp b);; fst (translate \<Delta> C);; Exhale (inhalify ?I))
  (compile False \<Delta> tcfes (stmt.Seq (stmt.Seq (stmt.Inhale (I && Atomic (Pure (translate_bexp b)))) (fst (translate_syn \<Delta> tcfes C))) (stmt.Exhale I)))"
      apply simp
      apply (rule verifies_more_seq)
      apply (rule verifies_more_seq)
          apply (rule verifies_more_inhale)
      using asm0(2) apply auto[1]
      using verifies_more_while_snd_exhale
      using asm0(1) typed_stmt.simps(9) apply blast
         apply (rule translation_refinement_main)      
      using asm0(1) apply auto[1]
      using ConcreteSemantics.wf_abs_stmt.simps(7) assms(3) assms(5) r apply blast
      using asm0(2) apply force
      using ConcreteSemantics.wf_abs_stmt.simps(7) asm0(3) asm0(4) r apply blast
       apply (rule verifies_more_exhale)
      apply (metis verifies_more_while_snd_exhale_bis)
      using ConcreteSemantics.wf_abs_stmt.simps(7) asm0(3) asm0(4) r
      by blast
    then show "\<exists>Csyn\<in>snd (translate_syn \<Delta> tcfes (Cwhile b I C)). verifies_more tcfe Csem (compile False \<Delta> tcfes Csyn)"
      using asm0 by simp
  qed
qed (simp_all)


theorem translation_refinement_syntactic_semantic:
  assumes "typed_stmt C"
      and "wf_stmt \<Delta> tcfes C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
    shows "verifies_more tcfe (fst (translate \<Delta> C)) (compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)))"
      and "verifies_more_set tcfe (snd (translate \<Delta> C)) (compile False \<Delta> tcfes ` (snd (translate_syn \<Delta> tcfes C)))"
  using assms(1) assms(2) assms(3) translation_refinement_main apply blast
  apply (rule verifies_more_setI)
  using translation_refinement_snd[OF assms(1) assms(2) assms(4) assms(3)]
  by (metis image_eqI)


lemma verifies_more_verifies:
  assumes "verifies_more \<Delta> C C'"
      and "ConcreteSemantics.verifies \<Delta> C' \<omega>"
      and "typed \<Delta> \<omega>"
      and "stable \<omega>"
    shows "ConcreteSemantics.verifies \<Delta> C \<omega>"
  by (meson ConcreteSemantics.verifies_def assms(1) assms(2) assms(3) assms(4) verifies_moreE)


theorem sound_syntactic_translation:

(* Well formedness *)

  assumes "wf_stmt \<Delta> tcfes C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_assertion tcfe P \<and> TypedEqui.wf_assertion tcfe Q"
      and "typed_stmt C" (* TODO: Unify the two notions of typing *)

(* Verification *)
      and "ConcreteSemantics.verifies_set tcfe atrue (abs_stmt.Inhale P ;; compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)) ;; abs_stmt.Exhale Q)"
      and "\<And>Cv. Cv \<in> compile False \<Delta> tcfes ` (snd (translate_syn \<Delta> tcfes C)) \<Longrightarrow> ConcreteSemantics.verifies_set tcfe atrue Cv"

shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
  using assms(1) assms(2) assms(3) assms(4) assms(5)
proof (rule sound_translation)
  show "ConcreteSemantics.verifies_set tcfe atrue (abs_stmt.Inhale P ;; fst (translate \<Delta> C) ;; abs_stmt.Exhale Q)"
  proof (rule ConcreteSemantics.verifies_setI)
    fix \<omega> assume asm0: "\<omega> \<in> atrue" "sep_algebra_class.stable \<omega>" "typed tcfe \<omega>"
    show "ConcreteSemantics.verifies tcfe (abs_stmt.Inhale P ;; fst (translate \<Delta> C) ;; abs_stmt.Exhale Q) \<omega>"
    proof (rule verifies_more_verifies)
      show "verifies_more tcfe (abs_stmt.Inhale P ;; fst (translate \<Delta> C) ;; abs_stmt.Exhale Q)
      (abs_stmt.Inhale P ;; compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)) ;; abs_stmt.Exhale Q)"
        apply (rule verifies_more_seq)
        apply (rule verifies_more_seq)
            apply simp_all
        using translation_refinement_main
        using assms(1) assms(3) assms(6) apply blast
        apply (simp add: assms(5))
        using assms(3) assms(5) by blast

      show "ConcreteSemantics.verifies tcfe (abs_stmt.Inhale P ;; compile False \<Delta> tcfes (fst (translate_syn \<Delta> tcfes C)) ;; abs_stmt.Exhale Q) \<omega>"
        using ConcreteSemantics.verifies_set_def asm0(1) asm0(2) asm0(3) assms(7) by blast
    qed (simp_all add: asm0)
  qed
  fix Cv
  assume asm0: "Cv \<in> snd (translate \<Delta> C)"
  moreover have "verifies_more_set tcfe (snd (translate \<Delta> C)) (compile False \<Delta> tcfes ` (snd (translate_syn \<Delta> tcfes C)))"
    using assms(1) assms(3) assms(4) assms(6) translation_refinement_syntactic_semantic(2) by blast
  ultimately obtain Cv' where "Cv' \<in> compile False \<Delta> tcfes ` (snd (translate_syn \<Delta> tcfes C))"
    "verifies_more tcfe Cv Cv'"
    by (meson verifies_more_set)
  then show "ConcreteSemantics.verifies_set tcfe atrue Cv"
    by (meson ConcreteSemantics.verifies_set_def assms(8) verifies_more_verifies)
qed (simp_all)


end