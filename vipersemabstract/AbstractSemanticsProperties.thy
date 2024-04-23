theory AbstractSemanticsProperties
  imports AbstractSemantics
begin

section Start

context semantics
begin

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
    by (meson \<open>has_write_perm_only r1 hl\<close> calculation semantics.frame_preserving_writing_orig semantics_axioms)
  then show "Some (set_value x hl v) = set_value a hl v \<oplus> b"    
    by (smt (verit, ccfv_threshold) \<open>Some a = r1 \<oplus> r2\<close> \<open>Some br = stabilize r2 \<oplus> b\<close> \<open>has_write_perm_only r1 hl\<close> assms(2) asso1 commutative frame_preserving_writing_orig stabilize_is_stable stabilize_sum_result_stable)
qed

lemma in_inh:
  assumes "A \<omega>"
    shows "\<omega> \<in> \<langle>A\<rangle>"
  by (simp add: assms(1) inh_def)

lemma ag_store_ext:
  assumes "\<And>x. the_ag \<sigma>1 x = the_ag \<sigma>2 x"
  shows "\<sigma>1 = \<sigma>2"
proof (rule agreement.expand)
  show "the_ag \<sigma>1 = the_ag \<sigma>2" using ext assms by blast
qed

lemma rel_stable_assertionI:
  assumes "\<And>x a. \<omega> ## a \<Longrightarrow> pure_larger x (stabilize a) \<Longrightarrow> x \<succeq> |\<omega>| \<Longrightarrow> (A a \<longleftrightarrow> A x)"
  shows "rel_stable_assertion \<omega> A"
  by (simp add: assms rel_stable_assertion_def)

lemma rel_stable_assertionE:
  assumes "rel_stable_assertion \<omega> A"
      and "\<omega> ## a"
      and "pure_larger x (stabilize a)"
      and "x \<succeq> |\<omega>|"
    shows "A a \<longleftrightarrow> A x"
  using assms rel_stable_assertion_def by blast


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

section \<open>Operational semantics\<close>

lemma equiv_compo_singleton:
  "red_stmt \<Delta> s \<omega> (b) \<longleftrightarrow> sequential_composition \<Delta> {\<omega>} s b" (is "?A \<longleftrightarrow> ?B")
proof -
  have "?B \<Longrightarrow> ?A" sorry
(*
    by (smt ccpo_Sup_singleton image_empty image_insert sequential_composition.cases singletonI)
*)
  moreover have "?A \<Longrightarrow> ?B"
  proof -
    assume ?A
    then obtain f where "f \<omega> = b"
      by simp
    show ?B
    proof (rule SeqComp)
      show "\<And>\<omega>'. \<omega>' \<in> {\<omega>} \<Longrightarrow> red_stmt \<Delta> s \<omega>' (f \<omega>')" sorry
(*
        using \<open>f \<omega> = b\<close> \<open>red_stmt \<Delta> s \<omega> (b)\<close> by blast
*)
      show "b = \<Union> (f ` {\<omega>})"
        using \<open>f \<omega> = b\<close> by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

thm local.red_stmt_sequential_composition.inducts[of \<Delta> C \<omega> S]

inductive_cases sequential_composition_elim[elim!]: "sequential_composition \<Delta> S C S'"

inductive_cases red_stmt_Seq_elim[elim!]: "red_stmt \<Delta> (Seq C1 C2) \<omega> S"
inductive_cases red_stmt_Inhale_elim[elim!]: "red_stmt \<Delta> (Inhale A) \<omega> S"
inductive_cases red_stmt_Exhale_elim[elim!]: "red_stmt \<Delta> (Exhale A) \<omega> S"
inductive_cases red_stmt_Skip_elim[elim!]: "red_stmt \<Delta> Skip \<omega> S"
inductive_cases red_stmt_Havoc_elim[elim!]: "red_stmt \<Delta> (Havoc x) \<omega> S"
inductive_cases red_stmt_Assign_elim[elim!]: "red_stmt \<Delta> (LocalAssign x e) \<omega> S"
inductive_cases red_stmt_If_elim[elim!]: "red_stmt \<Delta> (If b C1 C2) \<omega> S"
inductive_cases red_stmt_Assert_elim[elim!]: "red_stmt \<Delta> (Assert A) \<omega> S"
inductive_cases red_stmt_FieldAssign_elim[elim!]: "red_stmt \<Delta> (FieldAssign l e) \<omega> S"


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


lemma red_stmt_induct_simple [consumes 3, case_names Inhale Exhale FieldAssign Havoc LocalAssign Label]:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "P \<Delta> \<omega>"
      and "\<omega>' \<in> S"
      and "\<And>(A :: ('v, 'a) abs_state assertion) \<omega>' \<omega> \<Delta>. rel_stable_assertion \<omega> A \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> \<omega>'\<in>{\<omega>} \<otimes> \<langle>A\<rangle> \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>a (A :: ('v, 'a) abs_state assertion) \<omega> \<omega>' \<Delta>. a \<in> \<langle>A\<rangle> \<Longrightarrow> Some \<omega> = \<omega>' \<oplus> a \<Longrightarrow> stable \<omega>' \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> \<omega>'"
      and "\<And>\<Delta> r \<omega> hl e v. r \<omega> = Some hl \<Longrightarrow> e \<omega> = Some v \<Longrightarrow> has_write_perm (get_state \<omega>) hl \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_state \<omega> (set_value (get_state \<omega>) hl v))"
      and "\<And>\<Delta> x ty \<omega> v. variables \<Delta> x = Some ty \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> v \<in> ty \<Longrightarrow> P \<Delta> (set_store \<omega> ((get_store \<omega>)(x := Some v)))"
      and "\<And>\<Delta> e \<omega> v x. e \<omega> = Some v \<Longrightarrow> P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_store \<omega> ((get_store \<omega>)(x := Some v)))"
      and "\<And>\<Delta> l \<omega>. P \<Delta> \<omega> \<Longrightarrow> P \<Delta> (set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_state \<omega>))))"
  shows "P \<Delta> \<omega>'"
  using assms(1)
proof -
  have "P \<Delta> \<omega> \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')"
    using assms(1)
  proof (induct rule: red_stmt_sequential_composition.inducts(1)[of \<Delta> C \<omega> S "\<lambda>\<Delta> C \<omega> S. P \<Delta> \<omega> \<longrightarrow> (\<forall>\<omega>'\<in>S. P \<Delta> \<omega>')" "\<lambda>\<Delta> S C S'. (\<forall>\<omega>\<in>S. P \<Delta> \<omega>) \<longrightarrow> (\<forall>\<omega>\<in>S'. P \<Delta> \<omega>)"])
    case (RedInhale A \<omega> \<Delta>)
    then show ?case using assms by auto
  next
    case (RedExhale a A \<omega> \<omega>' \<Delta>)
    then show ?case using assms(5) by blast
  next
    case (RedFieldAssign r \<omega> hl e v \<Delta> ty)
    then show ?case
      using assms(6) by auto
  next
    case (RedLocalAssign \<Delta> x ty e \<omega> v)
    then show ?case
      using assms(8) by (simp)
  next
    case (RedHavoc \<Delta> x ty \<omega>)
    then show ?case
      by (auto simp add: assms(7))
  next
    case (RedLabel \<Delta> l \<omega>)
    then show ?case sorry
  qed (blast+)
  then show ?thesis
    using assms(2) assms(3) by blast
qed

lemma stable_snd:
  fixes \<omega> :: "('d agreement \<times> 'f agreement) \<times> ('e :: sep_algebra)"
  shows "stable \<omega> \<longleftrightarrow> (stable (snd \<omega>))"
  sorry
(*
  using stable_def stable_rel_prod_def stable_rel_agreement_def
  by (metis snd_conv u_prod_def)
*)

lemma red_stable:
  assumes "red_stmt \<Delta> C \<omega> S"
      and "stable \<omega>"
      and "\<omega>' \<in> S"
    shows "stable \<omega>'"
  using assms
proof (induct rule: red_stmt_induct_simple)
  case (FieldAssign \<Delta> r \<omega> hl e v)
  then show ?case sorry
next
  case (Havoc \<Delta> x ty \<omega> v)
  then show "sep_algebra_class.stable (set_store \<omega> ((get_store \<omega>)(x := Some v)))"
    apply (simp add: stable_snd)
    sorry (* TODO *)
next
  case (LocalAssign \<Delta> e \<omega> v x)
  then show ?case
    apply (simp add: stable_snd)
    sorry (* TODO *)
next
  case (Label \<Delta> l \<omega>)
  then show ?case
    apply (simp add: stable_snd)
    sorry (* TODO *)
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
  case (Inhale A \<omega>' \<omega> \<Delta>)
  then show ?case sorry
(*
    by (metis (no_types, lifting) agreement.exhaust_sel full_add_charact(1) get_store_def singletonD x_elem_set_product)
*)
next
  case (Exhale a A \<omega> \<omega>' \<Delta>)
  then show ?case sorry
(*
    by (metis agreement.expand full_add_charact(1) get_store_def)
*)
next
  case (Havoc \<Delta> x ty \<omega> v)
  show ?case
  proof (rule typed_storeI)
    show "dom (variables \<Delta>) = dom (get_store (set_store \<omega> ((get_store \<omega>)(x := Some v))))"
      using Havoc.hyps(1) Havoc.hyps(2) typed_store_def by auto
    fix x' v' ty' assume asm0: "get_store (set_store \<omega> ((get_store \<omega>)(x := Some v))) x' = Some v'" "variables \<Delta> x' = Some ty'"
    then show "v' \<in> ty'"
      by (metis Havoc.hyps(1) Havoc.hyps(2) Havoc.hyps(3) fun_upd_other fun_upd_same get_store_set_store option.inject typed_store_def)
  qed
next
  case (LocalAssign \<Delta> e \<omega> v x)
(* TODO: Force typing! *)
  then show ?case sorry
next
  case (Label \<Delta> l \<omega>)
  then show ?case sorry
next
  case (FieldAssign \<Delta> r \<omega> hl e v)
  then show ?case sorry
qed

section \<open>Assertions\<close>

subsection \<open>General concepts\<close>

(*
definition self_framing :: "('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "self_framing A \<longleftrightarrow> (\<forall>\<omega>. WdInhale A \<omega> \<and> (A \<omega> \<longleftrightarrow> A (stabilize \<omega>)))"
*)

lemma self_framingI:
  assumes "\<And>\<omega>. A \<omega> \<longleftrightarrow> A (stabilize \<omega>)"
  shows "self_framing A"
  using assms self_framing_def by blast

lemma framed_byI:
  assumes "\<And>\<omega> b x. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> stable \<omega> \<Longrightarrow> b ## \<omega> \<Longrightarrow> pure_larger x (stabilize b) \<Longrightarrow> x \<succeq> |\<omega>| \<Longrightarrow> (B b \<longleftrightarrow> B x)"
  shows "framed_by A B"
  by (simp add: assms defined_comm framed_by_def rel_stable_assertion_def)

lemma wf_expI:
  assumes "\<And>a b v. a \<succeq> b \<and> e b = Some v \<Longrightarrow> e a = Some v"
      and "\<And>a. e a = e |a|"
    shows "wf_exp e"
  using assms(1) assms(2) wf_exp_def by blast

lemma wf_exp_bisE:
  assumes "wf_exp e"
  shows "e a = e |a|"
  by (meson assms wf_exp_def)


lemma wf_expE:
  assumes "wf_exp e"
      and "a \<succeq> b"
      and "e b = Some v"
    shows "e a = Some v"
  by (meson assms(1) assms(2) assms(3) wf_exp_def)



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

lemma framed_by_expI:
  assumes "\<And>\<omega>. A \<omega> \<Longrightarrow> e \<omega> \<noteq> None"
  shows "framed_by_exp A e"
  by (simp add: assms framed_by_exp_def inh_def)

lemma framed_by_expE:
  assumes "framed_by_exp A e"
      and "\<omega> \<in> \<langle>A\<rangle>"
    shows "\<exists>v. e \<omega> = Some v"
  by (meson assms(1) assms(2) framed_by_exp_def not_Some_eq)

lemma equivI:
  assumes "\<And>\<omega>. A \<omega> \<Longrightarrow> B \<omega>"
      and "\<And>\<omega>. B \<omega> \<Longrightarrow> A \<omega>"
    shows "equiv A B"
  by (simp add: Collect_mono_iff assms(1) assms(2) inh_def local.equiv_def subset_antisym)


lemma entailsI:
  assumes "\<And>\<omega>. A \<omega> \<Longrightarrow> B \<omega>"
    shows "entails A B"
  by (simp add: Collect_mono_iff assms(1) entails_def inh_def)


lemma entails_self_framingI:
  assumes "\<And>\<omega>. stable \<omega> \<Longrightarrow> A \<omega> \<Longrightarrow> B \<omega>"
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

lemma overapprox_fvI:
  assumes "\<And>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed_store \<Delta> \<sigma>1 \<Longrightarrow> typed_store \<Delta> \<sigma>2 \<Longrightarrow> equal_on_set S \<sigma>1 \<sigma>2 \<Longrightarrow> A ((Ag \<sigma>1, \<tau>), \<gamma>) \<Longrightarrow> A ((Ag \<sigma>2, \<tau>), \<gamma>)"
  shows "overapprox_fv \<Delta> A S"
  using assms equal_on_set_symmetric overapprox_fv_def by blast

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


lemma stable_by_intersection_overapprox_fv:
  assumes "overapprox_fv \<Delta> A S1"
      and "overapprox_fv \<Delta> A S2"
    shows "overapprox_fv \<Delta> A (S1 \<inter> S2)"
proof (rule overapprox_fvI)
  fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
  assume asm0: "equal_on_set (S1 \<inter> S2) \<sigma>1 \<sigma>2" "A ((Ag \<sigma>1, \<tau>), \<gamma>)" "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2"
  then obtain \<sigma>3 where "equal_on_set S1 \<sigma>1 \<sigma>3 \<and> equal_on_set S2 \<sigma>3 \<sigma>2" "typed_store \<Delta> \<sigma>3"
    using intermediate_equal_set by blast
  then show "A ((Ag \<sigma>2, \<tau>), \<gamma>)"
    by (meson asm0(2) asm0(3) asm0(4) assms(1) assms(2) overapprox_fv_def) (* long *)
qed

lemma overapprox_fv_dom:
  "overapprox_fv \<Delta> A (dom (variables \<Delta>))"
proof (rule overapprox_fvI)
  fix \<sigma>1 \<sigma>2 \<gamma> \<tau>
  assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (dom (variables \<Delta>)) \<sigma>1 \<sigma>2" "A ((Ag \<sigma>1, \<tau>), \<gamma>)"
  have "\<sigma>1 = \<sigma>2"
  proof (rule ext)
    fix x show "\<sigma>1 x = \<sigma>2 x"
      apply (cases "x \<in> dom (variables \<Delta>)")      
      using asm0(3) equal_on_set_def apply auto[1]
      by (metis asm0(1) asm0(2) domIff typed_store_def)
  qed
  then show "A ((Ag \<sigma>2, \<tau>), \<gamma>)"
    using agreement.expand asm0(4) by blast
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

lemma domain_must_be_typable:
  assumes "variables \<Delta> x = Some {}"
  shows "free_vars \<Delta> A = {} \<and> overapprox_fv \<Delta> A {}"
  by (metis Inf_lower assms bot.extremum_uniqueI free_vars_def image_ident mem_Collect_eq no_typable_ag_store overapprox_fvI)

lemma free_vars_upper_bound:
  assumes "overapprox_fv \<Delta> A S"
  shows "free_vars \<Delta> A \<subseteq> S"
  by (simp add: Inf_lower assms free_vars_def)


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
    assume asm: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set ?S \<sigma>1 \<sigma>2" "A ((Ag \<sigma>1, \<tau>), \<gamma>)"
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
    then show "A ((Ag \<sigma>2, \<tau>), \<gamma>)"
      using agreement.expand asm(4) by auto
  qed
  then show ?thesis
    using assms free_vars_exists_finite by blast
qed

lemma finite_dom_fv_works:
  assumes "finite (dom (variables \<Delta>))"
  shows "overapprox_fv \<Delta> A (free_vars \<Delta> A)"
  using assms free_vars_exists_finite overapprox_fv_dom by auto

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
    shows "A ((s1, \<tau>), \<phi>) \<longleftrightarrow> A ((s2, \<tau>), \<phi>)"
  sorry
(*
  by (metis (full_types) option.distinct(1) plus_agreement_def u_neutral)
*)

lemma self_framing_ext:
  assumes "self_framing A"
      and "self_framing B"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> A \<omega> \<Longrightarrow> B \<omega>"
      and "\<And>\<omega>. stable \<omega> \<Longrightarrow> B \<omega> \<Longrightarrow> A \<omega>"
    shows "A = B"
  apply (rule ext)
  by (metis assms(1) assms(2) assms(3) assms(4) self_framing_def stabilize_is_stable)

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
    shows "(A && B) \<omega>"
  using assms(1) assms(2) assms(3) astar_def by blast

lemma sat_starE:
  assumes "(A && B) \<omega>"
  shows "\<exists>a b. Some \<omega> = a \<oplus> b \<and> A a \<and> B b"
  using assms(1) astar_def by blast

lemma sat_starE_ag_store:
  assumes "(A && B) \<omega>"
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
  "(A && B) \<omega> \<longleftrightarrow> (\<exists>a b. Some (get_state \<omega>) = a \<oplus> b \<and> A (fst \<omega>, a) \<and> B (fst \<omega>, b))" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis full_add_charact(2) get_state_def sat_starE_ag_store snd_conv)
  show "?B \<Longrightarrow> ?A"
    by (smt (z3) agreement.exhaust_sel fst_conv get_state_def get_store_def get_trace_def option.discI option.sel plus_state_def prod.collapse sat_starI snd_conv)
qed

lemma astar_inh:
  "\<langle>A && B\<rangle> = \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
proof
  show "\<langle>A && B\<rangle> \<subseteq> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
  proof
    fix x assume "x \<in> \<langle>A && B\<rangle>"
    then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
      by (metis astar_def inh_def mem_Collect_eq)
    then show "x \<in> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
      by (meson in_inh x_elem_set_product)
  qed
  show "\<langle>A\<rangle> \<otimes> \<langle>B\<rangle> \<subseteq> \<langle>A && B\<rangle>"
  proof
    fix x assume "x \<in> \<langle>A\<rangle> \<otimes> \<langle>B\<rangle>"
    then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
      by (metis (mono_tags, lifting) inh_def mem_Collect_eq x_elem_set_product)
    then show "x \<in> \<langle>A && B\<rangle>"
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
    shows "(A \<and>\<and> B) \<omega>"
  by (simp add: aconj_def assms(1) assms(2))

lemma sat_conjE:
  assumes "(A \<and>\<and> B) \<omega>"
    shows "A \<omega> \<and> B \<omega>"
  using aconj_def assms 
  by simp

lemma astar_conj:
  "\<langle>A \<and>\<and> B\<rangle> = \<langle>A\<rangle> \<inter> \<langle>B\<rangle>"
  sorry

lemma wf_conj:
  assumes "wf_assertion A"
      and "wf_exp b"
      and "framed_by_exp A b"
    shows "wf_assertion (A \<and>\<and> (pure_assertify b))"
proof (rule wf_assertionI)
  fix x x' assume "pure_larger x' x \<and> (A \<and>\<and> pure_assertify b) x"
  then have "A x' \<and> b x = Some True"
    by (metis assms(1) pure_assertify_def sat_conjE wf_assertionE)
  then have "b x' = Some True"
    by (meson \<open>pure_larger x' x \<and> (A \<and>\<and> pure_assertify b) x\<close> assms(2) greater_equiv pure_larger_sum succ_refl wf_expE)
  then show "(A \<and>\<and> pure_assertify b) x'"
    by (simp add: \<open>A x' \<and> b x = Some True\<close> pure_assertify_def sat_conjI)
qed

lemma wf_exp_framed_by_stabilize:
  assumes "wf_exp e"
      and "framed_by_exp A e"
      and "A \<omega>"
      and "self_framing A"
    shows "e \<omega> = Some b \<longleftrightarrow> e (stabilize \<omega>) = Some b"
proof
  show "e (stabilize \<omega>) = Some b \<Longrightarrow> e \<omega> = Some b"
    by (metis (no_types, lifting) assms(1) max_projection_prop_def max_projection_prop_stable_stabilize wf_expE)
  assume "e \<omega> = Some b"
  moreover obtain v where "e (stabilize \<omega>) = Some v"
    by (metis assms(2) assms(3) assms(4) framed_by_exp_def in_inh option.collapse self_framing_def)
  ultimately show "e (stabilize \<omega>) = Some b"
    by (metis (mono_tags, lifting) assms(1) max_projection_prop_def max_projection_prop_stable_stabilize wf_expE)
qed

lemma self_framing_conj:
  assumes "wf_assertion A"
      and "wf_exp b"
      and "framed_by_exp A b"
      and "self_framing A"
    shows "self_framing (A \<and>\<and> (pure_assertify b))"
proof (rule self_framingI)
  fix \<omega> show "(A \<and>\<and> pure_assertify b) \<omega> = (A \<and>\<and> pure_assertify b) (stabilize \<omega>)"
    by (metis (no_types, lifting) aconj_def assms(2) assms(3) assms(4) pure_assertify_def self_framing_sat_stabilize wf_exp_framed_by_stabilize)
qed

lemma sat_disjI:
  shows "A \<omega> \<Longrightarrow> (A || B) \<omega>"
    and "B \<omega> \<Longrightarrow> (A || B) \<omega>"
  apply (simp add: adisj_def)
  by (simp add: adisj_def)



lemma sat_disjE:
  assumes "(A || B) \<omega>"
    shows "A \<omega> \<or> B \<omega>"
  using adisj_def assms by simp

lemma inh_disj:
  "\<langle>A || B\<rangle> = \<langle>A\<rangle> \<union> \<langle>B\<rangle>"
proof
  show "\<langle>A || B\<rangle> \<subseteq> \<langle>A\<rangle> \<union> \<langle>B\<rangle>"
    by (metis UnI1 UnI2 adisj_def inh_def mem_Collect_eq subsetI)
  show "\<langle>A\<rangle> \<union> \<langle>B\<rangle> \<subseteq> \<langle>A || B\<rangle>"
    by (smt (verit) Un_iff inh_def mem_Collect_eq sat_disjI(1) sat_disjI(2) subsetI)
qed


lemma wf_disj:
  assumes "wf_assertion A"
      and "wf_assertion B"
    shows "wf_assertion (A || B)"
proof (rule wf_assertionI)
  show "\<And>x' x. pure_larger x' x \<and> (A || B) x \<Longrightarrow> (A || B) x'"
    by (metis adisj_def assms(1) assms(2) wf_assertionE)
qed

lemma self_framing_disj:
  assumes "self_framing A"
      and "self_framing B"
    shows "self_framing (A || B)"
  using adisj_def assms(1) assms(2) self_framing_def by auto

lemma wf_star:
  assumes "wf_assertion A"
      and "wf_assertion B"
    shows "wf_assertion (A && B)"
proof (rule wf_assertionI)
  fix x' x assume asm0: "pure_larger x' x \<and> (A && B) x"
  then obtain a b where "Some x = a \<oplus> b" "A a" "B b"
    using astar_def by auto
  then obtain a' where "pure_larger a' a" "Some x' = a' \<oplus> b"
    using asm0 pure_larger_sum by blast
  moreover have "A a'"
    using \<open>A a\<close> assms(1) calculation(1) wf_assertionE by blast
  ultimately show "(A && B) x'"
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
      and "wf_assertion (A && B)"
    shows "self_framing (A && B)"
  using assms(3)
proof (rule self_framing_wfI)
  fix \<omega>
  assume asm0: "(A && B) \<omega>"
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
  ultimately show "(A && B) (stabilize \<omega>)"
    using \<open>Some (stabilize \<omega>) = stabilize a \<oplus> b'\<close> sat_starI by blast
qed


lemma framed_by_self_framing_one_direction:
  assumes "wf_assertion A"
      and "wf_assertion B"
      and "self_framing A \<and> framed_by A B"
    shows "self_framing (A && B)"
proof (rule true_necessary_condition_from_framed_by)
  show "wf_assertion (A && B)"
    using assms(1) assms(2) wf_star by blast
  show "self_framing A"
    by (simp add: assms(3))
  fix a x b assume "a ## b" "stable a" "A a" "Some x = stabilize b \<oplus> |a|"
  then show "B b = B x"
    using framed_by_def[of A B] inh_def[of A] rel_stable_assertionE[of a B b x]
    by (metis (mono_tags, lifting) assms(3) greater_equiv in_inh max_projection_prop_def max_projection_prop_pure_core pure_larger_def)
qed

(*
lemma wf_assertion_assertify:
  "wf_assertion (assertify S)"
proof (rule wf_assertionI)
  fix x' x
  assume "pure_larger x' x \<and> (assertify S) x"
  then have "stabilize x \<in> S"
    by (simp add: assertify_def)
  moreover have "stabilize x' = stabilize x"
    using \<open>pure_larger x' x \<and> (assertify S) x\<close> pure_larger_stabilize_same by blast
  ultimately show "(assertify S) x'"
    by (simp add: assertify_def)
qed
*)

lemma assertify_self_framing:
  "self_framing (assertify S)"
proof (rule self_framingI)
  fix \<omega> show "assertify S \<omega> = assertify S (stabilize \<omega>)"
    by (simp add: already_stable assertify_def stabilize_is_stable)
qed

lemma same_assertify:
  assumes "self_framing A"
      and "S = \<langle>A\<rangle>"
    shows "A = assertify S"
  by (metis (no_types, lifting) assertify_self_framing assms(1) assms(2) mem_Collect_eq self_framing_ext self_framing_sat_stabilize assertify_def inh_def)


lemma negate_sat_equiv:
  "(pure_assertify (negate b)) \<omega> \<longleftrightarrow> b \<omega> = Some False"
  by (smt (verit, ccfv_threshold) negate_def option.distinct(1) option.exhaust_sel pure_assertify_def)



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
    by (metis RedFieldAssign.hyps(3) RedFieldAssign.prems(2) RedFieldAssign.prems(3) RedFieldAssign.prems(4) get_state_def plus_prodE semantics.frame_preserving_writing semantics_axioms snd_conv stable_snd)
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
      and "A ((Ag ((get_store \<omega>)(x := Some v)), Ag (get_trace \<omega>)), snd \<omega>)"
    shows "exists_assert \<Delta> x A \<omega>"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) exists_assert_def get_state_def)


section \<open>SL Proof\<close>

inductive_cases SL_proof_Skip_elim[elim!]: "\<Delta> \<turnstile> [A] Skip [B]"
inductive_cases SL_proof_Inhale_elim[elim!]: "\<Delta> \<turnstile> [A] Inhale P [B]"
inductive_cases SL_proof_Exhale_elim[elim!]: "\<Delta> \<turnstile> [A] Exhale P [B]"
inductive_cases SL_proof_Assert_elim[elim!]: "\<Delta> \<turnstile> [A] Assert P [B]"
inductive_cases SL_proof_Havoc_elim[elim!]: "\<Delta> \<turnstile> [A] Havoc x [B]"
inductive_cases SL_proof_FieldAssign_elim[elim!]: "\<Delta> \<turnstile> [A] FieldAssign r e [B]"
inductive_cases SL_proof_Seq_elim[elim!]: "\<Delta> \<turnstile> [A] Seq C1 C2 [B]"
inductive_cases SL_proof_If_elim[elim!]: "\<Delta> \<turnstile> [A] If b C1 C2 [B]"

lemma self_framing_exists_assert:
  assumes "self_framing A"
  shows "self_framing (exists_assert \<Delta> x A)"
proof (rule self_framingI)
  fix \<omega>
  show "exists_assert \<Delta> x A \<omega> = exists_assert \<Delta> x A (stabilize \<omega>)" (is "?A \<longleftrightarrow> ?B")
  proof
    show "?A \<Longrightarrow> ?B" sorry
(*
      by (smt (verit) agreement.exhaust_sel assertify_def assms exists_assert_def fst_conv full_add_charact(1) get_state_def get_trace_def pure_larger_stabilize pure_larger_stabilize_same same_assertify snd_conv stabilize_def stabilize_prod_def stabilize_rel_sum_pure)
*)
    assume asm0: ?B
    then obtain v0 v ty where "v0 \<in> ty \<and> get_store (stabilize \<omega>) x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> A ((Ag ((get_store (stabilize \<omega>))(x \<mapsto> v)), Ag (get_trace (stabilize \<omega>))), get_state (stabilize \<omega>))"
      using exists_assert_def by auto
    then show ?A sorry
(*
      by (metis DiffD2 agreement.sel domI dom_fun_upd fst_conv full_add_defined get_store_def insertI1 option.distinct(1) u_neutral)
*)
  qed
qed

lemma proofs_are_self_framing:
  assumes "\<Delta> \<turnstile> [P] C [Q]"
  shows "self_framing P \<and> self_framing Q"
  using assms
proof (induct rule: SL_proof.induct)
  case (RuleInhale A P uw)
  then show ?case sorry
next
  case (RuleIf A b \<Delta> C1 B1 C2 B2)
  then show ?case sorry
next
  case (RuleFieldAssign A r e \<Delta>)
  then show ?case sorry
next
  case (RuleFieldAssignHeapIndep A r e \<Delta>)
  then show ?case sorry
next
  case (RuleHavoc A \<Delta> x)
  then show ?case
    using self_framing_exists_assert by force
qed (simp_all)


section \<open>Real big proof\<close>

lemma wf_setI:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> stable \<omega> \<and> typed_store \<Delta> (get_store \<omega>)"
  shows "wf_set \<Delta> S"
  using assms wf_set_def wf_state_def
  by metis

lemma wf_set_subset:
  assumes "wf_set \<Delta> S'"
      and "S \<subseteq> S'"
    shows "wf_set \<Delta> S"
  by (meson assms(1) assms(2) wf_set_def subsetD)

lemma prove_equality_snd_assertify:
  assumes "wf_set \<Delta> S"
  shows "Set.filter (wf_state \<Delta>) (\<langle>assertify S\<rangle>) = S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    by (smt (verit, ccfv_SIG) already_stable assertify_def mem_Collect_eq member_filter semantics.inh_def semantics_axioms subsetI wf_state_def)
  show "?B \<subseteq> ?A"
    by (smt (verit, ccfv_SIG) already_stable assertify_def assms in_inh member_filter subsetI wf_set_def wf_state_def)
qed

lemma assertify_only:
  assumes "self_framing A"
  shows "assertify (\<langle>A\<rangle>) = A"
  using assms same_assertify by auto


lemma stabilize_state_equiv:
  "stabilize (\<omega> :: ('v, 'a) abs_state) = (fst \<omega>, stabilize (snd \<omega>))"
  by (metis already_stable fst_conv snd_conv stabilize_is_stable stabilize_prod_def stable_snd)

lemma finite_dom_free_varsE:
  assumes "finite (dom (variables \<Delta>))"
      and "equal_on_set (free_vars \<Delta> A) \<sigma>1 \<sigma>2"
      and "A ((Ag \<sigma>1, \<tau>), \<gamma>)"
    shows "A ((Ag \<sigma>2, \<tau>), \<gamma>)"
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
    assume asm0: "typed_store \<Delta> \<sigma>1" "typed_store \<Delta> \<sigma>2" "equal_on_set (free_vars \<Delta> A - {x}) \<sigma>1 \<sigma>2" "exists_assert \<Delta> x A ((Ag \<sigma>1, \<tau>), \<gamma>)"
    moreover obtain ty where "Some ty = variables \<Delta> x"
      using assms(2) by force
    ultimately obtain v where "A ((Ag (\<sigma>1(x := Some v)), \<tau>), \<gamma>)" "v \<in> ty" using exists_assert_def
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
    ultimately show "exists_assert \<Delta> x A ((Ag \<sigma>2, \<tau>), \<gamma>)"
      by (smt (verit, best) \<open>Some ty = variables \<Delta> x\<close> agreement.exhaust_sel agreement.sel assms(1) exists_assertI finite_dom_free_varsE fst_conv get_store_def get_trace_def snd_conv)
  qed
qed


(*
lemma havoc_case:
  assumes "wf_set \<Delta> (snd ` SA)"
(* set is well-typed *)
      and "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>ty \<sigma> \<gamma>. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(upd_ag_partial_map \<sigma> x (Some v), \<gamma>) |v. v \<in> ty} \<and> \<Delta> x = Some ty)"
    shows "entails (assertify (\<Union>\<omega>\<in>SA. f \<omega>)) (exists_assert \<Delta> x (assertify (snd ` SA)))"
proof (rule entailsI)
  fix \<omega>' assume asm0: "assertify (\<Union> (f ` SA)) \<omega>'"
  then obtain \<omega> where "\<omega> \<in> SA" "stabilize \<omega>' \<in> f \<omega>" using assertify_def by auto
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
  ultimately show "exists_assert \<Delta> x (assertify (snd ` SA)) \<omega>'"
    using exists_assert_def[of _ x "assertify (snd ` SA)" \<omega>']
      assertify_def[of "snd ` SA" "(upd_ag_partial_map (fst \<omega>') x (Some v), snd \<omega>')"]
    by (metis (mono_tags, opaque_lifting) \<open>\<omega> \<in> SA\<close> agreement.exhaust_sel fst_conv full_add_defined get_store_def image_iff option.distinct(1) prod.exhaust_sel r u_neutral)
qed
*)

lemma assertify_equal:
  assumes "wf_set \<Delta> S"
  shows "Set.filter stable (\<langle>assertify S\<rangle>) = S"
proof
  show "Set.filter stable (\<langle>assertify S\<rangle>) \<subseteq> S"
    by (metis (no_types, lifting) already_stable assertify_def inh_def mem_Collect_eq member_filter subsetI)
  show "S \<subseteq> Set.filter sep_algebra_class.stable (\<langle>assertify S\<rangle>)"
    by (metis assms member_filter prove_equality_snd_assertify subsetI wf_state_def)
qed

lemma wf_set_after_union:
  assumes "\<And>\<omega>. \<omega> \<in> S \<Longrightarrow> wf_set \<Delta> (f \<omega>)"
  shows "wf_set \<Delta> (\<Union>\<omega>\<in>S. f \<omega>)"
  by (meson UN_iff assms wf_set_def)

text \<open>fst \<omega> is the past (list of all past states), it represents the real choice. Indeed, imagine
1) {\<omega>1} --> {\<omega>'} --> {\<omega>1'}
2) {\<omega>2} --> {\<omega>'} --> {\<omega>2'}
--> {\<omega>1, \<omega>2} --> {\<omega>'} --> {\<omega>1', \<omega>2'}
How do we express the latter with a choice only on the last state?\<close>

lemma Viper_implies_SL_proof_aux:
  fixes f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "wf_set \<Delta> (snd ` SA)"
    shows "\<Delta> \<turnstile> [assertify (snd ` SA)] C [assertify (\<Union>\<omega>\<in>SA. f \<omega>)]"
  using assms
proof (induct C arbitrary: SA f)
  case (Seq C1 C2)
  let ?A = "assertify (snd ` SA)"
  let ?SB = "\<Union>\<omega>\<in>SA. f \<omega>"
  let ?B = "assertify ?SB"

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

  let ?R' = "assertify (\<Union>\<omega>\<in>SA. f1 \<omega>)"

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
  let ?R = "assertify (snd ` ?SR)"

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

  have "\<Delta> \<turnstile> [?R] C2 [assertify (\<Union> (f2 ` ?SR))]"
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
      then show "sep_algebra_class.stable \<omega>' \<and> typed_store \<Delta> (get_store \<omega>')"
        by (meson Seq.prems(3) \<open>\<omega> \<in> SA\<close> \<open>\<omega>' \<in> f1 \<omega>\<close> imageI red_stable red_well_typed wf_set_def wf_state_def)
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
  then have "?B = assertify (\<Union> (f2 ` ?SR))"
    by presburger

  ultimately show "\<Delta> \<turnstile> [?A] C1 ;; C2 [?B]"
    using RuleSeq \<open>\<Delta> \<turnstile> [assertify (snd ` SA)] C1 [assertify (\<Union> (f1 ` SA))]\<close> by force
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

  let ?A1 = "assertify (snd ` ?S1)"
  let ?B1 = "assertify (\<Union> (f ` ?S1))"

  have "\<Delta> \<turnstile> [assertify (snd ` ?S1)] C1 [assertify (\<Union> (f ` ?S1))]"
  proof (rule If(1))
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<Longrightarrow> red_stmt \<Delta> C1 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
    show "wf_abs_stmt \<Delta> C1"
      using If.prems(2) wf_abs_stmt.simps(6) by blast
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)"
      by (metis (no_types, lifting) If.prems(3) Un_upper1 \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono semantics.wf_set_subset semantics_axioms)
  qed

  have "framed_by_exp (assertify (snd ` SA)) b"
  proof (rule framed_by_expI)
    fix \<omega> assume "(assertify (snd ` SA)) \<omega>"
    then have "stabilize \<omega> \<in> snd ` SA"
      by (simp add: assertify_def)
    then show "b \<omega> \<noteq> None"
      by (smt (verit, ccfv_SIG) If.prems(1) If.prems(2) imageE max_projection_prop_def max_projection_prop_stable_stabilize option.distinct(1) semantics.red_stmt_If_elim semantics.wf_abs_stmt.simps(6) semantics_axioms wf_expE)
  qed


  have "?A1 = assertify (snd ` SA) \<and>\<and> pure_assertify b"
  proof (rule self_framing_ext)
    show "self_framing ?A1"
      using assertify_self_framing by blast
    show "self_framing (assertify (snd ` SA) \<and>\<and> pure_assertify b)"
      by (smt (verit, ccfv_threshold) If.prems(2) \<open>framed_by_exp (assertify (snd ` SA)) b\<close> aconj_def assertify_self_framing pure_assertify_def self_framing_def wf_abs_stmt.simps(6) wf_exp_framed_by_stabilize)
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "?A1 \<omega>"
    show "(assertify (snd ` SA) \<and>\<and> pure_assertify b) \<omega>"
    proof (rule sat_conjI)
      show "(assertify (snd ` SA)) \<omega>"
        using asm0(2) assertify_def by auto
      have "stabilize \<omega> \<in> snd ` ?S1"
        using asm0(2) assertify_def by blast
      then have "(pure_assertify b) (stabilize \<omega>)"
        by (smt (verit, best) imageE member_filter pure_assertify_def)
      then show "(pure_assertify b) \<omega>"
        by (simp add: already_stable asm0(1))
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "(assertify (snd ` SA) \<and>\<and> pure_assertify b) \<omega>"
    then show "?A1 \<omega>"
      by (smt (verit) already_stable assertify_def image_iff member_filter pure_assertify_def sat_conjE)
  qed

  let ?A2 = "assertify (snd ` ?S2)"
  let ?B2 = "assertify (\<Union> (f ` ?S2))"


  have "\<Delta> \<turnstile> [?A2] C2 [?B2]"
  proof (rule If(2))
    show "wf_abs_stmt \<Delta> C2"
      using If.prems(2) by auto
    show "wf_set \<Delta> (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA)"
      by (metis (no_types, lifting) If.prems(3) \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> image_mono inf_sup_ord(4) semantics.wf_set_subset semantics_axioms)
    show "\<And>\<omega>. \<omega> \<in> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA \<Longrightarrow> red_stmt \<Delta> C2 (snd \<omega>) (f \<omega>)"
      using If.prems(1) by fastforce
  qed

  have "?A2 = assertify (snd ` SA) \<and>\<and> pure_assertify (negate b)"
  proof (rule self_framing_ext)
    show "self_framing ?A2"
      using assertify_self_framing by blast
    show "self_framing (assertify (snd ` SA) \<and>\<and> pure_assertify (negate b))"
      by (smt (verit, ccfv_threshold) If.prems(2) \<open>framed_by_exp (assertify (snd ` SA)) b\<close> aconj_def assertify_self_framing negate_sat_equiv self_framing_def wf_abs_stmt.simps(6) wf_exp_framed_by_stabilize)

    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "?A2 \<omega>"
    show "(assertify (snd ` SA) \<and>\<and> pure_assertify (negate b)) \<omega>"
    proof (rule sat_conjI)
      show "(assertify (snd ` SA)) \<omega>"
        using asm0(2) assertify_def by auto
      have "stabilize \<omega> \<in> snd ` ?S2"
        using asm0(2) assertify_def by blast
      then have "(pure_assertify (negate b)) (stabilize \<omega>)"
        using negate_sat_equiv by fastforce
      then show "(pure_assertify (negate b)) \<omega>"
        by (simp add: already_stable asm0(1))
    qed
  next
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "(assertify (snd ` SA) \<and>\<and> pure_assertify (negate b)) \<omega>"
    then have "\<omega> \<in> snd ` SA \<and> b \<omega> = Some False"
      by (metis already_stable assertify_def negate_sat_equiv sat_conjE)
    then show "?A2 \<omega>"
      by (smt (verit) already_stable asm0(1) assertify_def image_iff member_filter)
  qed

  moreover have "\<Delta> \<turnstile> [assertify (snd ` SA)] abs_stmt.If b C1 C2 [?B1 || ?B2]"
    using RuleIf \<open>\<Delta> \<turnstile> [assertify (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA)] C2 [assertify (\<Union> (f ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA))]\<close> \<open>\<Delta> \<turnstile> [assertify (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA)] C1 [assertify (\<Union> (f ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA))]\<close> \<open>assertify (snd ` Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA) = assertify (snd ` SA) \<and>\<and> pure_assertify b\<close> \<open>framed_by_exp (assertify (snd ` SA)) b\<close> calculation by auto

  moreover have "?B1 || ?B2 = assertify (\<Union> (f ` SA))"
  proof (rule self_framing_ext)
    show "self_framing (?B1 || ?B2)"
      using calculation(2) proofs_are_self_framing by presburger
    show "self_framing (assertify (\<Union> (f ` SA)))"
      using assertify_self_framing by auto
    fix \<omega> :: "('v, 'a) abs_state" assume "stable \<omega>"
    show "(?B1 || ?B2) \<omega> \<Longrightarrow> assertify (\<Union> (f ` SA)) \<omega>"
      using UnI1 adisj_def assertify_def by auto
    show "assertify (\<Union> (f ` SA)) \<omega> \<Longrightarrow> (?B1 || ?B2) \<omega>"
      by (metis (no_types, lifting) UN_Un Un_iff \<open>SA = Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some True) SA \<union> Set.filter (\<lambda>\<omega>. b (snd \<omega>) = Some False) SA\<close> assertify_def sat_disjI(1) sat_disjI(2))
  qed
  ultimately show ?case
    by argo
next
  case (Inhale P)

  let ?A = "assertify (snd ` SA)"

  have "\<And>\<omega>. \<omega> \<in> \<langle>?A\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> rel_stable_assertion \<omega> P"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> \<langle>?A\<rangle>" "stable \<omega>"
    then obtain x where "x \<in> SA" "snd x = \<omega>"
      by (metis (no_types, opaque_lifting) already_stable assertify_def assertify_only assertify_self_framing image_iff)
    then have "red_stmt \<Delta> (Inhale P) \<omega> (f x)"
      by (metis Inhale.prems(1))
    then show "rel_stable_assertion \<omega> P"
      by force
  qed
  then have r: "framed_by ?A P"
    using framed_by_def by blast
  have "\<Delta> \<turnstile> [?A] Inhale P [astar ?A P]"
  proof (rule RuleInhale)
    show "self_framing ?A"
      by (simp add: assertify_self_framing)
  qed (simp add: r)
  moreover have "self_framing (?A && P)"
    using calculation proofs_are_self_framing by presburger
  moreover have "Set.filter sep_algebra_class.stable (snd ` SA) \<subseteq> \<langle>?A\<rangle>"
    by (metis (no_types, lifting) in_inh member_filter assertify_def already_stable subsetI)

  moreover have "Set.filter sep_algebra_class.stable (\<langle>?A && P\<rangle>) = \<Union> (f ` SA)"
  proof
    show "Set.filter sep_algebra_class.stable (\<langle>?A && P\<rangle>) \<subseteq> \<Union> (f ` SA)"
    proof
      fix \<omega> assume "\<omega> \<in> Set.filter sep_algebra_class.stable (\<langle>?A && P\<rangle>)"
      then obtain a p where asm0: "stable \<omega>" "Some \<omega> = a \<oplus> p" "?A a" "P p" "a \<in> \<langle>assertify (snd ` SA)\<rangle>"
        by (smt (verit, ccfv_threshold) inh_def mem_Collect_eq member_filter astar_def)
      then have "Some \<omega> = stabilize a \<oplus> p"
        using stabilize_sum_result_stable by blast
      moreover obtain l where "l \<in> SA" "snd l = stabilize a"
        using asm0(3) assertify_def by auto
      then have "red_stmt \<Delta> (Inhale P) (stabilize a) (f l)"
        by (metis Inhale.prems(1))
      then have "\<omega> \<in> f l"
        by (smt (verit, best) asm0(1) asm0(4) calculation in_inh member_filter semantics.red_stmt_Inhale_elim semantics_axioms singletonI x_elem_set_product)
      then show "\<omega> \<in> \<Union> (f ` SA)"
        using \<open>l \<in> SA\<close> by blast
    qed
    show "\<Union> (f ` SA) \<subseteq> Set.filter sep_algebra_class.stable (\<langle>assertify (snd ` SA) && P\<rangle>)"
    proof 
      fix \<omega> assume "\<omega> \<in> \<Union> (f ` SA)"
      then obtain x where "x \<in> SA" "\<omega> \<in> f x"
        by blast
      then have "red_stmt \<Delta> (Inhale P) (snd x) (f x)"
        using Inhale.prems(1) by blast
      then show "\<omega> \<in> Set.filter sep_algebra_class.stable (\<langle>assertify (snd ` SA) && P\<rangle>)"
      proof (rule red_stmt_Inhale_elim)
        assume "f x = Set.filter sep_algebra_class.stable ({snd x} \<otimes> \<langle>P\<rangle>)"
        then obtain p where "p \<in> \<langle>P\<rangle>" "Some \<omega> = snd x \<oplus> p" "stable \<omega>"
          by (smt (verit, ccfv_SIG) \<open>\<omega> \<in> f x\<close> member_filter singletonD x_elem_set_product)
        then show "\<omega> \<in> Set.filter sep_algebra_class.stable (\<langle>assertify (snd ` SA) && P\<rangle>)"
          by (smt (verit, ccfv_threshold) Inhale.prems(3) \<open>x \<in> SA\<close> astar_inh image_eqI member_filter prove_equality_snd_assertify x_elem_set_product)
      qed
    qed
  qed
  ultimately show ?case
    by (smt (verit, best) already_stable assertify_def assertify_self_framing member_filter same_assertify self_framing_ext)
next
  case (Exhale P)

  let ?A = "assertify (\<Union> (f ` SA))"
  let ?B = "assertify (snd ` SA)"

  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>a \<omega>'. f \<omega> = {\<omega>'} \<and> a \<in> \<langle>P\<rangle> \<and> Some (snd \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>')"
  proof -
    fix \<omega> assume "\<omega> \<in> SA"
    then have "red_stmt \<Delta> (Exhale P) (snd \<omega>) (f \<omega>)"
      using Exhale.prems(1) by blast
    then show "\<exists>a \<omega>'. f \<omega> = {\<omega>'} \<and> a \<in> \<langle>P\<rangle> \<and> Some (snd \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>'"
      using red_stmt_Exhale_elim
      by blast
  qed

  then have "wf_set \<Delta> (\<Union> (f ` SA))"
    by (smt (verit, ccfv_threshold) Exhale.prems(1) Exhale.prems(3) Set.set_insert image_insert insertCI red_well_typed wf_state_def singletonD wf_set_after_union wf_set_def)

  moreover have "entails ?B (?A && P)"
  proof (rule entailsI)
    fix \<omega> assume "(assertify (snd ` SA)) \<omega>"
    then have "stabilize \<omega> \<in> snd ` SA"
      using assertify_def by blast
    then obtain x where asm0: "x \<in> SA" "stabilize \<omega> = snd x"
      by blast
    then obtain a \<omega>' where "f x = {\<omega>'} \<and> a \<in> \<langle>P\<rangle> \<and> Some (stabilize \<omega>) = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>'"
      using r by metis
    moreover obtain \<omega>'' where "Some \<omega>'' = \<omega>' \<oplus> |\<omega>|"
      by (metis asso3 calculation commutative decompose_stabilize_pure not_Some_eq) (* long *)
    then have "stabilize \<omega>'' = stabilize \<omega>'" using pure_larger_stabilize_same[of \<omega>'' \<omega>']
      using core_is_pure pure_def pure_larger_def by blast
    then have "assertify (\<Union> (f ` SA)) \<omega>''"
      by (metis (no_types, lifting) UN_I already_stable asm0(1) assertify_def calculation singletonI)
    moreover have "Some \<omega> = \<omega>'' \<oplus> a"
      by (metis (no_types, lifting) \<open>Some \<omega>'' = \<omega>' \<oplus> |\<omega>|\<close> asso1 calculation(1) commutative decompose_stabilize_pure)
    ultimately show "(assertify (\<Union> (f ` SA)) && P) \<omega>"
      by (metis astar_def inh_def mem_Collect_eq)
  qed

  moreover show "\<Delta> \<turnstile> [?B] Exhale P [?A]"
  proof (rule RuleExhale)
    show "self_framing (assertify (\<Union> (f ` SA)))"
      using assertify_self_framing by auto
    show "self_framing (assertify (snd ` SA))"
      using assertify_self_framing by auto
    show "entails (assertify (snd ` SA)) (assertify (\<Union> (f ` SA)) && P)"
      using calculation(2) by simp
  qed
next
  case (Assert P)
  have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>} \<and> P (snd \<omega>)"
    using Assert.prems(1) by blast
  moreover have "entails (assertify (snd ` SA)) P"
  proof (rule entailsI)
    fix \<omega> assume "assertify (snd ` SA) \<omega>"
    then have "stabilize \<omega> \<in> snd ` SA"
      using assertify_def by blast
    then have "P (stabilize \<omega>)"
      using r by force
    then show "P \<omega>" sorry
(*
      by (metis Assert.prems(2) pure_larger_stabilize stabilize_def wf_assertionE wf_abs_stmt.simps(4))
*)
  qed
  moreover have "\<Union> (f ` SA) = snd ` SA"
  proof
    show "\<Union> (f ` SA) \<subseteq> snd ` SA"
      using r by auto
    show "snd ` SA \<subseteq> \<Union> (f ` SA)"
      using r by auto
  qed
  ultimately show ?case
    by (metis RuleAssert assertify_self_framing)
next
  case (LocalAssign x1a x2a)
  then show ?case sorry
next
  case (FieldAssign r e)

  then have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow>
  (\<exists>\<sigma> hl v ptr \<gamma>. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl)"
    using has_write_perm_def sorry (* by fast *)

  define eval_r :: "('v, 'a) abs_state \<Rightarrow> 'r" where "eval_r = (\<lambda>\<omega>. SOME v. r \<omega> = Some v)"
  then have eval_r_prop: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> r (snd \<omega>) = Some (eval_r (snd \<omega>))"
    using r by force

  show ?case
  proof (cases "depends_on_ag_store_only r \<and> depends_on_ag_store_only e")
    case True
    
    
    define get_ptr where "get_ptr = (\<lambda>\<omega>. SOME ptr. \<exists>\<sigma> \<gamma> hl v. snd \<omega> = (\<sigma>, \<gamma>) \<and> f \<omega> = {(\<sigma>, set_value \<gamma> hl v)} \<and> r (\<sigma>, \<gamma>) = Some hl \<and> e (\<sigma>, \<gamma>) = Some v
    \<and> \<gamma> \<succeq> ptr \<and> has_write_perm_only ptr hl \<and> stable ptr )"
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
    
    let ?A = "assertify ?SA"


    have "framed_by_exp ?A r" sorry

    moreover have "framed_by_exp ?A e" sorry

    moreover have "self_framing ?A"
      using assertify_self_framing by auto
(* points_to_r is also self_framing *)
    
    ultimately have "\<Delta> \<turnstile> [?A && points_to r] FieldAssign r e [?A && points_to_value r e]"
      using True semantics.RuleFieldAssignHeapIndep semantics_axioms by blast
    
    moreover have "assertify (snd ` SA) = ?A && points_to r"
    proof (rule self_framing_ext)
      show "self_framing (assertify (snd ` SA))"
        using assertify_self_framing by auto
    
      show "self_framing (?A && points_to r)"
        using calculation proofs_are_self_framing by presburger
    
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "assertify (snd ` SA) \<omega>"
      then obtain x where "x \<in> SA" "snd x = \<omega>"
        using already_stable assertify_def by fastforce
      then obtain \<sigma> \<gamma> hl v where "snd x = (\<sigma>, \<gamma>)" "f x = {(\<sigma>, set_value \<gamma> hl v)}" "r (\<sigma>, \<gamma>) = Some hl"
        "e (\<sigma>, \<gamma>) = Some v" "Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)" "stable (get_rem x)" "fst (get_rem x) = \<sigma>"
        using r_get_rem by blast
    
      show "(assertify ((stabilize \<circ> get_rem) ` SA) && points_to r) \<omega>"
      proof (rule sat_starI)
        show "Some \<omega> = get_rem x \<oplus> (\<sigma>, get_ptr x)"
          using \<open>Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)\<close> \<open>snd x = (\<sigma>, \<gamma>)\<close> \<open>snd x = \<omega>\<close> by auto
        show "assertify ((stabilize \<circ> get_rem) ` SA) (get_rem x)"
          using \<open>x \<in> SA\<close> assertify_def by auto
    
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
      assume asm0: "sep_algebra_class.stable \<omega>" "(assertify ((stabilize \<circ> get_rem) ` SA) && points_to r) \<omega>"
      then obtain a ptr where "Some \<omega> = a \<oplus> ptr" "stabilize a \<in> (stabilize \<circ> get_rem) ` SA" "points_to r ptr"
        using assertify_def astar_def by auto
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
          by (smt (verit, ccfv_threshold) True \<open>snd x = (\<sigma>, \<tau>, \<gamma>)\<close> \<open>x \<in> SA\<close> depends_on_ag_store_only_def r_ptr semantics.points_toI semantics_axioms snd_conv)
*)
      qed


      moreover have "Some (snd x) = get_rem x \<oplus> (fst \<omega>, get_ptr x)"
        using \<open>Some (\<sigma>, \<gamma>) = get_rem x \<oplus> (\<sigma>, get_ptr x)\<close> \<open>\<sigma> = fst \<omega>\<close> \<open>snd x = (\<sigma>, \<gamma>)\<close> by auto
      ultimately have "stabilize (snd x) = stabilize \<omega>"
        by (metis (no_types, lifting) \<open>Some \<omega> = a \<oplus> ptr\<close> \<open>\<sigma> = fst \<omega>\<close> \<open>stabilize a = stabilize (get_rem x)\<close> option.sel stabilize_sum)
      then show "assertify (snd ` SA) \<omega>"
        by (metis (no_types, lifting) FieldAssign.prems(3) \<open>x \<in> SA\<close> already_stable assertify_def assertify_equal image_eqI member_filter)
    qed
    
    moreover have "assertify (\<Union> (f ` SA)) = ?A && points_to_value r e"
    proof (rule self_framing_ext)
      show "self_framing (assertify (\<Union> (f ` SA)))"
        using assertify_self_framing by auto
      show "self_framing (assertify ((stabilize \<circ> get_rem) ` SA) && points_to_value r e)"
        sorry
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "assertify (\<Union> (f ` SA)) \<omega>"
      then obtain x where "x \<in> SA" "\<omega> \<in> f x"
        using already_stable assertify_def by fastforce
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

      moreover have "assertify ((stabilize \<circ> get_rem) ` SA) (get_rem x)"
        by (simp add: \<open>x \<in> SA\<close> assertify_def)


      ultimately show "(assertify ((stabilize \<circ> get_rem) ` SA) && points_to_value r e) \<omega>"
        by (simp add: commutative sat_starI)
    next
      fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "(assertify ((stabilize \<circ> get_rem) ` SA) && points_to_value r e) \<omega>"
      then obtain a ptr where "Some \<omega> = a \<oplus> ptr" "stabilize a \<in> ((stabilize \<circ> get_rem) ` SA)" "points_to_value r e ptr"
        using assertify_def astar_def by fastforce
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



      then show "assertify (\<Union> (f ` SA)) \<omega>"
        by (metis (no_types, lifting) UN_I \<open>x \<in> SA\<close> already_stable assertify_def calculation rr singletonI)
    qed
   
    
    ultimately show "\<Delta> \<turnstile> [assertify (snd ` SA)] FieldAssign r e [assertify (\<Union> (f ` SA))]"
      by presburger
  next
    case False
(* TODO?
Completely different rule...
 *)
    then show ?thesis sorry
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
  (* ultimately have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> (\<exists>\<sigma> \<tau> \<gamma>. snd \<omega> = ((\<sigma>, \<tau>), \<gamma>) \<and> f \<omega> = {((upd_ag_partial_map \<sigma> x (Some v), \<tau>), \<gamma>) |v. v \<in> ty})" *)
    (* by fastforce *)
  let ?A = "assertify (snd ` SA)"
  have "\<Delta> \<turnstile> [?A] Havoc x [exists_assert \<Delta> x ?A]"
    by (simp add: RuleHavoc assertify_self_framing)
  moreover have "assertify (\<Union> (f ` SA)) = exists_assert \<Delta> x ?A"
  proof (rule self_framing_ext)
    show "self_framing (assertify (\<Union> (f ` SA)))"
      by (simp add: assertify_self_framing)
    show "self_framing (exists_assert \<Delta> x (assertify (snd ` SA)))"
      using calculation proofs_are_self_framing by presburger
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "assertify (\<Union> (f ` SA)) \<omega>"
    then obtain xx where "xx \<in> SA" "\<omega> \<in> f xx"
      using already_stable assertify_def by fastforce
    moreover have "wf_state \<Delta> (snd xx)"
      by (meson Havoc.prems(3) calculation(1) image_iff wf_set_def)
    then obtain v0 where "v0 \<in> ty" "get_store (snd xx) x = Some v0"
      by (metis (mono_tags, lifting) \<open>variables \<Delta> x = Some ty\<close> domD domI typed_store_def wf_state_def)
    (* moreover obtain \<sigma> \<tau> \<gamma> where "snd xx = ((\<sigma>, \<tau>), \<gamma>) \<and> f xx = {((upd_ag_partial_map \<sigma> x (Some v), \<tau>), \<gamma>) |v. v \<in> ty}" *)
      (* using calculation(1) r by presburger *)
    (* then obtain v where "v \<in> ty" "((upd_ag_partial_map \<sigma> x (Some v), \<tau>), \<gamma>) = \<omega>" *)
      (* using calculation(2) by auto *)
    (* then have "assertify (snd ` SA) ((upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v0), \<tau>), \<gamma>)" *)
      (*
      by (metis (no_types, lifting) \<open>snd xx = ((\<sigma>, \<tau>), \<gamma>) \<and> f xx = {((upd_ag_partial_map \<sigma> x (Some v), \<tau>), \<gamma>) |v. v \<in> ty}\<close> already_stable asm0(1) assertify_def calculation(1) calculation(4) fst_conv image_eqI snd_conv stable_snd upd_ag_partial_map_invo upd_ag_partial_map_refl)
*)


    show "exists_assert \<Delta> x (assertify (snd ` SA)) \<omega>"
    proof (rule exists_assertI)
      show "variables \<Delta> x = Some ty"
        by (simp add: \<open>variables \<Delta> x = Some ty\<close>)
      show "assertify (snd ` SA) ((Ag ((get_store \<omega>)(x \<mapsto> v0)), Ag (get_trace \<omega>)), snd \<omega>)"
        sorry
        (* by (metis \<open>((upd_ag_partial_map \<sigma> x (Some v), \<tau>), \<gamma>) = \<omega>\<close> \<open>assertify (snd ` SA) ((upd_ag_partial_map (upd_ag_partial_map \<sigma> x (Some v)) x (Some v0), \<tau>), \<gamma>)\<close> agreement.collapse fst_eqD get_store_def get_trace_def semantics.upd_ag_partial_map_def semantics_axioms sndI) *)
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
    fix \<omega> assume asm0: "sep_algebra_class.stable \<omega>" "exists_assert \<Delta> x (assertify (snd ` SA)) \<omega>"

    thm exists_assert_def[of \<Delta> x "assertify (snd ` SA)" \<omega>]
    then obtain v v0 where "v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> assertify (snd ` SA) ((Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)"
      using exists_assert_def[of \<Delta> x "assertify (snd ` SA)" \<omega>] \<open>variables \<Delta> x = Some ty\<close> by auto
    then have "((Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>) \<in> snd ` SA"
      by (metis already_stable asm0(1) assertify_def get_state_def snd_conv stable_snd)
    then obtain xx where "xx \<in> SA" "snd xx = ((Ag ((get_store \<omega>)(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)"
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
      (* by (smt (z3) \<open>v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> assertify (snd ` SA) ((Ag (get_store \<omega>(x \<mapsto> v)), Ag (get_trace \<omega>)), get_state \<omega>)\<close> agreement.exhaust_sel agreement.sel fst_conv fun_upd_triv fun_upd_upd get_state_def get_store_def get_trace_def mem_Collect_eq prod.collapse r snd_conv upd_ag_partial_map_def) *)
    then show "assertify (\<Union> (f ` SA)) \<omega>"
      by (metis (no_types, opaque_lifting) UN_iff \<open>xx \<in> SA\<close> already_stable asm0(1) assertify_def)
  qed
  ultimately show "\<Delta> \<turnstile> [assertify (snd ` SA)] Havoc x [assertify (\<Union> (f ` SA))]"
    by simp
next
  case (Scope x1a x2a C)
  then show ?case sorry
next
  case Skip
  then have "\<Delta> \<turnstile> [assertify (snd ` SA)] Skip [assertify (snd ` SA)]"
    using RuleSkip assertify_self_framing by blast
  moreover have "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = {snd \<omega>}"
    using Skip.prems(1) by blast
  ultimately show ?case
    by (metis (no_types, lifting) SUP_cong UNION_singleton_eq_range)
next
  case (Assume A)
  then show ?case sorry
next
  case (Label l)
  then show ?case sorry
qed


(*
lemma Viper_implies_SL_proof_aux:
  fixes f :: "(('v, 'a) abs_state list \<times> ('v, 'a) abs_state) \<Rightarrow> ('v, 'a) abs_state set"
  assumes "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> red_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_abs_stmt \<Delta> C"
      and "wf_set \<Delta> (snd ` SA)"
    shows "\<Delta> \<turnstile> [assertify (snd ` SA)] C [assertify (\<Union>\<omega>\<in>SA. f \<omega>)]"
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

  let ?A = "assertify (snd ` SA)"
  let ?B = "assertify (\<Union>\<omega>\<in>SA. f \<omega>)"

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
      by (meson calculation(2) semantics.proofs_are_self_framing semantics_axioms)
    show "self_framing A"
      by (simp add: assms(3))
    fix \<omega> :: "('v, 'a) abs_state" assume asm0: "sep_algebra_class.stable \<omega>"
    show "A \<omega> \<Longrightarrow> ?A \<omega>"
    proof -
      assume asm1: "A \<omega>"
      then have "([], \<omega>) \<in> SA"
        using SA_def asm0 by blast
      then show "?A \<omega>"
        by (metis already_stable asm0 assertify_def image_eqI snd_conv)
    qed
    assume asm1: "?A \<omega>"
    then have "\<omega> \<in> snd ` SA"
      by (simp add: already_stable asm0 assertify_def)
    then show "A \<omega>" using SA_def by force
  qed
  ultimately show ?thesis
    by force
qed

lemma entails_trans:
  assumes "entails A B"
      and "entails B C"
    shows "entails A C"
  by (meson assms(1) assms(2) dual_order.trans entails_def)

lemma entails_refl:
  "entails A A"
  by (simp add: entailsI)

lemma SL_proof_Havoc_list_elim:
  assumes "\<Delta> \<turnstile> [A] havoc_list l [B]"
  shows "self_framing A \<and> self_framing B \<and> entails A B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - (set l)"
  using assms
proof (induct l arbitrary: A B)
  case Nil
  then show ?case using SL_proof_Skip_elim
    using entails_refl by force
next
  case (Cons a l)
  then obtain R where "\<Delta> \<turnstile> [A] Havoc a [R]" "\<Delta> \<turnstile> [R] havoc_list l [B]"
    by (metis SL_proof_Seq_elim havoc_list.simps(2))
  moreover have "self_framing B \<and> entails R B \<and> free_vars \<Delta> B \<subseteq> free_vars \<Delta> R - set l"
    using Cons.hyps calculation(2) by blast
  ultimately show ?case
    sorry
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
    shows "\<exists>F. \<Delta> \<turnstile> [A] C1 [F && P2 && P1] \<and> \<Delta> \<turnstile> [F && Q1 && Q2] C2 [B] \<and> set l \<inter> free_var F = {}"
proof -

  obtain D where triple: "\<Delta> \<turnstile> [A] ?C1 ;; ?C2 [D]"
    by (metis Viper_implies_SL_proof assms(1) assms(2) assms(3) assms(4))
  then obtain F where F_def: "\<Delta> \<turnstile> [A] ?C1 [F]" "\<Delta> \<turnstile> [F] ?C2 [D]"
    by (meson SL_proof_Seq_elim)
  then obtain FF where "\<Delta> \<turnstile> [A] (C1 ;; Exhale (astar P1 P2)) [FF]" "\<Delta> \<turnstile> [FF] havoc_list l [F]" (* "entails FF F" "free_var F \<subseteq> free_var FF - set l" *)
    by (meson SL_proof_Seq_elim)
  then obtain FFF where "\<Delta> \<turnstile> [A] C1 [FFF]" "\<Delta> \<turnstile> [FFF] Exhale (P1 && P2) [FF]"
    by (meson SL_proof_Seq_elim)
  then have "entails FFF (FF && (P1 && P2))"
    using SL_proof_Exhale_elim by blast
  thm SL_proof_Inhale_elim
  moreover obtain E where "\<Delta> \<turnstile> [F && (Q1 && Q2)] C2 [E]"  "\<Delta> \<turnstile> [E] Exhale B [D]"
    using SL_proof_Inhale_elim SL_proof_Seq_elim F_def
    by (metis (full_types)) (* long *)

(*
    by (metis SL_proof_Exhale_elim SL_proof_Seq_elim)
*)
  have r1: "\<Delta> \<turnstile> [A] C1 [(F && P2) && P1]"
  proof (rule RuleCons)
    show "self_framing ((F && P2) && P1)"
      sorry
    show "entails ((FF && P2) && P1) (F && P2 && P1)"
      sorry
    show "entails A A"
      by (simp add: entails_refl)
    show "\<Delta> \<turnstile> [A] C1 [FF && P2 && P1]"
      sorry
(*
      using \<open>\<Delta> \<turnstile> [A] C1 [FF && P2 && P1] \<and> \<Delta> \<turnstile> [FF && P2 && P1] Exhale P1 [FF && P2] \<and> framed_by FF P2 \<and> framed_by (FF && P2) P1\<close> by blast
*)
    show "self_framing A"
      by (simp add: assms(3))
  qed
  have "\<Delta> \<turnstile> [F] Inhale Q1 ;; Inhale Q2 ;; C2 [atrue && B] \<and> framed_by atrue B"
    sorry
(*
    by (metis SL_proof_Exhale_elim SL_proof_Seq_elim)
*)
  then have "\<Delta> \<turnstile> [(F && Q1) && Q2] C2 [atrue && B] \<and> framed_by F Q1 \<and> framed_by (F && Q1) Q2"
    by force
  have r2: "\<Delta> \<turnstile> [(F && Q1) && Q2] C2 [B]"
  proof (rule RuleCons)
    show "entails (F && Q1 && Q2) ((F && Q1) && Q2)"
      by (simp add: entails_refl)
    show "self_framing (F && Q1 && Q2)" sorry
    show "\<Delta> \<turnstile> [F && Q1 && Q2] C2 [atrue && B]"
      using \<open>\<Delta> \<turnstile> [F && Q1 && Q2] C2 [atrue && B] \<and> framed_by F Q1 \<and> framed_by (F && Q1) Q2\<close> by blast
    show "entails (atrue && B) B"
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
  then have "red_stmt \<Delta> (Inhale P) \<omega> (Set.filter stable ({\<omega>} \<otimes> \<langle>P\<rangle>))"
    using RedInhale by auto
  moreover have "{\<omega>} \<otimes> \<langle>P\<rangle> \<subseteq> \<langle>astar A P\<rangle>"
  proof
    fix \<omega>' assume "\<omega>' \<in> {\<omega>} \<otimes> \<langle>P\<rangle>"
    then obtain p where "p \<in> \<langle>P\<rangle>" "Some \<omega>' = \<omega> \<oplus> p"
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
  then obtain \<omega>' a where "a \<in> \<langle>P\<rangle>" "Some \<omega> = \<omega>' \<oplus> a" "\<omega>' \<in> \<langle>A\<rangle>"
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
    using \<open>a \<in> \<langle>P\<rangle>\<close> full_add_charact(1) RedExhale by blast
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
    have r: "\<And>\<omega>. \<omega> \<in> SA \<Longrightarrow> f \<omega> = Set.filter stable ({\<omega>} \<otimes> \<langle>P\<rangle>)"
      using asm0(2) by blast
    moreover have "SB = Set.filter stable (SA \<otimes> \<langle>P\<rangle>)"
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
        then obtain a p where "Some \<omega> = a \<oplus> p" "stabilize a \<in> SA" "p \<in> \<langle>P\<rangle>"
          by (smt (verit, best) in_inh astar_def self_framing_closure_def)

        then have "Some (stabilize \<omega>) = stabilize a \<oplus> p" sorry
        then have "stabilize \<omega> \<in> SB"
          by (metis (no_types, lifting) UN_iff \<open>p \<in> \<langle>P\<rangle>\<close> \<open>stabilize a \<in> SA\<close> asm0(1) is_in_set_sum member_filter r stabilize_is_stable)
        then show "(self_framing_closure SB) \<omega>"
          by (metis self_framing_closure_def)
      next
        fix \<omega> assume asm1: "(self_framing_closure SB) \<omega>"
        then have "stabilize \<omega> \<in> SB"
          by (metis self_framing_closure_def)
        then obtain a p where "a \<in> SA" "p \<in> \<langle>P\<rangle>" "Some (stabilize \<omega>) = a \<oplus> p"
          by (metis (no_types, lifting) \<open>SB = Set.filter sep_algebra_class.stable (SA \<otimes> \<langle>P\<rangle>)\<close> member_filter x_elem_set_product)

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
          by (smt (verit, del_insts) \<open>p \<in> \<langle>P\<rangle>\<close> inh_def mem_Collect_eq astar_def)
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
      then have "Set.filter stable ({stabilize a} \<otimes> \<langle>P\<rangle>) \<subseteq> \<langle>B\<rangle>"
        by blast
(* Should come from:
- P is framed by A
*)
      moreover obtain pp where "Some (stabilize \<omega>) = stabilize a \<oplus> pp" "pp \<in> \<langle>P\<rangle>"
        sorry
      then have "stabilize \<omega> \<in> Set.filter stable ({stabilize a} \<otimes> \<langle>P\<rangle>)"
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
  let ?remaining = "\<lambda>\<omega>. SOME \<omega>'. \<exists>a \<in> \<langle>P\<rangle>. Some \<omega> = \<omega>' \<oplus> a \<and> stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>"
  have remaining_prop: "\<And>\<omega>. \<omega> \<in> \<langle>A\<rangle> \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow>
  (\<exists>a \<in> \<langle>P\<rangle>. Some \<omega> = ?remaining \<omega> \<oplus> a \<and> stable (?remaining \<omega>) \<and> get_store \<omega> = get_store (?remaining \<omega>) \<and> ?remaining \<omega> \<in> \<langle>B\<rangle>)"
  proof -
    fix \<omega> assume asm0: "\<omega> \<in> \<langle>A\<rangle>" "sep_algebra_class.stable \<omega>"
    then obtain S where "red_stmt \<Delta> (Exhale P) \<omega> S \<and> S \<subseteq> \<langle>B\<rangle>"
      using Exhale.prems(1) by presburger

    then obtain a \<omega>' where "a \<in> \<langle>P\<rangle>" "Some \<omega> = \<omega>' \<oplus> a" "stable \<omega>'" "get_store \<omega> = get_store \<omega>'" "\<omega>' \<in> S"
      by auto
    then show "\<exists>a \<in> \<langle>P\<rangle>. Some \<omega> = ?remaining \<omega> \<oplus> a \<and> stable (?remaining \<omega>) \<and> get_store \<omega> = get_store (?remaining \<omega>) \<and> ?remaining \<omega> \<in> \<langle>B\<rangle>"
      using someI_ex[of "\<lambda>\<omega>'. \<exists>a \<in> \<langle>P\<rangle>. Some \<omega> = \<omega>' \<oplus> a \<and> stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>"]
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
        fix \<omega>' assume "\<omega>' \<in> \<langle>?A\<rangle>"
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
      then obtain p where "p \<in> \<langle>P\<rangle>" "Some (stabilize \<omega>) = ?remaining ?\<omega> \<oplus> p" "stable (?remaining ?\<omega>)"
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
        assume "\<omega> \<in> \<langle>?A\<rangle>"
        let ?\<omega> = "stabilize \<omega>"
        show "WdInhale P \<omega>" sorry
(* Unclear why *)
      qed
      ultimately show "(astar ?A P) \<omega>"
        using Exhale.prems(2) SL_proof_self_framing \<open>\<Delta> \<turnstile> [astar \<lparr>= \<lambda>\<omega>'. \<exists>\<omega>\<in>\<langle>A\<rangle>. sep_algebra_class.stable \<omega> \<and> \<omega>' = (SOME \<omega>'. \<exists>a\<in>\<langle>P\<rangle>. Some \<omega> = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>), WdInhale = \<lambda>_. True\<rparr> P] Exhale P [\<lparr>= \<lambda>\<omega>'. \<exists>\<omega>\<in>\<langle>A\<rangle>. sep_algebra_class.stable \<omega> \<and> \<omega>' = (SOME \<omega>'. \<exists>a\<in>\<langle>P\<rangle>. Some \<omega> = \<omega>' \<oplus> a \<and> sep_algebra_class.stable \<omega>' \<and> get_store \<omega> = get_store \<omega>' \<and> \<omega>' \<in> \<langle>B\<rangle>), WdInhale = \<lambda>_. True\<rparr>]\<close> self_framing_sat_stabilize by blast
    qed
    show "entails ?A B" sorry

  qed
next
  case (If b C1 C2)
  show ?case
  proof (rule RuleIf)
    show "\<Delta> \<turnstile> [astar (pure_assertify b) A] C1 [B]" sorry
    show "\<Delta> \<turnstile> [astar (pure_assertify_not b) A] C2 [B]" sorry
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
