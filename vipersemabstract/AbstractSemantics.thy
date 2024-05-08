theory AbstractSemantics
  imports ViperCommon.LiftSepAlgebra ViperCommon.SepLogic
begin

section Start

type_synonym 'a assertion = "'a set"


type_synonym 'a bexp = "'a \<rightharpoonup> bool"
type_synonym ('a, 'v) exp = "'a \<rightharpoonup> 'v"
type_synonym 'v abs_vtyp = "'v set"

text \<open>Types:
- 'a: State (with ag_store, trace, heap...)
- 'v: Type of values
- 'r: Type of heap locations
\<close>

datatype ('a, 'v, 'r) abs_stmt =

\<comment>\<open>Assertions\<close>
  Inhale "'a assertion" | Exhale "'a assertion" | Assert "'a assertion" | Assume "'a assertion"

\<comment>\<open>Control structures\<close>
| If "'a bexp" "('a, 'v, 'r) abs_stmt" "('a, 'v, 'r) abs_stmt"
| Seq "('a, 'v, 'r) abs_stmt" "('a, 'v, 'r) abs_stmt" (infixl ";;" 60)

\<comment>\<open>Assignments\<close>
| LocalAssign var "('a, 'v) exp"
| Havoc var
| FieldAssign "('a, 'r) exp" "('a, 'v) exp"


\<comment>\<open>Misc\<close>
| Label label
| Scope "'v abs_vtyp" "('a, 'v, 'r) abs_stmt"
| Skip

record ('v, 'r) abs_type_context =
  variables :: "var \<rightharpoonup> 'v abs_vtyp"
  heap_locs :: "'r \<rightharpoonup> 'v abs_vtyp"

(* Should also have a mapping from heap loc to abs_typ *)
(*
definition get_store :: "('v, 'a) abs_state \<Rightarrow> (var \<rightharpoonup> 'v)" where "get_store = the_ag \<circ> fst"
*)

locale semantics =

  fixes has_value :: "('a :: sep_algebra) \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool"
  fixes has_write_perm_only :: "'a \<Rightarrow> 'r \<Rightarrow> bool"
  fixes set_value :: "'a \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> 'a"
  fixes well_typed_heap :: "('r \<rightharpoonup> 'v abs_vtyp) \<Rightarrow> 'a \<Rightarrow> bool"

(* Axioms
- TODO: Add smth about has_value
*)

(* Needed? *)
  assumes frame_preserving_writing_orig: "Some x = a \<oplus> b \<Longrightarrow> stable b \<Longrightarrow> has_write_perm_only a hl \<Longrightarrow> Some (set_value x hl v) = set_value a hl v \<oplus> b"
      and has_write_perm_only_same: "has_write_perm_only a hl \<Longrightarrow> has_write_perm_only b hl \<Longrightarrow> stabilize a = stabilize b"
  (* TODO: WRONG! Needs something about the value! *)

      and set_value_then_has_value: "has_write_perm_only a hl \<Longrightarrow> has_value (set_value a hl v) hl v"

      and well_typed_heap_sum: "Some x = a \<oplus> b \<Longrightarrow> well_typed_heap \<Delta> a \<Longrightarrow> well_typed_heap \<Delta> b \<Longrightarrow> well_typed_heap \<Delta> x"
      and well_typed_heap_smaller: "a \<succeq> b \<Longrightarrow> well_typed_heap \<Delta> a \<Longrightarrow> well_typed_heap \<Delta> b"
      and well_typed_heap_core: "well_typed_heap \<Delta> x \<longleftrightarrow> well_typed_heap \<Delta> |x|"
      and well_typed_heap_update: "well_typed_heap \<Delta> x \<Longrightarrow> \<Delta> r = Some ty \<Longrightarrow> v \<in> ty \<Longrightarrow> well_typed_heap \<Delta> (set_value x r v)"

begin


(* Needed:
- Checking perm(x.f) = 1
- Setting x.f := 5
- Checking x.f = something
 *)

definition has_write_perm :: "'a \<Rightarrow> 'r \<Rightarrow> bool" where
  "has_write_perm x hl \<longleftrightarrow> (\<exists>r. x \<succeq> r \<and> has_write_perm_only r hl)"

lemma set_value_stable: "has_write_perm a hl \<Longrightarrow> stable a \<Longrightarrow> stable (set_value a hl v)"
  sorry


definition filter_dom where
  "filter_dom vars S = Set.filter (\<lambda>\<omega>. dom (get_store \<omega>) = vars) S"

(*
definition self_framing :: "(('v, 'a) abs_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "self_framing A \<longleftrightarrow> (\<forall>\<omega>. A \<omega> \<longleftrightarrow> A (stabilize \<omega>))"
*)

(*
lemma "Stable A \<longleftrightarrow> (\<forall>\<omega>. \<omega> \<in> A \<longleftrightarrow> stabilize \<omega> \<in> A)" (is "?P \<longleftrightarrow> ?Q")
proof -
  have "?P \<longleftrightarrow> A \<subseteq> {\<omega>. stabilize \<omega> \<in> A}" unfolding Stable_def Stabilize_def by blast
  also have "... \<longleftrightarrow> (\<forall>\<omega>. \<omega> \<in> A \<longrightarrow> stabilize \<omega> \<in> A)"
    by blast
\<omega> \<notin> A \<longrightarrow> stabilize \<omega> \<notin> A



definition Stable :: "'a set \<Rightarrow> bool" where
  "Stable A \<longleftrightarrow> (A \<subseteq> Stabilize A)"
*)

thm Stable_def
thm Stabilize_def (* Stabilize ?A = {\<omega>. stabilize \<omega> \<in> ?A} *)


subsection \<open>Typed stuff\<close>

subsection \<open>States\<close>

definition typed_store :: "('v, 'r) abs_type_context \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "typed_store \<Delta> \<sigma> \<longleftrightarrow> (dom (variables \<Delta>) = dom \<sigma> \<and> (\<forall>x v ty. \<sigma> x = Some v \<and> variables \<Delta> x = Some ty \<longrightarrow> v \<in> ty))"

definition typed where
  "typed \<Delta> \<omega> \<longleftrightarrow> typed_store \<Delta> (get_store \<omega>) \<and> well_typed_heap (heap_locs \<Delta>) (get_state \<omega>)"

definition wf_state where
  "wf_state \<Delta> \<omega> \<longleftrightarrow> (stable \<omega> \<and> typed \<Delta> \<omega>)"




lemma typed_state_then_stabilize_typed:
  assumes "typed \<Delta> \<omega>"
  shows "typed \<Delta> (stabilize \<omega>)"
  by (smt (verit, best) assms greater_charact max_projection_prop_stable_stabilize mpp_smaller typed_def well_typed_heap_smaller)

lemma typed_sum:
  assumes "Some x = a \<oplus> b"
      and "typed \<Delta> a"
      and "typed \<Delta> b"
    shows "typed \<Delta> x"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) full_add_charact(1) full_add_charact(2) typed_def well_typed_heap_sum)

lemma typed_core:
  assumes "typed \<Delta> a"
  shows "typed \<Delta> |a|"
  by (metis assms core_charact(1) core_charact(2) typed_def well_typed_heap_core)

lemma typed_smaller:
  assumes "typed \<Delta> \<omega>'"
      and "\<omega>' \<succeq> \<omega>"
    shows "typed \<Delta> \<omega>"
  by (metis assms(1) assms(2) greater_charact typed_def well_typed_heap_smaller)


subsection \<open>Assertions\<close>

definition typed_assertion where
  "typed_assertion \<Delta> A \<longleftrightarrow> (\<forall>\<omega>\<in>A. typed \<Delta> \<omega>)"

lemma typed_assertionI:
  assumes "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> typed \<Delta> \<omega>"
  shows "typed_assertion \<Delta> A"
  using assms typed_assertion_def by blast

lemma typed_subset:
  assumes "A \<subseteq> A'"
      and "typed_assertion \<Delta> A'"
    shows "typed_assertion \<Delta> A"
  using assms(1) assms(2) typed_assertion_def by auto

lemma typed_star:
  assumes "typed_assertion \<Delta> A"
      and "typed_assertion \<Delta> B"
    shows "typed_assertion \<Delta> (A \<otimes> B)"
  by (meson assms(1) assms(2) typed_assertion_def typed_sum x_elem_set_product)



text \<open>The truth of A in a only depends on parts of a (for a ## \<omega>) that:
1) are stable, or
2) are given by |\<omega>|\<close>
definition rel_stable_assertion where
(*  "rel_stable_assertion \<omega> A \<longleftrightarrow> (\<forall>\<omega>'. \<omega> ## \<omega>' \<longrightarrow> (A \<omega>' \<longleftrightarrow> A (stabilize_rel \<omega> \<omega>')))" *)
  "rel_stable_assertion \<omega> A \<longleftrightarrow> (\<forall>x a. \<omega> ## a \<and> pure_larger x (stabilize a) \<and> x \<succeq> |\<omega>| \<longrightarrow> (a \<in> A \<longleftrightarrow> x \<in> A))"
(* typed \<Delta> \<omega> \<and> typed \<Delta> a \<and>  *)

(* is typing important here? *)

definition wf_set where
  "wf_set \<Delta> S \<longleftrightarrow> (\<forall>x \<in> S. wf_state \<Delta> x)"

definition assign_var_state :: "var \<Rightarrow> 'v option \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "assign_var_state x v \<omega> = set_store \<omega> ((get_store \<omega>)(x := v))"

section \<open>Operational semantics\<close>

inductive red_stmt :: "('v, 'r) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 'r) abs_stmt \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
  and sequential_composition :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> (('v, 'a) abs_state, 'v, 'r) abs_stmt \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
where

\<comment>\<open>f maps each x to one possible final set of states: It performs the angelic choice\<close>
  SeqComp: "\<lbrakk> \<And>\<omega>. \<omega> \<in> S \<Longrightarrow> (red_stmt \<Delta> C \<omega> (f \<omega>)) ; S' = Union (f ` S) \<rbrakk> \<Longrightarrow> sequential_composition \<Delta> S C S'"

| RedSkip: "red_stmt \<Delta> Skip \<omega> ({\<omega>})"

| RedAssertTrue: "\<lbrakk> \<omega> \<in> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assert A) \<omega> ({\<omega>})"
| RedAssumeTrue: "\<lbrakk> rel_stable_assertion \<omega> A; \<omega> \<in> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assume A) \<omega> ({\<omega>})"
| RedAssumeFalse: "\<lbrakk> rel_stable_assertion \<omega> A; \<omega> \<notin> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assume A) \<omega> ({})"

| RedInhale: "\<lbrakk> rel_stable_assertion \<omega> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Inhale A) \<omega> (Set.filter stable ({\<omega>} \<otimes> A))"
| RedExhale: "\<lbrakk> a \<in> A ; Some \<omega> = \<omega>' \<oplus> a ; stable \<omega>' \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Exhale A) \<omega> {\<omega>'}"
\<comment>\<open>Both Inhale and Exhale could be defined equivalently with stabilize instead of stable\<close>

| RedIfTrue: "\<lbrakk> b \<omega> = Some True ; red_stmt \<Delta> C1 \<omega> S \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (If b C1 C2) \<omega> S"
| RedIfFalse: "\<lbrakk> b \<omega> = Some False ; red_stmt \<Delta> C2 \<omega> S \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (If b C1 C2) \<omega> S"

| RedSeq: "\<lbrakk> red_stmt \<Delta> C1 \<omega> S1 ; sequential_composition \<Delta> S1 C2 S2 \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (C1 ;; C2) \<omega> S2"

\<comment>\<open>No need to handle the case where the variable is not defined, since it is part of well-definedness of a program\<close>
| RedLocalAssign: "\<lbrakk>variables \<Delta> x = Some ty; e \<omega> = Some v; v \<in> ty \<rbrakk> \<Longrightarrow>
   red_stmt \<Delta> (LocalAssign x e) \<omega> ({assign_var_state x (Some v) \<omega>})"

| RedHavoc: "variables \<Delta> x = Some ty \<Longrightarrow>
  red_stmt \<Delta> (Havoc x) \<omega> ({ assign_var_state x (Some v) \<omega> |v. v \<in> ty})"

| RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; has_write_perm (get_state \<omega>) hl; heap_locs \<Delta> hl = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_stmt \<Delta> (FieldAssign r e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) hl v)}"

| RedLabel: "red_stmt \<Delta> (Label l) \<omega> {set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_state \<omega>)))}"



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






(*

Set all possible values in \<omega> as well...
| RedScope: "red_stmt (\<Delta>(0 \<mapsto> ty)) C \<omega> S \<Longrightarrow>
  red_stmt \<Delta> (Scope ty C) \<omega> S"

\<comment>\<open>Updated type context\<close>
| RedScope: "\<lbrakk> sequential_composition Pr (shift_and_add_list T tys) E { (\<sigma>', \<tau>, \<phi>) |\<sigma>'. \<sigma>' \<in> declare_var_list (domains \<Delta>) tys \<sigma>} s r \<rbrakk> \<Longrightarrow>
  red_stmt \<Delta> (Scope ty s) (\<sigma>, \<tau>, \<phi>) ((unshift_state 1 ` r))"
*)


(*

(* Only rets and args defined when executing a method call, also empty trace *)
(* If method does not exist, or wrong number of args or rets: Not well-defined *)
(* Concrete method *)

(* r is the "frame" *)

(* Two things to verify:
- exhale I ; havoc l ; inhale I ; assume not(b)
- havoc l ; assume b ; inhale I ; s \<longrightarrow> satisfies I
*)

Needs type context to havoc
*)


definition self_framing where
  "self_framing A \<longleftrightarrow> (\<forall>\<omega>. \<omega> \<in> A \<longleftrightarrow> stabilize \<omega> \<in> A)"

lemma self_framingI:
  assumes "\<And>\<omega>. \<omega> \<in> A \<longleftrightarrow> stabilize \<omega> \<in> A"
  shows "self_framing A"
  using self_framing_def assms by blast

lemma self_framing_eq:
  "self_framing A \<longleftrightarrow> A = Stabilize A"
  unfolding self_framing_def Stabilize_def by blast

lemma mono_and_Stable_then_self_framing:
  assumes "up_closed A"
      and "Stable A"
    shows "self_framing A"
proof -
  have "Stabilize A \<subseteq> A"
  proof
    fix x assume "x \<in> Stabilize A"
    moreover have "x \<succeq> stabilize x"
      using max_projection_prop_stable_stabilize mpp_smaller by auto
    ultimately show "x \<in> A"
      using assms(1) up_closed_def by auto
  qed
  then show ?thesis
    by (meson Stable_def assms(2) dual_order.eq_iff semantics.self_framing_eq semantics_axioms)
qed

lemma up_closed_core_stable_self_framing:
  assumes "up_close_core A = A" (* should be true for all assertions? *)
      and "Stable A"
    shows "self_framing A"
proof -
  have "Stabilize A \<subseteq> A"
  proof 
    fix x assume "x \<in> Stabilize A"
    moreover have "pure_larger x (stabilize x)"
      by (metis decompose_stabilize_pure max_projection_prop_def max_projection_prop_pure_core pure_larger_def)
    ultimately show "x \<in> A"
      using assms(1) prove_in_up_close_core pure_larger_def by fastforce
  qed
  then show ?thesis
    by (meson Stable_def assms(2) dual_order.eq_iff semantics.self_framing_eq semantics_axioms)
qed

section \<open>Assertions\<close>

subsection \<open>General concepts\<close>

definition framed_by where
  "framed_by A B \<longleftrightarrow> (\<forall>\<omega> \<in> A. stable \<omega> \<longrightarrow> rel_stable_assertion \<omega> B)"



definition framed_by_exp where
  "framed_by_exp A e \<longleftrightarrow> (\<forall>\<omega> \<in> A. e \<omega> \<noteq> None)"

definition entails where
  "entails A B \<longleftrightarrow> (\<forall>\<omega> \<in> A. \<omega> \<in> B)"



section \<open>Free variables\<close>

definition equal_on_set :: "var set \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "equal_on_set S \<sigma>1 \<sigma>2 \<longleftrightarrow> (\<forall>x \<in> S. \<sigma>1 x = \<sigma>2 x)"

definition overapprox_fv :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> var set \<Rightarrow> bool" where
  "overapprox_fv \<Delta> A S \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2 \<tau> \<gamma>. typed_store \<Delta> \<sigma>1 \<and> typed_store \<Delta> \<sigma>2 \<and> equal_on_set S \<sigma>1 \<sigma>2 \<longrightarrow> (((Ag \<sigma>1, \<tau>), \<gamma>) \<in> A \<longleftrightarrow> ((Ag \<sigma>2, \<tau>), \<gamma>) \<in> A))"


definition free_vars where
  "free_vars \<Delta> A = (\<Inter>S \<in> {S. overapprox_fv \<Delta> A S}. S)"

text \<open>Works only if (dom \<Delta>) is finite.\<close>

definition at_least_two_elems:
  "at_least_two_elems S \<longleftrightarrow> (\<exists>a b. a \<in> S \<and> b \<in> S \<and> a \<noteq> b)"

subsection \<open>wf_assertion\<close>

(* TODO: Is it needed? *)
definition wf_assertion :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "wf_assertion \<Delta> A \<longleftrightarrow> typed_assertion \<Delta> A \<and> (\<forall>x' x. pure_larger x' x \<and> x \<in> A \<longrightarrow> x' \<in> A)"

lemma self_framing_wfI:
  assumes "wf_assertion \<Delta> A"
      and "\<And>\<omega>. \<omega> \<in> A \<Longrightarrow> stabilize \<omega> \<in> A"
    shows "self_framing A"
  unfolding self_framing_def
proof -
  have "\<And>\<omega>. stabilize \<omega> \<in> A \<Longrightarrow> \<omega> \<in> A"
  proof -
    fix \<omega> assume "stabilize \<omega> \<in> A"
    then have "pure_larger \<omega> (stabilize \<omega>)"
      using core_is_pure decompose_stabilize_pure pure_def pure_larger_def by blast
    then show "\<omega> \<in> A"
      using \<open>stabilize \<omega> \<in> A\<close> assms(1) wf_assertion_def by blast
  qed
  then show "\<forall>\<omega>. (\<omega> \<in> A) = (stabilize \<omega> \<in> A)" using assms(2) by blast
qed


definition wf_exp where
  "wf_exp e \<longleftrightarrow> (\<forall>a b v. a \<succeq> b \<and> e b = Some v \<longrightarrow> e a = Some v) \<and> (\<forall>a. e a = e |a| )"

fun wf_abs_stmt where
  "wf_abs_stmt \<Delta> Skip \<longleftrightarrow> True"
| "wf_abs_stmt \<Delta> (Inhale A) \<longleftrightarrow> wf_assertion \<Delta> A"
| "wf_abs_stmt \<Delta> (Exhale A) \<longleftrightarrow> wf_assertion \<Delta> A"
| "wf_abs_stmt \<Delta> (Assert A) \<longleftrightarrow> wf_assertion \<Delta> A"
| "wf_abs_stmt \<Delta> (Assume A) \<longleftrightarrow> wf_assertion \<Delta> A"
| "wf_abs_stmt \<Delta> (If b C1 C2) \<longleftrightarrow> wf_exp b \<and> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (Seq C1 C2) \<longleftrightarrow> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (LocalAssign x e) \<longleftrightarrow> wf_exp e"
| "wf_abs_stmt \<Delta> (FieldAssign r e) \<longleftrightarrow> wf_exp r \<and> wf_exp e"
| "wf_abs_stmt \<Delta> (Havoc x) \<longleftrightarrow> x \<in> dom (variables \<Delta>)"
| "wf_abs_stmt \<Delta> (Label _) \<longleftrightarrow> True" (* TODO: Prevent duplicate labels? *)
| "wf_abs_stmt \<Delta> (Scope _ C) \<longleftrightarrow> wf_abs_stmt \<Delta> C" (* TODO: Update \<Delta>? *)


fun modif where
  "modif (LocalAssign x _) = {x}"
| "modif (Havoc x) = {x}"
| "modif (Seq C1 C2) = modif C1 \<union> modif C2"
| "modif (If _ C1 C2) = modif C1 \<union> modif C2"
| "modif (Scope _ C) = (\<lambda>x. x - 1) ` (Set.filter (\<lambda>x. x > 0) (modif C))" (* Shifting by one *)
| "modif _ = {}"

fun havoc_list where
  "havoc_list [] = Skip"
| "havoc_list (t # q) = Seq (Havoc t) (havoc_list q)"


subsection \<open>Assertion connectives\<close>

definition pure_Stabilize where
  "pure_Stabilize b = { \<omega> |\<omega>. b \<omega> = Some True}"

definition negate where
  "negate b \<omega> = (if b \<omega> = None then None else Some (\<not> (the (b \<omega>))))"
(*
definition astar :: "('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion"
 (infixl "&&" 60)
  where
  "(A && B) \<omega> \<longleftrightarrow> (\<exists>a b. Some \<omega> = a \<oplus> b \<and> A a \<and> B b)"


definition aconj :: "('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion"
 (infixl "\<and>\<and>" 60)
  where
    "(A \<and>\<and> B) \<omega> \<longleftrightarrow> A \<omega> \<and> B \<omega>"

definition adisj :: "('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion"
 (infixl "||" 60) where "(A || B) \<omega> \<longleftrightarrow> A \<omega> \<or> B \<omega>"
*)

section \<open>Minimal stuff\<close>

definition points_to where
  "points_to r = { \<omega> |\<omega> hl. r \<omega> = Some hl \<and> has_write_perm_only (get_state \<omega>) hl}"

definition points_to_value where
  "points_to_value r e = { \<omega> |\<omega> hl v. r \<omega> = Some hl \<and> e \<omega> = Some v \<and> has_write_perm_only (get_state \<omega>) hl \<and> has_value (get_state \<omega>) hl v}"

(*
definition atrue :: "('v, 'a) abs_state assertion" where
  "atrue \<omega> \<longleftrightarrow> True"
*)

section \<open>Something else\<close>

definition dom_vars where
  "dom_vars \<omega> = dom (get_store \<omega>)"

abbreviation univ :: "'a \<Rightarrow> ('v, 'a) abs_state set" where
  "univ r \<equiv> UNIV \<times> {r}"


definition exists_assert :: "('v, 'r) abs_type_context \<Rightarrow> var \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "exists_assert \<Delta> x A =
{ \<omega> |\<omega> v0 v ty. v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> (set_store \<omega> ((get_store \<omega>)(x \<mapsto> v))) \<in> A}"


\<comment> \<open>Hongyi defined these 3 functions for his thesis.
\<^const>\<open>framed_by_exp\<close> doesn't fully characterize the property "assertion \<^term>\<open>A\<close> frames expression \<^term>\<open>e\<close>",
in the sense that although \<^term>\<open>e (stabilize_state \<omega>)\<close> has value, it may not equal to \<^term>\<open>e \<omega>\<close>.
In addition to "frame expression" property, it also excludes evaluation error case. For example,
expression \<^term>\<open>1 / x\<close> is framed by any assertion, but atrue does not \<^const>\<open>framed_by_exp\<close>
it by definition, as there is evaluation error when \<^prop>\<open>x = 0\<close> and it evaluates to \<^const>\<open>None\<close> then.
Nevertheless, this additional characterization is also essential in defining LocalAssign rule when
choosing to do substitution in post-condition: this LocalAssign statement must reduce every state
satisfying pre-condition. As a result, every state satisfying pre-condition must evaluate the expression
\<^term>\<open>e\<close> not to \<^const>\<open>None\<close>, which is exactly characterized by \<^const>\<open>framed_by_exp\<close>. Moreover,
substitute_state should be used only when \<^prop>\<open>e \<omega> \<noteq> None\<close>. In SL rules, this is guaranteed by \<^const>\<open>framed_by_exp\<close>.
\<close>

definition assertion_frame_exp :: "('v, 'a) abs_state assertion \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> bool" where
  "assertion_frame_exp A e \<longleftrightarrow> (\<forall>\<omega> \<in> A. e \<omega> = e (stabilize \<omega>))"

definition substitute_var_state where
  "substitute_var_state x e \<omega> = assign_var_state x (e \<omega>) \<omega>"

definition post_substitute_var_assert :: "var \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "post_substitute_var_assert x e A = substitute_var_state x e ` A"

definition set_value_state :: "'r \<Rightarrow> 'v \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "set_value_state l v \<omega> = ((Ag (get_store \<omega>), Ag (get_trace \<omega>)), set_value (get_state \<omega>) l v)"

definition substitute_field_state :: "(('v, 'a) abs_state \<rightharpoonup> 'r) \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "substitute_field_state r e \<omega> = set_value_state (the (r \<omega>)) (the (e \<omega>)) \<omega>"

definition post_substitute_field_assert :: "(('v, 'a) abs_state \<rightharpoonup> 'r) \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "post_substitute_field_assert r e A = { \<omega>' |\<omega>' \<omega>. \<omega> \<in> A \<and> \<omega>' = substitute_field_state r e \<omega>}"

lemma wf_expE:
  assumes "wf_exp e"
      and "a \<succeq> b"
      and "e b = Some v"
    shows "e a = Some v"
  by (meson assms(1) assms(2) assms(3) wf_exp_def)


lemma assertion_frames_exp_eq:
  assumes "wf_exp e"
      and "self_framing A"
      and "framed_by_exp A e"
    shows "assertion_frame_exp A e"
  unfolding assertion_frame_exp_def
proof
  fix \<omega> assume asm0: "\<omega> \<in> A"
  then have "stabilize \<omega> \<in> A"
    using assms(2) self_framing_def by auto
  then obtain v where "e (stabilize \<omega>) = Some v"
    by (metis assms(3) framed_by_exp_def option.collapse)
  then show "e \<omega> = e (stabilize \<omega>)"
    by (metis (no_types, lifting) assms(1) decompose_stabilize_pure greater_def wf_expE)
qed




section \<open>SL Proof\<close>

definition depends_on_ag_store_only where
  "depends_on_ag_store_only e \<longleftrightarrow> (\<forall>\<sigma> \<gamma> \<gamma>'. e (\<sigma>, \<gamma>) = e (\<sigma>, \<gamma>'))"

inductive SL_proof :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> (('v, 'a) abs_state, 'v, 'r) abs_stmt \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> bool"
   ("_ \<turnstile> [_] _ [_]" [51,0,0] 81)
   where

  RuleSkip: "self_framing A \<Longrightarrow> _ \<turnstile> [A] Skip [A]"
\<comment>\<open>Because no frame rule, needs A on both sides.\<close>

| RuleInhale: "self_framing A \<Longrightarrow> framed_by A P \<Longrightarrow> _ \<turnstile> [A] Inhale P [A \<otimes> P]"
\<comment>\<open>P framed by A ensures that A && P is self-framing.\<close>

| RuleExhale: "self_framing B \<Longrightarrow> entails B (A \<otimes> P) \<Longrightarrow> self_framing A \<Longrightarrow> _ \<turnstile> [B] Exhale P [A]"
\<comment>\<open>Exhale can lose information, because we're forced to factorize the set, which is why the entails is needed.
Example:
{a1 + p1, a2 + p2} \<longlonglongrightarrow> {a1, a2}
<A * P> = {a1 + p1, a2 + p2, a1 + p2, a2 + p1} \<longlonglongrightarrow> {a1, a2}\<close>


| RuleAssert: "self_framing A \<Longrightarrow> entails A P \<Longrightarrow> _ \<turnstile> [A] Assert P [A]"
\<comment>\<open>Assert does not behave like exhale: It forces the *whole* heap to satisfy P.
Because there is not frame rule, it can be used to express leak checks, or absence of obligations.\<close>

| RuleHavoc: "self_framing A \<Longrightarrow> \<Delta> \<turnstile> [A] Havoc x [exists_assert \<Delta> x A]"

(*
| RuleHavoc: "self_framing A \<Longrightarrow> self_framing B \<Longrightarrow> entails A B \<Longrightarrow> free_vars \<Delta> B \<subseteq> free_vars \<Delta> A - {x} \<Longrightarrow> \<Delta> \<turnstile> [A] Havoc x [B]"
*)
\<comment>\<open>Entails needed, because we lose information. The strongest post might be \<exists>x. A, but does not seem more useful.\<close>

\<comment> \<open>
| RuleFieldAssignHeapIndep:
  "\<lbrakk> self_framing A; framed_by_exp A r; framed_by_exp A e; depends_on_ag_store_only r; depends_on_ag_store_only e \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A && points_to r] FieldAssign r e [A && points_to_value r e]"
Replaced by the new uniform one below in Hongyi's thesis.\<close>

| RuleFieldAssign: "\<lbrakk> self_framing (A \<otimes> points_to r); framed_by_exp (A \<otimes> points_to r) e; assertion_frame_exp (A \<otimes> points_to r) e \<rbrakk>
  \<Longrightarrow> _ \<turnstile> [A \<otimes> points_to r] FieldAssign r e [post_substitute_field_assert r e (A \<otimes> points_to r)]"

\<comment> \<open>Replaced to the new one above in Hongyi's thesis. The new one simply simulates reduction of this statement, with assumptions ensuring the simulation doesn't cause error.
| RuleFieldAssign: "\<lbrakk> self_framing (A && points_to_value r e') ; framed_by_exp (A && points_to r) e \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A && points_to_value r e'] FieldAssign r e [A && points_to_value r e]"\<close>



\<comment> \<open>
| RuleLocalAssign: "\<lbrakk> self_framing A; framed_by_exp A e; x \<notin> free_vars \<Delta> A \<rbrakk> \<Longrightarrow>  \<Delta> \<turnstile> [A] LocalAssign x e [ A && var_equal_exp x e ]"
Change to new one for Hongyi's thesis. The reason not to do substitution in precondition is that it is hard to express framing requirements.
Intuitively, since \<^term>\<open>e\<close> is not evaluated in post-condition, it is not reasonable to express "post-condition \<^term>\<open>A\<close> frames \<^term>\<open>e\<close>".
Assuming "A[x \<mapsto> e] frames e" makes the rule even more complicated than the one below.
Moreover, \<^prop>\<open>framed_by_exp A e\<close> doesn't work here: assume we want to have rule as "\<turnstile> {A[x \<mapsto> e]} x := e {A}",
then simply requiring \<^prop>\<open>framed_by_exp A e\<close> is wrong: due to the additional characterization of evaluation error case of \<^const>\<open>framed_by_exp\<close>,
this rule cannot express "\<turnstile> {x \<noteq> 0} x := 0/x {x = 0}" (if \<^term>\<open>A\<close> is \<^prop>\<open>x = 0\<close>,
then "0/x" always evaluates to \<^const>\<open>None\<close>, and \<^term>\<open>A\<close> can never \<^const>\<open>framed_by_exp\<close> "0/x").
Explanation of assumptions:
- To guarantee that \<^const>\<open>assign_var_state\<close> works under \<^prop>\<open>e \<omega> \<noteq> None\<close>, \<^prop>\<open>framed_by_exp A e\<close> is necessary.
- To get self-framingness of post-condition, \<^prop>\<open>assertion_frame_exp A e\<close> is necessary.
This rule is sound because: for every state \<^term>\<open>\<omega>\<close> satisfying \<^term>\<open>A\<close>. \<^term>\<open>e \<omega>\<close> evaluates to \<^term>\<open>Some v\<close>, and for the post-state \<^term>\<open>\<omega>'\<close>, the existence of \<^term>\<open>\<omega>\<close> makes it satisfy \<^term>\<open>post_substitute_assert x e A\<close>.
This rule should be complete (maybe not yet): as long as the LocalAssign statement reduces for pre-condition \<^term>\<open>A\<close>, \<^term>\<open>e\<close> must evaluate to not \<^const>\<open>None\<close> for every state in \<^term>\<open>A\<close>, thus \<^prop>\<open>framed_by_exp A e\<close>. \<^prop>\<open>assertion_frame_exp A e\<close> is a framing requirement, and a correct reduction should satisfy it.
\<close>
| RuleLocalAssign: "\<lbrakk> self_framing A; framed_by_exp A e \<rbrakk> \<Longrightarrow> _ \<turnstile> [A] LocalAssign x e [post_substitute_var_assert x e A]"

(*
  assumes "wf_exp e"
      and "self_framing A"
      and "framed_by_exp A e"
    shows "assertion_frame_exp A e"
*)



\<comment>\<open>Like inhale and the if rule, needs to frame r and e.
Interestingly, does not work if we only have
- self_framing A
- framed_by_exp A r.

Moreover, points_to_r is actually not *precise* enough.
Example: x.f.f \<mapsto> x.f

x.f == x

r := e

1) A is self-framing
2) A frames r
3) the set of states is *exactly* described by A && r \<mapsto> _


x.f := ...
--> "issue" if location of "x.f" depends on the value of x.f
--> Ok in Viper, because only depends on x, and x can be expressed through A self-framing

[e] := ...
--> "issue" if location of "e" depends on the value of e


x.f.f := ...
--> "issue" if location of "x.f.f" depends on the value of x.f.f
--> In Viper, location of "x.f.f" depends on the value of x.f
--> so, if x.f == x.f.f

State acc(x.f) && x.f == x.f.f

A fixes x
x = 0 && x.f \<mapsto> x.f.f
x = 0 && (\<exists>v. x.f \<mapsto> v /\ v

(x = 0 && 0.f \<mapsto> 0.f.f)

acc(x.f) && x.f = x
[x.f.f := ...]

Might need an entailment...\<close>

| RuleSeq: "\<lbrakk> \<Delta> \<turnstile> [A] C1 [R] ; \<Delta> \<turnstile> [R] C2 [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] Seq C1 C2 [B]"

| RuleIf: "\<lbrakk> framed_by_exp A b; \<Delta> \<turnstile> [A \<inter> pure_Stabilize b] C1 [B1] ; \<Delta> \<turnstile> [A \<inter> pure_Stabilize (negate b)] C2 [B2] \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A] If b C1 C2 [B1 \<union> B2]"

(*
| RuleFrame: "self_framing F \<Longrightarrow> \<Delta> \<turnstile> [A] C [B] \<Longrightarrow> free_var F \<inter> modif C = {} \<Longrightarrow> \<Delta> \<turnstile> [astar A F] C [astar B F]"
| RuleConsPre: "\<lbrakk> entails A' A ; self_framing A' ; \<Delta> \<turnstile> [A] C [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A'] C [B]"
| RuleConsPost: "\<lbrakk> entails B B' ; self_framing B' ; \<Delta> \<turnstile> [A] C [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] C [B']"
| RuleEquiv: "\<lbrakk> equiv A' A ; self_framing A' ; \<Delta> \<turnstile> [A] C [B]; equiv B B'; self_framing B' \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A'] C [B']"
*)


inductive_cases SL_proof_Skip_elim[elim!]: "\<Delta> \<turnstile> [A] Skip [B]"
inductive_cases SL_proof_Inhale_elim[elim!]: "\<Delta> \<turnstile> [A] Inhale P [B]"
inductive_cases SL_proof_Exhale_elim[elim!]: "\<Delta> \<turnstile> [A] Exhale P [B]"
inductive_cases SL_proof_Assert_elim[elim!]: "\<Delta> \<turnstile> [A] Assert P [B]"
inductive_cases SL_proof_Havoc_elim[elim!]: "\<Delta> \<turnstile> [A] Havoc x [B]"
inductive_cases SL_proof_FieldAssign_elim[elim!]: "\<Delta> \<turnstile> [A] FieldAssign r e [B]"
inductive_cases SL_proof_Seq_elim[elim!]: "\<Delta> \<turnstile> [A] Seq C1 C2 [B]"
inductive_cases SL_proof_If_elim[elim!]: "\<Delta> \<turnstile> [A] If b C1 C2 [B]"





definition verifies :: "('v, 'r) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 'r) abs_stmt \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> bool" where
  "verifies \<Delta> s \<omega> \<longleftrightarrow> (\<exists>S. red_stmt \<Delta> s \<omega> S)"

(* \<omega> is pure? *)
definition verifies_rel where
  "verifies_rel \<Delta> A C \<longleftrightarrow> (\<forall>\<omega> \<in> A. stable \<omega> \<longrightarrow> (\<exists>S. red_stmt \<Delta> C \<omega> S))"



end

end
