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

(* Axioms
- TODO: Add smth about has_value
*)

(* Needed? *)
  assumes frame_preserving_writing_orig: "Some x = a \<oplus> b \<Longrightarrow> stable b \<Longrightarrow> has_write_perm_only a hl \<Longrightarrow> Some (set_value x hl v) = set_value a hl v \<oplus> b"
      and has_write_perm_only_same: "has_write_perm_only a hl \<Longrightarrow> has_write_perm_only b hl \<Longrightarrow> stabilize a = stabilize b"
  (* TODO: WRONG! Needs something about the value! *)

      and set_value_then_has_value: "has_write_perm_only a hl \<Longrightarrow> has_value (set_value a hl v) hl v"

begin


(* Needed:
- Checking perm(x.f) = 1
- Setting x.f := 5
- Checking x.f = something
 *)

definition has_write_perm :: "'a \<Rightarrow> 'r \<Rightarrow> bool" where
  "has_write_perm x hl \<longleftrightarrow> (\<exists>r. x \<succeq> r \<and> has_write_perm_only r hl)"

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

text \<open>The truth of A in a only depends on parts of a (for a ## \<omega>) that:
1) are stable, or
2) are given by |\<omega>|\<close>
definition rel_stable_assertion where
(*  "rel_stable_assertion \<omega> A \<longleftrightarrow> (\<forall>\<omega>'. \<omega> ## \<omega>' \<longrightarrow> (A \<omega>' \<longleftrightarrow> A (stabilize_rel \<omega> \<omega>')))" *)
  "rel_stable_assertion \<omega> A \<longleftrightarrow> (\<forall>x a. \<omega> ## a \<and> pure_larger x (stabilize a) \<and> x \<succeq> |\<omega>| \<longrightarrow> (a \<in> A \<longleftrightarrow> x \<in> A))"
(* TODO: Think about it *)

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

| RedIfTrue: "\<lbrakk> b \<omega> = Some True ; red_stmt \<Delta> C1 \<omega> S \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (If b C1 C2) \<omega> S"
| RedIfFalse: "\<lbrakk> b \<omega> = Some False ; red_stmt \<Delta> C2 \<omega> S \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (If b C1 C2) \<omega> S"

| RedSeq: "\<lbrakk> red_stmt \<Delta> C1 \<omega> S1 ; sequential_composition \<Delta> S1 C2 S2 \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (C1 ;; C2) \<omega> S2"

\<comment>\<open>No need to handle the case where the variable is not defined, since it is part of well-definedness of a program\<close>
| RedLocalAssign: "\<lbrakk>variables \<Delta> x = Some ty; e \<omega> = Some v; v \<in> ty \<rbrakk> \<Longrightarrow>
   red_stmt \<Delta> (LocalAssign x e) \<omega> ({set_store \<omega> ((get_store \<omega>)(x := Some v)) })"


| RedHavoc: "variables \<Delta> x = Some ty \<Longrightarrow>
  red_stmt \<Delta> (Havoc x) \<omega> ({set_store \<omega> ((get_store \<omega>)(x := Some v)) |v. v \<in> ty})"

| RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; has_write_perm (get_state \<omega>) hl; heap_locs \<Delta> hl = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_stmt \<Delta> (FieldAssign r e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) hl v)}"

| RedLabel: "red_stmt \<Delta> (Label l) \<omega> {set_trace \<omega> ((get_trace \<omega>)(l:= Some (get_state \<omega>)))}"


(*

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


definition typed_store :: "('v, 'r) abs_type_context \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "typed_store \<Delta> \<sigma> \<longleftrightarrow> (dom (variables \<Delta>) = dom \<sigma> \<and> (\<forall>x v ty. \<sigma> x = Some v \<and> variables \<Delta> x = Some ty \<longrightarrow> v \<in> ty))"

section \<open>Assertions\<close>

subsection \<open>General concepts\<close>

definition framed_by :: "('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "framed_by A B \<longleftrightarrow> (\<forall>\<omega> \<in> A. stable \<omega> \<longrightarrow> rel_stable_assertion \<omega> B)"

definition wf_exp where
  "wf_exp e \<longleftrightarrow> (\<forall>a b v. a \<succeq> b \<and> e b = Some v \<longrightarrow> e a = Some v) \<and> (\<forall>a. e a = e |a| )"

definition framed_by_exp where
  "framed_by_exp A e \<longleftrightarrow> (\<forall>\<omega> \<in> A. e \<omega> \<noteq> None)"

definition entails where
  "entails A B \<longleftrightarrow> A \<subseteq> B"

definition equiv where
  "equiv A B \<longleftrightarrow> A = B"



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
(*
(* TODO: Is it needed? *)
definition wf_assertion :: "('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "wf_assertion A \<longleftrightarrow> (\<forall>x' x. pure_larger x' x \<and> A x \<longrightarrow> A x')"

fun wf_abs_stmt where
  "wf_abs_stmt \<Delta> Skip \<longleftrightarrow> True"
| "wf_abs_stmt \<Delta> (Inhale A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Exhale A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Assert A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Assume A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (If b C1 C2) \<longleftrightarrow> wf_exp b \<and> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (Seq C1 C2) \<longleftrightarrow> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (LocalAssign x e) \<longleftrightarrow> wf_exp e"
| "wf_abs_stmt \<Delta> (FieldAssign r e) \<longleftrightarrow> wf_exp r \<and> wf_exp e"
| "wf_abs_stmt \<Delta> (Havoc x) \<longleftrightarrow> x \<in> dom (variables \<Delta>)"
| "wf_abs_stmt \<Delta> (Label _) \<longleftrightarrow> True" (* TODO: Prevent duplicate labels? *)
| "wf_abs_stmt \<Delta> (Scope _ C) \<longleftrightarrow> wf_abs_stmt \<Delta> C" (* TODO: Prevent duplicate labels? *)
*)

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
  "pure_Stabilize b \<omega> \<longleftrightarrow> b \<omega> = Some True"

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
{ \<omega> |\<omega> v0 v ty. v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> ((Ag ((get_store \<omega>)(x := Some v)), Ag (get_trace \<omega>)), get_state \<omega>) \<in> A}"





\<comment> \<open>Hongyi defined these 3 functions for his thesis.
\<^const>\<open>framed_by_exp\<close> doesn't fully characterize the property "assertion \<^term>\<open>A\<close> frames expression \<^term>\<open>e\<close>",
in the sense that although \<^term>\<open>e (stabilize_state \<omega>)\<close> has value, it may not equal to \<^term>\<open>e \<omega>\<close>.
In addition to "frame expression" property, it also excludes evaluation error case. For example,
expression \<^term>\<open>1 / x\<close> is framed by any assertion, but \<^const>\<open>atrue\<close> does not \<^const>\<open>framed_by_exp\<close>
it by definition, as there is evaluation error when \<^prop>\<open>x = 0\<close> and it evaluates to \<^const>\<open>None\<close> then.
Nevertheless, this additional characterization is also essential in defining LocalAssign rule when
choosing to do substitution in post-condition: this LocalAssign statement must reduce every state
satisfying pre-condition. As a result, every state satisfying pre-condition must evaluate the expression
\<^term>\<open>e\<close> not to \<^const>\<open>None\<close>, which is exactly characterized by \<^const>\<open>framed_by_exp\<close>. Moreover,
substitute_state should be used only when \<^prop>\<open>e \<omega> \<noteq> None\<close>. In SL rules, this is guaranteed by \<^const>\<open>framed_by_exp\<close>.
\<close>

definition assertion_frame_exp :: "('v, 'a) abs_state assertion \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> bool" where
  "assertion_frame_exp A e \<longleftrightarrow> (\<forall>\<omega> \<in> A. e \<omega> = e (stabilize \<omega>))"

definition substitute_var_state :: "var \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "substitute_var_state x e \<omega> = ((Ag ((get_store \<omega>)(x := e \<omega>)), Ag (get_trace \<omega>)), get_state \<omega>)"

definition post_substitute_var_assert :: "var \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "post_substitute_var_assert x e A = { \<omega>' |\<omega> \<omega>'. \<omega> \<in> A \<and> \<omega>' = substitute_var_state x e \<omega>}"

definition set_value_state :: "'r \<Rightarrow> 'v \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "set_value_state l v \<omega> = ((Ag (get_store \<omega>), Ag (get_trace \<omega>)), set_value (get_state \<omega>) l v)"

definition substitute_field_state :: "(('v, 'a) abs_state \<rightharpoonup> 'r) \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "substitute_field_state r e \<omega> = set_value_state (the (r \<omega>)) (the (e \<omega>)) \<omega>"

definition post_substitute_field_assert :: "(('v, 'a) abs_state \<rightharpoonup> 'r) \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "post_substitute_field_assert r e A = { \<omega>' |\<omega>' \<omega>. \<omega> \<in> A \<and> \<omega>' = substitute_field_state r e \<omega>}"









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
(*
| RuleIf: "\<lbrakk> framed_by_exp A b; \<Delta> \<turnstile> [A \<and>\<and> (pure_Stabilize b)] C1 [B1] ; \<Delta> \<turnstile> [A \<and>\<and> (pure_Stabilize (negate b))] C2 [B2] \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A] If b C1 C2 [B1 || B2]"
*)


(*
| RuleFrame: "self_framing F \<Longrightarrow> \<Delta> \<turnstile> [A] C [B] \<Longrightarrow> free_var F \<inter> modif C = {} \<Longrightarrow> \<Delta> \<turnstile> [astar A F] C [astar B F]"
| RuleConsPre: "\<lbrakk> entails A' A ; self_framing A' ; \<Delta> \<turnstile> [A] C [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A'] C [B]"
| RuleConsPost: "\<lbrakk> entails B B' ; self_framing B' ; \<Delta> \<turnstile> [A] C [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] C [B']"
| RuleEquiv: "\<lbrakk> equiv A' A ; self_framing A' ; \<Delta> \<turnstile> [A] C [B]; equiv B B'; self_framing B' \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A'] C [B']"
*)

definition wf_state where
  "wf_state \<Delta> \<omega> \<longleftrightarrow> (stable \<omega> \<and> typed_store \<Delta> (get_store \<omega>))"

definition wf_set where
  "wf_set \<Delta> S \<longleftrightarrow> (\<forall>x \<in> S. wf_state \<Delta> x)"


definition verifies :: "('v, 'r) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 'r) abs_stmt \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> bool" where
  "verifies \<Delta> s \<omega> \<longleftrightarrow> (\<exists>S. red_stmt \<Delta> s \<omega> S)"

(* \<omega> is pure? *)
definition verifies_rel where
  "verifies_rel \<Delta> A C \<longleftrightarrow> (\<forall>\<omega> \<in> \<langle>A\<rangle>. stable \<omega> \<longrightarrow> (\<exists>S. red_stmt \<Delta> C \<omega> S))"



end

end
