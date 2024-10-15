theory AbstractSemantics
  imports ViperCommon.DeBruijn ViperCommon.SepLogic ViperCommon.SepAlgebra ViperCommon.PartialMap ViperCommon.ViperLang ViperCommon.ViperTyping
begin

section \<open>Add a store to the state\<close>

type_synonym 'v ag_store = "(var \<rightharpoonup> 'v) agreement"
type_synonym ('v, 'a) abs_state = "'v ag_store \<times> 'a"

subsection \<open>Normal states\<close>

(* TODO: rename get_ into abs_? *)
(* TODO: Should state be renamed to heap? get_abs_state on abs_state sounds like the identity *)
(* TODO: define this via record instead of getter and setter functions? This would require proving the
class instances for the record (via isomorphism?), but one would get nice getters and setters automatically *)

definition get_store :: "('v, 'a) abs_state \<Rightarrow> (var \<rightharpoonup> 'v)" where "get_store \<omega> = the_ag (fst \<omega>)"
definition get_abs_state :: "('v, 'a) abs_state \<Rightarrow> 'a" where "get_abs_state \<omega> = snd \<omega>"
definition set_store :: "('v, 'a) abs_state \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> ('v, 'a) abs_state" where
  "set_store \<omega> s = (Ag s, get_abs_state \<omega>)"
definition set_abs_state :: "('v, 'a) abs_state \<Rightarrow> 'a \<Rightarrow> ('v, 'a) abs_state" where
  "set_abs_state \<omega> s = (Ag (get_store \<omega>), s)"

lemma get_store_set_store [simp] :
  "get_store (set_store \<omega> st) = st"
  by (simp add:get_store_def set_store_def)
lemma get_store_set_abs_state [simp] :
  "get_store (set_abs_state \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_abs_state_def)

lemma get_abs_state_set_store [simp] :
  "get_abs_state (set_store \<omega> st) = get_abs_state \<omega>"
  by (simp add:get_abs_state_def set_store_def)
lemma get_abs_state_set_abs_state [simp] :
  "get_abs_state (set_abs_state \<omega> st) = st"
  by (simp add:get_abs_state_def set_abs_state_def)

lemma get_store_stabilize[simp]:
  "get_store (stabilize \<omega>) = get_store \<omega>"
  by (metis agreement.collapse fst_conv get_store_def stabilize_ag stabilize_prod_def)
lemma set_store_stabilize[simp]:
  "set_store (stabilize \<omega>) s = stabilize (set_store \<omega> s)"
  by (simp add: get_abs_state_def set_store_def stabilize_ag stabilize_prod_def)

lemma set_store_set_store [simp] :
  "set_store (set_store \<omega> st1) st2 = set_store \<omega> st2"
  by (simp add: get_abs_state_def set_store_def)
lemma set_store_get_store [simp] :
  "set_store \<omega> (get_store \<omega>) = \<omega>"
  by (simp add: get_abs_state_def get_store_def set_store_def)

lemma ag_the_ag_same:
  "a = b \<longleftrightarrow> the_ag a = the_ag b"
  using agreement.expand by blast

lemma ag_comp:
  fixes x :: "'v agreement"
  shows "x ## y \<longleftrightarrow> x = y"
  by (simp add: defined_def plus_agreement_def)

lemma comp_prod:
  "a ## b \<longleftrightarrow> (fst a ## fst b \<and> snd a ## snd b)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain x where "Some x = a \<oplus> b"
    by (metis defined_def not_Some_eq)
  then have "Some (fst x) = fst a \<oplus> fst b \<and> Some (snd x) = snd a \<oplus> snd b"
    by (metis plus_prodE)
  then show ?B
    by (metis defined_def option.discI)
next
  assume ?B
  then obtain r1 r2 where "Some r1 = fst a \<oplus> fst b \<and> Some r2 = snd a \<oplus> snd b"
    by (metis defined_def option.exhaust_sel)
  then show ?A
    using defined_def plus_prodIAlt by fastforce
qed    

lemma get_store_trace_comp:
  "fst a ## fst b \<longleftrightarrow> get_store a = get_store b" (is "?A \<longleftrightarrow> ?B")
  by (simp add: ag_comp ag_the_ag_same comp_prod get_store_def)

lemma plus_state_def:
  "\<omega>1 \<oplus> \<omega>2 = (let r = (get_abs_state \<omega>1 \<oplus> get_abs_state \<omega>2) in
  (if get_store \<omega>1 = get_store \<omega>2 \<and> r \<noteq> None then Some (Ag (get_store \<omega>1), the r)
  else None))" (is "?A = ?B")
proof (cases "\<omega>1 \<oplus> \<omega>2")
  case None
  then have "get_abs_state \<omega>1 \<oplus> get_abs_state \<omega>2 = None \<or> get_store \<omega>1 \<noteq> get_store \<omega>2"
    by (metis comp_prod defined_def get_abs_state_def get_store_trace_comp)
  then show ?thesis
    using None by auto
next
  case (Some x)
  then have asm0: "get_store \<omega>1 = get_store \<omega>2 \<and> get_abs_state \<omega>1 \<oplus> get_abs_state \<omega>2 \<noteq> None"
    by (metis comp_prod defined_def get_store_trace_comp get_abs_state_def option.simps(3))
  then obtain r where "Some r = get_abs_state \<omega>1 \<oplus> get_abs_state \<omega>2"
    by force
  moreover have "fst \<omega>1 \<oplus> fst \<omega>2 = Some (Ag (get_store \<omega>1))"
    by (metis (no_types, opaque_lifting) agreement.exhaust_sel asm0 core_is_smaller fst_conv get_store_def get_store_trace_comp greater_def smaller_compatible_core)
  ultimately show ?thesis
    by (smt (z3) asm0 get_abs_state_def option.sel plus_prodIAlt)
qed



lemma full_core_def:
  "|\<omega>| = (Ag (get_store \<omega>),  |get_abs_state \<omega>| )"
  by (smt (verit) agreement.exhaust_sel core_def core_is_smaller fst_conv get_abs_state_def get_store_def option.discI plus_state_def snd_conv)


lemma full_add_defined:
  "\<omega>1 \<oplus> \<omega>2 \<noteq> None \<longleftrightarrow> ((get_abs_state \<omega>1) \<oplus> (get_abs_state \<omega>2) \<noteq> None \<and> get_store \<omega>1 = get_store \<omega>2)"
  using plus_state_def[of \<omega>1 \<omega>2] option.discI
  by (smt (verit, del_insts))

lemma full_add_charact:
  assumes "Some x = a \<oplus> b"
  shows "get_store x = get_store a"
      and "Some (get_abs_state x) = (get_abs_state a) \<oplus> (get_abs_state b)"
proof -
  show "get_store x = get_store a"
    by (smt (verit) agreement.exhaust_sel assms fst_conv get_store_def option.discI option.sel plus_state_def)
  show "Some (get_abs_state x) = (get_abs_state a) \<oplus> (get_abs_state b)" 
    by (smt assms get_abs_state_def option.exhaust_sel option.sel option.simps(3) plus_state_def snd_conv)
qed

lemma full_state_ext:
  assumes "get_store a = get_store b"
      and "get_abs_state a = get_abs_state b"
    shows "a = b"
  by (metis agreement.exhaust_sel assms get_abs_state_def get_store_def prod_eqI)

lemma add_defined_lift:
  fixes s :: "'v ag_store"
  assumes "Some c = a \<oplus> b"
  shows "Some (s, c) = (s, a) \<oplus> (s, b)"
proof -
  have "Some s = s \<oplus> s"
    by (simp add: plus_agreement_def)
  then show ?thesis using plus_prodIAlt assms 
    by fastforce
qed

lemma ag_store_greater:
  fixes s :: "'v ag_store"
  shows "s' \<succeq> s \<longleftrightarrow> s = s'"
  by (metis ag_comp smaller_compatible_core succ_refl)

lemma greater_charact:
  "\<omega>' \<succeq> \<omega> \<longleftrightarrow> get_store \<omega> = get_store \<omega>' \<and> get_abs_state \<omega>' \<succeq> get_abs_state \<omega>" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis (no_types, opaque_lifting) get_abs_state_def get_store_trace_comp greater_prod_eq smaller_compatible)
  assume ?B
  then have "Ag (get_store \<omega>') \<succeq> Ag (get_store \<omega>) \<and> get_abs_state \<omega>' \<succeq> get_abs_state \<omega>"
    by (simp add: succ_refl)
  then show ?A
    by (simp add: get_abs_state_def get_store_def greater_prod_eq)
qed

lemma core_charact:
  shows "get_store |\<omega>| = get_store \<omega>"
    and "get_abs_state |\<omega>| = |get_abs_state \<omega>|"
   apply (simp add: full_core_def get_store_def)
  by (simp add: full_core_def get_abs_state_def)













section Start

type_synonym 'a assertion = "'a set"

type_synonym 'a bexp = "'a \<rightharpoonup> bool"
type_synonym ('a, 'v) exp = "'a \<rightharpoonup> 'v"
type_synonym 'v abs_vtyp = "'v set"

text \<open>Types:
- 'a: State (with ag_store, trace, heap...)
- 'v: Type of values
- 'r: Custom type
\<close>

datatype ('a, 'v, 'c) abs_stmt =

\<comment>\<open>Assertions\<close>
  Inhale "'a assertion" | Exhale "'a assertion" | Assert "'a assertion" | Assume "'a assertion"

\<comment>\<open>Control structures\<close>
| If "'a bexp" "('a, 'v, 'c) abs_stmt" "('a, 'v, 'c) abs_stmt"
| Seq "('a, 'v, 'c) abs_stmt" "('a, 'v, 'c) abs_stmt" (infixl ";;" 60)

\<comment>\<open>Basic statements\<close>
| LocalAssign var "('a, 'v) exp"
| Havoc var

| Custom 'c
| Skip

record ('v, 'c) abs_type_context =
  variables :: "var \<rightharpoonup> 'v abs_vtyp"
  custom_context :: 'c

locale typed_state =
    fixes wf_custom_state :: "'c \<Rightarrow> ('a :: sep_algebra) \<Rightarrow> bool"
  assumes wf_custom_state_sum: "Some x = a \<oplus> b \<Longrightarrow> wf_custom_state \<Gamma> a \<Longrightarrow> wf_custom_state \<Gamma> b \<Longrightarrow> wf_custom_state \<Gamma> x"
      and wf_custom_state_smaller: "a \<succeq> b \<Longrightarrow> wf_custom_state \<Gamma> a \<Longrightarrow> wf_custom_state \<Gamma> b"
      and wf_custom_state_core_aux: "wf_custom_state \<Gamma> |x| \<Longrightarrow> wf_custom_state \<Gamma> x"
begin

definition typed_store :: "('v, 'c) abs_type_context \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "typed_store \<Delta> \<sigma> \<longleftrightarrow> store_typed (variables \<Delta>) \<sigma>"


lemma typed_storeI:
  assumes "dom (variables \<Delta>) = dom \<sigma>"
      and "\<And>x v ty. \<sigma> x = Some v \<Longrightarrow> variables \<Delta> x = Some ty \<Longrightarrow> v \<in> ty"
    shows "typed_store \<Delta> \<sigma>"
  using assms(1) assms(2) typed_store_def store_typed_def by meson

lemma wf_custom_state_core: "wf_custom_state \<Gamma> |x| \<longleftrightarrow> wf_custom_state \<Gamma> x"
  using max_projection_prop_pure_core mpp_smaller wf_custom_state_core_aux wf_custom_state_smaller by blast



definition typed_exp where
  "typed_exp ty e \<longleftrightarrow> (\<forall>\<omega> v. e \<omega> = Some v \<longrightarrow> v \<in> ty)"

definition filter_dom where
  "filter_dom vars S = Set.filter (\<lambda>\<omega>. dom (get_store \<omega>) = vars) S"

subsection \<open>Typed stuff\<close>

subsection \<open>States\<close>

definition typed where
  "typed \<Delta> \<omega> \<longleftrightarrow> typed_store \<Delta> (get_store \<omega>) \<and> wf_custom_state (custom_context \<Delta>) (get_abs_state \<omega>)"

definition wf_state where
  "wf_state \<Delta> \<omega> \<longleftrightarrow> (stable \<omega> \<and> typed \<Delta> \<omega>)"

lemma typed_then_stabilize_typed:
  assumes "typed \<Delta> \<omega>"
  shows "typed \<Delta> (stabilize \<omega>)"
  by (metis (no_types, lifting) assms greater_charact max_projection_prop_def max_projection_prop_stable_stabilize typed_def wf_custom_state_smaller)

lemma typed_state_then_stabilize_typed:
  assumes "typed \<Delta> \<omega>"
  shows "typed \<Delta> (stabilize \<omega>)"
  by (smt (verit, best) assms greater_charact max_projection_prop_stable_stabilize mpp_smaller typed_def wf_custom_state_smaller)

lemma typed_sum:
  assumes "Some x = a \<oplus> b"
      and "typed \<Delta> a"
      and "typed \<Delta> b"
    shows "typed \<Delta> x"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) full_add_charact(1) full_add_charact(2) typed_def wf_custom_state_sum)

lemma typed_core:
  assumes "typed \<Delta> a"
  shows "typed \<Delta> |a|"
  by (metis assms core_charact(1) core_charact(2) typed_def wf_custom_state_core)

lemma typed_smaller:
  assumes "typed \<Delta> \<omega>'"
      and "\<omega>' \<succeq> \<omega>"
    shows "typed \<Delta> \<omega>"
  by (metis assms(1) assms(2) greater_charact typed_def wf_custom_state_smaller)

subsection \<open>Assertions\<close>

definition wf_set where
  "wf_set \<Delta> S \<longleftrightarrow> (\<forall>x \<in> S. wf_state \<Delta> x)"

definition assign_var_state :: "var \<Rightarrow> 'v option \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "assign_var_state x v \<omega> = set_store \<omega> ((get_store \<omega>)(x := v))"

lemma assign_var_state_stable:
  "stable \<omega> \<longleftrightarrow> stable (assign_var_state x v \<omega>)"
  by (metis (no_types, lifting) already_stable assign_var_state_def full_state_ext get_abs_state_set_store get_store_stabilize set_store_stabilize stabilize_is_stable)

lemma assign_var_state_stabilize:
  "stabilize (assign_var_state x v \<omega>) = assign_var_state x v (stabilize \<omega>)"
  by (simp add: assign_var_state_def)

lemma typed_assign_var:
  assumes "typed \<Delta> \<omega>"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
    shows "typed \<Delta> (assign_var_state x (Some v) \<omega>)"
  using assms unfolding  assign_var_state_def typed_def
  by (smt (verit, del_insts) dom_fun_upd get_abs_state_set_store get_store_set_store insert_dom map_upd_Some_unfold option.discI typed_store_def store_typed_def)



section \<open>Free variables\<close>

definition equal_on_set :: "var set \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "equal_on_set S \<sigma>1 \<sigma>2 \<longleftrightarrow> (\<forall>x \<in> S. \<sigma>1 x = \<sigma>2 x)"

definition overapprox_fv :: "('v, 'c) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> var set \<Rightarrow> bool" where
  "overapprox_fv \<Delta> A S \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2 \<gamma>. typed \<Delta> (Ag \<sigma>1, \<gamma>) \<and> typed \<Delta> (Ag \<sigma>2, \<gamma>) \<and> equal_on_set S \<sigma>1 \<sigma>2 \<longrightarrow> ((Ag \<sigma>1, \<gamma>) \<in> A \<longleftrightarrow> (Ag \<sigma>2, \<gamma>) \<in> A))"


definition free_vars where
  "free_vars \<Delta> A = (\<Inter>S \<in> {S. overapprox_fv \<Delta> A S}. S)"


text \<open>Works only if (dom \<Delta>) is finite.\<close>

definition at_least_two_elems:
  "at_least_two_elems S \<longleftrightarrow> (\<exists>a b. a \<in> S \<and> b \<in> S \<and> a \<noteq> b)"

subsection \<open>wf_assertion\<close>

definition wf_assertion :: "('v, 'a) abs_state assertion \<Rightarrow> bool" where
  "wf_assertion A \<longleftrightarrow> (\<forall>x' x. pure_larger x' x \<and> x \<in> A \<longrightarrow> x' \<in> A)"

lemma wf_assertionI:
  assumes "\<And>x' x. pure_larger x' x \<Longrightarrow> x \<in> A \<Longrightarrow> x' \<in> A"
  shows "wf_assertion A"
  using assms wf_assertion_def by blast

lemma wf_assertionE:
  assumes "wf_assertion A"
      and "pure_larger x' x"
      and "x \<in> A"
    shows "x' \<in> A"
  using assms(1) assms(2) assms(3) wf_assertion_def by blast


definition exists_assert :: "('v, 'c) abs_type_context \<Rightarrow> var \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "exists_assert \<Delta> x A =
{ \<omega> |\<omega> v0 v ty. v0 \<in> ty \<and> get_store \<omega> x = Some v0 \<and> variables \<Delta> x = Some ty \<and> v \<in> ty \<and> assign_var_state x (Some v) \<omega> \<in> A}"


lemma in_exists_assert:
  assumes "v0 \<in> ty"
      and "get_store \<omega> x = Some v0"
      and "variables \<Delta> x = Some ty"
      and "v \<in> ty"
      and "assign_var_state x (Some v) \<omega> \<in> A"
    shows "\<omega> \<in> exists_assert \<Delta> x A"  
  using assms(1) assms(2) assms(3) assms(4) assms(5) exists_assert_def by fastforce


definition stable_on where
  "stable_on \<omega> A \<longleftrightarrow> (\<forall>x. pure_larger x \<omega> \<longrightarrow> (\<omega> \<in> A \<longleftrightarrow> x \<in> A))"

lemma stable_onI:
  assumes "\<And>x. pure_larger x \<omega> \<Longrightarrow> (\<omega> \<in> A \<longleftrightarrow> x \<in> A)"
  shows "stable_on \<omega> A"
  using assms stable_on_def by blast

end







section \<open>Semantics\<close>

locale semantics =
  typed_state wf_custom_state for wf_custom_state :: "'c \<Rightarrow> ('a :: sep_algebra) \<Rightarrow> bool" +
  
  fixes red_custom_stmt :: "('v, 'c) abs_type_context \<Rightarrow> 's \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
  fixes wf_custom_stmt :: "('v, 'c) abs_type_context \<Rightarrow> 's \<Rightarrow> bool"
  fixes SL_Custom :: "('v, 'c) abs_type_context \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> 's \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"

  assumes SL_proof_custom: "(\<forall>(\<omega> :: (('v, 'a) abs_state list \<times> ('v, 'a) abs_state)) \<in> SA.
  red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)) \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> wf_set \<Delta> (snd ` SA)
  \<Longrightarrow> SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union>\<omega>\<in>SA. f \<omega>))"

      and red_custom_stable: "red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> stable \<omega> \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> stable \<omega>'"
      and red_custom_typed_store: "red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> typed_store \<Delta> (get_store \<omega>)
  \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> typed_store \<Delta> (get_store \<omega>')"

      and red_wf_custom: "red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> wf_custom_state (custom_context \<Delta>) (get_abs_state \<omega>) \<Longrightarrow>
        wf_custom_stmt \<Delta> C \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> wf_custom_state (custom_context \<Delta>) (get_abs_state \<omega>')"

      and red_wf_complete: "SL_Custom \<Delta> A C B \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> stable \<omega>
          \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> (\<exists>S. red_custom_stmt \<Delta> C \<omega> S \<and> S \<subseteq> B)"

begin

section \<open>Operational semantics\<close>

inductive red_stmt :: "('v, 'c) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 's) abs_stmt \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
  and sequential_composition :: "('v, 'c) abs_type_context \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> (('v, 'a) abs_state, 'v, 's) abs_stmt \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
where

\<comment>\<open>f maps each x to one possible final set of states: It performs the angelic choice\<close>
  SeqComp: "\<lbrakk> \<And>\<omega>. \<omega> \<in> S \<Longrightarrow> (red_stmt \<Delta> C \<omega> (f \<omega>)) ; S' = Union (f ` S) \<rbrakk> \<Longrightarrow> sequential_composition \<Delta> S C S'"

| RedSkip: "red_stmt \<Delta> Skip \<omega> ({\<omega>})"

| RedAssertTrue: "\<lbrakk> \<omega> \<in> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assert A) \<omega> ({\<omega>})"
| RedAssumeTrue: "\<lbrakk> stable_on \<omega> A; \<omega> \<in> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assume A) \<omega> ({\<omega>})"
| RedAssumeFalse: "\<lbrakk> stable_on \<omega> A; \<omega> \<notin> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Assume A) \<omega> ({})"

| RedInhale: "\<lbrakk> rel_stable_assertion \<omega> A \<rbrakk> \<Longrightarrow> red_stmt \<Delta> (Inhale A) \<omega> (Set.filter (\<lambda>\<omega>. stable \<omega> \<and> typed \<Delta> \<omega>) ({\<omega>} \<otimes> A))"

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

| RedCustom: "red_custom_stmt \<Delta> C \<omega> S \<Longrightarrow> red_stmt \<Delta> (Custom C) \<omega> S"

(*
\<comment>\<open>Updated type context\<close>
| RedScope: "\<lbrakk> variables \<Delta> x = None; \<Delta>' = \<Delta>\<lparr> variables := (variables \<Delta>)(x \<mapsto> ty) \<rparr>;
sequential_composition \<Delta> { assign_var_state x (Some v) \<omega> |v. v \<in> ty } C S' \<rbrakk>
\<Longrightarrow> red_stmt \<Delta> (Scope ty s) \<omega> {assign_var_state x None \<omega> |\<omega>. \<omega> \<in> S'}"
*)





inductive_cases sequential_composition_elim[elim!]: "sequential_composition \<Delta> S C S'"
inductive_cases red_stmt_Seq_elim[elim!]: "red_stmt \<Delta> (Seq C1 C2) \<omega> S"
inductive_cases red_stmt_Inhale_elim[elim!]: "red_stmt \<Delta> (Inhale A) \<omega> S"
inductive_cases red_stmt_Exhale_elim[elim!]: "red_stmt \<Delta> (Exhale A) \<omega> S"
inductive_cases red_stmt_Skip_elim[elim!]: "red_stmt \<Delta> Skip \<omega> S"
inductive_cases red_stmt_Havoc_elim[elim!]: "red_stmt \<Delta> (Havoc x) \<omega> S"
inductive_cases red_stmt_Assign_elim[elim!]: "red_stmt \<Delta> (LocalAssign x e) \<omega> S"
inductive_cases red_stmt_If_elim[elim!]: "red_stmt \<Delta> (If b C1 C2) \<omega> S"
inductive_cases red_stmt_Assert_elim[elim!]: "red_stmt \<Delta> (Assert A) \<omega> S"
inductive_cases red_stmt_Assume_elim[elim!]: "red_stmt \<Delta> (Assume A) \<omega> S"
inductive_cases red_stmt_Custom_elim[elim!]: "red_stmt \<Delta> (Custom C) \<omega> S"





section \<open>Assertions\<close>

subsection \<open>General concepts\<close>


fun modif where
  "modif (LocalAssign x _) = {x}"
| "modif (Havoc x) = {x}"
| "modif (Seq C1 C2) = modif C1 \<union> modif C2"
| "modif (If _ C1 C2) = modif C1 \<union> modif C2"
| "modif _ = {}"


fun wf_abs_stmt :: "('v, 'c) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 's) abs_stmt \<Rightarrow> bool" 
  where
  "wf_abs_stmt \<Delta> Skip \<longleftrightarrow> True"
| "wf_abs_stmt \<Delta> (Inhale A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Exhale A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Assert A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (Assume A) \<longleftrightarrow> wf_assertion A"
| "wf_abs_stmt \<Delta> (If b C1 C2) \<longleftrightarrow> wf_exp b \<and> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (Seq C1 C2) \<longleftrightarrow> wf_abs_stmt \<Delta> C1 \<and> wf_abs_stmt \<Delta> C2"
| "wf_abs_stmt \<Delta> (LocalAssign x e) \<longleftrightarrow> wf_exp e \<and> (\<exists>ty. variables \<Delta> x = Some ty \<and> typed_exp ty e)"
| "wf_abs_stmt \<Delta> (Havoc x) \<longleftrightarrow> x \<in> dom (variables \<Delta>)"
| "wf_abs_stmt \<Delta> (Custom C) \<longleftrightarrow> wf_custom_stmt \<Delta> C"

fun havoc_list where
  "havoc_list [] = Skip"
| "havoc_list (t # q) = Seq (Havoc t) (havoc_list q)"

section \<open>Free variables\<close>

definition dom_vars where
  "dom_vars \<omega> = dom (get_store \<omega>)"

abbreviation univ :: "'a \<Rightarrow> ('v, 'a) abs_state set" where
  "univ r \<equiv> UNIV \<times> {r}"


definition substitute_var_state where
  "substitute_var_state x e \<omega> = assign_var_state x (e \<omega>) \<omega>"

definition post_substitute_var_assert :: "var \<Rightarrow> (('v, 'a) abs_state, 'v) exp \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> ('v, 'a) abs_state assertion" where
  "post_substitute_var_assert x e A = substitute_var_state x e ` A"



section \<open>Axiomatic Semantics\<close>

definition purify where
  "purify b = { \<omega> |\<omega>. b \<omega> = Some True \<and> pure \<omega> }"

inductive SL_proof :: "('v, 'c) abs_type_context \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> (('v, 'a) abs_state, 'v, 's) abs_stmt \<Rightarrow> ('v, 'a) abs_state assertion \<Rightarrow> bool"
   ("_ \<turnstile> [_] _ [_]" [51,0,0] 81)
   where

  RuleSkip: "self_framing A \<Longrightarrow> \<Delta> \<turnstile> [A] Skip [A]"
\<comment>\<open>Because no frame rule, needs A on both sides.\<close>

| RuleInhale: "self_framing A \<Longrightarrow> framed_by A P \<Longrightarrow> \<Delta> \<turnstile> [A] Inhale P [A \<otimes> Set.filter (typed \<Delta> \<circ> stabilize) P]"
\<comment>\<open>P framed by A ensures that A && P is self-framing.\<close>

| RuleExhale: "self_framing B \<Longrightarrow> entails B (A \<otimes> P) \<Longrightarrow> self_framing A \<Longrightarrow> \<Delta> \<turnstile> [B] Exhale P [A]"

\<comment>\<open>Exhale can lose information, because we're forced to factorize the set, which is why the entails is needed.
Example:
{a1 + p1, a2 + p2} \<longlonglongrightarrow> {a1, a2}
<A * P> = {a1 + p1, a2 + p2, a1 + p2, a2 + p1} \<longlonglongrightarrow> {a1, a2}\<close>

| RuleAssert: "self_framing A \<Longrightarrow> entails A P \<Longrightarrow> \<Delta> \<turnstile> [A] Assert P [A]"
\<comment>\<open>Assert does not behave like exhale: It forces the *whole* heap to satisfy P.
Because there is not frame rule, it can be used to express leak checks, or absence of obligations.\<close>

| RuleAssume: "self_framing A \<Longrightarrow> self_framing_on A P \<Longrightarrow> \<Delta> \<turnstile> [A] Assume P [A \<inter> P]"

| RuleHavoc: "self_framing A \<Longrightarrow> \<Delta> \<turnstile> [A] Havoc x [exists_assert \<Delta> x A]"

| RuleLocalAssign: "\<lbrakk> self_framing A; framed_by_exp A e \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] LocalAssign x e [post_substitute_var_assert x e A]"

| RuleSeq: "\<lbrakk> \<Delta> \<turnstile> [A] C1 [R] ; \<Delta> \<turnstile> [R] C2 [B] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] Seq C1 C2 [B]"

| RuleIf: "\<lbrakk> self_framing A; framed_by_exp A b; \<Delta> \<turnstile> [A \<otimes> purify b] C1 [B1] ; \<Delta> \<turnstile> [A \<otimes> purify (negate b)] C2 [B2] \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A] If b C1 C2 [B1 \<union> B2]"

| RuleCustom: "\<lbrakk> self_framing A; self_framing B; SL_Custom \<Delta> A C B \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] Custom C [B]"

inductive_cases SL_proof_Skip_elim[elim!]: "\<Delta> \<turnstile> [A] Skip [B]"
inductive_cases SL_proof_Inhale_elim[elim!]: "\<Delta> \<turnstile> [A] Inhale P [B]"
inductive_cases SL_proof_Exhale_elim[elim!]: "\<Delta> \<turnstile> [A] Exhale P [B]"
inductive_cases SL_proof_Assert_elim[elim!]: "\<Delta> \<turnstile> [A] Assert P [B]"
inductive_cases SL_proof_Havoc_elim[elim!]: "\<Delta> \<turnstile> [A] Havoc x [B]"
inductive_cases SL_proof_Seq_elim[elim!]: "\<Delta> \<turnstile> [A] Seq C1 C2 [B]"
inductive_cases SL_proof_If_elim[elim!]: "\<Delta> \<turnstile> [A] If b C1 C2 [B]"
inductive_cases SL_proof_Custom_elim[elim!]: "\<Delta> \<turnstile> [A] Custom C [B]"
inductive_cases SL_proof_LocalAssign_elim[elim!]: "\<Delta> \<turnstile> [A] LocalAssign x e [B]"


definition verifies :: "('v, 'c) abs_type_context \<Rightarrow> (('v, 'a) abs_state, 'v, 's) abs_stmt \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> bool" where
  "verifies \<Delta> C \<omega> \<longleftrightarrow> (\<exists>S. red_stmt \<Delta> C \<omega> S)"

definition verifies_set where
  "verifies_set \<Delta> A C \<longleftrightarrow> (\<forall>\<omega> \<in> A. stable \<omega> \<and> typed \<Delta> \<omega> \<longrightarrow> verifies \<Delta> C \<omega>)"

lemma verifies_setI :
  assumes "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> stable \<omega> \<Longrightarrow> typed \<Delta> \<omega> \<Longrightarrow> verifies \<Delta> C \<omega>"
  shows "verifies_set \<Delta> A C"
  using assms unfolding verifies_set_def by (auto)

end

end
