section \<open>Viper State with a Total Heap\<close>

theory TotalViperState
imports Viper.ValueAndBasicState Viper.SepAlgebra
begin

type_synonym 'a total_heap = "heap_loc \<Rightarrow> 'a val"
type_synonym 'a predicate_mask = "'a predicate_loc \<Rightarrow> prat"

text \<open>For each predicate instance, the state tracks the heap snapshot represented as a subset of
heap locations and predicate locations. The values of the heap locations are given by the 
corresponding total heap\<close>

type_synonym 'a predicate_heap = "'a predicate_loc \<Rightarrow> heap_loc set \<times> 'a predicate_loc set"

type_synonym 'a pre_total_state = 
  "('a total_heap \<times> 'a predicate_heap) \<times> (mask \<times> 'a predicate_mask)"

text \<open> We use the following naming scheme:

hh: heap for heap locations
hp: heap for predicate locations
h: hh and hp together (e.g., (hh,hp))

mh: permission mask for heap locations
mp: permission mask for predicate locations
m: mh and mp together (e.g., (mh,mp))

lh: heap location
lp: predicate location
\<close>

fun get_lhset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> heap_loc set"
  where "get_lhset_pheap hp lp = fst (hp lp)"

fun get_lpset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a predicate_loc set"
  where "get_lpset_pheap hp lp = snd (hp lp)"

fun get_h_pre_total :: "'a pre_total_state \<Rightarrow> 'a total_heap \<times> 'a predicate_heap"
  where "get_h_pre_total \<phi> = fst \<phi>"

fun get_hh_pre_total :: "'a pre_total_state \<Rightarrow> 'a total_heap"
  where "get_hh_pre_total \<phi> = fst (get_h_pre_total \<phi>)"

fun get_hp_pre_total :: "'a pre_total_state \<Rightarrow> 'a predicate_heap"
  where "get_hp_pre_total \<phi> = snd (get_h_pre_total \<phi>)"

fun get_m_pre_total :: "'a pre_total_state \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_pre_total \<phi> = snd \<phi>"

fun get_mh_pre_total :: "'a pre_total_state \<Rightarrow> mask"
  where "get_mh_pre_total \<phi> = fst (get_m_pre_total \<phi>)"

fun get_mp_pre_total :: "'a pre_total_state \<Rightarrow> 'a predicate_mask"
  where "get_mp_pre_total \<phi> = snd (get_m_pre_total \<phi>)"

fun wf_pre_total_state :: "'a pre_total_state \<Rightarrow> bool" where
  "wf_pre_total_state \<phi> \<longleftrightarrow> wf_mask_simple (fst (get_m_pre_total \<phi>))"

(* TODO: Does it make sense to use a typedef here given that we can't express the entire state consistency
here? *)
typedef 'a total_state = "{ \<phi> :: 'a pre_total_state |\<phi>. wf_pre_total_state \<phi> }"
  apply (rule_tac x="((\<lambda>hl. VInt 0, \<lambda>p. ({},{})), (zero_mask, zero_mask))" in exI)
  apply (simp add: wf_zero_mask)
  done

setup_lifting type_definition_total_state

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)
type_synonym 'a full_total_state = "'a store \<times> 'a total_trace \<times> 'a total_state"

section \<open>Destructors for (full) total state\<close>

(*lift_definition get_heap_total :: "'a total_state \<Rightarrow> 'a total_heap" is "snd" done*)
(*fun get_m_total :: "'a total_stateotal_full  \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total \<phi> = get_m_pre_total (Rep_total_state \<phi>)"*)

subsection \<open>Heap destructors total state\<close>

fun get_h_total :: "'a total_state \<Rightarrow> 'a total_heap \<times> 'a predicate_heap" 
  where "get_h_total \<phi> = get_h_pre_total (Rep_total_state \<phi>)"

fun get_hh_total :: "'a total_state \<Rightarrow> 'a total_heap" 
  where "get_hh_total \<phi> = get_hh_pre_total (Rep_total_state \<phi>)"

fun get_hp_total :: "'a total_state \<Rightarrow> 'a predicate_heap" 
  where "get_hp_total \<phi> = get_hp_pre_total (Rep_total_state \<phi>)"

lemma get_hh_from_h_total: "get_hh_total \<phi> = fst (get_h_total \<phi>)"
  by simp

lemma get_hp_from_h_total: "get_hp_total \<phi> = snd (get_h_total \<phi>)"
  by simp

subsection \<open>Mask destructors total state\<close>

fun get_m_total :: "'a total_state \<Rightarrow> mask \<times> 'a predicate_mask" 
  where "get_m_total \<phi> = get_m_pre_total (Rep_total_state \<phi>)"

fun get_mh_total :: "'a total_state \<Rightarrow> mask" 
  where "get_mh_total \<phi> = get_mh_pre_total (Rep_total_state \<phi>)"

fun get_mp_total :: "'a total_state \<Rightarrow> 'a predicate_mask" 
  where "get_mp_total \<phi> = get_mp_pre_total (Rep_total_state \<phi>)"

lemma get_mask_total_wf: "wf_mask_simple (get_mh_total \<phi>)"
  using Rep_total_state by auto

lemma get_m_mh_mp_total: "get_m_total \<phi> = (get_mh_total \<phi>, get_mp_total \<phi>)"
  by simp

lemma get_mh_from_m_total: "get_mh_total \<phi> = fst (get_m_total \<phi>)"
  by simp

lemma get_mp_from_m_total: "get_mp_total \<phi> = snd (get_m_total \<phi>)"
  by simp

subsection \<open>Top-level constructors full total state\<close>

fun get_store_total :: "'a full_total_state \<Rightarrow> 'a store" 
  where "get_store_total \<omega> = fst \<omega>"

fun get_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace" 
  where "get_trace_total \<omega> = fst (snd \<omega>)"

fun get_total_full :: "'a full_total_state \<Rightarrow> 'a total_state"
  where "get_total_full \<omega> = snd (snd \<omega>)"

subsection \<open>Heap destructors full total state\<close>

fun get_h_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap \<times> 'a predicate_heap"
  where "get_h_total_full \<omega> = get_h_total (get_total_full \<omega>)"

fun get_hh_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap" 
  where "get_hh_total_full \<omega> = get_hh_total (get_total_full \<omega>)"

fun get_hp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_heap" 
  where "get_hp_total_full \<omega> = get_hp_total (get_total_full \<omega>)"

lemma get_hh_from_h_total_full: "get_hh_total_full \<phi> = fst (get_h_total_full \<phi>)"
  by simp

lemma get_hp_from_h_total_full: "get_hp_total_full \<phi> = snd (get_h_total_full \<phi>)"
  by simp

subsection \<open>Mask destructors full total state\<close>

fun get_m_total_full :: "'a full_total_state \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = get_m_total (get_total_full \<omega>)"

fun get_mh_total_full :: "'a full_total_state \<Rightarrow> mask" where "get_mh_total_full \<omega> = get_mh_total (get_total_full \<omega>)"

fun get_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask" where "get_mp_total_full \<omega> = get_mp_total (get_total_full \<omega>)"

lemma get_mh_from_m_total_full: "get_mh_total_full \<phi> = fst (get_m_total_full \<phi>)"
  by simp

lemma get_mp_from_m_total_full: "get_mp_total_full \<phi> = snd (get_m_total_full \<phi>)"
  by simp

section \<open>Lemmas for proving equality of states\<close>

lemma total_mask_eq:
  assumes "get_mh_total \<phi> = get_mh_total \<phi>'" and
          "get_mp_total \<phi> = get_mp_total \<phi>'" 
  shows "get_m_total \<phi> = get_m_total \<phi>'"
  using assms
  by (metis get_m_total.simps get_mh_pre_total.simps get_mh_total.simps get_mp_pre_total.simps get_mp_total.simps surjective_pairing)

lemma total_heap_eq:
  assumes "get_hh_total \<phi> = get_hh_total \<phi>'" and
          "get_hp_total \<phi> = get_hp_total \<phi>'" 
  shows "get_h_total \<phi> = get_h_total \<phi>'"
  using assms
  by (metis get_h_total.elims get_hh_pre_total.simps get_hh_total.elims get_hp_pre_total.simps get_hp_total.elims prod_eqI)

lemma total_state_eq:
  assumes "get_m_total \<phi> = get_m_total \<phi>'" and
          "get_h_total \<phi> = get_h_total \<phi>'"
  shows "\<phi> = \<phi>'"
  using assms
  by (metis Rep_total_state_inverse get_h_pre_total.simps get_h_total.simps get_m_pre_total.simps get_m_total.simps prod_eqI)

lemma full_total_state_eq: 
  assumes "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'" and 
          "get_total_full \<omega> = get_total_full \<omega>'"
        shows "\<omega> = \<omega>'"
  using assms 
  by (metis get_store_total.simps get_total_full.simps get_trace_total.simps prod.exhaust_sel)
  
lemma full_total_state_eq_2: 
  assumes "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'" and 
          "get_m_total_full \<omega> = get_m_total_full \<omega>'" and
          "get_h_total_full \<omega> = get_h_total_full \<omega>'"
        shows "\<omega> = \<omega>'"
  using assms full_total_state_eq
  by (metis get_h_total_full.elims get_m_total_full.elims total_state_eq)

lemma get_mask_total_full_wf: "wf_mask_simple (get_mh_total_full \<omega>)"
  using get_mask_total_wf
  by simp


end