section \<open>A state model for the Viper total heap semantics\<close>

theory TotalViperState
imports Viper.ValueAndBasicState
begin

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


type_synonym 'a total_heap = "heap_loc \<Rightarrow> 'a val"
type_synonym 'a predicate_mask = "'a predicate_loc \<Rightarrow> prat"

text \<open>For each predicate instance, the state tracks the heap snapshot represented as a subset of
heap locations and predicate locations. The values of the heap locations are given by the 
corresponding total heap\<close>

type_synonym 'a predicate_heap = "'a predicate_loc \<Rightarrow> heap_loc set \<times> 'a predicate_loc set"

fun get_lhset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> heap_loc set"
  where "get_lhset_pheap hp lp = fst (hp lp)"

fun get_lpset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a predicate_loc set"
  where "get_lpset_pheap hp lp = snd (hp lp)"

record 'a total_state =
   get_hh_total :: "'a total_heap"
   get_hp_total :: "'a predicate_heap"
   get_mh_total :: "mask"
   get_mp_total :: "'a predicate_mask"

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)
record 'a full_total_state = (*= "'a store \<times> 'a total_trace \<times> 'a total_state"*)
  get_store_total :: "'a store"
  get_trace_total :: "'a total_trace"
  get_total_full :: "'a total_state"

definition empty_full_total_state :: "'a store \<Rightarrow> 'a total_trace \<Rightarrow> 'a total_heap \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a full_total_state"
  where "empty_full_total_state \<sigma> t hh hp =
   \<lparr> get_store_total =\<sigma>, 
     get_trace_total = t, 
     get_total_full = \<lparr> get_hh_total = hh, get_hp_total = hp, get_mh_total = zero_mask, get_mp_total = zero_mask \<rparr> 
   \<rparr>"


section \<open>Destructors \<close>

subsection \<open>total_state\<close>


subsection \<open>full total state\<close>
fun get_hh_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap"
  where "get_hh_total_full \<omega> = get_hh_total (get_total_full \<omega>)"

fun get_hp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_heap"
  where "get_hp_total_full \<omega> = get_hp_total (get_total_full \<omega>)"

fun get_mh_total_full :: "'a full_total_state \<Rightarrow> mask"
  where "get_mh_total_full \<omega> = get_mh_total (get_total_full \<omega>)"

fun get_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask"
  where "get_mp_total_full \<omega> = get_mp_total (get_total_full \<omega>)"



section \<open>Lemmas for proving equality of states\<close>

(*
lemma total_mask_eq:
  assumes "get_mh_total \<phi> = get_mh_total \<phi>'" and
          "get_mp_total \<phi> = get_mp_total \<phi>'" 
  shows "get_m_total \<phi> = get_m_total \<phi>'"
  using assms
  by (metis get_m_mh_mp_total)

lemma total_heap_eq:
  assumes "get_hh_total \<phi> = get_hh_total \<phi>'" and
          "get_hp_total \<phi> = get_hp_total \<phi>'" 
  shows "get_h_total \<phi> = get_h_total \<phi>'"
  using assms
  by (simp add: prod_eq_iff)

lemma total_state_eq:
  assumes "get_m_total \<phi> = get_m_total \<phi>'" and
          "get_h_total \<phi> = get_h_total \<phi>'"
  shows "\<phi> = \<phi>'"
  using assms
  by (simp add: prod_eq_iff)

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
*)
(*
lemma get_mask_total_full_wf: "wf_mask_simple (get_mh_total_full \<omega>)"
  using get_mask_total_wf
  by simp
*)

end