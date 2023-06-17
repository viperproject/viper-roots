theory TotalStateUtil
imports TotalViperState Viper.DeBruijn
begin

section \<open>update_store_total\<close>

fun update_var_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_var_total \<omega> x v = \<omega>\<lparr>get_store_total := (get_store_total \<omega>)(x \<mapsto> v)\<rparr>"

fun update_store_total :: "'a full_total_state \<Rightarrow> 'a store \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> \<sigma> = \<omega>\<lparr>get_store_total := \<sigma>\<rparr>"

section \<open>update_trace_total\<close>

fun update_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace \<Rightarrow> 'a full_total_state"
  where "update_trace_total \<omega> \<pi> = \<omega>\<lparr>get_trace_total := \<pi>\<rparr>"

lemma update_trace_total_store_same: "get_store_total (update_trace_total \<omega> \<pi>) = get_store_total \<omega>"
  by simp

lemma update_trace_total_hm_same: "get_total_full (update_trace_total \<omega> \<pi>) = get_total_full \<omega>"
  by simp

lemma update_trace_total_heap_same: "get_hh_total_full (update_trace_total \<omega> \<pi>) = get_hh_total_full \<omega>"
  by simp

lemma update_trace_total_mask_same: "get_mh_total_full (update_trace_total \<omega> \<pi>) = get_mh_total_full \<omega>"
  by simp

section \<open>heap and mask in total state\<close>

fun update_hh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_hh_loc_total \<phi> l v = \<phi>\<lparr>get_hh_total := (get_hh_total \<phi>)(l := v)\<rparr>"

fun update_mh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a total_state"
  where "update_mh_loc_total \<phi> l p = \<phi>\<lparr>get_mh_total := (get_mh_total \<phi>)(l := p)\<rparr>"

fun update_mp_loc_total :: "'a total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> prat \<Rightarrow> 'a total_state"
  where "update_mp_loc_total \<phi> lp p = \<phi>\<lparr>get_mp_total := (get_mp_total \<phi>)(lp := p)\<rparr>"

fun update_mh_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mh_total \<phi> mh = \<phi>\<lparr>get_mh_total := mh\<rparr>"

fun update_mp_total :: "'a total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_mp_total \<phi> mp = \<phi>\<lparr>get_mp_total := mp\<rparr>"

fun update_hh_total :: "'a total_state \<Rightarrow> 'a total_heap \<Rightarrow> 'a total_state"
  where "update_hh_total \<phi> hh = \<phi>\<lparr>get_hh_total := hh\<rparr>"

fun update_hp_total :: "'a total_state \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a total_state"
  where "update_hp_total \<phi> hp = \<phi>\<lparr>get_hp_total := hp\<rparr>"

subsection \<open>heap and mask in full total state\<close>

subsubsection \<open>Definitions\<close>

fun get_h_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap \<times> 'a predicate_heap"
  where "get_h_total_full \<omega> = (get_hh_total_full \<omega>, get_hp_total_full \<omega>)"

fun update_h_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a full_total_state"
  where "update_h_total_full \<omega> hh hp = 
              \<omega>\<lparr> get_total_full := update_hp_total (update_hh_total (get_total_full \<omega>) hh) hp \<rparr>"

fun update_hh_total_full ::  "'a full_total_state \<Rightarrow> 'a total_heap \<Rightarrow> 'a full_total_state"
  where "update_hh_total_full \<omega> hh = \<omega>\<lparr> get_total_full := update_hh_total (get_total_full \<omega>) hh \<rparr>"

fun update_hp_total_full ::  "'a full_total_state \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a full_total_state"
  where "update_hp_total_full \<omega> hp = \<omega>\<lparr> get_total_full := update_hp_total (get_total_full \<omega>) hp \<rparr>"

fun update_hh_loc_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_hh_loc_total_full \<omega> l v = 
        \<omega>\<lparr> get_total_full := update_hh_loc_total (get_total_full \<omega>) l v \<rparr>"

fun get_m_total_full :: "'a full_total_state \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = (get_mh_total_full \<omega>, get_mp_total_full \<omega>)"

fun update_m_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_m_total_full \<omega> m pm = 
              \<omega>\<lparr> get_total_full := update_mp_total (update_mh_total (get_total_full \<omega>) m) pm \<rparr>"

fun update_mh_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mh_total_full \<omega> mh = \<omega>\<lparr> get_total_full :=  update_mh_total (get_total_full \<omega>) mh \<rparr>"

fun update_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_mp_total_full \<omega> mp = \<omega>\<lparr> get_total_full := update_mp_total (get_total_full \<omega>) mp \<rparr>"

fun update_mh_loc_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a full_total_state"
  where "update_mh_loc_total_full \<omega> l p = 
        \<omega>\<lparr> get_total_full := update_mh_loc_total (get_total_full \<omega>) l p \<rparr>"

fun update_mp_loc_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> prat \<Rightarrow> 'a full_total_state"
  where "update_mp_loc_total_full \<omega> lp p = 
        \<omega>\<lparr> get_total_full := update_mp_loc_total (get_total_full \<omega>) lp p \<rparr>"

subsubsection \<open>Lemmas\<close>

lemma update_hh_h_total: "update_hh_total_full \<omega> hh' = update_h_total_full \<omega> hh' (get_hp_total_full \<omega>)"
  by simp

lemma update_hp_h_total: "update_hp_total_full \<omega> hp' = update_h_total_full \<omega> (get_hh_total_full \<omega>) hp'"
  by simp

section \<open>Shifting stores\<close>

fun shift_and_add_state_total :: "'a full_total_state \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where 
    "shift_and_add_state_total \<omega> v = update_store_total \<omega> (shift_and_add (get_store_total \<omega>) v)"

fun unshift_state_total :: "nat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state"
  where
   "unshift_state_total n \<omega> = update_store_total \<omega> (unshift n (get_store_total \<omega>))"         

subsection \<open>Well-typed states\<close>

definition total_heap_well_typed :: "program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "total_heap_well_typed Pr \<Delta> h \<equiv>                      
           \<forall>loc \<tau>. declared_fields Pr (snd loc) = Some \<tau> \<longrightarrow> has_type \<Delta> \<tau> (h loc)"

end