theory TotalUtil
imports Viper.ViperLang Viper.ValueAndBasicState TotalViperState
begin

fun update_store_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> x v = ((get_store_total \<omega>)(x \<mapsto> v), get_trace_total \<omega>, get_total_full \<omega>)"

lemma update_store_total_trace_same: "get_trace_total (update_store_total \<omega> x v) = get_trace_total \<omega>"
  by simp

lemma update_store_total_hm_same: "get_total_full (update_store_total \<omega> x v) = get_total_full \<omega>"
  by simp

lemma update_store_total_heap_same: "get_hh_total_full (update_store_total \<omega> x v) = get_hh_total_full \<omega>"
  by simp

lemma update_store_total_mask_same: "get_total_full (update_store_total \<omega> x v) = get_total_full \<omega>"
  by simp

fun update_store_total_2 :: "'a full_total_state \<Rightarrow> 'a store \<Rightarrow> 'a full_total_state"
  where "update_store_total_2 \<omega> \<sigma> = (\<sigma>, get_trace_total \<omega>, get_total_full \<omega>)"

fun update_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace \<Rightarrow> 'a full_total_state"
  where "update_trace_total \<omega> \<pi> = (get_store_total \<omega>, \<pi>, get_total_full \<omega>)"

lemma update_trace_total_store_same: "get_store_total (update_trace_total \<omega> \<pi>) = get_store_total \<omega>"
  by simp

lemma update_trace_total_hm_same: "get_total_full (update_trace_total \<omega> \<pi>) = get_total_full \<omega>"
  by simp

lemma update_trace_total_heap_same: "get_hh_total_full (update_trace_total \<omega> \<pi>) = get_hh_total_full \<omega>"
  by simp

lemma update_trace_total_mask_same: "get_mh_total_full (update_trace_total \<omega> \<pi>) = get_mh_total_full \<omega>"
  by simp

definition update_hh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_hh_loc_total \<phi> l v = Abs_total_state (((get_hh_total \<phi>)(l := v), get_hp_total \<phi>), get_m_total \<phi>)"

definition update_mh_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mh_total \<phi> mh = Abs_total_state (get_h_total \<phi>, (mh, get_mp_total \<phi>))"

definition update_mp_total :: "'a total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_mp_total \<phi> mp = Abs_total_state (get_h_total \<phi>, (get_mh_total \<phi>, mp))"

definition update_m_total :: "'a total_state \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_m_total \<phi> m = Abs_total_state (get_h_total \<phi>, m)"

lemma Abs_total_state_inverse_2:
  assumes "wf_pre_total_state (m,h)"
  shows "Rep_total_state (Abs_total_state (m,h)) = (m,h)"
  using assms Abs_total_state_inverse
  by blast

lemma get_update_mh_total: 
  assumes "wf_mask_simple m0"
  shows   "get_mh_total (update_mh_total mh m0) = m0"
  unfolding update_mh_total_def
  using assms
  by (simp add: Abs_total_state_inverse_2)

lemma update_mh_total_multiple: 
  assumes "wf_mask_simple m0" and "wf_mask_simple m2"
  shows   "update_mh_total (update_mh_total mh m0) m1 = update_mh_total mh m1"
  unfolding update_mh_total_def  
  using assms
  by (simp add: Abs_total_state_inverse_2)

lemma update_hh_loc_total_mask_same: "get_mh_total (update_hh_loc_total \<phi> l v) = get_mh_total \<phi>"
  unfolding update_hh_loc_total_def
  (*
  by (metis Abs_total_state_inverse_2 fst_conv get_mh_total.simps get_mh_total_wf wf_pre_total_state.simps)*)
  sorry

lemma Rep_total_state_inj: "Rep_total_state a = Rep_total_state b \<Longrightarrow> a = b"
  by (metis Rep_total_state_inverse)

lemma update_hh_loc_total_overwrite: "update_hh_loc_total (update_hh_loc_total mh l v1) l v2 = update_hh_loc_total mh l v2"
 (* apply (rule total_state_eq)
   apply (simp only: update_hh_loc_total_mask_same)
  by (metis Abs_total_state_inverse_2 fun_upd_upd get_hh_total.simps get_mh_total_wf snd_conv update_hh_loc_total_def wf_pre_total_state.simps)*)
  sorry

lemma update_hh_loc_total_lookup_1: "get_hh_total (update_hh_loc_total \<phi> l v) l = v"
 (* by (metis (no_types, lifting) Abs_total_state_inverse_2 fun_upd_eqD fun_upd_triv get_hh_total.simps get_mh_total_wf snd_conv update_hh_loc_total_def wf_pre_total_state.simps) *)
  sorry

lemma update_hh_loc_total_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_hh_total (update_hh_loc_total \<phi> l1 v) l2 = get_hh_total \<phi> l2"
(*  by (metis (no_types, lifting) Abs_total_state_inverse_2 fun_upd_idem_iff fun_upd_triv fun_upd_twist get_hh_total.elims get_mh_total_wf sndI update_hh_loc_total_def wf_pre_total_state.simps) *)
  sorry

fun update_hh_loc_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_hh_loc_total_full \<omega> l v = (get_store_total \<omega>, get_trace_total \<omega>, update_hh_loc_total (get_total_full \<omega>) l v )"

lemma update_hh_loc_total_full_lookup_1: "get_hh_total_full (update_hh_loc_total_full \<phi> l v) l = v"
  by (metis get_hh_total_full.simps get_total_full.simps snd_conv update_hh_loc_total_full.simps update_hh_loc_total_lookup_1)

lemma update_hh_loc_total_full_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_hh_total_full (update_hh_loc_total_full \<phi> l1 v) l2 = get_hh_total_full \<phi> l2"
  by (metis get_hh_total_full.simps get_total_full.simps snd_conv update_hh_loc_total_full.simps update_hh_loc_total_lookup_2)

lemma update_hh_loc_total_overwrite_full: "update_hh_loc_total_full (update_hh_loc_total_full \<omega> l v1) l v2 = update_hh_loc_total_full \<omega> l v2"
  sorry
 (* apply (rule full_total_state_eq)
     apply simp
    apply simp
   apply (simp add: update_hh_loc_total_overwrite)
  by (metis get_total_full.elims get_mh_total_full.elims snd_conv update_hh_loc_total_full.simps update_hh_loc_total_mask_same)*)
  
fun update_mh_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mh_total_full \<omega> m = (get_store_total \<omega>, get_trace_total \<omega>, update_mh_total (get_total_full \<omega>) m)"

lemma update_hh_loc_total_full_mask_same: "get_mh_total_full (update_hh_loc_total_full \<omega> l v) = get_mh_total_full \<omega>"
  by (metis get_total_full.simps get_mh_total_full.simps snd_conv update_hh_loc_total_full.simps update_hh_loc_total_mask_same)

lemma get_update_mh_total_full: 
  assumes "wf_mask_simple m0"
  shows   "get_mh_total_full (update_mh_total_full mh m0) = m0"
  using assms get_update_mh_total
  by auto

lemma update_mh_total_full_same:
  "(update_mh_total_full \<omega> (get_mh_total_full \<omega>)) = \<omega>"
  by (simp add: update_mh_total_def Rep_total_state_inverse)

lemma update_mh_total_same_heap: 
  assumes "wf_mask_simple m"
  shows "get_hh_total (update_mh_total \<phi> m) = get_hh_total \<phi>"
  unfolding update_mh_total_def
  using assms
  by (simp add: Abs_total_state_inverse)

lemma update_mh_total_full_same_heap: 
  assumes "wf_mask_simple m"
  shows "get_hh_total_full (update_mh_total_full \<phi> m) = get_hh_total_full \<phi>"
  using assms update_mh_total_same_heap
  by auto
  
lemma update_mh_total_full_multiple: 
  assumes "wf_mask_simple m0"
  shows   "update_mh_total_full (update_mh_total_full \<omega> m0) m1 = update_mh_total_full \<omega> m1"
  using assms
  using update_mh_total_multiple by fastforce

fun update_m_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_m_total_full \<omega> m pm = 
                (get_store_total \<omega>, get_trace_total \<omega>, 
                 update_mp_total (update_mh_total (get_total_full \<omega>) m) pm)"

fun update_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_mp_total_full \<omega> pm = (get_store_total \<omega>, get_trace_total \<omega>, update_mp_total (get_total_full \<omega>) pm)"

fun map_result_2 :: "(mask \<Rightarrow> (mask set) option) \<Rightarrow> (mask set) option \<Rightarrow> (mask set) option"
  where 
    "map_result_2 f None = None"
  | "map_result_2 f (Some xs) = (if \<exists>x \<in> xs. f x = None then None else Some (\<Union>x \<in> xs. the (f x))) "

fun map_option_2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "map_option_2 f y None = y"
  | "map_option_2 f _ (Some x) = f x"

fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"

fun option_fold :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "option_fold f e (Some x) = f x"
  | "option_fold f e None = e"

fun nth_option :: "'a list => nat => 'a option"
  where "nth_option xs n = (if n < length xs then Some (nth xs n) else None)"

end