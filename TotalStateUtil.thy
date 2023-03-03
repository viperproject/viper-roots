theory TotalStateUtil
imports TotalViperState Viper.DeBruijn
begin

section \<open>update_store_total\<close>

fun update_var_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_var_total \<omega> x v = \<omega>\<lparr>get_store_total := (get_store_total \<omega>)(x \<mapsto> v)\<rparr>"

lemma update_var_total_trace_eq: "get_trace_total (update_var_total \<omega> x v) = get_trace_total \<omega>"
  by simp

lemma update_var_total_hm_same: "get_total_full (update_var_total \<omega> x v) = get_total_full \<omega>"
  by simp

lemma update_var_total_heap_same: "get_hh_total_full (update_var_total \<omega> x v) = get_hh_total_full \<omega>"
  by simp

lemma update_var_total_mask_same: "get_total_full (update_var_total \<omega> x v) = get_total_full \<omega>"
  by simp

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

section \<open>update heap and mask total\<close>

definition update_hh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_hh_loc_total \<phi> l v = \<phi>\<lparr>get_hh_total := (get_hh_total \<phi>)(l := v)\<rparr>"

definition update_mh_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mh_total \<phi> mh = \<phi>\<lparr>get_mh_total := mh\<rparr>"

definition update_mp_total :: "'a total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_mp_total \<phi> mp = \<phi>\<lparr>get_mp_total := mp\<rparr>"

(*
definition update_m_total :: "'a total_state \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_m_total \<phi> m = Abs_total_state (get_h_total \<phi>, m)"
*)

(*
lemma Abs_total_state_inverse_2:
  assumes "wf_pre_total_state (m,h)"
  shows "Rep_total_state (Abs_total_state (m,h)) = (m,h)"
  using assms Abs_total_state_inverse
  by blast
*)

(*
lemma get_m_update_m_total:
  assumes "wf_mask_simple (fst m)"
  shows "get_m_total (update_m_total \<phi> m) = m"
  unfolding update_m_total_def
  using assms
  by (simp add: Abs_total_state_inverse_2)


lemma get_h_update_m_total:
  assumes "wf_mask_simple (fst m)"
  shows "get_h_total (update_m_total \<phi> m) = get_h_total \<phi>"
  unfolding update_m_total_def
  using assms
  by (simp add: Abs_total_state_inverse_2)            

lemma update_m_total_eq: 
  assumes "wf_mask_simple (fst m)" and
          "get_h_total \<phi>1 = get_h_total \<phi>2"
  shows "update_m_total \<phi>1 m = update_m_total \<phi>2 m"
  apply (rule total_state_eq)
   apply (simp only: get_m_update_m_total[OF assms(1)])
  apply (simp only: get_h_update_m_total[OF assms(1)] assms(2))
  done
*)

lemma get_update_mh_total: 
  assumes "wf_mask_simple m0"
  shows   "get_mh_total (update_mh_total mh m0) = m0"
  unfolding update_mh_total_def
  using assms
  by simp

lemma update_mh_total_multiple: 
  shows   "update_mh_total (update_mh_total mh m0) m1 = update_mh_total mh m1"
  unfolding update_mh_total_def  
  by simp

(*
lemma wf_pre_total_state_1: 
  assumes"get_mh_pre_total \<phi>' = get_mh_total \<phi>"
  shows "wf_pre_total_state \<phi>'"
  using assms
  using get_mask_total_wf by fastforce
*)
(*
lemma update_hh_loc_total_m_eq: "get_m_total (update_hh_loc_total \<phi> l v) = get_m_total \<phi>"
  unfolding update_hh_loc_total_def
proof -
  let ?\<phi>' = "(((get_hh_total \<phi>)(l := v), get_hp_total \<phi>), get_m_total \<phi>)"
  have "wf_pre_total_state ?\<phi>'"
    apply (rule wf_pre_total_state_1[where ?\<phi>=\<phi>])
    by simp
  thus "get_m_total (Abs_total_state ?\<phi>') = (get_m_total \<phi>)"
    by (simp add: Abs_total_state_inverse_2)
qed
*)

(*
lemma m_eq_mh_eq_total: "get_m_total \<phi> = get_m_total \<phi>' \<Longrightarrow> get_mh_total \<phi> = get_mh_total \<phi>'"
  by simp

lemma m_eq_mp_eq_total: "get_m_total \<phi> = get_m_total \<phi>' \<Longrightarrow> get_mp_total \<phi> = get_mp_total \<phi>'"
  by simp
*)

lemma update_hh_loc_total_mh_eq: "get_mh_total (update_hh_loc_total \<phi> l v) = get_mh_total \<phi>"
  by (simp add: update_hh_loc_total_def)

lemma update_hh_loc_total_mp_eq: "get_mp_total (update_hh_loc_total \<phi> l v) = get_mp_total \<phi>"
  by (simp add: update_hh_loc_total_def)

lemma update_hh_loc_total_hp_eq: "get_hp_total (update_hh_loc_total \<phi> l v) = get_hp_total \<phi>"
  unfolding update_hh_loc_total_def
  by simp

lemma update_hh_loc_total_fupd: "get_hh_total (update_hh_loc_total \<phi> l1 v) = (get_hh_total \<phi>)(l1 := v)"
  by (simp add: update_hh_loc_total_def)

lemma update_hh_loc_total_lookup_1: "get_hh_total (update_hh_loc_total \<phi> l v) l = v"
  using update_hh_loc_total_fupd
  by (metis fun_upd_same)

lemma update_hh_loc_total_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_hh_total (update_hh_loc_total \<phi> l1 v) l2 = get_hh_total \<phi> l2"
  using update_hh_loc_total_fupd
  by (metis fun_upd_apply)

lemma update_hh_loc_total_overwrite: "update_hh_loc_total (update_hh_loc_total \<phi> l v1) l v2 = update_hh_loc_total \<phi> l v2"
  by (simp add: update_hh_loc_total_def)

fun get_h_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap \<times> 'a predicate_heap"
  where "get_h_total_full \<omega> = (get_hh_total_full \<omega>, get_hp_total_full \<omega>)"

fun update_hh_loc_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_hh_loc_total_full \<omega> l v = 
        \<omega>\<lparr> get_total_full := update_hh_loc_total (get_total_full \<omega>) l v \<rparr>"

lemma update_hh_loc_total_full_lookup_1: "get_hh_total_full (update_hh_loc_total_full \<phi> l v) l = v"
  by (simp add: update_hh_loc_total_fupd)

lemma update_hh_loc_total_full_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_hh_total_full (update_hh_loc_total_full \<phi> l1 v) l2 = get_hh_total_full \<phi> l2"
  by (simp add: update_hh_loc_total_lookup_2)

lemma update_hh_loc_total_overwrite_full: "update_hh_loc_total_full (update_hh_loc_total_full \<omega> l v1) l v2 = update_hh_loc_total_full \<omega> l v2"
  by (simp add: update_hh_loc_total_overwrite)
  
fun update_mh_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mh_total_full \<omega> mh = \<omega>\<lparr> get_total_full :=  update_mh_total (get_total_full \<omega>) mh \<rparr>"

fun update_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_mp_total_full \<omega> mp = \<omega>\<lparr> get_total_full := update_mp_total (get_total_full \<omega>) mp \<rparr>"

lemma update_hh_loc_total_full_mask_same: "get_mh_total_full (update_hh_loc_total_full \<omega> l v) = get_mh_total_full \<omega>"
  by (simp add: update_hh_loc_total_mh_eq)

lemma get_update_mh_total_full: 
  assumes "wf_mask_simple m0"
  shows   "get_mh_total_full (update_mh_total_full mh m0) = m0"
  using assms get_update_mh_total
  by auto

lemma update_mh_total_full_same:
  "(update_mh_total_full \<omega> (get_mh_total_full \<omega>)) = \<omega>"
  by (simp add: update_mh_total_def)

(*
lemma update_mp_total_h_eq: 
  shows "get_h_total (update_mp_total \<phi> m) = get_h_total \<phi>"
  by (metis Abs_total_state_inverse_2 fst_conv get_h_pre_total.simps get_h_total.elims get_m_pre_total.simps get_mask_total_wf snd_conv update_mp_total_def wf_pre_total_state.simps)

lemma update_mp_total_h_full_eq: 
  shows "get_h_total_full (update_mp_total_full \<phi> m) = get_h_total_full \<phi>"
  using update_mp_total_h_eq
  by auto

lemma update_mh_total_h_eq: 
  assumes "wf_mask_simple m"
  shows "get_h_total (update_mh_total \<phi> m) = get_h_total \<phi>"
  unfolding update_mh_total_def
  using assms
  by (simp add: Abs_total_state_inverse)

lemma update_mh_total_full_hh_eq: 
  assumes "wf_mask_simple m"
  shows "get_h_total_full (update_mh_total_full \<phi> m) = get_h_total_full \<phi>"
  using assms update_mh_total_h_eq
  by auto
*)

lemma update_mh_total_full_multiple: 
  shows   "update_mh_total_full (update_mh_total_full \<omega> m0) m1 = update_mh_total_full \<omega> m1"
  using update_mh_total_multiple 
  by (metis full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) update_mh_total_full.simps)


fun get_m_total_full :: "'a full_total_state \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = (get_mh_total_full \<omega>, get_mp_total_full \<omega>)"

fun update_m_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_m_total_full \<omega> m pm = 
              \<omega>\<lparr> get_total_full := update_mp_total (update_mh_total (get_total_full \<omega>) m) pm \<rparr>"

lemma get_m_total_full_aux:
  "get_m_total_full \<omega> = get_m_total_full (update_hh_loc_total_full \<omega> (addr, f_vpr) v_vpr)"
  apply simp
  by (simp add: update_hh_loc_total_mh_eq update_hh_loc_total_mp_eq)

section \<open>Shifting stores\<close>

fun shift_and_add_state_total :: "'a full_total_state \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where 
    "shift_and_add_state_total \<omega> v = update_store_total \<omega> (shift_and_add (get_store_total \<omega>) v)"

fun unshift_state_total :: "nat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state"
  where
   "unshift_state_total n \<omega> = update_store_total \<omega> (unshift n (get_store_total \<omega>))"         
                                                            

end