section \<open>Helper lemmas, instantiations, definitions for the total state\<close>

theory TotalStateUtil
imports ViperCommon.SepAlgebra TotalViperUtil TotalViperState ViperCommon.DeBruijn
begin                                    

subsection \<open>update_store_total\<close>

fun update_var_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_var_total \<omega> x v = \<omega>\<lparr>get_store_total := (get_store_total \<omega>)(x \<mapsto> v)\<rparr>"

fun update_store_total :: "'a full_total_state \<Rightarrow> 'a store \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> \<sigma> = \<omega>\<lparr>get_store_total := \<sigma>\<rparr>"

subsection \<open>update_trace_total\<close>

fun update_trace_total :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a total_trace \<Rightarrow> ('a, 'b) full_total_state_scheme" 
  where "update_trace_total \<omega> \<pi> = \<omega>\<lparr>get_trace_total := \<pi>\<rparr>"

lemma update_trace_total_store_same: "get_store_total (update_trace_total \<omega> \<pi>) = get_store_total \<omega>"
  by simp

lemma update_trace_total_hm_same: "get_total_full (update_trace_total \<omega> \<pi>) = get_total_full \<omega>"
  by simp

lemma update_trace_total_heap_same: "get_hh_total_full (update_trace_total \<omega> \<pi>) = get_hh_total_full \<omega>"
  by simp

lemma update_trace_total_mask_same: "get_mh_total_full (update_trace_total \<omega> \<pi>) = get_mh_total_full \<omega>"
  by simp

fun update_trace_label_total :: "('a, 'b) full_total_state_scheme \<Rightarrow> label \<Rightarrow> 'a total_state \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "update_trace_label_total \<omega> lbl \<phi> = update_trace_total \<omega> ((get_trace_total \<omega>)(lbl \<mapsto> \<phi>))"

subsection \<open>heap and mask in total state\<close>

fun get_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<times> 'a predicate_mask"
  where "get_m_total \<omega> = (get_mh_total \<omega>, get_mp_total \<omega>)"

fun update_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<times> 'a predicate_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "update_m_total \<omega> m = \<omega>\<lparr> get_mh_total := fst m, get_mp_total := snd m \<rparr>"

fun update_hh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_hh_loc_total \<omega> l v = \<omega>\<lparr>get_hh_total := (get_hh_total \<omega>)(l := v)\<rparr>"

fun update_mh_loc_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a total_state"
  where "update_mh_loc_total \<omega> l p = \<omega>\<lparr>get_mh_total := (get_mh_total \<omega>)(l := p)\<rparr>"

fun update_mp_loc_total :: "'a total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a total_state"
  where "update_mp_loc_total \<omega> lp p = \<omega>\<lparr>get_mp_total := (get_mp_total \<omega>)(lp := p)\<rparr>"

fun update_mh_total :: "'a total_state \<Rightarrow> field_mask \<Rightarrow> 'a total_state"
  where "update_mh_total \<omega> mh = \<omega>\<lparr>get_mh_total := mh\<rparr>"

fun update_mp_total :: "'a total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a total_state"
  where "update_mp_total \<omega> mp = \<omega>\<lparr>get_mp_total := mp\<rparr>"

fun update_hh_total :: "'a total_state \<Rightarrow> 'a total_heap \<Rightarrow> 'a total_state"
  where "update_hh_total \<omega> hh = \<omega>\<lparr>get_hh_total := hh\<rparr>"

fun update_hp_total :: "'a total_state \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a total_state"
  where "update_hp_total \<omega> hp = \<omega>\<lparr>get_hp_total := hp\<rparr>"

subsection \<open>heap and mask in full total state\<close>

subsubsection \<open>Definitions\<close>

fun get_h_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> 'a total_heap \<times> 'a predicate_heap"
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

fun get_m_total_full :: "'a full_total_state \<Rightarrow> field_mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = (get_mh_total_full \<omega>, get_mp_total_full \<omega>)"

fun update_m_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> field_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a,'b) full_total_state_scheme"
  where "update_m_total_full \<omega> m pm = 
              \<omega>\<lparr> get_total_full := update_mp_total (update_mh_total (get_total_full \<omega>) m) pm \<rparr>"

fun update_mh_total_full :: "'a full_total_state \<Rightarrow> field_mask \<Rightarrow> 'a full_total_state"
  where "update_mh_total_full \<omega> mh = \<omega>\<lparr> get_total_full :=  update_mh_total (get_total_full \<omega>) mh \<rparr>"

fun update_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a full_total_state"
  where "update_mp_total_full \<omega> mp = \<omega>\<lparr> get_total_full := update_mp_total (get_total_full \<omega>) mp \<rparr>"

fun update_mh_loc_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a full_total_state"
  where "update_mh_loc_total_full \<omega> l p = 
        \<omega>\<lparr> get_total_full := update_mh_loc_total (get_total_full \<omega>) l p \<rparr>"

fun update_mp_loc_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a full_total_state"
  where "update_mp_loc_total_full \<omega> lp p = 
        \<omega>\<lparr> get_total_full := update_mp_loc_total (get_total_full \<omega>) lp p \<rparr>"

subsubsection \<open>Lemmas\<close>

lemma update_hh_h_total: "update_hh_total_full \<omega> hh' = update_h_total_full \<omega> hh' (get_hp_total_full \<omega>)"
  by simp

lemma update_hp_h_total: "update_hp_total_full \<omega> hp' = update_h_total_full \<omega> (get_hh_total_full \<omega>) hp'"
  by simp

lemma update_mh_m_total: "update_mh_total_full \<omega> mh' = update_m_total_full \<omega> mh' (get_mp_total_full \<omega>)"
  by simp

lemma update_mp_m_total: "update_mp_total_full \<omega> mp' = update_m_total_full \<omega> (get_mh_total_full \<omega>) mp'"
  by simp

subsection \<open>Shifting stores\<close>

fun shift_and_add_state_total :: "'a full_total_state \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where 
    "shift_and_add_state_total \<omega> v = update_store_total \<omega> (shift_and_add (get_store_total \<omega>) v)"

fun unshift_state_total :: "nat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state"
  where
   "unshift_state_total n \<omega> = update_store_total \<omega> (unshift_2 n (get_store_total \<omega>))"  

fun shift_state_total
  where "shift_state_total n \<omega> = update_store_total \<omega> (DeBruijn.shift n (get_store_total \<omega>))"

lemma shift_1_shift_and_add_total: 
  "shift_and_add_state_total \<omega> y = update_var_total (shift_state_total 1 \<omega>) 0 y"
  apply (simp add: shift_and_add_def)
  apply (rule full_total_state.equality)
  unfolding DeBruijn.shift_def
  by auto

subsection \<open>Well-typed states\<close>

definition total_heap_well_typed :: "program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "total_heap_well_typed Pr \<Delta> h \<equiv>                      
           \<forall>loc \<tau>. declared_fields Pr (snd loc) = Some \<tau> \<longrightarrow> has_type \<Delta> \<tau> (h loc)"

subsection \<open>Ordering lemmas\<close>

lemma less_eq_full_total_stateD_2:
  assumes "\<omega>1 \<le> \<omega>2"
  shows "get_h_total_full \<omega>1 = get_h_total_full \<omega>2 \<and>
         get_mh_total_full \<omega>1 \<le> get_mh_total_full \<omega>2 \<and>     
         get_mp_total_full \<omega>1 \<le> get_mp_total_full \<omega>2"
  using assms 
  by (fastforce dest: less_eq_full_total_stateD less_eq_total_stateD)  

lemma update_mh_loc_total_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "update_mh_loc_total \<omega>1 l p1 \<le> update_mh_loc_total \<omega>2 l p2"
proof -
  have *: "(get_mh_total \<omega>1)(l := p1) \<le> (get_mh_total \<omega>2)(l := p2)"
    using assms 
    by (simp add: le_funD le_funI less_eq_total_stateD)

  show ?thesis
    apply (insert assms)
    by (fastforce intro: less_eq_total_stateI dest: less_eq_total_stateD simp: *)
qed

lemma update_mp_loc_total_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "update_mp_loc_total \<omega>1 l p1 \<le> update_mp_loc_total \<omega>2 l p2"
proof -
  have *: "(get_mp_total \<omega>1)(l := p1) \<le> (get_mp_total \<omega>2)(l := p2)"
    using assms 
    by (simp add: le_funD le_funI less_eq_total_stateD)

  show ?thesis
    apply (insert assms)
    by (fastforce intro: less_eq_total_stateI dest: less_eq_total_stateD simp: *)
qed

lemma update_mh_loc_total_full_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "update_mh_loc_total_full \<omega>1 l p1 \<le> update_mh_loc_total_full \<omega>2 l p2"
proof -
  have *: "update_mh_loc_total (get_total_full \<omega>1) l p1 \<le> update_mh_loc_total (get_total_full \<omega>2) l p2"
    using assms update_mh_loc_total_mono less_eq_full_total_state_ext_def
    by blast

  show ?thesis
    apply (insert assms *)
    apply (rule less_eq_full_total_stateI2)
    by (fastforce dest: less_eq_full_total_stateD)+
qed

lemma update_mp_loc_total_full_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "update_mp_loc_total_full \<omega>1 l p1 \<le> update_mp_loc_total_full \<omega>2 l p2"
proof -
  have *: "update_mp_loc_total (get_total_full \<omega>1) l p1 \<le> update_mp_loc_total (get_total_full \<omega>2) l p2"
    using assms update_mp_loc_total_mono less_eq_full_total_state_ext_def
    by blast

  show ?thesis
    apply (insert assms *)
    apply (rule less_eq_full_total_stateI2)
    by (fastforce dest: less_eq_full_total_stateD)+
qed

lemma less_eq_add_masks: "m1 \<le> add_masks m1 m2"
  unfolding add_masks_def le_fun_def
proof
  fix x
  show "m1 x \<le> (m1 x) + (m2 x)"
    by (simp add: padd_pgte)
qed  

subsection \<open>General helper lemmas\<close>

lemma add_masks_minus:
  assumes "m1 = add_masks (m2 :: ('a, preal) abstract_mask) m3"
  shows "m3 = m1 - m2"
  unfolding fun_diff_def
proof
  fix x

  have "m1 x = (m2 x) + (m3 x)"
    using assms
    by (simp add: add_masks_def)

  thus "m3 x = m1 x - m2 x"
    unfolding minus_preal_def
    by (simp add: Rep_preal_inverse plus_preal.rep_eq)    
qed

lemma minus_masks_empty:
 "m - (m :: ('a, preal) abstract_mask) = zero_mask"
  unfolding fun_diff_def
proof
  fix x
  show "m x - m x = zero_mask x"
    unfolding minus_preal_def zero_mask_def
    by (simp add: zero_preal_def)
qed

lemma minus_preal_gte:
  assumes "p \<ge> (q :: preal)" 
  shows "p - (p - q) = q"
proof -
  have "p - q = Abs_preal (Rep_preal p - Rep_preal q)" (is "_ = ?pminusq")
    by (simp add: minus_preal_def)

  have "Rep_preal p \<ge> Rep_preal q"
    using assms
    apply transfer
    by simp

  hence "Rep_preal ?pminusq = (Rep_preal p - Rep_preal q)"
    by (metis Rep_preal_inverse add_diff_cancel_left' assms plus_preal.rep_eq pperm_gte_padd)

  hence "Rep_preal p - Rep_preal ?pminusq = Rep_preal q"
    by simp

  thus ?thesis
    unfolding minus_preal_def
    by (simp add: Rep_preal_inverse)
qed

lemma mask_plus_Some:
  shows "(m1 :: ('a, preal) abstract_mask) \<oplus> m2 = Some (add_masks m1 m2)"
  unfolding plus_fun_def add_masks_def
  by (simp split: if_split add: SepAlgebra.plus_preal_def compatible_fun_def)

lemma add_masks_self_zero_mask:
  assumes "m1 = add_masks m1 m2"
  shows "m2 = zero_mask"
  using assms
  unfolding add_masks_def
  by (metis (full_types) add.commute add_0 le_fun_def order_class.order_eq_iff pos_perm_class.padd_cancellative zero_mask_def)

lemma succ_maskI:
  assumes "(m :: ('a, preal) abstract_mask) \<ge> m'"
  shows "m \<succeq> m'"
  unfolding greater_def
proof
  let ?\<Delta> = "\<lambda>l. (m l) \<ominus> (m' l)"

  have "m = add_masks m' ?\<Delta>"
    unfolding add_masks_def
  proof
    fix l

    from assms have "m l \<ge> m' l"
      by (simp add: le_funD)

    from this obtain p where "m l = padd (m' l) p"
      using preal_gte_padd
      by blast
      
    hence "Some (m l) = (m' l) \<oplus> p"
      unfolding plus_preal_def
      by simp

    thus "m l = padd (m' l) (m l \<ominus> m' l)"
      by (metis SepAlgebra.plus_preal_def add.commute greater_equiv minus_equiv_def option.inject)
  qed

  thus "Some m = m' \<oplus> ?\<Delta>"
    by (metis (mono_tags, lifting) SepAlgebra.plus_preal_def add_masks_def plus_funI)
qed

subsection \<open>Partial commutative monoid instantiation\<close>

lemma plus_masks_defined: "(m1 :: ('a, preal) abstract_mask) ## m2"
  unfolding defined_def
  by (simp add: SepAlgebra.plus_preal_def compatible_funI plus_fun_def)

instantiation total_state_ext :: (type,type) pcm
begin

definition plus_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext option"
  where "plus_total_state_ext \<phi>1 \<phi>2 = 
              (let (mh1, mp1, mh2, mp2) = (get_mh_total \<phi>1, get_mp_total \<phi>1, get_mh_total \<phi>2, get_mp_total \<phi>2) in 
                   if get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and> get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and> 
                      total_state.more \<phi>1 = total_state.more \<phi>2
                   then Some (update_m_total \<phi>1 (the (mh1 \<oplus> mh2), the (mp1 \<oplus> mp2)))
                   else None)"

instance proof
  fix a b ab c bc :: "('a,'b) total_state_ext"

  let ?mh_a = "get_mh_total a"
  let ?mp_a = "get_mp_total a"
  let ?mh_b = "get_mh_total b"
  let ?mp_b = "get_mp_total b"
  let ?mh_c = "get_mh_total c"
  let ?mp_c = "get_mp_total c"

  obtain mh_ab where MhEqAB: "?mh_a \<oplus> ?mh_b = Some mh_ab" 
    using plus_masks_defined
    unfolding defined_def
    by blast

  obtain mp_ab where MpEqAB: "?mp_a \<oplus> ?mp_b = Some mp_ab"
    using plus_masks_defined
    unfolding defined_def
    by blast

  note MEqAB = MhEqAB MpEqAB

  obtain mh_bc where MhEqBC: "?mh_b \<oplus> ?mh_c = Some mh_bc" 
    using plus_masks_defined
    unfolding defined_def
    by blast

  obtain mp_bc where MpEqBC: "?mp_b \<oplus> ?mp_c = Some mp_bc"
    using plus_masks_defined
    unfolding defined_def
    by blast

  note MEqBC = MhEqBC MpEqBC

  show "a \<oplus> b = b \<oplus> a" 
    unfolding plus_total_state_ext_def
    by (simp add: commutative)      
  
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  proof -
    have *: "mh_ab \<oplus> get_mh_total c = get_mh_total a \<oplus> mh_bc"
      using MEqAB MEqBC asso1
      by blast

    have **: "mp_ab \<oplus> get_mp_total c = get_mp_total a \<oplus> mp_bc"
      using MEqAB MEqBC asso1
      by blast

    assume "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
    thus ?thesis
    unfolding plus_total_state_ext_def
    by (clarsimp simp: * ** MEqAB MEqBC split: if_split if_split_asm)
  qed

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split if_split_asm)

  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
  proof -
    assume A: "a \<oplus> b = Some c" and B: "Some c = c \<oplus> c"

    obtain mh_cc where MhEqCC: "?mh_c \<oplus> ?mh_c = Some mh_cc"
    using plus_masks_defined
    unfolding defined_def
    by blast

    obtain mp_cc where MpEqCC: "?mp_c \<oplus> ?mp_c = Some mp_cc"
    using plus_masks_defined
    unfolding defined_def
    by blast

    note MEqCC = MhEqCC MpEqCC

    from B have *: "?mh_c \<oplus> ?mh_c = Some ?mh_c \<and> ?mp_c \<oplus> ?mp_c = Some ?mp_c"
      unfolding plus_total_state_ext_def
      
    proof (clarsimp simp: MEqCC split: if_split if_split_asm)
      assume "c = c\<lparr>get_mh_total := mh_cc, get_mp_total := mp_cc\<rparr>"
      have "get_mh_total c = mh_cc"
        apply (subst \<open>c = _\<close>)
        by simp
      moreover have "get_mp_total c = mp_cc"
        apply (subst \<open>c = _\<close>)
        by simp
      ultimately show "mh_cc = get_mh_total c \<and> mp_cc = get_mp_total c"
        by simp
    qed

    moreover from * A have "?mh_a \<oplus> ?mh_b = Some ?mh_c \<and> ?mp_a \<oplus> ?mp_b = Some ?mp_c"
      unfolding plus_total_state_ext_def
      by (clarsimp simp: MEqAB split: if_split if_split_asm)

    ultimately have "?mh_a \<oplus> ?mh_a = Some ?mh_a \<and> ?mp_a \<oplus> ?mp_a = Some ?mp_a"
      using positivity
      by metis

    thus ?thesis
      unfolding plus_total_state_ext_def
      by (clarsimp simp: MEqAB MEqBC split: if_split if_split_asm)
  qed    
qed

end

instantiation full_total_state_ext :: (type,type) pcm
begin

\<comment>\<open>In the following definitions, traces must be the same. A different design decision would be to add the traces.
   Since our setting, elements of a trace once initialised are never modified it seems natural to force
   the traces to be the same.\<close>

definition plus_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext option"
  where "plus_full_total_state_ext \<omega>1 \<omega>2 = 
            (if get_store_total \<omega>1 = get_store_total \<omega>2 \<and> 
                get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and> 
                get_total_full \<omega>1 ## get_total_full \<omega>2 \<and>
                full_total_state.more \<omega>1 = full_total_state.more \<omega>2 then
                Some (\<omega>1\<lparr>get_total_full := the (get_total_full \<omega>1 \<oplus> get_total_full \<omega>2) \<rparr>)
            else 
                None)"

instance

proof
  fix a b c ab bc :: "('a,'b) full_total_state_ext"

  show "a \<oplus> b = b \<oplus> a"
    unfolding plus_full_total_state_ext_def
    by (simp add: commutative defined_def)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    unfolding plus_full_total_state_ext_def
    by (metis (no_types, lifting) asso2 defined_def full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3) option.collapse option.discI option.inject)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc" (is "?A \<Longrightarrow> _")
  proof -
    let ?at = "get_total_full a"
    let ?bt = "get_total_full b"
    let ?ct = "get_total_full c"
    let ?abt = "get_total_full ab"
    let ?bct = "get_total_full bc"

    assume ?A

    hence "?at \<oplus> ?bt = Some ?abt \<and> ?bt \<oplus> ?ct = Some ?bct"
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)

    hence "?abt \<oplus> ?ct = ?at \<oplus> ?bct"
      using asso1 by blast

    with \<open>?A\<close>
    show ?thesis
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)
  qed

  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a" (is "?A \<Longrightarrow> ?B \<Longrightarrow> _")
  proof -
    let ?at = "get_total_full a"
    let ?bt = "get_total_full b"
    let ?ct = "get_total_full c"
    assume ?A and ?B

    from \<open>?A\<close> have "?at \<oplus> ?bt = Some ?ct"
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)

    moreover from \<open>?B\<close> have "Some ?ct = ?ct \<oplus> ?ct"
      unfolding plus_full_total_state_ext_def defined_def
      apply (simp split: if_split if_split_asm)      
      by (metis full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))

    ultimately have "Some ?at = ?at \<oplus> ?at"
      using positivity by blast

    thus ?thesis 
      unfolding plus_full_total_state_ext_def defined_def
      by (metis full_total_state.surjective full_total_state.update_convs(3) option.discI option.sel)   
  qed
qed

end

subsubsection \<open>Lemmas\<close>

lemma plus_mask_zero_mask_neutral: "(m :: ('a, preal) abstract_mask) \<oplus> zero_mask = Some m"
proof -
  have "compatible_fun m zero_mask"
    by (simp add: SepAlgebra.plus_preal_def compatible_funI)

  thus ?thesis
  unfolding plus_fun_def
  by (simp add: SepAlgebra.plus_preal_def zero_mask_def)
qed

lemma core_mask_zero_mask: "zero_mask = |m :: ('a, preal) abstract_mask|"
proof 
  fix x
  show "zero_mask x = |m| x"
    unfolding zero_mask_def
    by (simp add: core_fun core_preal_def)
qed

lemma total_state_plus_defined: 
  assumes "a \<oplus> b = Some c"
  shows "get_hh_total a = get_hh_total b \<and> get_hp_total a = get_hp_total b \<and> total_state.more a = total_state.more b \<and>
         get_hh_total a = get_hh_total c \<and> get_hp_total a = get_hp_total c \<and> total_state.more a = total_state.more c"
  using assms
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split_asm ) 

lemma plus_Some_total_state_eq:
  assumes "\<phi> \<oplus> \<phi>' = Some \<phi>sum"
  shows "\<phi>sum = \<phi> \<lparr> get_mh_total := add_masks (get_mh_total \<phi>) (get_mh_total \<phi>'),
                    get_mp_total := add_masks (get_mp_total \<phi>) (get_mp_total \<phi>') \<rparr>"
  using assms 
  unfolding plus_total_state_ext_def
  by (simp split: if_split_asm add: mask_plus_Some)

lemma plus_Some_full_total_state_eq:
  assumes "\<omega> \<oplus> \<omega>' = Some \<omega>sum"
  shows "\<omega>sum = update_m_total_full \<omega> (add_masks (get_mh_total_full \<omega>) (get_mh_total_full \<omega>'))
                                      (add_masks (get_mp_total_full \<omega>) (get_mp_total_full \<omega>'))"
  using assms 
  unfolding plus_full_total_state_ext_def defined_def
  by (fastforce split: if_split_asm dest: plus_Some_total_state_eq)

lemma plus_Some_full_total_state_total_state:
  assumes "Some a = b \<oplus> x"
  shows "Some (get_total_full a) = (get_total_full b) \<oplus> (get_total_full x)"
  using assms
  unfolding plus_full_total_state_ext_def defined_def
  by (auto split: if_split_asm)

lemma plus_total_state_zero_mask:
  assumes "get_hh_total \<phi> = get_hh_total \<phi>' \<and> get_hp_total \<phi> = get_hp_total \<phi>' \<and> total_state.more \<phi> = total_state.more \<phi>'" and
          "get_mh_total \<phi>' = zero_mask \<and> get_mp_total \<phi>' = zero_mask"
        shows "\<phi>' \<oplus> \<phi> = Some \<phi>"
  using assms
  unfolding plus_total_state_ext_def
  apply simp
  by (metis (no_types, lifting) commutative option.sel plus_mask_zero_mask_neutral total_state.surjective total_state.update_convs(3) total_state.update_convs(4))  

lemma plus_full_total_state_zero_mask:
  assumes "get_store_total \<omega> = get_store_total \<omega>' \<and> get_trace_total \<omega> = get_trace_total \<omega>' \<and> get_h_total_full \<omega> = get_h_total_full \<omega>' \<and>
           full_total_state.more \<omega> = full_total_state.more \<omega>'" and
          "get_mh_total_full \<omega>' = zero_mask \<and> get_mp_total_full \<omega>' = zero_mask"
  shows "\<omega>' \<oplus> \<omega> = Some \<omega>"
proof -
  have "get_total_full \<omega>' \<oplus> get_total_full \<omega> = Some (get_total_full \<omega>)"
    apply (rule plus_total_state_zero_mask)
    using assms 
    by simp_all

  thus ?thesis
  unfolding plus_full_total_state_ext_def defined_def
  using plus_total_state_zero_mask assms
  by simp
qed
  
lemma full_total_state_greater_only_mask_changed:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_store_total \<omega> = get_store_total \<omega>' \<and>
         get_trace_total \<omega> = get_trace_total \<omega>' \<and>
         get_h_total_full \<omega> = get_h_total_full \<omega>' \<and>
         full_total_state.more \<omega> = full_total_state.more \<omega>'"
  using assms
  unfolding greater_def 
  unfolding plus_full_total_state_ext_def defined_def plus_total_state_ext_def
  by (force split: if_split if_split_asm)

lemma succ_total_stateI:
  assumes "get_mh_total \<phi> \<succeq> get_mh_total \<phi>'"  (is "?mh \<succeq> ?mh'")
      and "get_mp_total \<phi> \<succeq> get_mp_total \<phi>'"  (is "?mp \<succeq> ?mp'")
      and "get_hh_total \<phi> = get_hh_total \<phi>'" 
      and "get_hp_total \<phi> = get_hp_total \<phi>'" 
      and "total_state.more \<phi> = total_state.more \<phi>'"
    shows "\<phi> \<succeq> \<phi>'"
proof -
  from assms(1-2) obtain mh_diff mp_diff where 
    Eqns: "?mh' \<oplus> mh_diff = Some ?mh" "?mp' \<oplus> mp_diff = Some ?mp"
    by (auto simp: greater_def)

  have "\<phi>' \<oplus> (update_m_total \<phi>' (mh_diff,mp_diff)) = Some \<phi>"
    unfolding plus_total_state_ext_def
    apply (simp add: Eqns)
    apply (rule total_state.equality)
    using assms 
    by auto

  thus ?thesis
    unfolding greater_def
    by metis
qed

lemma succ_full_total_stateI:
  assumes "get_mh_total_full \<omega> \<succeq> get_mh_total_full \<omega>'" 
      and "get_mp_total_full \<omega> \<succeq> get_mp_total_full \<omega>'"
      and "get_h_total_full \<omega> = get_h_total_full \<omega>'"
      and "get_store_total \<omega> = get_store_total \<omega>'"
      and "get_trace_total \<omega> = get_trace_total \<omega>'"
      and "full_total_state.more \<omega> = full_total_state.more \<omega>'"
    shows "\<omega> \<succeq> \<omega>'"
proof -
  have "get_total_full \<omega> \<succeq> get_total_full \<omega>'" (is "?\<phi> \<succeq> ?\<phi>'")
    apply (rule succ_total_stateI)
    using assms
    by auto

  from this obtain \<phi>_diff where *: "?\<phi>' \<oplus> \<phi>_diff = Some ?\<phi>"
    by (auto simp: greater_def)

  have "Some \<omega> = \<omega>' \<oplus> (\<omega> \<lparr> get_total_full := \<phi>_diff \<rparr>)"
    unfolding plus_full_total_state_ext_def defined_def
    apply (clarsimp split: if_split)
    apply (intro conjI)
  proof -
    show "\<exists>y. get_total_full \<omega>' \<oplus> \<phi>_diff = Some y"
      by (metis *)
  next
    fix A \<comment>\<open>LHS irrelevant\<close>
    show "A \<longrightarrow> \<omega> = \<omega>'\<lparr>get_total_full := the (get_total_full \<omega>' \<oplus> \<phi>_diff)\<rparr>"
    proof (rule impI, simp add: *)
      show "\<omega> = \<omega>'\<lparr>get_total_full := get_total_full \<omega>\<rparr>"
        apply (rule full_total_state.equality)
        using assms by auto
    qed
  qed (insert assms, simp_all)

  thus ?thesis
    by (auto simp add: greater_def)
qed

lemma greater_full_total_state_total_state:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_total_full \<omega> \<succeq> get_total_full \<omega>'"
  using assms
  unfolding greater_def plus_full_total_state_ext_def
  by (metis defined_def full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) option.distinct(1) option.exhaust_sel option.sel)  


lemma total_state_greater_mask:
  assumes "\<phi> \<succeq> \<phi>'"
  shows "get_mh_total \<phi> \<succeq> get_mh_total \<phi>' \<and> get_mp_total \<phi> \<succeq> get_mp_total \<phi>'"
proof -

  from assms obtain \<phi>a where "\<phi>' \<oplus> \<phi>a = Some \<phi>"
    unfolding greater_def
    by auto

  hence "get_mh_total \<phi> = add_masks (get_mh_total \<phi>') (get_mh_total \<phi>a)" and
        "get_mp_total \<phi> = add_masks (get_mp_total \<phi>') (get_mp_total \<phi>a)"
    using plus_Some_total_state_eq 
    by fastforce+

  thus ?thesis
    using mask_plus_Some
    unfolding greater_def
    by metis
qed
      
lemma full_total_state_greater_mask:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_mh_total_full \<omega> \<succeq> get_mh_total_full \<omega>' \<and> get_mp_total_full \<omega> \<succeq> get_mp_total_full \<omega>'"
  using greater_full_total_state_total_state[OF assms] total_state_greater_mask
  by auto

lemma total_state_greater_equiv:
  shows "(\<omega> :: 'a total_state) \<succeq> \<omega>' \<longleftrightarrow> \<omega> \<ge> \<omega>'"
proof
  assume "\<omega> \<succeq> \<omega>'"

  from this obtain \<omega>2 where Sum: "\<omega>' \<oplus> \<omega>2 = Some \<omega>"
    by (auto simp add: greater_def) 

  show "\<omega> \<ge> \<omega>'"
    unfolding plus_Some_total_state_eq[OF Sum]
    by (rule less_eq_total_stateI) (simp_all add: less_eq_add_masks)
next
  assume *: "\<omega> \<ge> \<omega>'"

  let ?mh2 = "\<lambda>l. get_mh_total \<omega> l - get_mh_total \<omega>' l"
  let ?mp2 = "\<lambda>l. get_mp_total \<omega> l - get_mp_total \<omega>' l"

  have MhEq: "get_mh_total \<omega> = add_masks (get_mh_total \<omega>') ?mh2"
    unfolding add_masks_def
  proof
    fix hl
    have "get_mh_total \<omega> hl \<ge> get_mh_total \<omega>' hl"
    using less_eq_total_stateD[OF *]
    by (simp add: le_funD)

    thus "get_mh_total \<omega> hl = padd (get_mh_total \<omega>' hl) (get_mh_total \<omega> hl - get_mh_total \<omega>' hl)"
      unfolding minus_preal_def
      by (metis Rep_preal_inverse add.commute add_diff_cancel plus_preal.rep_eq preal_gte_padd)
  qed

  have MpEq: "get_mp_total \<omega> = add_masks (get_mp_total \<omega>') ?mp2"
    unfolding add_masks_def
  proof
    fix hl
    have "get_mp_total \<omega> hl \<ge> get_mp_total \<omega>' hl"
    using less_eq_total_stateD[OF *]
    by (simp add: le_funD)

    thus "get_mp_total \<omega> hl = padd (get_mp_total \<omega>' hl) (get_mp_total \<omega> hl - get_mp_total \<omega>' hl)"
      unfolding minus_preal_def
      by (metis Rep_preal_inverse add.commute add_diff_cancel plus_preal.rep_eq preal_gte_padd)
  qed  

  have "Some \<omega> = \<omega>' \<oplus> (\<omega> \<lparr> get_mh_total := ?mh2, get_mp_total := ?mp2 \<rparr>)"
    unfolding plus_total_state_ext_def
    using MhEq MpEq less_eq_total_stateD[OF *]
    by (auto simp: mask_plus_Some)

  thus "\<omega> \<succeq> \<omega>'"
    by (auto simp add: greater_def)
qed

lemma full_total_state_succ_implies_gte:
  assumes "(\<omega> :: 'a full_total_state) \<succeq> \<omega>'"
  shows "\<omega> \<ge> \<omega>'"
proof -
  from assms obtain \<omega>2 where Sum: "\<omega>' \<oplus> \<omega>2 = Some \<omega>"
    by (auto simp add: greater_def) 

  show "\<omega> \<ge> \<omega>'"
    unfolding plus_Some_full_total_state_eq[OF Sum]
    apply (rule less_eq_full_total_stateI)
       apply simp
      apply simp
    using less_eq_add_masks plus_Some_full_total_state_eq[OF Sum] \<open>\<omega> \<succeq> \<omega>'\<close> 
          greater_full_total_state_total_state total_state_greater_equiv 
     apply blast
    by simp
qed

lemma full_total_state_gte_implies_succ:
  assumes "\<omega> \<ge> \<omega>'"
      and TraceEq: "get_trace_total \<omega> = get_trace_total \<omega>'"
  shows "(\<omega> :: 'a full_total_state) \<succeq> \<omega>'"
proof -
  from \<open>\<omega> \<ge> \<omega>'\<close> have "get_total_full \<omega> \<ge> get_total_full \<omega>'"
    using less_eq_full_total_state_ext_def 
    by auto

  hence "get_total_full \<omega> \<succeq> get_total_full \<omega>'"    
    by (simp add: total_state_greater_equiv)

  thus "\<omega> \<succeq> \<omega>'"
    using TraceEq less_eq_full_total_stateD
    using assms(1) less_eq_full_total_stateD_2 succ_full_total_stateI total_state_greater_mask 
    by fastforce
qed

subsection \<open>Partial commutative monoid with core instantiation\<close>

instantiation total_state_ext :: (type,type) pcm_with_core
begin

definition core_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a, 'b) total_state_ext"
  where "core_total_state_ext \<phi> = (update_m_total \<phi> (zero_mask, zero_mask))"

instance proof
  fix a b c x y :: "('a,'b) total_state_ext"

  show "Some x = x \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    apply simp
    using plus_mask_zero_mask_neutral
    by (metis option.sel total_state.surjective total_state.update_convs(3) total_state.update_convs(4))
    

  show "Some |x| = |x| \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    apply simp
    using plus_mask_zero_mask_neutral
    by (metis option.sel)

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r" (is "?lhs \<Longrightarrow> ?rhs")
  proof -
    assume ?lhs

    have *: "get_mh_total c = zero_mask \<and> get_mp_total c = zero_mask"
    proof -
      note MaskPlusEq = 
          mask_plus_Some[of "get_mh_total x" "get_mh_total c"]
          mask_plus_Some[of "get_mp_total x" "get_mp_total c"]

      from \<open>?lhs\<close> show ?thesis
        unfolding plus_total_state_ext_def
        apply (simp split: if_split_asm)
        apply (simp add: MaskPlusEq)
        using add_masks_self_zero_mask
        by (metis total_state.ext_inject total_state.surjective total_state.update_convs(3) total_state.update_convs(4))        
    qed       

    show ?thesis
      unfolding core_total_state_ext_def plus_total_state_ext_def 
     apply (rule exI[where ?x="c\<lparr> get_mh_total := zero_mask, get_mp_total := zero_mask \<rparr>"])
     apply (simp add: * split: if_split if_split_asm)
      apply (simp add: plus_mask_zero_mask_neutral[simplified commutative])
      using total_state_plus_defined[OF HOL.sym[OF \<open>?lhs\<close>]]
      by simp
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by (clarsimp split: if_split if_split_asm simp: plus_mask_zero_mask_neutral)

  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y" (is "?A \<Longrightarrow> ?B \<Longrightarrow> _ \<Longrightarrow> _") 
    \<comment>\<open>\<^prop>\<open>|x| = |y|\<close> is not needed, since it is always the case if he heap of \<^term>\<open>x\<close> and \<^term>\<open>y\<close> 
       are the same, which it must be because of the first two assumptions\<close>
  proof -
    assume ?A and ?B
    
    from \<open>?A\<close> have Eqx1: "a = b \<lparr> get_mh_total := add_masks (get_mh_total b) (get_mh_total x),
                            get_mp_total := add_masks (get_mp_total b) (get_mp_total x) \<rparr>"
      using plus_Some_total_state_eq
      by metis

    from \<open>?B\<close> have Eqy1: "a = b \<lparr> get_mh_total := add_masks (get_mh_total b) (get_mh_total y),
                            get_mp_total := add_masks (get_mp_total b) (get_mp_total y) \<rparr>"
      using plus_Some_total_state_eq
      by metis

    from Eqx1 have Eqx2: "get_mh_total a = add_masks (get_mh_total b) (get_mh_total x) \<and>
                    get_mp_total a = add_masks (get_mp_total b) (get_mp_total x)"
      by simp

    from Eqy1 have Eqy2: "get_mh_total a = add_masks (get_mh_total b) (get_mh_total y) \<and>
                    get_mp_total a = add_masks (get_mp_total b) (get_mp_total y)"
      by simp

    have "get_mh_total x = get_mh_total y \<and> get_mp_total x = get_mp_total y"
      unfolding add_masks_def
       \<comment>\<open>one could instead do a proof here that does not unfold \<^term>\<open>add_masks\<close> and instead uses the properties
        of the mask core instantiation (but the current proof is more straightforward)\<close>
      by (metis Eqx2 Eqy2 add_masks_minus)

    thus ?thesis
      by (metis \<open>?A\<close> \<open>?B\<close> total_state.equality total_state_plus_defined)
  qed     
qed

end

instantiation full_total_state_ext :: (type,type) pcm_with_core
begin

text \<open>In the following, we do not take the core of the trace, because the addition of states is 
      defined only if the traces are the same.\<close>

definition core_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a, 'b) full_total_state_ext"
  where "core_full_total_state_ext \<omega> = 
            \<omega> \<lparr> get_total_full := |get_total_full \<omega>| \<rparr>"
instance proof
  fix a b c x y :: "('a,'b) full_total_state_ext"

  let ?at = "get_total_full a"
  let ?bt = "get_total_full b"
  let ?ct = "get_total_full c"
  let ?xt = "get_total_full x"
  let ?yt = "get_total_full y"
  

  show "Some x = x \<oplus> |x|"
  proof -
    from core_is_smaller[where ?x = ?xt] 
    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      using option.sel  
      by (fastforce split: if_split_asm)
  qed

  show "Some |x| = |x| \<oplus> |x|"
  proof -
    from core_is_pure[where ?x = ?xt] 
    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      using option.sel  
      by (fastforce split: if_split_asm)
  qed

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r" (is "?A \<Longrightarrow> _")
  proof -
    assume ?A
    hence "Some ?xt = ?xt \<oplus> ?ct"
      by (blast intro: plus_Some_full_total_state_total_state)

    from core_max[OF plus_Some_full_total_state_total_state[OF \<open>?A\<close>]] obtain rt where Eq_xt: "Some |?xt| = ?ct \<oplus> rt" 
      by blast

    let ?r = "x \<lparr> get_total_full := rt \<rparr>"

    have "Some |x| = c \<oplus> ?r"
      using \<open>?A\<close>
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      apply (simp split: if_split_asm if_split)
      using Eq_xt
      by (metis full_total_state.surjective full_total_state.update_convs(3) option.sel)

    thus ?thesis
      by blast
  qed


  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|" (is "?A \<Longrightarrow> _")
  proof -
    assume "?A"
    hence *: "Some ?ct = ?at \<oplus> ?bt"
      by (blast intro: plus_Some_full_total_state_total_state)

    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      apply (simp split: if_split_asm if_split)
      using core_sum[OF *] 
      by (metis (no_types, lifting) \<open>?A\<close> full_total_state.surjective full_total_state.update_convs(3) option.distinct(1) option.sel plus_full_total_state_ext_def)      
  qed

  
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y" (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> _")
  proof -
    assume "?A" and "?B" and "?C"

    from \<open>?A\<close> have "Some ?at = ?bt \<oplus> ?xt"
      by (blast intro: plus_Some_full_total_state_total_state)

    moreover from \<open>?B\<close> have "Some ?at = ?bt \<oplus> ?yt"
      by (blast intro: plus_Some_full_total_state_total_state)

    moreover from \<open>?C\<close> have "|?xt| = |?yt|"
      unfolding core_full_total_state_ext_def
      by (metis full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))

    ultimately have "?xt = ?yt"
      using cancellative by blast

    thus ?thesis
      by (metis Some_Some_ifD \<open>?A\<close> \<open>?B\<close> full_total_state.surjective plus_full_total_state_ext_def)
  qed
qed

end

subsubsection \<open>Lemmas\<close>

lemma total_state_defined_core_same:
  assumes "(\<phi> :: 'a total_state) ## \<phi>'"
  shows "|\<phi>| = |\<phi>'|"
  using assms
  unfolding defined_def plus_total_state_ext_def core_total_state_ext_def
  by (simp split: if_split_asm)

lemma full_total_state_defined_core_same:
  assumes "(\<omega> :: 'a full_total_state) ## \<omega>'"
  shows "|\<omega>| = |\<omega>'|"
  using assms total_state_defined_core_same
  unfolding defined_def plus_full_total_state_ext_def core_full_total_state_ext_def  
  by (fastforce split: if_split_asm)    

lemma full_total_state_defined_core_same_2:
  assumes "(\<omega> :: 'a full_total_state) \<oplus> \<omega>' = Some \<omega>''"
  shows "|\<omega>| = |\<omega>'|"
  using assms full_total_state_defined_core_same
  unfolding defined_def
  by fast


lemma minus_total_state:
  assumes "\<phi> \<succeq> \<phi>'"
  shows "\<phi> \<ominus> \<phi>' = \<phi> \<lparr> get_mh_total := get_mh_total \<phi> - get_mh_total \<phi>', 
                      get_mp_total := get_mp_total \<phi> - get_mp_total \<phi>' \<rparr>" (is "_ = ?\<Delta>")
proof -
  from assms minus_exists obtain \<phi>m
    where PlusSome: "Some \<phi> = \<phi>' \<oplus> \<phi>m" and "\<phi>m \<succeq> |\<phi>|"
    by blast

  hence "\<phi>m = \<phi> \<ominus> \<phi>'"
    using minusI by auto

  from PlusSome have 
     PlusMh: "get_mh_total \<phi> = add_masks (get_mh_total \<phi>') (get_mh_total \<phi>m)" and
     PlusMp: "get_mp_total \<phi> = add_masks (get_mp_total \<phi>') (get_mp_total \<phi>m)"
    unfolding plus_total_state_ext_def
    by (auto split: if_split_asm simp: mask_plus_Some)

  have "get_mh_total \<phi>m = get_mh_total \<phi> - get_mh_total \<phi>'"
    using add_masks_minus PlusMh
    by blast

  moreover have "get_mp_total \<phi>m = get_mp_total \<phi> - get_mp_total \<phi>'"
    using add_masks_minus PlusMp
    by blast

  moreover from PlusSome have "get_hh_total \<phi> = get_hh_total \<phi>m \<and>
                               get_hp_total \<phi> = get_hp_total \<phi>m \<and>
                               total_state.more \<phi> = total_state.more \<phi>m"
    by (metis total_state_plus_defined)
  ultimately have "\<phi>m = ?\<Delta>"
    by simp
  thus ?thesis
    using \<open>\<phi>m = \<phi> \<ominus> \<phi>'\<close>
    by argo
qed

lemma minus_full_total_state_only_mask_different:
  shows "get_store_total (\<omega> \<ominus> \<omega>') = get_store_total \<omega> \<and>
         get_trace_total (\<omega> \<ominus> \<omega>') = get_trace_total \<omega> \<and>
         get_h_total_full (\<omega> \<ominus> \<omega>') = get_h_total_full \<omega>"
  using full_total_state_greater_only_mask_changed minus_default minus_smaller
  by metis

lemma minus_full_total_state_only_mask_different_2:
  assumes "\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'"
  shows
    "get_store_total \<omega>_inh = get_store_total \<omega> \<and>
     get_trace_total \<omega>_inh = get_trace_total \<omega> \<and>
     get_h_total_full \<omega>_inh = get_h_total_full \<omega>"
  by (metis assms full_total_state_greater_only_mask_changed greater_def minus_bigger minus_full_total_state_only_mask_different)

lemma minus_full_total_state:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "\<omega> \<ominus> \<omega>' = \<omega> \<lparr> get_total_full := get_total_full \<omega> \<ominus> get_total_full \<omega>' \<rparr>" (is "_ = ?\<Delta>")
proof -
  from assms minus_exists obtain \<omega>m
    where PlusSome: "\<omega>' \<oplus> \<omega>m = Some \<omega>" and "\<omega>m \<succeq> |\<omega>|"
    by force

  hence "\<omega>m = \<omega> \<ominus> \<omega>'"
    using minusI 
    by metis

  from plus_Some_full_total_state_eq[OF PlusSome] have
     PlusMh: "get_mh_total_full \<omega> = add_masks (get_mh_total_full \<omega>') (get_mh_total_full \<omega>m)" and
     PlusMp: "get_mp_total_full \<omega> = add_masks (get_mp_total_full \<omega>') (get_mp_total_full \<omega>m)"
    by simp_all
    

  have "get_mh_total_full \<omega>m = get_mh_total_full \<omega> - get_mh_total_full \<omega>'"
    using add_masks_minus PlusMh
    by blast

  moreover have "get_mp_total_full \<omega>m = get_mp_total_full \<omega> - get_mp_total_full \<omega>'"
    using add_masks_minus PlusMp
    by blast

  moreover from PlusSome have "get_store_total \<omega> = get_store_total \<omega>m \<and>
                               get_trace_total \<omega> = get_trace_total \<omega>m \<and>
                               get_h_total_full \<omega> = get_h_total_full \<omega>m \<and>
                               full_total_state.more \<omega> = full_total_state.more \<omega>m"
    by (metis \<open>\<omega>m = \<omega> \<ominus> \<omega>'\<close> core_is_smaller minus_equiv_def_any_elem minus_full_total_state_only_mask_different option.discI plus_full_total_state_ext_def)
    
  ultimately have "\<omega>m = ?\<Delta>"
    using minus_total_state[OF greater_full_total_state_total_state[OF assms]]
    by simp
  thus ?thesis
    using \<open>\<omega>m = \<omega> \<ominus> \<omega>'\<close>
    by argo
qed

lemma minus_full_total_state_mask:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_mh_total_full (\<omega> \<ominus> \<omega>') = get_mh_total_full \<omega> - get_mh_total_full \<omega>' \<and>
         get_mp_total_full (\<omega> \<ominus> \<omega>') = get_mp_total_full \<omega> - get_mp_total_full \<omega>'"
proof -
  from minus_full_total_state[OF assms] 
  have "get_total_full (\<omega> \<ominus> \<omega>') = get_total_full \<omega> \<ominus> get_total_full \<omega>'" (is "_ = ?\<phi> \<ominus> ?\<phi>'")
    by simp

  thus ?thesis
  using greater_full_total_state_total_state[OF assms, THEN minus_total_state] 
  by simp
qed

subsection \<open>Monotonicity relationship\<close>

text \<open>The following lemma shows for \<^typ>\<open>'a full_total_state\<close> that downwards monotonicity w.r.t. 
the order type class is at least as strong as downwards monotoncity w.r.t. order defined via the pcm
addition. The converse is not true, because the order type class instantiation is a larger relation
(since traces need not be equal as opposed to the pcm addition case where traces must be equal).\<close>

lemma mono_prop_downward_ord_implies_mono_prop_downward:
  assumes "mono_prop_downward_ord (StateCons :: 'a full_total_state \<Rightarrow> bool)"
  shows "mono_prop_downward StateCons"
  using assms full_total_state_succ_implies_gte
  unfolding mono_prop_downward_ord_def mono_prop_downward_def
  by blast

subsection \<open>valid mask (TODO: move to ViperLang?)\<close>

abbreviation valid_heap_mask :: "preal mask \<Rightarrow> bool"
  where "valid_heap_mask \<equiv> wf_mask_simple"

lemma valid_heap_maskD:
  assumes "valid_heap_mask m"
  shows "pgte pwrite (m l)"
  using assms
  unfolding wf_mask_simple_def
  apply transfer
  by blast

lemma valid_heap_mask_downward_mono:
  assumes "valid_heap_mask m0" and "m0 \<succeq> m1"
  shows "valid_heap_mask m1"
proof -
  from \<open>m0 \<succeq> m1\<close> obtain m2 where "m0 = add_masks m1 m2"
    unfolding greater_def
    using mask_plus_Some
    by (metis option.sel)

  show "valid_heap_mask m1"
    unfolding wf_mask_simple_def
  proof
    fix l
    have "m0 l = padd (m1 l) (m2 l)"
      using \<open>m0 = _\<close>
      by (simp add: add_masks_def)

    thus "pwrite \<ge> (m1 l)"
      using valid_heap_maskD[of m0 l, OF assms(1)] \<open>m0 = add_masks m1 m2\<close> assms(1) wf_mask_simple_def wf_mask_simple_false_preserved 
      by blast
  qed
qed

end