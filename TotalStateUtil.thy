theory TotalStateUtil
imports Viper.SepAlgebra TotalViperState Viper.DeBruijn
begin

section \<open>update_store_total\<close>

fun update_var_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_var_total \<omega> x v = \<omega>\<lparr>get_store_total := (get_store_total \<omega>)(x \<mapsto> v)\<rparr>"

fun update_store_total :: "'a full_total_state \<Rightarrow> 'a store \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> \<sigma> = \<omega>\<lparr>get_store_total := \<sigma>\<rparr>"

section \<open>update_trace_total\<close>

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

section \<open>heap and mask in total state\<close>

fun get_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total \<phi> = (get_mh_total \<phi>, get_mp_total \<phi>)"

fun update_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "update_m_total \<phi> m = \<phi>\<lparr> get_mh_total := fst m, get_mp_total := snd m \<rparr>"

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

fun get_m_total_full :: "'a full_total_state \<Rightarrow> mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = (get_mh_total_full \<omega>, get_mp_total_full \<omega>)"

fun update_m_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> mask \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a,'b) full_total_state_scheme"
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

lemma update_mh_m_total: "update_mh_total_full \<omega> mh' = update_m_total_full \<omega> mh' (get_mp_total_full \<omega>)"
  by simp

lemma update_mp_m_total: "update_mp_total_full \<omega> mp' = update_m_total_full \<omega> (get_mh_total_full \<omega>) mp'"
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

subsection \<open>Ordering lemmas\<close>

lemma less_eq_full_total_stateD_2:
  assumes "\<omega>1 \<le> \<omega>2"
  shows "get_h_total_full \<omega>1 = get_h_total_full \<omega>2 \<and>
         get_mh_total_full \<omega>1 \<le> get_mh_total_full \<omega>2 \<and>     
         get_mp_total_full \<omega>1 \<le> get_mp_total_full \<omega>2"
  using assms 
  by (fastforce dest: less_eq_full_total_stateD less_eq_total_stateD)  

lemma update_mh_loc_total_mono:
  assumes "\<phi>1 \<le> \<phi>2" and "p1 \<le> p2"
  shows "update_mh_loc_total \<phi>1 l p1 \<le> update_mh_loc_total \<phi>2 l p2"
proof -
  have *: "(get_mh_total \<phi>1)(l := p1) \<le> (get_mh_total \<phi>2)(l := p2)"
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
    apply (rule less_eq_full_total_stateI)
    by (fastforce dest: less_eq_full_total_stateD)+
qed

subsection \<open>Partial Commutative Monoid Instantiation\<close>

lemma plus_masks_defined: "(m1 :: 'a abstract_mask) ## m2"
  unfolding defined_def
  by (simp add: SepAlgebra.plus_prat_def compatible_funI plus_fun_def)

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

  show "a \<oplus> b = None \<and> b \<oplus> c = Some bc \<Longrightarrow> a \<oplus> bc = None"
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split if_split_asm)

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
  sorry

end

term "core (a :: mask)"

lemma plus_mask_zero_mask_neutral: "m \<oplus> zero_mask = Some m"
proof -
  have "compatible_fun m zero_mask"
    by (simp add: SepAlgebra.plus_prat_def compatible_funI)

  thus ?thesis
  unfolding plus_fun_def
  by (simp add: SepAlgebra.plus_prat_def zero_mask_def)
qed

lemma core_mask_zero_mask: "zero_mask = |m :: 'a abstract_mask|"
proof 
  fix x
  show "zero_mask x = |m| x"
    unfolding zero_mask_def
    by (simp add: core_fun core_prat_def)
qed

lemma total_state_plus_defined: 
  assumes "a \<oplus> b = Some c"
  shows "get_hh_total a = get_hh_total b \<and> get_hp_total a = get_hp_total b \<and> total_state.more a = total_state.more b \<and>
         get_hh_total a = get_hh_total c \<and> get_hp_total a = get_hp_total c \<and> total_state.more a = total_state.more c"
  using assms
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split_asm ) 

lemma mask_plus_Some:
  shows "m1 \<oplus> m2 = Some (add_masks m1 m2)"
  unfolding plus_fun_def add_masks_def
  by (simp split: if_split add: SepAlgebra.plus_prat_def compatible_fun_def)

lemma add_masks_self_zero_mask:
  assumes "m1 = add_masks m1 m2"
  shows "m2 = zero_mask"
  using assms
  unfolding add_masks_def
  (* TODO: faster proof *)
  by (metis add.commute add_0 le_fun_def order_class.order_eq_iff padd_cancellative zero_mask_def zero_mask_less_eq_mask)

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
    hence "get_hh_total x = get_hh_total c \<and> get_hp_total x = get_hp_total c \<and> total_state.more x = total_state.more c"
      unfolding plus_total_state_ext_def
      by (smt (verit) case_prod_conv option.discI)

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

  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    sorry
    
    
qed

end

instantiation full_total_state_ext :: (type,type) pcm_with_core
begin

text \<open>In the following, we do not take the core of the trace, because the addition of states is 
      defined only if the traces are the same.\<close>

definition core_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a, 'b) full_total_state_ext"
  where "core_full_total_state_ext \<phi> = 
            \<phi> \<lparr> get_trace_total := get_trace_total \<phi>, get_total_full := |get_total_full \<phi>|\<rparr>"
instance
  sorry
end

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

end