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


subsection \<open>Order\<close>

definition less_eq_mask :: "'a abstract_mask \<Rightarrow> 'a abstract_mask \<Rightarrow> bool"
  where "less_eq_mask m1 m2 \<equiv> \<forall>l. lte (m1 l) (m2 l)"

definition less_mask :: "'a abstract_mask \<Rightarrow> 'a abstract_mask \<Rightarrow> bool"
  where "less_mask m1 m2 \<equiv> (\<forall>l. lte (m1 l) (m2 l)) \<and> (\<exists>l. lt (m1 l) (m2 l))"

lemma less_mask_less_eq_mask: "less_mask m1 m2 = (less_eq_mask m1 m2 \<and> \<not> less_eq_mask m2 m1)"
  unfolding less_mask_def less_eq_mask_def
  apply(transfer)
  using linorder_not_less by blast

lemma less_eq_mask_refl: "less_eq_mask m m"
  unfolding less_eq_mask_def  
  by (transfer) simp

lemma less_eq_mask_transitive: "less_eq_mask m1 m2 \<Longrightarrow> less_eq_mask m2 m3 \<Longrightarrow> less_eq_mask m1 m3"
  unfolding less_eq_mask_def
  apply transfer
  using dual_order.trans by blast

lemma less_eq_mask_antisymmetric: "less_eq_mask m1 m2 \<Longrightarrow> less_eq_mask m2 m1 \<Longrightarrow> m1 = m2"
  unfolding less_eq_mask_def
  apply transfer
  using order_antisym_conv by blast


instantiation total_state_ext :: (type,type) order
begin

definition less_eq_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 \<le> \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and>
         less_eq_mask (get_mh_total \<phi>1) (get_mh_total \<phi>2) \<and>
         less_eq_mask (get_mp_total \<phi>1) (get_mp_total \<phi>2) \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"

definition less_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 < \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and>
         ( (less_eq_mask (get_mh_total \<phi>1) (get_mh_total \<phi>2) \<and> less_mask (get_mp_total \<phi>1) (get_mp_total \<phi>2)) \<or>
           (less_mask (get_mh_total \<phi>1) (get_mh_total \<phi>2) \<and> less_eq_mask (get_mp_total \<phi>1) (get_mp_total \<phi>2))) \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"
instance
proof
  fix x y z :: "('a,'b) total_state_ext"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof
    assume "x < y"
    show "x \<le> y \<and> \<not> y \<le> x"
    proof (rule conjI)
      show "x \<le> y"
        using \<open>x < y\<close> less_mask_less_eq_mask
        unfolding less_total_state_ext_def less_eq_total_state_ext_def
        by meson
    next
      show "\<not> y \<le> x"
      using \<open>x < y\<close> less_mask_less_eq_mask
      unfolding less_total_state_ext_def less_eq_total_state_ext_def
      by metis
    qed
  next
    assume "x \<le> y \<and> \<not> y \<le> x"
    thus "x < y"
      using less_mask_less_eq_mask
      unfolding less_total_state_ext_def less_eq_total_state_ext_def
      by metis
  qed

  show "x \<le> x"
    unfolding less_eq_total_state_ext_def
    using less_eq_mask_refl
    by meson

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_total_state_ext_def
    using less_eq_mask_transitive
    by metis
  
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_total_state_ext_def
    apply (rule total_state.equality)
    using less_eq_mask_antisymmetric
    by blast+
qed

end

instantiation full_total_state_ext :: (type,type) order
begin

definition less_eq_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> bool"
  where "\<omega>1 \<le> \<omega>2 \<equiv> 
         get_store_total \<omega>1 = get_store_total \<omega>2 \<and>
         dom (get_trace_total \<omega>1) = dom (get_trace_total \<omega>2) \<and>
         (\<forall>lbl \<phi>1 \<phi>2. get_trace_total \<omega>1 lbl = Some \<phi>1 \<longrightarrow> get_trace_total \<omega>2 lbl = Some \<phi>2 \<longrightarrow>
                      \<phi>1 \<le> \<phi>2) \<and>
         get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<and>
         full_total_state.more \<omega>1 = full_total_state.more \<omega>2"

definition less_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> bool"
  where "\<omega>1 < \<omega>2 \<equiv> 
           \<omega>1 \<le> \<omega>2 \<and>
           ( 
             (\<exists>lbl \<phi>1 \<phi>2.  get_trace_total \<omega>1 lbl = Some \<phi>1 \<and> get_trace_total \<omega>2 lbl = Some \<phi>2 \<and>
                           \<phi>1 < \<phi>2) \<or>
             get_total_full \<omega>1 < get_total_full \<omega>2 
           )"

instance
proof
  fix x y z :: "('a,'b) full_total_state_ext"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof
    assume "x < y"
    show "x \<le> y \<and> \<not> y \<le> x"
    proof (rule conjI)
      show "x \<le> y"
        using \<open>x < y\<close> 
        unfolding less_full_total_state_ext_def
        by simp
    next
      from \<open>x < y\<close>
      show "\<not> y \<le> x"
        unfolding less_full_total_state_ext_def less_eq_full_total_state_ext_def
        by fastforce
    qed
  next
    assume "x \<le> y \<and> \<not> y \<le> x"
    thus "x < y"
    unfolding less_full_total_state_ext_def less_eq_full_total_state_ext_def    
    by force
  qed

  show "x \<le> x"
    unfolding less_eq_full_total_state_ext_def
    by auto

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_full_total_state_ext_def
    by (metis (mono_tags, opaque_lifting) domD domI dual_order.trans)

  have *: "dom (get_trace_total x) = dom (get_trace_total y) \<Longrightarrow>
        (\<forall>lbl \<phi>1 \<phi>2. get_trace_total x lbl = Some \<phi>1 \<longrightarrow> get_trace_total y lbl = Some \<phi>2 \<longrightarrow> \<phi>1 \<le> \<phi>2) \<Longrightarrow>
        (\<forall>lbl \<phi>1 \<phi>2. get_trace_total y lbl = Some \<phi>1 \<longrightarrow> get_trace_total x lbl = Some \<phi>2 \<longrightarrow> \<phi>1 \<le> \<phi>2) \<Longrightarrow>
        get_trace_total x = get_trace_total y" (is "?A1 \<Longrightarrow> ?A2 \<Longrightarrow> ?A3 \<Longrightarrow> ?goal")
  proof (rule HOL.ext)
    fix arg
    assume "?A1" and "?A2" and "?A3"

    show "get_trace_total x arg = get_trace_total y arg"
    proof (cases "get_trace_total x arg = None")
      case True
      then show ?thesis using \<open>?A1\<close>
        by (metis domIff)
    next
      case False
      from this obtain \<phi>1 \<phi>2 where
        "get_trace_total x arg = Some \<phi>1" and
        "get_trace_total y arg = Some \<phi>2"
        using \<open>?A1\<close>
        by (metis domD domIff)

      then show ?thesis 
        using \<open>?A2\<close> \<open>?A3\<close>
        by fastforce
    qed
  qed

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_full_total_state_ext_def
    apply (rule full_total_state.equality)
       apply blast
    using *
      apply blast
     apply fastforce
    by blast
qed
end

subsection \<open>Destructors \<close>

fun get_hh_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap"
  where "get_hh_total_full \<omega> = get_hh_total (get_total_full \<omega>)"

fun get_hp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_heap"
  where "get_hp_total_full \<omega> = get_hp_total (get_total_full \<omega>)"

fun get_mh_total_full :: "'a full_total_state \<Rightarrow> mask"
  where "get_mh_total_full \<omega> = get_mh_total (get_total_full \<omega>)"

fun get_mp_total_full :: "'a full_total_state \<Rightarrow> 'a predicate_mask"
  where "get_mp_total_full \<omega> = get_mp_total (get_total_full \<omega>)"

end