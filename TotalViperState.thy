section \<open>Viper State with a Total Heap\<close>

theory TotalViperState
imports Viper.ValueAndBasicState Viper.SepAlgebra
begin

type_synonym 'a total_heap = "heap_loc \<Rightarrow> 'a val"

(* We ignore predicates for now *)
type_synonym 'a pre_total_state = "mask \<times> 'a total_heap"

fun wf_pre_total_state :: "'a pre_total_state \<Rightarrow> bool" where
  "wf_pre_total_state (\<pi>, h) \<longleftrightarrow> wf_mask_simple \<pi>"

typedef 'a total_state = "{ \<phi> :: 'a pre_total_state |\<phi>. wf_pre_total_state \<phi> }"
  apply (rule_tac x="(zero_mask, \<lambda>a. VInt 0)" in exI)
  apply (simp add: wf_zero_mask)
  done

setup_lifting type_definition_total_state

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)
type_synonym 'a full_total_state = "'a store \<times> 'a total_trace \<times> 'a total_state"

subsection \<open>Destructors for (full) total state\<close>

(*lift_definition get_heap_total :: "'a total_state \<Rightarrow> 'a total_heap" is "snd" done*)
fun get_heap_total :: "'a total_state \<Rightarrow> 'a total_heap" where "get_heap_total \<phi> = snd (Rep_total_state \<phi>)"
fun get_mask_total :: "'a total_state \<Rightarrow> mask" where "get_mask_total \<phi> = fst (Rep_total_state \<phi>)"

lemma get_mask_total_wf: "wf_mask_simple (get_mask_total \<phi>)"  
  using Rep_total_state
  by (metis get_mask_total.simps mem_Collect_eq prod.exhaust_sel wf_pre_total_state.simps)


fun get_store_total :: "'a full_total_state \<Rightarrow> 'a store" where "get_store_total \<omega> = fst \<omega>"
fun get_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace" where "get_trace_total \<omega> = fst (snd \<omega>)"
fun get_hm_total_full :: "'a full_total_state \<Rightarrow> 'a total_state"
  where "get_hm_total_full \<omega> = snd (snd \<omega>)"
fun get_heap_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap" where "get_heap_total_full \<omega> = get_heap_total (get_hm_total_full \<omega>)"
fun get_mask_total_full :: "'a full_total_state \<Rightarrow> mask" where "get_mask_total_full \<omega> = get_mask_total (get_hm_total_full \<omega>)"

lemma total_state_eq:
  assumes "get_mask_total \<phi> = get_mask_total \<phi>'" and
          "get_heap_total \<phi> = get_heap_total \<phi>'"
  shows "\<phi> = \<phi>'"
  using assms
  by (metis Rep_total_state_inverse get_heap_total.simps get_mask_total.simps surjective_pairing)

lemma full_total_state_eq: 
  assumes "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'" and 
          "get_heap_total_full \<omega> = get_heap_total_full \<omega>'" and
          "get_mask_total_full \<omega> = get_mask_total_full \<omega>'"
        shows "\<omega> = \<omega>'"
  using assms
  by (metis Rep_total_state_inject get_heap_total.elims get_heap_total_full.elims get_hm_total_full.elims get_mask_total.elims get_mask_total_full.elims get_store_total.elims get_trace_total.elims prod.expand) 

lemma get_hm_total_full_comp: "Rep_total_state (get_hm_total_full \<omega>) = (get_mask_total_full \<omega>, get_heap_total_full \<omega>)"
  by simp

lemma get_mask_total_full_wf: "wf_mask_simple (get_mask_total_full \<omega>)"
  using get_mask_total_wf
  by (metis get_mask_total_full.elims)

subsection \<open>Addition of total states\<close>

fun compatible_pre_states_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> bool"
  where
    "compatible_pre_states_total s1 s2 =     
    (let m1 = (fst s1); h1 = snd (s1); m2 = (fst s2); h2 = snd s2 in
    ( (\<forall>l. (pgt (m1 l) pnone \<and> pgt (m2 l) pnone) \<longrightarrow> (h1 l = h2 l)) \<and>
      wf_mask_simple (add_masks m1 m2))
    )"

definition add_total_heaps :: "'a total_heap \<Rightarrow> 'a total_heap \<Rightarrow> mask \<Rightarrow> 'a total_heap"
  where "add_total_heaps h1 h2 m2 = (\<lambda>l. if ((pgt (m2 l) pnone)) then h2 l else h1 l)"

text \<open>For compatible states, always the heap value of the first state is taken if the second state 
does not have positive permission to the corresponding location.\<close>

fun pre_plus_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> 'a pre_total_state option" where
  "pre_plus_total s1 s2 =
    (if compatible_pre_states_total s1 s2 then
       Some (add_masks (fst s1) (fst s2), add_total_heaps (snd s1) (snd s2) (fst s2))
     else None)"

lemma add_total_heaps_pos_compat:
  assumes "m1 hl \<noteq> pnone" and "compatible_pre_states_total (m1,h1) (m2,h2)"
  shows "(add_total_heaps h1 h2 m2) hl = h1 hl"
proof (cases "pgt (m2 hl) pnone")
  case True
  hence "h1 hl = h2 hl" using assms    
    apply simp
    apply (drule prat_pnone_pgt)
    by (metis prod.exhaust)
  thus ?thesis
    by (simp add: add_total_heaps_def)
qed (simp add: add_total_heaps_def)

fun plus_total :: "'a total_state \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state option"  where
  "plus_total \<phi>1 \<phi>2 = map_option Abs_total_state (pre_plus_total (Rep_total_state \<phi>1) (Rep_total_state \<phi>2))"

fun plus_total_full :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state option" (infixl "|\<oplus>|\<^sub>t" 60) where
  (*"(\<sigma>1,\<tau>1,\<phi>1) |\<oplus>|\<^sub>t (\<sigma>2,\<tau>2,\<phi>2) = 
           (if \<sigma>1 = \<sigma>2 \<and> \<tau>1 = \<tau>2 then map_option (\<lambda>res. (\<sigma>1,\<tau>1,res)) (plus_total \<phi>1 \<phi>2) else None)"*)
 "\<omega>1 |\<oplus>|\<^sub>t \<omega>2 = 
           (if fst \<omega>1 = fst \<omega>2 \<and> fst (snd \<omega>1) = fst (snd \<omega>2) then map_option (\<lambda>res. (fst \<omega>1, fst (snd \<omega>1),res)) (plus_total (snd (snd \<omega>1)) (snd (snd \<omega>2))) else None)"

lemma plus_total_full_properties:
  assumes "\<omega>1 |\<oplus>|\<^sub>t \<omega>2 = Some \<omega>3"
  shows "compatible_pre_states_total (get_mask_total_full \<omega>1, get_heap_total_full \<omega>1) (get_mask_total_full \<omega>2, get_heap_total_full \<omega>2) \<and> 
         get_mask_total_full \<omega>3 = add_masks (get_mask_total_full \<omega>1) (get_mask_total_full \<omega>2) \<and> 
         get_heap_total_full \<omega>3 = add_total_heaps (get_heap_total_full \<omega>1) (get_heap_total_full \<omega>2) (get_mask_total_full \<omega>2) \<and>
         get_store_total \<omega>1 = get_store_total \<omega>3 \<and>
         get_trace_total \<omega>1 = get_trace_total \<omega>3" (is "compatible_pre_states_total (?m1,?h1) (?m2,?h2) \<and> ?Q")
  using assms
proof -
  let ?hm1 = "get_hm_total_full \<omega>1"
  let ?hm2 = "get_hm_total_full \<omega>2"
  have R1: "Rep_total_state ?hm1 = (?m1, ?h1)" and R2:"Rep_total_state ?hm2 = (?m2, ?h2)"
    by simp_all
  from assms have A0:"plus_total ?hm1 ?hm2 = Some (get_hm_total_full \<omega>3)"
    by (clarsimp split: if_split_asm)
  hence A1:"pre_plus_total (?m1, ?h1) (?m2, ?h2) = Some (add_masks ?m1 ?m2, add_total_heaps ?h1 ?h2 ?m2) \<and> compatible_pre_states_total (?m1, ?h1) (?m2, ?h2)"
    apply (clarsimp simp del: get_hm_total_full.simps)
    apply (subst R1 R2)+
    apply (subst (asm) R1 R2)+
    by (metis fst_conv option.discI snd_conv)  
  hence A2:"Some (get_hm_total_full \<omega>3) = Some (Abs_total_state (add_masks ?m1 ?m2, add_total_heaps ?h1 ?h2 ?m2))"
    using A0
    by simp
  hence "get_mask_total_full \<omega>3 = add_masks ?m1 ?m2"
    using HOL.conjunct2[OF A1]
    by (metis (mono_tags, lifting) Abs_total_state_inverse compatible_pre_states_total.simps fst_conv get_hm_total_full_comp mem_Collect_eq option.inject wf_pre_total_state.simps) 
  moreover from A2 have "get_heap_total_full \<omega>3 = add_total_heaps ?h1 ?h2 ?m2"
    using HOL.conjunct2[OF A1]
    by (metis Abs_total_state_inverse calculation get_hm_total_full_comp get_mask_total_full_wf mem_Collect_eq option.inject sndI wf_pre_total_state.simps) 
  ultimately show ?thesis
    using HOL.conjunct2[OF A1] assms
    by (clarsimp split: if_split_asm)
qed

definition plus_total_full_set :: "('a full_total_state) set \<Rightarrow> ('a full_total_state) set \<Rightarrow> ('a full_total_state) set"
  where
    "plus_total_full_set A B \<equiv> { \<phi> | \<phi> a b. a \<in> A \<and> b \<in> B \<and> Some \<phi> = a |\<oplus>|\<^sub>t b }"
                  

end