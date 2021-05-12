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

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)
type_synonym 'a full_total_state = "'a store \<times> 'a total_trace \<times> 'a total_state"

subsection \<open>Destructors for (full) total state\<close>

fun get_heap_total :: "'a total_state \<Rightarrow> 'a total_heap" where "get_heap_total \<phi> = snd (Rep_total_state \<phi>)"
fun get_mask_total :: "'a total_state \<Rightarrow> mask" where "get_mask_total \<phi> = fst (Rep_total_state \<phi>)"


fun get_store_total :: "'a full_total_state \<Rightarrow> 'a store" where "get_store_total (\<sigma>,_,_) = \<sigma>"
fun get_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace" where "get_trace_total (_,\<tau>,_) = \<tau>"
fun get_heap_total_full :: "'a full_total_state \<Rightarrow> 'a total_heap" where "get_heap_total_full (_,_,\<phi>) = get_heap_total \<phi>"
fun get_mask_total_full :: "'a full_total_state \<Rightarrow> mask" where "get_mask_total_full (_,_,\<phi>) = get_mask_total \<phi>"
fun get_hm_total_full :: "'a full_total_state \<Rightarrow> 'a total_state"
  where "get_hm_total_full (_,_,\<phi>) = \<phi>"

subsection \<open>Addition of total states\<close>

fun compatible_pre_states_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> bool"
  where
    "compatible_pre_states_total (m1,h1) (m2,h2) = 
    ( (\<forall>l. (pgte (m1 l) pnone \<and> pgte (m2 l) pnone) \<longrightarrow> (h1 l = h2 l)) \<and>
      wf_mask_simple (add_masks m1 m2))"

text \<open>For compatible states, always the heap value of the first state is taken if the second state 
does not have positive permission to the corresponding location.\<close>

fun pre_plus_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> 'a pre_total_state option" where
  "pre_plus_total (m1,h1) (m2,h2) =
    (if compatible_pre_states_total (m1,h1) (m2,h2) then
       Some (add_masks m1 m2, \<lambda>l. if ((pgt (m2 l) pnone)) then h2 l else h1 l)
     else None)"

fun plus_total :: "'a total_state \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state option"  where
  "plus_total \<phi>1 \<phi>2 = map_option Abs_total_state  (pre_plus_total (Rep_total_state \<phi>1) (Rep_total_state \<phi>2))"

fun plus_full_total :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state option" (infixl "|\<oplus>|\<^sub>t" 60) where
  "(\<sigma>1,\<tau>1,\<phi>1) |\<oplus>|\<^sub>t (\<sigma>2,\<tau>2,\<phi>2) = 
           (if \<sigma>1 = \<sigma>2 \<and> \<tau>1 = \<tau>2 then map_option (\<lambda>res. (\<sigma>1,\<tau>1,res)) (plus_total \<phi>1 \<phi>2) else None)"


abbreviation plus_total_set where 
"plus_total_set \<equiv> sep_algebra.add_set plus_full_total"

end