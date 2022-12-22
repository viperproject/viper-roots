theory TotalConsistency
imports TotalExpressions
begin


definition red_inhale_nset :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> ('a full_total_state) set"
  where "red_inhale_nset ctxt R A \<omega> = { \<omega>'. red_inhale ctxt R A \<omega> (RNormal \<omega>')}"

definition unfold_rel_general_set  :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> ('a full_total_state) set \<Rightarrow> ('a full_total_state) set \<Rightarrow> bool"
  where "unfold_rel_general_set ctxt R W W' \<equiv> \<exists> pred vs q. W' = {\<omega>'. \<exists> \<omega> \<in> W. unfold_rel ctxt R pred vs q \<omega> \<omega>'}"

definition unfold_rel_multi_set :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> ('a full_total_state) set \<Rightarrow> ('a full_total_state) set \<Rightarrow> bool"
  where "unfold_rel_multi_set ctxt R \<equiv> rtranclp (unfold_rel_general_set ctxt R)"

(*
definition unfold_consistent_set :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "unfold_consistent_set Pr \<Delta> \<omega> \<equiv>
          \<forall> W' \<omega>' pred_id vs q. (unfold_rel_multi_set Pr \<Delta> {\<omega>} W' \<and> \<omega>' \<in> W' \<and> pgt (get_mp_total_full \<omega>' (pred_id,vs)) q) \<longrightarrow> 
               (\<exists>\<omega>1 \<omega>2. \<omega>1 \<in> W' \<and> unfold_rel Pr \<Delta> pred_id vs q \<omega>1 \<omega>2)"

lemma unfolding_consistent_1:
  assumes "unfold_consistent Pr \<Delta> \<omega>"
  shows "unfold_consistent_set Pr \<Delta> \<omega>"  
  unfolding unfold_consistent_set_def
proof ((rule allI)+, rule impI)
  fix W' \<omega>' pred_id vs q
  assume "unfold_rel_multi_set Pr \<Delta> {\<omega>} W' \<and> \<omega>' \<in> W' \<and> pgt (get_mp_total_full \<omega> (pred_id, vs)) q"
  oops
*)

lemma unfold_rel_general_set_non_empty:
  assumes "unfold_rel_general_set ctxt R W W'" and "W' \<noteq> {}"
  shows "W \<noteq> {}"
  using assms
  unfolding unfold_rel_general_set_def
  by blast

(* This theorem is harder to prove with the corrected definition of total heap consistency that unfolds
a full predicate at each step.

lemma unfolding_consistent_1: 
  assumes "unfold_rel_multi_set ctxt R W1 W2" and "W1 \<noteq> {}" and 
          "\<forall> \<omega> \<in> W1. total_heap_consistent ctxt \<omega>" and "W2 \<noteq> {}"
  shows "\<exists>\<omega>' \<in> W2. total_heap_consistent ctxt \<omega>'"
  using assms
  unfolding unfold_rel_multi_set_def
proof (induction rule: rtranclp_induct)
case base
  thus ?case by blast
next
  case (step W2 W3)
  from this obtain \<omega>2 where "\<omega>2 \<in> W2" and \<omega>2_cons:"total_heap_consistent ctxt \<omega>2" using unfold_rel_general_set_non_empty by blast
  from step(2) obtain pred_id vs q where "W3 = {\<omega>'. \<exists> \<omega> \<in> W2. unfold_rel ctxt R pred_id vs q \<omega> \<omega>'}"
    unfolding unfold_rel_general_set_def by blast
  with \<open>W3 \<noteq> {}\<close> and \<open>\<omega>2 \<in> W2\<close> have "pgt (get_mp_total_full \<omega>2 (pred_id,vs)) q"
    
    
  from \<omega>2_cons obtain \<omega>3 where "unfold_rel Pr \<Delta> pred vs q \<omega>2 \<omega>3"
    apply (cases rule: total_heap_consistent.cases)
  then show ?case    
qed
*)

end