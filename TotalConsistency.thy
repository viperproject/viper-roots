theory TotalConsistency
imports TotalExpressions
begin


definition red_inhale_nset :: "program \<Rightarrow>  'a interp \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> ('a full_total_state) set"
  where "red_inhale_nset Pr \<Delta> R A \<omega> = { \<omega>'. red_inhale Pr \<Delta> R A \<omega> (RNormal \<omega>')}"

definition unfold_rel_general_set  :: "program \<Rightarrow> 'a interp \<Rightarrow> ('a full_total_state) set \<Rightarrow> ('a full_total_state) set \<Rightarrow> bool"
  where "unfold_rel_general_set Pr \<Delta> W W' \<equiv> \<exists> pred vs q. W' = {\<omega>'. \<exists> \<omega> \<in> W. unfold_rel Pr \<Delta> pred vs q \<omega> \<omega>'}"

definition unfold_rel_multi_set :: "program \<Rightarrow> 'a interp \<Rightarrow> ('a full_total_state) set \<Rightarrow> ('a full_total_state) set \<Rightarrow> bool"
  where "unfold_rel_multi_set Pr \<Delta> \<equiv> rtranclp (unfold_rel_general_set Pr \<Delta>)"

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

lemma unfold_rel_general_set_non_empty:
  assumes "unfold_rel_general_set Pr \<Delta> W W'" and "W' \<noteq> {}"
  shows "W \<noteq> {}"
  using assms
  unfolding unfold_rel_general_set_def
  by blast

lemma unfolding_consistent_1: 
  assumes "unfold_rel_multi_set Pr \<Delta> W1 W2" and "W1 \<noteq> {}" and 
          "\<forall> \<omega> \<in> W1. unfold_consistent Pr \<Delta> \<omega>" and "W2 \<noteq> {}"
  shows "\<exists>\<omega>' \<in> W2. unfold_consistent Pr \<Delta> \<omega>'"
  using assms
  unfolding unfold_rel_multi_set_def
proof (induction rule: rtranclp_induct)
case base
  thus ?case by blast
next
  case (step W2 W3)
  from this obtain \<omega>2 where "\<omega>2 \<in> W2" and \<omega>2_cons:"unfold_consistent Pr \<Delta> \<omega>2" using unfold_rel_general_set_non_empty by blast
  from step(2) obtain pred_id vs q where "W3 = {\<omega>'. \<exists> \<omega> \<in> W2. unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>'}"
    unfolding unfold_rel_general_set_def by blast
  with \<open>W3 \<noteq> {}\<close> and \<open>\<omega>2 \<in> W2\<close> have "pgt (get_mp_total_full \<omega>2 (pred_id,vs)) q"
    
  thm unfold_consistent.cases
  from \<omega>2_cons obtain \<omega>3 where "unfold_rel Pr \<Delta> pred vs q \<omega>2 \<omega>3"
    apply (cases rule: unfold_consistent.cases)
  then show ?case    
qed




                                       



end