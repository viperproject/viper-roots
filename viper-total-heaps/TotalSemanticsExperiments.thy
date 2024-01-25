theory TotalSemanticsExperiments
imports TotalExpressions
begin

section \<open>This theory is used to experiment with definitions and lemmas that could potentially be added 
later to the TotalSemantics theory\<close>

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a stmt_result_total"

fun is_failure_config :: "'a stmt_config \<Rightarrow> bool"
  where "is_failure_config config \<longleftrightarrow> (snd config) = RFailure"

fun is_normal_config :: "'a stmt_config \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "is_normal_config config \<omega> \<longleftrightarrow> (snd config) = RNormal \<omega>"

end