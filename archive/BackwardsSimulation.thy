theory BackwardsSimulation
imports TotalSemantics
begin

type_synonym 'a simulation_rel = "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"

subsection \<open>Backwards simulation\<close>

(*definition lift_simulation_rel :: "'a simulation_rel \<Longrightarrow> *)

definition lift_sim_rel :: "'a simulation_rel \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "lift_sim_rel R w1 w2 \<equiv>
            (is_failure_config w1 \<and> is_failure_config w2 \<and> fst w1 = fst w2) \<or>
            (\<exists>\<omega>1 \<omega>2. is_normal_config w1 \<omega>1 \<and> is_normal_config w2 \<omega>2 \<and> R \<omega>1 \<omega>2 \<and> fst w1 = fst w2)"

lemma lift_sim_rel_fail: "lift_sim_rel R w1 w2 \<Longrightarrow> is_failure_config w1 \<Longrightarrow> is_failure_config w2"
  by (simp add: lift_sim_rel_def)

lemma lift_sim_rel_fail_2: "lift_sim_rel R w1 w2 \<Longrightarrow> is_failure_config w1 \<Longrightarrow> fst w1 = fst w2 \<and> snd w2 = RFailure"
  by (simp add: lift_sim_rel_def)

lemma lift_sim_rel_fail_3: "lift_sim_rel R w1 w2 \<Longrightarrow> w1 = (Inr (), RFailure) \<Longrightarrow> w2 = (Inr (), RFailure)"
  unfolding lift_sim_rel_def
  by (metis is_failure_config.elims(2) is_failure_config.elims(3) lift_sim_rel_def lift_sim_rel_fail prod.exhaust_sel snd_conv)

lemma lift_sim_rel_normal: "lift_sim_rel R w1 w2 \<Longrightarrow> is_normal_config w1 \<omega>1 \<Longrightarrow> 
                              fst w1 = fst w2 \<and> (\<exists>\<omega>2. is_normal_config w2 \<omega>2 \<and> R \<omega>1 \<omega>2)"
  unfolding lift_sim_rel_def by auto

lemma lift_sim_rel_not_magic: "lift_sim_rel R w1 w2 \<Longrightarrow> snd w1 \<noteq> RMagic \<and> snd w2 \<noteq> RMagic"
  unfolding lift_sim_rel_def by fastforce

lemma red_stmt_total_start_normal:
  assumes "red_stmt_total_single Pr \<Delta> conf w1 w2"
  shows "\<exists>\<omega>. is_normal_config w1 \<omega>"
  using assms
  by (cases) auto

lemma backwards_simulation_aux:
  assumes "red_stmt_total_multi Pr \<Delta> conf ((Inl s, RNormal \<omega>)) w" and
          single_step:"\<And> s \<omega> w' w2'. red_stmt_total_single Pr \<Delta> conf (Inl s, RNormal \<omega>) w' \<Longrightarrow> lift_sim_rel R w' w2' \<Longrightarrow>                               
                      \<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'"
 shows "\<And>w2'. lift_sim_rel R w w2' \<Longrightarrow> \<exists> \<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'"
using assms(1)
proof (induction rule: rtranclp_induct)
  case base   
    from this obtain \<omega>2' where "w2' = (Inl s, RNormal \<omega>2')" and "R \<omega> \<omega>2'"
    unfolding lift_sim_rel_def
    by (metis fstI is_failure_config.elims(2) is_normal_config.elims(2) prod.collapse snd_conv stmt_result_total.distinct(5) stmt_result_total.inject)
  show ?case
    apply (rule exI)
    apply (rule conjI[OF \<open>R \<omega> \<omega>2'\<close>])
    by (simp add: \<open>w2' = _\<close>)        
next
  case (step y z)
  from this obtain s'' \<omega>'' where "y = (Inl s'', RNormal \<omega>'')"
    by (meson red_stmt_total_single.cases)
  with step.hyps step.prems single_step obtain \<omega>2'' where "R \<omega>'' \<omega>2''" and
    RedW2'':"red_stmt_total_single Pr2 \<Delta> conf2 (Inl s'', RNormal \<omega>2'') w2'"
    by blast
  hence "lift_sim_rel R y (Inl s'', RNormal \<omega>2'')"
    unfolding lift_sim_rel_def
    using \<open>y = _\<close>
    by simp
  with step.IH obtain \<omega>2 where "R \<omega> \<omega>2" and 
    "red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) (Inl s'', RNormal \<omega>2'')"
    by blast
  then show ?case
    using RedW2''
    by fastforce
qed

lemma result_normal_exhaust: 
   "w \<noteq> RMagic \<Longrightarrow> w \<noteq> RFailure \<Longrightarrow> \<exists>\<omega>. w = RNormal \<omega>"
  by (cases w) auto

lemma stmt_config_normal_exhaust:
  assumes "\<not>is_failure_config w" and "snd w \<noteq> RMagic"
  shows "\<exists>\<omega>. is_normal_config w \<omega>"
proof -
  from assms have "\<exists>\<omega>. snd w = RNormal \<omega>"
    using result_normal_exhaust
    by auto
  thus ?thesis
    by simp
qed

lemma lift_total_rel:
  assumes "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'"
  shows "\<forall>w :: 'a stmt_config. snd w \<noteq> RMagic \<longrightarrow> (\<exists>w'. lift_sim_rel R w w')"
proof (rule allI, rule impI)+
  fix w :: "'a stmt_config"
  assume *:"snd w \<noteq> RMagic"
  show "\<exists>w'. lift_sim_rel R w w'"
  proof (cases "is_failure_config w")
    case False   
    from stmt_config_normal_exhaust[OF False *] obtain \<omega> where NormW:"is_normal_config w \<omega>"
      by auto
    moreover obtain \<omega>' where "R \<omega> \<omega>'" using assms 
      by blast
    show ?thesis 
      apply (rule exI[where ?x="(fst w, RNormal \<omega>')"])
      apply (unfold lift_sim_rel_def)
      using NormW \<open>R \<omega> \<omega>'\<close>
      by auto
  qed (auto simp: lift_sim_rel_def)
qed   

lemma backwards_simulation:
  assumes initial_rel: "\<And> \<omega> \<omega>2. is_empty_total \<omega> \<Longrightarrow> R \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2" and
          total_rel: "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'" and
          single_step:"\<And> s \<omega> w' w2'. red_stmt_total_single Pr \<Delta> conf (Inl s, RNormal \<omega>) w' \<Longrightarrow> lift_sim_rel R w' w2' \<Longrightarrow>                               
                      \<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'" and
        verif:"stmt_verifies_total (dummy :: 'a) Pr2 \<Delta> conf2 s"
 shows "stmt_verifies_total (dummy :: 'a) Pr \<Delta> conf s"
  unfolding stmt_verifies_total_def    
proof ( (rule allI | rule impI) +)
  fix \<omega>::"'a full_total_state" and w'
  assume "is_empty_total \<omega>" and Red:"red_stmt_total_multi Pr \<Delta> conf (Inl s, RNormal \<omega>) w'"
  show "\<not> (is_failure_config w')"
  proof (cases "snd w' \<noteq> RMagic")
    case True
    from this obtain w2 where RelResult:"lift_sim_rel R w' w2" using lift_total_rel[OF assms(2)]
      by blast
    from this Red obtain \<omega>2 where "R \<omega> \<omega>2" and "red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2"
      using backwards_simulation_aux single_step
      by blast
    then show ?thesis
      using verif initial_rel[OF \<open>is_empty_total \<omega>\<close> \<open>R \<omega> \<omega>2\<close>] RelResult lift_sim_rel_fail
      unfolding stmt_verifies_total_def
      by blast      
  qed (simp)
qed

end