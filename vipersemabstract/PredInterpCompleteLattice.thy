theory PredInterpCompleteLattice
  imports EquiViper
begin

type_synonym 'v pred_interp = "'v predicate_loc \<rightharpoonup> 'v virtual_state set"
type_synonym 'v domain_interp = "'v \<Rightarrow> abs_type"
type_synonym 'v fun_interp = "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'v virtual_state \<rightharpoonup> 'v val"



section \<open>Partial Order of pred_interp\<close>

fun smaller_vstate_set_opt :: "'v virtual_state set option \<Rightarrow> 'v virtual_state set option \<Rightarrow> bool" ("_ \<sqsubseteq> _" [51, 51] 50) where
  "None \<sqsubseteq> _ \<longleftrightarrow> True"
| "_ \<sqsubseteq> None \<longleftrightarrow> False"
| "Some S \<sqsubseteq> Some S' \<longleftrightarrow> S \<subseteq> S'"

definition smaller_pred_interp :: "'v pred_interp \<Rightarrow> 'v pred_interp \<Rightarrow> bool" ("_ \<preceq> _" [51, 51] 50) where
  "\<Delta> \<preceq> \<Delta>' \<longleftrightarrow> (\<forall>l. \<Delta> l \<sqsubseteq> \<Delta>' l)"

lemma smaller_pred_interp_rule:
  assumes "\<And>l. \<Delta> l \<sqsubseteq> \<Delta>' l"
  shows "\<Delta> \<preceq> \<Delta>'"
  by (simp add: assms smaller_pred_interp_def)



section \<open>Monotonicity\<close>

definition inc_sat_assertion :: "'v domain_interp \<Rightarrow> 'v fun_interp \<Rightarrow> assertion \<Rightarrow> bool" where
  "inc_sat_assertion D F A \<longleftrightarrow> (\<forall>\<Delta> \<Delta>' :: 'v pred_interp. \<forall>\<omega> :: 'v equi_state. \<Delta> \<preceq> \<Delta>' \<longrightarrow> \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle> \<longrightarrow> \<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle>)"

lemma inc_sat_assertion_rule:
  assumes "\<And>\<Delta> \<Delta>' \<omega>. \<Delta> \<preceq> \<Delta>' \<Longrightarrow> \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle> \<Longrightarrow> \<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle>"
  shows "inc_sat_assertion D F A"
  by (simp add: assms inc_sat_assertion_def)

definition dec_sat_assertion :: "'v domain_interp \<Rightarrow> 'v fun_interp \<Rightarrow> assertion \<Rightarrow> bool" where
  "dec_sat_assertion D F A \<longleftrightarrow> (\<forall>\<Delta> \<Delta>' :: 'v pred_interp. \<forall>\<omega> :: 'v equi_state. \<Delta> \<preceq> \<Delta>' \<longrightarrow> (\<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle> \<longrightarrow> \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle>))"

lemma dec_sat_assertion_rule:
  assumes "\<And>\<Delta> \<Delta>' \<omega>. \<Delta> \<preceq> \<Delta>' \<Longrightarrow> \<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle> \<Longrightarrow> \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> \<Turnstile> \<langle>A; \<omega>\<rangle>"
  shows "dec_sat_assertion D F A"
  by (simp add: assms dec_sat_assertion_def)

definition inc_assertion_upt :: "('v pred_interp \<Rightarrow> 'v virtual_state set) \<Rightarrow> bool" where
  "inc_assertion_upt f \<longleftrightarrow> (\<forall>\<Delta> \<Delta>' :: 'v pred_interp. \<Delta> \<preceq> \<Delta>' \<longrightarrow> f \<Delta> \<subseteq> f \<Delta>')"

lemma inc_assertion_upt_rule:
  assumes "\<And>\<Delta> \<Delta>' \<omega>. \<Delta> \<preceq> \<Delta>' \<Longrightarrow> \<omega> \<in> f \<Delta> \<Longrightarrow> \<omega> \<in> f \<Delta>'"
  shows "inc_assertion_upt f"
  by (simp add: assms inc_assertion_upt_def subsetI)

definition dec_assertion_upt :: "('v pred_interp \<Rightarrow> 'v virtual_state set) \<Rightarrow> bool" where
  "dec_assertion_upt f \<longleftrightarrow> (\<forall>\<Delta> \<Delta>' :: 'v pred_interp. \<Delta> \<preceq> \<Delta>' \<longrightarrow> f \<Delta> \<supseteq> f \<Delta>')"

lemma dec_assertion_upt_rule:
  assumes "\<And>\<Delta> \<Delta>' \<omega>. \<Delta> \<preceq> \<Delta>' \<Longrightarrow> \<omega> \<in> f \<Delta>' \<Longrightarrow> \<omega> \<in> f \<Delta>"
  shows "dec_assertion_upt f"
  by (simp add: assms dec_assertion_upt_def subsetI)

definition mono_inc :: "('v pred_interp \<Rightarrow> 'v pred_interp) \<Rightarrow> bool" where
  "mono_inc f \<longleftrightarrow> (\<forall>\<Delta> \<Delta>' :: 'v pred_interp. \<Delta> \<preceq> \<Delta>' \<longrightarrow> f \<Delta> \<preceq> f \<Delta>')"

lemma mono_inc_rule:
  assumes "\<And>\<Delta> \<Delta>' l. \<Delta> \<preceq> \<Delta>' \<Longrightarrow> f \<Delta> l \<sqsubseteq> f \<Delta>' l"
  shows "mono_inc f"
  by (simp add: assms mono_inc_def smaller_pred_interp_rule)



section \<open>Instantiations\<close>

subsection \<open>Instantiation of order\<close>

instantiation option :: (order) order
begin

fun less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_eq_option None _ \<longleftrightarrow> True"
| "less_eq_option _ None \<longleftrightarrow> False"
| "less_eq_option (Some a) (Some b) \<longleftrightarrow> a \<le> b"

definition less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_option a b \<longleftrightarrow> (a \<le> b) \<and> a \<noteq> b"

instance proof
  fix x y :: "'a option"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not>(y \<le> x)"
    by (metis antisym less_eq_option.elims(2) less_eq_option.simps(2) less_option_def option.inject)
next
  fix x y z :: "'a option"
  assume "x \<le> y"
     and "y \<le> z"
  show "x \<le> z"
    by (metis \<open>x \<le> y\<close> \<open>y \<le> z\<close> less_eq_option.elims(1) option.distinct(1) option.inject preorder_class.order.trans)
next
  fix x :: "'a option"
  show "x \<le> x"
    by (metis less_eq_option.elims(3) option.discI option.inject preorder_class.order_refl)
next
  fix x y :: "'a option"
  assume "x \<le> y"
     and "y \<le> x"
  show "x = y"
    by (metis \<open>x \<le> y\<close> \<open>y \<le> x\<close> less_eq_option.elims(2) less_eq_option.simps(2) option.inject order_class.order_antisym)
qed

end


lemma same_smaller_vstate_set_opt:
  "S \<sqsubseteq> S' \<longleftrightarrow> S \<le> S'"
  by (metis less_eq_option.elims(1) option.discI smaller_vstate_set_opt.elims(1) smaller_vstate_set_opt.simps(3))

lemma same_smaller_pred_interp:
  shows "\<Delta> \<preceq> \<Delta>' \<longleftrightarrow> \<Delta> \<le> \<Delta>'"
  by (simp add: le_fun_def same_smaller_vstate_set_opt smaller_pred_interp_def)

lemma same_mono:
  "mono_inc f \<longleftrightarrow> order_class.mono f"
  by (metis (mono_tags) mono_inc_def order_class.monoD order_class.monoI same_smaller_pred_interp)



subsection \<open>Instantiation of complete lattice\<close>

instantiation option :: (complete_lattice) complete_lattice
begin

definition Inf_option :: "'a option set \<Rightarrow> 'a option" where
  "Inf_option A = (if \<exists>x \<in> A. x = None then None else Some (Inf {x. Some x \<in> A}))"

definition Sup_option :: "'a option set \<Rightarrow> 'a option" where
  "Sup_option A = (if \<forall>x \<in> A. x = None then None else Some (Sup {x. Some x \<in> A}))"

definition bot_option :: "'a option" where
  "bot_option = None"

definition sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "sup_option x y = (
    if x = None then y else (
      if y = None then x else Some (sup (the x) (the y))
    )
  )"

definition top_option :: "'a option" where
  "top_option = Some top"

definition inf_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "inf_option x y = (
    if x = None \<or> y = None then None else Some (inf (the x) (the y))
  )"

lemma inf_commute:
  "inf (x :: 'a option) y = inf y x"
proof (cases "x = None \<or> y = None")
  case True
  then show ?thesis
    using inf_option_def by auto
next
  case False
  moreover have "inf (the x) (the y) = inf (the y) (the x)"
    by (simp add: inf.commute)
  ultimately show ?thesis
    by (simp add: inf_option_def)
qed

lemma sup_commute:
  "sup (x :: 'a option) y = sup y x"
proof (cases "x = None")
  case True
  then show ?thesis
    by (simp add: sup_option_def)
next
  case False
  then show ?thesis
  proof (cases "y = None")
    case True
    then show ?thesis
      by (simp add: sup_option_def)
  next
    case False
    moreover have "sup (the x) (the y) = sup (the y) (the x)"
      by (simp add: sup.commute)
    ultimately show ?thesis
      using sup_option_def by auto
  qed
qed

instance proof
  fix x y :: "'a option"
  show "inf x y \<le> x"
    using inf_option_def by auto
  show "inf x y \<le> y"
    using inf_option_def by auto
  show "x \<le> sup x y"
    using sup_option_def by auto
  show "y \<le> sup x y"
    using sup_option_def by auto
next
  fix x y z :: "'a option"
  assume "x \<le> y"
     and "x \<le> z"
  then show "x \<le> inf y z"
    using inf_option_def less_eq_option.elims(3) by fastforce
next
  fix y x z :: "'a option"
  assume "y \<le> x"
     and "z \<le> x"
  then show "sup y z \<le> x"
    using less_eq_option.elims(3) sup_option_def by fastforce
next
  fix x :: "'a option"
  fix A :: "'a option set"
  assume "x \<in> A"
  show "Inf A \<le> x"
  proof (cases "\<exists>y \<in> A. y = None")
    case True
    then have "Inf A = None"
      by (simp add: Inf_option_def)
    then show ?thesis
      by simp
  next
    case False
    then have "x \<noteq> None"
      by (metis \<open>x \<in> A\<close>)
    then obtain v where "x = Some v"
      by auto
    moreover obtain u where
          "Inf A = Some u"
      and "u = Inf {y. Some y \<in> A}"
      using False Inf_option_def by auto
    moreover have "u \<le> v"
      by (metis Inf_lower \<open>x \<in> A\<close> calculation(1) calculation(3) mem_Collect_eq)
    ultimately show ?thesis
      by simp
  qed
  show "x \<le> Sup A"
  proof (cases "x = None")
    case True
    then show ?thesis
      by simp
  next
    case False
    then obtain v where "x = Some v"
      by auto
    have "\<not>(\<forall>y \<in> A. y = None)"
      using False \<open>x \<in> A\<close> by auto
    then obtain u where
          "Sup A = Some u"
      and "u = Sup {y. Some y \<in> A}"
      by (simp add: Sup_option_def)
    then have "v \<le> u"
      by (metis Sup_upper \<open>x = Some v\<close> \<open>x \<in> A\<close> mem_Collect_eq)
    then show ?thesis
      by (simp add: \<open>Sup A = Some u\<close> \<open>x = Some v\<close>)
  qed
next
  fix A :: "'a option set"
  fix z :: "'a option"
  assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  then show "z \<le> Inf A"
  proof (cases "z = None")
    case True
    then show ?thesis
      by simp
  next
    case False
    then obtain w where "z = Some w"
      by auto
    have "\<not>(\<exists>y \<in> A. y = None)"
      using \<open>\<And>x. x \<in> A \<Longrightarrow> z \<le> x\<close> \<open>z = Some w\<close> less_eq_option.simps(2) by blast
    then obtain u where
          "Inf A = Some u"
      and "u = Inf {y. Some y \<in> A}"
      by (simp add: Inf_option_def)
    moreover have "w \<le> u"
    proof -
      have "\<And>v. v \<in> {y. Some y \<in> A} \<Longrightarrow> w \<le> v"
        using \<open>\<And>x. x \<in> A \<Longrightarrow> z \<le> x\<close> \<open>z = Some w\<close> less_eq_option.simps(3) by blast
      then show ?thesis
        by (simp add: calculation(2) le_Inf_iff)
    qed
    ultimately show ?thesis
      by (simp add: \<open>z = Some w\<close>)
  qed
next
  fix A :: "'a option set"
  fix z :: "'a option"
  assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  then show "Sup A \<le> z"
  proof (cases "\<forall>y \<in> A. y = None")
    case True
    then have "Sup A = None"
      by (simp add: Sup_option_def)
    then show ?thesis
      by simp
  next
    case False
    then obtain u where
          "Sup A = Some u"
      and "u = Sup {y. Some y \<in> A}"
      by (simp add: Sup_option_def)
    moreover obtain w where "z = Some w"
      by (meson False \<open>\<And>x. x \<in> A \<Longrightarrow> x \<le> z\<close> less_eq_option.elims(2))
    moreover have "u \<le> w"
    proof -
      have "\<And>v. v \<in> {y. Some y \<in> A} \<Longrightarrow> v \<le> w"
        using \<open>\<And>x. x \<in> A \<Longrightarrow> x \<le> z\<close> calculation(3) by fastforce
      then show ?thesis
        using Sup_least calculation(2) by blast
    qed
    ultimately show ?thesis
      by simp
  qed
next
  have "{x. Some x \<in> {}} = {}"
    by simp
  then show "Inf {} = (top :: 'a option)"
    by (simp add: Inf_option_def top_option_def)
next
  have "\<forall>x \<in> {}. x = None"
    by simp
  then show "Sup {} = (bot :: 'a option)"
    by (simp add: Sup_option_def bot_option_def)
qed

end



end