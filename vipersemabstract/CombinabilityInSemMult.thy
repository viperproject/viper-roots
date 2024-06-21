theory CombinabilityInSemMult
  imports SemSynMultEquiv
begin

(* This monotonicity of virtual_state (more precisely, of partial heap part of virtual_state) of function interpretation is critical for combinability of atomic pure expressions *)
definition fun_interp_mono :: "'v fun_interp \<Rightarrow> bool" where
  "fun_interp_mono F \<longleftrightarrow> (\<forall>\<phi>1 \<phi>2 :: 'v virtual_state. \<forall>f :: function_ident. \<forall>args :: 'v val list. \<forall>v :: 'v val. F f args \<phi>1 = Some v \<and> \<phi>2 \<succeq> \<phi>1 \<longrightarrow> F f args \<phi>2 = Some v)"

section \<open>Set Closure Property\<close>

definition set_closure :: "('v virtual_state \<Rightarrow> 'v virtual_state \<Rightarrow> 'v virtual_state set) \<Rightarrow> 'v pred_interp \<Rightarrow> bool" where
  "set_closure S \<Delta> \<longleftrightarrow> (\<forall>a b l s. \<Delta> l = Some s \<and> a \<in> s \<and> b \<in> s \<longrightarrow> S a b \<subseteq> s)"

lemma set_closure_rule:
  assumes "\<And>a b l s. \<Delta> l = Some s \<Longrightarrow> a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> S a b \<subseteq> s"
  shows "set_closure S \<Delta>"
  by (meson assms set_closure_def)

lemma set_closure_imp:
  assumes "set_closure S \<Delta>"
      and "\<Delta> l = Some s"
      and "a \<in> s"
      and "b \<in> s"
      and "x \<in> S a b"
    shows "x \<in> s"
  using assms set_closure_def by blast

lemma set_closure_admissible:
  "ccpo.admissible Sup (\<le>) (set_closure S)"
proof (rule ccpo.admissibleI)
  fix A :: "'a pred_interp set"
  assume "Complete_Partial_Order.chain (\<le>) A"
     and "A \<noteq> {}"
     and "\<forall>x \<in> A. set_closure S x"
  show "set_closure S (Sup A)"
  proof (rule set_closure_rule)
    fix a b :: "'a virtual_state"
    fix l :: "'a predicate_loc"
    fix Ssup :: "'a virtual_state set"
    let ?Al = "{x l | x. x \<in> A}"
    assume "Sup A l = Some Ssup"
       and "a \<in> Ssup"
       and "b \<in> Ssup"
    then have "Some Ssup = Sup ?Al"
      by (simp add: Setcompr_eq_image)
    then have Ssup_exp: "Ssup = Sup {\<sigma>. Some \<sigma> \<in> ?Al}"
      by (metis (no_types, lifting) Collect_cong Sup_option_def option.discI option.inject)
    then obtain \<Delta>a sa where
          "\<Delta>a \<in> A"
      and "\<Delta>a l = Some sa"
      and "a \<in> sa"
      using \<open>a \<in> Ssup\<close> by force
    moreover obtain \<Delta>b sb where
          "\<Delta>b \<in> A"
      and "\<Delta>b l = Some sb"
      and "b \<in> sb"
      using Ssup_exp \<open>b \<in> Ssup\<close> by force
    ultimately show "S a b \<subseteq> Ssup"
    proof (cases "\<Delta>a \<le> \<Delta>b")
      case True
      then have "sa \<subseteq> sb"
        by (metis \<open>\<Delta>a l = Some sa\<close> \<open>\<Delta>b l = Some sb\<close> le_fun_def less_eq_option.simps(3))
      then have "a \<in> sb"
        by (simp add: \<open>a \<in> sa\<close> in_mono)
      moreover have "set_closure S \<Delta>b"
        by (simp add: \<open>\<Delta>b \<in> A\<close> \<open>\<forall>x \<in> A. set_closure S x\<close>)
      ultimately have "S a b \<subseteq> sb"
        using \<open>\<Delta>b l = Some sb\<close> \<open>b \<in> sb\<close> set_closure_def by blast
      moreover have "sb \<subseteq> Ssup"
        by (metis Sup_upper \<open>Sup A l = Some Ssup\<close> \<open>\<Delta>b \<in> A\<close> \<open>\<Delta>b l = Some sb\<close> le_funD less_eq_option.simps(3))
      ultimately show ?thesis
        by auto
    next
      case False
      then have "\<Delta>b \<le> \<Delta>a"
        by (metis \<open>Complete_Partial_Order.chain (\<le>) A\<close> \<open>\<Delta>a \<in> A\<close> \<open>\<Delta>b \<in> A\<close> chain_def)
      then have "sb \<subseteq> sa"
        by (metis \<open>\<Delta>a l = Some sa\<close> \<open>\<Delta>b l = Some sb\<close> le_fun_def less_eq_option.simps(3))
      then have "b \<in> sa"
        by (simp add: \<open>b \<in> sb\<close> in_mono)
      moreover have "set_closure S \<Delta>a"
        by (simp add: \<open>\<Delta>a \<in> A\<close> \<open>\<forall>x \<in> A. set_closure S x\<close>)
      ultimately have "S a b \<subseteq> sa"
        using \<open>\<Delta>a l = Some sa\<close> \<open>a \<in> sa\<close> set_closure_def by blast
      moreover have "sa \<subseteq> Ssup"
        by (metis Sup_upper \<open>Sup A l = Some Ssup\<close> \<open>\<Delta>a \<in> A\<close> \<open>\<Delta>a l = Some sa\<close> le_funD less_eq_option.simps(3))
      ultimately show ?thesis
        by auto
    qed
  qed
qed

lemma empty_interp_set_closure:
  "set_closure S bot"
proof (rule set_closure_rule)
  fix a b :: "'a virtual_state"
  fix l :: "'a predicate_loc"
  fix s :: "'a virtual_state set"
  assume "bot l = Some s"
  then show "S a b \<subseteq> s"
    by (simp add: bot_option_def)
qed

lemma full_interp_set_closure:
  "set_closure S top"
proof (rule set_closure_rule)
  fix a b :: "'a virtual_state"
  fix l :: "'a predicate_loc"
  fix s :: "'a virtual_state set"
  assume "top l = Some s"
  then show "S a b \<subseteq> s"
    by (simp add: top_option_def)
qed

definition preserve_set_closure :: "('v virtual_state \<Rightarrow> 'v virtual_state \<Rightarrow> 'v virtual_state set) \<Rightarrow> ('v pred_interp \<Rightarrow> 'v pred_interp) \<Rightarrow> bool" where
  "preserve_set_closure S f \<longleftrightarrow> (\<forall>\<Delta>. set_closure S \<Delta> \<longrightarrow> set_closure S (f \<Delta>))"

lemma preserve_set_closure_rule:
  assumes "\<And>\<Delta>. set_closure S \<Delta> \<Longrightarrow> set_closure S (f \<Delta>)"
  shows "preserve_set_closure S f"
  by (simp add: assms preserve_set_closure_def)

lemma preserve_set_closure_imp:
  assumes "preserve_set_closure S f"
      and "set_closure S \<Delta>"
    shows "set_closure S (f \<Delta>)"
  using assms preserve_set_closure_def by auto

theorem LFP_set_closure:
  assumes "mono_inc f"
      and "preserve_set_closure S f"
   shows "set_closure S (ccpo_class.fixp f)"
  using set_closure_admissible
proof (rule fixp_induct[of "set_closure S"])
  show "mono f"
    using assms(1) same_mono by auto
next
  show "set_closure S (Sup {})"
    by (simp add: empty_interp_set_closure)
next
  fix x :: "'a pred_interp"
  assume "set_closure S x"
  then show "set_closure S (f x)"
    using assms(2) preserve_set_closure_def by auto
qed


section \<open>Combinability\<close>

text\<open>
definition vstate_seg :: "'v virtual_state \<Rightarrow> 'v virtual_state \<Rightarrow> 'v virtual_state set" where
  "vstate_seg a b = {\<sigma> | \<sigma> p q. p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"

Final goal is to prove "wd_pred_prog P \<Longrightarrow> preserve_set_closure vstate_seg (predInterpUpdate P D F)"

To prove this, first prove atomic assertion satisfies this, then prove connective preserve this

In both proofs, we prove for more general states other than "shift_and_add_list_state (\<lambda>n. None, \<lambda>l. None, \<omega>) v" that is defined in assertion_upt

This two steps are in subsection "Combinability for satisfaction function '_ \<Turnstile> \<langle>_; _\<rangle>' of a single assertion"
\<close>

definition interp_combinable :: "'v pred_interp \<Rightarrow> bool" where
  "interp_combinable \<Delta> \<longleftrightarrow> (\<forall>l :: 'v predicate_loc. \<forall>S :: 'v virtual_state set. \<Delta> l = Some S \<longrightarrow> (\<forall>p q :: preal. \<forall>a b x :: 'v virtual_state. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> a \<in> S \<and> b \<in> S \<and> p \<odot> a \<oplus> q \<odot> b = Some x \<longrightarrow> x \<in> S))"

lemma interp_combinable_rule:
  assumes "\<And>l :: 'v predicate_loc. \<And>S :: 'v virtual_state set. \<And>p q :: preal. \<And>a b x :: 'v virtual_state. \<Delta> l = Some S \<Longrightarrow> p > 0 \<Longrightarrow> q > 0 \<Longrightarrow> p + q = 1 \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> p \<odot> a \<oplus> q \<odot> b = Some x \<Longrightarrow> x \<in> S"
  shows "interp_combinable \<Delta>"
  using assms interp_combinable_def by blast

lemma interp_combinable_imp:
  assumes "interp_combinable \<Delta>"
      and "\<Delta> l = Some S"
      and "p > 0"
      and "q > 0"
      and "p + q = 1"
      and "a \<in> S"
      and "b \<in> S"
      and "p \<odot> a \<oplus> q \<odot> b = Some x"
    shows "x \<in> S"
  using assms interp_combinable_def by blast

lemma interp_combinable_set_closure:
  "interp_combinable = set_closure (\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b})"
proof (rule ext)
  fix \<Delta> :: "'v pred_interp"
  show "interp_combinable \<Delta> \<longleftrightarrow> set_closure (\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) \<Delta>"
  proof
    assume "interp_combinable \<Delta>"
    show "set_closure (\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) \<Delta>"
    proof (rule set_closure_rule)
      fix a b :: "'v virtual_state"
      fix l :: "'v predicate_loc"
      fix s :: "'v virtual_state set"
      assume "\<Delta> l = Some s"
         and "a \<in> s"
         and "b \<in> s"
      show "{\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b} \<subseteq> s"
      proof
        fix x :: "'v virtual_state"
        assume "x \<in> {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
        then obtain p q where
              "p + q = 1"
          and "Some x = p \<odot> a \<oplus> q \<odot> b"
          and "p > 0"
          and "q > 0"
          by auto
        then show "x \<in> s"
          by (metis \<open>\<Delta> l = Some s\<close> \<open>a \<in> s\<close> \<open>b \<in> s\<close> \<open>interp_combinable \<Delta>\<close> interp_combinable_imp)
      qed
    qed
  next
    assume set_closure_assm: "set_closure (\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}) \<Delta>"
    show "interp_combinable \<Delta>"
    proof (rule interp_combinable_rule)
      fix l :: "'v predicate_loc"
      fix S :: "'v virtual_state set"
      fix p q :: preal
      fix a b x :: "'v virtual_state"
      assume "\<Delta> l = Some S"
         and "p > 0"
         and "q > 0"
         and "p + q = 1"
         and "a \<in> S"
         and "b \<in> S"
         and "p \<odot> a \<oplus> q \<odot> b = Some x"
      then have "x \<in> {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
        by fastforce
      then show "x \<in> S"
        using set_closure_assm \<open>\<Delta> l = Some S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close> set_closure_imp by blast
    qed
  qed
qed


subsection \<open>Combinability for satisfaction function "_ \<Turnstile> \<langle>_; _\<rangle>" of a single assertion\<close>

definition asst_combinable :: "('v, 'v virtual_state) interp \<Rightarrow> assertion \<Rightarrow> bool" where
  "asst_combinable I A \<longleftrightarrow> (\<forall>a b :: preal. \<forall>\<omega> :: 'v equi_state. a > 0 \<and> b > 0 \<and> (\<exists>\<alpha> \<beta> :: 'v equi_state. I \<Turnstile> \<langle>A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)) \<longrightarrow> I \<Turnstile>[sem] \<langle>A^(a + b); \<omega>\<rangle>)"

lemma asst_combinable_rule_origin:
  assumes "\<And>a b :: preal. \<And>\<omega> :: 'v equi_state. a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (\<exists>\<alpha> \<beta> :: 'v equi_state. I \<Turnstile> \<langle>A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)) \<Longrightarrow> I \<Turnstile>[sem] \<langle>A^(a + b); \<omega>\<rangle>"
  shows "asst_combinable I A"
  by (simp add: assms asst_combinable_def)

lemma asst_combinable_rule:
  assumes "\<And>a b :: preal. \<And>\<omega> :: 'v equi_state. a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a + b = 1 \<Longrightarrow> \<exists>\<alpha> \<beta> :: 'v equi_state. I \<Turnstile> \<langle>A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>) \<Longrightarrow> I \<Turnstile> \<langle>A; \<omega>\<rangle>"
  shows "asst_combinable I A"
proof (rule asst_combinable_rule_origin)
  fix a b :: preal
  fix \<omega> :: "'v equi_state"
  assume "a > 0"
     and "b > 0"
     and "\<exists>\<alpha> \<beta> :: 'v equi_state. I \<Turnstile> \<langle>A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>A; \<alpha>\<rangle>" "I \<Turnstile> \<langle>A; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  let ?p = "Rep_preal (a + b)"
  have "?p > 0"
    using \<open>0 < a\<close> \<open>0 < b\<close> less_preal.rep_eq plus_preal.rep_eq zero_preal.rep_eq by auto
  then obtain q where "q * ?p = 1"
    by (metis less_numeral_extra(3) nonzero_eq_divide_eq)
  then have "q \<ge> 0"
    by (metis \<open>0 < ?p\<close> linorder_le_less_linear mult_pos_neg2 not_one_less_zero)
  then obtain inv where "inv = Abs_preal q" "q = Rep_preal inv" using Abs_preal_inverse
    by fastforce
  then have "inv * (a + b) = 1"
    by (metis Rep_preal_inject \<open>q * ?p = 1\<close> one_preal.rep_eq times_preal.rep_eq)
  let ?a = "inv * a"
  let ?b = "inv * b"
  let ?\<omega> = "inv \<odot> \<omega>"
  have "?a + ?b = 1"
    using \<open>inv * (a + b) = 1\<close> pmult_distr by auto
  moreover have "?a > 0"
    by (metis \<open>0 < ?p\<close> \<open>0 < a\<close> \<open>q * ?p = 1\<close> \<open>q = Rep_preal inv\<close> less_preal.rep_eq mult_pos_pos times_preal.rep_eq zero_less_mult_pos2 zero_less_one zero_preal.rep_eq)
  moreover have "?b > 0"
    by (metis \<open>0 < ?p\<close> \<open>0 < b\<close> \<open>q * ?p = 1\<close> \<open>q = Rep_preal inv\<close> less_preal.rep_eq mult_pos_pos times_preal.rep_eq zero_less_mult_pos2 zero_less_one zero_preal.rep_eq)
  moreover have "Some ?\<omega> = (?a \<odot> \<alpha>) \<oplus> (?b \<odot> \<beta>)"
    by (simp add: \<open>Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)\<close> distrib_state_mult mult_mult)
  ultimately have "I \<Turnstile> \<langle>A; ?\<omega>\<rangle>"
    using \<open>I \<Turnstile> \<langle>A; \<alpha>\<rangle>\<close> \<open>I \<Turnstile> \<langle>A; \<beta>\<rangle>\<close> assms by blast
  moreover have "\<omega> = (a + b) \<odot> ?\<omega>"
    by (simp add: \<open>inv * (a + b) = 1\<close> mult.commute mult_mult unit_mult)
  ultimately show "I \<Turnstile>[sem] \<langle>A^(a + b); \<omega>\<rangle>"
    using sat_sem_mult_def by blast
qed

lemma asst_combinable_imp:
  assumes "asst_combinable I A"
      and "a > 0"
      and "b > 0"
      and "I \<Turnstile> \<langle>A; \<alpha>\<rangle>"
      and "I \<Turnstile> \<langle>A; \<beta>\<rangle>"
      and "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
      and "\<omega> = (a + b) \<odot> \<omega>0"
    shows "I \<Turnstile> \<langle>A; \<omega>0\<rangle>"
proof -
  let ?p = "Rep_preal (a + b)"
  have "?p > 0"
    by (metis assms(2) padd_pos pgt.rep_eq preal_pnone_pgt verit_comp_simplify1(1) zero_preal.rep_eq)
  moreover have "a + b = Abs_preal ?p"
    by (simp add: Rep_preal_inverse)
  moreover have "\<exists>\<omega>'. I \<Turnstile> \<langle>A; \<omega>'\<rangle> \<and> \<omega> = (a + b) \<odot> \<omega>'"
    using assms asst_combinable_def sat_sem_mult_def by blast
  ultimately show ?thesis using mult_inv_on_state_implies_uniqueness
    by (metis assms(7))
qed

(*
The reverse direction of combinability holds unconditionally
*)
lemma asst_split:
  assumes "a > 0"
      and "b > 0"
      and "I \<Turnstile>[sem] \<langle>A^(a + b); \<omega>\<rangle>"
    shows "\<exists>\<alpha> \<beta>. I \<Turnstile> \<langle>A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>A; \<beta>\<rangle> \<and> Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
proof -
  obtain \<omega>' where "\<omega> = (a + b) \<odot> \<omega>'" "I \<Turnstile> \<langle>A; \<omega>'\<rangle>"
    using assms(3) sat_sem_mult_def by blast
  moreover have "Some \<omega> = (a \<odot> \<omega>') \<oplus> (b \<odot> \<omega>')"
    by (simp add: calculation(1) distrib_scala_mult)
  ultimately show ?thesis
    by blast
qed

(* Only reduce to same value in success. But reducing to failure in \<omega>0 doesn't imply reducing to failure in \<omega>1 *)
lemma greater_red_pure_same:
  assumes "fun_interp_indep_mask (interp.funs \<Delta>)"
      and "fun_interp_mono (interp.funs \<Delta>)"
      and "\<omega>1 \<succeq> \<omega>0"
  shows "\<Delta> \<turnstile> \<langle>e; \<omega>0\<rangle> [\<Down>] res \<Longrightarrow> res = Val v \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>1\<rangle> [\<Down>] res"
    and "red_pure_exps \<Delta> \<omega>0 exps vals \<Longrightarrow> red_pure_exps \<Delta> \<omega>1 exps vals"
  using assms
proof (induct arbitrary: \<omega>1 v and \<omega>1 rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c \<omega> exps vals)
  then show ?case
    by (smt (verit) list_all2_mono red_pure_red_pure_exps.RedPureExps)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    using red_pure_red_pure_exps.RedLit by blast
next
  case (RedVar \<sigma> n v \<Delta> uv)
  then show ?case sorry
(*
    by (metis get_s.simps greater_cover_store prod.exhaust_sel red_pure_red_pure_exps.RedVar)
*)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    using red_pure_red_pure_exps.RedUnop by blast
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    using red_pure_red_pure_exps.RedBinopLazy by blast
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    using red_pure_red_pure_exps.RedBinop by blast
next
  case (RedOld t l \<phi> \<Delta> e \<sigma> v uw)
(*
  obtain \<sigma>1 t1 uw1 where \<omega>1_decomp: "\<omega>1 = ((\<sigma>1, t1), uw1)"
    using get_pv.cases by blast
  then have "t1 \<succeq> t"
    by (metis (mono_tags, lifting) RedOld.prems(4) get_t.simps greater_def state_add_iff)
  then have "t1 l \<succeq> t l"
    by (simp add: greaterE)
  then obtain \<phi>1 where "t1 l = Some \<phi>1"
    using RedOld.hyps(1) greater_def succ_antisym by fastforce
  then have "\<phi>1 \<succeq> \<phi>"
    by (smt (verit) RedOld.hyps(1) \<open>t1 l \<succeq> t l\<close> core_is_smaller greater_def option.distinct(1) option.sel plus_option.elims)
  moreover have "\<sigma>1 \<succeq> \<sigma>"
    using \<omega>1_decomp RedOld.prems(4) greater_prod_eq by fastforce
  ultimately have "(\<sigma>1, t1, \<phi>1) \<succeq> (\<sigma>, t, \<phi>)"
    by (simp add: \<open>t1 \<succeq> t\<close> greater_comp)
  then have "\<Delta> \<turnstile> \<langle>e; (\<sigma>1, t1, \<phi>1)\<rangle> [\<Down>] Val v"
    using RedOld.hyps(3) RedOld.prems(1) RedOld.prems(2) RedOld.prems(3) by auto
  then show ?case
    by (simp add: RedOld.prems(1) \<omega>1_decomp \<open>t1 l = Some \<phi>1\<close> red_pure_red_pure_exps.RedOld)
*)
  then show ?case sorry
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then have "shift_and_add_equi_state \<omega>1 v1 \<succeq> shift_and_add_equi_state \<omega> v1"
    by (simp add: shift_and_add_equi_state_preserve_greater)
  then have "\<Delta> \<turnstile> \<langle>e2; shift_and_add_equi_state \<omega>1 v1\<rangle> [\<Down>] r"
    using RedLet.hyps(4) RedLet.prems(1) RedLet.prems(2) RedLet.prems(3) by auto
  moreover have "\<Delta> \<turnstile> \<langle>e1; \<omega>1\<rangle> [\<Down>] Val v1"
    by (simp add: RedLet.hyps(2) RedLet.prems(2) RedLet.prems(3) RedLet.prems(4))
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedLet)
next
  case (RedExistsTrue va \<Delta> ty e \<omega>)
  moreover have "shift_and_add_equi_state \<omega>1 va \<succeq> shift_and_add_equi_state \<omega> va"
    by (simp add: calculation(8) shift_and_add_equi_state_preserve_greater)
  ultimately have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 va\<rangle> [\<Down>] Val (VBool True)"
    by presburger
<<<<<<< HEAD
  moreover have "\<And>v'. v' \<in> set_from_type (interp.domains \<Delta>) ty \<Longrightarrow> \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool b)"
  proof -
    fix v' assume "v' \<in> set_from_type (interp.domains \<Delta>) ty"
    then obtain b where
=======
  moreover have "\<And>v'. \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool b)"
  proof -
    fix v'
    obtain b where
>>>>>>> abssem_proof
          "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v'\<rangle> [\<Down>] Val (VBool b)"
      and "\<forall>x xa.
            Val (VBool b) = Val xa \<longrightarrow>
            fun_interp_indep_mask (interp.funs \<Delta>) \<longrightarrow>
            fun_interp_mono (interp.funs \<Delta>) \<longrightarrow>
            x \<succeq> shift_and_add_equi_state \<omega> v' \<longrightarrow> \<Delta> \<turnstile> \<langle>e; x\<rangle> [\<Down>] Val (VBool b)"
      using RedExistsTrue.hyps(4) by fastforce
    moreover have "shift_and_add_equi_state \<omega>1 v' \<succeq> shift_and_add_equi_state \<omega> v'"
      by (simp add: RedExistsTrue.prems(4) shift_and_add_equi_state_preserve_greater)
    ultimately have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool b)"
      using RedExistsTrue.prems(2) RedExistsTrue.prems(3) by blast
    then show "\<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool b)"
      by auto
  qed
  ultimately show ?case
    using RedExistsTrue.hyps(1) red_pure_red_pure_exps.RedExistsTrue by blast
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then have "\<And>v'. v' \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool False)"
  proof -
    fix v'
    assume "v' \<in> set_from_type (domains \<Delta>) ty"
    moreover have "shift_and_add_equi_state \<omega>1 v' \<succeq> shift_and_add_equi_state \<omega> v'"
      by (simp add: RedExistsFalse.prems(4) shift_and_add_equi_state_preserve_greater)
    ultimately show "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool False)"
      by (simp add: RedExistsFalse.hyps RedExistsFalse.prems(2) RedExistsFalse.prems(3))
  qed
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedExistsFalse)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then have "\<And>v'. v' \<in> set_from_type (interp.domains \<Delta>) ty \<Longrightarrow> \<Delta> \<turnstile> \<langle>e;shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool True)"
  proof -
    fix v'
    assume "v' \<in> set_from_type (interp.domains \<Delta>) ty"
    moreover have "shift_and_add_equi_state \<omega>1 v' \<succeq> shift_and_add_equi_state \<omega> v'"
      by (simp add: RedForallTrue.prems(4) shift_and_add_equi_state_preserve_greater)
    ultimately show "\<Delta> \<turnstile> \<langle>e;shift_and_add_equi_state \<omega>1 v'\<rangle> [\<Down>] Val (VBool True)"
      by (simp add: RedForallTrue.hyps RedForallTrue.prems(2) RedForallTrue.prems(3))
  qed
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedForallTrue)
next
  case (RedForallFalse va \<Delta> ty e \<omega>)
  moreover have "shift_and_add_equi_state \<omega>1 va \<succeq> shift_and_add_equi_state \<omega> va"
<<<<<<< HEAD
    by (simp add: calculation(8) shift_and_add_equi_state_preserve_greater)
  ultimately have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 va\<rangle> [\<Down>] Val (VBool False)"
    by presburger
  then show ?case
    using RedForallFalse.hyps(1) red_pure_red_pure_exps.RedForallFalse
    by (metis RedForallFalse.hyps(4) RedForallFalse.prems(2) RedForallFalse.prems(3) RedForallFalse.prems(4) shift_and_add_equi_state_preserve_greater)
=======
    by (simp add: calculation(7) shift_and_add_equi_state_preserve_greater)
  ultimately have "\<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega>1 va\<rangle> [\<Down>] Val (VBool False)"
    by presburger
  then show ?case
    using RedForallFalse.hyps(1) red_pure_red_pure_exps.RedForallFalse by blast
>>>>>>> abssem_proof
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then have "\<Delta> \<turnstile> \<langle>e1; \<omega>1\<rangle> [\<Down>] Val (VBool True)"
    by simp
  moreover have "\<Delta> \<turnstile> \<langle>e2; \<omega>1\<rangle> [\<Down>] r"
    using RedCondExpTrue.hyps(4) RedCondExpTrue.prems by auto
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then have "\<Delta> \<turnstile> \<langle>e1; \<omega>1\<rangle> [\<Down>] Val (VBool False)"
    by simp
  moreover have "\<Delta> \<turnstile> \<langle>e3; \<omega>1\<rangle> [\<Down>] r"
    using RedCondExpFalse.hyps(4) RedCondExpFalse.prems by auto
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then have "\<Delta> \<turnstile> \<langle>e; \<omega>1\<rangle> [\<Down>] Val (VRef Null)"
    by simp
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPermNull)
next
  case (RedResult \<sigma> v \<Delta> ux uy)
  then show ?case sorry
(*
    by (metis get_s.elims greater_cover_store prod.inject red_pure_red_pure_exps.RedResult)
*)
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    by simp
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by simp
next
  case (RedOldFailure t l \<Delta> e uz va)
  then show ?case
    by simp
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case
    by simp
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case
    by simp
next
  case (RedPropagateFailure e e' \<Delta> \<omega>)
  then show ?case
    by simp
next
  case (RedField \<Delta> e \<omega> a f va)
  then have "\<Delta> \<turnstile> \<langle>e; \<omega>1\<rangle> [\<Down>] Val (VRef (Address a))"
    by simp
  moreover have "read_field (get_state \<omega>1) (a, f) = Some va"
    using RedField.hyps(3) RedField.prems(4) greater_state_has_greater_parts(3) read_field_mono by blast
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedField)
next
  case (RedFunApp \<Delta> \<omega> exps vals f va)
  then have "red_pure_exps \<Delta> \<omega>1 exps vals"
    by simp
  moreover have "interp.funs \<Delta> f vals (get_state \<omega>1) = Some va"
    using RedFunApp.hyps(3) RedFunApp.prems(3) RedFunApp.prems(4) fun_interp_mono_def greater_state_has_greater_parts(3) by blast
  ultimately show ?case
    by (simp add: red_pure_red_pure_exps.RedFunApp)
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case
    by simp
qed

lemma red2val_same_for_convex_combination:
  assumes "fun_interp_indep_mask (interp.funs \<Delta>)"
      and "fun_interp_mono (interp.funs \<Delta>)"
      and "a > 0"
      and "b > 0"
      and "Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
      and "\<Delta> \<turnstile> \<langle>e; \<alpha>\<rangle> [\<Down>] Val va"
      and "\<Delta> \<turnstile> \<langle>e; \<beta>\<rangle> [\<Down>] Val vb"
    shows "va = vb"
      and "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val va"
proof -
  have "\<Delta> \<turnstile> \<langle>e; a \<odot> \<alpha>\<rangle> [\<Down>] Val va"
    by (simp add: assms(1) assms(6) red_pure_equiv(1))
  moreover have "\<omega> \<succeq> a \<odot> \<alpha>"
    using assms(5) greater_def by auto
  ultimately show "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val va"
    by (simp add: assms(1) assms(2) greater_red_pure_same(1))
  moreover have "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val vb"
  proof -
    have "\<Delta> \<turnstile> \<langle>e; b \<odot> \<beta>\<rangle> [\<Down>] Val vb"
      by (simp add: assms(1) assms(7) red_pure_equiv(1))
    moreover have "\<omega> \<succeq> b \<odot> \<beta>"
      using assms(5) greater_equiv by auto
    ultimately show ?thesis
      by (simp add: assms(1) assms(2) greater_red_pure_same(1))
  qed
  ultimately show "va = vb"
    by (simp add: red_pure_val_unique(1))
qed

lemma red_exps_same_for_convex_combination:
  assumes "fun_interp_indep_mask (interp.funs \<Delta>)"
      and "fun_interp_mono (interp.funs \<Delta>)"
      and "a > 0"
      and "b > 0"
      and "Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
      and "red_pure_exps \<Delta> \<alpha> exps vas"
      and "red_pure_exps \<Delta> \<beta> exps vbs"
    shows "vas = vbs"
      and "red_pure_exps \<Delta> \<omega> exps vas"
proof -
  have "list_all2 (\<lambda>e v. \<Delta> \<turnstile> \<langle>e; \<alpha>\<rangle> [\<Down>] Val v) exps vas"
    using assms(6) red_pure_exps.simps by blast
  moreover have "\<And>e v. \<Delta> \<turnstile> \<langle>e; \<alpha>\<rangle> [\<Down>] Val v \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v"
    using assms(1) assms(2) assms(5) greater_def greater_red_pure_same(1) red_pure_equiv(1) by blast
  ultimately have *: "list_all2 (\<lambda>e v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vas"
    by (simp add: list_all2_mono)
  then show "red_pure_exps \<Delta> \<omega> exps vas"
    by (simp add: RedPureExps)
  have "list_all2 (\<lambda>e v. \<Delta> \<turnstile> \<langle>e; \<beta>\<rangle> [\<Down>] Val v) exps vbs"
    using assms(7) red_pure_exps.simps by blast
  moreover have "\<And>e v. \<Delta> \<turnstile> \<langle>e; \<beta>\<rangle> [\<Down>] Val v \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v"
    using assms(1) assms(2) assms(5) greater_equiv greater_red_pure_same(1) red_pure_equiv(1) by blast
  ultimately have "list_all2 (\<lambda>e v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vbs"
    by (simp add: list_all2_mono)
  moreover from * have "list_all2 (\<lambda>e v. \<forall>v'. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v') \<longrightarrow> v' = v) exps vas"
    by (simp add: list_all2_mono red_pure_val_unique(1))
  ultimately show "vas = vbs" using list_all2_unique
    by fastforce
qed

lemma red_accfield_combinable:
  shows "red_atomic_assert \<Delta> (Acc x f e) \<alpha> res \<Longrightarrow> fun_interp_indep_mask (interp.funs \<Delta>) \<Longrightarrow> fun_interp_mono (interp.funs \<Delta>) \<Longrightarrow> a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a + b = 1 \<Longrightarrow> Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta> \<Longrightarrow> red_atomic_assert \<Delta> (Acc x f e) \<beta> res \<Longrightarrow> red_atomic_assert \<Delta> (Acc x f e) \<omega> res"
proof (induction _ "Acc x f e" _ res rule: red_atomic_assert.induct)
  case (RedAtomicAcc \<Delta> \<alpha> r p v)
  moreover obtain r' where "\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef r')" using RedAtomicAcc.hyps(4) RedAtomicAcc.prems(7)
    by (metis RedAccFieldPerm_case calculation(11) option.distinct(1))
  ultimately have "\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)"
    using red2val_same_for_convex_combination(2) by blast
  obtain v' where "\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val (VPerm v')"
    using RedAtomicAcc.hyps(4) RedAccFieldPerm_case RedAtomicAcc.prems(7) by blast
  then have "\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm v)" using RedAtomicAcc.hyps RedAtomicAcc.prems red2val_same_for_convex_combination(2)
    by blast
  moreover have "(is_address r \<and> Abs_preal v \<le> get_m \<omega> (the_address r, f)) = (is_address r \<and> Abs_preal v \<le> get_m \<alpha> (the_address r, f))"
  proof (cases "is_address r")
    case True
    have "(Abs_preal v \<le> get_m \<alpha> (the_address r, f)) = (Abs_preal v \<le> get_m \<beta> (the_address r, f))"
    proof -
      have "red_atomic_assert \<Delta> (Acc x f e) \<beta> (Some (is_address r' \<and> Abs_preal v' \<le> get_m \<beta> (the_address r', f)))"
        using RedAtomicAcc.hyps(2) RedAtomicAcc.hyps(3) RedAtomicAcc.hyps(4) RedAtomicAcc.prems(1) RedAtomicAcc.prems(2) RedAtomicAcc.prems(3) RedAtomicAcc.prems(4) RedAtomicAcc.prems(6) \<open>\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val (VPerm v')\<close> \<open>\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef r')\<close> red2val_same_for_convex_combination(1) red_atomic_assert.RedAtomicAcc by blast
      then have "(is_address r \<and> Abs_preal v \<le> get_m \<alpha> (the_address r, f)) = (is_address r' \<and> Abs_preal v' \<le> get_m \<beta> (the_address r', f))"
        by (metis RedAtomicAcc.prems(7) option.inject red_accfield_unique)
      moreover have "r = r'" using red2val_same_for_convex_combination(1) \<open>\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef r')\<close> RedAtomicAcc.hyps(1) RedAtomicAcc.prems
        by blast
      moreover have "v = v'" using red2val_same_for_convex_combination(1) \<open>\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val (VPerm v')\<close> RedAtomicAcc.hyps(2) RedAtomicAcc.prems
        by blast
      ultimately show ?thesis
        using True by auto
    qed
    then have "(Abs_preal v \<le> get_m \<omega> (the_address r, f)) = (Abs_preal v \<le> get_m \<alpha> (the_address r, f))"
      using RedAtomicAcc.prems(5) RedAtomicAcc.prems(6) get_m_combine by blast
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
  ultimately show ?case
    by (smt (verit) RedAtomicAcc.hyps(3) RedAtomicAcc.hyps(4) \<open>\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef r)\<close> red_atomic_assert.RedAtomicAcc)
next
  case (RedAtomicAccZero \<Delta> \<alpha> uu p)
  moreover obtain uu' where "\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef uu')"
    by (metis RedAccFieldPerm_case calculation(10) calculation(3) option.distinct(1))
  ultimately have "\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)"
    using red2val_same_for_convex_combination(2) by blast
  obtain v' where "\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val (VPerm v')"
    using RedAccFieldPerm_case RedAtomicAccZero.hyps(3) RedAtomicAccZero.prems(7) by blast
  then have "\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm 0)" using RedAtomicAccZero.hyps RedAtomicAccZero.prems red2val_same_for_convex_combination(2)
    by blast
  then show ?case
    using RedAtomicAccZero.hyps(3) \<open>\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef uu)\<close> red_atomic_assert.RedAtomicAccZero by blast
next
  case (RedAtomicAccWildcard \<Delta> \<alpha> aa)
  moreover obtain aa' where "\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef aa')"
    by (metis RedAccFieldWild_case calculation(9) calculation(2))
  ultimately have "\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef (Address aa))"
    using red2val_same_for_convex_combination(2) by blast
  moreover have "(0 < get_m \<omega> (aa, f)) = (0 < get_m \<alpha> (aa, f))"
  proof -
    have "Address aa = aa'" using \<open>\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef aa')\<close> RedAtomicAccWildcard red2val_same_for_convex_combination(1)
      by blast
    then have "(0 < get_m \<alpha> (aa, f)) = (0 < get_m \<beta> (aa, f))"
      by (metis RedAtomicAccWildcard.hyps(2) RedAtomicAccWildcard.prems(7) \<open>\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef aa')\<close> option.inject red_accfield_unique red_atomic_assert.RedAtomicAccWildcard)
    then show ?thesis
      by (smt (verit) RedAtomicAccWildcard.prems(5) RedAtomicAccWildcard.prems(6) dual_order.strict_trans1 get_m_combine linorder_le_cases)
  qed
  ultimately show ?case
    by (smt (verit, del_insts) RedAtomicAccWildcard.hyps(2) red_atomic_assert.RedAtomicAccWildcard)
next
  case (RedAtomicAccWildcardNull \<Delta> \<alpha>)
  moreover obtain aa' where "\<Delta> \<turnstile> \<langle>x; \<beta>\<rangle> [\<Down>] Val (VRef aa')"
    by (metis RedAccFieldWild_case calculation(9) calculation(2))
  ultimately have "\<Delta> \<turnstile> \<langle>x; \<omega>\<rangle> [\<Down>] Val (VRef Null)"
    using red2val_same_for_convex_combination(2) by blast
  then show ?case
    using RedAtomicAccWildcardNull.hyps(2) red_atomic_assert.RedAtomicAccWildcardNull by blast
next
  case (RedAtomicAccNeg \<Delta> p \<alpha> v)
  moreover obtain v' where "\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val v'"
    using RedAccFieldPerm_case calculation(10) calculation(3) by blast
  ultimately have "\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm v)"
    using red2val_same_for_convex_combination(2) by blast
  then show ?case
    using RedAtomicAccNeg.hyps(2) RedAtomicAccNeg.hyps(3) red_atomic_assert.RedAtomicAccNeg by blast
qed

lemma red_accpred_combinable:
    shows "red_atomic_assert \<Delta> (AccPredicate P exps pm) \<alpha> (Some True) \<Longrightarrow> interp_combinable (predicates \<Delta>) \<Longrightarrow> fun_interp_indep_mask (interp.funs \<Delta>) \<Longrightarrow> fun_interp_mono (interp.funs \<Delta>) \<Longrightarrow> a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a + b = 1 \<Longrightarrow> Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta> \<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps pm) \<beta> (Some True) \<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps pm) \<omega> (Some True)"
proof (induction _ "AccPredicate P exps pm" _ "Some True" rule: red_atomic_assert.induct)
  case (RedAtomicPred \<Delta> \<alpha> vals p v A)
  then obtain v' where "\<Delta> \<turnstile> \<langle>p; \<beta>\<rangle> [\<Down>] Val v'"
    by (meson RedAccPredPerm_case)
  then have "\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm v)" using RedAtomicPred red2val_same_for_convex_combination(2)
    by blast
  moreover have "red_pure_exps \<Delta> \<omega> exps vals"
    using RedAtomicPred.hyps(1) RedAtomicPred.prems(2) RedAtomicPred.prems(3) RedAtomicPred.prems(7) greater_def greater_red_pure_same(2) red_pure_equiv(2) by blast
  ultimately show ?case
  proof (cases "v = 0")
    case True
    then have "0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<alpha> = Abs_preal v \<odot> a)"
      by simp
    moreover have "0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)"
      by (simp add: True)
    moreover have "red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega>
     (Some (0 < v \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = Abs_preal v \<odot> a)))"
      using RedAtomicPred.hyps(3) RedAtomicPred.hyps(4) \<open>\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> \<open>red_pure_exps \<Delta> \<omega> exps vals\<close> red_atomic_assert.RedAtomicPred by blast
    ultimately show ?thesis
      by (simp add: RedAtomicPred.hyps(5))
  next
    case False
    then have "v > 0"
      using RedAtomicPred.hyps(3) by auto
    then obtain v\<alpha>v where "v\<alpha>v \<in> A" "get_state \<alpha> = Abs_preal v \<odot> v\<alpha>v"
      using RedAtomicPred.hyps(6) by auto
    moreover obtain v\<beta>v where "v\<beta>v \<in> A" "get_state \<beta> = Abs_preal v \<odot> v\<beta>v"
      by (smt (verit) RedAccPred_case RedAtomicPred.hyps RedAtomicPred.prems \<open>0 < v\<close> exp_or_wildcard.distinct(1) exp_or_wildcard.inject option.discI option.inject red2val_same_for_convex_combination(1) red_exps_same_for_convex_combination(1) val.inject(3))
    moreover have "Some (get_state \<omega>) = a \<odot> (get_state \<alpha>) \<oplus> b \<odot> (get_state \<beta>)"
      by (metis RedAtomicPred.prems(7) mult_get_v_interchange state_add_iff)
    ultimately have "Some (get_state \<omega>) = Abs_preal v \<odot> (a \<odot> v\<alpha>v) \<oplus> Abs_preal v \<odot> (b \<odot> v\<beta>v)"
      by (simp add: mult_mult mult.commute)
    moreover have "Abs_preal v > 0"
    proof -
      have "Rep_preal (Abs_preal v) = v" using Abs_preal_inverse
        by (simp add: RedAtomicPred.hyps(3))
      then have "Rep_preal (Abs_preal v) > 0"
        by (simp add: \<open>0 < v\<close>)
      then show ?thesis
        by (simp add: less_preal.rep_eq zero_preal.rep_eq)
    qed
    ultimately have "a \<odot> v\<alpha>v ## b \<odot> v\<beta>v" using compatible_mult_mult defined_def
      by (metis option.distinct(1))
    then obtain v\<omega>v where "Some v\<omega>v = a \<odot> v\<alpha>v \<oplus> b \<odot> v\<beta>v" using defined_def
      by (metis not_Some_eq)
    then have "v\<omega>v \<in> A" using \<open>v\<alpha>v \<in> A\<close> \<open>v\<beta>v \<in> A\<close> \<open>interp.predicates \<Delta> (P, vals) = Some A\<close> \<open>interp_combinable (interp.predicates \<Delta>)\<close> interp_combinable_imp \<open>a + b = 1\<close> \<open>a > 0\<close> \<open>b > 0\<close>
      by metis
    moreover have "get_state \<omega> = Abs_preal v \<odot> v\<omega>v" using \<open>Some (get_state \<omega>) = Abs_preal v \<odot> (a \<odot> v\<alpha>v) \<oplus> Abs_preal v \<odot> (b \<odot> v\<beta>v)\<close> \<open>Some v\<omega>v = a \<odot> v\<alpha>v \<oplus> b \<odot> v\<beta>v\<close>
      by (metis distrib_state_mult option.inject)
    ultimately have "v > 0 \<longrightarrow> (\<exists>v\<omega>v \<in> A. get_state \<omega> = Abs_preal v \<odot> v\<omega>v)"
      by auto
    then show ?thesis using \<open>red_pure_exps \<Delta> \<omega> exps vals\<close> \<open>\<Delta> \<turnstile> \<langle>p; \<omega>\<rangle> [\<Down>] Val (VPerm v)\<close> RedAtomicPred.hyps red_atomic_assert.RedAtomicPred[of \<Delta> \<omega> exps vals p v P A]
      by simp
  qed
next
  case (RedAtomicPredWildcard \<Delta> \<alpha> vals A)
  then obtain vals' A' v\<beta>v v' where
        "red_pure_exps \<Delta> \<beta> exps vals'"
    and "interp.predicates \<Delta> (P, vals') = Some A'"
    and "v\<beta>v \<in> A'"
    and "v' > 0"
    and "get_state \<beta> = v' \<odot> v\<beta>v"
    by (smt (verit) RedAccPredWild_case option.inject)
  then have "vals' = vals"
    using RedAtomicPredWildcard.hyps(1) RedAtomicPredWildcard.prems red_exps_same_for_convex_combination(1) by blast
  then have "A' = A"
    using RedAtomicPredWildcard.hyps(2) \<open>interp.predicates \<Delta> (P, vals') = Some A'\<close> by auto
  obtain v\<alpha>v v where "v\<alpha>v \<in> A" "v > 0" "get_state \<alpha> = v \<odot> v\<alpha>v"
    using RedAtomicPredWildcard.hyps(4) by auto
  moreover have "Some (get_state \<omega>) = a \<odot> (get_state \<alpha>) \<oplus> b \<odot> (get_state \<beta>)"
    by (metis RedAtomicPredWildcard.prems(7) mult_get_v_interchange state_add_iff)
  ultimately have "Some (get_state \<omega>) = (a * v) \<odot> v\<alpha>v \<oplus> (b * v') \<odot> v\<beta>v"
    by (simp add: \<open>get_state \<beta> = v' \<odot> v\<beta>v\<close> mult_mult)
  let ?norm = "v * a + v' * b"
  have "?norm > 0" using \<open>v > 0\<close>
    by (metis RedAtomicPredWildcard.prems(6) \<open>pnone < v'\<close> dual_order.strict_trans1 linorder_not_less order_less_imp_le pmult_comm preal_greater_convex)
  then obtain inv where "inv * ?norm = 1" "inv > 0"
    using positive_have_inv by auto
  then have "Some (get_state \<omega>) = ?norm \<odot> ((a * v * inv) \<odot> v\<alpha>v) \<oplus> ?norm \<odot> ((b * v' * inv) \<odot> v\<beta>v)"
    by (metis (no_types, opaque_lifting) \<open>Some (get_state \<omega>) = (a * v) \<odot> v\<alpha>v \<oplus> (b * v') \<odot> v\<beta>v\<close> mult.commute mult.right_neutral mult_mult)
  then have "(a * v * inv) \<odot> v\<alpha>v ## (b * v' * inv) \<odot> v\<beta>v" using \<open>?norm > 0\<close> compatible_mult_mult defined_def
    by (metis option.distinct(1))
  then obtain v\<omega>v where "Some v\<omega>v = (a * v * inv) \<odot> v\<alpha>v \<oplus> (b * v' * inv) \<odot> v\<beta>v" using defined_def
    by (metis not_Some_eq)
  moreover have "a * v * inv + b * v' * inv = 1"
    by (metis \<open>inv * ?norm = 1\<close> mult.commute pmult_distr)
  moreover have "a * v * inv > 0" using mult_positive_preal_positive
    by (simp add: RedAtomicPredWildcard.prems(4) \<open>0 < inv\<close> \<open>0 < v\<close>)
  moreover have "b * v' * inv > 0" using mult_positive_preal_positive
    by (simp add: RedAtomicPredWildcard.prems(5) \<open>0 < inv\<close> \<open>0 < v'\<close>)
  ultimately have "v\<omega>v \<in> A" using \<open>v\<alpha>v \<in> A\<close> \<open>v\<beta>v \<in> A'\<close> \<open>A' = A\<close> \<open>interp.predicates \<Delta> (P, vals) = Some A\<close> \<open>interp_combinable (interp.predicates \<Delta>)\<close> interp_combinable_imp
    by metis
  moreover have "get_state \<omega> = ?norm \<odot> v\<omega>v"
    by (metis \<open>Some (get_state \<omega>) = ?norm \<odot> ((a * v * inv) \<odot> v\<alpha>v) \<oplus> ?norm \<odot> ((b * v' * inv) \<odot> v\<beta>v)\<close> \<open>Some v\<omega>v = (a * v * inv) \<odot> v\<alpha>v \<oplus> (b * v' * inv) \<odot> v\<beta>v\<close> distrib_state_mult option.inject)
  ultimately have "\<exists>v\<omega>v \<in> A. \<exists>v'. v' > 0 \<and> get_state \<omega> = v' \<odot> v\<omega>v"
    using \<open>?norm > 0\<close> by auto
  moreover have "red_pure_exps \<Delta> \<omega> exps vals"
    using RedAtomicPredWildcard.hyps(1) RedAtomicPredWildcard.prems \<open>red_pure_exps \<Delta> \<beta> exps vals'\<close> red_exps_same_for_convex_combination(2) by blast
  ultimately show ?case using \<open>interp.predicates \<Delta> (P, vals) = Some A\<close> red_atomic_assert.RedAtomicPredWildcard[of \<Delta> \<omega> exps vals P A] \<open>Wildcard = pm\<close>
    by simp
qed

lemma atomic_combinable:
  assumes "interp_combinable (predicates I)"
      and "fun_interp_indep_mask (interp.funs I)"
      and "fun_interp_mono (interp.funs I)"
  shows "asst_combinable I (Atomic A)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>Atomic A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>Atomic A; \<beta>\<rangle> \<and> Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
  then obtain \<alpha> \<beta> where "red_atomic_assert I A \<alpha> (Some True)" "red_atomic_assert I A \<beta> (Some True)" "Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>"
    using sat.simps(1) by blast
  then have "red_atomic_assert I A \<omega> (Some True)"
  proof (cases A)
    case (Pure x1)
    then show ?thesis
      by (metis RedAtomicPure RedPure2True_case \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>0 < a\<close> \<open>0 < b\<close> \<open>red_atomic_assert I A \<alpha> (Some True)\<close> \<open>red_atomic_assert I A \<beta> (Some True)\<close> assms(2) assms(3) red2val_same_for_convex_combination(2))
  next
    case (Acc x21 x22 x23)
    then show ?thesis
      using \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> \<open>red_atomic_assert I A \<alpha> (Some True)\<close> \<open>red_atomic_assert I A \<beta> (Some True)\<close> assms(2) assms(3) red_accfield_combinable by blast
  next
    case (AccPredicate x31 x32 x33)
    then show ?thesis
      using \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> \<open>red_atomic_assert I A \<alpha> (Some True)\<close> \<open>red_atomic_assert I A \<beta> (Some True)\<close> assms(1) assms(2) assms(3) red_accpred_combinable by blast
  qed
  then show "I \<Turnstile> \<langle>Atomic A; \<omega>\<rangle>"
    by simp
qed

lemma imp_combinable:
  assumes "asst_combinable I A"
      and "interp_combinable (predicates I)"
      and "fun_interp_indep_mask (interp.funs I)"
      and "fun_interp_mono (interp.funs I)"
  shows "asst_combinable I (Imp e A)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>Imp e A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>Imp e A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>Imp e A; \<alpha>\<rangle>" "I \<Turnstile> \<langle>Imp e A; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  then obtain va where "I \<turnstile> \<langle>e; \<alpha>\<rangle> [\<Down>] Val va" "va = VBool True \<Longrightarrow> I \<Turnstile> \<langle>A; \<alpha>\<rangle>"
    using sat.simps(2) by blast
  moreover obtain vb where "I \<turnstile> \<langle>e; \<beta>\<rangle> [\<Down>] Val vb" "vb = VBool True \<Longrightarrow> I \<Turnstile> \<langle>A; \<beta>\<rangle>"
    using \<open>I \<Turnstile> \<langle>Imp e A; \<beta>\<rangle>\<close> sat.simps(2) by blast
  ultimately have "I \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val va"
    using \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(3) assms(4) red2val_same_for_convex_combination(2) by blast
  moreover have "va = VBool True \<Longrightarrow> I \<Turnstile> \<langle>A; \<omega>\<rangle>"
  proof -
    assume "va = VBool True"
    moreover have "vb = va"
      using \<open>I \<turnstile> \<langle>e; \<alpha>\<rangle> [\<Down>] Val va\<close> \<open>I \<turnstile> \<langle>e; \<beta>\<rangle> [\<Down>] Val vb\<close> \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(3) assms(4) red2val_same_for_convex_combination(1) by blast
    ultimately have "I \<Turnstile> \<langle>A; \<beta>\<rangle>"
      by (simp add: \<open>vb = VBool True \<Longrightarrow> I \<Turnstile> \<langle>A; \<beta>\<rangle>\<close>)
    moreover have "I \<Turnstile> \<langle>A; \<alpha>\<rangle>"
      by (simp add: \<open>va = VBool True\<close> \<open>va = VBool True \<Longrightarrow> I \<Turnstile> \<langle>A; \<alpha>\<rangle>\<close>)
    ultimately show "I \<Turnstile> \<langle>A; \<omega>\<rangle>"
      by (metis \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(1) asst_combinable_imp unit_mult)
  qed
  ultimately show "I \<Turnstile> \<langle>Imp e A; \<omega>\<rangle>"
    by auto
qed

lemma star_combinable:
  assumes "asst_combinable I A"
      and "asst_combinable I B"
    shows "asst_combinable I (Star A B)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>Star A B; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>Star A B; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>Star A B; \<alpha>\<rangle>" "I \<Turnstile> \<langle>Star A B; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  then show "I \<Turnstile> \<langle>Star A B; \<omega>\<rangle>"
  proof -
    obtain \<alpha>1 \<alpha>2 where "I \<Turnstile> \<langle>A; \<alpha>1\<rangle>" "I \<Turnstile> \<langle>B; \<alpha>2\<rangle>" "Some \<alpha> = \<alpha>1 \<oplus> \<alpha>2"
      using \<open>I \<Turnstile> \<langle>Star A B; \<alpha>\<rangle>\<close> by auto
    obtain \<beta>1 \<beta>2 where "I \<Turnstile> \<langle>A; \<beta>1\<rangle>" "I \<Turnstile> \<langle>B; \<beta>2\<rangle>" "Some \<beta> = \<beta>1 \<oplus> \<beta>2"
      using \<open>I \<Turnstile> \<langle>Star A B; \<beta>\<rangle>\<close> by auto
    (* Following is probably easier to prove using splus *)
    have "\<alpha> ## \<beta>"
      by (metis \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>0 < a\<close> \<open>0 < b\<close> compatible_mult_mult defined_def option.discI)
    then have "\<alpha>1 ## \<beta>1"
      using \<open>Some \<alpha> = \<alpha>1 \<oplus> \<alpha>2\<close> \<open>Some \<beta> = \<beta>1 \<oplus> \<beta>2\<close> defined_comm greater_def smaller_compatible by blast
    then have "a \<odot> \<alpha>1 ## b \<odot> \<beta>1"
      by (simp add: \<open>0 < a\<close> \<open>0 < b\<close> compatible_mult_mult)
    then obtain \<omega>1 where "Some \<omega>1 = a \<odot> \<alpha>1 \<oplus> b \<odot> \<beta>1"
      by (metis defined_def not_Some_eq)
    have "\<alpha>2 ## \<beta>2"
      by (metis (no_types, lifting) \<open>Some \<alpha> = \<alpha>1 \<oplus> \<alpha>2\<close> \<open>Some \<beta> = \<beta>1 \<oplus> \<beta>2\<close> \<open>\<alpha> ## \<beta>\<close> asso3 commutative defined_def)
    then have "a \<odot> \<alpha>2 ## b \<odot> \<beta>2"
      by (simp add: \<open>0 < a\<close> \<open>0 < b\<close> compatible_mult_mult)
    then obtain \<omega>2 where "Some \<omega>2 = a \<odot> \<alpha>2 \<oplus> b \<odot> \<beta>2"
      by (metis defined_def not_Some_eq)
    then have "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
    proof -
      have "Some (a \<odot> \<alpha>) = a \<odot> \<alpha>1 \<oplus> a \<odot> \<alpha>2"
        by (simp add: \<open>Some \<alpha> = \<alpha>1 \<oplus> \<alpha>2\<close> distrib_state_mult)
      moreover have "Some (b \<odot> \<beta>) = b \<odot> \<beta>1 \<oplus> b \<odot> \<beta>2"
        by (simp add: \<open>Some \<beta> = \<beta>1 \<oplus> \<beta>2\<close> distrib_state_mult)
      ultimately show ?thesis
        by (metis (no_types, lifting) \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>Some \<omega>1 = a \<odot> \<alpha>1 \<oplus> b \<odot> \<beta>1\<close> \<open>Some \<omega>2 = a \<odot> \<alpha>2 \<oplus> b \<odot> \<beta>2\<close> commutative splus.simps(3) splus_asso)
    qed

    moreover have "I \<Turnstile> \<langle>A; \<omega>1\<rangle>"
      by (metis \<open>I \<Turnstile> \<langle>A; \<alpha>1\<rangle>\<close> \<open>I \<Turnstile> \<langle>A; \<beta>1\<rangle>\<close> \<open>Some \<omega>1 = a \<odot> \<alpha>1 \<oplus> b \<odot> \<beta>1\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(1) asst_combinable_imp unit_mult)
    moreover have "I \<Turnstile> \<langle>B; \<omega>2\<rangle>"
      by (metis \<open>I \<Turnstile> \<langle>B; \<alpha>2\<rangle>\<close> \<open>I \<Turnstile> \<langle>B; \<beta>2\<rangle>\<close> \<open>Some \<omega>2 = a \<odot> \<alpha>2 \<oplus> b \<odot> \<beta>2\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(2) asst_combinable_imp unit_mult)
    ultimately show ?thesis
      using sat.simps(4) by blast
  qed
qed

lemma wand_combinable:
  assumes "asst_combinable I B"
    shows "asst_combinable I (Wand A B)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>Wand A B; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>Wand A B; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>Wand A B; \<alpha>\<rangle>" "I \<Turnstile> \<langle>Wand A B; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  show "I \<Turnstile> \<langle>Wand A B; \<omega>\<rangle>"
  proof (rule sat_wand_rule)
    fix \<omega>1 \<omega>0 :: "'a equi_state"
    assume "Some \<omega>1 = \<omega> \<oplus> \<omega>0"
       and "I \<Turnstile> \<langle>A; \<omega>0\<rangle>"
    (*
    Following paragraph is proving \<omega>1 = a \<odot> (\<alpha> \<oplus> \<omega>0) \<oplus> b \<odot> (\<beta> \<oplus> \<omega>0), where operands around all \<oplus>s are compatible and all \<oplus>s in this equation take out value part of option type
    *)
    (* Probably easier to prove commutivity using splus *)
    have "\<omega>0 = (a + b) \<odot> \<omega>0"
      by (simp add: \<open>a + b = 1\<close> unit_mult)
    then have "Some \<omega>0 = a \<odot> \<omega>0 \<oplus> b \<odot> \<omega>0"
      by (metis distrib_scala_mult)
    have "a \<odot> \<alpha> ## \<omega>0"
      by (metis (no_types, lifting) \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>Some \<omega>1 = \<omega> \<oplus> \<omega>0\<close> asso2 commutative defined_def option.distinct(1))
    then have "\<alpha> ## \<omega>0"
      by (simp add: \<open>0 < a\<close> compatible_mult)
    then obtain \<alpha>1 where "Some \<alpha>1 = \<alpha> \<oplus> \<omega>0"
      by (metis defined_def not_None_eq)
    then have "Some (a \<odot> \<alpha>1) = a \<odot> \<alpha> \<oplus> a \<odot> \<omega>0"
      by (simp add: distrib_state_mult)
    have "b \<odot> \<beta> ## \<omega>0"
      by (metis (no_types, lifting) \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>Some \<omega>1 = \<omega> \<oplus> \<omega>0\<close> asso2 defined_def option.distinct(1))
    then have "\<beta> ## \<omega>0"
      by (simp add: \<open>0 < b\<close> compatible_mult)
    then obtain \<beta>1 where "Some \<beta>1 = \<beta> \<oplus> \<omega>0"
      by (metis defined_def not_None_eq)
    then have "Some (b \<odot> \<beta>1) = b \<odot> \<beta> \<oplus> b \<odot> \<omega>0"
      by (simp add: distrib_state_mult)
    then have "Some \<omega>1 = a \<odot> \<alpha>1 \<oplus> b \<odot> \<beta>1"
      by (smt (verit, ccfv_threshold) \<open>Some (a \<odot> \<alpha>1) = a \<odot> \<alpha> \<oplus> a \<odot> \<omega>0\<close> \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>Some \<omega>0 = a \<odot> \<omega>0 \<oplus> b \<odot> \<omega>0\<close> \<open>Some \<omega>1 = \<omega> \<oplus> \<omega>0\<close> splus.simps(3) splus_asso splus_comm)
    (*
    Finish proving \<omega>1 = a \<odot> (\<alpha> \<oplus> \<omega>0) \<oplus> b \<odot> (\<beta> \<oplus> \<omega>0), and obtain \<alpha>1 = \<alpha> \<oplus> \<omega>0 and \<beta>1 = \<beta> \<oplus> \<omega>0
    *)
    have "I \<Turnstile> \<langle>B; \<alpha>1\<rangle>"
      using \<open>I \<Turnstile> \<langle>Wand A B; \<alpha>\<rangle>\<close> \<open>I \<Turnstile> \<langle>A; \<omega>0\<rangle>\<close> \<open>Some \<alpha>1 = \<alpha> \<oplus> \<omega>0\<close> sat.simps(5) by blast
    moreover have "I \<Turnstile> \<langle>B; \<beta>1\<rangle>"
      using \<open>I \<Turnstile> \<langle>Wand A B; \<beta>\<rangle>\<close> \<open>I \<Turnstile> \<langle>A; \<omega>0\<rangle>\<close> \<open>Some \<beta>1 = \<beta> \<oplus> \<omega>0\<close> sat.simps(5) by blast
    ultimately show "I \<Turnstile> \<langle>B; \<omega>1\<rangle>"
      by (metis \<open>Some \<omega>1 = a \<odot> \<alpha>1 \<oplus> b \<odot> \<beta>1\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms asst_combinable_imp unit_mult)
  qed
qed

lemma forall_combinable:
  assumes "asst_combinable I A"
  shows "asst_combinable I (ForAll ty A)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>ForAll ty A; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>ForAll ty A; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>ForAll ty A; \<alpha>\<rangle>" "I \<Turnstile> \<langle>ForAll ty A; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  show "I \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle>"
  proof (rule sat_forall_rule)
    fix v
    assume v_in_domain: "v \<in> set_from_type (interp.domains I) ty"
    then have "I \<Turnstile> \<langle>A; shift_and_add_equi_state \<alpha> v\<rangle>"
      using \<open>I \<Turnstile> \<langle>ForAll ty A; \<alpha>\<rangle>\<close> by auto
    moreover have "I \<Turnstile> \<langle>A; shift_and_add_equi_state \<beta> v\<rangle>"
      using v_in_domain \<open>I \<Turnstile> \<langle>ForAll ty A; \<beta>\<rangle>\<close> by auto
    moreover have "Some (shift_and_add_equi_state \<omega> v) = a \<odot> (shift_and_add_equi_state \<alpha> v) \<oplus> b \<odot> (shift_and_add_equi_state \<beta> v)"
      by (simp add: \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> add_shift_and_add_equi_state_interchange mult_shift_and_add_equi_state_interchange)
    ultimately show "I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>"
      by (metis \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms asst_combinable_imp unit_mult)
  qed
qed

lemma and_combinable:
  assumes "asst_combinable I A"
      and "asst_combinable I B"
    shows "asst_combinable I (ImpureAnd A B)"
proof (rule asst_combinable_rule)
  fix a b :: preal
  fix \<omega> :: "'a equi_state"
  assume "a > 0"
     and "b > 0"
     and "a + b = 1"
     and "\<exists>\<alpha> \<beta> :: 'a equi_state. I \<Turnstile> \<langle>ImpureAnd A B; \<alpha>\<rangle> \<and> I \<Turnstile> \<langle>ImpureAnd A B; \<beta>\<rangle> \<and> Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
  then obtain \<alpha> \<beta> where "I \<Turnstile> \<langle>ImpureAnd A B; \<alpha>\<rangle>" "I \<Turnstile> \<langle>ImpureAnd A B; \<beta>\<rangle>" "Some \<omega> = (a \<odot> \<alpha>) \<oplus> (b \<odot> \<beta>)"
    by blast
  moreover have "I \<Turnstile> \<langle>A; \<omega>\<rangle>"
  proof -
    have "I \<Turnstile> \<langle>A; \<alpha>\<rangle>"
      using calculation(1) by auto
    moreover have "I \<Turnstile> \<langle>A; \<beta>\<rangle>"
      using \<open>I \<Turnstile> \<langle>ImpureAnd A B; \<beta>\<rangle>\<close> by auto
    ultimately show ?thesis
      by (metis \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(1) asst_combinable_imp unit_mult)
  qed
  moreover have "I \<Turnstile> \<langle>B; \<omega>\<rangle>"
  proof -
    have "I \<Turnstile> \<langle>B; \<alpha>\<rangle>"
      using calculation(1) by auto
    moreover have "I \<Turnstile> \<langle>B; \<beta>\<rangle>"
      using \<open>I \<Turnstile> \<langle>ImpureAnd A B; \<beta>\<rangle>\<close> by auto
    ultimately show ?thesis
      by (metis \<open>Some \<omega> = a \<odot> \<alpha> \<oplus> b \<odot> \<beta>\<close> \<open>a + b = 1\<close> \<open>0 < a\<close> \<open>0 < b\<close> assms(2) asst_combinable_imp unit_mult)
  qed
  ultimately show "I \<Turnstile> \<langle>ImpureAnd A B; \<omega>\<rangle>"
    by simp
qed

lemma wd_asst_combinable:
  assumes "interp_combinable \<Delta>"
      and "fun_interp_indep_mask F"
      and "fun_interp_mono F"
      and "no_exists_or A"
    shows "asst_combinable \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> A"
  using assms
proof (induction A)
  case (Atomic x)
  then show ?case
    by (simp add: atomic_combinable)
next
  case (Imp x1a A)
  then show ?case
    by (simp add: imp_combinable)
next
  case (CondAssert x1a A1 A2)
  then show ?case sorry
next
  case (ImpureAnd A1 A2)
  then show ?case
    by (simp add: and_combinable)
next
  case (ImpureOr A1 A2)
  then show ?case
    by simp
next
  case (Star A1 A2)
  then show ?case
    by (simp add: star_combinable)
next
  case (Wand A1 A2)
  then show ?case
    by (simp add: wand_combinable)
next
  case (ForAll x1a A)
  then show ?case
    by (simp add: forall_combinable)
next
  case (Exists x1a A)
  then show ?case
    by simp
qed


subsection \<open>Relate asst_combinable with interp_combinable\<close>

definition vstate_set_convex :: "'v virtual_state set \<Rightarrow> bool" where
  "vstate_set_convex S \<longleftrightarrow> (\<forall>p q :: preal. \<forall>a b x :: 'v virtual_state. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> a \<in> S \<and> b \<in> S \<and> p \<odot> a \<oplus> q \<odot> b = Some x \<longrightarrow> x \<in> S)"

lemma vstate_set_convex_rule:
  assumes "\<And>p q a b x. p > 0 \<Longrightarrow> q > 0 \<Longrightarrow> p + q = 1 \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> p \<odot> a \<oplus> q \<odot> b = Some x \<Longrightarrow> x \<in> S"
  shows "vstate_set_convex S"
  using assms vstate_set_convex_def by blast

lemma vstate_set_convex_imp:
  assumes "vstate_set_convex S"
      and "p + q = 1"
      and "p > 0"
      and "q > 0"
      and "a \<in> S"
      and "b \<in> S"
      and "p \<odot> a \<oplus> q \<odot> b = Some x"
    shows "x \<in> S"
  using assms vstate_set_convex_def by blast

(* Relation between new definition and interp_combinable *)
lemma interp_combinable_equiv:
  "interp_combinable \<Delta> \<longleftrightarrow> (\<forall>l :: 'v predicate_loc. \<forall>S :: 'v virtual_state set. \<Delta> l = Some S \<longrightarrow> vstate_set_convex S)" (is "?A \<longleftrightarrow> ?B")
  by (blast intro: vstate_set_convex_rule interp_combinable_rule dest: interp_combinable_imp vstate_set_convex_imp)

(* Definition of preserve_set_closure that directly works on combinability *)
definition preserve_combinable :: "('v pred_interp \<Rightarrow> 'v pred_interp) \<Rightarrow> bool" where
  "preserve_combinable f \<longleftrightarrow> (\<forall>\<Delta>. interp_combinable \<Delta> \<longrightarrow> interp_combinable (f \<Delta>))"

lemma preserve_combinable_rule:
  assumes "\<And>\<Delta>. interp_combinable \<Delta> \<Longrightarrow> interp_combinable (f \<Delta>)"
  shows "preserve_combinable f"
  by (simp add: assms preserve_combinable_def)

lemma preserve_combinable_equiv:
  "preserve_combinable = preserve_set_closure (\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b})"
proof (rule ext)
  let ?S_fun = "\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
  fix f :: "'v pred_interp \<Rightarrow> 'v pred_interp"
  show "preserve_combinable f \<longleftrightarrow> preserve_set_closure ?S_fun f" (is "?A \<longleftrightarrow> ?B")
  proof
    assume ?A
    show ?B
    proof (rule preserve_set_closure_rule)
      fix \<Delta> :: "'v pred_interp"
      assume "set_closure ?S_fun \<Delta>"
      then have "interp_combinable \<Delta>"
        by (simp add: interp_combinable_set_closure)
      then have "interp_combinable (f \<Delta>)"
        using \<open>preserve_combinable f\<close> preserve_combinable_def by auto
      then show "set_closure ?S_fun (f \<Delta>)"
        by (simp add: interp_combinable_set_closure)
    qed
  next
    assume ?B
    show ?A
    proof (rule preserve_combinable_rule)
      fix \<Delta> :: "'v pred_interp"
      assume "interp_combinable \<Delta>"
      then have "set_closure ?S_fun \<Delta>"
        by (simp add: interp_combinable_set_closure)
      then have "set_closure ?S_fun (f \<Delta>)" using \<open>?B\<close> preserve_set_closure_imp[of ?S_fun f \<Delta>]
        by auto
      then show "interp_combinable (f \<Delta>)"
        by (simp add: interp_combinable_set_closure)
    qed
  qed
qed

(* Apply asst_combinable result on assertion_upt function *)
lemma asst_combinable_implies_vstate_set_convex:
  "asst_combinable \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> A \<Longrightarrow> vstate_set_convex (assertion_upt D F A v \<Delta>)"
  sorry
(*
proof -
  let ?I = "\<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr>"
  assume "asst_combinable ?I A"
  show "vstate_set_convex (assertion_upt D F A v \<Delta>)"
  proof (rule vstate_set_convex_rule)
    fix p q a b x
    let ?S = "assertion_upt D F A v \<Delta>"
    assume "p + q = 1"
       and "p > 0"
       and "q > 0"
       and "a \<in> ?S"
       and "b \<in> ?S"
       and "p \<odot> a \<oplus> q \<odot> b = Some x"
    let ?\<omega>x = "shift_and_add_list_state (\<lambda>n. None, \<lambda>l. None, x) v"
    let ?\<omega>a = "shift_and_add_list_state (\<lambda>n. None, \<lambda>l. None, a) v"
    let ?\<omega>b = "shift_and_add_list_state (\<lambda>n. None, \<lambda>l. None, b) v"
    have "Some (\<lambda>n. None, \<lambda>l. None, x) = (p \<odot> (\<lambda>n. None, \<lambda>l. None, a)) \<oplus> (q \<odot> (\<lambda>n. None, \<lambda>l. None, b))" using extend_part_relation_to_tuple[of p q x a b "\<lambda>n. None" "\<lambda>l. None"]
      by (simp add: \<open>p + q = 1\<close> \<open>p \<odot> a \<oplus> q \<odot> b = Some x\<close>)
    then have "Some ?\<omega>x = p \<odot> ?\<omega>a \<oplus> q \<odot> ?\<omega>b"
      using shift_and_add_list_state_rel_interchange by blast
    moreover have "?I \<Turnstile> \<langle>A; ?\<omega>a\<rangle>" using \<open>a \<in> ?S\<close>
      by (simp add: assertion_upt_def)
    moreover have "?I \<Turnstile> \<langle>A; ?\<omega>b\<rangle>" using \<open>b \<in> ?S\<close>
      by (simp add: assertion_upt_def)
    moreover have "?\<omega>x = (p + q) \<odot> ?\<omega>x"
      by (simp add: \<open>p + q = 1\<close> unit_mult)
    ultimately have "?I \<Turnstile> \<langle>A; ?\<omega>x\<rangle>" using asst_combinable_imp
      using \<open>asst_combinable ?I A\<close> \<open>0 < p\<close> \<open>0 < q\<close> by blast
    then show "x \<in> ?S"
      by (simp add: assertion_upt_def)
  qed
qed
*)

theorem wd_prog_preserve_combinable:
  assumes "fun_interp_indep_mask F"
      and "fun_interp_mono F"
      and "wd_pred_prog P"
    shows "preserve_combinable (predInterpUpdate P D F)"
proof (rule preserve_combinable_rule)
  fix \<Delta> :: "'a pred_interp"
  assume "interp_combinable \<Delta>"
  have "\<And>l :: 'a predicate_loc. \<And>S :: 'a virtual_state set. predInterpUpdate P D F \<Delta> l = Some S \<Longrightarrow> vstate_set_convex S"
  proof -
    fix l :: "'a predicate_loc"
    fix S :: "'a virtual_state set"
    assume "predInterpUpdate P D F \<Delta> l = Some S"
    then obtain A where "A = predicate_body P (fst l)" "S = assertion_upt D F A (snd l) \<Delta>"
      by (metis option.discI option.inject predInterpUpdate_domain)
    moreover have "asst_combinable \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> A"
    proof -
      obtain pred where "program.predicates P (fst l) = Some pred" "A = the (predicate_decl.body pred)"
        by (smt (verit, del_insts) \<open>predInterpUpdate P D F \<Delta> l = Some S\<close> calculation(1) option.collapse option.discI predInterpUpdate_def predicate_body_def predicate_exists_def)
      then have "wd_pred pred"
        using assms(3) wd_pred_prog_def by auto
      then have "wd_pred_asst A"
        by (simp add: \<open>A = the (predicate_decl.body pred)\<close> wd_pred_def)
      then have "no_exists_or A"
        by (simp add: wd_pred_asst_def)
      then show ?thesis using assms(1) assms(2) \<open>interp_combinable \<Delta>\<close> wd_asst_combinable
        by auto
    qed
    ultimately show "vstate_set_convex S"
      by (simp add: asst_combinable_implies_vstate_set_convex)
  qed
  then show "interp_combinable (predInterpUpdate P D F \<Delta>)"
    by (simp add: interp_combinable_equiv)
qed

theorem wd_prog_lfp_combinable:
  assumes "fun_interp_indep_mask F"
      and "fun_interp_mono F"
      and "wd_pred_prog P"
    shows "interp_combinable (ccpo_class.fixp (predInterpUpdate P D F))"
proof -
  let ?f = "predInterpUpdate P D F"
  let ?S_fun = "\<lambda>a b. {\<sigma> | \<sigma> p q. p > 0 \<and> q > 0 \<and> p + q = 1 \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
  have "mono_inc ?f"
    by (simp add: assms(3) mono_inc_predInterpUpdate)
  moreover have "preserve_set_closure ?S_fun ?f"
    by (metis assms preserve_combinable_equiv wd_prog_preserve_combinable)
  ultimately have "set_closure ?S_fun (ccpo_class.fixp ?f)"
    by (simp add: LFP_set_closure)
  then show ?thesis
    by (simp add: interp_combinable_set_closure)
qed


end