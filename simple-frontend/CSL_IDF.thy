theory CSL_IDF
  imports ParImp ViperCommon.SepAlgebra ViperCommon.SepLogic "../vipersemabstract/Instantiation"
begin

subsection \<open>Safety\<close>

definition binary_mask where
  "binary_mask \<omega> \<longleftrightarrow> (\<forall>l. get_vm \<omega> l = 0 \<or> get_vm \<omega> l = 1)"

lemma binary_maskI:
  assumes "\<And>l. get_vm \<omega> l = 0 \<or> get_vm \<omega> l = 1"
  shows "binary_mask \<omega>"
  using assms binary_mask_def by blast

abbreviation concretize where                                              
  "concretize s \<omega> \<equiv> (s, get_vh \<omega>)"

definition read_dom where 
  "read_dom \<omega> = { l. get_vm \<omega> (l, field_val) > 0 }"

definition write_dom where 
  "write_dom \<omega> = { l. get_vm \<omega> (l, field_val) = 1 }"

definition no_aborts where
  "no_aborts C s0 \<omega>0 \<longleftrightarrow> (\<forall>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>0' \<and> sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<longrightarrow> \<not> aborts C (s0, get_vh \<omega>0'))"

lemma no_abortsI[intro]:
  assumes "\<And>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>0' \<Longrightarrow> sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<Longrightarrow> \<not> aborts C (s0, get_vh \<omega>0')"
  shows "no_aborts C s0 \<omega>0"
  using assms no_aborts_def by blast

lemma no_abortsE:
  assumes "no_aborts C s0 \<omega>0"
      and "sep_algebra_class.stable \<omega>0'"
      and "sep_algebra_class.stable \<omega>f"
      and "Some \<omega>0' = \<omega>0 \<oplus> \<omega>f"
      and "binary_mask \<omega>0'"
    shows "\<not> aborts C (s0, get_vh \<omega>0')"
  using assms(1) assms(2) assms(3) assms(4) assms(5) no_aborts_def by blast



(*
type_synonym 'v ag_store = "(var \<rightharpoonup> 'v) agreement"
type_synonym ('v, 'a) abs_state = "'v ag_store \<times> 'a"
('a val, ('a ag_trace \<times> 'a virtual_state)) abs_state"
*)

 primrec
  safe :: "nat \<Rightarrow> cmd \<Rightarrow> stack \<Rightarrow> int ag_trace \<Rightarrow> int virtual_state \<Rightarrow> int equi_state set \<Rightarrow> bool"
where
  "safe 0 C s \<tau> \<omega> Q \<longleftrightarrow> True"
| "safe (Suc n) C s0 \<tau> \<omega>0 Q \<longleftrightarrow>
  (C = Cskip \<longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q)
  \<and> accesses C s0 \<subseteq> read_dom \<omega>0
  \<and> writes C s0 \<subseteq> write_dom \<omega>0
  \<and> no_aborts C s0 \<omega>0
  \<and> (\<forall>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q))"

lemma safeI:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts C s0 \<omega>0"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
    shows "safe (Suc n) C s0 \<tau> \<omega>0 Q"
  using assms safe.simps(1) by auto


lemma safeI_alt:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "\<And>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>0' \<Longrightarrow> sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow> aborts C (concretize s0 \<omega>0') \<Longrightarrow> False"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
    shows "safe (Suc n) C s0 \<tau> \<omega>0 Q"
  using assms safe.simps(1) 
  by fastforce

lemma safeE:
  assumes "safe (Suc n) C s0 \<tau> \<omega>0 Q"
  shows "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts C s0 \<omega>0"
      and "sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
  using assms safe.simps(1) apply simp_all
  by (metis prod.collapse)


definition CSL :: "int equi_state set \<Rightarrow> cmd \<Rightarrow> int equi_state set \<Rightarrow> bool" where
  "CSL P C Q \<longleftrightarrow> (\<forall>n s \<tau> \<omega>. (Ag s, \<tau>, \<omega>) \<in> P \<and> sep_algebra_class.stable \<omega> \<longrightarrow> safe n C s \<tau> \<omega> Q)"

lemma CSL_I:
  assumes "\<And>n s \<tau> \<omega>. (Ag s, \<tau>, \<omega>) \<in> P \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> safe (Suc n) C s \<tau> \<omega> Q"
  shows "CSL P C Q"
  by (metis CSL_def assms not0_implies_Suc safe.simps(1))

lemma CSL_E:
  assumes "CSL P C Q"
      and "(Ag s, \<tau>, \<omega>) \<in> P"
      and "sep_algebra_class.stable \<omega>"
    shows "safe n C s \<tau> \<omega> Q"
  using CSL_def assms by fast


lemma safety_mono:
  assumes "safe n C s \<tau> \<omega> Q"
      and "m \<le> n"
    shows "safe m C s \<tau> \<omega> Q"
  using assms
proof (induct m arbitrary: C n s \<omega>)
  case (Suc m)
  then obtain k where "n = Suc k"
    using Suc_le_D by presburger
  then show ?case using safeI[of C s \<tau> \<omega> Q] safeE
    by (smt (verit, ccfv_threshold) Suc.hyps Suc.prems(1) Suc.prems(2) Suc_le_mono)
qed (simp)

lemma no_aborts_agrees:
  assumes "no_aborts C s \<omega>"
      and "agrees (fvC C) s s'"
    shows "no_aborts C s' \<omega>"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "sep_algebra_class.stable \<omega>0'" "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f \<and> binary_mask \<omega>0'"
  then show "\<not> aborts C (concretize s' \<omega>0')"
    by (metis aborts_agrees agrees_search(1) assms(1) assms(2) fst_conv no_aborts_def snd_conv)
qed

definition fvA where
  "fvA Q = undefined Q"

lemma fvA_agrees:
  assumes "agrees (fvA Q) s s'"
    shows "(Ag s, \<tau>, \<omega>) \<in> Q \<longleftrightarrow> (Ag s', \<tau>, \<omega>) \<in> Q"
  sorry (* TODO: free_vars... *)

lemma safe_agrees:
  assumes "safe n C s \<tau> \<omega> Q"
      and "agrees (fvC C \<union> fvA Q) s s'"
    shows "safe n C s' \<tau> \<omega> Q"
  using assms
proof (induct n arbitrary: C s s' \<omega>)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s', \<tau>, \<omega>) \<in> Q"
      using safeE(1)[OF Suc.prems(1)]
      by (meson Suc.prems(2) agrees_simps(4) fvA_agrees)
    show "accesses C s' \<subseteq> read_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) accesses_agrees by force
    show "writes C s' \<subseteq> write_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) agrees_simps(4) safeE(3) writes_agrees by blast
    show "no_aborts C s' \<omega>"
      by (meson Suc.prems(1) Suc.prems(2) agrees_simps(4) no_aborts_agrees safeE(4))
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "\<langle>C, concretize s' \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain s' h' where "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
      using red_agrees[OF asm0(4)]
      by (metis Suc.prems(2) Un_upper1 agrees_search(1) fst_conv snd_conv)
    then obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1'
  \<and> snd (s', h') = get_vh \<omega>1' \<and> safe n C' (fst (s', h')) \<tau> \<omega>1 Q"
      using safeE(5)[OF Suc(2), of \<omega>f \<omega>0' C']
      using asm0(1) asm0(2) asm0(3) by blast
    then have "safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
      by (smt (verit, ccfv_SIG) Suc.hyps \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s' \<and> snd \<sigma>' = h'\<close> agreesC agrees_search(2) agrees_simps(4) fstI red_properties)
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
      using \<open>Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd (s', h') = get_vh \<omega>1' \<and> safe n C' (fst (s', h')) \<tau> \<omega>1 Q\<close> \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s' \<and> snd \<sigma>' = h'\<close> by auto
  qed
qed (simp)



subsection \<open>Skip\<close>

lemma safe_skip[intro!]:
  assumes "(Ag s, \<tau>, \<omega>) \<in> Q"
  shows "safe n Cskip s \<tau> \<omega> Q"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "no_aborts Cskip s \<omega>"
      by (simp add: no_abortsI)
    show "Cskip = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> Q"
      by (simp add: assms)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume "\<langle>Cskip, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
      by force
  qed (simp_all)
qed (simp)

proposition rule_skip:
  "CSL P Cskip P"
  using CSL_def by blast




subsection \<open>Frame rule\<close>

lemma read_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "read_dom \<omega> \<subseteq> read_dom \<omega>'"
  by (smt (verit, ccfv_SIG) EquiViper.add_masks_def antisym assms get_vm_additive greater_def mem_Collect_eq not_gr_0 order_less_le pos_perm_class.sum_larger read_dom_def subsetI)


lemma write_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "write_dom \<omega> \<subseteq> write_dom \<omega>'"
proof -
  have "\<And>l. get_vm \<omega>' l \<le> 1" sorry (* TODO: assumption \<le> 1 *)
  moreover have "\<And>l. get_vm \<omega>' l \<ge> get_vm \<omega> l"
    by (metis EquiViper.add_masks_def assms get_vm_additive greater_def pos_perm_class.sum_larger)
  ultimately show ?thesis
    by (metis (mono_tags, lifting) antisym mem_Collect_eq subsetI write_dom_def)
qed

lemma no_aborts_mono_aux:
  assumes "aborts C \<sigma>'"
      and "fst \<sigma>' = s"
      and "snd \<sigma>' = h'"
      and "h \<subseteq>\<^sub>m h'"
    shows "aborts C (s, h)"
  using assms
proof (induct arbitrary:  rule: aborts.induct)
  case (aborts_Read \<sigma> r l x)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Read fst_conv map_le_implies_dom_le snd_conv subsetD)
next
  case (aborts_Write \<sigma> r l E)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Write fst_conv map_le_implies_dom_le snd_conv subsetD)
next
  case (aborts_Free \<sigma> r l)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Free fst_conv map_le_implies_dom_le snd_conv subsetD)
qed (auto)


lemma no_aborts_mono:
  assumes "no_aborts C s \<omega>"
      and "\<omega>' \<succeq> \<omega>"
      and "sep_algebra_class.stable \<omega>"
    shows "no_aborts C s \<omega>'"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "sep_algebra_class.stable \<omega>0'" "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f \<and> binary_mask \<omega>0'"
  then obtain r where "Some \<omega>0' = \<omega> \<oplus> r"
    using assms(2) bigger_sum_smaller by blast
  then have "Some \<omega>0' = \<omega> \<oplus> stabilize r"
    by (metis asm0(1) commutative stabilize_sum_result_stable)
  then show "\<not> aborts C (concretize s \<omega>0')"
    using asm0(1) asm0(3) assms(1) no_aborts_def stabilize_is_stable by blast
qed

lemma compatibleI:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_state a ## get_state b"
    shows "a ## b"
proof (rule compatible_prodI)
  show "fst a ## fst b"
    using assms(1) get_store_trace_comp by blast
  show "snd a ## snd b"
    apply (rule compatible_prodI)
    apply (metis ag_comp agreement.expand assms(2) get_trace_def)
    by (metis assms(3) get_state_def)
qed

lemma sum_equi_statesI:
  assumes "get_store x = get_store a"
      and "get_store x = get_store b"
      and "get_trace x = get_trace a"
      and "get_trace x = get_trace b"
      and "Some (get_state x) = get_state a \<oplus> get_state b"
    shows "Some x = a \<oplus> b"
proof -
  obtain y where "Some y = a \<oplus> b"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) compatibleI defined_def option.distinct(1) option.exhaust_sel)
  moreover have "x = y"
  proof (rule full_state_ext)
    show "get_store x = get_store y"
      by (simp add: assms(1) calculation full_add_charact(1))
    show "get_abs_state x = get_abs_state y"
      by (smt (verit) \<open>get_store x = get_store y\<close> assms(3) assms(5) calculation greater_def greater_state_has_greater_parts(2) option.sel state_add_iff)
  qed
  ultimately show ?thesis by simp
qed


lemma sum_equi_states_easy:
  fixes \<tau> :: "'a ag_trace"
  assumes "Some \<omega> = a \<oplus> b"
  shows "Some (Ag s, \<tau>, \<omega>) = (Ag s, \<tau>, a) \<oplus> (Ag s, \<tau>, b)"
proof (rule plus_prodI)
  show "Some (fst (Ag s, \<tau>, \<omega>)) = fst (Ag s, \<tau>, a) \<oplus> fst (Ag s, \<tau>, b)"
    by (simp add: plus_AgI)
  show "Some (snd (Ag s, \<tau>, \<omega>)) = snd (Ag s, \<tau>, a) \<oplus> snd (Ag s, \<tau>, b)"
  proof (rule plus_prodI)
    show "Some (fst (snd (Ag s, \<tau>, \<omega>))) = fst (snd (Ag s, \<tau>, a)) \<oplus> fst (snd (Ag s, \<tau>, b))"
      by (simp add: plus_AgI)
    show "Some (snd (snd (Ag s, \<tau>, \<omega>))) = snd (snd (Ag s, \<tau>, a)) \<oplus> snd (snd (Ag s, \<tau>, b))"
      using assms by force
  qed
qed

lemma sum_equi_states_easy_rev:
  fixes \<tau> :: "'a ag_trace"
  assumes "Some (Ag s, \<tau>, \<omega>) = (s1, \<tau>1, \<omega>1) \<oplus> (s2, \<tau>2, \<omega>2)"
  shows "s1 = Ag s \<and> s2 = Ag s \<and> \<tau>1 = \<tau> \<and> \<tau>2 = \<tau> \<and> Some \<omega> = \<omega>1 \<oplus> \<omega>2"
proof -
  have "fst (s1, \<tau>1, \<omega>1) \<oplus> fst (s2, \<tau>2, \<omega>2) = Some (fst (Ag s, \<tau>, \<omega>)) \<and> snd (s1, \<tau>1, \<omega>1) \<oplus> snd (s2, \<tau>2, \<omega>2) = Some (snd (Ag s, \<tau>, \<omega>))"
    using plus_prodE[OF HOL.sym[OF assms(1)]] by simp
  then show ?thesis using plus_prodE[of "snd (s1, \<tau>1, \<omega>1)" "snd (s2, \<tau>2, \<omega>2)" "snd (Ag s, \<tau>, \<omega>)"]
    by (metis fst_conv option.discI option.inject plus_agreement_def snd_conv)
qed

lemma frame_safe:
  assumes "safe n C s \<tau> \<omega> Q"
      and "fvA R \<inter> wrC C = {}"
      and "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "(Ag s, \<tau>, \<omega>f) \<in> R"
      and "sep_algebra_class.stable \<omega>f"
      and "sep_algebra_class.stable \<omega>"
    shows "safe n C s \<tau> \<omega>' (Q \<otimes> R)"
  using assms
proof (induct n arbitrary: C \<omega> \<omega>' \<omega>f s)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>') \<in> Q \<otimes> R"
      using safeE(1)[OF Suc(2)]
      by (meson Suc.prems(3) Suc.prems(4) sum_equi_states_easy x_elem_set_product)
    show "accesses C s \<subseteq> read_dom \<omega>'"
      using safeE(2)[OF Suc(2)]
      using Suc.prems(3) commutative greater_equiv read_dom_mono by fastforce
    show "writes C s \<subseteq> write_dom \<omega>'"
      by (metis (no_types, lifting) Suc.prems(1) Suc.prems(3) greater_def inf.absorb_iff2 inf.coboundedI1 safeE(3) write_dom_mono)
    show "no_aborts C s \<omega>'"
      by (meson Suc.prems(1) Suc.prems(3) Suc.prems(6) greater_def no_aborts_mono safeE(4))
    fix \<omega>0' \<omega>f' C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f'" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f'" "binary_mask \<omega>0'" "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>f'' where "Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asso2 option.collapse)
    then have "Some \<omega>0' = \<omega> \<oplus> \<omega>f''"
      using asm0 Suc.prems(3) asso1 by force
    then obtain \<omega>1'' \<omega>1' where "Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'" "safe n C' (fst \<sigma>') \<tau> \<omega>1'' Q"
      "sep_algebra_class.stable \<omega>1''"
      using safeE(5)[OF Suc(2), of \<omega>0' \<omega>f'' C' \<sigma>'] asm0 
      by (meson Suc.prems(1) Suc.prems(5) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> safeE(5) stable_sum)
    then obtain \<omega>1 where "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
      by (metis (no_types, opaque_lifting) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> asso3 option.collapse)
    moreover have "safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q \<otimes> R)"
      using \<open>safe n C' (fst \<sigma>') \<tau> \<omega>1'' Q\<close>
    proof (rule Suc(1)[of C' _ \<omega>1'' \<omega>1 \<omega>f])
      show "fvA R \<inter> wrC C' = {}"
        by (meson Suc.prems(2) asm0 disjoint_iff red_properties subset_iff)
      show "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
        using calculation by auto
      have "agrees (-(wrC C)) s (fst \<sigma>')"
        by (metis agrees_search(1) asm0(4) fst_conv red_properties)
      then have "agrees (fvA R) s (fst \<sigma>')"
        using Suc.prems(2) agrees_search(3) by auto
      then show "(Ag (fst \<sigma>'), \<tau>, \<omega>f) \<in> R"
        by (meson Suc.prems(4) fvA_agrees)
      show "sep_algebra_class.stable \<omega>1''"
        by (simp add: \<open>sep_algebra_class.stable \<omega>1''\<close>)
    qed (simp_all add: Suc.prems)
    ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f' \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q \<otimes> R)"
      by (metis Suc.prems(5) \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'\<close> \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> \<open>sep_algebra_class.stable \<omega>1''\<close> asso1 stable_sum)
  qed
qed (simp)

(*
lemma self_framing_wf_split:
  assumes "\<omega> \<in> A \<otimes> B"
      and "TypedEqui.wf_assertion \<Delta> A"
      and "self_framing B"
    shows "\<exists>a b. a \<in> A \<and> b \<in> B \<and> Some \<omega> = a \<oplus> b \<and> sep_algebra_class.stable b"
proof -
  obtain a b where "Some \<omega> = a \<oplus> b" "a \<in> A" "b \<in> B"
    by (meson assms(1) x_elem_set_product)
  then obtain a' where "Some a' = a \<oplus> |\<omega>|"
    by (metis commutative minus_equiv_def_any_elem)
  then have "Some \<omega> = a' \<oplus> stabilize b"
    by (smt (verit, best) \<open>Some \<omega> = a \<oplus> b\<close> asso1 commutative core_is_pure core_is_smaller core_sum decompose_stabilize_pure)
  then show ?thesis
    by (metis (no_types, opaque_lifting) TypedEqui.wf_assertion_def \<open>Some a' = a \<oplus> |\<omega>|\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> assms(2) assms(3) core_is_pure in_Stabilize pure_def pure_larger_def self_framing_eq stabilize_is_stable)
qed
*)

lemma sum_equi_states_easy_decompose:
  fixes \<tau> :: "'a ag_trace"
  assumes "(Ag s, \<tau>, \<omega>) \<in> P \<otimes> R"
  shows "\<exists>\<omega>p \<omega>r. Some \<omega> = \<omega>p \<oplus> \<omega>r \<and> (Ag s, \<tau>, \<omega>p) \<in> P \<and> (Ag s, \<tau>, \<omega>r) \<in> R"
proof -
  obtain p r where "Some (Ag s, \<tau>, \<omega>) = p \<oplus> r" "p \<in> P" "r \<in> R"
    by (meson assms x_elem_set_product)
  then have "fst p = fst r \<and> fst p = Ag s"
    by (metis eq_fst_iff sum_equi_states_easy_rev)
  moreover have "fst (snd p) = fst (snd r) \<and> fst (snd p) = \<tau>"
    by (metis \<open>Some (Ag s, \<tau>, \<omega>) = p \<oplus> r\<close> prod.exhaust_sel sum_equi_states_easy_rev)
  ultimately show ?thesis
    by (metis \<open>Some (Ag s, \<tau>, \<omega>) = p \<oplus> r\<close> \<open>p \<in> P\<close> \<open>r \<in> R\<close> prod.exhaust_sel sum_equi_states_easy_rev)
qed


lemma stabilize_equi_state:
  fixes \<tau> :: "'a ag_trace"
  shows "stabilize (Ag s, \<tau>, \<omega>) = (Ag s, \<tau>, stabilize \<omega>)"
  by (smt (z3) core_def decompose_stabilize_pure snd_conv stabilize_prod_def sum_equi_states_easy_rev)


proposition frame_rule:
  assumes "CSL P C Q"
      and "disjoint (fvA R) (wrC C)"
      and "self_framing P"
      and "self_framing R"
    shows "CSL (P \<otimes> R) C (Q \<otimes> R)"
proof (rule CSL_I)
  fix n s \<tau> \<omega> assume "(Ag s, \<tau>, \<omega>) \<in> P \<otimes> R" "sep_algebra_class.stable \<omega>"
  then obtain \<omega>p \<omega>r where r: "Some \<omega> = \<omega>p \<oplus> \<omega>r" "(Ag s, \<tau>, \<omega>p) \<in> P" "(Ag s, \<tau>, \<omega>r) \<in> R"
    by (meson sum_equi_states_easy_decompose)
  then have "Some \<omega> = stabilize \<omega>p \<oplus> stabilize \<omega>r"
    using \<open>sep_algebra_class.stable \<omega>\<close> stabilize_sum_of_stable by blast
  then show "safe (Suc n) C s \<tau> \<omega> (Q \<otimes> R)"
    using frame_safe[of n C s \<tau> "stabilize \<omega>p" Q R \<omega> "stabilize \<omega>r"]
    by (metis (no_types, lifting) CSL_def assms(1) assms(2) assms(3) assms(4) disjoint_def frame_safe r(2) r(3) self_framing_def stabilize_equi_state stabilize_is_stable)
qed




subsection \<open>Parallel rule\<close>

lemma disj_conv:
  assumes "\<omega>1 ## \<omega>2"
  shows "disjoint (write_dom \<omega>1) (read_dom \<omega>2)"
  unfolding disjoint_def
proof
  show "write_dom \<omega>1 \<inter> read_dom \<omega>2 \<subseteq> {}"
  proof
    fix l assume "l \<in> write_dom \<omega>1 \<inter> read_dom \<omega>2"
    then have "get_vm \<omega>1 (l, field_val) + get_vm \<omega>2 (l, field_val) > 1"
      by (smt (verit) CollectD IntD1 add.commute comm_monoid_add_class.add_0 inf.absorb_iff2 inf_commute leI not_gr_0 pos_perm_class.padd_cancellative pos_perm_class.sum_larger read_dom_def write_dom_def)
    then show "l \<in> {}"
      sorry (* TODO: Need \<le> 1 assumption *)
  qed
qed (simp)

lemma read_dom_union:
  assumes "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
  shows "read_dom \<omega> = read_dom \<omega>1 \<union> read_dom \<omega>2" (is "?A = ?B")
proof -
  have "\<And>l. l \<in> ?A \<longleftrightarrow> l \<in> ?B"
  proof -
    fix l
    have "l \<in> ?A \<longleftrightarrow> get_vm \<omega> (l, field_val) > 0"
      unfolding read_dom_def by simp
    also have "... \<longleftrightarrow> get_vm \<omega>1 (l, field_val) + get_vm \<omega>2 (l, field_val) > 0"
      by (simp add: EquiViper.add_masks_def assms get_vm_additive)
    also have "... \<longleftrightarrow> get_vm \<omega>1 (l, field_val) > 0 \<or> get_vm \<omega>2 (l, field_val) > 0"
      by (metis add_0 padd_pos pperm_pnone_pgt)
    finally show "l \<in> ?A \<longleftrightarrow> l \<in> ?B"
      unfolding read_dom_def by blast
  qed
  then show ?thesis by blast
qed


lemma write_dom_union:
  assumes "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
  shows "write_dom \<omega>1 \<union> write_dom \<omega>2 \<subseteq> write_dom \<omega>"
  by (meson Un_least assms greater_def greater_equiv write_dom_mono)

lemma safe_par:
  assumes "safe n C1 s \<tau> \<omega>1 Q1"
      and "safe n C2 s \<tau> \<omega>2 Q2"
      and "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
      and "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
      and "sep_algebra_class.stable \<omega>1"
      and "sep_algebra_class.stable \<omega>2"
    shows "safe n (C1 || C2) s \<tau> \<omega> (Q1 \<otimes> Q2)"
  using assms
proof (induct n arbitrary: C1 C2 \<omega>1 \<omega>2 \<omega> s)
  case (Suc n)
  show "safe (Suc n) (C1 || C2) s \<tau> \<omega> (Q1 \<otimes> Q2)"
  proof (rule safeI_alt)
    show "accesses (C1 || C2) s \<subseteq> read_dom \<omega>"
      by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) Un_mono accesses.simps(8) read_dom_union safeE(2))
    show "writes (C1 || C2) s \<subseteq> write_dom \<omega>"
    proof -
      have "writes C1 s \<subseteq> write_dom \<omega> \<and> writes C2 s \<subseteq> write_dom \<omega>"
        by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Suc.prems(3) dual_order.trans le_supE safeE(3) write_dom_union)
      then show ?thesis
        by simp
    qed
    fix \<omega>0' \<omega>f
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    show "aborts (C1 || C2) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts (C1 || C2) (concretize s \<omega>0')"
      then show "False"
      proof (rule aborts_par_elim)
        show "aborts C1 (concretize s \<omega>0') \<Longrightarrow> False"
          using safeE(4)[OF Suc.prems(1)]
          by (metis Suc.prems(3) Suc.prems(6) Suc.prems(7) asm0(1) asm0(2) asm0(3) greater_def no_aborts_def no_aborts_mono stable_sum)
        show "aborts C2 (concretize s \<omega>0') \<Longrightarrow> False"
          using safeE(4)[OF Suc.prems(2)]
          by (metis Suc.prems(3) Suc.prems(6) Suc.prems(7) asm0(1) asm0(2) asm0(3) commutative greater_def no_aborts_def no_aborts_mono stable_sum)
        have r1: "accesses C1 s \<subseteq> read_dom \<omega>1 \<and> writes C1 s \<subseteq> write_dom \<omega>1"
          using Suc.prems(1) by auto
        moreover have r2: "accesses C2 s \<subseteq> read_dom \<omega>2 \<and> writes C2 s \<subseteq> write_dom \<omega>2"
          using Suc.prems(2) by auto
        ultimately show "\<not> disjoint (accesses C1 (fst (concretize s \<omega>0'))) (writes C2 (fst (concretize s \<omega>0'))) \<Longrightarrow> False"
          by (metis (no_types, lifting) Pair_inject Suc.prems(3) commutative defined_def disj_conv disjoint_search(3) disjoint_search(4) option.simps(3) prod.exhaust_sel)
        show "\<not> disjoint (writes C1 (fst (concretize s \<omega>0'))) (accesses C2 (fst (concretize s \<omega>0'))) \<Longrightarrow> False"
          by (metis (no_types, lifting) Pair_inject Suc.prems(3) defined_def disj_conv disjoint_search(5) option.discI r1 r2 surjective_pairing)
      qed
    qed

    fix C' \<sigma>'
    assume asm1: "\<langle>C1 || C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
    proof (rule red_par_cases)
      show "C' = Cskip \<Longrightarrow> \<sigma>' = concretize s \<omega>0' \<Longrightarrow> C1 = Cskip \<Longrightarrow> C2 = Cskip
  \<Longrightarrow> \<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using safeE(1)[OF Suc.prems(1)] safeE(1)[OF Suc.prems(2)]
        by (metis Suc.prems(3) Suc.prems(5) Suc.prems(6) Suc.prems(7) asm0(2) asm0(3) disjoint_def disjoint_simps(3) frame_safe fst_conv safe_skip snd_conv stable_sum)
      fix C1'
      assume asm2: "C' = C1' || C2" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>2 \<oplus> \<omega>f"
        by (metis (no_types, opaque_lifting) Suc.prems(3) asm0(2) asso2 option.exhaust_sel)
      then have "Some \<omega>0' = \<omega>1 \<oplus> \<omega>f'"
        using Suc.prems(3) asm0(2) asso1 by force
      then obtain \<omega>a \<omega>a' where ra: "Some \<omega>a' = \<omega>a \<oplus> \<omega>f' \<and> binary_mask \<omega>a' \<and> snd \<sigma>' = get_vh \<omega>a'" "safe n C1' (fst \<sigma>') \<tau> \<omega>a Q1"
        "sep_algebra_class.stable \<omega>a"
        using safeE(5)[OF Suc(2), of \<omega>f' \<omega>0' C1' \<sigma>'] asm0 asm2(2)
        using Suc.prems(7) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> stable_sum by blast
      moreover have "safe n C2 (fst \<sigma>') \<tau> \<omega>2 Q2"
      proof -
        have "safe n C2 s \<tau> \<omega>2 Q2"
          by (meson Suc.prems(2) Suc_n_not_le_n nat_le_linear safety_mono)
        moreover have "agrees (-wrC C1) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        ultimately show ?thesis
          using Suc.prems(5) agrees_minusD disjoint_commute safe_agrees by blast
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>a \<oplus> \<omega>2"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso2 calculation(1) commutative option.exhaust_sel)
      then have "Some \<omega>a' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso1 calculation(1))
      ultimately have "safe n C' (fst \<sigma>') \<tau> \<omega>' (Q1 \<otimes> Q2)"
        using Suc(1)[OF ra(2) \<open>safe n C2 (fst \<sigma>') \<tau> \<omega>2 Q2\<close>]
        by (metis (no_types, lifting) Suc.prems(4) Suc.prems(5) Suc.prems(7) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close> asm2(1) asm2(2) disjoint_search(2) disjoint_search(4) disjoint_simps(3) red_properties)
      
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>a' = \<omega>' \<oplus> \<omega>f\<close> ra(1)
        using Suc.prems(7) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close> \<open>sep_algebra_class.stable \<omega>a\<close> stable_sum by blast
    next
      fix C2'
      assume asm2: "C' = C1 || C2'" "\<langle>C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C2', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>1 \<oplus> \<omega>f"
        by (metis Suc.prems(3) asm0(2) asso2 commutative option.exhaust_sel)
      then have "Some \<omega>0' = \<omega>2 \<oplus> \<omega>f'"
        by (metis Suc.prems(3) asm0(2) asso1 commutative)
      then obtain \<omega>b \<omega>b' where rb: "Some \<omega>b' = \<omega>b \<oplus> \<omega>f' \<and> binary_mask \<omega>b' \<and> snd \<sigma>' = get_vh \<omega>b'" "safe n C2' (fst \<sigma>') \<tau> \<omega>b Q2"
        "sep_algebra_class.stable \<omega>b"
        using safeE(5)[OF Suc(3), of \<omega>f' \<omega>0' C2' \<sigma>'] asm0 asm2(2)
        using Suc.prems(6) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> stable_sum by blast
      moreover have "safe n C1 (fst \<sigma>') \<tau> \<omega>1 Q1"
      proof -
        have "safe n C1 s \<tau> \<omega>1 Q1"
          by (meson Suc.prems(1) Suc_n_not_le_n nat_le_linear safety_mono)
        moreover have "agrees (-wrC C2) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        ultimately show ?thesis
          using Suc.prems(4) agrees_minusD disjoint_search(1) safe_agrees by blast
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>b \<oplus> \<omega>1"
        by (metis \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso3 option.exhaust_sel rb(1))
      then have "Some \<omega>b' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso1 rb(1))
      ultimately have "safe n C' (fst \<sigma>') \<tau> \<omega>' (Q1 \<otimes> Q2)"
        using Suc(1)[OF \<open>safe n C1 (fst \<sigma>') \<tau> \<omega>1 Q1\<close> rb(2)]
        by (metis (no_types, lifting) Suc.prems(4) Suc.prems(5) Suc.prems(6) \<open>Some \<omega>' = \<omega>b \<oplus> \<omega>1\<close> asm2(1) asm2(2) commutative disjoint_search(4) disjoint_simps(3) red_properties sup.orderE)      
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using Suc.prems(6) \<open>Some \<omega>' = \<omega>b \<oplus> \<omega>1\<close> \<open>Some \<omega>b' = \<omega>' \<oplus> \<omega>f\<close> rb(1) rb(3) stable_sum by blast
    qed
  qed (simp)
qed (simp)




proposition rule_par:
  assumes "CSL P1 C1 Q1"
      and "CSL P2 C2 Q2"
      and "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
      and "self_framing P1"
      and "self_framing P2"
    shows "CSL (P1 \<otimes> P2) (C1 || C2) (Q1 \<otimes> Q2)"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> P1 \<otimes> P2" "sep_algebra_class.stable \<omega>"
  then obtain p1 p2 where "Some \<omega> = p1 \<oplus> p2" "(Ag s, \<tau>, p1) \<in> P1" "(Ag s, \<tau>, p2) \<in> P2"
    by (meson sum_equi_states_easy_decompose)
  then have "Some \<omega> = stabilize p1 \<oplus> stabilize p2"
    using asm0(2) stabilize_sum_of_stable by blast
  then show "safe (Suc n) (C1 || C2) s \<tau> \<omega> (Q1 \<otimes> Q2)"
    using safe_par[of "Suc n" C1 s \<tau> p1 Q1 C2 p2 Q2 \<omega>]
    by (metis CSL_def \<open>(Ag s, \<tau>, p1) \<in> P1\<close> \<open>(Ag s, \<tau>, p2) \<in> P2\<close> assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) safe_par self_framing_def stabilize_equi_state stabilize_is_stable)
qed


subsection \<open>Sequential composition\<close>

lemma safe_seq:
  assumes "safe n C1 s \<tau> \<omega> Q"
      and "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<tau>, \<omega>') \<in> Q \<and> sep_algebra_class.stable \<omega>' \<Longrightarrow> safe m C2 s' \<tau> \<omega>' R"
      and "sep_algebra_class.stable \<omega>"
    shows "safe n (Cseq C1 C2) s \<tau> \<omega> R"
  using assms
proof (induct n arbitrary: C1 \<omega> s)
  case (Suc n)
  show "safe (Suc n) (Cseq C1 C2) s \<tau> \<omega> R"
  proof (rule safeI)
    show "accesses (Cseq C1 C2) s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) accesses.simps(7) safeE(2) by blast
    show "writes (Cseq C1 C2) s \<subseteq> write_dom \<omega>"
      by (metis Suc.prems(1) safeE(3) writes.simps(7))
    show "no_aborts (Cseq C1 C2) s \<omega>"
      using safeE(4)[OF Suc.prems(1)] aborts_seq_elim
      by (meson no_aborts_def)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Cseq C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 R"
    proof (rule red_seq_cases)
      assume asm1: "C1 = Cskip" "C' = C2" "\<sigma>' = concretize s \<omega>0'"
      then have "safe (Suc n) C2 s \<tau> \<omega> R"
        using Suc.prems(2)[of "Suc n" _ \<omega>] safeE(1)[OF Suc.prems(1)] Suc.prems(3) by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 R"
        using safeE(5)
        by (metis (no_types, lifting) Suc.prems(3) Suc_n_not_le_n asm0(2) asm0(3) asm1(2) asm1(3) fst_conv nat_le_linear safety_mono snd_conv)
    next
      fix C1' assume asm1: "C' = Cseq C1' C2" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      then obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f" "sep_algebra_class.stable \<omega>1" "binary_mask \<omega>1'"
        "snd \<sigma>' = get_vh \<omega>1'" "safe n C1' (fst \<sigma>') \<tau> \<omega>1 Q"
        using safeE(5)[OF Suc.prems(1), of \<omega>f \<omega>0' C1' \<sigma>'] asm0(1) asm0(2) asm0(3) by blast
      then have "safe n (Cseq C1' C2) (fst \<sigma>') \<tau> \<omega>1 R" using Suc(1)[OF \<open>safe n C1' (fst \<sigma>') \<tau> \<omega>1 Q\<close>]
        by (simp add: Suc.prems(2))
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 R"
        using \<open>Some \<omega>1' = \<omega>1 \<oplus> \<omega>f\<close> \<open>binary_mask \<omega>1'\<close> \<open>sep_algebra_class.stable \<omega>1\<close> \<open>snd \<sigma>' = get_vh \<omega>1'\<close> asm1(1) by blast
    qed
  qed (simp)
qed (simp)


proposition rule_seq:
  assumes "CSL P C1 Q"
    and "CSL Q C2 R"
    shows "CSL P (Cseq C1 C2) R"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> P" "sep_algebra_class.stable \<omega>"
  show "safe n (Cseq C1 C2) s \<tau> \<omega> R"
  proof (rule safe_seq[of n C1 s \<tau> \<omega> Q C2 R])
    show "safe n C1 s \<tau> \<omega> Q"
      using CSL_E asm0(1) asm0(2) assms(1) by blast
    show "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<tau>, \<omega>') \<in> Q \<and> sep_algebra_class.stable \<omega>' \<Longrightarrow> safe m C2 s' \<tau> \<omega>' R"
      using CSL_E[OF assms(2)] by blast
  qed (simp add: asm0)
qed



subsection \<open>Consequence rule\<close>

lemma safe_conseq:
  assumes "safe n C s \<tau> \<omega> Q"
      and "Q \<subseteq> Q'"
    shows "safe n C s \<tau> \<omega> Q'"
  using assms
proof (induct n arbitrary: C \<omega> s)
  case (Suc n)
  show "safe (Suc n) C s \<tau> \<omega> Q'"
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> Q'"
      using Suc.prems(1) assms(2) safe.simps(2) by blast
    show "accesses C s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) safeE(2) by blast
    show "writes C s \<subseteq> write_dom \<omega>"
      using Suc.prems(1) by auto
    show "no_aborts C s \<omega>"
      using Suc.prems(1) safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
      "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q'"
      using safeE(5)[OF Suc.prems(1)] by (meson Suc.hyps assms(2))
  qed
qed (simp)

proposition rule_conseq:
  assumes "CSL P C Q"
      and "P' \<subseteq> P"
      and "Q \<subseteq> Q'"
    shows "CSL P' C Q'"
proof (rule CSL_I)
  show "\<And>n s \<tau> \<omega>. (Ag s, \<tau>, \<omega>) \<in> P' \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> safe (Suc n) C s \<tau> \<omega> Q'"
    using CSL_E assms(1) assms(2) assms(3) safe_conseq by blast
qed



subsection \<open>Conditional rule\<close>

(*
| RuleIf: "\<lbrakk> self_framing_and_typed \<Delta> A; framed_by_exp A b; \<Delta> \<turnstile> [A \<otimes> pure_typed \<Delta> b] C1 [B1] ; \<Delta> \<turnstile> [A \<otimes> pure_typed \<Delta> (negate b)] C2 [B2] \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> [A] If b C1 C2 [B1 \<union> B2]"
*)
definition assertify_bexp where
  "assertify_bexp b = { \<omega> |\<omega>. bdenot b (get_store \<omega>)}"

lemma in_assertify_bexp:
  assumes "bdenot b (get_store \<omega>)"
  shows "\<omega> \<in> assertify_bexp b"
  by (simp add: assertify_bexp_def assms)

lemma in_assertify_bexp_alt:
  assumes "bdenot b s"
  shows "(Ag s, \<tau>, \<omega>) \<in> assertify_bexp b"
  by (simp add: assms get_store_def in_assertify_bexp)

proposition rule_if:
  assumes "CSL (P \<inter> assertify_bexp b) C1 Q"
      and "CSL (P \<inter> assertify_bexp (Bnot b)) C2 Q"
    shows "CSL P (Cif b C1 C2) Q"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> P" "sep_algebra_class.stable \<omega>"
  show "safe (Suc n) (Cif b C1 C2) s \<tau> \<omega> Q"
  proof (rule safeI)
    show "no_aborts (Cif b C1 C2) s \<omega>"
      using aborts.cases cmd.distinct(45) cmd.distinct(57) cmd.distinct(85) cmd.simps(91) no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Cif b C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
    proof (rule red_if_cases)
      assume asm2: "C' = C1" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<tau>, \<omega>) \<in> P \<inter> assertify_bexp b"
        by (simp add: asm0(1) asm1(2) full_add_charact(1) in_assertify_bexp_alt)
      then have "safe n C' s \<tau> \<omega> Q"
        using CSL_E[OF assms(1), of s \<tau> \<omega> n] asm0 asm2 by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    next
      assume asm2: "C' = C2" "\<sigma>' = concretize s \<omega>0'" "\<not> bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<tau>, \<omega>) \<in> P \<inter> assertify_bexp (Bnot b)"
        by (simp add: asm0(1) asm1(2) full_add_charact(1) in_assertify_bexp_alt)
      then have "safe n C' s \<tau> \<omega> Q"
        using CSL_E[OF assms(2), of s \<tau> \<omega> n] asm0 asm2 by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    qed
  qed (simp_all)
qed


subsection \<open>While loops\<close>


lemma safe_while:
  assumes "CSL (I \<inter> (assertify_bexp b)) C I"
      and "(Ag s, \<tau>, \<omega>) \<in> I"
      and "sep_algebra_class.stable \<omega>"
    shows "safe n (Cwhile b C) s \<tau> \<omega> (I \<inter> (assertify_bexp (Bnot b)))"
  using assms
proof (induct n arbitrary: \<omega> s)
  case (Suc n)
  note SucOuter = Suc
  show "safe (Suc n) (Cwhile b C) s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
  proof (rule safeI)
    show "no_aborts (Cwhile b C) s \<omega>"
      using aborts_while_elim no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Cwhile b C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
    proof (rule red_while_cases)
      assume asm1: "C' = Cif b (Cseq C (Cwhile b C)) Cskip" "\<sigma>' = concretize s \<omega>0'"
      have "safe n C' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
      proof (cases n)
        case (Suc m)
        show "safe n C' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
          unfolding Suc
        proof (rule safeI)
          show "no_aborts C' s \<omega>"
            using asm1(1) by blast
          fix \<omega>0' \<omega>f C'' \<sigma>'
          assume asm2: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
          assume "\<langle>C', concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C'', \<sigma>'\<rangle>"
          then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
            unfolding asm1(1)
          proof (rule red_if_cases)
            show "C'' = Cskip \<Longrightarrow> \<sigma>' = concretize s \<omega>0' \<Longrightarrow> \<not> bdenot b (fst (concretize s \<omega>0')) \<Longrightarrow>
    \<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              by (metis IntI SucOuter(3) SucOuter(4) asm2(2) asm2(3) bdenot.simps(3) fst_conv in_assertify_bexp_alt safe_skip snd_conv)
            assume asm3: "C'' = Cseq C (Cwhile b C)" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
            have "safe m C'' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
              unfolding asm3(1)
            proof (rule safe_seq)
              show "safe m C s \<tau> \<omega> I"
                by (metis CSL_def IntI SucOuter(3) SucOuter(4) asm3(3) assms(1) fst_conv in_assertify_bexp_alt)
              show "\<And>ma \<omega>' s'. ma \<le> m \<and> (Ag s', \<tau>, \<omega>') \<in> I \<and> sep_algebra_class.stable \<omega>' \<Longrightarrow> safe ma (Cwhile b C) s' \<tau> \<omega>' (I \<inter> assertify_bexp (Bnot b))"
                using Suc Suc.hyps[OF assms(1)] le_SucI safety_mono by fast
            qed (simp add: \<open>sep_algebra_class.stable \<omega>\<close>)
            then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              using SucOuter(4) asm2(2) asm2(3) asm3(2) by auto
          qed
        qed (simp_all add: asm1(1))
      qed (simp)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
        using asm0 Suc.prems(3) asm1(2) by auto
    qed
  qed (simp_all)
qed (simp)


proposition rule_while:
  assumes "CSL (I \<inter> (assertify_bexp b)) C I"
      and "self_framing I"
    shows "CSL I (Cwhile b C) (I \<inter> (assertify_bexp (Bnot b)))"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume "(Ag s, \<tau>, \<omega>) \<in> I" "sep_algebra_class.stable \<omega>"
  then show "safe (Suc n) (Cwhile b C) s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
    using assms(1) safe_while by blast
qed




subsection \<open>Rule FieldAssign\<close>

abbreviation update_heap_val where
  "update_heap_val \<omega> l v \<equiv> set_state \<omega> (set_value (get_state \<omega>) l v)"

lemma write_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "sep_algebra_class.stable \<omega>f"
      and "get_vm \<omega> l = 1"
    shows "Some (set_value \<omega>' l v) = set_value \<omega> l v \<oplus> \<omega>f"
proof -
  have "get_vm \<omega>' l = get_vm \<omega> l + get_vm \<omega>f l"
    using EquiViper.add_masks_def assms(1) get_vm_additive by blast
  moreover have "get_vm \<omega>' l \<le> 1"
    sorry (* TODO: Need assumption in def of virtual_state *)
  ultimately have "get_vm \<omega>f l = 0"
    by (metis PosReal.padd_cancellative add.commute add.right_neutral assms(3) nle_le pos_perm_class.sum_larger)
  moreover have "get_vh \<omega>f l = None"
    using assms(2) calculation pperm_pgt_pnone stable_virtual_state_def by blast
  show ?thesis
  proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
    show "Some (Rep_virtual_state (set_value \<omega>' l v)) = Rep_virtual_state (set_value \<omega> l v) \<oplus> Rep_virtual_state \<omega>f"
    proof (rule plus_prodI)
      show "Some (fst (Rep_virtual_state (set_value \<omega>' l v))) = fst (Rep_virtual_state (set_value \<omega> l v)) \<oplus> fst (Rep_virtual_state \<omega>f)"
        by (metis assms(1) get_vm_additive get_vm_def set_value_charact(1))
      show "Some (snd (Rep_virtual_state (set_value \<omega>' l v))) = snd (Rep_virtual_state (set_value \<omega> l v)) \<oplus> snd (Rep_virtual_state \<omega>f)"
      proof (rule plus_funI)
        fix la show "Some (snd (Rep_virtual_state (set_value \<omega>' l v)) la) = snd (Rep_virtual_state (set_value \<omega> l v)) la \<oplus> snd (Rep_virtual_state \<omega>f) la"
        proof (cases "l = la")
          case True
          then have "snd (Rep_virtual_state (set_value \<omega>' l v)) la = Some v"
            by (metis fun_upd_apply get_vh_def set_value_charact(2))
          moreover have "snd (Rep_virtual_state (set_value \<omega> l v)) la = Some v"
            by (metis True fun_upd_apply get_vh_def set_value_charact(2))
          ultimately show ?thesis
            by (metis True \<open>get_vh \<omega>f l = None\<close> get_vh_def plus_option.simps(2))
        next
          case False
          then show ?thesis
            by (metis assms(1) fun_upd_apply get_vh_def plus_funE set_value_charact(2) vstate_add_iff)
        qed
      qed
    qed
  qed
qed


definition full_ownership :: "var \<Rightarrow> int equi_state set"
  where
  "full_ownership r = { \<omega> |\<omega> l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1}"

definition full_ownership_with_val where
  "full_ownership_with_val r e = { \<omega> |\<omega> l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1
  \<and> get_h \<omega> (l, field_val) = Some (VInt (edenot e (get_store \<omega>)))  }"

lemma in_full_ownership_with_val:
  assumes "get_store \<omega> r = Some (VRef (Address l))"
      and "get_m \<omega> (l, field_val) = 1"
      and "get_h \<omega> (l, field_val) = Some (VInt (edenot e (get_store \<omega>)))"
    shows "\<omega> \<in> full_ownership_with_val r e"
  using assms full_ownership_with_val_def by blast

lemma get_simps_unfolded[simp]:
  "get_store (Ag s, \<tau>, \<omega>) = s"
  "get_state (Ag s, \<tau>, \<omega>) = \<omega>"
  "get_h (Ag s, \<tau>, \<omega>) = get_vh \<omega>"
  "get_m (Ag s, \<tau>, \<omega>) = get_vm \<omega>"
     apply (simp add: get_store_def)
      apply (simp add: get_state_def)
    apply (simp add: get_state_def)
  by (simp add: get_state_def)


lemma in_full_ownership_with_val_alt:
  assumes "s r = Some (VRef (Address l))"
      and "get_vm \<omega> (l, field_val) = 1"
      and "get_vh \<omega> (l, field_val) = Some (VInt (edenot e s))"
    shows "(Ag s, \<tau>, \<omega>) \<in> full_ownership_with_val r e"
  unfolding full_ownership_with_val_def
  using assms by auto


lemma in_read_dom_write_dom:
  assumes "get_vm \<omega> (l, field_val) = 1"
  shows "l \<in> read_dom \<omega>"
    and "l \<in> write_dom \<omega>"
  apply (metis CollectI assms not_gr_0 read_dom_def zero_neq_one)
  by (simp add: assms write_dom_def)

lemma stable_before_then_update_stable:
  assumes "sep_algebra_class.stable \<omega>"
      and "get_vh \<omega> l \<noteq> None"
  shows "sep_algebra_class.stable (set_value \<omega> l v)"
  by (metis assms(1) assms(2) fun_upd_apply set_value_charact(1) set_value_charact(2) stable_virtual_state_def)


proposition rule_write:
  "CSL (full_ownership r) (Cwrite r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n s \<tau> \<omega> assume "(Ag s, \<tau>, \<omega>) \<in> full_ownership r" "sep_algebra_class.stable \<omega>"
  then obtain l where asm0: "s r = Some (VRef (Address l)) \<and> get_vm \<omega> (l, field_val) = 1"
    using full_ownership_def by fastforce
  show "safe n (Cwrite r e) s \<tau> \<omega> (full_ownership_with_val r e)"
  proof (cases n)
    case (Suc m)
    moreover have "safe (Suc m) (Cwrite r e) s \<tau> \<omega> (full_ownership_with_val r e)"
    proof (rule safeI_alt)
      have "accesses (Cwrite r e) s = {l}" using get_address_simp asm0 by auto
      then show "accesses (Cwrite r e) s \<subseteq> read_dom \<omega>" using asm0
        by (simp add: in_read_dom_write_dom(1))
      show "writes (Cwrite r e) s \<subseteq> write_dom \<omega>"
        by (simp add: asm0 in_read_dom_write_dom(2))
      fix \<omega>0' \<omega>f
      assume asm1: "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "sep_algebra_class.stable \<omega>f"
      then have "s r = Some (VRef (Address l)) \<and> get_vm \<omega>0' (l, field_val) = 1"
        by (metis EquiViper.add_masks_def asm0 binary_mask_def get_vm_additive padd_pos)
      then have "get_vh \<omega>0' (l, field_val) \<noteq> None"
        by (simp add: pperm_pnone_pgt vstate_wf_imp)

      show "aborts (Cwrite r e) (concretize s \<omega>0') \<Longrightarrow> False"
      proof -
        assume "aborts (Cwrite r e) (concretize s \<omega>0')"
        then show False
          using \<open>get_vh \<omega>0' (l, field_val) \<noteq> None\<close> asm0 by auto
      qed
      fix C' \<sigma>'
      assume asm2: "sep_algebra_class.stable \<omega>f" "\<langle>Cwrite r e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      let ?v = "VInt (edenot e s)"

      have "Some (set_value \<omega>0' (l, field_val) ?v) = set_value \<omega> (l, field_val) ?v \<oplus> \<omega>f"
        using asm0 asm1 asm2 write_helper by blast
      moreover have "\<sigma>' = concretize s (set_value \<omega>0' (l, field_val) ?v) \<and> C' = Cskip"
        using red_write_cases[OF asm2(2)]
        using \<open>s r = Some (VRef (Address l)) \<and> get_vm \<omega>0' (l, field_val) = PosReal.pwrite\<close> old.prod.inject option.inject ref.inject set_value_charact(2) val.inject(4) by fastforce
      moreover have "safe m Cskip s \<tau> (set_value \<omega> (l, field_val) ?v) (full_ownership_with_val r e)"
      proof (rule safe_skip)
        show "(Ag s, \<tau>, set_value \<omega> (l, field_val) (VInt (edenot e s))) \<in> full_ownership_with_val r e"
          by (simp add: asm0 asm1 full_add_charact(1) full_ownership_with_val_def)
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe m C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"
        by (metis \<open>sep_algebra_class.stable \<omega>\<close> asm0 asm1(2) binary_mask_def fst_conv not_gr_0 one_neq_zero set_value_charact(1) snd_conv stable_before_then_update_stable vstate_wf_imp)
    qed (simp)
    ultimately show ?thesis by blast
  qed (simp)
qed


subsection \<open>Rule assignment\<close>

(*
| RuleLocalAssign: "\<lbrakk> self_framing_and_typed \<Delta> A; framed_by_exp A e \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> [A] LocalAssign x e [post_substitute_var_assert x e A]"
*)
(*
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x \<mapsto> VInt (edenot e s)), h) \<rbrakk> \<Longrightarrow> \<langle>Cassign x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
*)

definition sub_pre where
  "sub_pre x e P = { (Ag s, \<tau>, \<omega>) |s \<tau> \<omega>. (Ag (s(x \<mapsto> VInt (edenot e s))), \<tau>, \<omega>) \<in> P }"

proposition rule_assign:
  "CSL (sub_pre x e P) (Cassign x e) P"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> sub_pre x e P" "sep_algebra_class.stable \<omega>"
  then have r: "(Ag (s(x \<mapsto> VInt (edenot e s))), \<tau>, \<omega>) \<in> P"
    by (simp add: sub_pre_def)
  show "safe (Suc n) (Cassign x e) s \<tau> \<omega> P"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Cassign x e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 P"
      by (metis asm0(2) asm1(2) asm1(3) fst_eqD r red_assign_cases safe_skip snd_eqD)
  qed (auto simp add: no_aborts_def)
qed



subsection \<open>Rule Alloc\<close>

definition set_perm_and_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> preal \<Rightarrow> 'a val option \<Rightarrow> 'a virtual_state" where
  "set_perm_and_value \<phi> hl p v = Abs_virtual_state ((get_vm \<phi>)(hl := p), (get_vh \<phi>)(hl := v))"

(* Not true, needs pre... *)
lemma wf_set_perm:
  assumes "p > 0 \<Longrightarrow> v \<noteq> None"
  shows "wf_pre_virtual_state ((get_vm \<phi>)(hl := p), (get_vh \<phi>)(hl := v))"
  using assms gr_0_is_ppos vstate_wf_imp by fastforce

lemma update_perm_simps[simp]:
  assumes "p > 0 \<Longrightarrow> v \<noteq> None"
    shows "get_vh (set_perm_and_value \<phi> hl p v) = (get_vh \<phi>)(hl := v)"
      and "get_vm (set_perm_and_value \<phi> hl p v) = (get_vm \<phi>)(hl := p)"
  unfolding set_perm_and_value_def
  apply (metis Abs_virtual_state_inverse assms get_vh_def mem_Collect_eq snd_conv wf_set_perm)
  by (metis Abs_virtual_state_inverse assms fst_conv get_vm_def mem_Collect_eq wf_set_perm)

lemma stable_set_perm_and_value:
  assumes "p > 0 \<longleftrightarrow> v \<noteq> None"
      and "stable \<omega>"
    shows "stable (set_perm_and_value \<omega> hl p v)"
proof (rule stable_virtual_stateI)
  show "\<And>hla. get_vh (set_perm_and_value \<omega> hl p v) hla \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm (set_perm_and_value \<omega> hl p v) hla"
    by (metis assms(1) assms(2) fun_upd_apply stable_virtual_state_def update_perm_simps(1) update_perm_simps(2))
qed

lemma plus_virtual_stateI:
  assumes "Some (get_vh \<phi>) = get_vh a \<oplus> get_vh b"
      and "Some (get_vm \<phi>) = get_vm a \<oplus> get_vm b"
    shows "Some \<phi> = a \<oplus> b"
  using assms(1) assms(2) vstate_add_iff by blast



lemma alloc_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "get_vh \<omega>f l = None"
      and "p > 0 \<Longrightarrow> v \<noteq> None"
    shows "Some (set_perm_and_value \<omega>' l p v) = set_perm_and_value \<omega> l p v \<oplus> \<omega>f"
proof (rule plus_virtual_stateI)
  show "Some (get_vh (set_perm_and_value \<omega>' l p v)) = get_vh (set_perm_and_value \<omega> l p v) \<oplus> get_vh \<omega>f"
    by (smt (verit, ccfv_threshold) assms commutative fun_upd_apply plus_funE plus_funI plus_option.simps(1) update_perm_simps(1) vstate_add_iff)
  show "Some (get_vm (set_perm_and_value \<omega>' l p v)) = get_vm (set_perm_and_value \<omega> l p v) \<oplus> get_vm \<omega>f"
    apply (rule plus_funI)
    by (smt (verit, ccfv_threshold) SepAlgebra.plus_preal_def add.right_neutral assms fun_upd_apply get_vm_additive not_gr_0 plus_funE update_perm_simps(2) vstate_wf_imp)
qed


proposition rule_alloc:
  assumes "r \<notin> fvE e"
  shows "CSL UNIV (Calloc r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n :: nat
  fix s :: stack
  fix \<tau> :: "int ag_trace"
  fix \<omega> :: "int virtual_state"
  assume "sep_algebra_class.stable \<omega>"


  show "safe (Suc n) (Calloc r e) s \<tau> \<omega> (full_ownership_with_val r e)"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Calloc r e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"
    proof (rule red_alloc_cases)
      fix sa h l
      assume asm1: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "(l, field_val) \<notin> dom h"
        "\<sigma>' = (sa(r \<mapsto> VRef (Address l)), h((l, field_val) \<mapsto> VInt (edenot e sa)))"
      then have r: "Some (set_perm_and_value \<omega>0' (l, field_val) 1 (Some (VInt (edenot e s))))
  = set_perm_and_value \<omega> (l, field_val) 1 (Some (VInt (edenot e s))) \<oplus> \<omega>f"
        using alloc_helper
        by (smt (verit, ccfv_SIG) EquiViper.add_masks_def Pair_inject asm0(1) asm0(2) commutative dom_eqD option.discI padd_pos pperm_pnone_pgt stable_virtual_state_def vstate_add_iff vstate_wf_imp)
      let ?\<omega>1 = "set_perm_and_value \<omega> (l, field_val) 1 (Some (VInt (edenot e s)))"
      let ?\<omega>1' = "set_perm_and_value \<omega>0' (l, field_val) 1 (Some (VInt (edenot e s)))"

      have "sep_algebra_class.stable ?\<omega>1"
        by (simp add: \<open>sep_algebra_class.stable \<omega>\<close> pperm_pnone_pgt stable_set_perm_and_value)
      moreover have "binary_mask ?\<omega>1'"
      proof (rule binary_maskI)
        fix la show "get_vm (set_perm_and_value \<omega>0' (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) la = PosReal.pnone \<or>
          get_vm (set_perm_and_value \<omega>0' (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) la = PosReal.pwrite"
          by (metis asm0(3) binary_mask_def fun_upd_apply option.discI update_perm_simps(2))
      qed
      moreover have "\<sigma>' = concretize (fst \<sigma>') ?\<omega>1'"
        using asm1(1) asm1(4) by auto
      moreover have "(Ag (fst \<sigma>'), \<tau>, ?\<omega>1) \<in> full_ownership_with_val r e"
      proof (rule in_full_ownership_with_val_alt[of "(fst \<sigma>')" r l])
        show "fst \<sigma>' r = Some (VRef (Address l))"
          by (simp add: asm1(4))
        show "get_vm (set_perm_and_value \<omega> (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) (l, field_val) = PosReal.pwrite"
          by auto
        have "edenot e (fst \<sigma>') = edenot e s"
          using asm1(1) asm1(4) assms by auto
        then show "get_vh (set_perm_and_value \<omega> (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) (l, field_val)
          = Some (VInt (edenot e (fst \<sigma>')))"
          by simp
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"
        using r asm1(2)
        by (metis safe_skip snd_conv)
    qed
  qed (auto)
qed



subsection \<open>Rule free\<close>

definition erase_perm_and_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a virtual_state" where
  "erase_perm_and_value \<phi> hl = Abs_virtual_state ((get_vm \<phi>)(hl := 0), (get_vh \<phi>)(hl := None))"

lemma erase_perm_and_value_simps[simp]:
  "get_vm (erase_perm_and_value \<phi> hl) = (get_vm \<phi>)(hl := 0)"
  "get_vh (erase_perm_and_value \<phi> hl) = (get_vh \<phi>)(hl := None)"
proof -
  show "get_vm (erase_perm_and_value \<phi> hl) = (get_vm \<phi>)(hl := PosReal.pnone)"
    by (metis erase_perm_and_value_def pperm_pgt_pnone set_perm_and_value_def update_perm_simps(2))
  show "get_vh (erase_perm_and_value \<phi> hl) = (get_vh \<phi>)(hl := None)"
    by (metis erase_perm_and_value_def pperm_pgt_pnone set_perm_and_value_def update_perm_simps(1))
qed


lemma free_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "sep_algebra_class.stable \<omega>f"
      and "get_vm \<omega> hl = 1"
    shows "Some (erase_perm_and_value \<omega>' hl) = erase_perm_and_value \<omega> hl \<oplus> \<omega>f"
proof -
  have asm: "get_vm \<omega>' hl \<le> 1"
    sorry (* TODO: Need assumption in def of virtual_state *)
  then have "get_vm \<omega>' hl = 1"
    by (simp add: EquiViper.add_masks_def antisym assms(1) assms(3) get_vm_additive pos_perm_class.sum_larger)
  then have "get_vm \<omega>f hl = 0"
    by (smt (verit, ccfv_threshold) EquiViper.add_masks_def PosReal.ppos.rep_eq assms(1) assms(3) get_vm_additive gr_0_is_ppos not_gr_0 plus_preal.rep_eq)
  then have "get_vh \<omega>f hl = None"
    using assms(2) pperm_pgt_pnone stable_virtual_state_def by blast
  show ?thesis
  proof (rule plus_virtual_stateI)
    show "Some (get_vh (erase_perm_and_value \<omega>' hl)) = get_vh (erase_perm_and_value \<omega> hl) \<oplus> get_vh \<omega>f"
      by (metis \<open>get_vh \<omega>f hl = None\<close> alloc_helper assms(1) erase_perm_and_value_def pperm_pgt_pnone set_perm_and_value_def vstate_add_iff)
    show "Some (get_vm (erase_perm_and_value \<omega>' hl)) = get_vm (erase_perm_and_value \<omega> hl) \<oplus> get_vm \<omega>f"
      by (metis \<open>get_vh \<omega>f hl = None\<close> alloc_helper assms(1) erase_perm_and_value_def pperm_pgt_pnone set_perm_and_value_def vstate_add_iff)
  qed
qed

lemma stable_erase_perm_value:
  assumes "sep_algebra_class.stable \<omega>"
  shows "sep_algebra_class.stable (erase_perm_and_value \<omega> hl)"
  by (metis assms erase_perm_and_value_def order_less_irrefl set_perm_and_value_def stable_set_perm_and_value)

lemma binary_mask_erase_perm_value:
  assumes "binary_mask \<omega>"
  shows "binary_mask (erase_perm_and_value \<omega> hl)"
  by (metis assms binary_mask_def erase_perm_and_value_simps(1) fun_upd_def)


proposition rule_free:
  "CSL (full_ownership r) (Cfree r) UNIV"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> full_ownership r" "sep_algebra_class.stable \<omega>"
  then obtain l where r: "s r = Some (VRef (Address l)) \<and> get_vm \<omega> (l, field_val) = 1"
    using full_ownership_def by fastforce
  show "safe (Suc n) (Cfree r) s \<tau> \<omega> UNIV"
  proof (rule safeI_alt)
    show "accesses (Cfree r) s \<subseteq> read_dom \<omega>"
      by (simp add: in_read_dom_write_dom(1) r)
    show "writes (Cfree r) s \<subseteq> write_dom \<omega>"
      by (simp add: in_read_dom_write_dom(2) r)
    fix \<omega>0' \<omega>f
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    show "aborts (Cfree r) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts (Cfree r) (concretize s \<omega>0')"
      then show False
      proof (rule aborts_free_elim)
        show "fst (concretize s \<omega>0') r = Some (VRef Null) \<Longrightarrow> False"
          by (simp add: r)
        fix hl assume "fst (concretize s \<omega>0') r = Some (VRef (Address hl))"
        then have "hl = l"
          by (simp add: r)
        moreover have "get_vm \<omega>0' (l, field_val) \<ge> 1"
          by (simp add: EquiViper.add_masks_def asm1(2) get_vm_additive pos_perm_class.sum_larger r)
        moreover assume "(hl, field_val) \<notin> dom (snd (concretize s \<omega>0'))"
        ultimately show False
          by (metis domIff linorder_not_less pperm_pnone_pgt sndI vstate_wf_imp zero_neq_one)
      qed
    qed
    fix C' \<sigma>'
    assume "\<langle>Cfree r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 UNIV"
    proof (rule red_free_cases)
      fix sa h l'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa, h((l', field_val) := None))"
        "sa r = Some (VRef (Address l'))"
      let ?\<omega>1 = "erase_perm_and_value \<omega> (l', field_val)"
      let ?\<omega>1' = "erase_perm_and_value \<omega>0' (l', field_val)"
      have "snd \<sigma>' = get_vh ?\<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> ?\<omega>1 UNIV"
        using asm2(1) asm2(2) asm2(3) by auto
      moreover have "Some ?\<omega>1' = ?\<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable ?\<omega>1"
        using asm0(2) asm1(1) asm1(2) asm2(1) asm2(4) free_helper r stable_erase_perm_value by fastforce
      moreover have "binary_mask ?\<omega>1'"
        by (simp add: asm1(3) binary_mask_erase_perm_value)        
      ultimately show
        "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 UNIV"
        by blast
    qed
  qed (simp_all)
qed


subsection \<open>Read\<close>

lemma read_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "get_vh \<omega> l = Some v"
    shows "get_vh \<omega>' l = Some v"
  by (metis assms(1) assms(2) commutative greater_equiv read_field.elims read_field_mono)



definition read_result where
  "read_result x r = { \<omega> |\<omega> l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_store \<omega> x = get_h \<omega> (l, field_val) }"

definition read_perm where
  "read_perm r = { \<omega> |\<omega> l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0 \<and> get_h \<omega> (l, field_val) = Some (VInt v)}"

proposition rule_read:
  assumes "x \<notin> fvA A"
      and "A \<subseteq> read_perm r"
    shows "CSL A (Cread x r) (A \<inter> read_result x r)"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> A" "sep_algebra_class.stable \<omega>"
  then obtain l v where lv_def: "s r = Some (VRef (Address l))" "get_vm \<omega> (l, field_val) > 0" "get_vh \<omega> (l, field_val) = Some (VInt v)"
    using assms(2) unfolding read_perm_def by force
  show "safe (Suc n) (Cread x r) s \<tau> \<omega> (A \<inter> read_result x r)"
  proof (rule safeI_alt)
    show "accesses (Cread x r) s \<subseteq> read_dom \<omega>"
      by (simp add: lv_def(1) lv_def(2) read_dom_def)
    fix \<omega>0' \<omega>f
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    then have "get_vh \<omega>0' (l, field_val) = Some (VInt v)"
      using lv_def(3) read_helper by blast
    then show "aborts (Cread x r) (concretize s \<omega>0') \<Longrightarrow> False"
      using lv_def(1) by auto
    have "(Ag (s(x := Some (VInt v))), \<tau>, \<omega>) \<in> A"
      by (meson agrees_search(4) asm0(1) assms(1) fvA_agrees)

    fix C' \<sigma>'
    assume "\<langle>Cread x r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (A \<inter> read_result x r)"
    proof (rule red_read_cases)
      fix sa h l' v'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa(x \<mapsto> VInt v'), h)" "sa r = Some (VRef (Address l'))"
      "h (l', field_val) = Some (VInt v')"
      then have "l = l' \<and> v = v'"
        using \<open>get_vh \<omega>0' (l, field_val) = Some (VInt v)\<close> lv_def(1) by auto
      moreover have "(Ag (s(x := Some (VInt v))), \<tau>, \<omega>) \<in> read_result x r"
        unfolding read_result_def
        using \<open>(Ag (s(x \<mapsto> VInt v)), \<tau>, \<omega>) \<in> A\<close> assms(2) get_simps_unfolded(1) lv_def(1) lv_def(3) unfolding read_perm_def  by fastforce
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 (A \<inter> read_result x r)"
        using \<open>(Ag (s(x \<mapsto> VInt v)), \<tau>, \<omega>) \<in> A\<close> asm0(2) asm1(2) asm1(3) asm2(1) asm2(2) asm2(3) by auto
    qed
  qed (simp_all)
qed


section \<open>Actual logic\<close>

inductive CSL_syn :: "int equi_state set \<Rightarrow> cmd \<Rightarrow> int equi_state set \<Rightarrow> bool" 
  ("\<turnstile>CSL [_] _ [_]" [51,0,0] 81)
  where
  RuleSkip: "\<turnstile>CSL [P] Cskip [P]"
| RuleFrame: "\<lbrakk> \<turnstile>CSL [P] C [Q]; disjoint (fvA R) (wrC C); self_framing P; self_framing R\<rbrakk> \<Longrightarrow> \<turnstile>CSL [P \<otimes> R] C [Q \<otimes> R]"
| RulePar: "\<lbrakk> disjoint (fvC C1 \<union> fvA Q1) (wrC C2); disjoint (fvC C2 \<union> fvA Q2) (wrC C1); self_framing P1; self_framing P2;
    \<turnstile>CSL [P1] C1 [Q1]; \<turnstile>CSL [P2] C2 [Q2] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P1 \<otimes> P2] C1 || C2 [Q1 \<otimes> Q2]"
| RuleSeq: "\<lbrakk> \<turnstile>CSL [P] C1 [Q]; \<turnstile>CSL [Q] C2 [R] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P] Cseq C1 C2 [R]"
| RuleCons: "\<lbrakk>\<turnstile>CSL [P] C [Q]; P' \<subseteq> P; Q \<subseteq> Q'\<rbrakk> \<Longrightarrow> \<turnstile>CSL [P'] C [Q']"
| RuleIf: "\<lbrakk> \<turnstile>CSL [P \<inter> assertify_bexp b] C1 [Q]; \<turnstile>CSL [P \<inter> assertify_bexp (Bnot b)] C2 [Q]\<rbrakk> \<Longrightarrow> \<turnstile>CSL [P] Cif b C1 C2 [Q]"
| RuleWhile: "\<lbrakk> \<turnstile>CSL [I \<inter> (assertify_bexp b)] C [I]; self_framing I \<rbrakk> \<Longrightarrow> \<turnstile>CSL [I] (Cwhile b C) [I \<inter> (assertify_bexp (Bnot b))]"
| RuleWrite: "\<turnstile>CSL [full_ownership r] Cwrite r e [full_ownership_with_val r e]"
| RuleAssign: "\<turnstile>CSL [sub_pre x e P] Cassign x e [P]"
| RuleAlloc: "r \<notin> fvE e \<Longrightarrow> \<turnstile>CSL [UNIV] Calloc r e [full_ownership_with_val r e]"
| RuleFree: "\<turnstile>CSL [full_ownership r] Cfree r [UNIV]"
| RuleRead: "\<lbrakk> x \<notin> fvA A; A \<subseteq> read_perm r\<rbrakk> \<Longrightarrow> \<turnstile>CSL [A] Cread x r [A \<inter> read_result x r]"


theorem CSL_sound:
  assumes "\<turnstile>CSL [P] C [Q]"
  shows "CSL P C Q"
  using assms
  by (induct rule: CSL_syn.induct)
    (simp_all add: rule_skip frame_rule rule_par rule_seq rule_conseq rule_if rule_while
      rule_write rule_assign rule_alloc rule_free rule_read)


subsection \<open>Adequacy\<close>

inductive n_steps where
  NoStep: "n_steps C \<sigma> C \<sigma>"
| OneStep: "\<lbrakk> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C'', \<sigma>''\<rangle>; n_steps C'' \<sigma>'' C' \<sigma>' \<rbrakk> \<Longrightarrow>  n_steps C \<sigma> C' \<sigma>'"


definition assertify_store_assertion where
  "assertify_store_assertion P = { (Ag s, \<tau>, h) |s \<tau> h. P s }"

lemma in_assertify_equiv:
  "(Ag s, \<tau>, \<omega>) \<in> assertify_store_assertion P \<longleftrightarrow> P s"
  by (simp add: assertify_store_assertion_def)

lemma uu_simps[simp]:
  "get_vh uu = empty_heap"
  "get_vm uu = zero_mask"
  unfolding uu_def
proof -
  have r: "wf_pre_virtual_state uuu"
    by (metis uuu_def wf_uuu)
  then show "get_vh (Abs_virtual_state uuu) = empty_heap"
    unfolding uuu_def
    by (smt (verit) Abs_virtual_state_inverse get_vh_def mem_Collect_eq snd_conv)
  show "get_vm (Abs_virtual_state uuu) = zero_mask"
    by (metis Abs_virtual_state_inverse fst_conv get_vm_def mem_Collect_eq r uuu_def)
qed


lemma stable_uu:
  "sep_algebra_class.stable uu"
proof (rule stable_virtual_stateI)
  show "\<And>hl. get_vh uu hl \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm uu hl"
    by (simp add: empty_heap_def)
qed


lemma uu_neutral:
  "Some \<omega> = \<omega> \<oplus> uu"
proof (rule plus_virtual_stateI)
  show "Some (get_vh \<omega>) = get_vh \<omega> \<oplus> get_vh uu"
    by (simp add: empty_heap_identity)
  show "Some (get_vm \<omega>) = get_vm \<omega> \<oplus> get_vm uu"
    using zero_mask_identity by auto
qed



lemma get_wf_easy:
  assumes "wf_pre_virtual_state \<phi>"
  shows "get_vm (Abs_virtual_state \<phi>) = fst \<phi> \<and> get_vh (Abs_virtual_state \<phi>) = snd \<phi>"
  by (simp add: Abs_virtual_state_inverse assms get_vh_def get_vm_def)

definition mk_virtual_state where
  "mk_virtual_state h = Abs_virtual_state (\<lambda>l. if l \<in> dom h then 1 else 0, h)"

lemma mk_virtual_state_simps[simp]:
  "get_vm (mk_virtual_state h) = (\<lambda>l. if l \<in> dom h then 1 else 0)"
  "get_vh (mk_virtual_state h) = h"
proof -
  have "wf_pre_virtual_state (\<lambda>l. if l \<in> dom h then 1 else 0, h)"
    using gr_0_is_ppos by fastforce
  then show "get_vm (mk_virtual_state h) = (\<lambda>l. if l \<in> dom h then 1 else 0)"
    unfolding mk_virtual_state_def using get_wf_easy 
    by (metis fst_conv)
  show "get_vh (mk_virtual_state h) = h"
    by (metis \<open>wf_pre_virtual_state (\<lambda>l. if l \<in> dom h then PosReal.pwrite else PosReal.pnone, h)\<close> get_wf_easy mk_virtual_state_def snd_conv)
qed

lemma mk_virtual_state_charact[simp]:
  "sep_algebra_class.stable (mk_virtual_state h)"
  "binary_mask (mk_virtual_state h)"
  "concretize s (mk_virtual_state h) = (s, h)"
  apply (metis domIff mk_virtual_state_simps(1) mk_virtual_state_simps(2) not_gr_0 one_neq_zero stable_virtual_stateI)
  apply (simp add: binary_maskI)
  by simp


lemma safeE_no_frame:
  assumes "safe (Suc n) C s \<tau> \<omega> Q"
      and "binary_mask \<omega>"
      and "\<langle>C, concretize s \<omega>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    shows "\<exists>\<omega>1. sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1 \<and> snd \<sigma>' = get_vh \<omega>1 \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
proof -
  obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> uu \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
    using safeE(5)[OF assms(1), of uu \<omega> C' \<sigma>']
    using assms(2) assms(3) stable_uu uu_neutral by blast
  then show ?thesis
    by (metis pure_def stable_and_sum_pure_same uu_neutral)
qed

lemma binary_mask_and_stable_then_mk_virtual:
  assumes "sep_algebra_class.stable \<omega>"
      and "binary_mask \<omega>"
    shows "\<omega> = mk_virtual_state (get_vh \<omega>)"
proof (rule virtual_state_ext)
  show "get_vm \<omega> = get_vm (mk_virtual_state (get_vh \<omega>))"
  proof
    fix l show "get_vm \<omega> l = get_vm (mk_virtual_state (get_vh \<omega>)) l"
      by (metis assms(1) assms(2) binary_mask_def mk_virtual_state_charact(1) mk_virtual_state_simps(1) mk_virtual_state_simps(2) not_gr_0 stable_virtual_state_def vstate_wf_imp)
  qed
qed (simp)

lemma safeE_no_frame_alt:
  assumes "safe (Suc n) C s \<tau> (mk_virtual_state h) Q"
      and "\<langle>C, (s, h)\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    shows "\<exists>\<omega>1. sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1 \<and> snd \<sigma>' = get_vh \<omega>1 \<and> safe n C' (fst \<sigma>') \<tau> \<omega>1 Q"
  by (metis assms(1) assms(2) mk_virtual_state_charact(2) mk_virtual_state_simps(2) safeE_no_frame)



lemma safe_n_steps:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "s = fst \<sigma>"
      and "get_vh \<omega> = snd \<sigma>"
      and "binary_mask \<omega>"
      and "sep_algebra_class.stable \<omega>"       
      and "\<And>n. safe n C s \<tau> \<omega> (assertify_store_assertion Q)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q (fst \<sigma>'))"
  using assms
proof (induct arbitrary: s \<omega> rule: n_steps.induct)
  case (NoStep C \<sigma>)
  then have r: "safe (Suc 0) C s \<tau> \<omega> (assertify_store_assertion Q)"
    by simp
  then show ?case
    using safeE(1)[OF r] no_abortsE[OF safeE(4)[OF r], of \<omega> uu]
    using NoStep.prems(1) NoStep.prems(2) stable_uu uu_neutral
    using NoStep.prems(3) NoStep.prems(4)
    by (metis in_assertify_equiv surjective_pairing)
next
  case (OneStep C \<sigma> C'' \<sigma>'' C' \<sigma>')
  show "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q (fst \<sigma>'))"
  proof (rule OneStep(3)[of "fst \<sigma>''" "mk_virtual_state (snd \<sigma>'')"])
    fix n
    obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> uu \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1'"
      "snd \<sigma>'' = get_vh \<omega>1' \<and> safe n C'' (fst \<sigma>'') \<tau> \<omega>1 (assertify_store_assertion Q)"
      using safeE(5)[OF OneStep(8)[of "Suc n"], of uu \<omega> C'' \<sigma>'']
      using OneStep.hyps(1) OneStep.prems(1) OneStep.prems(2) OneStep.prems(3) stable_uu uu_neutral by auto
    then show "safe n C'' (fst \<sigma>'') \<tau> (mk_virtual_state (snd \<sigma>'')) (assertify_store_assertion Q)"
      by (metis binary_mask_and_stable_then_mk_virtual pure_def stable_and_sum_pure_same uu_neutral)
  qed (simp_all)
qed





theorem adequacy:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "\<turnstile>CSL [assertify_store_assertion P] C [assertify_store_assertion Q]"
      and "P (fst \<sigma>)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q (fst \<sigma>'))"
proof (rule safe_n_steps[OF assms(1), where ?Q = Q])
  fix n
  show "safe n C (fst \<sigma>) (Ag (Map.empty)) (mk_virtual_state (snd \<sigma>)) (assertify_store_assertion Q)"
    by (metis CSL_E CSL_sound assms(2) assms(3) in_assertify_equiv mk_virtual_state_charact(1))
qed (simp_all)

end