theory CSL_IDF
  imports ParImp ViperCommon.SepAlgebra ViperCommon.SepLogic "../vipersemabstract/Instantiation"
begin

definition binary_mask where
  "binary_mask \<omega> \<longleftrightarrow> (\<forall>l. get_m \<omega> l = 0 \<or> get_m \<omega> l = 1)"

definition concretize :: "int equi_state \<Rightarrow> state" where                                              
  "concretize \<omega> = (get_store \<omega>, get_h \<omega>)"

definition read_dom where 
  "read_dom \<omega> = { l. get_m \<omega> (l, field_val) > 0 }"

definition write_dom where 
  "write_dom \<omega> = { l. get_m \<omega> (l, field_val) = 1 }"

definition no_aborts where
  "no_aborts C \<omega>0 \<longleftrightarrow> (\<forall>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<longrightarrow> \<not> aborts C (concretize \<omega>0'))"

lemma no_abortsI[intro]:
  assumes "\<And>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<Longrightarrow> \<not> aborts C (concretize \<omega>0')"
  shows "no_aborts C \<omega>0"
  using assms no_aborts_def by blast

(*
inductive
  aborts :: "cmd \<Rightarrow> state \<Rightarrow> bool"
where
  aborts_Seq[intro]:   "aborts C1 \<sigma> \<Longrightarrow> aborts (Cseq C1 C2) \<sigma>" 
| aborts_Par1[intro]:  "aborts C1 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>" 
| aborts_Par2[intro]:  "aborts C2 \<sigma> \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"

| aborts_Race1[intro]:  "\<not> disjoint (accesses C1 (fst \<sigma>)) (writes C2 (fst \<sigma>)) \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"
| aborts_Race2[intro]:  "\<not> disjoint (writes C1 (fst \<sigma>)) (accesses C2 (fst \<sigma>)) \<Longrightarrow> aborts (Cpar C1 C2) \<sigma>"

| aborts_Read[intro]:  "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cread x r) \<sigma>"
| aborts_Write[intro]: "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cwrite r E) \<sigma>"
| aborts_Free[intro]:  "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cdispose r) \<sigma>"

| aborts_ReadNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cread x r) \<sigma>"
| aborts_WriteNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cwrite r e) \<sigma>"
| aborts_FreeNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cdispose r) \<sigma>"
*)

(* Probably should be stable somewhere *)
 primrec
  safe :: "nat \<Rightarrow> cmd \<Rightarrow> int equi_state \<Rightarrow> int equi_state set \<Rightarrow> bool"
where
  "safe 0 C \<omega> Q \<longleftrightarrow> True"
| "safe (Suc n) C \<omega>0 Q \<longleftrightarrow>
  (C = Cskip \<longrightarrow> \<omega>0 \<in> Q)
  \<and> accesses C (get_store \<omega>0) \<subseteq> read_dom \<omega>0
  \<and> writes C (get_store \<omega>0) \<subseteq> write_dom \<omega>0
  \<and> no_aborts C \<omega>0
  \<and> (\<forall>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and>
  (\<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q))"

lemma safeI:
  assumes "C = Cskip \<Longrightarrow> \<omega>0 \<in> Q"
      and "accesses C (get_store \<omega>0) \<subseteq> read_dom \<omega>0"
      and "writes C (get_store \<omega>0) \<subseteq> write_dom \<omega>0"
      and "no_aborts C \<omega>0"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and>
  (\<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q)"
    shows "safe (Suc n) C \<omega>0 Q"
  using assms safe.simps(1) by auto


lemma safeI_alt:
  assumes "C = Cskip \<Longrightarrow> \<omega>0 \<in> Q"
      and "accesses C (get_store \<omega>0) \<subseteq> read_dom \<omega>0"
      and "writes C (get_store \<omega>0) \<subseteq> write_dom \<omega>0"
      and "\<And>\<omega>0' \<omega>f. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<Longrightarrow> aborts C (concretize \<omega>0') \<Longrightarrow> False"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q)"
    shows "safe (Suc n) C \<omega>0 Q"
  using assms safe.simps(1) 
  by fastforce

lemma safeE:
  assumes "safe (Suc n) C \<omega>0 Q"
  shows "C = Cskip \<Longrightarrow> \<omega>0 \<in> Q"
      and "accesses C (get_store \<omega>0) \<subseteq> read_dom \<omega>0"
      and "writes C (get_store \<omega>0) \<subseteq> write_dom \<omega>0"
      and "no_aborts C \<omega>0"
      and "sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> (\<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q)"
  using assms safe.simps(1) apply simp_all
  by (metis prod.collapse)


definition CSL_judgment where
  "CSL_judgment P C Q \<longleftrightarrow> (\<forall>n \<omega>. \<omega> \<in> P \<longrightarrow> safe n C \<omega> Q)"

lemma CSL_I:
  assumes "\<And>n \<omega>. \<omega> \<in> P \<Longrightarrow> safe n C \<omega> Q"
  shows "CSL_judgment P C Q"
  by (simp add: CSL_judgment_def assms)

lemma CSL_E:
  assumes "CSL_judgment P C Q"
      and "\<omega> \<in> P"
    shows "safe n C \<omega> Q"
  using CSL_judgment_def assms(1) assms(2) by blast


lemma safety_mono:
  assumes "safe n C \<omega> Q"
      and "m \<le> n"
    shows "safe m C \<omega> Q"
  using assms
proof (induct m arbitrary: C n \<omega>)
  case (Suc m)
  then obtain k where "n = Suc k"
    using Suc_le_D by presburger
  then show ?case using safeI[of C \<omega> Q] safeE
    by (smt (verit, ccfv_threshold) Suc.hyps Suc.prems(1) Suc.prems(2) Suc_le_mono)
qed (simp)

(* Need to define the fvA Q... *)

lemma no_aborts_agrees:
  assumes "no_aborts C \<omega>"
      and "agrees (fvC C) (get_store \<omega>) (get_store \<omega>')"
      and "get_state \<omega> = get_state \<omega>'"
    shows "no_aborts C \<omega>'"
  sorry

definition fvA where
  "fvA Q = undefined Q"

lemma fvA_agrees:
  assumes "agrees (fvA Q) (get_store \<omega>) (get_store \<omega>')"
      and "get_state \<omega> = get_state \<omega>'"
    shows "\<omega> \<in> Q \<longleftrightarrow> \<omega>' \<in> Q"
  sorry

lemma safe_agrees:
  assumes "safe n C \<omega> Q"
      and "agrees (fvC C \<union> fvA Q) (get_store \<omega>) (get_store \<omega>')"
      and "get_state \<omega> = get_state \<omega>'"
    shows "safe n C \<omega>' Q"
  using assms
proof (induct n arbitrary: C \<omega> \<omega>')
  case (Suc n)
  show ?case
  proof (rule safeI)
    have "C = Cskip \<Longrightarrow> \<omega> \<in> Q"
      using Suc.prems(1) safe.simps(2) by blast
    then show "C = Cskip \<Longrightarrow> \<omega>' \<in> Q"
      using Suc.prems(2) Suc.prems(3) agrees_simps(4) fvA_agrees by blast
    show "accesses C (get_store \<omega>') \<subseteq> read_dom \<omega>'"
      by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) accesses_agrees agrees_simps(4) read_dom_def safeE(2))
    show "writes C (get_store \<omega>') \<subseteq> write_dom \<omega>'"
      by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) agrees_simps(4) safeE(3) write_dom_def writes_agrees)
    show "no_aborts C \<omega>'"
      using Suc.prems(1) Suc.prems(2) Suc.prems(3) agrees_simps(4) no_aborts_agrees safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> \<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"

    show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q"
      sorry
  qed
qed (simp)

subsection Skip

lemma safe_skip[intro!]:
  assumes "\<omega> \<in> Q"
  shows "safe n Cskip \<omega> Q"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "no_aborts Cskip \<omega>"
      by (simp add: no_abortsI)
    show "Cskip = Cskip \<Longrightarrow> \<omega> \<in> Q"
      by (simp add: assms)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume "Some \<omega>0' = \<omega> \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> \<langle>Cskip, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 Q"
      using \<open>Some \<omega>0' = \<omega> \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> \<langle>Cskip, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>\<close> by auto
  qed (simp_all)
qed (simp)

proposition rule_skip:
  "CSL_judgment P Cskip P"
  by (simp add: CSL_judgment_def safe_skip)


subsection \<open>Frame rule\<close>

lemma read_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "read_dom \<omega> \<subseteq> read_dom \<omega>'"
  sorry

lemma write_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "write_dom \<omega> \<subseteq> write_dom \<omega>'"
  sorry

lemma no_aborts_mono:
  assumes "no_aborts C \<omega>"
      and "\<omega>' \<succeq> \<omega>"
    shows "no_aborts C \<omega>'"
  sorry

lemma frame_safe:
  assumes "safe n C \<omega> Q"
      and "fvA R \<inter> wrC C = {}"
      and "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "\<omega>f \<in> R"
      and "sep_algebra_class.stable \<omega>f"
    shows "safe n C \<omega>' (Q \<otimes> R)"
  using assms
proof (induct n arbitrary: C \<omega> \<omega>' \<omega>f)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> \<omega>' \<in> Q \<otimes> R"
      by (metis Suc.prems(1) Suc.prems(3) Suc.prems(4) safeE(1) x_elem_set_product)
    show "accesses C (get_store \<omega>') \<subseteq> read_dom \<omega>'"
      by (metis (no_types, lifting) Suc.prems(1) Suc.prems(3) Suc.prems(4) dual_order.trans full_add_charact(1) in_set_sum is_in_set_sum read_dom_mono safeE(2) singletonD)
    show "writes C (get_store \<omega>') \<subseteq> write_dom \<omega>'"
      by (metis (no_types, lifting) Suc.prems(1) Suc.prems(3) full_add_charact(1) greater_def inf.absorb_iff2 inf.coboundedI1 safeE(3) write_dom_mono)
    show "no_aborts C \<omega>'"
      by (meson Suc.prems(1) Suc.prems(3) greater_def no_aborts_mono safeE(4))
    fix \<omega>0' \<omega>f' C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f'" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f' \<and> binary_mask \<omega>0' \<and> \<langle>C, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>f'' where "Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asso2 option.collapse)
    then have "Some \<omega>0' = \<omega> \<oplus> \<omega>f''"
      using asm0 Suc.prems(3) asso1 by force
    then obtain \<omega>1'' \<omega>1' where "Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1'" "safe n C' \<omega>1'' Q"
      using safeE(5)[OF Suc(2), of \<omega>0' \<omega>f'' C' \<sigma>'] asm0 
      by (meson Suc.prems(1) Suc.prems(5) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> safeE(5) stable_sum)
    then obtain \<omega>1 where "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
      by (metis (no_types, opaque_lifting) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> asso3 option.collapse)
    moreover have "safe n C' \<omega>1 (Q \<otimes> R)"
      using \<open>safe n C' \<omega>1'' Q\<close>
    proof (rule Suc(1)[of C' \<omega>1'' \<omega>1 \<omega>f])
      show "fvA R \<inter> wrC C' = {}"
        by (meson Suc.prems(2) asm0 disjoint_iff red_properties subset_iff)
      show "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
        using calculation by auto
    qed (simp_all add: Suc.prems)
    ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f' \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe n C' \<omega>1 (Q \<otimes> R)"
      by (metis (no_types, lifting) \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1'\<close> \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> asso1)
  qed
qed (simp)

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

proposition frame_rule:
  assumes "CSL_judgment P C Q"
      and "disjoint (fvA R) (wrC C)"
      and "self_framing R"
      and "TypedEqui.wf_assertion \<Delta> P"
    shows "CSL_judgment (P \<otimes> R) C (Q \<otimes> R)"
proof (rule CSL_I)
  fix n \<omega> assume "\<omega> \<in> P \<otimes> R"
  then obtain \<omega>p \<omega>r where r: "Some \<omega> = \<omega>p \<oplus> \<omega>r" "\<omega>p \<in> P" "\<omega>r \<in> R" "sep_algebra_class.stable \<omega>r"
    using assms(3) assms(4) self_framing_wf_split by blast
  then have "safe n C \<omega>p Q"
    using CSL_E assms(1) by blast
  then show "safe n C \<omega> (Q \<otimes> R)"
    by (meson \<open>Some \<omega> = \<omega>p \<oplus> \<omega>r\<close> \<open>\<omega>r \<in> R\<close> assms(2) disjoint_def frame_safe r)
qed


subsection \<open>Rule FieldAssign\<close>

abbreviation update_heap_val where
  "update_heap_val \<omega> l v \<equiv> set_state \<omega> (set_value (get_state \<omega>) l v)"

lemma compatibleI:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_state a ## get_state b"
    shows "a ## b"
  sorry

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


lemma write_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "sep_algebra_class.stable \<omega>f"
      and "get_m \<omega> l = 1"
    shows "Some (update_heap_val \<omega>' l v) = update_heap_val \<omega> l v \<oplus> \<omega>f"
proof -
  have "get_m \<omega>' l = get_m \<omega> l + get_m \<omega>f l"
    by (meson assms(1) get_m_additive)
  moreover have "get_m \<omega>' l \<le> 1" sorry
  ultimately have "get_m \<omega>f l = 0"
    by (metis PosReal.padd_cancellative add.commute add.right_neutral assms(3) nle_le pos_perm_class.sum_larger)
  moreover have "get_h \<omega>f l = None" (* TODO: Extract as lemma *)
  proof -
    have "sep_algebra_class.stable (get_state \<omega>f)"
      using stable_prod_def
      by (metis assms(2) get_state_def)
    then show ?thesis using stable_virtual_state_def[of "get_state \<omega>f"]
      using calculation pperm_pgt_pnone by blast
  qed
  show "Some (update_heap_val \<omega>' l v) = update_heap_val \<omega> l v \<oplus> \<omega>f"
  proof (rule sum_equi_statesI)
    show "get_store (update_heap_val \<omega>' l v) = get_store (update_heap_val \<omega> l v)"
      by (simp add: assms(1) full_add_charact(1))
    show "get_store (update_heap_val \<omega>' l v) = get_store \<omega>f"
      by (metis assms(1) commutative full_add_charact(1) get_store_set_state)
    show "get_trace (update_heap_val \<omega>' l v) = get_trace (update_heap_val \<omega> l v)"
      by (metis assms(1) get_trace_set_state greater_def greater_state_has_greater_parts(2))
    show "get_trace (update_heap_val \<omega>' l v) = get_trace \<omega>f"
      by (metis assms(1) get_trace_set_state greater_equiv greater_state_has_greater_parts(2))
    show "Some (get_state (update_heap_val \<omega>' l v)) = get_state (update_heap_val \<omega> l v) \<oplus> get_state \<omega>f"
    proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
      show "Some (Rep_virtual_state (get_state (update_heap_val \<omega>' l v))) =
    Rep_virtual_state (get_state (update_heap_val \<omega> l v)) \<oplus> Rep_virtual_state (get_state \<omega>f)"
      proof (rule plus_prodI)
        show "Some (fst (Rep_virtual_state (get_state (update_heap_val \<omega>' l v)))) =
    fst (Rep_virtual_state (get_state (update_heap_val \<omega> l v))) \<oplus> fst (Rep_virtual_state (get_state \<omega>f))"
          by (metis assms(1) get_state_set_state get_vm_additive get_vm_def set_value_charact(1) state_add_iff)
        show "Some (snd (Rep_virtual_state (get_state (update_heap_val \<omega>' l v)))) =
    snd (Rep_virtual_state (get_state (update_heap_val \<omega> l v))) \<oplus> snd (Rep_virtual_state (get_state \<omega>f))"
        proof (rule plus_funI)
          fix la show "Some (snd (Rep_virtual_state (get_state (update_heap_val \<omega>' l v))) la) =
          snd (Rep_virtual_state (get_state (update_heap_val \<omega> l v))) la \<oplus> snd (Rep_virtual_state (get_state \<omega>f)) la"
          proof (cases "l = la")
            case True
            then have "snd (Rep_virtual_state (get_state (update_heap_val \<omega>' l v))) la = Some v"
              by (metis fun_upd_apply get_state_set_state get_vh_def set_value_charact(2))
            moreover have "snd (Rep_virtual_state (get_state (update_heap_val \<omega> l v))) la = Some v"
              by (metis True fun_upd_apply get_state_set_state get_vh_def set_value_charact(2))
            ultimately show ?thesis
              by (metis True \<open>get_h \<omega>f l = None\<close> get_vh_def plus_option.simps(2))
          next
            case False
            then have "Some (snd (Rep_virtual_state (get_state (update_heap_val \<omega>' l v))) la)
  = Some (snd (Rep_virtual_state (get_state \<omega>')) la)"
              by (metis fun_upd_apply get_state_set_state get_vh_def set_value_charact(2))
            moreover have "snd (Rep_virtual_state (get_state (update_heap_val \<omega> l v))) la
  = snd (Rep_virtual_state (get_state \<omega>)) la"
              by (metis False fun_upd_apply get_state_set_state get_vh_def set_value_charact(2))
            ultimately show ?thesis
              by (metis assms(1) get_vh_def plus_funE state_add_iff vstate_add_iff)
          qed
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

lemma in_read_dom_write_dom:
  assumes "get_m \<omega> (l, field_val) = 1"
  shows "l \<in> read_dom \<omega>"
    and "l \<in> write_dom \<omega>"
  apply (metis CollectI assms not_gr_0 read_dom_def zero_neq_one)
  by (simp add: assms write_dom_def)


proposition rule_write:
  "CSL_judgment (full_ownership r) (Cwrite r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n \<omega> assume "\<omega> \<in> full_ownership r"
  then obtain l where asm0: "get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1"
    using full_ownership_def by blast
  show "safe n (Cwrite r e) \<omega> (full_ownership_with_val r e)"
  proof (cases n)
    case (Suc m)
    moreover have "safe (Suc m) (Cwrite r e) \<omega> (full_ownership_with_val r e)"
    proof (rule safeI_alt)
      have "accesses (Cwrite r e) (get_store \<omega>) = {l}" using get_address_simp asm0 by auto
      then show "accesses (Cwrite r e) (get_store \<omega>) \<subseteq> read_dom \<omega>" using asm0
        by (simp add: in_read_dom_write_dom(1))
      show "writes (Cwrite r e) (get_store \<omega>) \<subseteq> write_dom \<omega>"
        by (metis \<open>\<And>thesis. (\<And>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = PosReal.pwrite \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> get_address_simp in_read_dom_write_dom(2) singletonD subsetI writes.simps(4))
      
      fix \<omega>0' \<omega>f
      assume asm1: "Some \<omega>0' = \<omega> \<oplus> \<omega>f \<and> binary_mask \<omega>0'"
      then have "get_store \<omega>0' r = Some (VRef (Address l)) \<and> get_m \<omega>0' (l, field_val) = 1"
        by (metis asm0 binary_mask_def full_add_charact(1) get_m_additive padd_pos)
      then have "get_h \<omega>0' (l, field_val) \<noteq> None"
        by (simp add: pperm_pnone_pgt vstate_wf_imp)

      show "aborts (Cwrite r e) (concretize \<omega>0') \<Longrightarrow> False"
      proof -
        assume "aborts (Cwrite r e) (concretize \<omega>0')"
        then show False
          using aborts_write_elim
          using \<open>get_h \<omega>0' (l, field_val) \<noteq> None\<close> \<open>get_store \<omega>0' r = Some (VRef (Address l)) \<and> get_m \<omega>0' (l, field_val) = PosReal.pwrite\<close> concretize_def domIff fst_conv option.sel by auto
      qed
      fix C' \<sigma>'
      assume asm2: "sep_algebra_class.stable \<omega>f" "\<langle>Cwrite r e, concretize \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      let ?v = "VInt (edenot e (get_store \<omega>0'))"

      have "Some (update_heap_val \<omega>0' (l, field_val) ?v) = update_heap_val \<omega> (l, field_val) ?v \<oplus> \<omega>f"
        using asm0 asm1 asm2 write_helper by blast
      moreover have "\<sigma>' = concretize (update_heap_val \<omega>0' (l, field_val) ?v) \<and> C' = Cskip"
        using red_write_cases[OF asm2(2)]
        by (metis (no_types, lifting) \<open>get_store \<omega>0' r = Some (VRef (Address l)) \<and> get_m \<omega>0' (l, field_val) = PosReal.pwrite\<close> concretize_def get_state_set_state get_store_set_state old.prod.inject option.sel ref.sel set_value_charact(2) val.sel(4))
      moreover have "safe m Cskip (update_heap_val \<omega> (l, field_val) ?v) (full_ownership_with_val r e)"
      proof (rule safe_skip)
        show "update_heap_val \<omega> (l, field_val) (VInt (edenot e (get_store \<omega>0'))) \<in> full_ownership_with_val r e"
          by (simp add: asm0 asm1 full_add_charact(1) full_ownership_with_val_def)
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> binary_mask \<omega>1' \<and> \<sigma>' = concretize \<omega>1' \<and> safe m C' \<omega>1 (full_ownership_with_val r e)"
        by (metis asm1 binary_mask_def get_state_set_state set_value_charact(1))
    qed (simp)
    ultimately show ?thesis by blast
  qed (simp)
qed




end