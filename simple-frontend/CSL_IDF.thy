theory CSL_IDF
  imports ParImp ViperCommon.SepAlgebra ViperCommon.SepLogic ViperAbstract.Instantiation
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
  "no_aborts \<Delta> C s0 \<tau> \<omega>0 \<longleftrightarrow> (\<forall>\<omega>0' \<omega>f. TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0') \<and> sep_algebra_class.stable \<omega>0' \<and> sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<longrightarrow> \<not> aborts C (s0, get_vh \<omega>0'))"

lemma no_abortsI[intro]:
  assumes "\<And>\<omega>0' \<omega>f. TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0') \<Longrightarrow> sep_algebra_class.stable \<omega>0' \<Longrightarrow> sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<Longrightarrow> \<not> aborts C (s0, get_vh \<omega>0')"
  shows "no_aborts \<Delta> C s0 \<tau> \<omega>0"
  using assms no_aborts_def by blast

lemma no_abortsE:
  assumes "no_aborts \<Delta> C s0 \<tau> \<omega>0"
      and "sep_algebra_class.stable \<omega>0'"
      and "sep_algebra_class.stable \<omega>f"
      and "Some \<omega>0' = \<omega>0 \<oplus> \<omega>f"
      and "binary_mask \<omega>0'"
      and "TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0')"
    shows "\<not> aborts C (s0, get_vh \<omega>0')"
  using assms no_aborts_def by blast



(*
type_synonym 'v ag_store = "(var \<rightharpoonup> 'v) agreement"
type_synonym ('v, 'a) abs_state = "'v ag_store \<times> 'a"
('a val, ('a ag_trace \<times> 'a virtual_state)) abs_state"
*)

type_synonym 'a concrete_type_context = "('a val, (field_ident \<rightharpoonup> 'a val set)) abs_type_context"


 primrec
  safe :: "'a concrete_type_context \<Rightarrow> nat \<Rightarrow> cmd \<Rightarrow> 'a stack \<Rightarrow> 'a ag_trace \<Rightarrow> 'a virtual_state \<Rightarrow> 'a equi_state set \<Rightarrow> bool"
where
  "safe \<Delta> 0 C s \<tau> \<omega> Q \<longleftrightarrow> True"
| "safe \<Delta> (Suc n) C s0 \<tau> \<omega>0 Q \<longleftrightarrow>
  (C = Cskip \<longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q)
  \<and> accesses C s0 \<subseteq> read_dom \<omega>0
  \<and> writes C s0 \<subseteq> write_dom \<omega>0
  \<and> no_aborts \<Delta> C s0 \<tau> \<omega>0
  \<and> (\<forall>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0')
\<longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe \<Delta> n C' (fst \<sigma>') \<tau> \<omega>1 Q))"

lemma safeI:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts \<Delta> C s0 \<tau> \<omega>0"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow> TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0') \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe \<Delta> n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
    shows "safe \<Delta> (Suc n) C s0 \<tau> \<omega>0 Q"
  using assms safe.simps(1) by auto


lemma safeI_alt:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "\<And>\<omega>0' \<omega>f. TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0') \<Longrightarrow> sep_algebra_class.stable \<omega>0' \<Longrightarrow> sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow> aborts C (concretize s0 \<omega>0') \<Longrightarrow> False"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0') \<Longrightarrow> sep_algebra_class.stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> binary_mask \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe \<Delta> n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
    shows "safe \<Delta> (Suc n) C s0 \<tau> \<omega>0 Q"
  using assms safe.simps(1) 
  by fastforce

lemma safeE:
  assumes "safe \<Delta> (Suc n) C s0 \<tau> \<omega>0 Q"
  shows "C = Cskip \<Longrightarrow> (Ag s0, \<tau>, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts \<Delta> C s0 \<tau> \<omega>0"
      and "sep_algebra_class.stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> binary_mask \<omega>0' \<and> (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
  \<and> TypedEqui.typed \<Delta> (Ag s0, \<tau>, \<omega>0')
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe \<Delta> n C' (fst \<sigma>') \<tau> \<omega>1 Q)"
  using assms safe.simps(1) apply simp_all
  by (metis prod.collapse)

definition CSL :: "'a concrete_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> cmd \<Rightarrow> 'a equi_state set \<Rightarrow> bool" where
  "CSL \<Delta> P C Q \<longleftrightarrow> (\<forall>n s \<tau> \<omega>. TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>) \<and> (Ag s, \<tau>, \<omega>) \<in> P \<and> sep_algebra_class.stable \<omega> \<longrightarrow> safe \<Delta> n C s \<tau> \<omega> Q)"

lemma CSL_I:
  assumes "\<And>n s \<tau> \<omega>. TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>) \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> P \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> safe \<Delta> (Suc n) C s \<tau> \<omega> Q"
  shows "CSL \<Delta> P C Q"
  by (metis CSL_def assms not0_implies_Suc safe.simps(1))

lemma CSL_E:
  assumes "CSL \<Delta> P C Q"
      and "(Ag s, \<tau>, \<omega>) \<in> P"
      and "sep_algebra_class.stable \<omega>"
      and "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>)"
    shows "safe \<Delta> n C s \<tau> \<omega> Q"
  using CSL_def assms by fast


lemma safety_mono:
  assumes "safe \<Delta> n C s \<tau> \<omega> Q"
      and "m \<le> n"
    shows "safe \<Delta> m C s \<tau> \<omega> Q"
  using assms
proof (induct m arbitrary: C n s \<omega>)
  case (Suc m)
  then obtain k where "n = Suc k"
    using Suc_le_D by presburger
  then show ?case using safeI[of C s \<tau> \<omega> Q] safeE
    by (smt (verit, ccfv_threshold) Suc.hyps Suc.prems(1) Suc.prems(2) Suc_le_mono)
qed (simp)

lemma no_aborts_agrees:
  assumes "no_aborts \<Delta> C s \<tau> \<omega>"
      and "agrees (fvC C) s s'"
      and "TypedEqui.typed_store \<Delta> s"
    shows "no_aborts \<Delta> C s' \<tau> \<omega>"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "TypedEqui.typed \<Delta> (Ag s', \<tau>, \<omega>0')" "sep_algebra_class.stable \<omega>0'" "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f \<and> binary_mask \<omega>0'"
  then have "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>0')"
    by (simp add: TypedEqui.typed_def assms(3) get_abs_state_def)
  then show "\<not> aborts C (concretize s' \<omega>0')"
    by (metis asm0(2-4) aborts_agrees agrees_search(1) assms(1) assms(2) fst_conv no_aborts_def snd_conv)
qed

abbreviation fvA where
  "fvA \<Delta> Q \<equiv> TypedEqui.free_vars \<Delta> Q"

lemma fvA_agrees:
  assumes "agrees (fvA \<Delta> Q) s s'"
      and "TypedEqui.finite_context \<Delta>"
      and "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>)"
      and "TypedEqui.typed \<Delta> (Ag s', \<tau>, \<omega>)"
    shows "(Ag s, \<tau>, \<omega>) \<in> Q \<longleftrightarrow> (Ag s', \<tau>, \<omega>) \<in> Q"
proof (rule TypedEqui.free_vars_agree)
  show "TypedEqui.equal_on_set (fvA \<Delta> Q) s s'"
    using assms(1)
    unfolding agrees_def TypedEqui.equal_on_set_def
    by simp
qed (simp_all add: assms)


thm TypedEqui.typed_store_def

(* variables and tys should agree? *)

(*
make_context_semantic \<Delta> (type_ctxt_front_end_syntactic tys)

definition type_ctxt_front_end_syntactic :: "vtyp list \<Rightarrow> (var \<Rightarrow> vtyp option) \<times> (char list \<Rightarrow> vtyp option)"
  where
  "type_ctxt_front_end_syntactic tys =
  ( (\<lambda>x. if x < length tys then Some (case tys ! x of TInt \<Rightarrow> TInt | _ \<Rightarrow> TRef) else None), (\<lambda>f. if f = field_val then Some TInt else None) )"


*)

(*
thm red_keeps_typed_store

term "make_context_semantic \<Delta> (type_ctxt_front_end_syntactic tys)"
abbreviation well_typed_cmd where
  "well_typed_cmd tys C \<equiv> custom_context \<Delta> = type_ctxt_heap \<and> variables \<Delta> = type_ctxt_store \<Delta> tys \<and> well_typed_cmd tys C"
*)
(*
definition make_context_semantic  :: "('a, 'a virtual_state) interp \<Rightarrow> (nat \<Rightarrow> vtyp option) \<times> (char list \<Rightarrow> vtyp option) \<Rightarrow> ('a val, char list \<Rightarrow> 'a val set option) abs_type_context"
  where
  "make_context_semantic \<Delta> F = \<lparr> variables = (sem_store (domains \<Delta>) (fst F)), custom_context = (sem_fields (domains \<Delta>) (snd F))  \<rparr>"
*)

thm red_keeps_typed_store
(*
\<langle>?C, ?\<sigma>\<rangle> \<rightarrow> \<langle>?C', ?\<sigma>'\<rangle> \<Longrightarrow>
TypedEqui.typed_store (make_context_semantic ?\<Delta> (type_ctxt_front_end_syntactic ?tys)) (fst ?\<sigma>) \<Longrightarrow>
well_typed_cmd ?tys ?C \<Longrightarrow> TypedEqui.typed_store (make_context_semantic ?\<Delta> (type_ctxt_front_end_syntactic ?tys)) (fst ?\<sigma>')
*)

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
    show "get_trace x = get_trace y"
      by (metis assms(3) assms(4) calculation greater_state_has_greater_parts(2) minus_bigger minus_default)
    show "get_state x = get_state y"
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

definition mk_virtual_state where
  "mk_virtual_state h = Abs_virtual_state (\<lambda>l. if l \<in> dom h then 1 else 0, h)"

(* TODO: lift_definition
\<longrightarrow> ex: t2a_virtual_state AbstractRefinesTotal
.rep_eq
 *)

lemma get_wf_easy:
  assumes "wf_pre_virtual_state \<phi>"
  shows "get_vm (Abs_virtual_state \<phi>) = fst \<phi> \<and> get_vh (Abs_virtual_state \<phi>) = snd \<phi>"
  by (simp add: Abs_virtual_state_inverse assms get_vh_def get_vm_def)



lemma mk_virtual_state_simps[simp]:
  "get_vm (mk_virtual_state h) = (\<lambda>l. if l \<in> dom h then 1 else 0)"
  "get_vh (mk_virtual_state h) = h"
proof -
  have "wf_pre_virtual_state (\<lambda>l. if l \<in> dom h then 1 else 0, h)"
    by (smt (verit, best) EquiSemAuxLemma.gr_0_is_ppos domIff leD linorder_linear not_gr_0 wf_mask_simple_def wf_pre_virtual_stateI)
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



lemma binary_mask_and_stable_then_mk_virtual:
  assumes "sep_algebra_class.stable \<omega>"
      and "binary_mask \<omega>"
    shows "\<omega> = mk_virtual_state (get_vh \<omega>)"
proof (rule virtual_state_ext)
  show "get_vm \<omega> = get_vm (mk_virtual_state (get_vh \<omega>))"
  proof
    fix l show "get_vm \<omega> l = get_vm (mk_virtual_state (get_vh \<omega>)) l"
      by (metis EquiSemAuxLemma.gr_0_is_ppos assms(1) assms(2) binary_mask_def mk_virtual_state_charact(1) mk_virtual_state_simps(1) mk_virtual_state_simps(2) norm_preal(4) stable_virtual_state_def vstate_wf_imp)
  qed
qed (simp)


lemma typed_smaller_state:
  assumes "TypedEqui.typed \<Delta> (Ag s, (\<tau>, \<omega>'))"
      and "\<omega>' \<succeq> \<omega>"
    shows "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>)"
proof -
  have "(\<tau>, \<omega>') \<succeq> (\<tau>, \<omega>)"
    by (simp add: assms(2) greater_two_comp succ_refl)
  then have "(Ag s, (\<tau>, \<omega>')) \<succeq> (Ag s, \<tau>, \<omega>)"
    by (meson add_defined_lift greater_equiv)
  then show ?thesis
    using TypedEqui.typed_smaller assms(1) by blast
qed


lemma get_simps_unfolded[simp]:
  "get_store (Ag s, \<tau>, \<omega>) = s"
  "get_state (Ag s, \<tau>, \<omega>) = \<omega>"
  "get_h (Ag s, \<tau>, \<omega>) = get_vh \<omega>"
  "get_m (Ag s, \<tau>, \<omega>) = get_vm \<omega>"
     apply (simp add: get_store_def)
      apply (simp add: get_state_def)
    apply (simp add: get_state_def)
  by (simp add: get_state_def)

lemma typed_then_store_typed[simp]:
  assumes "typed (tcfe \<Delta> tys) \<sigma>"
  shows "store_typed (type_ctxt_store \<Delta> tys) (get_store \<sigma>)"
  using assms unfolding TypedEqui.typed_def TypedEqui.typed_store_def
  by (simp add: type_ctxt_front_end_def)


lemma typed_equi_red:
  assumes "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "\<langle>C, (s, get_vh \<omega>)\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      and "sep_algebra_class.stable \<omega>'"
      and "binary_mask \<omega>'"
      and "snd \<sigma>' = get_vh \<omega>'"
      and "well_typed_cmd tys C"
    shows "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>')"
  unfolding TypedEqui.typed_def
proof
  have "store_typed (type_ctxt_store \<Delta> tys) (fst \<sigma>')"
    using assms(2)
    apply (rule red_keeps_typed_store)
    using assms(1)
    using typed_then_store_typed apply fastforce
    by (simp add: assms(6))


  then show "TypedEqui.typed_store (tcfe \<Delta> tys) (get_store (Ag (fst \<sigma>'), \<tau>, \<omega>'))"
    unfolding TypedEqui.typed_store_def
    by (simp add: type_ctxt_front_end_def)
  
  show "well_typed (custom_context (tcfe \<Delta> tys)) (get_abs_state (Ag (fst \<sigma>'), \<tau>, \<omega>'))"
  proof (rule well_typedI)
    show "\<And>l \<phi>. the_ag (fst (get_abs_state (Ag (fst \<sigma>'), \<tau>, \<omega>'))) l = Some \<phi> \<Longrightarrow> well_typed_heap (custom_context (tcfe \<Delta> tys)) \<phi>"
      by (metis TypedEqui.typed_def assms(1) fst_conv get_abs_state_def snd_conv well_typedE(2))
    have "heap_typed type_ctxt_heap (snd \<sigma>')"
    proof (rule red_keeps_well_typed_cmd[OF assms(2)])
      have "Instantiation.well_typed_heap (custom_context (tcfe \<Delta> tys)) \<omega>"
        by (metis TypedEqui.typed_def assms(1) get_abs_state_def snd_conv well_typedE(1))
      then show "heap_typed type_ctxt_heap (snd (concretize s \<omega>))"
        by (simp add: type_ctxt_front_end_def)
    qed
    then show "well_typed_heap (custom_context (tcfe \<Delta> tys)) (snd (get_abs_state (Ag (fst \<sigma>'), \<tau>, \<omega>')))"
      by (simp add: assms(5) get_abs_state_def type_ctxt_front_end_def)
  qed
qed

(*
lemma fvA_agrees:
  assumes "agrees (fvA \<Delta> Q) s s'"
      and "TypedEqui.finite_fv \<Delta> Q"
      and "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>)"
      and "TypedEqui.typed \<Delta> (Ag s', \<tau>, \<omega>)"
    shows "(Ag s, \<tau>, \<omega>) \<in> Q \<longleftrightarrow> (Ag s', \<tau>, \<omega>) \<in> Q"
proof (rule TypedEqui.free_vars_agree)
*)

lemma fvA_agrees_better:
  assumes "agrees (fvA \<Delta> A) (get_store a) (get_store b)"
      and "get_trace a = get_trace b"
      and "get_state a = get_state b"
      and "a \<in> A"
      and "TypedEqui.typed \<Delta> a"
      and "TypedEqui.typed \<Delta> b"
      and "TypedEqui.finite_context \<Delta>"
    shows "b \<in> A"
  by (metis assms fvA_agrees set_state_def set_state_get_state)

lemma finite_context_simp[simp]:
  "TypedEqui.finite_context (tcfe \<Delta> tys)"
  by (metis (no_types, opaque_lifting) TypedEqui.finite_context_def abs_type_context.select_convs(1) domIff finite_nat_set_iff_bounded type_ctxt_front_end_def type_ctxt_store_def)

lemma safe_agrees:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q"
      and "agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) s s'"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys C"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s', \<tau>, \<omega>)"
    shows "safe (tcfe \<Delta> tys) n C s' \<tau> \<omega> Q"
  using assms
proof (induct n arbitrary: C s s' \<omega>)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s', \<tau>, \<omega>) \<in> Q"
      apply (rule fvA_agrees_better[of "tcfe \<Delta> tys" _ "(Ag s, \<tau>, \<omega>)"])
            apply (simp_all add: Suc)
      using Suc.prems(2) apply auto[1]
        apply (simp add: get_trace_def)
      by (simp add: safeE(1)[OF Suc.prems(1)])

    show "accesses C s' \<subseteq> read_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) accesses_agrees by force
    show "writes C s' \<subseteq> write_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) agrees_simps(4) safeE(3) writes_agrees by blast
    show "no_aborts (tcfe \<Delta> tys) C s' \<tau> \<omega>"
      by (metis ConcreteSemantics.get_store_Ag_simplifies Suc.prems(1) Suc.prems(2) Suc.prems(3) TypedEqui.typed_def agrees_simps(4) no_aborts_agrees safeE(4))
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "\<langle>C, concretize s' \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      "TypedEqui.typed (tcfe \<Delta> tys) (Ag s', \<tau>, \<omega>0')"
    then obtain s'' h' where "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'"
      using red_agrees[OF asm0(4)]
      by (metis Suc.prems(2) Un_upper1 agrees_search(1) fst_conv snd_conv)
    moreover have "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
      by (metis ConcreteSemantics.get_store_Ag_simplifies Suc.prems(3) TypedEqui.typed_def asm0(5) get_abs_state_def snd_conv)
    ultimately obtain \<omega>1 \<omega>1' where r1: "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1'
  \<and> snd (s'', h') = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst (s'', h')) \<tau> \<omega>1 Q"
      using safeE(5)[OF Suc(2), of \<omega>f \<omega>0' C']
      using asm0(1) asm0(2) asm0(3) by blast
    moreover have "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
    proof (rule Suc.hyps)
      show "safe (tcfe \<Delta> tys) n C' (fst (s'', h')) \<tau> \<omega>1 Q"
        using r1 by blast
      show "agrees (fvC C' \<union> fvA (tcfe \<Delta> tys) Q) (fst (s'', h')) (fst \<sigma>')"
        by (metis \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close> agreesC agrees_simps(4) fst_eqD red_properties sup.absorb_iff1)
      
      have "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst (s'', h')), \<tau>, \<omega>1')"
      proof (rule typed_equi_red)
        show "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle>"          
          by (simp add: \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close>)
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
          using \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')\<close> by auto
        show "sep_algebra_class.stable \<omega>1'"
          using asm0(1) r1 stable_sum by blast
        show "snd (s'', h') = get_vh \<omega>1'"
          using r1 by auto
        show "well_typed_cmd tys C"
          using Suc.prems(4) by fastforce
      qed (simp_all add: r1 Suc)
      show "well_typed_cmd tys C'"
        using Suc.prems(4) asm0(4) well_typed_cmd_red by blast
      show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
        by (metis (no_types, lifting) Suc.prems(4) \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close> asm0(1) asm0(4) asm0(5) commutative greater_equiv r1 sndI stable_sum typed_equi_red typed_smaller_state)
      show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst (s'', h')), \<tau>, \<omega>1)"
        using \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst (s'', h')), \<tau>, \<omega>1')\<close> greater_def r1 typed_smaller_state by blast
    qed
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
      using \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA (tcfe \<Delta> tys) Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close> r1 by auto
  qed
qed (simp)



subsection \<open>Skip\<close>

lemma safe_skip[intro!]:
  assumes "(Ag s, \<tau>, \<omega>) \<in> Q"
  shows "safe \<Delta> n Cskip s \<tau> \<omega> Q"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "no_aborts \<Delta> Cskip s \<tau> \<omega>"
      by (simp add: no_abortsI)
    show "Cskip = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> Q"
      by (simp add: assms)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume "\<langle>Cskip, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe \<Delta> n C' (fst \<sigma>') \<tau> \<omega>1 Q"
      by force
  qed (simp_all)
qed (simp)

proposition rule_skip:
  "CSL \<Delta> P Cskip P"
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
  have "\<And>l. get_vm \<omega>' l \<le> 1"
    by (simp add: get_vm_bound)
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
  assumes "no_aborts \<Delta> C s \<tau> \<omega>"
      and "\<omega>' \<succeq> \<omega>"
    shows "no_aborts \<Delta> C s \<tau> \<omega>'"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>0')" "sep_algebra_class.stable \<omega>0'" "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f \<and> binary_mask \<omega>0'"
  then obtain r where "Some \<omega>0' = \<omega> \<oplus> r"
    using assms(2) bigger_sum_smaller by blast
  then have "Some \<omega>0' = \<omega> \<oplus> stabilize r"
    by (metis asm0(2) commutative stabilize_sum_result_stable)
  then show "\<not> aborts C (concretize s \<omega>0')"
    using asm0(1) asm0(2) asm0(4) assms(1) no_abortsE stabilize_is_stable by blast
qed


lemma frame_safe:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q"
      and "fvA (tcfe \<Delta> tys) R \<inter> wrC C = {}"
      and "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "(Ag s, \<tau>, \<omega>f) \<in> R"
      and "sep_algebra_class.stable \<omega>f"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys C"
    shows "safe (tcfe \<Delta> tys) n C s \<tau> \<omega>' (Q \<otimes> R)"
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
    show "no_aborts (tcfe \<Delta> tys) C s \<tau> \<omega>'"
      using safeE(4)[OF Suc.prems(1)]
      using Suc.prems(3) greater_def no_aborts_mono by blast
    fix \<omega>0' \<omega>f' C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f'" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f'" "binary_mask \<omega>0'" "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    then obtain \<omega>f'' where "Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asso2 option.collapse)
    then have "Some \<omega>0' = \<omega> \<oplus> \<omega>f''"
      using asm0 Suc.prems(3) asso1 by force
    moreover have "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>f'')"
      using asm0(5) calculation greater_equiv typed_smaller_state by blast
    ultimately obtain \<omega>1'' \<omega>1' where "Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'" "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1'' Q"
      "sep_algebra_class.stable \<omega>1''"
      using safeE(5)[OF Suc(2), of \<omega>0' \<omega>f'' C' \<sigma>'] asm0
      by (meson Suc.prems(1) Suc.prems(5) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> safeE(5) stable_sum)
    then obtain \<omega>1 where "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
      by (metis (no_types, opaque_lifting) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> asso3 option.collapse)
    moreover have "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q \<otimes> R)"
      using \<open>safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1'' Q\<close>
    proof (rule Suc(1)[of C' _ \<omega>1'' \<omega>1 \<omega>f])
      show "fvA (tcfe \<Delta> tys) R \<inter> wrC C' = {}"
        by (meson Suc.prems(2) asm0 disjoint_iff red_properties subset_iff)
      show "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
        using calculation by auto
      have "agrees (-(wrC C)) s (fst \<sigma>')"
        by (metis agrees_search(1) asm0(4) fst_conv red_properties)
      then have "agrees (fvA (tcfe \<Delta> tys) R) s (fst \<sigma>')"
        using Suc.prems(2) agrees_search(3) by auto
      show "(Ag (fst \<sigma>'), \<tau>, \<omega>f) \<in> R"
      proof (rule TypedEqui.free_varsE)
        show "TypedEqui.equal_on_set (fvA (tcfe \<Delta> tys) R) s (fst \<sigma>')"
          by (meson TypedEqui.equal_on_set_def \<open>agrees (fvA (tcfe \<Delta> tys) R) s (fst \<sigma>')\<close> agrees_def)
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>f)"
          using \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>f'')\<close> greater_def typed_smaller_state by blast
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>f)"
          unfolding TypedEqui.typed_def
          apply (rule conjI)
           apply (metis Suc.prems(7) TypedEqui.typed_store_def \<open>typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>f)\<close> abs_type_context.select_convs(1) asm0(4) fst_conv get_simps_unfolded(1) red_keeps_typed_store type_ctxt_front_end_def typed_then_store_typed)
          by (metis TypedEqui.typed_def \<open>typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>f)\<close> get_abs_state_def snd_conv)
        show "(Ag s, \<tau>, \<omega>f) \<in> R"
          by (simp add: Suc.prems(4))
      qed (simp add: assms)
      have "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1')"
        using typed_equi_red[OF _ asm0(4)]
        by (metis Suc.prems(5) Suc.prems(7) \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'\<close> \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> \<open>sep_algebra_class.stable \<omega>1''\<close> asm0(1) asm0(5) stable_sum)
      then show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1'')"
        using \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'\<close> greater_def typed_smaller_state by blast
      show "well_typed_cmd tys C'"
        using Suc.prems(7) asm0(4) well_typed_cmd_red by blast
    qed (simp_all add: Suc.prems)
    ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f' \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q \<otimes> R)"
      by (metis Suc.prems(5) \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'\<close> \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> \<open>sep_algebra_class.stable \<omega>1''\<close> asso1 stable_sum)
  qed
qed (simp)


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
(*
lemma stabilize_stable_simp[simp]:
  "sep_algebra_class.stable (stabilize \<omega>)"
  using stabilize_is_stable by blast
*)

proposition frame_rule:
  assumes "CSL (tcfe \<Delta> tys) P C Q"
      and "disjoint (fvA (tcfe \<Delta> tys) R) (wrC C)"
      and "self_framing P"
      and "self_framing R"
      and "well_typed_cmd tys C"
    shows "CSL (tcfe \<Delta> tys) (P \<otimes> R) C (Q \<otimes> R)"
proof (rule CSL_I)
  fix n s \<tau> \<omega> assume asm0: "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)" "(Ag s, \<tau>, \<omega>) \<in> P \<otimes> R" "sep_algebra_class.stable \<omega>"
    "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
  then obtain \<omega>p \<omega>r where r: "Some \<omega> = \<omega>p \<oplus> \<omega>r" "(Ag s, \<tau>, \<omega>p) \<in> P" "(Ag s, \<tau>, \<omega>r) \<in> R"
    by (meson sum_equi_states_easy_decompose)
(*
  then have "TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>p) \<and> TypedEqui.typed \<Delta> (Ag s, \<tau>, \<omega>r)"
    using TypedEqui.typed_assertionE[OF assms(5), of "(Ag s, \<tau>, \<omega>p)"] TypedEqui.typed_assertionE[OF assms(6)]
    by simp
*)
  show "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> (Q \<otimes> R)"
  proof (rule frame_safe[of _ _ "Suc n" C s \<tau> "stabilize \<omega>p" Q R \<omega> "stabilize \<omega>r"])
    show "Some \<omega> = stabilize \<omega>p \<oplus> stabilize \<omega>r"
      using \<open>sep_algebra_class.stable \<omega>\<close> stabilize_sum_of_stable r by blast
    show "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> (stabilize \<omega>p) Q"
      by (metis (no_types, lifting) CSL_E TypedEqui.typed_state_then_stabilize_typed asm0(1) assms(1) assms(3) commutative greater_equiv r(1) r(2) self_framingE stabilize_equi_state stabilize_is_stable typed_smaller_state)
    show "fvA (tcfe \<Delta> tys) R \<inter> wrC C = {}"
      by (meson assms(2) disjoint_def)
    show "(Ag s, \<tau>, stabilize \<omega>r) \<in> R"
      by (metis assms(4) r(3) self_framingE stabilize_equi_state)
    show "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, stabilize \<omega>p)"
      using \<open>Some \<omega> = stabilize \<omega>p \<oplus> stabilize \<omega>r\<close> asm0(1) greater_def typed_smaller_state by blast
    show "well_typed_cmd tys C"
      using assms(5) by blast
  qed (simp_all add: assms)
qed




subsection \<open>Parallel rule\<close>

lemma compatible_sum_less_one:
  assumes "a ## b"
  shows "get_vm a l + get_vm b l \<le> 1"
proof -
  obtain \<omega> where "Some \<omega> = a \<oplus> b"
    by (metis assms defined_def not_Some_eq)
  then show ?thesis
    by (metis EquiViper.add_masks_def get_vm_additive get_vm_bound)
qed

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
      by (simp add: assms compatible_sum_less_one leD)
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
  assumes "safe (tcfe \<Delta> tys) n C1 s \<tau> \<omega>1 Q1"
      and "safe (tcfe \<Delta> tys) n C2 s \<tau> \<omega>2 Q2"
      and "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
      and "disjoint (fvC C1 \<union> fvA (tcfe \<Delta> tys) Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) Q2) (wrC C1)"
      and "sep_algebra_class.stable \<omega>1"
      and "sep_algebra_class.stable \<omega>2"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys ({A1} C1 {B1} || {A2} C2 {B2})"
    shows "safe (tcfe \<Delta> tys) n ({A1} C1 {B1} || {A2} C2 {B2}) s \<tau> \<omega> (Q1 \<otimes> Q2)"
  using assms
proof (induct n arbitrary: C1 C2 \<omega>1 \<omega>2 \<omega> s)
  case (Suc n)
  show "safe (tcfe \<Delta> tys) (Suc n) ({A1} C1 {B1} || {A2} C2 {B2}) s \<tau> \<omega> (Q1 \<otimes> Q2)"
  proof (rule safeI_alt)
    show "accesses ({A1} C1 {B1} || {A2} C2 {B2}) s \<subseteq> read_dom \<omega>"
      by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) Un_mono accesses.simps(8) read_dom_union safeE(2))
    show "writes ({A1} C1 {B1} || {A2} C2 {B2}) s \<subseteq> write_dom \<omega>"
    proof -
      have "writes C1 s \<subseteq> write_dom \<omega> \<and> writes C2 s \<subseteq> write_dom \<omega>"
        by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Suc.prems(3) dual_order.trans le_supE safeE(3) write_dom_union)
      then show ?thesis
        by simp
    qed
    fix \<omega>0' \<omega>f
    assume asm0: "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')" "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    then have types: "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>1) \<and> TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>2)"
      by (meson Suc.prems(3) greater_def greater_equiv typed_smaller_state)
    show "aborts ({A1} C1 {B1} || {A2} C2 {B2}) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts ({A1} C1 {B1} || {A2} C2 {B2}) (concretize s \<omega>0')"
      then show "False"
      proof (rule aborts_par_elim)
        show "aborts C1 (concretize s \<omega>0') \<Longrightarrow> False"
          using no_abortsE[OF safeE(4)[OF Suc.prems(1)], of \<omega>0']
          by (smt (verit) Suc.prems(1) Suc.prems(3) Suc.prems(6) Suc.prems(7) asm0(1) asm0(2) asm0(3) asm0(4) commutative greater_equiv no_abortsE no_aborts_mono safe.simps(2) stable_sum)
        show "aborts C2 (concretize s \<omega>0') \<Longrightarrow> False"
          using no_abortsE[OF safeE(4)[OF Suc.prems(2)]]
        proof -
          assume "aborts C2 (concretize s \<omega>0')"
          then have "\<forall>v. \<omega>f \<oplus> \<omega> \<noteq> v \<oplus> \<omega>2"
            by (metis (no_types) Suc.prems(3) Suc.prems(6) Suc.prems(7) \<open>\<And>\<omega>f \<omega>0'. \<lbrakk>sep_algebra_class.stable \<omega>0'; sep_algebra_class.stable \<omega>f; Some \<omega>0' = \<omega>2 \<oplus> \<omega>f; binary_mask \<omega>0'; TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')\<rbrakk> \<Longrightarrow> \<not> aborts C2 (concretize s \<omega>0')\<close> already_stable asm0(1) asm0(2) asm0(3) asm0(4) commutative stabilize_is_stable stabilize_sum_of_stable stable_sum)
          then show ?thesis
            by (metis (no_types) Suc.prems(3) asm0(3) commutative greater_equiv succ_trans)
        qed
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
    assume asm1: "\<langle>({A1} C1 {B1} || {A2} C2 {B2}), concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
    proof (rule red_par_cases)
      show "C' = Cskip \<Longrightarrow> \<sigma>' = concretize s \<omega>0' \<Longrightarrow> C1 = Cskip \<Longrightarrow> C2 = Cskip
  \<Longrightarrow> \<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using safeE(1)[OF Suc.prems(1)] safeE(1)[OF Suc.prems(2)]
        by (smt (verit) Suc.prems(3) Suc.prems(6) Suc.prems(7) asm0(3) asm0(4) fst_conv safe_skip snd_conv stable_sum sum_equi_states_easy x_elem_set_product)
      fix C1'
      assume asm2: "C' = ({A1} C1' {B1} || {A2} C2 {B2})" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>2 \<oplus> \<omega>f"
        by (metis (no_types, opaque_lifting) Suc.prems(3) asm0(3) asso2 option.exhaust_sel)
      then have "Some \<omega>0' = \<omega>1 \<oplus> \<omega>f'"
        using Suc.prems(3) asm0(3) asso1 by force
      then obtain \<omega>a \<omega>a' where ra: "Some \<omega>a' = \<omega>a \<oplus> \<omega>f' \<and> binary_mask \<omega>a' \<and> snd \<sigma>' = get_vh \<omega>a'" "safe (tcfe \<Delta> tys) n C1' (fst \<sigma>') \<tau> \<omega>a Q1"
        "sep_algebra_class.stable \<omega>a"
        using safeE(5)[OF Suc(2), of \<omega>f' \<omega>0' C1' \<sigma>'] asm0 asm2(2)
        using Suc.prems(7) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> stable_sum by blast
      moreover have "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>a')"
        using typed_equi_red[OF Suc(9)]
        by (metis Suc.prems(7) Suc.prems(9) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asm0(1) asm0(2) asm1 ra(1) ra(3) stable_sum typed_equi_red)
      then have "TypedEqui.typed_store (tcfe \<Delta> tys) (fst \<sigma>')"
        by (simp add: TypedEqui.typed_def)
      moreover have "safe (tcfe \<Delta> tys) n C2 (fst \<sigma>') \<tau> \<omega>2 Q2"
      proof (rule safe_agrees)
        show "safe (tcfe \<Delta> tys) n C2 s \<tau> \<omega>2 Q2"
          by (meson Suc.prems(2) Suc_n_not_le_n nat_le_linear safety_mono)
        have "agrees (-wrC C1) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        then show "agrees (fvC C2 \<union> fvA (tcfe \<Delta> tys) Q2) s (fst \<sigma>')"
          using Suc.prems(5) agrees_minusD disjoint_search(1) by blast
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>2)"
          using types by blast
        show "well_typed_cmd tys C2"
          using Suc.prems(9) by auto
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>2)"
          by (metis ConcreteSemantics.get_store_Ag_simplifies TypedEqui.typed_def calculation(4) get_abs_state_def snd_conv types)
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>a \<oplus> \<omega>2"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso2 calculation(1) commutative option.exhaust_sel)
      then have "Some \<omega>a' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso1 calculation(1))
      moreover have "safe (tcfe \<Delta> tys) n {A1} C1' {B1} || {A2} C2 {B2} (fst \<sigma>') \<tau> \<omega>' (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close>
      proof (rule Suc(1)[OF ra(2) \<open>safe (tcfe \<Delta> tys) n C2 (fst \<sigma>') \<tau> \<omega>2 Q2\<close>])
        show "disjoint (fvC C1' \<union> fvA (tcfe \<Delta> tys) Q1) (wrC C2)"
          by (metis Suc.prems(4) asm2(2) disjoint_search(2) disjoint_simps(3) red_properties)
        show "disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) Q2) (wrC C1')"
          by (meson Suc.prems(5) asm2(2) disjoint_search(1) disjoint_search(2) red_properties)
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>')"
          using \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>a')\<close> calculation(6) commutative greater_equiv typed_smaller_state by fastforce
        show "well_typed_cmd tys {A1} C1' {B1} || {A2} C2 {B2}"
          using Suc.prems(9) asm1 asm2(1) well_typed_cmd_red by blast
      qed (simp_all add: Suc disjoint_def ra(3))
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>a' = \<omega>' \<oplus> \<omega>f\<close> ra(1)
        using Suc.prems(7) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close> \<open>sep_algebra_class.stable \<omega>a\<close> stable_sum
        using asm2(1) by blast
    next
      fix C2'
      assume asm2: "C' = ({A1} C1 {B1} || {A2} C2' {B2})" "\<langle>C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C2', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>1 \<oplus> \<omega>f"
        by (metis Suc.prems(3) asm0(3) asso2 commutative option.exhaust_sel)
      then have "Some \<omega>0' = \<omega>2 \<oplus> \<omega>f'"
        by (metis Suc.prems(3) asm0(3) asso1 commutative)
      then obtain \<omega>a \<omega>a' where ra: "Some \<omega>a' = \<omega>a \<oplus> \<omega>f' \<and> binary_mask \<omega>a' \<and> snd \<sigma>' = get_vh \<omega>a'" "safe (tcfe \<Delta> tys) n C2' (fst \<sigma>') \<tau> \<omega>a Q2"
        "sep_algebra_class.stable \<omega>a"
        using safeE(5)[OF Suc(3), of \<omega>f' \<omega>0' C2' \<sigma>'] asm0 asm2(2)
        using Suc.prems(6) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> stable_sum by blast
      moreover have "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>a')"
        using typed_equi_red[OF Suc(9)]
        by (metis Suc.prems(6) Suc.prems(9) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asm0(1) asm0(2) asm2(2) ra(1) ra(3) stable_sum typed_equi_red well_typed_cmd.simps(9))
      then have "TypedEqui.typed_store (tcfe \<Delta> tys) (fst \<sigma>')"
        by (simp add: TypedEqui.typed_def)
      moreover have "safe (tcfe \<Delta> tys) n C1 (fst \<sigma>') \<tau> \<omega>1 Q1"
      proof (rule safe_agrees)
        show "safe (tcfe \<Delta> tys) n C1 s \<tau> \<omega>1 Q1"
          by (meson Suc.prems(1) Suc_n_not_le_n nat_le_linear safety_mono)
        have "agrees (-wrC C2) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        then show "agrees (fvC C1 \<union> fvA (tcfe \<Delta> tys) Q1) s (fst \<sigma>')"
          using Suc.prems(4) agrees_minusD disjoint_search(1) by blast
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>1)"
          using types by blast
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
          by (metis ConcreteSemantics.get_store_Ag_simplifies TypedEqui.typed_def \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>1)\<close> calculation(4) get_abs_state_def snd_conv)
        show "well_typed_cmd tys C1"
          using Suc.prems(9) by auto
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>a \<oplus> \<omega>1"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso2 calculation(1) commutative option.exhaust_sel)
      then have "Some \<omega>a' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso1 calculation(1))
      moreover have "safe (tcfe \<Delta> tys) n {A1} C1 {B1} || {A2} C2' {B2} (fst \<sigma>') \<tau> \<omega>' (Q1 \<otimes> Q2)"
      proof (rule Suc(1)[OF  \<open>safe (tcfe \<Delta> tys) n C1 (fst \<sigma>') \<tau> \<omega>1 Q1\<close> ra(2)])
        show "Some \<omega>' = \<omega>1 \<oplus> \<omega>a"
          by (simp add: \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>1\<close> commutative)
        show "disjoint (fvC C2' \<union> fvA (tcfe \<Delta> tys) Q2) (wrC C1)"
          by (metis Suc.prems(5) asm2(2) disjoint_search(2) disjoint_simps(3) red_properties)
        show "disjoint (fvC C1 \<union> fvA (tcfe \<Delta> tys) Q1) (wrC C2')"
          by (meson Suc.prems(4) asm2(2) disjoint_search(1) disjoint_search(2) red_properties)
        show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>')"
          using \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>a')\<close> calculation(6) commutative greater_equiv typed_smaller_state by fastforce
        show "well_typed_cmd tys {A1} C1 {B1} || {A2} C2' {B2}"
          using Suc.prems(9) asm1 asm2(1) well_typed_cmd_red by blast
      qed (simp_all add: Suc disjoint_def ra(3))
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>a' = \<omega>' \<oplus> \<omega>f\<close> ra(1)
        using Suc.prems(6) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>1\<close> \<open>sep_algebra_class.stable \<omega>a\<close> stable_sum
        using asm2(1) by blast
    qed
  qed (simp)
qed (simp)




proposition rule_par:
  assumes "CSL (tcfe \<Delta> tys) P1 C1 Q1"
      and "CSL (tcfe \<Delta> tys) P2 C2 Q2"
      and "disjoint (fvC C1 \<union> fvA (tcfe \<Delta> tys) Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) Q2) (wrC C1)"
      and "self_framing P1"
      and "self_framing P2"
      and "well_typed_cmd tys ({A1} C1 {B1} || {A2} C2 {B2})"
    shows "CSL (tcfe \<Delta> tys) (P1 \<otimes> P2) ({A1} C1 {B1} || {A2} C2 {B2}) (Q1 \<otimes> Q2)"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)" "(Ag s, \<tau>, \<omega>) \<in> P1 \<otimes> P2" "sep_algebra_class.stable \<omega>"
  then obtain p1 p2 where "Some \<omega> = p1 \<oplus> p2" "(Ag s, \<tau>, p1) \<in> P1" "(Ag s, \<tau>, p2) \<in> P2"
    by (meson sum_equi_states_easy_decompose)
  then have r: "Some \<omega> = stabilize p1 \<oplus> stabilize p2"
    using asm0(3) stabilize_sum_of_stable by blast
  moreover have "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, stabilize p1) \<and> TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, stabilize p2)"
    using asm0(1) greater_def greater_equiv r typed_smaller_state by blast
  moreover have "(Ag s, \<tau>, stabilize p1) \<in> P1 \<and> (Ag s, \<tau>, stabilize p2) \<in> P2"
    by (metis \<open>(Ag s, \<tau>, p1) \<in> P1\<close> \<open>(Ag s, \<tau>, p2) \<in> P2\<close> assms(5) assms(6) self_framingE stabilize_equi_state)
  show "safe (tcfe \<Delta> tys) (Suc n) {A1} C1 {B1} || {A2} C2 {B2} s \<tau> \<omega> (Q1 \<otimes> Q2)"
  proof (rule safe_par[of _ _ "Suc n" C1 s \<tau> "stabilize p1" Q1 C2 "stabilize p2" Q2 \<omega>])
    show "safe (tcfe \<Delta> tys) (Suc n) C1 s \<tau> (stabilize p1) Q1"
      using CSL_E \<open>(Ag s, \<tau>, stabilize p1) \<in> P1 \<and> (Ag s, \<tau>, stabilize p2) \<in> P2\<close> assms(1) calculation(2) stabilize_is_stable by blast
    show "safe (tcfe \<Delta> tys) (Suc n) C2 s \<tau> (stabilize p2) Q2"
      using CSL_E \<open>(Ag s, \<tau>, stabilize p1) \<in> P1 \<and> (Ag s, \<tau>, stabilize p2) \<in> P2\<close> assms(2) calculation(2) stabilize_is_stable by blast
    show "disjoint (fvC C1 \<union> fvA (tcfe \<Delta> tys) Q1) (wrC C2)"      
      using assms(3) by auto
    show "disjoint (fvC C2 \<union> fvA (tcfe \<Delta> tys) Q2) (wrC C1)"
      using assms(4) by auto
    show "well_typed_cmd tys {A1} C1 {B1} || {A2} C2 {B2}"
      using assms(7) by auto
  qed (simp_all add: assms r asm0)
qed



subsection \<open>Sequential composition\<close>


lemma safe_seq:
  assumes "safe (tcfe \<Delta> tys) n C1 s \<tau> \<omega> Q"
      and "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<tau>, \<omega>') \<in> Q \<and> sep_algebra_class.stable \<omega>' \<and> TypedEqui.typed (tcfe \<Delta> tys) (Ag s', \<tau>, \<omega>') \<Longrightarrow> safe (tcfe \<Delta> tys) m C2 s' \<tau> \<omega>' R"
      and "sep_algebra_class.stable \<omega>"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys (Cseq C1 C2)"
    shows "safe (tcfe \<Delta> tys) n (Cseq C1 C2) s \<tau> \<omega> R"
  using assms
proof (induct n arbitrary: C1 \<omega> s)
  case (Suc n)
  show "safe (tcfe \<Delta> tys) (Suc n) (Cseq C1 C2) s \<tau> \<omega> R"
  proof (rule safeI)
    show "accesses (Cseq C1 C2) s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) accesses.simps(7) safeE(2) by blast
    show "writes (Cseq C1 C2) s \<subseteq> write_dom \<omega>"
      by (metis Suc.prems(1) safeE(3) writes.simps(7))
    show "no_aborts (tcfe \<Delta> tys) (Cseq C1 C2) s \<tau> \<omega>"
      using safeE(4)[OF Suc.prems(1)] aborts_seq_elim
      by (meson no_aborts_def)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    assume "\<langle>Cseq C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 R"
    proof (rule red_seq_cases)
      assume asm1: "C1 = Cskip" "C' = C2" "\<sigma>' = concretize s \<omega>0'"
      then have "safe (tcfe \<Delta> tys) (Suc n) C2 s \<tau> \<omega> R"
        using Suc.prems(2)[of "Suc n" _ \<omega>] safeE(1)[OF Suc.prems(1)] Suc.prems(3)
        using Suc.prems(4) by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 R"
        by (metis (no_types, lifting) Suc.prems(3) Suc_n_not_le_n asm0(2) asm0(3) asm1(2) asm1(3) fst_conv nat_le_linear safety_mono snd_conv)
    next
      fix C1' assume asm1: "C' = Cseq C1' C2" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      then obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f" "sep_algebra_class.stable \<omega>1" "binary_mask \<omega>1'"
        "snd \<sigma>' = get_vh \<omega>1'" "safe (tcfe \<Delta> tys) n C1' (fst \<sigma>') \<tau> \<omega>1 Q"
        using safeE(5)[OF Suc.prems(1), of \<omega>f \<omega>0' C1' \<sigma>'] asm0(1) asm0(2) asm0(3) asm0(4) by blast
      then have "safe (tcfe \<Delta> tys) n (Cseq C1' C2) (fst \<sigma>') \<tau> \<omega>1 R" using Suc(1)[OF \<open>safe (tcfe \<Delta> tys) n C1' (fst \<sigma>') \<tau> \<omega>1 Q\<close>]
        using typed_equi_red[OF Suc.prems(4)]
        by (smt (verit, ccfv_SIG) Suc.prems(2) Suc.prems(5) \<open>TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')\<close> \<open>\<langle>Cseq C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>\<close> asm0(1) asm1(1) greater_def le_SucI stable_sum typed_equi_red typed_smaller_state well_typed_cmd_red)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 R"
        using \<open>Some \<omega>1' = \<omega>1 \<oplus> \<omega>f\<close> \<open>binary_mask \<omega>1'\<close> \<open>sep_algebra_class.stable \<omega>1\<close> \<open>snd \<sigma>' = get_vh \<omega>1'\<close> asm1(1) by blast
    qed
  qed (simp)
qed (simp)


proposition rule_seq:
  assumes "CSL (tcfe \<Delta> tys) P C1 Q"
      and "CSL (tcfe \<Delta> tys) Q C2 R"
      and "well_typed_cmd tys (Cseq C1 C2)"
    shows "CSL (tcfe \<Delta> tys) P (Cseq C1 C2) R"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)" "(Ag s, \<tau>, \<omega>) \<in> P" "sep_algebra_class.stable \<omega>"
  show "safe (tcfe \<Delta> tys) n (Cseq C1 C2) s \<tau> \<omega> R"
  proof (rule safe_seq[of _ _ n C1 s \<tau> \<omega> Q C2 R])
    show "safe (tcfe \<Delta> tys) n C1 s \<tau> \<omega> Q"
      using CSL_E asm0(1) asm0(2) asm0(3) assms(1) by blast
    show "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<tau>, \<omega>') \<in> Q \<and> sep_algebra_class.stable \<omega>' \<and> TypedEqui.typed (tcfe \<Delta> tys) (Ag s', \<tau>, \<omega>') \<Longrightarrow> safe (tcfe \<Delta> tys) m C2 s' \<tau> \<omega>' R"
      using CSL_E[OF assms(2)] by blast
    show "well_typed_cmd tys (Cseq C1 C2)"
      using assms(3) by blast
  qed (simp_all add: asm0)
qed



subsection \<open>Consequence rule\<close>

lemma safe_conseq:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q"
      and "Q \<subseteq> Q'"
    shows "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q'"
  using assms
proof (induct n arbitrary: C \<omega> s)
  case (Suc n)
  show "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> Q'"
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> Q'"
      using Suc.prems(1) assms(2) safe.simps(2) by blast
    show "accesses C s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) safeE(2) by blast
    show "writes C s \<subseteq> write_dom \<omega>"
      using Suc.prems(1) by auto
    show "no_aborts (tcfe \<Delta> tys) C s \<tau> \<omega>"
      using Suc.prems(1) safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
      "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q'"
      using safeE(5)[OF Suc.prems(1)] by (meson Suc.hyps assms(2))
  qed
qed (simp)

proposition rule_conseq:
  assumes "CSL (tcfe \<Delta> tys) P C Q"
      and "P' \<subseteq> P"
      and "Q \<subseteq> Q'"
    shows "CSL (tcfe \<Delta> tys) P' C Q'"
proof (rule CSL_I)
  show "\<And>n s \<tau> \<omega>. TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>) \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> P' \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> Q'"
    using CSL_E assms(1) assms(2) assms(3) safe_conseq by blast
qed


lemma safe_conseq_typed:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q"
      and "\<And>\<omega>. TypedEqui.typed (tcfe \<Delta> tys) \<omega> \<Longrightarrow> \<omega> \<in> Q \<Longrightarrow> \<omega> \<in> Q'"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys C"
    shows "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> Q'"
  using assms
proof (induct n arbitrary: C \<omega> s)
  case (Suc n)
  show "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> Q'"
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> Q'"
      using Suc.prems(1) assms(2) safe.simps(2)
      using Suc.prems(3) by blast
    show "accesses C s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) safeE(2) by blast
    show "writes C s \<subseteq> write_dom \<omega>"
      using Suc.prems(1) by auto
    show "no_aborts (tcfe \<Delta> tys) C s \<tau> \<omega>"
      using Suc.prems(1) safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
      "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q'"
      using safeE(5)[OF Suc.prems(1), of \<omega>f \<omega>0' C' \<sigma>']
      by (smt (verit, ccfv_SIG) Suc.hyps Suc.prems(4) assms(2) greater_def stable_sum typed_equi_red typed_smaller_state well_typed_cmd_red)      
  qed
qed (simp)


proposition rule_conseq_typed:
  assumes "CSL (tcfe \<Delta> tys) P C Q"
      and "ConcreteSemantics.entails_typed (tcfe \<Delta> tys) P' P"
      and "ConcreteSemantics.entails_typed (tcfe \<Delta> tys) Q Q'"
      and "well_typed_cmd tys C"
    shows "CSL (tcfe \<Delta> tys) P' C Q'"
proof (rule CSL_I)
  show "\<And>n s \<tau> \<omega>. TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>) \<Longrightarrow> (Ag s, \<tau>, \<omega>) \<in> P' \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> Q'"
    using CSL_E assms(1) assms(2) assms(3) assms(4) safe_conseq_typed unfolding ConcreteSemantics.entails_typed_def by metis
qed




subsection \<open>Conditional rule\<close>

(*
| RuleIf: "\<lbrakk> self_framing_and_typed (tcfe \<Delta> tys) A; framed_by_exp A b; (tcfe \<Delta> tys) \<turnstile> [A \<otimes> pure_typed (tcfe \<Delta> tys) b] C1 [B1] ; (tcfe \<Delta> tys) \<turnstile> [A \<otimes> pure_typed (tcfe \<Delta> tys) (negate b)] C2 [B2] \<rbrakk>
  \<Longrightarrow> (tcfe \<Delta> tys) \<turnstile> [A] If b C1 C2 [B1 \<union> B2]"
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
  assumes "CSL (tcfe \<Delta> tys) (P \<inter> assertify_bexp b) C1 Q"
      and "CSL (tcfe \<Delta> tys) (P \<inter> assertify_bexp (Bnot b)) C2 Q"
    shows "CSL (tcfe \<Delta> tys) P (Cif b C1 C2) Q"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> P" "sep_algebra_class.stable \<omega>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
  show "safe (tcfe \<Delta> tys) (Suc n) (Cif b C1 C2) s \<tau> \<omega> Q"
  proof (rule safeI)
    show "no_aborts (tcfe \<Delta> tys) (Cif b C1 C2) s \<tau> \<omega>"
      using aborts.cases cmd.distinct(45) cmd.distinct(57) cmd.distinct(85) cmd.simps(91) no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    assume "\<langle>Cif b C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
    proof (rule red_if_cases)
      assume asm2: "C' = C1" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<tau>, \<omega>) \<in> P \<inter> assertify_bexp b"
        by (simp add: asm0(1) asm1(2) full_add_charact(1) in_assertify_bexp_alt)
      then have "safe (tcfe \<Delta> tys) n C' s \<tau> \<omega> Q"
        using CSL_E[OF assms(1), of s \<tau> \<omega> n] asm0 asm2 by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    next
      assume asm2: "C' = C2" "\<sigma>' = concretize s \<omega>0'" "\<not> bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<tau>, \<omega>) \<in> P \<inter> assertify_bexp (Bnot b)"
        by (simp add: asm0(1) asm1(2) full_add_charact(1) in_assertify_bexp_alt)
      then have "safe (tcfe \<Delta> tys) n C' s \<tau> \<omega> Q"
        using CSL_E[OF assms(2), of s \<tau> \<omega> n] asm0 asm2 by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    qed
  qed (simp_all)
qed


subsection \<open>While loops\<close>


lemma safe_while:
  assumes "CSL (tcfe \<Delta> tys) (I \<inter> (assertify_bexp b)) C I"
      and "(Ag s, \<tau>, \<omega>) \<in> I"
      and "sep_algebra_class.stable \<omega>"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys (Cwhile b I' C)"
    shows "safe (tcfe \<Delta> tys) n (Cwhile b I' C) s \<tau> \<omega> (I \<inter> (assertify_bexp (Bnot b)))"
  using assms
proof (induct n arbitrary: \<omega> s)
  case (Suc n)
  note SucOuter = Suc
  show "safe (tcfe \<Delta> tys) (Suc n) (Cwhile b I' C) s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
  proof (rule safeI)
    show "no_aborts (tcfe \<Delta> tys) (Cwhile b I' C) s \<tau> \<omega>"
      using aborts_while_elim no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')"
    assume "\<langle>Cwhile b I' C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
    proof (rule red_while_cases)
      assume asm1: "C' = Cif b (Cseq C (Cwhile b I' C)) Cskip" "\<sigma>' = concretize s \<omega>0'"
      have "safe (tcfe \<Delta> tys) n C' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
      proof (cases n)
        case (Suc m)
        show "safe (tcfe \<Delta> tys) n C' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
          unfolding Suc
        proof (rule safeI)
          show "no_aborts (tcfe \<Delta> tys) C' s \<tau> \<omega>"
            using asm1(1) by blast
          fix \<omega>0' \<omega>f C'' \<sigma>'
          assume asm2: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
          assume "\<langle>C', concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C'', \<sigma>'\<rangle>"
          then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
            unfolding asm1(1)
          proof (rule red_if_cases)
            show "C'' = Cskip \<Longrightarrow> \<sigma>' = concretize s \<omega>0' \<Longrightarrow> \<not> bdenot b (fst (concretize s \<omega>0')) \<Longrightarrow>
    \<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              by (metis IntI SucOuter(3) SucOuter(4) asm2(2) asm2(3) bdenot.simps(3) fst_conv in_assertify_bexp_alt safe_skip snd_conv)
            assume asm3: "C'' = Cseq C (Cwhile b I' C)" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
            have "safe (tcfe \<Delta> tys) m C'' s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
              unfolding asm3(1)
            proof (rule safe_seq)
              show "safe (tcfe \<Delta> tys) m C s \<tau> \<omega> I"
                by (metis CSL_E IntI SucOuter(3) SucOuter(4) SucOuter(5) asm3(3) assms(1) fst_conv in_assertify_bexp_alt)
              show "\<And>ma \<omega>' s'. ma \<le> m \<and> (Ag s', \<tau>, \<omega>') \<in> I \<and> sep_algebra_class.stable \<omega>' \<and> TypedEqui.typed (tcfe \<Delta> tys) (Ag s', \<tau>, \<omega>') \<Longrightarrow> safe (tcfe \<Delta> tys) ma (Cwhile b I' C) s' \<tau> \<omega>' (I \<inter> assertify_bexp (Bnot b))"
                using Suc Suc.hyps[OF assms(1)] le_SucI safety_mono
                by (meson assms(5))
              show "well_typed_cmd tys (Cseq C (Cwhile b I' C))"
                using SucOuter(6) by auto
            qed (simp_all add: \<open>sep_algebra_class.stable \<omega>\<close> SucOuter(5))
            then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) m C'' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              using SucOuter(4) asm2(2) asm2(3) asm3(2) by auto
          qed
        qed (simp_all add: asm1(1))
      qed (simp)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
        using asm0 Suc.prems(3) asm1(2) by auto
    qed
  qed (simp_all)
qed (simp)


proposition rule_while:
  assumes "CSL (tcfe \<Delta> tys) (I \<inter> (assertify_bexp b)) C I"
      and "well_typed_cmd tys (Cwhile b I' C)"
    shows "CSL (tcfe \<Delta> tys) I (Cwhile b I' C) (I \<inter> (assertify_bexp (Bnot b)))"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume "(Ag s, \<tau>, \<omega>) \<in> I" "sep_algebra_class.stable \<omega>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
  then show "safe (tcfe \<Delta> tys) (Suc n) (Cwhile b I' C) s \<tau> \<omega> (I \<inter> assertify_bexp (Bnot b))"
    using assms(1) safe_while assms(2) by blast
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
    using get_vm_bound by blast
  ultimately have "get_vm \<omega>f l = 0"
    by (metis PosReal.padd_cancellative add.commute add.right_neutral assms(3) nle_le pos_perm_class.sum_larger)
  moreover have "get_vh \<omega>f l = None"
    using assms(2) calculation pperm_pgt_pnone stable_virtual_state_def
    by (metis EquiSemAuxLemma.gr_0_is_ppos)
  show ?thesis
  proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
    show "Some (Rep_virtual_state (set_value \<omega>' l v)) = Rep_virtual_state (set_value \<omega> l v) \<oplus> Rep_virtual_state \<omega>f"
    proof (rule plus_prodI)
      show "Some (fst (Rep_virtual_state (set_value \<omega>' l v))) = fst (Rep_virtual_state (set_value \<omega> l v)) \<oplus> fst (Rep_virtual_state \<omega>f)"
        by (metis assms(1) get_vh_vm_set_value(2) get_vm_additive get_vm_def)
      show "Some (snd (Rep_virtual_state (set_value \<omega>' l v))) = snd (Rep_virtual_state (set_value \<omega> l v)) \<oplus> snd (Rep_virtual_state \<omega>f)"
      proof (rule plus_funI)
        fix la show "Some (snd (Rep_virtual_state (set_value \<omega>' l v)) la) = snd (Rep_virtual_state (set_value \<omega> l v)) la \<oplus> snd (Rep_virtual_state \<omega>f) la"
        proof (cases "l = la")
          case True
          then have "snd (Rep_virtual_state (set_value \<omega>' l v)) la = Some v"
            by (metis fun_upd_apply get_vh_def get_vh_vm_set_value(1))
          moreover have "snd (Rep_virtual_state (set_value \<omega> l v)) la = Some v"
            by (metis True fun_upd_apply get_vh_def get_vh_vm_set_value(1))
          ultimately show ?thesis
            by (metis True \<open>get_vh \<omega>f l = None\<close> get_vh_def plus_option.simps(2))
        next
          case False
          then show ?thesis
            by (metis assms(1) fun_upd_apply get_vh_def plus_funE get_vh_vm_set_value(1) vstate_add_iff)
        qed
      qed
    qed
  qed
qed
(*
definition force_typing where
  "force_typing (tcfe \<Delta> tys) A = Set.filter (TypedEqui.typed (tcfe \<Delta> tys)) A"

lemma force_typing_is_typed[simp]:
  "TypedEqui.typed_assertion (tcfe \<Delta> tys) (force_typing (tcfe \<Delta> tys) A)"
  by (simp add: TypedEqui.typed_assertion_def force_typing_def)
*)
definition full_ownership :: "var \<Rightarrow> 'a equi_state set"
  where
  "full_ownership r = { \<omega> |\<omega> l v. get_store \<omega> r = Some (VRef (Address l)) \<and> 
get_state \<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt v) }"

lemma in_full_ownership:
  assumes "get_store \<omega> r = Some (VRef (Address l))"
      and "get_state \<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt v)"
    shows "\<omega> \<in> full_ownership r"
  using assms full_ownership_def by blast


(*
Use:
get_state \<omega> = acc_virt (l, field_val) (Abs_preal 1) v
*)

definition full_ownership_with_val where
  "full_ownership_with_val r e = { \<omega> |\<omega> l.
  get_state \<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt (edenot e (get_store \<omega>)))
  \<and> get_store \<omega> r = Some (VRef (Address l)) }"

(*
definition full_ownership_with_val where
  "full_ownership_with_val r e = { \<omega> |\<omega> l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1
  \<and> get_h \<omega> (l, field_val) = Some (VInt (edenot e (get_store \<omega>)))  }"
*)
(*
lemma in_full_ownership_with_val:
  assumes "get_store \<omega> r = Some (VRef (Address l))"
      and "get_m \<omega> (l, field_val) = 1"
      and "get_h \<omega> (l, field_val) = Some (VInt (edenot e (get_store \<omega>)))"
    shows "\<omega> \<in> full_ownership_with_val r e"
  using assms full_ownership_with_val_def by blast

*)

lemma in_full_ownership_with_val:
  assumes "s r = Some (VRef (Address l))"
      and "\<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt (edenot e s))"
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
  by (metis assms(1) assms(2) fun_upd_apply get_vh_vm_set_value(1) get_vh_vm_set_value(2) stable_virtual_state_def)



lemma acc_virt_set_value:
  "set_value (acc_virt hl p v) hl v' = acc_virt hl p v'"
proof (rule virtual_state_ext)
  show "get_vm (set_value (acc_virt hl p v) hl v') = get_vm (acc_virt hl p v')"
    by auto
  show "get_vh (set_value (acc_virt hl p v) hl v') = get_vh (acc_virt hl p v')"
    by simp
qed



proposition rule_write:
  "CSL (tcfe \<Delta> tys) (full_ownership r) (Cwrite r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n s \<tau> \<omega> assume "(Ag s, \<tau>, \<omega>) \<in> full_ownership r" "sep_algebra_class.stable \<omega>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
  then obtain l v where asm0: "s r = Some (VRef (Address l))" "\<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt v)"
    unfolding full_ownership_def by fastforce
  then have "get_vm \<omega> (l, field_val) = 1"
    by (simp add: one_preal.abs_eq)

  show "safe (tcfe \<Delta> tys) n (Cwrite r e) s \<tau> \<omega> (full_ownership_with_val r e)"
  proof (cases n)
    case (Suc m)
    moreover have "safe (tcfe \<Delta> tys) (Suc m) (Cwrite r e) s \<tau> \<omega> (full_ownership_with_val r e)"
    proof (rule safeI_alt)
      have "accesses (Cwrite r e) s = {l}" using get_address_simp asm0 by auto
      then show "accesses (Cwrite r e) s \<subseteq> read_dom \<omega>"

        by (simp add: \<open>get_vm \<omega> (l, field_val) = 1\<close> in_read_dom_write_dom(1))

      show "writes (Cwrite r e) s \<subseteq> write_dom \<omega>"
        by (simp add: \<open>get_vm \<omega> (l, field_val) = 1\<close> asm0(1) in_read_dom_write_dom(2))

      fix \<omega>0' \<omega>f
      assume asm1: "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'" "sep_algebra_class.stable \<omega>f"
      then have "s r = Some (VRef (Address l)) \<and> get_vm \<omega>0' (l, field_val) = 1"
        by (metis EquiViper.add_masks_def \<open>get_vm \<omega> (l, field_val) = 1\<close> asm0(1) binary_mask_def get_vm_additive padd_pos)

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
        by (simp add: \<open>get_vm \<omega> (l, field_val) = 1\<close> asm1(1) asm2(1) write_helper)
      moreover have "\<sigma>' = concretize s (set_value \<omega>0' (l, field_val) ?v) \<and> C' = Cskip"
        using red_write_cases[OF asm2(2)]
        using \<open>s r = Some (VRef (Address l)) \<and> get_vm \<omega>0' (l, field_val) = PosReal.pwrite\<close> old.prod.inject option.inject ref.inject get_vh_vm_set_value(1) val.inject(4) by fastforce
      moreover have "safe (tcfe \<Delta> tys) m Cskip s \<tau> (set_value \<omega> (l, field_val) ?v) (full_ownership_with_val r e)"
      proof (rule safe_skip)
        show "(Ag s, \<tau>, set_value \<omega> (l, field_val) (VInt (edenot e s))) \<in> full_ownership_with_val r e"
        proof (rule in_full_ownership_with_val)
          show "s r = Some (VRef (Address l))"
            by (simp add: asm0(1))
          show "set_value \<omega> (l, field_val) (VInt (edenot e s)) = acc_virt (l, field_val) (Abs_preal 1) (VInt (edenot e s))"
            by (simp add: acc_virt_set_value asm0(2))
        qed
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) m C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"        
        by (metis \<open>get_vm \<omega> (l, field_val) = 1\<close> \<open>sep_algebra_class.stable \<omega>\<close> asm1(2) binary_mask_def fst_conv get_vh_vm_set_value(2) not_gr_0 one_neq_zero snd_conv stable_before_then_update_stable vstate_wf_imp)
    qed (simp)
    ultimately show ?thesis by blast
  qed (simp)
qed


subsection \<open>Rule assignment\<close>

(*
| RuleLocalAssign: "\<lbrakk> self_framing_and_typed (tcfe \<Delta> tys) A; framed_by_exp A e \<rbrakk> \<Longrightarrow> (tcfe \<Delta> tys) \<turnstile> [A] LocalAssign x e [post_substitute_var_assert x e A]"
*)
(*
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x \<mapsto> VInt (edenot e s)), h) \<rbrakk> \<Longrightarrow> \<langle>Cassign x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
*)

definition sub_pre where
  "sub_pre x e P = { (Ag s, \<tau>, \<omega>) |s \<tau> \<omega>. (Ag (s(x \<mapsto> VInt (edenot e s))), \<tau>, \<omega>) \<in> P }"

proposition rule_assign:
  "CSL (tcfe \<Delta> tys) (sub_pre x e P) (Cassign x e) P"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> sub_pre x e P" "sep_algebra_class.stable \<omega>"
  then have r: "(Ag (s(x \<mapsto> VInt (edenot e s))), \<tau>, \<omega>) \<in> P"
    by (simp add: sub_pre_def)
  show "safe (tcfe \<Delta> tys) (Suc n) (Cassign x e) s \<tau> \<omega> P"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Cassign x e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 P"
      by (metis asm0(2) asm1(2) asm1(3) fst_eqD r red_assign_cases safe_skip snd_eqD)
  qed (auto simp add: no_aborts_def)
qed



subsection \<open>Rule Alloc\<close>

definition set_perm_and_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> preal \<Rightarrow> 'a val option \<Rightarrow> 'a virtual_state" where
  "set_perm_and_value \<phi> hl p v = Abs_virtual_state ((get_vm \<phi>)(hl := p), (get_vh \<phi>)(hl := v))"

(* Not true, needs pre... *)
lemma wf_set_perm:
  assumes "p > 0 \<Longrightarrow> v \<noteq> None"
      and "p \<le> 1"
    shows "wf_pre_virtual_state ((get_vm \<phi>)(hl := p), (get_vh \<phi>)(hl := v))"
  by (smt (verit) EquiSemAuxLemma.gr_0_is_ppos assms(1) assms(2) fun_upd_apply get_vm_bound vstate_wf_imp wf_mask_simpleI wf_pre_virtual_stateI)

lemma update_perm_simps[simp]:
  assumes "p > 0 \<Longrightarrow> v \<noteq> None"
      and "p \<le> 1"
    shows "get_vh (set_perm_and_value \<phi> hl p v) = (get_vh \<phi>)(hl := v)"
      and "get_vm (set_perm_and_value \<phi> hl p v) = (get_vm \<phi>)(hl := p)"
  unfolding set_perm_and_value_def
  apply (metis Abs_virtual_state_inverse assms get_vh_def mem_Collect_eq snd_conv wf_set_perm)
  by (metis Abs_virtual_state_inverse assms fst_conv get_vm_def mem_Collect_eq wf_set_perm)

lemma stable_set_perm_and_value:
  assumes "p > 0 \<longleftrightarrow> v \<noteq> None"
      and "stable \<omega>"
      and "p \<le> 1"
    shows "stable (set_perm_and_value \<omega> hl p v)"
proof (rule stable_virtual_stateI)
  show "\<And>hla. get_vh (set_perm_and_value \<omega> hl p v) hla \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm (set_perm_and_value \<omega> hl p v) hla"
    by (metis EquiSemAuxLemma.gr_0_is_ppos assms(1) assms(2) assms(3) fun_upd_apply stable_virtual_state_def update_perm_simps(1) update_perm_simps(2))
qed


lemma alloc_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "get_vh \<omega>f l = None"
      and "p > 0 \<Longrightarrow> v \<noteq> None"
      and "p \<le> 1"
    shows "Some (set_perm_and_value \<omega>' l p v) = set_perm_and_value \<omega> l p v \<oplus> \<omega>f"
proof (rule plus_virtual_stateI)
  show "Some (get_vh (set_perm_and_value \<omega>' l p v)) = get_vh (set_perm_and_value \<omega> l p v) \<oplus> get_vh \<omega>f"
    by (smt (verit, ccfv_threshold) assms commutative fun_upd_apply plus_funE plus_funI plus_option.simps(1) update_perm_simps(1) vstate_add_iff)
  show "Some (get_vm (set_perm_and_value \<omega>' l p v)) = get_vm (set_perm_and_value \<omega> l p v) \<oplus> get_vm \<omega>f"
    apply (rule plus_funI)
    by (smt (verit, ccfv_threshold) SepAlgebra.plus_preal_def add.right_neutral assms fun_upd_apply get_vm_additive not_gr_0 plus_funE update_perm_simps(2) vstate_wf_imp)
qed

lemma in_emp_then_zero_mask:
  assumes "\<omega> \<in> emp"
  shows "get_m \<omega> l = 0"
  using assms unfolding emp_def apply simp
  by (metis core_charact_equi(2) core_structure(1) get_m_stabilize zero_mask_def)

lemma in_emp_then_zero_vmask:
  assumes "\<omega> \<in> emp"
  shows "get_vm \<omega> l = 0"
  using assms unfolding emp_def apply simp
  by (metis core_structure(1) vstate_stabilize_structure(1) zero_mask_def)


lemma in_emp_then_empty_heap:
  assumes "\<omega> \<in> emp"
  shows "get_h \<omega> l = None"
  using assms unfolding emp_def apply simp
  by (metis assms in_emp_then_zero_mask norm_preal(1) norm_preal(4) stabilize_is_stable stable_get_state stable_virtual_state_def)

lemma in_emp_then_empty_vheap:
  assumes "\<omega> \<in> emp"
  shows "get_vh \<omega> l = None"
  using assms unfolding emp_def apply simp
  by (metis core_structure(1) core_structure(2) empty_heap_def get_vm_stabilize stabilize_is_stable stable_virtual_state_def uu_get(2) vstate_wf_ppos)


lemma p_between_0_and_1_then_min:
  assumes "p \<le> 1"
  shows "p = PosReal.pmin 1 p"
  by (simp add: assms inf_absorb2)


lemma in_emp_set_perm_value_acc_virt:
  assumes "\<omega> \<in> emp"
      and "0 < p \<and> p \<le> 1"
  shows "set_perm_and_value \<omega> hl p (Some v) = acc_virt hl p v"
proof (rule virtual_state_ext)
  show "get_vm (set_perm_and_value \<omega> hl p (Some v)) = get_vm (acc_virt hl p v)"
    apply (simp add: assms)
    apply (rule ext)
    apply simp
    apply (rule conjI)
    using p_between_0_and_1_then_min assms apply simp
    using assms(1) in_emp_then_zero_vmask by blast
  show "get_vh (set_perm_and_value \<omega> hl p (Some v)) = get_vh (acc_virt hl p v)"
    using assms(1) assms(2) in_emp_then_empty_vheap by fastforce
qed

lemma in_emp_smaller:
  assumes "\<omega> \<in> emp"
  shows "get_state \<omega> \<in> emp"
  using assms unfolding emp_def apply simp
  by (metis core_charact_equi(2) get_state_stabilize)

proposition rule_alloc:
  assumes "r \<notin> fvE e"
  shows "CSL (tcfe \<Delta> tys) emp (Calloc r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n :: nat
  fix s :: "'a stack"
  fix \<tau> :: "'a ag_trace"
  fix \<omega> :: "'a virtual_state"
  assume asm: "sep_algebra_class.stable \<omega>" "(Ag s, \<tau>, \<omega>) \<in> emp"


  show "safe (tcfe \<Delta> tys) (Suc n) (Calloc r e) s \<tau> \<omega> (full_ownership_with_val r e)"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    assume "\<langle>Calloc r e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"
    proof (rule red_alloc_cases)
      fix sa h l
      assume asm1: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "(l, field_val) \<notin> dom h"
        "\<sigma>' = (sa(r \<mapsto> VRef (Address l)), h((l, field_val) \<mapsto> VInt (edenot e sa)))"
      then have r: "Some (set_perm_and_value \<omega>0' (l, field_val) 1 (Some (VInt (edenot e s))))
  = set_perm_and_value \<omega> (l, field_val) 1 (Some (VInt (edenot e s))) \<oplus> \<omega>f"
        using alloc_helper
        by (smt (verit, ccfv_threshold) EquiSemAuxLemma.gr_0_is_ppos EquiViper.add_masks_def Pair_inject \<open>sep_algebra_class.stable \<omega>\<close> asm0(1) asm0(2) asm0(3) binary_mask_and_stable_then_mk_virtual comm_monoid_add_class.add_0 leI mk_virtual_state_simps(1) option.discI order_less_imp_le padd_pos pperm_pgt_pnone stable_sum stable_virtual_state_def vstate_add_iff)
      let ?\<omega>1 = "set_perm_and_value \<omega> (l, field_val) 1 (Some (VInt (edenot e s)))"
      let ?\<omega>1' = "set_perm_and_value \<omega>0' (l, field_val) 1 (Some (VInt (edenot e s)))"

      have "sep_algebra_class.stable ?\<omega>1"
        by (simp add: \<open>sep_algebra_class.stable \<omega>\<close> pperm_pnone_pgt stable_set_perm_and_value)
      moreover have "binary_mask ?\<omega>1'"
      proof (rule binary_maskI)
        fix la show "get_vm (set_perm_and_value \<omega>0' (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) la = PosReal.pnone \<or>
          get_vm (set_perm_and_value \<omega>0' (l, field_val) PosReal.pwrite (Some (VInt (edenot e s)))) la = PosReal.pwrite"
          by (metis asm0(3) binary_mask_def dual_order.refl fun_upd_def option.simps(3) update_perm_simps(2))
      qed
      moreover have "\<sigma>' = concretize (fst \<sigma>') ?\<omega>1'"
        using asm1(1) asm1(4) by auto
      moreover have "(Ag (fst \<sigma>'), \<tau>, ?\<omega>1) \<in> full_ownership_with_val r e"
      proof (rule in_full_ownership_with_val[of "(fst \<sigma>')" r l])
        show "fst \<sigma>' r = Some (VRef (Address l))"
          by (simp add: asm1(4))
        have "edenot e (fst \<sigma>') = edenot e s"
          using asm1(1) asm1(4) assms by auto
        then show "set_perm_and_value \<omega> (l, field_val) 1 (Some (VInt (edenot e s))) = acc_virt (l, field_val) (Abs_preal 1) (VInt (edenot e (fst \<sigma>')))"
          using in_emp_set_perm_value_acc_virt[of \<omega> 1 "(l, field_val)" "VInt (edenot e s)"] in_emp_smaller[OF asm(2)]
          using one_preal.abs_eq preal_not_0_gt_0 by force
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (full_ownership_with_val r e)"
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
    by (metis all_pos erase_perm_and_value_def order_less_irrefl set_perm_and_value_def update_perm_simps(2))
  show "get_vh (erase_perm_and_value \<phi> hl) = (get_vh \<phi>)(hl := None)"
    by (metis all_pos erase_perm_and_value_def pperm_pgt_pnone set_perm_and_value_def update_perm_simps(1))
qed


lemma free_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "sep_algebra_class.stable \<omega>f"
      and "get_vm \<omega> hl = 1"
    shows "Some (erase_perm_and_value \<omega>' hl) = erase_perm_and_value \<omega> hl \<oplus> \<omega>f"
proof -
  have asm: "get_vm \<omega>' hl \<le> 1"
    using get_vm_bound by blast
  then have "get_vm \<omega>' hl = 1"
    by (simp add: EquiViper.add_masks_def antisym assms(1) assms(3) get_vm_additive pos_perm_class.sum_larger)
  then have "get_vm \<omega>f hl = 0"
    by (smt (verit, ccfv_threshold) EquiViper.add_masks_def PosReal.ppos.rep_eq assms(1) assms(3) get_vm_additive gr_0_is_ppos not_gr_0 plus_preal.rep_eq)
  then have "get_vh \<omega>f hl = None"
    using EquiSemAuxLemma.gr_0_is_ppos assms(2) pperm_pgt_pnone stable_virtual_state_def by blast
  show ?thesis
  proof (rule plus_virtual_stateI)
    show "Some (get_vh (erase_perm_and_value \<omega>' hl)) = get_vh (erase_perm_and_value \<omega> hl) \<oplus> get_vh \<omega>f"
      by (smt (verit, ccfv_SIG) \<open>get_vh \<omega>f hl = None\<close> assms(1) erase_perm_and_value_simps(2) fun_upd_apply partial_heap_same_sum plus_funE plus_funI vstate_add_iff)
    show "Some (get_vm (erase_perm_and_value \<omega>' hl)) = get_vm (erase_perm_and_value \<omega> hl) \<oplus> get_vm \<omega>f"
      by (smt (verit, ccfv_threshold) \<open>get_vm \<omega>f hl = 0\<close> assms(1) erase_perm_and_value_simps(1) fun_plus_iff fun_upd_apply get_vm_additive zero_mask_def zero_mask_identity)
  qed
qed

lemma stable_erase_perm_value:
  assumes "sep_algebra_class.stable \<omega>"
  shows "sep_algebra_class.stable (erase_perm_and_value \<omega> hl)"
  by (metis all_pos assms erase_perm_and_value_def linorder_not_le set_perm_and_value_def stable_set_perm_and_value)

lemma binary_mask_erase_perm_value:
  assumes "binary_mask \<omega>"
  shows "binary_mask (erase_perm_and_value \<omega> hl)"
  by (metis assms binary_mask_def erase_perm_and_value_simps(1) fun_upd_def)

proposition rule_free:
  "CSL (tcfe \<Delta> tys) (full_ownership r) (Cfree r) UNIV"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> full_ownership r" "sep_algebra_class.stable \<omega>" "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
  then obtain l v where r0: "s r = Some (VRef (Address l))" "\<omega> = acc_virt (l, field_val) (Abs_preal 1) (VInt v)"
    unfolding full_ownership_def by fastforce
  then have r: "get_vm \<omega> (l, field_val) = 1"
    by (simp add: one_preal.abs_eq)
  show "safe (tcfe \<Delta> tys) (Suc n) (Cfree r) s \<tau> \<omega> UNIV"
  proof (rule safeI_alt)
    show "accesses (Cfree r) s \<subseteq> read_dom \<omega>"
      by (simp add: in_read_dom_write_dom(1) r r0(1))
    show "writes (Cfree r) s \<subseteq> write_dom \<omega>"
      by (simp add: in_read_dom_write_dom(2) r r0(1))
    fix \<omega>0' \<omega>f
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    show "aborts (Cfree r) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts (Cfree r) (concretize s \<omega>0')"
      then show False
      proof (rule aborts_free_elim)
        show "fst (concretize s \<omega>0') r = Some (VRef Null) \<Longrightarrow> False"
          by (simp add: r0(1))
        fix hl assume "fst (concretize s \<omega>0') r = Some (VRef (Address hl))"
        then have "hl = l"
          by (simp add: r0(1))
        moreover have "get_vm \<omega>0' (l, field_val) \<ge> 1"
          by (simp add: EquiViper.add_masks_def asm1(2) get_vm_additive pos_perm_class.sum_larger r)
        moreover assume "(hl, field_val) \<notin> dom (snd (concretize s \<omega>0'))"
        ultimately show False
          by (metis domIff linorder_not_less pperm_pnone_pgt sndI vstate_wf_imp zero_neq_one)
      qed
    qed
    fix C' \<sigma>'
    assume "\<langle>Cfree r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (UNIV)"
    proof (rule red_free_cases)
      fix sa h l'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa, h((l', field_val) := None))"
        "sa r = Some (VRef (Address l'))"
      let ?\<omega>1 = "erase_perm_and_value \<omega> (l', field_val)"
      let ?\<omega>1' = "erase_perm_and_value \<omega>0' (l', field_val)"
      have "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, ?\<omega>1)"
        unfolding TypedEqui.typed_def
      proof
        show "TypedEqui.typed_store (tcfe \<Delta> tys) (get_store (Ag (fst \<sigma>'), \<tau>, erase_perm_and_value \<omega> (l', field_val)))"
          by (metis TypedEqui.typed_def asm0(3) asm2(1) asm2(3) fst_conv get_simps_unfolded(1))
        show "well_typed (custom_context (tcfe \<Delta> tys)) (get_abs_state (Ag (fst \<sigma>'), \<tau>, erase_perm_and_value \<omega> (l', field_val)))"
        proof (rule well_typedI)
          show "Instantiation.well_typed_heap (custom_context (tcfe \<Delta> tys)) (snd (get_abs_state (Ag (fst \<sigma>'), \<tau>, erase_perm_and_value \<omega> (l', field_val))))"
            by (metis TypedEqui.typed_def asm0(3) erase_perm_and_value_simps(2) get_abs_state_def heap_typed_remove snd_conv well_typedE(1))
          show "\<And>l \<phi>. the_ag (fst (get_abs_state (Ag (fst \<sigma>'), \<tau>, erase_perm_and_value \<omega> (l', field_val)))) l = Some \<phi> \<Longrightarrow>
           Instantiation.well_typed_heap (custom_context (tcfe \<Delta> tys)) \<phi>"
            by (metis TypedEqui.typed_def asm0(3) fst_conv get_abs_state_def snd_conv well_typedE(2))
        qed
      qed
      then have "snd \<sigma>' = get_vh ?\<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> ?\<omega>1 (UNIV)"
        using asm2(1) asm2(2) asm2(3) by auto
      moreover have "Some ?\<omega>1' = ?\<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable ?\<omega>1"
        using asm0(2) asm1(1) asm1(2) asm2(1) asm2(4) free_helper r r0(1) stable_erase_perm_value by fastforce
      moreover have "binary_mask ?\<omega>1'"
        by (simp add: asm1(3) binary_mask_erase_perm_value)        
      ultimately show
        "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (UNIV)"
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


(*
ConcreteSemantics.post_substitute_var_assert x (semantify_heap_loc r) P"
*)
thm ConcreteSemantics.post_substitute_var_assert_def
thm ConcreteSemantics.substitute_var_state_def

definition read_result :: "'a equi_state set \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'a equi_state set" where
  "read_result A x r = { TypedEqui.assign_var_state x (get_h \<omega> (l, field_val)) \<omega> |\<omega> l.
  \<omega> \<in> A \<and> get_store \<omega> r = Some (VRef (Address l)) }"

definition simple_read_result where
  "simple_read_result x r = { \<omega> |\<omega> l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_store \<omega> x = get_h \<omega> (l, field_val) }"

definition read_perm where
  "read_perm r = { \<omega> |\<omega> l v. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) > 0 \<and> get_h \<omega> (l, field_val) = Some v}"



lemma assign_var_state_refl:
  "\<omega> = TypedEqui.assign_var_state x (get_store \<omega> x) \<omega>"
  by (simp add: AbstractSemantics.full_state_ext TypedEqui.assign_var_state_def)

lemma get_store_assign_var[simp]:
  "get_store (TypedEqui.assign_var_state x v \<omega>) = (get_store \<omega>)(x := v)"
  by (simp add: TypedEqui.assign_var_state_def)

lemma fvA_assign_var_state:
  assumes "x \<notin> fvA (tcfe \<Delta> tys) A"
      and "\<omega> \<in> A"
      and "TypedEqui.typed (tcfe \<Delta> tys) \<omega>"
      and "variables (tcfe \<Delta> tys) x = Some ty"
      and "v \<in> ty"
    shows "TypedEqui.assign_var_state x (Some v) \<omega> \<in> A"
  apply (rule fvA_agrees_better[of "tcfe \<Delta> tys" _ \<omega>])
        apply (simp_all add: assms)
     apply (simp add: agrees_search(4) assms(1))
  apply (simp add: TypedEqui.assign_var_state_def)
  apply (simp add: TypedEqui.assign_var_state_def)
  by (simp add: TypedEqui.typed_state_axioms assms(3) assms(4) assms(5) typed_state.typed_assign_var)


lemma fvA_assign_var_state_reciprocal:
  assumes "x \<notin> fvA (tcfe \<Delta> tys) A"
      and "TypedEqui.assign_var_state x (Some v) \<omega> \<in> A"
      and "TypedEqui.typed (tcfe \<Delta> tys) \<omega>"
      and "variables (tcfe \<Delta> tys) x = Some ty"
      and "v \<in> ty"
    shows "\<omega> \<in> A"
  apply (rule fvA_agrees_better[of "tcfe \<Delta> tys" _ "TypedEqui.assign_var_state x (Some v) \<omega>"])
        apply (simp_all add: assms)
  apply (simp add: agreesC agrees_search(4) assms(1))
  apply (simp add: TypedEqui.assign_var_state_def)
   apply (simp add: TypedEqui.assign_var_state_def)
  by (simp add: TypedEqui.typed_state_axioms assms(3) assms(4) assms(5) typed_state.typed_assign_var)


(*
lemma read_result_simple_same:
  assumes "x \<notin> fvA (tcfe \<Delta> tys) A"
      and "x \<noteq> r"
      and "TypedEqui.typed_store (tcfe \<Delta> tys) (get_store \<omega>)"
      and "variables (tcfe \<Delta> tys) x = Some ty"
      and "v \<in> ty"
  shows "read_result A x r = A \<inter> simple_read_result x r" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<omega>' assume asm0: "\<omega>' \<in> read_result A x r"
    then obtain \<omega> l where "\<omega>' = TypedEqui.assign_var_state x (get_h \<omega> (l, field_val)) \<omega>"
      "\<omega> \<in> A" "get_store \<omega> r = Some (VRef (Address l))"
      using read_result_def by auto
    then have "\<omega>' \<in> A"
      using assms fvA_assign_var_state by blast
    moreover have "\<omega>' \<in> simple_read_result x r"
      unfolding simple_read_result_def
      by (smt (verit, ccfv_threshold) CollectI TypedEqui.assign_var_state_def \<open>\<omega>' = TypedEqui.assign_var_state x (get_h \<omega> (l, field_val)) \<omega>\<close> \<open>get_store \<omega> r = Some (VRef (Address l))\<close> assms(2) fun_upd_other fun_upd_same get_state_set_store get_store_assign_var)
    ultimately show "\<omega>' \<in> ?B"
      by blast
  qed
  show "?B \<subseteq> ?A"
  proof
    fix \<omega> assume "\<omega> \<in> A \<inter> simple_read_result x r"
    then obtain l where "get_store \<omega> r = Some (VRef (Address l)) \<and> get_store \<omega> x = get_h \<omega> (l, field_val)"
      unfolding simple_read_result_def by blast
    then have "\<omega> = TypedEqui.assign_var_state x (get_h \<omega> (l, field_val)) \<omega>"
      by (metis assign_var_state_refl)
    then show "\<omega> \<in> ?A"
      by (smt (verit, del_insts) CollectI Int_iff \<open>\<omega> \<in> A \<inter> simple_read_result x r\<close> \<open>get_store \<omega> r = Some (VRef (Address l)) \<and> get_store \<omega> x = get_h \<omega> (l, field_val)\<close> read_result_def)
  qed
qed
*)


proposition rule_read:
  assumes "A \<subseteq> read_perm r"
    shows "CSL (tcfe \<Delta> tys) A (Cread x r) (read_result A x r)"
proof (rule CSL_I)
  fix n s \<tau> \<omega>
  assume asm0: "(Ag s, \<tau>, \<omega>) \<in> A" "sep_algebra_class.stable \<omega>"
  then obtain l v where lv_def: "s r = Some (VRef (Address l))" "get_vm \<omega> (l, field_val) > 0" "get_vh \<omega> (l, field_val) = Some v"
    using assms(1) unfolding read_perm_def by force
  show "safe (tcfe \<Delta> tys) (Suc n) (Cread x r) s \<tau> \<omega> (read_result A x r)"
  proof (rule safeI_alt)
    show "accesses (Cread x r) s \<subseteq> read_dom \<omega>"
      by (simp add: lv_def(1) lv_def(2) read_dom_def)
    fix \<omega>0' \<omega>f
    assume asm1: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
    then have "get_vh \<omega>0' (l, field_val) = Some v"
      using lv_def(3) read_helper by blast
    then show "aborts (Cread x r) (concretize s \<omega>0') \<Longrightarrow> False"
      using lv_def(1) by auto

    fix C' \<sigma>'
    assume "\<langle>Cread x r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (read_result A x r)"
    proof (rule red_read_cases)
      fix sa h l' v'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa(x \<mapsto> VInt v'), h)" "sa r = Some (VRef (Address l'))"
      "h (l', field_val) = Some (VInt v')"
      then have "l = l' \<and> v = VInt v'"
        using \<open>get_vh \<omega>0' (l, field_val) = Some v\<close> lv_def(1) by auto
      moreover have "(Ag (s(x := Some v)), \<tau>, \<omega>) \<in> read_result A x r"
        unfolding read_result_def TypedEqui.assign_var_state_def
        using asm0(1) lv_def(1) lv_def(3) by force
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'
        \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (read_result A x r)"
        using asm0(2) asm1(2) asm1(3) asm2(1) asm2(2) asm2(3) by auto
    qed
  qed (simp_all)
qed


subsection \<open>Force typing\<close>

lemma can_convert_safe_to_stabilize:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> A"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "stable (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys C"
  shows "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> (Stabilize A)"
  using assms
proof (induct n arbitrary: C s \<omega>)
  case (Suc n)
  show ?case
    apply (rule safeI)
    using Suc.prems(1) assms(2)
        apply (simp add: Suc.prems(3) already_stable)
        apply (meson Suc.prems(1) safeE(2))
    apply (meson Suc.prems(1) safeE(3))
    using Suc.prems(1) safeE(4) apply blast
  proof -
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
       "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')" "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>1 \<omega>1' where
       r: "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'" "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 A"
      using Suc.prems(1) safeE(5) by blast
    have "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Stabilize A)"
      using r(2)
    proof (rule Suc(1))
      show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
        unfolding TypedEqui.typed_def
      proof
        show "TypedEqui.typed_store (tcfe \<Delta> tys) (get_store (Ag (fst \<sigma>'), \<tau>, \<omega>1))"
          by (meson Suc.prems(4) TypedEqui.typed_def asm0(1) asm0(4) asm0(5) greater_def r(1) stable_sum typed_equi_red typed_smaller_state)
        show "well_typed (custom_context (tcfe \<Delta> tys)) (get_abs_state (Ag (fst \<sigma>'), \<tau>, \<omega>1))"
          by (meson Suc.prems(4) TypedEqui.typed_def asm0(1) asm0(4) asm0(5) greater_def r(1) stable_sum typed_equi_red typed_smaller_state)
      qed
      show "sep_algebra_class.stable (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
        using r(1) stable_get_state by fastforce
      show "well_typed_cmd tys C'"
        by (metis Suc.prems(4) asm0(5) well_typed_cmd_red)
    qed
    then show "\<exists>\<omega>1 \<omega>1'.
          Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Stabilize A)"
      using r by blast
  qed
qed (simp)

lemma can_convert_to_Stabilize:
  assumes "CSL (tcfe \<Delta> tys) A C B"
      and "well_typed_cmd tys C"
    shows "CSL (tcfe \<Delta> tys) (Stabilize A) C (Stabilize B)"
  apply (rule CSL_I)
  by (metis CSL_E already_stable assms(1) assms(2) can_convert_safe_to_stabilize get_simps_unfolded(2) in_Stabilize stable_get_state)
(*
abbreviation inhalify where
  "inhalify P \<equiv> Set.filter (typed tcfe \<circ> stabilize) P"
*)
lemma can_convert_safe_to_inhalify:
  assumes "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> A"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
      and "stable (Ag s, \<tau>, \<omega>)"
      and "well_typed_cmd tys C"
  shows "safe (tcfe \<Delta> tys) n C s \<tau> \<omega> (Set.filter (typed (tcfe \<Delta> tys) \<circ> stabilize) A)"
  using assms
proof (induct n arbitrary: C s \<omega>)
  case (Suc n)
  show ?case
    apply (rule safeI)
    using Suc.prems(1) Suc.prems(2) TypedEqui.typed_state_then_stabilize_typed apply auto[1]
    using Suc.prems(1) safeE(2) apply blast
    using Suc.prems(1) safeE(3) apply blast
    using Suc.prems(1) safeE(4) apply blast
  proof -
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "sep_algebra_class.stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "binary_mask \<omega>0'"
       "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>0')" "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>1 \<omega>1' where
       r: "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1'" "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 A"
      using Suc.prems(1) safeE(5) by blast
    have "safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Set.filter (typed (tcfe \<Delta> tys) \<circ> stabilize) A)"
      using r(2)
    proof (rule Suc(1))
      show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
        unfolding TypedEqui.typed_def
      proof
        show "TypedEqui.typed_store (tcfe \<Delta> tys) (get_store (Ag (fst \<sigma>'), \<tau>, \<omega>1))"
          by (metis ConcreteSemantics.get_store_Ag_simplifies Suc.prems(4) TypedEqui.typed_store_def abs_type_context.select_convs(1) asm0(4) asm0(5) fst_conv red_keeps_typed_store type_ctxt_front_end_def typed_then_store_typed)
        show "well_typed (custom_context (tcfe \<Delta> tys)) (get_abs_state (Ag (fst \<sigma>'), \<tau>, \<omega>1))"
          by (meson Suc.prems(4) TypedEqui.typed_def asm0(1) asm0(4) asm0(5) greater_def r(1) stable_sum typed_equi_red typed_smaller_state)
      qed
      show "sep_algebra_class.stable (Ag (fst \<sigma>'), \<tau>, \<omega>1)"
        using r(1) stable_get_state by fastforce
      show "well_typed_cmd tys C'"
        by (metis Suc.prems(4) asm0(5) well_typed_cmd_red)
    qed
    then show "\<exists>\<omega>1 \<omega>1'.
          Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and>
          sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 (Set.filter (typed (tcfe \<Delta> tys) \<circ> stabilize) A)"
     using r by blast
  qed
qed (simp)

lemma can_inhalify:
  assumes "CSL (tcfe \<Delta> tys) A C B"
      and "well_typed_cmd tys C"
    shows "CSL (tcfe \<Delta> tys) A C (Set.filter (typed (tcfe \<Delta> tys) \<circ> stabilize) B)"
  apply (rule CSL_I)
  by (metis CSL_E assms(1) assms(2) can_convert_safe_to_inhalify get_simps_unfolded(2) stable_get_state)


lemma subset_entails:
  assumes "P \<subseteq> Q"
  shows "ConcreteSemantics.entails_typed \<Delta> P Q"
  using assms ConcreteSemantics.entails_typed_def by blast

section \<open>Actual logic\<close>

inductive CSL_syn :: "'a concrete_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> cmd \<Rightarrow> 'a equi_state set \<Rightarrow> bool" 
  ("_ \<turnstile>CSL [_] _ [_]" [51,0,0] 81)
  where
  RuleSkip: "\<Delta> \<turnstile>CSL [P] Cskip [P]"
| RuleFrame: "\<lbrakk> \<Delta> \<turnstile>CSL [P] C [Q]; disjoint (fvA \<Delta> R) (wrC C); self_framing P; self_framing R\<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile>CSL [P \<otimes> R] C [Q \<otimes> R]"
| RulePar: "\<lbrakk> disjoint (fvC C1 \<union> fvA \<Delta> Q1) (wrC C2); disjoint (fvC C2 \<union> fvA \<Delta> Q2) (wrC C1); self_framing P1;
  self_framing P2;
    \<Delta> \<turnstile>CSL [P1] C1 [Q1]; \<Delta> \<turnstile>CSL [P2] C2 [Q2] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [P1 \<otimes> P2] {_} C1 {_} || {_} C2 {_} [Q1 \<otimes> Q2]"
| RuleSeq: "\<lbrakk> \<Delta> \<turnstile>CSL [P] C1 [Q]; \<Delta> \<turnstile>CSL [Q] C2 [R] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [P] Cseq C1 C2 [R]"
(*
| RuleCons: "\<lbrakk>\<Delta> \<turnstile>CSL [P] C [Q]; P' \<subseteq> P; Q \<subseteq> Q'\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [P'] C [Q']"
*)
| RuleIf: "\<lbrakk> \<Delta> \<turnstile>CSL [P \<inter> assertify_bexp b] C1 [Q]; \<Delta> \<turnstile>CSL [P \<inter> assertify_bexp (Bnot b)] C2 [Q]\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [P] Cif b C1 C2 [Q]"
| RuleWhile: "\<lbrakk> \<Delta> \<turnstile>CSL [I \<inter> assertify_bexp b] C [I] \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [I] (Cwhile b I' C) [I \<inter> assertify_bexp (Bnot b)]"
| RuleWrite: "\<Delta> \<turnstile>CSL [full_ownership r] Cwrite r e [full_ownership_with_val r e]"
| RuleAssign: "\<Delta> \<turnstile>CSL [sub_pre x e P] Cassign x e [P]"
| RuleAlloc: "r \<notin> fvE e \<Longrightarrow> \<Delta> \<turnstile>CSL [emp] Calloc r e [full_ownership_with_val r e]"
| RuleFree: "\<Delta> \<turnstile>CSL [full_ownership r] Cfree r [UNIV]"
| RuleRead: "\<lbrakk> A \<subseteq> read_perm r\<rbrakk> \<Longrightarrow> \<Delta> \<turnstile>CSL [A] Cread x r [read_result A x r]"

| RuleConsTyped: "\<lbrakk>\<Delta> \<turnstile>CSL [P] C [Q]; ConcreteSemantics.entails_typed \<Delta> P' P; ConcreteSemantics.entails_typed \<Delta> Q Q'\<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile>CSL [P'] C [Q']"

| RuleStabilizeTyped: "\<Delta> \<turnstile>CSL [P] C [Q] \<Longrightarrow> \<Delta> \<turnstile>CSL [Stabilize P] C [Stabilize Q]"
| RuleInhalify: "\<Delta> \<turnstile>CSL [P] C [Q] \<Longrightarrow> \<Delta> \<turnstile>CSL [P] C [Set.filter (typed \<Delta> \<circ> stabilize) Q]"


theorem CSL_sound:
  assumes "\<Gamma> \<turnstile>CSL [P] C [Q]"
      and "well_typed_cmd tys C"
      and "\<Gamma> = tcfe \<Delta> tys"
    shows "CSL (tcfe \<Delta> tys) P C Q"
  using assms
  apply (induct rule: CSL_syn.induct)
  by (simp_all add: rule_skip rule_seq rule_conseq_typed rule_if rule_while
      rule_write rule_assign rule_alloc rule_free rule_read frame_rule rule_par can_convert_to_Stabilize can_inhalify)



subsection \<open>Adequacy\<close>

inductive n_steps where
  NoStep: "n_steps C \<sigma> C \<sigma>"
| OneStep: "\<lbrakk> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C'', \<sigma>''\<rangle>; n_steps C'' \<sigma>'' C' \<sigma>' \<rbrakk> \<Longrightarrow>  n_steps C \<sigma> C' \<sigma>'"

definition assertify_state_exp :: "(('a store \<times> 'a partial_heap) \<Rightarrow> bool) \<Rightarrow> 'a equi_state set" where
  "assertify_state_exp P = { (Ag s, Ag Map.empty, h) |s h. P (s, get_vh h) }"

lemma in_assertify_equiv:
  "(Ag s, Ag Map.empty, \<omega>) \<in> assertify_state_exp P \<longleftrightarrow> P (s, get_vh \<omega>)"
  by (simp add: assertify_state_exp_def)

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


lemma safeE_no_frame:
  assumes "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> \<omega> Q"
      and "binary_mask \<omega>"
      and "\<langle>C, concretize s \<omega>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, \<omega>)"
    shows "\<exists>\<omega>1. sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1 \<and> snd \<sigma>' = get_vh \<omega>1 \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
proof -
  obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> uu \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1' \<and> snd \<sigma>' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
    using safeE(5)[OF assms(1), of uu \<omega> C' \<sigma>']
    using assms stable_uu uu_neutral by blast
  then show ?thesis
    by (metis pure_def stable_and_sum_pure_same uu_neutral)
qed



lemma safeE_no_frame_alt:
  assumes "safe (tcfe \<Delta> tys) (Suc n) C s \<tau> (mk_virtual_state h) Q"
      and "\<langle>C, (s, h)\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, \<tau>, (mk_virtual_state h))"
    shows "\<exists>\<omega>1. sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1 \<and> snd \<sigma>' = get_vh \<omega>1 \<and> safe (tcfe \<Delta> tys) n C' (fst \<sigma>') \<tau> \<omega>1 Q"
  by (metis assms mk_virtual_state_charact(2) mk_virtual_state_simps(2) safeE_no_frame)



lemma safe_n_steps:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "s = fst \<sigma>"
      and "get_vh \<omega> = snd \<sigma>"
      and "binary_mask \<omega>"
      and "sep_algebra_class.stable \<omega>"       
      and "\<And>n. safe (tcfe \<Delta> tys) n C s (Ag Map.empty) \<omega> (assertify_state_exp Q)"
      and "TypedEqui.typed (tcfe \<Delta> tys) (Ag s, Ag Map.empty, \<omega>)"
      and "well_typed_cmd tys C"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  using assms
proof (induct arbitrary: s \<omega> rule: n_steps.induct)
  case (NoStep C \<sigma>)
  then have r: "safe (tcfe \<Delta> tys) (Suc 0) C s (Ag Map.empty) \<omega> (assertify_state_exp Q)"
    by presburger
  then show ?case
    using safeE(1)[OF r] no_abortsE[OF safeE(4)[OF r], of \<omega> uu]
    using NoStep.prems(1) NoStep.prems(2) stable_uu uu_neutral
    using NoStep.prems(3) NoStep.prems(4)
    by (metis NoStep.prems(6) in_assertify_equiv surjective_pairing)
next
  case (OneStep C \<sigma> C'' \<sigma>'' C' \<sigma>')
  show "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  proof (rule OneStep(3)[of "fst \<sigma>''" "mk_virtual_state (snd \<sigma>'')"])
    fix n
    obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> uu \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1'"
      "snd \<sigma>'' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C'' (fst \<sigma>'') (Ag Map.empty) \<omega>1 (assertify_state_exp Q)"
      using safeE(5)[OF OneStep(8)[of "Suc n"], of uu \<omega> C'' \<sigma>'']
      using OneStep.hyps(1) OneStep.prems(1) OneStep.prems(2) OneStep.prems(3) stable_uu uu_neutral
      using OneStep.prems(6) by auto
    then show "safe (tcfe \<Delta> tys) n C'' (fst \<sigma>'') (Ag Map.empty) (mk_virtual_state (snd \<sigma>'')) (assertify_state_exp Q)"
      by (metis binary_mask_and_stable_then_mk_virtual pure_def stable_and_sum_pure_same uu_neutral)
    show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>''), Ag Map.empty, mk_virtual_state (snd \<sigma>''))"
      using OneStep.hyps(1) OneStep.prems(1) OneStep.prems(2) OneStep.prems(6) OneStep.prems(7) typed_equi_red
      by (metis \<open>Some \<omega>1' = \<omega>1 \<oplus> uu \<and> sep_algebra_class.stable \<omega>1 \<and> binary_mask \<omega>1'\<close> \<open>snd \<sigma>'' = get_vh \<omega>1' \<and> safe (tcfe \<Delta> tys) n C'' (fst \<sigma>'') (Ag Map.empty) \<omega>1 (assertify_state_exp Q)\<close> binary_mask_and_stable_then_mk_virtual option.inject prod.collapse uu_neutral)
    show "well_typed_cmd tys C''"
      by (metis OneStep.hyps(1) OneStep.prems(7) well_typed_cmd_red)
  qed (simp_all)
qed

lemma well_typedI_empty_trace:
  assumes "well_typed_heap \<Gamma> (snd \<omega>)"
      and "the_ag (fst \<omega>) = Map.empty"
    shows "well_typed \<Gamma> \<omega>"
  by (simp add: assms(1) assms(2) well_typed_def)

theorem adequacy:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "(tcfe \<Delta> tys) \<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
      and "well_typed_cmd tys C"
      and "TypedEqui.typed_store (tcfe \<Delta> tys) (fst \<sigma>)"
      and "heap_typed type_ctxt_heap (snd \<sigma>)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
proof (rule safe_n_steps[OF assms(1), where ?Q = Q])
  fix n
  have r:"TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>))"
    unfolding TypedEqui.typed_def
  proof
    show "well_typed (custom_context (tcfe \<Delta> tys)) (get_abs_state (Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>)))"
    proof (rule well_typedI_empty_trace)
      show "Instantiation.well_typed_heap (custom_context (tcfe \<Delta> tys)) (snd (get_abs_state (Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>))))"
        by (simp add: assms(6) get_abs_state_def type_ctxt_front_end_def)
      show "the_ag (fst (get_abs_state (Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>)))) = (\<lambda>x. None)"
        by (simp add: get_abs_state_def)
    qed
  qed (simp_all add: assms(5-6))
  show "safe (tcfe \<Delta> tys) n C (fst \<sigma>) (Ag (Map.empty)) (mk_virtual_state (snd \<sigma>)) (assertify_state_exp Q)"
  proof (rule CSL_E)
    show "CSL (tcfe \<Delta> tys) (assertify_state_exp P) C (assertify_state_exp Q)"
      using CSL_sound assms(2) assms(4) by blast
    show "(Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>)) \<in> assertify_state_exp P"
      by (simp add: assms(3) in_assertify_equiv)
  qed (simp_all add: r)
  show "TypedEqui.typed (tcfe \<Delta> tys) (Ag (fst \<sigma>), Ag (\<lambda>x. None), mk_virtual_state (snd \<sigma>))" using r by blast
  show "well_typed_cmd tys C"
    by (simp add: assms(4))
qed (simp_all add: assms)


end