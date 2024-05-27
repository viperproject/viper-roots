theory Instantiation           
  imports AbstractSemanticsProperties EquiViper EquiSemAuxLemma
begin

definition make_semantic_bexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'a equi_state bexp" where
  "make_semantic_bexp \<Delta> b \<omega> =
  (if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool True) then Some True
  else if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool False) then Some False
  else None)"

definition make_semantic_exp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> ('a equi_state, 'a val) exp" where
  "make_semantic_exp \<Delta> e \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v then Some (SOME v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) else None)"

definition make_semantic_rexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> ('a equi_state, address) exp" where
  "make_semantic_rexp \<Delta> r \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v))
  then Some (SOME v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v)))
  else None)"


definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" where
  "make_semantic_assertion \<Delta> A = { \<omega> |\<omega>. \<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> }"

fun make_semantic_vtyp :: "('a, 'a virtual_state) interp \<Rightarrow> vtyp \<Rightarrow> 'a val abs_vtyp" where
  "make_semantic_vtyp _ TInt = { VInt n |n. True }"
| "make_semantic_vtyp _ TBool = { VBool b |b. True }"
| "make_semantic_vtyp _ TPerm = { VPerm p |p. True }"
| "make_semantic_vtyp _ TRef = { VRef r |r. True }"

| "make_semantic_vtyp \<Delta> (TAbs ty) = undefined" (* { VAbs x |x. True }" *)
(*
TODO: Ignoring domains so far...
record ('v, 'a) interp =
  domains :: "'v \<Rightarrow> abs_type"
*)

datatype 'a custom =
  FieldAssign "('a equi_state, address) exp" field_ident "('a equi_state, 'a val) exp"
  | Label label

fun compile :: "('a, 'a virtual_state) interp \<Rightarrow> stmt \<Rightarrow> ('a equi_state, 'a val, 'a custom) abs_stmt"
  where
  "compile \<Delta> stmt.Skip = abs_stmt.Skip"

| "compile \<Delta> (stmt.If b C1 C2) = abs_stmt.If (make_semantic_bexp \<Delta> b) (compile \<Delta> C1) (compile \<Delta> C2)"
| "compile \<Delta> (stmt.Seq C1 C2) = abs_stmt.Seq (compile \<Delta> C1) (compile \<Delta> C2)"

(*
| "compile \<Delta> (stmt.Scope ty C) = abs_stmt.Scope (make_semantic_vtyp \<Delta> ty) (compile \<Delta> C)"
*)
| "compile \<Delta> (stmt.Havoc x) = abs_stmt.Havoc x"
| "compile \<Delta> (stmt.LocalAssign x e) = abs_stmt.LocalAssign x (make_semantic_exp \<Delta> e)"


| "compile \<Delta> (stmt.Inhale A) = abs_stmt.Inhale (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Exhale A) = abs_stmt.Exhale (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Assert A) = abs_stmt.Assert (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Assume A) = abs_stmt.Assume (make_semantic_assertion \<Delta> A)"

| "compile \<Delta> (stmt.Unfold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Fold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Package _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Apply _ _) = abs_stmt.Skip"

(* TODO: We can take the program as input, and emit the encodings *)
| "compile \<Delta> (stmt.MethodCall _ _ _) = undefined"
| "compile \<Delta> (stmt.While b I C) = undefined"
| "compile \<Delta> (stmt.Scope _ _) = undefined"

| "compile \<Delta> (stmt.FieldAssign r f e) = abs_stmt.Custom (FieldAssign (make_semantic_rexp \<Delta> r) f (make_semantic_exp \<Delta> e))"
| "compile \<Delta> (stmt.Label l) = abs_stmt.Custom (Label l)"



(*
(*
type_synonym 'a equi_state = "('a trace \<times> 'a virtual_state, 'a val) state"
*)
definition has_write_perm_only :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> bool" where
  "has_write_perm_only \<phi> hl \<longleftrightarrow> get_vm \<phi> hl = 1"
(* Could be expressed as "set_value" is frame-preserving
*)

definition has_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> bool" where
  "has_value \<phi> hl v \<longleftrightarrow> get_vh \<phi> hl = Some v"

*)



lemma sum_val_defined:
  assumes "Some a = x \<oplus> y"
      and "get_vh a hl = Some v"
    shows "get_vh x hl = Some v \<or> get_vh y hl = Some v"
proof (cases "get_vh x hl")
  case None
  then have "get_vh a hl = get_vh y hl"
    by (meson assms(1) result_sum_partial_functions(1) vstate_add_iff)
  then show ?thesis using assms by simp
next
  case (Some a)
  then have "a = v"
    by (metis assms(1) assms(2) greater_def option.inject read_field.elims read_field_mono)
  then show ?thesis
    using Some by fastforce
qed


definition set_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" where
  "set_value \<phi> hl v = Abs_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"

lemma set_value_charact[simp]:
  "get_vm (set_value \<phi> hl v) = get_vm \<phi>"
  "get_vh (set_value \<phi> hl v) = (get_vh \<phi>)(hl := Some v)"
proof -
  have "wf_pre_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"
    using gr_0_is_ppos vstate_wf_imp by fastforce
  then show "get_vm (set_value \<phi> hl v) = get_vm \<phi>"
    by (simp add: Abs_virtual_state_inverse get_vm_def set_value_def)
  show "get_vh (set_value \<phi> hl v) = (get_vh \<phi>)(hl \<mapsto> v)"
    by (metis Abs_virtual_state_inverse \<open>wf_pre_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl \<mapsto> v))\<close> get_vh_def mem_Collect_eq set_value_def snd_conv)
qed


definition owns_only where
  "owns_only \<omega> l \<longleftrightarrow> get_vm (get_state \<omega>) l = 1 \<and> (\<forall>l'. l' \<noteq> l \<longrightarrow> get_vm (get_state \<omega>) l' = 0)"

lemma owns_onlyI[intro]:
  assumes "get_vm (get_state \<omega>) l = 1"
      and "\<And>l'. l' \<noteq> l \<Longrightarrow> get_vm (get_state \<omega>) l' = 0"
    shows "owns_only \<omega> l"
  using assms(1) assms(2) owns_only_def by blast

definition remove_only where
  "remove_only \<omega> l = set_state \<omega> (Abs_virtual_state ((get_vm (get_state \<omega>))(l := 0), get_vh (get_state \<omega>)))"

lemma remove_only_charact:
  "get_vh (get_state (remove_only \<omega> l)) = get_vh (get_state \<omega>)"
  "get_vm (get_state (remove_only \<omega> l)) = (get_vm (get_state \<omega>))(l := 0)"
proof -
  have "wf_pre_virtual_state ((get_vm (get_state \<omega>))(l := 0), get_vh (get_state \<omega>))"
  proof (rule wf_pre_virtual_stateI)
    fix hl assume asm0: "PosReal.ppos (((get_vm (get_state \<omega>))(l := PosReal.pnone)) hl)"
    show "get_vh (get_state \<omega>) hl \<noteq> None"
    proof (cases "hl = l")
      case True
      then show ?thesis using ppos_def
        using asm0 gr_0_is_ppos by auto
    next
      case False
      then have "PosReal.ppos (get_vm (get_state \<omega>) hl)"
        using asm0 by force
      then show ?thesis
        by (simp add: gr_0_is_ppos vstate_wf_imp)
    qed
  qed
  then show "get_vh (get_state (remove_only \<omega> l)) = get_vh (get_state \<omega>)"
    by (simp add: Abs_virtual_state_inverse get_vh_def remove_only_def)
  show "get_vm (get_state (remove_only \<omega> l)) = (get_vm (get_state \<omega>))(l := PosReal.pnone)"
    by (metis (mono_tags, lifting) Abs_virtual_state_inverse \<open>wf_pre_virtual_state ((get_vm (get_state \<omega>))(l := PosReal.pnone), get_vh (get_state \<omega>))\<close> get_state_set_state get_vm_def mem_Collect_eq prod.sel(1) remove_only_def)
qed

lemma remove_only_core:
  "|remove_only \<omega> l| = |\<omega>|"
proof (rule full_state_ext)
  show "get_store |remove_only \<omega> l| = get_store |\<omega>|"
    by (simp add: core_charact(1) remove_only_def)
  show "get_abs_state |remove_only \<omega> l| = get_abs_state |\<omega>|"
    by (metis Rep_virtual_state_inverse agreement.exhaust_sel core_charact(2) core_def core_structure(1) core_structure(2) get_abs_state_def get_state_def get_trace_def get_trace_set_state get_vh_def get_vm_def prod.exhaust_sel remove_only_charact(1) remove_only_def)
qed


definition points_to where
  "points_to r = { \<omega> |\<omega> hl. r \<omega> = Some hl \<and> owns_only \<omega> hl }"
                                                 
abbreviation well_typed_concrete_heap where
  "well_typed_concrete_heap \<Gamma> h \<equiv> (\<forall>hl v. h hl = Some v \<longrightarrow> (\<exists>ty. \<Gamma> (snd hl) = Some ty \<and> v \<in> ty))"

lemma well_typed_concrete_heap_update:
  assumes "well_typed_concrete_heap \<Gamma> h"
      and "\<Gamma> (snd hl) = Some ty"
      and "v \<in> ty"
    shows "well_typed_concrete_heap \<Gamma> (h(hl \<mapsto> v))"
  using assms(1) assms(2) assms(3) by auto

lemma well_typed_concrete_heap_remove:
  assumes "well_typed_concrete_heap \<Gamma> h"
    shows "well_typed_concrete_heap \<Gamma> (h(hl := None))"
  using assms(1) by auto

definition well_typed_heap where
  "well_typed_heap \<Gamma> \<phi> \<longleftrightarrow> (well_typed_concrete_heap \<Gamma> (get_vh \<phi>))"

lemma well_typed_heapI[intro]:
  assumes "\<And>hl v. get_vh \<phi> hl = Some v \<Longrightarrow> (\<exists>ty. \<Gamma> (snd hl) = Some ty \<and> v \<in> ty)"
  shows "well_typed_heap \<Gamma> \<phi>"
  by (simp add: Instantiation.well_typed_heap_def assms)

lemma well_typed_heapE:
  assumes "well_typed_heap \<Gamma> \<phi>"
      and "get_vh \<phi> hl = Some v"
    shows "\<exists>ty. \<Gamma> (snd hl) = Some ty \<and> v \<in> ty"
  using assms
  unfolding well_typed_heap_def by blast

lemma well_typed_heap_sum:
  assumes "Some x = a \<oplus> b"
      and "well_typed_heap \<Gamma> a"
      and "well_typed_heap \<Gamma> b"
    shows "well_typed_heap \<Gamma> x"
  using Instantiation.well_typed_heap_def assms(1) assms(2) assms(3) sum_val_defined
  by blast

lemma well_typed_heap_smaller:
  assumes "a \<succeq> b"
      and "Instantiation.well_typed_heap \<Gamma> a"
    shows "Instantiation.well_typed_heap \<Gamma> b"
  by (metis Instantiation.well_typed_heap_def assms(1) assms(2) read_field.elims read_field_mono)

lemma well_typed_heap_core:
  "Instantiation.well_typed_heap \<Gamma> x = Instantiation.well_typed_heap \<Gamma> |x|"
  by (simp add: Instantiation.well_typed_heap_def core_structure(2))

lemma partial_heap_same_sum:
  fixes h :: "'r partial_heap"
  assumes "h = h1"
      and "h = h2"
  shows "Some h = h1 \<oplus> h2"
proof (rule plus_funI)
  fix l show "Some (h l) = h1 l \<oplus> h2 l"
    by (metis core_is_smaller assms core_option.elims option.simps(3) plus_val_def)
qed

lemma same_core:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_vh (get_state a) = get_vh (get_state b)"
    shows "|a| = |b|"
proof (rule full_state_ext)
  show "get_store |a| = get_store |b|"
    by (simp add: assms(1) core_charact(1))
  show "get_abs_state |a| = get_abs_state |b|"
    by (metis Rep_virtual_state_inverse agreement.exhaust_sel assms(2) assms(3) core_charact(2) core_def core_structure(1) core_structure(2) get_abs_state_def get_state_def get_trace_def get_vh_def get_vm_def prod.exhaust_sel)
qed

lemma split_remove_only_owns_only:
  assumes "r \<omega> = Some l"
      and "wf_exp r"
      and "get_vm (get_state \<omega>) l = 1"
  shows "\<exists>ptr. Some \<omega> = remove_only \<omega> l \<oplus> ptr \<and> ptr \<in> points_to r"
proof -
  obtain v where "get_vh (get_state \<omega>) l = Some v"
    by (metis assms(3) not_Some_eq not_gr_0 vstate_wf_imp zero_neq_one)
  let ?m = "\<lambda>l'. if l = l' then 1 else 0"
  let ?h = "get_vh (get_state \<omega>)"
  define ptr where "ptr = set_state \<omega> (Abs_virtual_state (?m, ?h))"

  have "wf_pre_virtual_state (?m, ?h)"
    using \<open>get_vh (get_state \<omega>) l = Some v\<close> gr_0_is_ppos by auto
  then have "get_vm (get_state ptr) = ?m"
    by (simp add: Abs_virtual_state_inverse get_vm_def ptr_def)
  then have "owns_only ptr l"
    by (simp add: owns_only_def)

  moreover have "Some \<omega> = remove_only \<omega> l \<oplus> ptr"
  proof (rule plus_prodI)
    show "Some (fst \<omega>) = fst (remove_only \<omega> l) \<oplus> fst ptr"
      by (metis agreement.exhaust_sel core_charact(1) get_store_def get_store_set_state plus_AgI ptr_def remove_only_core)
    show "Some (snd \<omega>) = snd (remove_only \<omega> l) \<oplus> snd ptr"
    proof (rule plus_prodI)
      show "Some (fst (snd \<omega>)) = fst (snd (remove_only \<omega> l)) \<oplus> fst (snd ptr)"        
        by (smt (verit) core_def core_is_smaller fst_conv option.distinct(1) plus_agreement_def ptr_def remove_only_core remove_only_def set_state_def snd_conv)
      show "Some (snd (snd \<omega>)) = snd (snd (remove_only \<omega> l)) \<oplus> snd (snd ptr)"
      proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
        show "Some (Rep_virtual_state (snd (snd \<omega>))) = Rep_virtual_state (snd (snd (remove_only \<omega> l))) \<oplus> Rep_virtual_state (snd (snd ptr))"
        proof (rule plus_prodI)
          show "Some (fst (Rep_virtual_state (snd (snd \<omega>)))) = fst (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) \<oplus> fst (Rep_virtual_state (snd (snd ptr)))"
          proof (rule plus_funI)
            fix la show "Some (fst (Rep_virtual_state (snd (snd \<omega>))) la) =
          fst (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la \<oplus> fst (Rep_virtual_state (snd (snd ptr))) la"
            by (metis SepAlgebra.plus_preal_def \<open>get_vm (get_state ptr) = (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone)\<close> add.right_neutral assms(3) commutative fun_upd_def get_state_def get_vm_def remove_only_charact(2))
          qed
          show "Some (snd (Rep_virtual_state (snd (snd \<omega>)))) = snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) \<oplus> snd (Rep_virtual_state (snd (snd ptr)))"
          proof (rule partial_heap_same_sum)
            show "snd (Rep_virtual_state (snd (snd \<omega>))) = snd (Rep_virtual_state (snd (snd (remove_only \<omega> l))))"
              by (metis get_state_def get_vh_def remove_only_charact(1))
            show "snd (Rep_virtual_state (snd (snd \<omega>))) = snd (Rep_virtual_state (snd (snd ptr)))"
              by (metis Abs_virtual_state_inverse \<open>wf_pre_virtual_state (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone, get_vh (get_state \<omega>))\<close> get_state_def get_state_set_state get_vh_def mem_Collect_eq ptr_def snd_eqD)
          qed
        qed
      qed
    qed
  qed
  moreover have "r ptr = Some l"
    using assms(2) assms(1)
  proof (rule wf_exp_combinedE)
    have "|ptr| = |\<omega>|"
      by (metis Abs_virtual_state_inverse \<open>wf_pre_virtual_state (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone, get_vh (get_state \<omega>))\<close> get_state_set_state get_store_set_state get_trace_set_state get_vh_def mem_Collect_eq ptr_def same_core snd_eqD)
    then show "|ptr| \<succeq> |\<omega>|"
      by (simp add: succ_refl)
  qed
  ultimately show ?thesis
    by (metis (mono_tags, lifting) CollectI points_to_def)
qed

definition pure_post_field_assign where
  "pure_post_field_assign r e b = { \<omega> |\<omega> l v. let \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v) in
  (b \<omega>' = Some True \<and> get_vm (get_state \<omega>) (the (r \<omega>')) = 1 \<and> get_vh (get_state \<omega>) (the (r \<omega>')) = (e \<omega>'))}"






definition well_typed :: "(field_ident \<rightharpoonup> 'a val set) \<Rightarrow> ('a ag_trace \<times> 'a virtual_state) \<Rightarrow> bool" where
  "well_typed \<Gamma> \<omega> \<longleftrightarrow> well_typed_heap \<Gamma> (snd \<omega>) \<and> (\<forall>l \<phi>. the_ag (fst \<omega>) l = Some \<phi> \<longrightarrow> well_typed_heap \<Gamma> \<phi>)"

(* TODO:
1. Adapt interpretation and prove rules
2. Prove simpler rules for FieldAssign when heap independent
3. Prove rule label?
*)

lemma well_typedI[intro]:
  assumes "well_typed_heap \<Gamma> (snd \<omega>)"
      and "\<And>l \<phi>. the_ag (fst \<omega>) l = Some \<phi> \<Longrightarrow> well_typed_heap \<Gamma> \<phi>"
    shows "well_typed \<Gamma> \<omega>"
  by (simp add: assms(1) assms(2) well_typed_def)

thm well_typedI[elim_format]

lemma well_typedE:
  assumes "well_typed \<Gamma> \<omega>"
  shows "well_typed_heap \<Gamma> (snd \<omega>)"
    and "the_ag (fst \<omega>) l = Some \<phi> \<Longrightarrow> well_typed_heap \<Gamma> \<phi>"
  using assms well_typed_def apply blast
  by (meson assms well_typed_def)

thm well_typedE(1)[elim_format]


lemma well_typed_sum:
  assumes "Some x = a \<oplus> b"
      and "well_typed \<Gamma> a"
      and "well_typed \<Gamma> b"
    shows "well_typed \<Gamma> x"
proof (rule well_typedI)
  show "Instantiation.well_typed_heap \<Gamma> (snd x)"
    by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) plus_prodE well_typedE(1) well_typed_heap_sum)
  fix l \<phi> assume "the_ag (fst x) l = Some \<phi>"
  moreover have "fst x = fst a"
    by (metis assms(1) greater_def greater_prod_eq option.distinct(1) option.inject plus_agreement_def)
  ultimately show "Instantiation.well_typed_heap \<Gamma> \<phi>"
    by (metis assms(2) well_typedE(2))
qed

lemma well_typed_smaller:
  assumes "a \<succeq> b"
      and "well_typed \<Gamma> a"
    shows "well_typed \<Gamma> b"
proof (rule well_typedI)
  show "Instantiation.well_typed_heap \<Gamma> (snd b)"
    by (meson assms(1) assms(2) greater_prod_eq well_typed_def well_typed_heap_smaller)
  fix l \<phi> assume asm0: "the_ag (fst b) l = Some \<phi>"
  moreover have "the_ag (fst b) = the_ag (fst a)"
    by (metis (mono_tags, lifting) assms(1) greater_def option.inject option.simps(3) plus_agreement_def plus_prodE)
  ultimately show "Instantiation.well_typed_heap \<Gamma> \<phi>"
    by (metis assms(2) well_typedE(2))
qed

lemma well_typed_core:
  assumes "well_typed \<Gamma> |x|"
  shows "well_typed \<Gamma> x"
proof (rule well_typedI)
  show "Instantiation.well_typed_heap \<Gamma> (snd x )"
    by (metis assms core_def snd_conv well_typedE(1) well_typed_heap_core)
  fix l \<phi>
  assume "the_ag (fst x ) l = Some \<phi>"
  then show "Instantiation.well_typed_heap \<Gamma> \<phi>"
    by (metis (mono_tags, lifting) assms core_is_smaller option.simps(3) plus_agreement_def plus_prodE well_typedE(2))
qed


global_interpretation TypedEqui: typed_state well_typed
proof
  fix x a b :: "('a ag_trace \<times> 'a virtual_state)"
  fix \<Gamma>
  show "Some x = a \<oplus> b \<Longrightarrow> well_typed \<Gamma> a \<Longrightarrow> well_typed \<Gamma> b \<Longrightarrow> well_typed \<Gamma> x"
    using well_typed_sum by blast
  show "a \<succeq> b \<Longrightarrow> well_typed \<Gamma> a \<Longrightarrow> well_typed \<Gamma> b"
    using well_typed_smaller by blast
  show "well_typed \<Gamma> |x| \<Longrightarrow> well_typed \<Gamma> x"
    using well_typed_core by blast
qed







fun wf_custom_stmt where
  "wf_custom_stmt \<Delta> (FieldAssign r f e) \<longleftrightarrow> sep_algebra_class.wf_exp r \<and> sep_algebra_class.wf_exp e
  \<and> (\<exists>ty. custom_context \<Delta> f = Some ty \<and> TypedEqui.typed_exp ty e)"
| "wf_custom_stmt _ (Label _) \<longleftrightarrow> True"








definition update_value where
  "update_value \<Delta> A r f e =
  { \<omega>' |\<omega>' \<omega> l v ty. custom_context \<Delta> f = Some ty \<and> v \<in> ty \<and>
 \<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)}"




lemma in_update_value:
  assumes "\<omega> \<in> A"
      and "r \<omega> = Some l"
      and "e \<omega> = Some v"
      and "\<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      and "custom_context \<Delta> f = Some ty"
      and "v \<in> ty"
    shows "\<omega>' \<in> update_value \<Delta> A r f e"
  using assms update_value_def by fast

lemma update_valueE:
  assumes "\<omega>' \<in> update_value \<Delta> A r f e"
  shows "\<exists>\<omega> l v ty. custom_context \<Delta> f = Some ty \<and> v \<in> ty \<and>
 \<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
  using assms update_value_def
  by (smt (verit, best) mem_Collect_eq)

definition assertion_holds_at where
  "assertion_holds_at l A = { \<omega> |\<omega> \<phi>. get_trace \<omega> l = Some \<phi> \<and> set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> \<phi>)) \<in> A }"

inductive SL_Custom :: "('a val, (field_ident \<rightharpoonup> 'a val set)) abs_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state assertion \<Rightarrow> bool"
  where
  RuleFieldAssign: "\<lbrakk> TypedEqui.self_framing_typed \<Delta> A; entails A { \<omega> |\<omega> l. get_m \<omega> (l, f) = 1 \<and> r \<omega> = Some l};
  framed_by_exp A r; framed_by_exp A e \<rbrakk> \<Longrightarrow> SL_Custom \<Delta> A (FieldAssign r f e) (update_value \<Delta> A r f e)"
| RuleLabel: "SL_Custom \<Delta> A (Label l) (assertion_holds_at l A)"


inductive_cases SL_custom_FieldAssign[elim!]: "SL_Custom \<Delta> A (FieldAssign r f e) B"
inductive_cases SL_custom_Label[elim!]: "SL_Custom \<Delta> A (Label l) B"


lemma typed_then_update_value_typed:
  assumes "TypedEqui.typed_assertion \<Delta> A"
  shows "TypedEqui.typed_assertion \<Delta> (update_value \<Delta> A r f e)"
proof (rule TypedEqui.typed_assertionI)
  fix \<omega>' assume asm0: "\<omega>' \<in> update_value \<Delta> A r f e"
  then obtain \<omega> l v ty where "custom_context \<Delta> f = Some ty" "v \<in> ty"
 "\<omega> \<in> A" "r \<omega> = Some l" "e \<omega> = Some v" "\<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
    using update_valueE by blast
  show "TypedEqui.typed \<Delta> \<omega>'"
    unfolding TypedEqui.typed_def
  proof
    show "TypedEqui.typed_store \<Delta> (get_store \<omega>')"
      by (metis TypedEqui.typed_assertion_def TypedEqui.typed_def \<open>\<omega> \<in> A\<close> \<open>\<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)\<close> assms get_store_set_state)
    show "well_typed (custom_context \<Delta>) (get_abs_state \<omega>')"
    proof (rule well_typedI)
      show "\<And>l \<phi>. the_ag (fst (get_abs_state \<omega>')) l = Some \<phi> \<Longrightarrow> Instantiation.well_typed_heap (custom_context \<Delta>) \<phi>"
        by (metis TypedEqui.typed_assertion_def TypedEqui.typed_def \<open>\<omega> \<in> A\<close> \<open>\<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)\<close> assms get_abs_state_def get_trace_def get_trace_set_state well_typedE(2))
      show "Instantiation.well_typed_heap (custom_context \<Delta>) (snd (get_abs_state \<omega>'))"
        by (smt (z3) Instantiation.well_typed_heap_def TypedEqui.typed_assertion_def TypedEqui.typed_def \<open>\<And>thesis. (\<And>\<omega> l v ty. \<lbrakk>custom_context \<Delta> f = Some ty; v \<in> ty; \<omega> \<in> A; r \<omega> = Some l; e \<omega> = Some v; \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms fun_upd_apply get_abs_state_def get_state_def get_state_set_state option.sel set_value_charact(2) snd_conv well_typedE(1))
    qed
  qed
qed


lemma set_state_value_inv:
  assumes "get_vh \<phi> l = Some v"
      and "x = set_value \<phi> l v'"
    shows "\<phi> = set_value x l v"
proof (rule virtual_state_ext)
  show "get_vm \<phi> = get_vm (set_value x l v)"
    by (simp add: assms(2))
  show "get_vh \<phi> = get_vh (set_value x l v)"
    using assms(1) assms(2) by force
qed

lemma stabilize_value_persists:
  assumes "get_h (stabilize \<omega>) l = Some v"
  shows "get_h \<omega> l = Some v"
  by (metis (no_types, lifting) assms greater_state_has_greater_parts(3) max_projection_propE(1) max_projection_prop_stable_stabilize read_field.elims read_field_mono)

lemma get_vm_stabilize[simp]:
  "get_vm (stabilize \<omega>) = get_vm \<omega>"
  by (metis core_is_smaller core_structure(1) decompose_stabilize_pure get_vm_additive option.inject)

lemma get_m_stabilize[simp]:
  "get_m (stabilize \<omega>) = get_m \<omega>"
  by (simp add: get_state_def stabilize_prod_def)




lemma virtual_state_ext_stable:
  assumes "get_vm a = get_vm b"
      and "stable a"
      and "stable b"
      and "\<And>l va vb. get_vh a l = Some va \<Longrightarrow> get_vh b l = Some vb \<Longrightarrow> va = vb"
    shows "a = b"
proof (rule virtual_state_ext)
  show "get_vh a = get_vh b"
  proof (rule ext)
    fix x show "get_vh a x = get_vh b x"
      by (metis assms(1) assms(2) assms(3) assms(4) option.exhaust stable_virtual_state_def vstate_wf_imp)
  qed
  show "get_vm a = get_vm b"
    by (simp add: assms(1))
qed

lemma stable_virtual_stateI:
  assumes "\<And>hl. get_vh x hl \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm x hl"
  shows "stable x"
  using assms stable_virtual_state_def by blast



lemma stabilize_set_value:
  assumes "get_m \<omega> l > 0"
  shows "stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)) = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)"
proof (rule full_state_ext)

  show "get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))) = get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v))"
  proof
    show "fst (get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)))) =
    fst (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))"
      by (metis agreement.collapse get_abs_state_def get_trace_def get_trace_set_state get_trace_stabilize)
    show "snd (get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)))) =
    snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))"
    proof (rule virtual_state_ext_stable)
      show "sep_algebra_class.stable (snd (get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)))))"
        by (metis get_abs_state_def stabilize_is_stable stable_prod_def)
      show "sep_algebra_class.stable (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v))))"
      proof (rule stable_virtual_stateI)
        fix hl assume "get_vh (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))) hl \<noteq> None"
        then show "0 < get_vm (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))) hl"
        proof (cases "l = hl")
          case True
          then show ?thesis
            by (metis assms get_abs_state_def get_m_stabilize get_state_def get_state_set_state set_value_charact(1))
        next
          case False
          then show ?thesis
            by (metis \<open>get_vh (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))) hl \<noteq> None\<close> fun_upd_apply get_abs_state_def get_state_def get_state_set_state set_value_charact(1) set_value_charact(2) snd_conv stabilize_is_stable stabilize_prod_def stable_virtual_state_def)
        qed
      qed
      fix hl va vb assume "get_vh (snd (get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))))) hl = Some va"
         "get_vh (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))) hl = Some vb"
      then show "va = vb"
        by (metis fun_upd_def get_abs_state_def get_state_def get_state_set_state option.inject set_value_charact(2) stabilize_value_persists)
    next
      show "get_vm (snd (get_abs_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))))) =
      get_vm (snd (get_abs_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v))))"
        by (metis get_abs_state_def get_m_stabilize get_state_def get_state_set_state set_value_charact(1))
    qed
  qed
qed (simp)

lemma full_state_ext_better:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_state a = get_state b"
    shows "a = b"
  by (metis agreement.exhaust_sel assms(1) assms(2) assms(3) get_state_def get_store_def get_trace_def prod.exhaust_sel)

lemma typed_get_vh:
  assumes "TypedEqui.typed \<Delta> \<omega>"
      and "get_vh (get_state \<omega>) hl = Some v"
    shows "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v \<in> ty"  
  by (metis TypedEqui.typed_def assms(1) assms(2) get_abs_state_def get_state_def well_typedE(1) well_typed_heapE)

lemma self_framing_update_value:
  assumes "TypedEqui.self_framing_typed \<Delta> A"
      and "wf_exp r"
      and "wf_exp e"
      and "framed_by_exp A r"
      and "framed_by_exp A e"
      and "\<And>\<omega> l. \<omega> \<in> A \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> (l, f) = 1"
      and "TypedEqui.typed_assertion \<Delta> A"
    shows "TypedEqui.self_framing_typed \<Delta> (update_value \<Delta> A r f e)"
proof (rule TypedEqui.self_framing_typedI)
  fix \<omega>'
  assume asm0: "TypedEqui.typed \<Delta> \<omega>'"
  show "\<omega>' \<in> update_value \<Delta> A r f e \<longleftrightarrow> stabilize \<omega>' \<in> update_value \<Delta> A r f e" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain \<omega> l v ty where r: "custom_context \<Delta> f = Some ty \<and> v \<in> ty" "\<omega> \<in> A" "r \<omega> = Some l"
      "e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      using update_valueE[of \<omega>' \<Delta> A r f e] by blast
    then have "r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      using TypedEqui.wf_exp_framed_by_stabilize_typed[OF _ _ \<open>\<omega> \<in> A\<close>, of _ \<Delta>]
      by (smt (verit, ccfv_threshold) TypedEqui.typed_state_axioms assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) typed_state.typed_assertion_def)
    moreover have "stabilize \<omega>' = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) (l, f) v)"
      by (simp add: assms(6) pperm_pnone_pgt r(2) r(3) r(4) stabilize_set_value)
    ultimately show ?Q
      by (metis TypedEqui.typed_assertion_def TypedEqui.typed_state_axioms assms(1) assms(7) in_update_value r(1) r(2) typed_state.self_framing_typedE)
  next
    assume ?Q
    then obtain \<omega> l v ty where asm1: "custom_context \<Delta> f = Some ty \<and> v \<in> ty \<and> \<omega> \<in> A" "r \<omega> = Some l"
      "e \<omega> = Some v \<and> stabilize \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      using update_valueE[of "stabilize \<omega>'" \<Delta> A r f e] by blast
    then have "stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      by (meson TypedEqui.self_framing_typedE TypedEqui.typed_assertion_def TypedEqui.typed_state_axioms assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) typed_state.wf_exp_framed_by_stabilize_typed)
    have r: "get_store \<omega>' = get_store \<omega> \<and> get_trace \<omega>' = get_trace \<omega> \<and> get_m \<omega>' = get_m \<omega>"
      by (metis asm1(3) get_m_stabilize get_state_set_state get_store_set_state get_store_stabilize get_trace_set_state get_trace_stabilize set_value_charact(1))
    have "\<exists>x. stabilize x = stabilize \<omega> \<and> \<omega>' = set_state x (set_value (get_state x) (l, f) v) \<and> TypedEqui.typed \<Delta> x"
    proof -
      obtain v0 where "get_h \<omega> (l, f) = Some v0"
        using assms(6) asm1
        by (metis not_gr_0 option.exhaust_sel vstate_wf_imp zero_neq_one)

      let ?x = "set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)"
      have "\<omega>' = set_state ?x (set_value (get_state ?x) (l, f) v)"
      proof (rule full_state_ext)
        have "get_state \<omega>' = set_value (get_state ?x) (l, f) v"
        proof (rule set_state_value_inv)
          have "get_h (stabilize \<omega>') (l, f) = Some v"
            by (simp add: asm1)
          then show "get_h \<omega>' (l, f) = Some v"
            using stabilize_value_persists by blast
        qed (auto)
        then show "get_abs_state \<omega>' =
    get_abs_state (set_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)) (set_value (get_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) (l, f) v))"
          by (simp add: get_state_def get_store_def get_trace_def set_state_def)
      qed (simp_all)
      moreover have "stabilize ?x = stabilize \<omega>"
      proof (rule full_state_ext_better)
        show "get_state (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) = get_state (stabilize \<omega>)"
        proof (rule virtual_state_ext_stable)
          have "get_m (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) = get_m \<omega>'" 
            by simp
          then show "get_m (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) = get_m (stabilize \<omega>)"
            using r by auto
          show "sep_algebra_class.stable (get_state (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))))"
            by (metis get_state_def stabilize_is_stable stable_prod_def)
          show "sep_algebra_class.stable (get_state (stabilize \<omega>))"
            by (metis get_state_def stabilize_is_stable stable_prod_def)
          
          fix l' va vb assume "get_h (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) l' = Some va"
            "get_h (stabilize \<omega>) l' = Some vb"
          then have "get_h \<omega> l' = Some vb"
            using stabilize_value_persists by blast
          moreover have "get_vh (set_value (get_state \<omega>') (l, f) v0) l' = Some va"
            by (metis \<open>get_h (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) l' = Some va\<close> get_state_set_state stabilize_value_persists)
          then show "va = vb"
          proof (cases "(l, f) = l'")
            case True
            then show ?thesis
              using \<open>get_h \<omega> (l, f) = Some v0\<close> \<open>get_vh (set_value (get_state \<omega>') (l, f) v0) l' = Some va\<close> calculation by auto
          next
            case False
            then show ?thesis
              by (metis (no_types, lifting) \<open>get_h (stabilize (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) l' = Some va\<close> \<open>get_h \<omega> (l, f) = Some v0\<close> asm1(1) asm1(2) asm1(3) assms(6) calculation get_state_set_state not_gr_0 option.sel r set_state_value_inv stabilize_set_value zero_neq_one)
          qed
        qed
      qed (simp_all add: r)
      moreover have "TypedEqui.typed \<Delta> ?x"
        unfolding TypedEqui.typed_def
      proof
        show "TypedEqui.typed_store \<Delta> (get_store (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)))"
          by (metis TypedEqui.typed_def asm0(1) get_store_set_state)
        show "well_typed (custom_context \<Delta>) (get_abs_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)))"
        proof (rule well_typedI)
          show "\<And>la \<phi>. the_ag (fst (get_abs_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)))) la = Some \<phi> \<Longrightarrow>
       Instantiation.well_typed_heap (custom_context \<Delta>) \<phi>"
            by (metis TypedEqui.typed_def asm0(1) get_abs_state_def get_trace_def get_trace_set_state well_typedE(2))
          show "Instantiation.well_typed_heap (custom_context \<Delta>) (snd (get_abs_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))))"
          proof (rule well_typed_heapI)
            fix hl v' assume asm2: "get_vh (snd (get_abs_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)))) hl = Some v'"
            show "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v' \<in> ty"
              apply (cases "hl = (l, f)")
              apply (metis (mono_tags, lifting) TypedEqui.typed_assertion_def \<open>get_h \<omega> (l, f) = Some v0\<close> asm1(1) asm2 assms(7) get_abs_state_def get_state_def get_state_set_state map_upd_Some_unfold set_value_charact(2) typed_get_vh)
            proof -
              assume "hl \<noteq> (l, f)"
              then have "get_vh (set_value (get_state \<omega>') (l, f) v0) hl = Some v'"
                by (metis get_abs_state_def get_state_def get_state_set_state asm2)
              then have "get_vh (get_state \<omega>') hl = Some v'"
                by (simp add: \<open>hl \<noteq> (l, f)\<close>)
              then show "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v' \<in> ty"
                using asm0 typed_get_vh by blast
            qed
          qed
        qed
      qed
      ultimately show ?thesis by fast
    qed
    then have "\<exists>x. x \<in> A \<and> r x = Some l \<and> e x = Some v \<and> \<omega>' = set_state x (set_value (get_state x) (l, f) v)"
      by (metis (no_types, lifting) TypedEqui.self_framing_typed_altE \<open>stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v\<close> assms(1) assms(2) assms(3) wf_exp_stabilize)
    then show ?P
      using asm0(1) in_update_value
      using asm1(1) by blast
  qed
qed








inductive red_custom_stmt :: "('a val, field_ident \<rightharpoonup> 'a val set) abs_type_context \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state \<Rightarrow> 'a equi_state set \<Rightarrow> bool"
  where
  RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; get_vm (get_state \<omega>) (hl, f) = 1; custom_context \<Delta> f = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_custom_stmt \<Delta> (FieldAssign r f e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) (hl, f) v)}"
| RedLabel: "red_custom_stmt \<Delta> (Label l) \<omega> {set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> get_state \<omega>)) }"

inductive_cases red_custom_stmt_FieldAssign[elim!]: "red_custom_stmt \<Delta> (FieldAssign r f e) \<omega> S"
inductive_cases red_custom_stmt_Label[elim!]: "red_custom_stmt \<Delta> (Label l) \<omega> S"

lemma SL_proof_FieldAssign_easy:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> (FieldAssign r g e) (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> (FieldAssign r g e)"
      and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>) \<and> TypedEqui.typed \<Delta> (snd \<alpha>)"
    shows "SL_Custom \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) (FieldAssign r g e) (TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
proof -

  have wfs: "wf_exp r \<and> wf_exp e" using assms by auto

  let ?r = "\<lambda>\<omega>. the (r \<omega>)"
  let ?e = "\<lambda>\<omega>. the (e \<omega>)"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (r (snd \<alpha>) = Some (?r (snd \<alpha>)) \<and> e (snd \<alpha>) = Some (?e (snd \<alpha>))
  \<and> get_m (snd \<alpha>) (?r (snd \<alpha>), g) = 1
  \<and> (?e (snd \<alpha>)) \<in> (the (custom_context \<Delta> g))
  \<and> f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (?r (snd \<alpha>), g) (?e (snd \<alpha>)))} )"
    using assms(1) by fastforce

  let ?A = "TypedEqui.Stabilize_typed \<Delta> (snd ` SA)"
  let ?B = "update_value \<Delta> ?A r g e"


  have "SL_Custom \<Delta> ?A (custom.FieldAssign r g e) ?B"
  proof (rule RuleFieldAssign)
    show "TypedEqui.self_framing_typed \<Delta> ?A"
      by simp
    show entails_rel: "entails (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) {\<omega> |\<omega> l. get_m \<omega> (l, g) = PosReal.pwrite \<and> r \<omega> = Some l}"
    proof (rule entailsI)
      fix \<omega> assume "\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (snd ` SA)"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by (metis (no_types, lifting) TypedEqui.Stabilize_typed_def imageE in_Stabilize member_filter)
      then obtain l where "get_m (stabilize \<omega>) (l, g) = PosReal.pwrite \<and> r (stabilize \<omega>) = Some l"
        by (metis r)
      then have "get_m \<omega> (l, g) = 1 \<and> r \<omega> = Some l"
        using wf_exp_stabilize wfs by force
      then show "\<omega> \<in> {\<omega> |\<omega> l. get_m \<omega> (l, g) = 1 \<and> r \<omega> = Some l}"
        by blast
    qed
    then show "framed_by_exp (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r"
      by (smt (verit, best) Collect_mem_eq Collect_mono_iff entails_def framed_by_exp_def option.distinct(1))
    show "framed_by_exp (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) e"
      by (smt (verit, ccfv_SIG) TypedEqui.Stabilize_typed_def framed_by_exp_def image_iff in_Stabilize member_filter option.distinct(1) r wf_exp_stabilize wfs)
  qed
  moreover have "?B = TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA))" (is "?B = ?Q")
  proof (rule TypedEqui.self_framing_typed_ext)
    show "TypedEqui.self_framing_typed \<Delta> (update_value \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r g e)"
    proof (rule self_framing_update_value)
      show "wf_exp r" using wfs by simp
      show "wf_exp e" using wfs by simp
      show "framed_by_exp (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r"
        using calculation by force
      show "framed_by_exp (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) e"
        using calculation by fastforce
      show "\<And>\<omega> l. \<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (snd ` SA) \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> (l, g) = 1"
        by (metis (no_types, opaque_lifting) RangeE TypedEqui.Stabilize_typed_def get_m_stabilize in_Stabilize member_filter option.sel r snd_conv snd_eq_Range wf_exp_stabilize wfs)
    qed (simp_all)

    show "TypedEqui.typed_assertion \<Delta> (update_value \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r g e)"
      using TypedEqui.typed_Stabilize_typed typed_then_update_value_typed by blast

    fix \<omega>'
    assume asm0: "sep_algebra_class.stable \<omega>'" "TypedEqui.typed \<Delta> \<omega>'"
    show "\<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA)) \<Longrightarrow> \<omega>' \<in> update_value \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r g e"
    proof -
      assume asm1: "\<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA))"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' \<in> f \<alpha>" "TypedEqui.typed \<Delta> \<omega>'"
        by (metis (no_types, lifting) TypedEqui.Stabilize_typed_def UN_E in_Stabilize member_filter)
      then obtain l v where "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)}"  "r (snd \<alpha>) = Some l" "e (snd \<alpha>) = Some v"
        using r[of \<alpha>] by blast
      then have "stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)"
        using \<open>stabilize \<omega>' \<in> f \<alpha>\<close> by blast
      moreover have "stable (snd \<alpha>)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> assms(3))
      ultimately have "snd \<alpha> \<in> Stabilize (snd ` SA)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> already_stable)
      moreover have "TypedEqui.typed \<Delta> (stabilize \<omega>')"
        by (simp add: TypedEqui.typed_state_then_stabilize_typed asm0(2))
      moreover have "stabilize \<omega>' \<in> ?B"
        using in_update_value[of _ _ r _ e, OF _ \<open>r (snd \<alpha>) = Some l\<close> \<open>e (snd \<alpha>) = Some v\<close> \<open>stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)\<close>]
        by (smt (verit) TypedEqui.Stabilize_typed_def \<open>\<alpha> \<in> SA\<close> \<open>e (snd \<alpha>) = Some v\<close> assms(1) assms(3) calculation(1) member_filter option.sel red_custom_stmt_FieldAssign)
      then show "\<omega>' \<in> ?B" unfolding update_value_def
        by (simp add: \<open>sep_algebra_class.stable \<omega>'\<close> already_stable)
    qed
    
    show "\<omega>' \<in> update_value \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r g e \<Longrightarrow> \<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA))"
    proof -
      assume "\<omega>' \<in> update_value \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) r g e"
      then obtain \<omega> l v where "\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)"
        unfolding update_value_def by blast
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by (metis (no_types, lifting) TypedEqui.Stabilize_typed_def imageE in_Stabilize member_filter)
      then have "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (the (r (snd \<alpha>)), g) (the (e (snd \<alpha>))))}"
        using r by blast
      moreover have "the (r (snd \<alpha>)) = l \<and> the (e (snd \<alpha>)) = v"
        by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> option.sel r wf_exp_stabilize wfs)
      then have "stabilize \<omega>' \<in> f \<alpha>"
        by (metis \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> TypedEqui.Stabilize_typed \<Delta> (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> get_m_stabilize pperm_pnone_pgt r singleton_iff stabilize_set_value zero_neq_one)
      then show "\<omega>' \<in> TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA))"
        using TypedEqui.Stabilize_typed_def \<open>\<alpha> \<in> SA\<close> asm0(2) by fastforce
    qed
  qed (simp_all)
  ultimately show ?thesis by argo
qed




(*
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> (FieldAssign r g e) (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> (FieldAssign r g e)"
      and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>)"
    shows "SL_Custom \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) (FieldAssign r g e) (TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
*)


lemma SL_proof_aux_custom:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> C"
    and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>) \<and> TypedEqui.typed \<Delta> (snd \<alpha>)"
  shows "SL_Custom \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) C (TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA)))"
proof (cases C)
  case (FieldAssign r g e)
  then show ?thesis
    using SL_proof_FieldAssign_easy assms by blast
next
  case (Label l)
  then show ?thesis sorry (* Label *)
qed

lemma custom_reciprocal:
  assumes "SL_Custom \<Delta> A C B"
      and "\<omega> \<in> A"
      and "wf_custom_stmt \<Delta> C"
      and "sep_algebra_class.stable \<omega>"
      and "TypedEqui.typed \<Delta> \<omega>"
    shows "\<exists>S. red_custom_stmt \<Delta> C \<omega> S \<and> S \<subseteq> B"
  using assms
proof (induct rule: SL_Custom.induct)
  case (RuleFieldAssign \<Delta> A f r e)
  then obtain hl v where "r \<omega> = Some hl" "e \<omega> = Some v" "get_m \<omega> (hl, f) = 1"
    by (smt (verit, ccfv_SIG) CollectD entails_def framed_by_expE subset_iff)
  then obtain ty where "custom_context \<Delta> f = Some ty" "v \<in> ty"
    by (meson RuleFieldAssign.prems(2) TypedEqui.typed_exp_def wf_custom_stmt.simps(1))
  then have "red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) (hl, f) v)}"
    using RedFieldAssign[of r \<omega> hl e v f \<Delta> ty]
    using \<open>e \<omega> = Some v\<close> \<open>get_m \<omega> (hl, f) = PosReal.pwrite\<close> \<open>r \<omega> = Some hl\<close> by fastforce
  then show "\<exists>S. red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega> S \<and> S \<subseteq> update_value \<Delta> A r f e"
    by (meson RuleFieldAssign.prems(1) \<open>custom_context \<Delta> f = Some ty\<close> \<open>e \<omega> = Some v\<close> \<open>r \<omega> = Some hl\<close> \<open>v \<in> ty\<close> empty_subsetI in_update_value insert_subset)
next
  case (RuleLabel \<Delta> A l)
  then show ?case sorry (* Label *)
qed

lemma red_custom_stable:
  assumes "red_custom_stmt \<Delta> C \<omega> S"
      and "sep_algebra_class.stable \<omega>"
      and "\<omega>' \<in> S"
    shows "sep_algebra_class.stable \<omega>'"
  using assms
proof (induct rule: red_custom_stmt.induct)
  case (RedFieldAssign r \<omega> hl e v f \<Delta> ty)
  then show ?case
    by (metis already_stable pperm_pnone_pgt singleton_iff stabilize_is_stable stabilize_set_value zero_neq_one)
next
  case (RedLabel \<Delta> l \<omega>)
  then show ?case
    by (metis already_stable set_trace_stabilize singletonD stabilize_is_stable)
qed

lemma red_custom_well_typed:
  assumes "red_custom_stmt \<Delta> C \<omega> S"
      and "well_typed (custom_context \<Delta>) (get_abs_state \<omega>)"
      and "wf_custom_stmt \<Delta> C"
      and "\<omega>' \<in> S"
    shows "well_typed (custom_context \<Delta>) (get_abs_state \<omega>')"
  using assms
proof (induct rule: red_custom_stmt.induct)
  case (RedFieldAssign r \<omega> hl e v f \<Delta> ty)
  show "well_typed (custom_context \<Delta>) (get_abs_state \<omega>')"
  proof (rule well_typedI)
    show "\<And>l \<phi>. the_ag (fst (get_abs_state \<omega>')) l = Some \<phi> \<Longrightarrow> Instantiation.well_typed_heap (custom_context \<Delta>) \<phi>"
      by (metis RedFieldAssign.prems(1) RedFieldAssign.prems(3) get_abs_state_def get_trace_def get_trace_set_state singletonD well_typedE(2))
    show "Instantiation.well_typed_heap (custom_context \<Delta>) (snd (get_abs_state \<omega>'))"
    proof (rule well_typed_heapI)
      fix hl v assume "get_vh (snd (get_abs_state \<omega>')) hl = Some v"
      then show "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v \<in> ty"
        by (metis RedFieldAssign.hyps(4) RedFieldAssign.hyps(5) RedFieldAssign.prems(1) RedFieldAssign.prems(3) fun_upd_other fun_upd_same get_abs_state_def get_state_def get_state_set_state option.sel set_value_charact(2) singletonD snd_conv well_typedE(1) well_typed_heapE)
    qed
  qed
next
  case (RedLabel \<Delta> l \<omega>)
  show "well_typed (custom_context \<Delta>) (get_abs_state \<omega>')"
  proof (rule well_typedI)
    show "Instantiation.well_typed_heap (custom_context \<Delta>) (snd (get_abs_state \<omega>'))"
      by (metis RedLabel.prems(1) RedLabel.prems(3) get_abs_state_def get_state_def get_state_set_trace singletonD well_typedE(1))
    fix l' \<phi> assume asm0: "the_ag (fst (get_abs_state \<omega>')) l' = Some \<phi>"
    show "Instantiation.well_typed_heap (custom_context \<Delta>) \<phi>"
    proof (rule well_typed_heapI)
      fix hl v assume "get_vh \<phi> hl = Some v"
      then show "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v \<in> ty"
        by (metis RedLabel.prems(1) RedLabel.prems(3) asm0 fun_upd_apply get_abs_state_def get_state_def get_trace_def get_trace_set_trace option.sel singletonD well_typed_def well_typed_heapE)
    qed
  qed
qed



global_interpretation ConcreteSemantics: semantics well_typed red_custom_stmt wf_custom_stmt SL_Custom
proof
  fix SA :: "('a equi_state list \<times> 'a equi_state) set"
  fix \<Delta> C f
  show "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>) \<Longrightarrow>
       wf_custom_stmt \<Delta> C \<Longrightarrow>
       TypedEqui.wf_set \<Delta> (snd ` SA) \<Longrightarrow> SL_Custom \<Delta> (TypedEqui.Stabilize_typed \<Delta> (snd ` SA)) C (TypedEqui.Stabilize_typed \<Delta> (\<Union> (f ` SA)))"    
    by (simp add: SL_proof_aux_custom TypedEqui.wf_set_def TypedEqui.wf_state_def)
  fix A B \<omega>
  show "SL_Custom \<Delta> A C B \<Longrightarrow> \<omega> \<in> A \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> sep_algebra_class.stable \<omega> \<Longrightarrow> TypedEqui.typed \<Delta> \<omega> \<Longrightarrow> \<exists>S. red_custom_stmt \<Delta> C \<omega> S \<and> S \<subseteq> B"
    using custom_reciprocal by blast
  fix S \<omega>'
  assume asm0: "red_custom_stmt \<Delta> C \<omega> S"
  show "sep_algebra_class.stable \<omega> \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> sep_algebra_class.stable \<omega>'"
    using asm0 red_custom_stable by blast
  show "TypedEqui.typed_store \<Delta> (get_store \<omega>) \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> TypedEqui.typed_store \<Delta> (get_store \<omega>')"
    using asm0 by (induct rule: red_custom_stmt.induct) auto
  show "well_typed (custom_context \<Delta>) (get_abs_state \<omega>) \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> \<omega>' \<in> S \<Longrightarrow> well_typed (custom_context \<Delta>) (get_abs_state \<omega>')"
    using asm0 red_custom_well_typed by blast

qed

definition viper_prog_verifies where
  "viper_prog_verifies Pr \<Delta> ty C \<omega> \<longleftrightarrow> ConcreteSemantics.verifies ty (compile \<Delta> C) \<omega>"
  (* ty is a type-context *)



end