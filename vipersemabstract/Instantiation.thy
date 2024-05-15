theory Instantiation           
  imports AbstractSemantics EquiViper EquiSemAuxLemma
begin

definition make_semantic_bexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'a equi_state bexp" where
  "make_semantic_bexp \<Delta> b \<omega> =
  (if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool True) then Some True
  else if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool False) then Some False
  else None)"

definition make_semantic_exp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> ('a equi_state, 'a val) exp" where
  "make_semantic_exp \<Delta> e \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v then Some (SOME v. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) else None)"

definition make_semantic_rexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> field_ident \<Rightarrow> ('a equi_state, address \<times> field_ident) exp" where
  "make_semantic_rexp \<Delta> r f \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v))
  then Some (SOME v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v)), f)
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
  FieldAssign "('a equi_state, address \<times> field_ident) exp" "('a equi_state, 'a val) exp"


fun compile :: "('a, 'a virtual_state) interp \<Rightarrow> stmt \<Rightarrow> ('a equi_state, 'a val, 'a custom) abs_stmt"
  where
  "compile \<Delta> stmt.Skip = abs_stmt.Skip"

| "compile \<Delta> (stmt.If b C1 C2) = abs_stmt.If (make_semantic_bexp \<Delta> b) (compile \<Delta> C1) (compile \<Delta> C2)"
| "compile \<Delta> (stmt.Seq C1 C2) = abs_stmt.Seq (compile \<Delta> C1) (compile \<Delta> C2)"

| "compile \<Delta> (stmt.Scope ty C) = abs_stmt.Scope (make_semantic_vtyp \<Delta> ty) (compile \<Delta> C)"
| "compile \<Delta> (stmt.Havoc x) = abs_stmt.Havoc x"
| "compile \<Delta> (stmt.LocalAssign x e) = abs_stmt.LocalAssign x (make_semantic_exp \<Delta> e)"

| "compile \<Delta> (stmt.Label l) = abs_stmt.Label l"

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

| "compile \<Delta> (stmt.FieldAssign r f e) = abs_stmt.Custom (FieldAssign (make_semantic_rexp \<Delta> r f) (make_semantic_exp \<Delta> e))"



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

(*
  fixes red_custom_stmt :: "('v, 'r) abs_type_context \<Rightarrow> 'c \<Rightarrow> ('v, ('a :: sep_algebra)) abs_state \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"
  fixes wf_custom_stmt :: "('v, 'r) abs_type_context \<Rightarrow> 'c \<Rightarrow> bool"
  fixes SL_Custom :: "('v, 'r) abs_type_context \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> 'c \<Rightarrow> ('v, 'a) abs_state set \<Rightarrow> bool"

  fixes well_typed_heap :: "('r \<rightharpoonup> 'v abs_vtyp) \<Rightarrow> 'a \<Rightarrow> bool"

  assumes well_typed_heap_sum: "Some x = a \<oplus> b \<Longrightarrow> well_typed_heap \<Gamma> a \<Longrightarrow> well_typed_heap \<Gamma> b \<Longrightarrow> well_typed_heap \<Gamma> x"
      and well_typed_heap_smaller: "a \<succeq> b \<Longrightarrow> well_typed_heap \<Gamma> a \<Longrightarrow> well_typed_heap \<Gamma> b"
      and well_typed_heap_core: "well_typed_heap \<Gamma> x \<longleftrightarrow> well_typed_heap \<Gamma> |x|"
      and well_typed_heap_update: "well_typed_heap \<Gamma> x \<Longrightarrow> \<Gamma> r = Some ty \<Longrightarrow> v \<in> ty \<Longrightarrow> well_typed_heap \<Gamma> (set_value x r v)"

      and SL_proof_custom: "(\<forall>(\<omega> :: (('v, 'a) abs_state list \<times> ('v, 'a) abs_state)) \<in> SA.
  red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)) \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union>\<omega>\<in>SA. f \<omega>))"
*)

inductive red_custom_stmt :: "('a val, address \<times> field_ident) abs_type_context \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state \<Rightarrow> 'a equi_state set \<Rightarrow> bool"
  where
  RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; get_vm (get_state \<omega>) hl = 1; heap_locs \<Delta> hl = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_custom_stmt \<Delta> (FieldAssign r e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) hl v)}"

inductive_cases red_custom_stmt_FieldAssign[elim!]: "red_custom_stmt \<Delta> (FieldAssign r e) \<omega> S"


definition owns_only where
  "owns_only \<omega> l \<longleftrightarrow> get_vm (get_state \<omega>) l = 1 \<and> (\<forall>l'. l' \<noteq> l \<longrightarrow> get_vm (get_state \<omega>) l' = 0)"

lemma owns_onlyI:
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
  by (smt (z3) core_charact(1) core_charact(2) core_is_pure core_structure(1) core_structure(2) get_store_set_state get_trace_set_state greater_state_has_greater_parts(2) max_projection_prop_pure_core mpp_smaller plus_state_def remove_only_charact(1) remove_only_def smaller_than_core vstate_add_iff)


definition points_to where
  "points_to r = { \<omega> |\<omega> hl. r \<omega> = Some hl \<and> owns_only \<omega> hl }"
                                                 


definition well_typed_heap where
  "well_typed_heap \<Gamma> \<phi> \<longleftrightarrow> (\<forall>hl v. get_vh \<phi> hl = Some v \<longrightarrow> (\<exists>ty. \<Gamma> hl = Some ty \<and> v \<in> ty))"

lemma well_typed_heapI:
  assumes "\<And>hl v. get_vh \<phi> hl = Some v \<Longrightarrow> (\<exists>ty. \<Gamma> hl = Some ty \<and> v \<in> ty)"
  shows "well_typed_heap \<Gamma> \<phi>"
  by (simp add: Instantiation.well_typed_heap_def assms)

lemma well_typed_heapE:
  assumes "well_typed_heap \<Gamma> \<phi>"
      and "get_vh \<phi> hl = Some v"
    shows "\<exists>ty. \<Gamma> hl = Some ty \<and> v \<in> ty"
  using Instantiation.well_typed_heap_def assms(1) assms(2) by blast

lemma well_typed_heap_sum:
  assumes "Some x = a \<oplus> b"
      and "well_typed_heap \<Gamma> a"
      and "well_typed_heap \<Gamma> b"
    shows "well_typed_heap \<Gamma> x"
  using Instantiation.well_typed_heap_def assms(1) assms(2) assms(3) sum_val_defined by blast

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
  by (smt (verit, best) assms(1) assms(2) assms(3) core_is_pure core_structure(1) core_structure(2) full_core_def max_projection_prop_pure_core mpp_smaller smaller_than_core vstate_add_iff)


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
    proof (rule plus_prodI)
      show "Some (fst (fst \<omega>)) = fst (fst (remove_only \<omega> l)) \<oplus> fst (fst ptr)"
        apply (rule plus_AgI)
         apply (metis agreement.exhaust_sel get_store_def get_store_set_state remove_only_def)
        by (metis agreement.exhaust_sel get_store_def get_store_set_state ptr_def)
      show "Some (snd (fst \<omega>)) = snd (fst (remove_only \<omega> l)) \<oplus> snd (fst ptr)"
        by (simp add: get_trace_def plus_AgI ptr_def remove_only_def set_state_def)
    qed
    show "Some (snd \<omega>) = snd (remove_only \<omega> l) \<oplus> snd ptr"
    proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
      show "Some (Rep_virtual_state (snd \<omega>)) = Rep_virtual_state (snd (remove_only \<omega> l)) \<oplus> Rep_virtual_state (snd ptr)"
      proof (rule plus_prodI)
        show "Some (fst (Rep_virtual_state (snd \<omega>))) =
    fst (Rep_virtual_state (snd (remove_only \<omega> l))) \<oplus> fst (Rep_virtual_state (snd ptr))"
        proof (rule plus_funI)
          fix la show "Some (fst (Rep_virtual_state (snd \<omega>)) la) =
          fst (Rep_virtual_state (snd (remove_only \<omega> l))) la \<oplus> fst (Rep_virtual_state (snd ptr)) la"
            by (metis SepAlgebra.plus_preal_def \<open>get_vm (get_state ptr) = (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone)\<close> add.right_neutral assms(3) commutative fun_upd_def get_state_def get_vm_def remove_only_charact(2))
        qed

        show "Some (snd (Rep_virtual_state (snd \<omega>))) =
    snd (Rep_virtual_state (snd (remove_only \<omega> l))) \<oplus> snd (Rep_virtual_state (snd ptr))"
        proof (rule partial_heap_same_sum)
          show "snd (Rep_virtual_state (snd \<omega>)) = snd (Rep_virtual_state (snd (remove_only \<omega> l)))"
            by (metis get_state_def get_vh_def remove_only_charact(1))
          show "snd (Rep_virtual_state (snd \<omega>)) = snd (Rep_virtual_state (snd ptr))"
            by (metis Abs_virtual_state_inverse \<open>wf_pre_virtual_state (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone, get_vh (get_state \<omega>))\<close> get_state_def get_state_set_state get_vh_def mem_Collect_eq ptr_def snd_eqD)
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


(*
lemma stabilize_remove_only_is_stabilize:
  "stabilize (remove_only \<omega> l) = remove_only (stabilize \<omega>) l"
  apply (rule full_state_ext)
    apply (simp add: remove_only_def)
proof -
  show "get_trace (stabilize (remove_only \<omega> l)) = get_trace (remove_only (stabilize \<omega>) l)"
    by (simp add: remove_only_def)
  show "get_state (stabilize (remove_only \<omega> l)) = get_state (remove_only (stabilize \<omega>) l)"
  proof (rule virtual_state_ext)
    show "get_vh (get_state (stabilize (remove_only \<omega> l))) = get_vh (get_state (remove_only (stabilize \<omega>) l))"
    proof (rule ext)
      fix x show "get_vh (get_state (stabilize (remove_only \<omega> l))) x = get_vh (get_state (remove_only (stabilize \<omega>) l)) x"
        apply (cases "x = l")
        sorry
*)
fun wf_custom_stmt where
  "wf_custom_stmt \<Delta> (FieldAssign r e) \<longleftrightarrow> sep_algebra_class.wf_exp r \<and> sep_algebra_class.wf_exp e"

definition pure_post_field_assign where
  "pure_post_field_assign r e b = { \<omega> |\<omega> l v. let \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v) in
  (b \<omega>' = Some True \<and> get_vm (get_state \<omega>) (the (r \<omega>')) = 1 \<and> get_vh (get_state \<omega>) (the (r \<omega>')) = (e \<omega>'))}"
(*
inductive SL_Custom :: "('a val, address \<times> field_ident) abs_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state assertion \<Rightarrow> bool"
  where
  RuleFieldAssign: "\<lbrakk> self_framing A; framed_by_exp A r; framed_by_exp (A \<otimes> points_to r) b; wf_exp b;
  framed_by_exp (A \<otimes> points_to r \<otimes> pure_Stabilize b) e \<rbrakk>
    \<Longrightarrow> SL_Custom _ (A \<otimes> points_to r \<otimes> pure_Stabilize b) (FieldAssign r e) (A \<otimes> pure_post_field_assign r e b)"
*)

definition update_value where
  "update_value A r e = { \<omega>' |\<omega>' \<omega> l v. \<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)}"


inductive SL_Custom :: "('a val, address \<times> field_ident) abs_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state assertion \<Rightarrow> bool"
  where
  RuleFieldAssign: "\<lbrakk> self_framing A; entails A { \<omega> |\<omega> l. get_m \<omega> l = 1 \<and> r \<omega> = Some l};
  framed_by_exp A r; framed_by_exp A e \<rbrakk> \<Longrightarrow> SL_Custom _ A (FieldAssign r e) (update_value A r e)"

inductive_cases SL_custom_FieldAssign[elim!]: "SL_Custom \<Delta> A (FieldAssign r e) B"


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
  by (metis (no_types, lifting) core_charact(2) decompose_stabilize_pure full_add_charact(2) get_vm_stabilize plus_pure_stabilize_eq)




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

thm stable_virtual_state_def

lemma stable_virtual_stateI:
  assumes "\<And>hl. get_vh x hl \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm x hl"
  shows "stable x"
  using assms stable_virtual_state_def by blast



lemma stabilize_set_value:
  assumes "get_m \<omega> l > 0"
  shows "stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)) = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)"
proof (rule full_state_ext)
  show "get_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))) = get_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v))"
  proof (rule virtual_state_ext_stable)
    show "sep_algebra_class.stable (get_state (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))))"
      by (metis get_state_def stabilize_is_stable stable_prod_def)
    show "sep_algebra_class.stable (get_state (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)))"
      apply simp
    proof (rule stable_virtual_stateI)
      fix hl assume "get_vh (set_value (get_state (stabilize \<omega>)) l v) hl \<noteq> None"
      then show "0 < get_vm (set_value (get_state (stabilize \<omega>)) l v) hl"
      proof (cases "l = hl")
        case True
        then show ?thesis
          using assms by auto
      next
        case False
        then show ?thesis
          by (metis \<open>get_vh (set_value (get_state (stabilize \<omega>)) l v) hl \<noteq> None\<close> fun_upd_apply get_state_def set_value_charact(1) set_value_charact(2) stabilize_is_stable stable_prod_def stable_virtual_state_def)
      qed
    qed
    fix hl va vb assume "get_h (stabilize (set_state \<omega> (set_value (get_state \<omega>) l v))) hl = Some va"
      "get_h (set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)) hl = Some vb"
    then show "va = vb"
      by (metis fun_upd_def get_state_set_state option.inject set_value_charact(2) stabilize_value_persists)
  qed (simp_all)
qed (simp_all)



lemma self_framing_update_value:
  assumes "self_framing A"
      and "wf_exp r"
      and "wf_exp e"
      and "framed_by_exp A r"
      and "framed_by_exp A e"
      and "\<And>\<omega> l. \<omega> \<in> A \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> l = 1"
  shows "self_framing (update_value A r e)"
proof (rule self_framingI)
  fix \<omega>'
  show "\<omega>' \<in> update_value A r e \<longleftrightarrow> stabilize \<omega>' \<in> update_value A r e" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain \<omega> l v where "\<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)"
      unfolding update_value_def by blast
    then have "r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      by (meson assms wf_exp_framed_by_stabilize)
    moreover have "stabilize \<omega>' = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)"
      by (simp add: \<open>\<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)\<close> assms(6) pperm_pnone_pgt stabilize_set_value)
    ultimately show ?Q
      by (smt (verit, del_insts) CollectI \<open>\<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)\<close> assms(1) self_framing_def update_value_def)
  next
    assume ?Q
    then obtain \<omega> l v where asm0: "\<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> stabilize \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)"
      unfolding update_value_def by blast
    then have "stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) self_framing_def wf_exp_framed_by_stabilize)

    have r: "get_store \<omega>' = get_store \<omega> \<and> get_trace \<omega>' = get_trace \<omega> \<and> get_m \<omega>' = get_m \<omega>"
      by (smt (verit) asm0 core_structure(1) decompose_stabilize_pure get_state_def get_store_set_state get_store_stabilize get_trace_set_state get_trace_stabilize get_vm_additive option.sel prod.inject pure_larger_stabilize pure_larger_stabilize_same set_state_def set_value_charact(1) stabilize_prod_def)

    have "\<exists>x. stabilize x = stabilize \<omega> \<and> \<omega>' = set_state x (set_value (get_state x) l v)"
    proof -
      obtain v0 where "get_h \<omega> l = Some v0"
        using assms(6) asm0
        by (metis not_gr_0 option.exhaust_sel vstate_wf_imp zero_neq_one)

      let ?x = "set_state \<omega>' (set_value (get_state \<omega>') l v0)"
      have "\<omega>' = set_state ?x (set_value (get_state ?x) l v)"
      proof (rule full_state_ext)
        have "get_state \<omega>' = set_value (get_state ?x) l v"
        proof (rule set_state_value_inv)
          have "get_h (stabilize \<omega>') l = Some v"
            by (simp add: asm0)
          then show "get_h \<omega>' l = Some v"
            using stabilize_value_persists by blast
          show "get_state (set_state \<omega>' (set_value (get_state \<omega>') l v0)) = set_value (get_state \<omega>') l v0"
            by auto
        qed
        then show "get_state \<omega>' = get_state (set_state ?x (set_value (get_state ?x) l v))"
          by auto
      qed (simp_all)
      moreover have "stabilize ?x = stabilize \<omega>"
      proof (rule full_state_ext)
        show "get_state (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))) = get_state (stabilize \<omega>)"
        proof (rule virtual_state_ext_stable)
          have "get_m (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))) = get_m \<omega>'" 
            by simp
          then show "get_m (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))) = get_m (stabilize \<omega>)"
            using r by auto
          show "sep_algebra_class.stable (get_state (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))))"
            by (metis get_state_def stabilize_is_stable stable_prod_def)
          show "sep_algebra_class.stable (get_state (stabilize \<omega>))"
            by (metis get_state_def stabilize_is_stable stable_prod_def)
          fix l' va vb assume "get_h (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))) l' = Some va"
            "get_h (stabilize \<omega>) l' = Some vb"
          then have "get_h \<omega> l' = Some vb"
            using stabilize_value_persists by blast
          moreover have "get_vh (set_value (get_state \<omega>') l v0) l' = Some va"
            by (metis \<open>get_h (stabilize (set_state \<omega>' (set_value (get_state \<omega>') l v0))) l' = Some va\<close> get_state_set_state stabilize_value_persists)
          then show "va = vb"
          proof (cases "l = l'")
            case True
            then show ?thesis
              using \<open>get_h \<omega> l = Some v0\<close> \<open>get_vh (set_value (get_state \<omega>') l v0) l' = Some va\<close> calculation by auto
          next
            case False
            then show ?thesis
              by (metis \<open>get_vh (set_value (get_state \<omega>') l v0) l' = Some va\<close> asm0 calculation fun_upd_apply get_state_set_state option.sel set_value_charact(2) stabilize_value_persists)
          qed
        qed
      qed (simp_all add: r)
      ultimately show ?thesis
        by blast
    qed
    then have "\<exists>x. x \<in> A \<and> r x = Some l \<and> e x = Some v \<and> \<omega>' = set_state x (set_value (get_state x) l v)"
      by (metis \<open>stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v\<close> assms(1) assms(2) assms(3) self_framing_def wf_exp_stabilize)
    then show ?P
      by (metis (mono_tags, lifting) CollectI update_value_def)
  qed
qed




lemma SL_proof_FieldAssign_easy:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> (FieldAssign r e) (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> (FieldAssign r e)"
      and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>)"
    shows "SL_Custom \<Delta> (Stabilize (snd ` SA)) (FieldAssign r e) (Stabilize (\<Union> (f ` SA)))"
proof -

  have wfs: "wf_exp r \<and> wf_exp e" using assms by auto

  let ?r = "\<lambda>\<omega>. the (r \<omega>)"
  let ?e = "\<lambda>\<omega>. the (e \<omega>)"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (r (snd \<alpha>) = Some (?r (snd \<alpha>)) \<and> e (snd \<alpha>) = Some (?e (snd \<alpha>))
  \<and> get_m (snd \<alpha>) (?r (snd \<alpha>)) = 1
  \<and> heap_locs \<Delta> (the (r (snd \<alpha>))) = Some (the (heap_locs \<Delta> (?r (snd \<alpha>))))
  \<and>  (?e (snd \<alpha>)) \<in> (the (heap_locs \<Delta> (?r (snd \<alpha>))))
  \<and> f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (?r (snd \<alpha>)) (?e (snd \<alpha>)))} )"
    using assms(1) by fastforce

  let ?A = "Stabilize (snd ` SA)"
  let ?B = "update_value ?A r e"


  have "SL_Custom \<Delta> ?A (custom.FieldAssign r e) ?B"
  proof (rule RuleFieldAssign)
    show "self_framing ?A"
      using Stabilize_self_framing by blast
    show "entails (Stabilize (snd ` SA)) {\<omega> |\<omega> l. get_m \<omega> l = PosReal.pwrite \<and> r \<omega> = Some l}"
    proof (rule entailsI)
      fix \<omega> assume "\<omega> \<in> Stabilize (snd ` SA)"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by (meson imageE in_Stabilize)
      then obtain l where "get_m (stabilize \<omega>) l = PosReal.pwrite \<and> r (stabilize \<omega>) = Some l"
        by (metis r)
      then have "get_m \<omega> l = PosReal.pwrite \<and> r \<omega> = Some l"
        by (smt (verit, best) core_charact(2) core_structure(1) decompose_stabilize_pure get_m_additive pure_larger_stabilize pure_larger_stabilize_same wf_exp_stabilize wfs)
      then show "\<omega> \<in> {\<omega> |\<omega> l. get_m \<omega> l = PosReal.pwrite \<and> r \<omega> = Some l}"
        by blast
    qed
    show "framed_by_exp (Stabilize (snd ` SA)) r"
      by (metis (no_types, opaque_lifting) RangeE framed_by_expI in_Stabilize not_None_eq prod.sel(2) r snd_eq_Range wf_exp_stabilize wfs)
    show "framed_by_exp (Stabilize (snd ` SA)) e"
      by (metis (no_types, opaque_lifting) RangeE framed_by_expI in_Stabilize not_None_eq prod.sel(2) r snd_eq_Range wf_exp_stabilize wfs)
  qed
  moreover have "?B = Stabilize (\<Union> (f ` SA))" (is "?B = ?Q")
  proof (rule self_framing_ext)
    show "self_framing (update_value (Stabilize (snd ` SA)) r e)"
    proof (rule self_framing_update_value)
      show "self_framing (Stabilize (snd ` SA))"
        using Stabilize_self_framing by blast
      show "wf_exp r"
        using wfs by auto
      show "wf_exp e"
        by (simp add: wfs)
      show "framed_by_exp (Stabilize (snd ` SA)) r"
        using calculation by force
      show "framed_by_exp (Stabilize (snd ` SA)) e"
        using calculation by blast
      show "\<And>\<omega> l. \<omega> \<in> Stabilize (snd ` SA) \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> l = PosReal.pwrite"
        by (metis (no_types, opaque_lifting) RangeE Stabilize_self_framing \<open>framed_by_exp (Stabilize (snd ` SA)) r\<close> get_m_stabilize in_Stabilize option.sel r snd_conv snd_eq_Range wf_exp_framed_by_stabilize wfs)
    qed

    show "self_framing (Stabilize (\<Union> (f ` SA)))"
      using Stabilize_self_framing by auto

    fix \<omega>'
    show "sep_algebra_class.stable \<omega>' \<Longrightarrow> \<omega>' \<in> Stabilize (\<Union> (f ` SA)) \<Longrightarrow> \<omega>' \<in> update_value (Stabilize (snd ` SA)) r e"
    proof -
      assume "sep_algebra_class.stable \<omega>'" "\<omega>' \<in> ?Q"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' \<in> f \<alpha>"
        by auto
      then obtain l v where "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) l v)}"  "r (snd \<alpha>) = Some l" "e (snd \<alpha>) = Some v"
        using r[of \<alpha>] by blast
      then have "stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) l v)"
        using \<open>stabilize \<omega>' \<in> f \<alpha>\<close> by blast
      moreover have "stable (snd \<alpha>)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> assms(3))
      ultimately have "snd \<alpha> \<in> Stabilize (snd ` SA)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> already_stable)
      then have "stabilize \<omega>' \<in> ?B"
        by (smt (verit, ccfv_SIG) CollectI \<open>e (snd \<alpha>) = Some v\<close> \<open>r (snd \<alpha>) = Some l\<close> \<open>stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) l v)\<close> update_value_def)
      then show "\<omega>' \<in> ?B" unfolding update_value_def
        by (simp add: \<open>sep_algebra_class.stable \<omega>'\<close> already_stable)
    qed
    assume "sep_algebra_class.stable \<omega>'" "\<omega>' \<in> update_value (Stabilize (snd ` SA)) r e"
    then obtain \<omega> l v where "\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)"
      unfolding update_value_def by blast
    then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
      by auto
    then have "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (the (r (snd \<alpha>))) (the (e (snd \<alpha>))))}"
      using r by blast
    moreover have "the (r (snd \<alpha>)) = l \<and> the (e (snd \<alpha>)) = v"
      by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> option.sel r wf_exp_stabilize wfs)
    then have "stabilize \<omega>' \<in> f \<alpha>"
      by (metis \<open>\<And>thesis. (\<And>\<alpha>. \<lbrakk>\<alpha> \<in> SA; stabilize \<omega> = snd \<alpha>\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) l v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> calculation get_m_stabilize not_gr_0 r singleton_iff stabilize_set_value zero_neq_one)
    then show "\<omega>' \<in> Stabilize (\<Union> (f ` SA))"
      using \<open>\<alpha> \<in> SA\<close> by auto
  qed
  ultimately show ?thesis by argo
qed
















(*




lemma SL_proof_FieldAssign:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> (FieldAssign r e) (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> (FieldAssign r e)"
    shows "SL_Custom \<Delta> (Stabilize (snd ` SA)) (FieldAssign r e) (Stabilize (\<Union> (f ` SA)))"
proof -

  have wfs: "wf_exp r \<and> wf_exp e" using assms by auto

  let ?r = "\<lambda>\<omega>. the (r \<omega>)"
  let ?e = "\<lambda>\<omega>. the (e \<omega>)"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (r (snd \<alpha>) = Some (?r (snd \<alpha>)) \<and> e (snd \<alpha>) = Some (?e (snd \<alpha>))
  \<and> get_vm (get_state (snd \<alpha>)) (?r (snd \<alpha>)) = 1
  \<and> heap_locs \<Delta> (the (r (snd \<alpha>))) = Some (the (heap_locs \<Delta> (?r (snd \<alpha>))))
  \<and>  (?e (snd \<alpha>)) \<in> (the (heap_locs \<Delta> (?r (snd \<alpha>))))
  \<and> f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (?r (snd \<alpha>)) (?e (snd \<alpha>)))} )"
    using assms(1) by fastforce

(*
SL_Custom \<Delta> (?A \<otimes> points_to r \<otimes> pure_Stabilize ?b) (custom.FieldAssign r e) (?A \<otimes> pure_post_field_assign r e ?b)
*)

  let ?A = "Stabilize { remove_only \<omega> l |\<alpha> \<omega> l. \<alpha> \<in> SA \<and> \<omega> = snd \<alpha> \<and> r \<omega> = Some l }"
(* How do I remove something l if I don't know l... *)
(* Consider all pure_larger? *)

  let ?b = "\<lambda>\<omega>. if (\<exists>\<omega>' \<in> snd ` SA. \<omega> \<succeq> |\<omega>'| ) then Some True else None"
(* TODO: Think about... *)

  have eq1: "?A \<otimes> points_to r \<otimes> pure_Stabilize ?b = Stabilize (snd ` SA)" (is "?P = ?Q")
  proof
    show "?Q \<subseteq> ?P"
    proof
      fix \<omega> assume "\<omega> \<in> ?Q"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by auto
      then obtain l where "r \<omega> = Some l"
        by (metis (no_types, lifting) r wf_exp_stabilize wfs)
      moreover have "get_vm (get_state \<omega>) l = 1"
      proof -
        have "get_vm (get_state \<omega>) = get_vm (get_state (stabilize \<omega>))"
          by (metis (no_types, opaque_lifting) core_structure(1) decompose_stabilize_pure get_state_def get_vm_additive option.sel pure_larger_stabilize pure_larger_stabilize_same snd_conv stabilize_prod_def)
        then show ?thesis
          by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> calculation option.sel r wf_exp_stabilize wfs)
      qed
      then obtain ptr where "Some \<omega> = remove_only \<omega> l \<oplus> ptr" "ptr \<in> points_to r"
        using calculation split_remove_only_owns_only wfs by blast
      moreover have "stabilize (remove_only \<omega> l) \<in> ?A"
(*
?A cannot be this, because doing the stabilize might remove the info
...
*)
        sorry


        by (smt (verit, best) CollectI \<open>\<And>thesis. (\<And>\<alpha>. \<lbrakk>\<alpha> \<in> SA; stabilize \<omega> = snd \<alpha>\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>r (stabilize \<omega>) = Some l\<close> decompose_stabilize_pure in_Stabilize plus_pure_stabilize_eq stabilize_remove_only_is_stabilize)
      ultimately have "stabilize \<omega> \<in> ?A \<otimes> points_to r"
        using add_set_def by blast
      moreover have "Some \<omega> = stabilize \<omega> \<oplus> |\<omega>|"
        using decompose_stabilize_pure by blast
      moreover have "|\<omega>| \<in> pure_Stabilize ?b"
        unfolding pure_Stabilize_def
      proof -
        have "|\<omega>| \<succeq> |snd \<alpha>|"
          by (metis \<open>stabilize \<omega> = snd \<alpha>\<close> core_stabilize_mono(1) max_projection_prop_stable_stabilize mpp_smaller)
        then show "|\<omega>| \<in> {\<omega> |\<omega>. (if \<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'| then Some True else None) = Some True \<and> pure \<omega>}"
          by (metis (no_types, lifting) CollectI \<open>\<omega> \<in> Stabilize (snd ` SA)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> core_is_pure in_Stabilize pure_def)
      qed
      ultimately show "\<omega> \<in> (?A \<otimes> points_to r) \<otimes> pure_Stabilize ?b"
        using x_elem_set_product by blast
    qed
    show "?P \<subseteq> ?Q"
    proof
      fix \<omega> assume "\<omega> \<in> ?P"
      then obtain \<omega>'' p where asm0: "Some \<omega> = \<omega>'' \<oplus> p" "p \<in> pure_Stabilize ?b" "\<omega>'' \<in> ?A \<otimes> points_to r"
        using add_set_def by blast
      then obtain \<omega>' ptr where asm1: "Some \<omega>'' = \<omega>' \<oplus> ptr" "\<omega>' \<in> ?A" "ptr \<in> points_to r"
        by (meson x_elem_set_product)



      then show "\<omega> \<in> ?Q"
        sorry
    qed


  moreover have eq2: "?A \<otimes> pure_post_field_assign r e ?b = Stabilize (\<Union> (f ` SA))"
    sorry

  moreover have "SL_Custom \<Delta> (?A \<otimes> points_to r \<otimes> pure_Stabilize ?b) (custom.FieldAssign r e) (?A \<otimes> pure_post_field_assign r e ?b)"
  proof (rule RuleFieldAssign[of _ r _ e \<Delta>])
    show "self_framing ?A"
      using Stabilize_self_framing by blast
    show "framed_by_exp ?A r"
    proof (rule framed_by_expI)
      fix a assume "a \<in> ?A"
      then obtain \<alpha> \<omega> l where "stabilize a = remove_only \<omega> l" "\<alpha> \<in> SA \<and> \<omega> = snd \<alpha> \<and> r \<omega> = Some l"
        by auto
      then have "r |\<omega>| = Some l"
        using wf_exp_coreE[of r \<omega>] wfs by argo
      then show "r a \<noteq> None"
        by (metis (no_types, lifting) \<open>stabilize a = remove_only \<omega> l\<close> option.distinct(1) remove_only_core wf_exp_coreE wf_exp_stabilize wfs)
    qed
    show "wf_exp (\<lambda>\<omega>. if \<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'| then Some True else None)"
    proof (rule wf_expI)
      fix a show "(if \<exists>\<omega>'\<in>snd ` SA. a \<succeq> |\<omega>'| then Some True else None) = (if \<exists>\<omega>'\<in>snd ` SA. |a| \<succeq> |\<omega>'| then Some True else None)"
        by (metis (no_types, lifting) max_projection_prop_def max_projection_prop_pure_core succ_trans)
      fix a b v show "a \<succeq> b \<and> (if \<exists>\<omega>'\<in>snd ` SA. b \<succeq> |\<omega>'| then Some True else None) = Some v \<Longrightarrow> (if \<exists>\<omega>'\<in>snd ` SA. a \<succeq> |\<omega>'| then Some True else None) = Some v"
        by (meson option.distinct(1) succ_trans)
    qed
    show "framed_by_exp (?A \<otimes> points_to r) (\<lambda>\<omega>. if \<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'| then Some True else None)"
    proof (rule framed_by_expI)
      fix \<omega> assume asm0: "\<omega> \<in> ?A \<otimes> points_to r"
      then obtain \<omega>'' ptr where "Some \<omega> = \<omega>'' \<oplus> ptr" "ptr \<in> points_to r" "\<omega>'' \<in> ?A"
        by (meson x_elem_set_product)
      then obtain \<alpha> \<omega>' l where "stabilize \<omega>'' = remove_only \<omega>' l" "\<alpha> \<in> SA \<and> \<omega>' = snd \<alpha> \<and> r \<omega>' = Some l"
        by auto
      then have "\<omega> \<succeq> |\<omega>'|"
        by (metis (no_types, lifting) \<open>Some \<omega> = \<omega>'' \<oplus> ptr\<close> greater_def max_projection_prop_pure_core max_projection_prop_stable_stabilize mpp_smaller remove_only_core succ_trans)
      then have "\<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'|"
        using \<open>\<alpha> \<in> SA \<and> \<omega>' = snd \<alpha> \<and> r \<omega>' = Some l\<close> by blast
      then show "(if \<exists>\<omega>'\<in>snd ` SA. \<omega> \<succeq> |\<omega>'| then Some True else None) \<noteq> None"
        by auto
    qed
    show "framed_by_exp (?A \<otimes> points_to r \<otimes> pure_Stabilize ?b) e"
    proof (rule framed_by_expI)
      fix \<omega> assume asm0: "\<omega> \<in> ?A \<otimes> points_to r \<otimes> pure_Stabilize ?b"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        using eq1 by auto
      then show "e \<omega> \<noteq> None"
        by (metis option.distinct(1) r wf_exp_stabilize wfs)
    qed
  qed
  ultimately show ?thesis by argo
qed

*)


lemma SL_proof_aux_custom:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
    and "wf_custom_stmt \<Delta> C"
    and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>)"
    shows "SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union> (f ` SA)))"
proof (cases C)
  case (FieldAssign r e)
  then show ?thesis
    using SL_proof_FieldAssign_easy assms(1) assms(2) assms(3) by blast
qed

global_interpretation ConcreteSemantics: semantics red_custom_stmt wf_custom_stmt SL_Custom well_typed_heap
proof
  fix x a b :: "'a virtual_state"
  fix \<Gamma>
  show "Some x = a \<oplus> b \<Longrightarrow> Instantiation.well_typed_heap \<Gamma> a \<Longrightarrow> Instantiation.well_typed_heap \<Gamma> b \<Longrightarrow> Instantiation.well_typed_heap \<Gamma> x"
    using well_typed_heap_sum by blast
  show "a \<succeq> b \<Longrightarrow> Instantiation.well_typed_heap \<Gamma> a \<Longrightarrow> Instantiation.well_typed_heap \<Gamma> b"
    using well_typed_heap_smaller by auto
  show "Instantiation.well_typed_heap \<Gamma> x = Instantiation.well_typed_heap \<Gamma> |x|"
    using well_typed_heap_core by blast
  show "\<And>SA \<Delta> C f. \<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>) \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> Ball (snd ` SA) sep_algebra_class.stable \<Longrightarrow> SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union> (f ` SA)))"
    using SL_proof_aux_custom
    by fastforce
qed


definition viper_prog_verifies where
  "viper_prog_verifies Pr \<Delta> ty C \<omega> \<longleftrightarrow> ConcreteSemantics.verifies ty (compile \<Delta> C) \<omega>"
  (* ty is a type-context *)



end