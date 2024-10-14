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

(*
definition make_semantic_rexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> field_ident \<Rightarrow> ('a equi_state, address \<times> field_ident) exp" where
  "make_semantic_rexp \<Delta> r f \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v))
  then Some (SOME v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v)), f)
  else None)"
*)

definition make_semantic_rexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> ('a equi_state, address) exp" where
  "make_semantic_rexp \<Delta> r \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v))
  then Some (SOME v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v)))
  else None)"

lemma make_semantic_bexp_Some[simp]:
  shows "make_semantic_bexp \<Delta> b \<omega> = Some vb \<longleftrightarrow> \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool vb)"
  by (simp add:make_semantic_bexp_def split:if_splits; cases vb; auto dest:red_pure_val_unique)

lemma make_semantic_exp_Some[simp]:
  shows "make_semantic_exp \<Delta> b \<omega> = Some v \<longleftrightarrow> \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v"
  by (simp add:make_semantic_exp_def split:if_splits; auto intro:someI dest:red_pure_val_unique)

lemma make_semantic_rexp_Some[simp]:
  shows "make_semantic_rexp \<Delta> r \<omega> = Some a \<longleftrightarrow> (\<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address a)))"
  by (metis (no_types, lifting) make_semantic_rexp_def option.sel option.simps(3) red_pure_val_unique(1) ref.inject someI_ex val.inject(4))

(* TODO: Move somewhere? *)
definition red_pure_assert ::  "('a, 'a virtual_state) interp \<Rightarrow> pure_exp \<Rightarrow> 'a extended_val \<Rightarrow> 'a equi_state set" ("_ \<turnstile> ((\<langle>_\<rangle>) [\<Down>] _)" [51,0,0] 81) where
"red_pure_assert \<Delta> e r = corely {\<omega>. \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] r}"

lemma red_pure_assert_intro :
  assumes "\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] r"
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = interp.funs \<Delta> f vals |st|"
  assumes "\<omega> \<in> A"
  shows "\<omega> \<in> (\<Delta> \<turnstile> \<langle>e\<rangle> [\<Down>] r) \<otimes> A"
  using assms
  apply (subst add_set_commm)
  unfolding add_set_def
  apply (safe)
  apply (rule exI)
  apply (rule exI[of _ "\<omega>"])
  apply (rule exI[of _ "|\<omega>|"])
  apply (safe; (simp add:core_is_smaller)?)
  by (simp add: red_pure_assert_def corely_def red_pure_core core_in_emp_core)

lemma red_pure_assert_elim :
  assumes "\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] r1"
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = None"
  shows "{\<omega>} \<otimes> (\<Delta> \<turnstile> \<langle>e\<rangle> [\<Down>] r2) = up_close_core ({\<omega>} \<otimes> \<llangle>r2 = r1\<rrangle>)"
  using assms unfolding red_pure_assert_def
  apply (cases "r1 = r2"; simp split:bool_to_assertion_splits)
  subgoal
    apply (rule sep_and_corely)
    subgoal by (simp add:red_pure_core)
    subgoal apply (rule up_closedI) by (clarsimp simp add:red_pure_greater)
    subgoal by (simp)
    done
  apply (simp add:corely_def)
  unfolding emp_core_def add_set_def
  apply (auto)
  using red_pure_det_defined defined_def
  by (metis option.discI)

definition acc_heap_loc :: "('a, 'a virtual_state) interp \<Rightarrow> vtyp \<Rightarrow> heap_loc \<Rightarrow> real \<Rightarrow> 'a equi_state set" where
"acc_heap_loc \<Delta> ty hl p = {\<omega> | v \<omega>. get_state \<omega> = acc_virt hl (Abs_preal p) v \<and> 0 < p \<and> p \<le> 1 \<and> v \<in> sem_vtyp (domains \<Delta>) ty }"



lemma acc_heap_loc_Stable [simp] :
  "Stable (acc_heap_loc \<Delta> ty hl p)"
  apply (clarsimp simp add:acc_heap_loc_def)
  apply (rule StableI)
  by (smt (verit) get_state_stabilize mem_Collect_eq norm_preal(1) positive_real_preal preal_not_0_gt_0 stabilize_acc_virt)

lemma abs_state_ext_iff :
  "\<omega>1 = \<omega>2 \<longleftrightarrow> get_store \<omega>1 = get_store \<omega>2 \<and> get_trace \<omega>1 = get_trace \<omega>2 \<and> get_state \<omega>1 = get_state \<omega>2"
  using full_state_ext by blast


lemma abs_state_star_singletonI :
  assumes "get_store \<omega>' = get_store \<omega>"
  assumes "get_trace \<omega>' = get_trace \<omega>"
  assumes "make_equi_state (get_store \<omega>) (get_trace \<omega>) st \<in> A"
  assumes "Some (get_state \<omega>') = get_state \<omega> \<oplus> st"
  shows "\<omega>' \<in> {\<omega>} \<otimes> A"
  apply (subst in_add_set)
  apply (rule exI, rule exI)
  apply (safe)
    apply (rule refl)
   apply (rule assms(3))
  using assms
  by (smt (verit, best) core_charact(1) core_is_smaller get_state_make_equi_state get_store_make_equi_state get_trace_make_equi_state greater_equiv greater_state_has_greater_parts(2) state_add_iff)


lemma acc_heap_loc_starI :
  assumes "0 < p"
  assumes "Abs_preal p \<le> get_vm (get_state \<omega>') hl"
  assumes "get_vh (get_state \<omega>') hl = Some v"
  assumes "\<omega> = set_state \<omega>' (del_perm (get_state \<omega>') hl (Abs_preal p))"
  assumes "v \<in> sem_vtyp (domains \<Delta>) ty"
  shows "\<omega>' \<in> {\<omega>} \<otimes> acc_heap_loc \<Delta> ty hl p"
  apply (rule abs_state_star_singletonI)
  using assms apply (solves \<open>simp\<close>)
  using assms apply (solves \<open>simp\<close>)
    using assms apply (simp add:acc_heap_loc_def)
    apply (rule, safe; assumption?) apply (rule)
     apply (insert get_vm_bound[of "get_state \<omega>'" hl])
     apply (solves \<open>simp add:preal_to_real\<close>)
  using assms by (simp add:acc_virt_plus add_perm_del_perm compatible_partial_functions_singleton defined_val preal_to_real)

lemma abs_state_star_singletonE :
  assumes "\<omega>' \<in> {\<omega>} \<otimes> A"
  assumes "\<And> \<omega>''. \<omega>'' \<in> A \<Longrightarrow>
     get_store \<omega>'' = get_store \<omega> \<Longrightarrow> 
     get_trace \<omega>'' = get_trace \<omega> \<Longrightarrow>
     get_store \<omega>' = get_store \<omega> \<Longrightarrow>
     get_trace \<omega>' = get_trace \<omega> \<Longrightarrow>
     Some (get_state \<omega>') = get_state \<omega> \<oplus> get_state \<omega>'' \<Longrightarrow>
     P"
  shows "P"
  by (smt (z3) add_set_commm assms(1) assms(2) full_add_charact(1) greater_state_has_greater_parts(2) in_set_sum singletonD star_to_singletonE state_add_iff x_elem_set_product)
(*
  by (metis (no_types, lifting) assms(1) assms(2) full_add_charact(2) full_add_defined greater_charact in_set_sum option.discI singletonD x_elem_set_product)
*)

lemma acc_heap_loc_starE :
  assumes "\<omega>' \<in> {\<omega>} \<otimes> acc_heap_loc \<Delta> ty hl p"
  shows "\<exists> v. \<omega>' = set_state \<omega> (add_perm (get_state \<omega>) hl (Abs_preal p) v) \<and> 0 < p \<and> p \<le> 1 \<and> get_vm (get_state \<omega>) hl + Abs_preal p \<le> 1 \<and>
      v \<in> sem_vtyp (domains \<Delta>) ty \<and> (get_vh (get_state \<omega>) ## [hl \<mapsto> v])"
  apply (insert assms)
  apply (erule abs_state_star_singletonE) subgoal for \<omega>''
    apply (clarsimp simp add:acc_heap_loc_def) subgoal for v
      by (auto simp add:acc_virt_plus abs_state_ext_iff preal_to_real)
    done
  done


definition acc :: "('a, 'a virtual_state) ValueAndBasicState.interp \<Rightarrow> vtyp \<Rightarrow> ref \<Rightarrow> field_name \<Rightarrow> real option \<Rightarrow> _ set" where
"acc \<Delta> ty r f p =
  (if r = Null then \<llangle>p = Some 0\<rrangle> else
     if p = Some 0 then emp else
     \<Union> pp. \<llangle>p = None \<or> pp = the p\<rrangle> \<otimes> acc_heap_loc \<Delta> ty (the_address r, f) pp)"


lemma acc_Stable [simp] :
  "Stable (acc \<Delta> ty r f p)"
  apply (clarsimp simp add:acc_def)
  by (rule Stable_ex, rule Stable_star; simp)



fun atomic_assert :: "('v, ('v virtual_state)) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> pure_exp atomic_assert \<Rightarrow> bool option \<Rightarrow> 'v equi_state set" where
  "atomic_assert \<Delta> F (Pure e) (Some b) = (\<Delta> \<turnstile> \<langle>e\<rangle> [\<Down>] Val (VBool b))"
| "atomic_assert \<Delta> F (Acc e f ep) (Some True) = (\<Union> r p ty. (\<Delta> \<turnstile> \<langle>e\<rangle> [\<Down>] Val (VRef r)) \<otimes> \<llangle>F f = Some ty\<rrangle> \<otimes>
      (case ep of Wildcard \<Rightarrow> \<llangle>p = None\<rrangle> | PureExp ep \<Rightarrow> \<Union> p'. (\<Delta> \<turnstile> \<langle>ep\<rangle> [\<Down>] Val (VPerm p')) \<otimes> \<llangle>p = Some p'\<rrangle>) \<otimes>
      acc \<Delta> ty r f p)"

fun sat_set :: "('a, 'a virtual_state) ValueAndBasicState.interp \<Rightarrow> (field_name \<rightharpoonup> vtyp)
     \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" ("\<langle>_, _\<rangle> \<Turnstile> ((\<langle>_\<rangle>))" [0,0,0] 84) where
  "\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>Atomic A\<rangle> = atomic_assert \<Delta> F A (Some True)"
| "\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>Imp b A\<rangle> = (\<Union>v. (\<Delta> \<turnstile> \<langle>b\<rangle> [\<Down>] Val v) \<otimes> (if v = VBool True then (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) else emp))"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>CondAssert b A B\<rangle>) = (\<Union>v. (\<Delta> \<turnstile> \<langle>b\<rangle> [\<Down>] Val v) \<otimes>
     (if v = VBool True then (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) else emp) \<otimes> 
     (if v = VBool False then (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>) else emp) )"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A && B\<rangle>) = ((\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) \<otimes> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>))"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A --* B\<rangle>) = ((\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) --\<otimes> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>))"
(* | "\<Delta> \<Turnstile> \<langle>ForAll ty A\<rangle> \<longleftrightarrow> (\<forall>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)" *)
(* | "\<Delta> \<Turnstile> \<langle>Exists ty A\<rangle> \<longleftrightarrow> (\<exists>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)" *)
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>ImpureAnd A B\<rangle>) = \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<inter> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>ImpureOr A B\<rangle>) = \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<union> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>"

(*
definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state \<Rightarrow> bool" where
  "make_semantic_assertion \<Delta> F A \<omega> \<longleftrightarrow> \<omega> \<in> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
*)




(*
definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set" where
  "make_semantic_assertion \<Delta> A = { \<omega> |\<omega>. \<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> }"
*)

(*
TODO: Ignoring domains so far...
record ('v, 'a) interp =
  domains :: "'v \<Rightarrow> abs_type"
*)

datatype 'a custom =
  FieldAssign "('a equi_state, address) exp" field_ident "('a equi_state, 'a val) exp"
(* | Label label *)

definition has_write_perm_only :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> bool" where
  "has_write_perm_only \<phi> hl \<longleftrightarrow> get_vm \<phi> hl = 1"

definition has_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> bool" where
  "has_value \<phi> hl v \<longleftrightarrow> get_vh \<phi> hl = Some v"

lift_definition set_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" is
  "\<lambda> \<phi> hl v. (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"
  apply (simp add:wf_pre_virtual_state_def)
  using gr_0_is_ppos vstate_wf_imp by auto

lemma get_vh_vm_set_value [simp] :
   "get_vh (set_value st hl v) = (get_vh st) (hl \<mapsto> v)"
   "get_vm (set_value st hl v) = get_vm st"
  by (simp_all add:get_vh_def get_vm_def set_value.rep_eq)



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

(*
definition set_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" where
  "set_value \<phi> hl v = Abs_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"
*)


definition owns_only where
  "owns_only \<omega> l \<longleftrightarrow> get_vm (get_state \<omega>) l = 1 \<and> (\<forall>l'. l' \<noteq> l \<longrightarrow> get_vm (get_state \<omega>) l' = 0)"

lemma owns_onlyI[intro]:
  assumes "get_vm (get_state \<omega>) l = 1"
      and "\<And>l'. l' \<noteq> l \<Longrightarrow> get_vm (get_state \<omega>) l' = 0"
    shows "owns_only \<omega> l"
  using assms(1) assms(2) owns_only_def by blast

definition remove_only where
  "remove_only \<omega> l = set_state \<omega> (Abs_virtual_state ((get_vm (get_state \<omega>))(l := 0), (get_vh (get_state \<omega>))(l := None)))"

lemma remove_only_charact:
  "get_vh (get_state (remove_only \<omega> l)) = (get_vh (get_state \<omega>))(l := None)"
  "get_vm (get_state (remove_only \<omega> l)) = (get_vm (get_state \<omega>))(l := 0)"
proof -
  have r: "wf_pre_virtual_state ((get_vm (get_state \<omega>))(l := 0), (get_vh (get_state \<omega>))(l := None))"
  proof (rule wf_pre_virtual_stateI)
    fix hl assume asm0: "PosReal.ppos (((get_vm (get_state \<omega>))(l := PosReal.pnone)) hl)"
    show "((get_vh (get_state \<omega>))(l := None)) hl \<noteq> None"
    proof (cases "hl = l")
      case True
      then show ?thesis using ppos_def
        using asm0 gr_0_is_ppos by auto
    next
      case False
      then have "PosReal.ppos (get_vm (get_state \<omega>) hl)"
        using asm0 by force
      then show ?thesis
        by (simp add: False vstate_wf_ppos)
    qed
  next
    show "wf_mask_simple ((get_m \<omega>)(l := 0))"
      by (simp add: all_pos get_vm_bound wf_mask_simpleI)
  qed
  then show "get_vh (get_state (remove_only \<omega> l)) = (get_vh (get_state \<omega>))(l := None)"
    by (simp add: Abs_virtual_state_inverse get_vh_def remove_only_def)
  show "get_vm (get_state (remove_only \<omega> l)) = (get_vm (get_state \<omega>))(l := PosReal.pnone)"
    by (metis (mono_tags, lifting) Abs_virtual_state_inverse r get_state_set_state get_vm_def mem_Collect_eq prod.sel(1) remove_only_def)
qed
(*
lemma remove_only_core:
  "|remove_only \<omega> l| = |\<omega>|"
proof (rule full_state_ext)
  show "get_store |remove_only \<omega> l| = get_store |\<omega>|"
    by (simp add: core_charact(1) remove_only_def)
  show "get_trace |remove_only \<omega> l| = get_trace |\<omega>|"
    by (metis get_trace_set_state remove_only_def set_state_core)
  show "get_state |remove_only \<omega> l| = get_state |\<omega>|"
    by (metis Rep_virtual_state_inverse agreement.exhaust_sel core_charact(2) core_def core_structure(1) core_structure(2) get_abs_state_def get_abs_state_set_abs_state get_state_def get_state_set_state get_state_set_trace get_vh_def get_vm_def prod.exhaust_sel remove_only_charact(1) set_abs_state_def set_trace_def)
qed
*)

lemma remove_only_stabilize:
  "stabilize (remove_only \<omega> l) = remove_only (stabilize \<omega>) l"
proof (rule full_state_ext)
  show "get_state (stabilize (remove_only \<omega> l)) = get_state (remove_only (stabilize \<omega>) l)"
  proof (rule virtual_state_ext)
    show "get_m (stabilize (remove_only \<omega> l)) = get_m (remove_only (stabilize \<omega>) l)"
      by (simp add: remove_only_charact(2) vstate_stabilize_structure(1))
    show "get_h (stabilize (remove_only \<omega> l)) = get_h (remove_only (stabilize \<omega>) l)"
    proof
      fix x show "get_h (stabilize (remove_only \<omega> l)) x = get_h (remove_only (stabilize \<omega>) l) x"
        apply (cases "x = l")
        apply (metis \<open>get_m (stabilize (remove_only \<omega> l)) = get_m (remove_only (stabilize \<omega>) l)\<close> fun_upd_same remove_only_charact(1) stabilize_is_stable stable_get_state stable_virtual_state_def vstate_wf_ppos)
        apply (cases "get_h (stabilize (remove_only \<omega> l)) x")
        apply (metis fun_upd_apply get_state_stabilize remove_only_charact(1) remove_only_charact(2) stabilize_is_stable stable_virtual_state_def vstate_stabilize_structure(1) vstate_wf_ppos)
      proof -
        fix a :: "'a val"
        assume a1: "get_h (stabilize (remove_only \<omega> l)) x = Some a"
        assume a2: "x \<noteq> l"
        have "\<forall>p. (p::(nat \<Rightarrow> 'a val option) agreement \<times> (char list \<Rightarrow> 'a virtual_state option) agreement \<times> 'a virtual_state) \<succeq> stabilize p \<and> sep_algebra_class.stable (stabilize p) \<and> (\<forall>pa. \<not> sep_algebra_class.stable pa \<or> \<not> p \<succeq> pa \<or> stabilize p \<succeq> pa)"
          by (metis (no_types) max_projection_prop_def max_projection_prop_stable_stabilize)
        then show ?thesis
          using a2 a1 by (smt (z3) \<open>get_m (stabilize (remove_only \<omega> l)) = get_m (remove_only (stabilize \<omega>) l)\<close> fun_upd_other get_vh_Some_greater remove_only_charact(1) stable_get_state stable_virtual_state_def vstate_wf_Some)
      qed        
    qed
  qed
qed (simp_all add: remove_only_def)




definition points_to where
  "points_to r = { \<omega> |\<omega> hl. r \<omega> = Some hl \<and> owns_only \<omega> hl }"

(*
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

(* TODO: change this to "well_typed_heap \<Gamma> \<phi> \<longleftrightarrow> (heap_typed \<Gamma> (get_vh \<phi>))" *)
*)


abbreviation well_typed_heap where
  "well_typed_heap \<Gamma> \<phi> \<equiv> heap_typed \<Gamma> (get_vh \<phi>)"

lemma well_typed_heapI[intro]:
  assumes "\<And>hl v ty. get_vh \<phi> hl = Some v \<Longrightarrow> \<Gamma> (snd hl) = Some ty \<Longrightarrow> v \<in> ty"
  shows "well_typed_heap \<Gamma> \<phi>"
  by (simp add: assms heap_typed_def)

lemma well_typed_heapE:
  assumes "well_typed_heap \<Gamma> \<phi>"
      and "get_vh \<phi> hl = Some v"
      and "\<Gamma> (snd hl) = Some ty"
    shows "v \<in> ty"
  using assms
  unfolding heap_typed_def by blast

lemma well_typed_heap_sum:
  assumes "Some x = a \<oplus> b"
      and "well_typed_heap \<Gamma> a"
      and "well_typed_heap \<Gamma> b"
    shows "well_typed_heap \<Gamma> x"
  using assms(1) assms(2) assms(3) heap_typed_def sum_val_defined
  by smt

lemma well_typed_heap_smaller:
  assumes "a \<succeq> b"
      and "Instantiation.well_typed_heap \<Gamma> a"
    shows "Instantiation.well_typed_heap \<Gamma> b"
  by (metis heap_typed_def assms(1) assms(2) read_field.elims read_field_mono)

lemma well_typed_heap_core:
  "Instantiation.well_typed_heap \<Gamma> x = Instantiation.well_typed_heap \<Gamma> |x|"
  by (simp add: heap_typed_def core_structure(2))

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
  show "get_state |a| = get_state |b|"
    by (metis Rep_virtual_state_inverse agreement.exhaust_sel assms(2) assms(3) core_charact(2) core_def core_structure(1) core_structure(2) get_abs_state_def get_state_def get_trace_def get_vh_def get_vm_def prod.exhaust_sel)
  show "get_trace |a| = get_trace |b|"
    by (metis assms(2) get_trace_set_state set_state_core)
qed

lemma split_remove_only_owns_only:
  assumes "get_vm (get_state \<omega>) l = 1"
  shows "Some \<omega> = remove_only \<omega> l \<oplus> (set_state \<omega> (Abs_virtual_state (\<lambda>l'. if l = l' then 1 else 0, get_vh (get_state \<omega>))))"
proof -
  obtain v where "get_vh (get_state \<omega>) l = Some v"
    by (metis assms(1) not_Some_eq not_gr_0 vstate_wf_imp zero_neq_one)
  let ?m = "\<lambda>l'. if l = l' then 1 else 0"
  let ?h = "get_vh (get_state \<omega>)"
  define ptr where "ptr = set_state \<omega> (Abs_virtual_state (?m, ?h))"

  have rwf: "wf_pre_virtual_state (?m, ?h)"
    using \<open>get_vh (get_state \<omega>) l = Some v\<close> gr_0_is_ppos
    by (smt (verit, best) PosReal.ppos.rep_eq all_pos option.distinct(1) order.refl wf_mask_simple_def wf_pre_virtual_stateI zero_preal.rep_eq)

  then have "get_vm (get_state ptr) = ?m"
    by (simp add: Abs_virtual_state_inverse get_vm_def ptr_def)
  then have "owns_only ptr l"
    by (simp add: owns_only_def)

  moreover have "Some \<omega> = remove_only \<omega> l \<oplus> ptr"
  proof (rule plus_prodI)
    show "Some (fst \<omega>) = fst (remove_only \<omega> l) \<oplus> fst ptr"
      by (simp add: get_store_def plus_agreement_def ptr_def remove_only_def set_state_def)
    show "Some (snd \<omega>) = snd (remove_only \<omega> l) \<oplus> snd ptr"
    proof (rule plus_prodI)
      show "Some (fst (snd \<omega>)) = fst (snd (remove_only \<omega> l)) \<oplus> fst (snd ptr)"
        by (metis plus_agreement_def prod.exhaust_sel prod.inject ptr_def remove_only_def set_state_def set_state_get_state)
      show "Some (snd (snd \<omega>)) = snd (snd (remove_only \<omega> l)) \<oplus> snd (snd ptr)"
      proof (rule compatible_virtual_state_implies_pre_virtual_state_rev)
        show "Some (Rep_virtual_state (snd (snd \<omega>))) = Rep_virtual_state (snd (snd (remove_only \<omega> l))) \<oplus> Rep_virtual_state (snd (snd ptr))"
        proof (rule plus_prodI)
          show "Some (fst (Rep_virtual_state (snd (snd \<omega>)))) = fst (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) \<oplus> fst (Rep_virtual_state (snd (snd ptr)))"
          proof (rule plus_funI)
            fix la show "Some (fst (Rep_virtual_state (snd (snd \<omega>))) la) =
          fst (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la \<oplus> fst (Rep_virtual_state (snd (snd ptr))) la"
            by (metis SepAlgebra.plus_preal_def \<open>get_vm (get_state ptr) = (\<lambda>l'. if l = l' then PosReal.pwrite else PosReal.pnone)\<close> add.right_neutral assms(1) commutative fun_upd_def get_state_def get_vm_def remove_only_charact(2))
          qed
          show "Some (snd (Rep_virtual_state (snd (snd \<omega>)))) = snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) \<oplus> snd (Rep_virtual_state (snd (snd ptr)))"
          proof (rule plus_funI)
            fix la show "Some (snd (Rep_virtual_state (snd (snd \<omega>))) la) =
          snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la \<oplus> snd (Rep_virtual_state (snd (snd ptr))) la"
            proof (cases "la = l")
              case True
              then have "Some (snd (Rep_virtual_state (snd (snd \<omega>))) la) = Some (get_h \<omega> l)"
                by (simp add: get_state_def get_vh_def)
              moreover have "snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la = None"
                by (metis True fun_upd_same get_state_def get_vh_def remove_only_charact(1))
              moreover have "snd (Rep_virtual_state (snd (snd ptr))) la = get_vh (get_state \<omega>) l"
                unfolding ptr_def using rwf
                by (metis Abs_virtual_state_inverse True get_state_def get_state_set_state mem_Collect_eq snd_conv)
              ultimately show ?thesis
                by simp
            next
              case False
              then have "Some (snd (Rep_virtual_state (snd (snd \<omega>))) la) = Some (get_h \<omega> la)"
                by (simp add: get_state_def get_vh_def)
              moreover have "snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la = get_h \<omega> la"
                by (metis False fun_upd_def get_abs_state_def get_vh_def remove_only_charact(1) snd_get_abs_state)
              moreover have "snd (Rep_virtual_state (snd (snd ptr))) la = get_vh (get_state \<omega>) la"
                unfolding ptr_def using rwf
                by (metis Abs_virtual_state_inverse get_state_def get_state_set_state mem_Collect_eq snd_conv)
              ultimately show ?thesis
              proof -
                have "\<forall>z. (z::'a val option) \<oplus> z = Some z \<or> z = None"
                  by (smt (z3) core_option.cases plus_option.simps(3) plus_val_def)
                then show ?thesis
                  by (smt (z3) \<open>Some (snd (Rep_virtual_state (snd (snd \<omega>))) la) = Some (get_h \<omega> la)\<close> \<open>snd (Rep_virtual_state (snd (snd (remove_only \<omega> l)))) la = get_h \<omega> la\<close> \<open>snd (Rep_virtual_state (snd (snd ptr))) la = get_h \<omega> la\<close> plus_option.simps(1))
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  ultimately show ?thesis
    using ptr_def by blast
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


lemma well_typedE:
  assumes "well_typed \<Gamma> \<omega>"
  shows "well_typed_heap \<Gamma> (snd \<omega>)"
    and "the_ag (fst \<omega>) l = Some \<phi> \<Longrightarrow> well_typed_heap \<Gamma> \<phi>"
  using assms well_typed_def apply blast
  by (meson assms well_typed_def)


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
(* | "wf_custom_stmt _ (Label _) \<longleftrightarrow> True" *)

definition typed_value where
  "typed_value \<Delta> f v \<longleftrightarrow> (\<forall>ty. custom_context \<Delta> f = Some ty \<longrightarrow> v \<in> ty)"

lemma typed_valueI:
  assumes "\<And>ty. custom_context \<Delta> f = Some ty \<Longrightarrow> v \<in> ty"
  shows "typed_value \<Delta> f v"
  by (simp add: assms typed_value_def)


definition update_value where
  "update_value \<Delta> A r f e =
  { \<omega>' |\<omega>' \<omega> l v. typed_value \<Delta> f v \<and>
 \<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)}"

(* TODO: Start from here *)

lemma in_update_value:
  assumes "\<omega> \<in> A"
      and "r \<omega> = Some l"
      and "e \<omega> = Some v"
      and "\<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      and "typed_value \<Delta> f v"
    shows "\<omega>' \<in> update_value \<Delta> A r f e"
  using assms update_value_def by fast

lemma update_valueE:
  assumes "\<omega>' \<in> update_value \<Delta> A r f e"
  shows "\<exists>\<omega> l v. typed_value \<Delta> f v \<and>
 \<omega> \<in> A \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
  using assms update_value_def
  by (smt (verit, best) mem_Collect_eq)

definition assertion_holds_at where
  "assertion_holds_at l A = { \<omega> |\<omega> \<phi>. get_trace \<omega> l = Some \<phi> \<and> set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> \<phi>)) \<in> A }"

inductive SL_Custom :: "('a val, (field_ident \<rightharpoonup> 'a val set)) abs_type_context \<Rightarrow> 'a equi_state set \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state assertion \<Rightarrow> bool"
  where
  RuleFieldAssign: "\<lbrakk> self_framing A; entails A { \<omega> |\<omega> l. get_m \<omega> (l, f) = 1 \<and> r \<omega> = Some l};
  framed_by_exp A r; framed_by_exp A e \<rbrakk> \<Longrightarrow> SL_Custom \<Delta> A (FieldAssign r f e) (update_value \<Delta> A r f e)"
(* | RuleLabel: "SL_Custom \<Delta> A (Label l) (assertion_holds_at l A)" *)


inductive_cases SL_custom_FieldAssign[elim!]: "SL_Custom \<Delta> A (FieldAssign r f e) B"
(* inductive_cases SL_custom_Label[elim!]: "SL_Custom \<Delta> A (Label l) B" *)

(*
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
      proof (rule well_typed_heapI)
        fix hl v assume asm1: "get_vh (snd (get_abs_state \<omega>')) hl = Some v"
        show "\<exists>ty. custom_context \<Delta> (snd hl) = Some ty \<and> v \<in> ty"
        proof (cases "fst hl = l")
          case True
          then show ?thesis
            by (smt (verit, ccfv_SIG) TypedEqui.typed_assertion_def TypedEqui.typed_def \<open>\<And>thesis. (\<And>\<omega> l v ty. \<lbrakk>custom_context \<Delta> f = Some ty; v \<in> ty; \<omega> \<in> A; r \<omega> = Some l; e \<omega> = Some v; \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> asm1 assms get_abs_state_def get_state_def get_state_set_state get_vh_vm_set_value(1) snd_conv well_typedE(1) well_typed_concrete_heap_update well_typed_heapE)
        next
          case False
          then show ?thesis
            by (smt (verit, ccfv_SIG) TypedEqui.typed_assertion_def TypedEqui.typed_def \<open>\<And>thesis. (\<And>\<omega> l v ty. \<lbrakk>custom_context \<Delta> f = Some ty; v \<in> ty; \<omega> \<in> A; r \<omega> = Some l; e \<omega> = Some v; \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> asm1 assms get_abs_state_def get_state_def get_state_set_state get_vh_vm_set_value(1) snd_conv well_typedE(1) well_typed_concrete_heap_update well_typed_heapE)
        qed
      qed
    qed
  qed
qed
*)

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
      by (metis assms(1) assms(2) assms(3) assms(4) stable_virtual_state_def vstate_wf_Some)
  qed
  show "get_vm a = get_vm b"
    by (simp add: assms(1))
qed

lemma stable_virtual_stateI:
  assumes "\<And>hl. get_vh x hl \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm x hl"
  shows "stable x"
  using assms stable_virtual_state_def
  using EquiSemAuxLemma.gr_0_is_ppos by auto



lemma stabilize_set_value:
  assumes "get_m \<omega> l > 0"
  shows "stabilize (set_state \<omega> (set_value (get_state \<omega>) l v)) = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) l v)"
  apply (rule full_state_ext)
    apply (rule ext)
    apply simp
   apply (rule virtual_state_ext_stable)
      apply simp_all
   apply (rule stable_virtual_stateI)
  apply (metis EquiSemAuxLemma.gr_0_is_ppos assms fun_upd_apply get_vh_vm_set_value(1) get_vh_vm_set_value(2) get_vm_stabilize stabilize_is_stable stable_virtual_state_def)
  by (metis (mono_tags, opaque_lifting) fun_upd_other fun_upd_same get_state_set_state get_state_stabilize get_vh_vm_set_value(1) option.sel stabilize_value_persists)

lemma full_state_ext_better:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_state a = get_state b"
    shows "a = b"
  by (metis agreement.exhaust_sel assms(1) assms(2) assms(3) get_state_def get_store_def get_trace_def prod.exhaust_sel)

lemma typed_get_vh:
  assumes "TypedEqui.typed \<Delta> \<omega>"
      and "get_vh (get_state \<omega>) hl = Some v"
      and "custom_context \<Delta> (snd hl) = Some ty"
    shows "v \<in> ty"
  by (metis TypedEqui.typed_def assms get_abs_state_def get_state_def well_typedE(1) well_typed_heapE)

lemma self_framing_update_value:
  fixes \<Delta> :: "('a val, char list \<Rightarrow> 'a val set option) abs_type_context"
  assumes "self_framing A"
      and "wf_exp r"
      and "wf_exp e"
      and "framed_by_exp A r"
      and "framed_by_exp A e"
      and "\<And>\<omega> l. \<omega> \<in> A \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> (l, f) = 1"
    shows "self_framing (update_value \<Delta> A r f e)"
proof (rule self_framingI)
  fix \<omega>'
  show "\<omega>' \<in> update_value \<Delta> A r f e \<longleftrightarrow> stabilize \<omega>' \<in> update_value \<Delta> A r f e" (is "?P \<longleftrightarrow> ?Q")
  proof
    assume ?P
    then obtain \<omega> l v where r: "typed_value \<Delta> f v" "\<omega> \<in> A" "r \<omega> = Some l"
      "e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      using update_valueE[of \<omega>' \<Delta> A r f e] by blast
    then have "r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) wf_exp_framed_by_stabilize)
    moreover have "stabilize \<omega>' = set_state (stabilize \<omega>) (set_value (get_state (stabilize \<omega>)) (l, f) v)"
      by (simp add: assms(6) pperm_pnone_pgt r(2) r(3) r(4) stabilize_set_value)
    ultimately show ?Q
      by (metis assms(1) in_update_value r(1) r(2) self_framing_def)
  next
    assume ?Q
    then obtain \<omega> l v where asm1: "typed_value \<Delta> f v \<and> \<omega> \<in> A" "r \<omega> = Some l"
      "e \<omega> = Some v \<and> stabilize \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, f) v)"
      using update_valueE[of "stabilize \<omega>'" \<Delta> A r f e] by blast
    then have "stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v"
      using self_framingE[OF assms(1)]
      by (meson assms(1) assms(2) assms(3) assms(4) assms(5) wf_exp_framed_by_stabilize)
    have r: "get_store \<omega>' = get_store \<omega> \<and> get_trace \<omega>' = get_trace \<omega> \<and> get_m \<omega>' = get_m \<omega>"
      by (metis AbstractSemantics.get_store_stabilize asm1(3) get_state_set_state get_state_stabilize get_store_set_state get_trace_set_state get_trace_stabilize get_vh_vm_set_value(2) vstate_stabilize_structure(1))
    have "\<exists>x. stabilize x = stabilize \<omega> \<and> \<omega>' = set_state x (set_value (get_state x) (l, f) v)" (* \<and> TypedEqui.typed \<Delta> x" *)
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
        then show "get_state \<omega>' =
    get_state (set_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0)) (set_value (get_state (set_state \<omega>' (set_value (get_state \<omega>') (l, f) v0))) (l, f) v))"
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
(*
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
              apply (metis (mono_tags, lifting) TypedEqui.typed_assertionE \<open>get_h \<omega> (l, f) = Some v0\<close> asm1(1) asm2 assms(7) get_abs_state_def get_state_def get_state_set_state get_vh_vm_set_value(1) map_upd_Some_unfold typed_get_vh)
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
*)
      ultimately show ?thesis by blast
    qed
    then have "\<exists>x. x \<in> A \<and> r x = Some l \<and> e x = Some v \<and> \<omega>' = set_state x (set_value (get_state x) (l, f) v)"
      by (metis \<open>stabilize \<omega> \<in> A \<and> r (stabilize \<omega>) = Some l \<and> e (stabilize \<omega>) = Some v\<close> assms(1) assms(2) assms(3) self_framing_invE wf_exp_stabilize)
    then show ?P
      unfolding update_value_def
      using asm1(1) by blast
  qed
qed



inductive red_custom_stmt :: "('a val, field_ident \<rightharpoonup> 'a val set) abs_type_context \<Rightarrow> 'a custom \<Rightarrow> 'a equi_state \<Rightarrow> 'a equi_state set \<Rightarrow> bool"
  where
  RedFieldAssign: "\<lbrakk> r \<omega> = Some hl ; e \<omega> = Some v ; get_vm (get_state \<omega>) (hl, f) = 1; custom_context \<Delta> f = Some ty; v \<in> ty \<rbrakk>
  \<Longrightarrow> red_custom_stmt \<Delta> (FieldAssign r f e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) (hl, f) v)}"
(* | RedLabel: "red_custom_stmt \<Delta> (Label l) \<omega> {set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> get_state \<omega>)) }" *)

inductive_cases red_custom_stmt_FieldAssign[elim!]: "red_custom_stmt \<Delta> (FieldAssign r f e) \<omega> S"
(* inductive_cases red_custom_stmt_Label[elim!]: "red_custom_stmt \<Delta> (Label l) \<omega> S" *)

(*
  assumes SL_proof_custom: "(\<forall>(\<omega> :: (('v, 'a) abs_state list \<times> ('v, 'a) abs_state)) \<in> SA.
  red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)) \<Longrightarrow> wf_custom_stmt \<Delta> C \<Longrightarrow> wf_set \<Delta> (snd ` SA)
  \<Longrightarrow> SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union>\<omega>\<in>SA. f \<omega>))"
*)
lemma SL_proof_FieldAssign_easy:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> (FieldAssign r g e) (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> (FieldAssign r g e)"
      and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>) \<and> TypedEqui.typed \<Delta> (snd \<alpha>)"
    shows "SL_Custom \<Delta> (Stabilize (snd ` SA)) (FieldAssign r g e) (Stabilize (\<Union> (f ` SA)))"
proof -

  have wfs: "wf_exp r \<and> wf_exp e" using assms by auto

  let ?r = "\<lambda>\<omega>. the (r \<omega>)"
  let ?e = "\<lambda>\<omega>. the (e \<omega>)"

  have r: "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> (r (snd \<alpha>) = Some (?r (snd \<alpha>)) \<and> e (snd \<alpha>) = Some (?e (snd \<alpha>))
  \<and> get_m (snd \<alpha>) (?r (snd \<alpha>), g) = 1
  \<and> (?e (snd \<alpha>)) \<in> (the (custom_context \<Delta> g))
  \<and> f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (?r (snd \<alpha>), g) (?e (snd \<alpha>)))} )"
    using assms(1) by fastforce

  let ?A = "Stabilize (snd ` SA)"
  let ?B = "update_value \<Delta> ?A r g e"


  have "SL_Custom \<Delta> ?A (custom.FieldAssign r g e) ?B"
  proof (rule RuleFieldAssign)
    show "self_framing (Stabilize (snd ` SA))"
      by simp
    show entails_rel: "entails (Stabilize (snd ` SA)) {\<omega> |\<omega> l. get_m \<omega> (l, g) = PosReal.pwrite \<and> r \<omega> = Some l}"
    proof (rule entailsI)
      fix \<omega> assume "\<omega> \<in> Stabilize (snd ` SA)"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by (meson imageE in_Stabilize)
      then obtain l where "get_m (stabilize \<omega>) (l, g) = PosReal.pwrite \<and> r (stabilize \<omega>) = Some l"
        by (metis r)
      then have "get_m \<omega> (l, g) = 1 \<and> r \<omega> = Some l"
        using wf_exp_stabilize wfs by force
      then show "\<omega> \<in> {\<omega> |\<omega> l. get_m \<omega> (l, g) = 1 \<and> r \<omega> = Some l}"
        by blast
    qed
    then show "framed_by_exp (Stabilize (snd ` SA)) r"
      by (smt (verit, best) Collect_mem_eq Collect_mono_iff entails_def framed_by_exp_def option.distinct(1))
    show "framed_by_exp (Stabilize (snd ` SA)) e"
      by (smt (verit, ccfv_threshold) framed_by_exp_def image_iff in_Stabilize option.distinct(1) r wf_exp_stabilize wfs)
  qed
  moreover have "?B = Stabilize (\<Union> (f ` SA))" (is "?B = ?Q")
  proof (rule self_framing_ext)
    show "self_framing (update_value \<Delta> (Stabilize (snd ` SA)) r g e)"
    proof (rule self_framing_update_value)
      show "wf_exp r" using wfs by simp
      show "wf_exp e" using wfs by simp
      show "framed_by_exp (Stabilize (snd ` SA)) r"
        using calculation by force
      show "framed_by_exp (Stabilize (snd ` SA)) e"
        using calculation by fastforce
      show "\<And>\<omega> l. \<omega> \<in> Stabilize (snd ` SA) \<Longrightarrow> r \<omega> = Some l \<Longrightarrow> get_m \<omega> (l, g) = 1"
        by (metis (no_types, opaque_lifting) RangeE Stabilize_self_framing \<open>framed_by_exp (Stabilize (snd ` SA)) r\<close> \<open>wf_exp r\<close> get_m_stabilize in_Stabilize option.sel r snd_conv snd_eq_Range wf_exp_framed_by_stabilize)
    qed (simp_all)

    show "self_framing (Stabilize (\<Union> (f ` SA)))"
      by simp

    fix \<omega>' :: "((nat \<Rightarrow> 'b val option) agreement \<times> (char list \<Rightarrow> 'b virtual_state option) agreement \<times> 'b virtual_state)"
    assume asm0: "sep_algebra_class.stable \<omega>'"
    show "\<omega>' \<in> Stabilize (\<Union> (f ` SA)) \<Longrightarrow> \<omega>' \<in> update_value \<Delta> (Stabilize (snd ` SA)) r g e"
    proof -
      assume asm1: "\<omega>' \<in> Stabilize (\<Union> (f ` SA))"
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega>' \<in> f \<alpha>"
        by auto

(* "TypedEqui.typed \<Delta> \<omega>'"
        by (metis (no_types, lifting) TypedEqui.Stabilize_typed_def UN_E in_Stabilize member_filter)
*)

      then obtain l v where "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)}"  "r (snd \<alpha>) = Some l" "e (snd \<alpha>) = Some v"
        using r[of \<alpha>] by blast
      then have "stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)"
        using \<open>stabilize \<omega>' \<in> f \<alpha>\<close> by blast
      moreover have "stable (snd \<alpha>)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> assms(3))
      ultimately have "snd \<alpha> \<in> Stabilize (snd ` SA)"
        by (simp add: \<open>\<alpha> \<in> SA\<close> already_stable)
(*
      moreover have "TypedEqui.typed \<Delta> (stabilize \<omega>')"
        by (simp add: TypedEqui.typed_state_then_stabilize_typed asm0(2))
*)
      moreover have "stabilize \<omega>' \<in> ?B"
        using in_update_value[of _ _ r _ e, OF _ \<open>r (snd \<alpha>) = Some l\<close> \<open>e (snd \<alpha>) = Some v\<close>
            \<open>stabilize \<omega>' = set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (l, g) v)\<close>]
        by (smt (verit, ccfv_threshold) \<open>\<alpha> \<in> SA\<close> \<open>e (snd \<alpha>) = Some v\<close> calculation option.sel r typed_value_def)
      then show "\<omega>' \<in> ?B" unfolding update_value_def
        by (simp add: \<open>sep_algebra_class.stable \<omega>'\<close> already_stable)
    qed
    
    show "\<omega>' \<in> update_value \<Delta> (Stabilize (snd ` SA)) r g e \<Longrightarrow> \<omega>' \<in> Stabilize (\<Union> (f ` SA))"
    proof -
      assume "\<omega>' \<in> update_value \<Delta> (Stabilize (snd ` SA)) r g e"
      then obtain \<omega> l v where "\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)"
        unfolding update_value_def by blast
      then obtain \<alpha> where "\<alpha> \<in> SA" "stabilize \<omega> = snd \<alpha>"
        by auto
      then have "f \<alpha> = {set_state (snd \<alpha>) (set_value (get_state (snd \<alpha>)) (the (r (snd \<alpha>)), g) (the (e (snd \<alpha>))))}"
        using r by blast
      moreover have "the (r (snd \<alpha>)) = l \<and> the (e (snd \<alpha>)) = v"
        by (metis (no_types, lifting) \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> option.sel r wf_exp_stabilize wfs)
      then have "stabilize \<omega>' \<in> f \<alpha>"
        by (metis \<open>\<alpha> \<in> SA\<close> \<open>\<omega> \<in> Stabilize (snd ` SA) \<and> r \<omega> = Some l \<and> e \<omega> = Some v \<and> \<omega>' = set_state \<omega> (set_value (get_state \<omega>) (l, g) v)\<close> \<open>stabilize \<omega> = snd \<alpha>\<close> get_m_stabilize pperm_pnone_pgt r singleton_iff stabilize_set_value zero_neq_one)
      then show "\<omega>' \<in> Stabilize (\<Union> (f ` SA))"
        using \<open>\<alpha> \<in> SA\<close> by auto
    qed
  qed
  ultimately show ?thesis by argo
qed




lemma SL_proof_aux_custom:
  assumes "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>)"
      and "wf_custom_stmt \<Delta> C"
    and "\<And>\<alpha>. \<alpha> \<in> SA \<Longrightarrow> stable (snd \<alpha>) \<and> TypedEqui.typed \<Delta> (snd \<alpha>)"
  shows "SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union> (f ` SA)))"
proof (cases C)
  case (FieldAssign r g e)
  then show ?thesis
    using SL_proof_FieldAssign_easy assms by blast
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
  case (RuleFieldAssign A f r e \<Delta>)
  then obtain hl v where "r \<omega> = Some hl" "e \<omega> = Some v" "get_m \<omega> (hl, f) = 1"
    by (smt (verit, ccfv_SIG) CollectD entails_def framed_by_expE subset_iff)
  then obtain ty where "custom_context \<Delta> f = Some ty" "v \<in> ty"
    by (meson RuleFieldAssign.prems(2) TypedEqui.typed_exp_def wf_custom_stmt.simps(1))
  then have "red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega> {set_state \<omega> (set_value (get_state \<omega>) (hl, f) v)}"
    using RedFieldAssign[of r \<omega> hl e v f \<Delta> ty]
    using \<open>e \<omega> = Some v\<close> \<open>get_m \<omega> (hl, f) = PosReal.pwrite\<close> \<open>r \<omega> = Some hl\<close> by fastforce
  then show "\<exists>S. red_custom_stmt \<Delta> (custom.FieldAssign r f e) \<omega> S \<and> S \<subseteq> update_value \<Delta> A r f e"
    by (metis (no_types, lifting) RuleFieldAssign.prems(1) \<open>custom_context \<Delta> f = Some ty\<close> \<open>e \<omega> = Some v\<close> \<open>r \<omega> = Some hl\<close> \<open>v \<in> ty\<close> in_update_value option.inject singletonD subsetI typed_value_def)
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
      fix hl v ty assume "get_vh (snd (get_abs_state \<omega>')) hl = Some v" "custom_context \<Delta> (snd hl) = Some ty"
      then show "v \<in> ty"
        by (metis (mono_tags, lifting) RedFieldAssign.hyps(4) RedFieldAssign.hyps(5) RedFieldAssign.prems(1) RedFieldAssign.prems(3) fun_upd_triv get_abs_state_def get_state_def get_state_set_state get_vh_vm_set_value(1) heap_typed_insert singletonD snd_conv well_typedE(1))
    qed
  qed
(*
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
*)
qed



global_interpretation ConcreteSemantics: semantics well_typed red_custom_stmt wf_custom_stmt SL_Custom
proof
  fix SA :: "('a equi_state list \<times> 'a equi_state) set"
  fix \<Delta> C f
  show "\<forall>\<omega>\<in>SA. red_custom_stmt \<Delta> C (snd \<omega>) (f \<omega>) \<Longrightarrow>
       wf_custom_stmt \<Delta> C \<Longrightarrow>
       TypedEqui.wf_set \<Delta> (snd ` SA) \<Longrightarrow> SL_Custom \<Delta> (Stabilize (snd ` SA)) C (Stabilize (\<Union> (f ` SA)))"    
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

abbreviation typed where
  "typed \<equiv> TypedEqui.typed"

(*
text \<open>'v represents the type of the "domain" values, and 'a the type of Viper resource states\<close>

record ('v, 'a) interp =
  domains :: "'v \<Rightarrow> abs_type"
  predicates :: "'v predicate_loc \<rightharpoonup> 'a set"
  funs :: "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'a \<rightharpoonup> 'v val"
*)

(* TODO: unify make_context_semantic, s2a_ctxt and t2a_ctxt? *)
definition make_context_semantic  :: "('a, 'a virtual_state) interp \<Rightarrow> (nat \<Rightarrow> vtyp option) \<times> (char list \<Rightarrow> vtyp option) \<Rightarrow> ('a val, char list \<Rightarrow> 'a val set option) abs_type_context"
  where
  "make_context_semantic \<Delta> F = \<lparr> variables = (sem_store (domains \<Delta>) (fst F)), custom_context = (sem_fields (domains \<Delta>) (snd F))  \<rparr>"

definition well_typedly (* :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> 'a equi_state set \<Rightarrow> 'a equi_state set"*)
  where
    "well_typedly \<Delta> F A = Set.filter (typed (make_context_semantic \<Delta> F)) A"
(*
A \<inter> {\<omega> |\<omega>. typed (make_context_semantic \<Delta> F)}"
*)

lemma well_typedly_incl :
  shows "well_typedly \<Delta> F A \<subseteq> A"
  by (simp add: subset_iff well_typedly_def)

lemma well_typedly_add_set1 :
  shows "well_typedly \<Delta> F A1 \<otimes> well_typedly \<Delta> F A2 \<subseteq> well_typedly \<Delta> F (A1 \<otimes> A2)"
  unfolding well_typedly_def add_set_def
  apply (auto)
   apply blast
  using TypedEqui.typed_sum by blast

lemma well_typedly_plus1 :
  assumes "Some \<phi> = a \<oplus> b"
  assumes "typed (make_context_semantic \<Delta> F) \<phi>"
  shows "typed (make_context_semantic \<Delta> F) a"
  using TypedEqui.typed_state_axioms assms(1) assms(2) greater_def typed_state.typed_smaller by blast


lemma well_typedly_plus :
  assumes "Some \<phi> = a \<oplus> b"
  assumes "typed (make_context_semantic \<Delta> F) \<phi>"
  shows "typed (make_context_semantic \<Delta> F) a"
   and "typed (make_context_semantic \<Delta> F) b"
  using assms(1) assms(2) well_typedly_plus1 apply blast
  by (metis assms(1) assms(2) commutative well_typedly_plus1)

lemma well_typedly_add_set2 :
  shows "well_typedly \<Delta> F (A1 \<otimes> A2) \<subseteq> well_typedly \<Delta> F A1 \<otimes> well_typedly \<Delta> F A2"
  unfolding well_typedly_def add_set_def
  using well_typedly_plus
  by (smt (verit) mem_Collect_eq member_filter subsetI)


lemma well_typedly_add_set :
  shows "well_typedly \<Delta> F A1 \<otimes> well_typedly \<Delta> F A2 = well_typedly \<Delta> F (A1 \<otimes> A2)"
  using well_typedly_add_set1 well_typedly_add_set2 by blast

lemma well_typedly_add_set_l :
  shows "well_typedly \<Delta> F (A1 \<otimes> A2) \<subseteq> A1 \<otimes> well_typedly \<Delta> F A2"
  unfolding well_typedly_def add_set_def
  using well_typedly_plus
  by (smt (verit) CollectD CollectI member_filter subsetI)

lemma Stable_well_typedly :
  assumes "Stable A"
  shows "Stable (well_typedly \<Delta> F A)"
  using assms          
  apply (simp add:Stable_def Stabilize_def well_typedly_def)
  using TypedEqui.typed_state_then_stabilize_typed by fastforce

definition make_semantic_assertion_gen
  :: "bool \<Rightarrow> ('a, 'a virtual_state) interp \<Rightarrow> ((var \<rightharpoonup> vtyp) \<times> (field_name \<rightharpoonup> vtyp)) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state set"
  where
  "make_semantic_assertion_gen ta \<Delta> F A = (if ta then well_typedly \<Delta> F else (\<lambda> x. x)) (\<langle>\<Delta>, snd F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
  (*"make_semantic_assertion \<Delta> F A = \<langle>\<Delta>, snd F\<rangle> \<Turnstile> \<langle>A\<rangle>" *)

abbreviation make_semantic_assertion where
 "make_semantic_assertion \<equiv> make_semantic_assertion_gen True"

lemma make_semantic_assertion_def :
  "make_semantic_assertion \<Delta> F A = well_typedly \<Delta> F (\<langle>\<Delta>, snd F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
  by (simp add:make_semantic_assertion_gen_def)

abbreviation make_semantic_assertion_untyped where
 "make_semantic_assertion_untyped \<equiv> make_semantic_assertion_gen False"

(*
lemma well_behaved:
  "TypedEqui.typed_assertion \<Delta> (Set.filter stable (\<langle>\<Delta>, snd F\<rangle> \<Turnstile> \<langle>A\<rangle>))" oops
*)

(*


typed (make_context_semantic \<Delta> F)
*)

lemma make_semantic_assertion_in_unfold :
  shows "make_semantic_assertion \<Delta> F A \<subseteq> \<langle>\<Delta>, snd F\<rangle> \<Turnstile> \<langle>A\<rangle>"
  by (simp add:make_semantic_assertion_gen_def well_typedly_incl)

fun compile (* :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> stmt \<Rightarrow> ('a equi_state, 'a val, 'a custom) abs_stmt" *)
  where
  "compile ta \<Delta> F stmt.Skip = abs_stmt.Skip"

| "compile ta \<Delta> F (stmt.If b C1 C2) = abs_stmt.If (make_semantic_bexp \<Delta> b) (compile ta \<Delta> F C1) (compile ta \<Delta> F C2)"
| "compile ta \<Delta> F (stmt.Seq C1 C2) = abs_stmt.Seq (compile ta \<Delta> F C1) (compile ta \<Delta> F C2)"

| "compile ta \<Delta> F (stmt.Havoc x) = abs_stmt.Havoc x"
| "compile ta \<Delta> F (stmt.LocalAssign x e) = abs_stmt.LocalAssign x (make_semantic_exp \<Delta> e)"


| "compile ta \<Delta> F (stmt.Inhale A) = abs_stmt.Inhale (make_semantic_assertion_gen ta \<Delta> F A)"
| "compile ta \<Delta> F (stmt.Exhale A) = abs_stmt.Exhale (make_semantic_assertion_gen ta \<Delta> F A)"
| "compile ta \<Delta> F (stmt.Assert A) = abs_stmt.Assert (make_semantic_assertion_gen ta \<Delta> F A)"
| "compile ta \<Delta> F (stmt.Assume A) = abs_stmt.Assume (make_semantic_assertion_gen ta \<Delta> F A)"

| "compile ta \<Delta> F (stmt.Unfold _ _ _) = abs_stmt.Skip"
| "compile ta \<Delta> F (stmt.Fold _ _ _) = abs_stmt.Skip"
| "compile ta \<Delta> F (stmt.Package _ _) = abs_stmt.Skip"
| "compile ta \<Delta> F (stmt.Apply _ _) = abs_stmt.Skip"

(* TODO: We can take the program as input, and emit the encodings *)
| "compile ta \<Delta> F (stmt.MethodCall _ _ _) = undefined"
| "compile ta \<Delta> F (stmt.While b I C) = undefined"
| "compile ta \<Delta> F (stmt.Scope _ _) = undefined"
| "compile ta \<Delta> F (stmt.Label l) = undefined"

| "compile ta \<Delta> F (stmt.FieldAssign r f e) = abs_stmt.Custom (FieldAssign (make_semantic_rexp \<Delta> r) f (make_semantic_exp \<Delta> e))"





(*
definition viper_prog_verifies where
  "viper_prog_verifies Pr \<Delta> ty C \<omega> \<longleftrightarrow> ConcreteSemantics.verifies ty (compile \<Delta> F C) \<omega>"
  (* ty is a type-context *)
*)












(* TODO:

*)



(*

lemma make_semantic_assertion_inh :
  "\<langle>make_semantic_assertion \<Delta> F A\<rangle> = (\<langle>\<Delta>,F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
  by (simp add:ConcreteSemantics.inh_def make_semantic_assertion_def)
*)


section \<open>red_stmt with (overapproximating) postcondition\<close>

definition concrete_red_stmt_post (* :: "('a val, address) abs_type_context \<Rightarrow>
   ('a equi_state, 'a val, address) abs_stmt \<Rightarrow>
   ('a val, 'a virtual_state) abs_state \<Rightarrow> ('a val, 'a virtual_state) abs_state set \<Rightarrow> bool"
  *)
  where
"concrete_red_stmt_post \<Delta> C \<omega> S \<longleftrightarrow> (\<exists> S'. ConcreteSemantics.red_stmt \<Delta> C \<omega> S' \<and> S' \<subseteq> S)"

lemma concrete_red_stmt_post_impl :
  assumes "concrete_red_stmt_post \<Delta> C \<omega> S'"
  assumes "S' \<subseteq> S"
  shows "concrete_red_stmt_post \<Delta> C \<omega> S"
  using assms unfolding concrete_red_stmt_post_def by blast

lemma concrete_red_stmt_post_stable_wf :
  assumes "stable \<omega>"
  assumes "concrete_red_stmt_post \<Delta> C \<omega> {\<omega>'. stable \<omega>' \<longrightarrow> \<omega>' \<in> S}"
  shows "concrete_red_stmt_post \<Delta> C \<omega> S"
  using assms unfolding concrete_red_stmt_post_def using ConcreteSemantics.red_stable by blast

lemma concrete_post_Inhale :
  assumes "rel_stable_assertion \<omega> A"
  assumes "(Set.filter sep_algebra_class.stable ({\<omega>} \<otimes> A)) \<subseteq> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Inhale A) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def
  by (smt (verit, del_insts) ConcreteSemantics.RedInhale in_mono member_filter subsetI)

lemma concrete_post_Exhale_raw :
  assumes "a \<in> A"
  assumes "Some \<omega> = \<omega>' \<oplus> a"
  assumes "sep_algebra_class.stable \<omega>'"
  assumes "\<omega>' \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Exhale A) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def by (blast intro: ConcreteSemantics.RedExhale)

lemma concrete_post_Exhale :
  assumes "stable \<omega>"
  assumes "\<omega> \<in> {\<omega>'} \<otimes> A"
  assumes "stabilize \<omega>' \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Exhale A) \<omega> S"
  apply (rule star_to_singleton_stabilizeE)
  using assms apply (simp)
  using assms apply (simp)
  apply (clarsimp simp add: add_set_def)
  apply (rule concrete_post_Exhale_raw; simp?)
   apply (simp)
  using assms by (simp)

lemma concrete_post_Assert :
  assumes "\<omega> \<in> A"
  assumes "\<omega> \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Assert A) \<omega> S"
  unfolding concrete_red_stmt_post_def
  using assms
  by (blast intro: ConcreteSemantics.RedAssertTrue)

lemma concrete_post_If :
  assumes "e \<omega> = Some b"
  assumes "concrete_red_stmt_post \<Delta> (if b then C1 else C2) \<omega> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.If e C1 C2) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def
  apply (safe)
  apply (rule exI, rule conjI; assumption?)
  by (cases "b"; auto intro: ConcreteSemantics.RedIfTrue ConcreteSemantics.RedIfFalse)

lemma concrete_post_Seq :
  assumes "concrete_red_stmt_post \<Delta> C1 \<omega> { \<omega>'. concrete_red_stmt_post \<Delta> C2 \<omega>' S}"
  shows "concrete_red_stmt_post \<Delta> (C1;; C2) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def
proof -

  let ?S = "{\<omega>'. \<exists>S'. ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' S' \<and> S' \<subseteq> S}"
  let ?f = "\<lambda> \<omega>'. SOME S'. ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' S' \<and> S' \<subseteq> S"

  have r: "\<And>\<omega>'. \<omega>' \<in> ?S \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' (?f \<omega>') \<and> ?f \<omega>' \<subseteq> S"
  proof -
    fix \<omega>' assume "\<omega>' \<in> ?S"
    then obtain S'' where "ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' S'' \<and> S'' \<subseteq> S"
      by blast
    then show "ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' (?f \<omega>') \<and> ?f \<omega>' \<subseteq> S"
      by (rule someI)
  qed

  assume "\<exists>S'. ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S' \<and> S' \<subseteq> {\<omega>'. \<exists>S'. ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' S' \<and> S' \<subseteq> S}"
  then obtain S' where asm0: "ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S'" "S' \<subseteq> ?S"
    by blast

  let ?S' = "\<Union>\<omega>' \<in> S'. ?f \<omega>'"

  have "ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> ?S'"
  proof (rule ConcreteSemantics.RedSeq)
    show "ConcreteSemantics.red_stmt \<Delta> C1 \<omega> S'" using asm0 by blast
    show "ConcreteSemantics.sequential_composition \<Delta> S' C2 (\<Union>\<omega>'\<in>S'. ?f \<omega>')"
    proof (rule ConcreteSemantics.SeqComp)
      show "\<And>\<omega>'. \<omega>' \<in> S' \<Longrightarrow> ConcreteSemantics.red_stmt \<Delta> C2 \<omega>' (?f \<omega>')"
        using asm0(2) r by blast
    qed (simp)
  qed
  then show "\<exists>S'. ConcreteSemantics.red_stmt \<Delta> (C1 ;; C2) \<omega> S' \<and> S' \<subseteq> S"
    by (metis (no_types, lifting) SUP_least asm0(2) r subset_iff)
qed

lemma concrete_post_LocalAssign :
  assumes "variables \<Delta> x = Some ty"
  assumes "e \<omega> = Some v"
  assumes "v \<in> ty"
  assumes "set_store \<omega> ((get_store \<omega>)(x \<mapsto> v)) \<in> S"
  shows "concrete_red_stmt_post \<Delta> (LocalAssign x e) \<omega> S"
  using assms
  apply (simp add: concrete_red_stmt_post_def)
  apply (rule exI, rule conjI)
   apply (solves \<open>rule ConcreteSemantics.RedLocalAssign; assumption\<close>)
  by (simp add: TypedEqui.assign_var_state_def)

lemma concrete_post_FieldAssign :
  assumes "r \<omega> = Some hl"
  assumes "e \<omega> = Some v"
  assumes "has_write_perm_only (get_state \<omega>) (hl, f)"
  assumes "custom_context \<Delta> f = Some ty"
  assumes "v \<in> ty"
  assumes "set_state \<omega> (set_value (get_state \<omega>) (hl, f) v) \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Custom (FieldAssign r f e)) \<omega> S"
  using assms
  apply (simp add: concrete_red_stmt_post_def has_write_perm_only_def)
  apply (rule exI, rule conjI)
   apply (rule ConcreteSemantics.RedCustom, rule RedFieldAssign; assumption)
  by simp

lemma concrete_post_Havoc :
  assumes "variables \<Delta> x = Some ty"
  assumes "{set_store \<omega> ((get_store \<omega>)(x \<mapsto> v)) | v. v \<in> ty } \<subseteq> S"
  shows "concrete_red_stmt_post \<Delta> (Havoc x) \<omega> S"
  using assms
  apply (simp add: concrete_red_stmt_post_def)
  apply (rule exI, rule conjI)
   apply (solves \<open>rule ConcreteSemantics.RedHavoc; assumption\<close>)
  by (simp add: TypedEqui.assign_var_state_def)

(* No Scope
lemma concrete_post_Scope :
  assumes "concrete_red_stmt_post \<Delta> s (\<omega>) S"
  shows "concrete_red_stmt_post \<Delta> (Scope ty s) \<omega> S"
  using assms
  apply (clarsimp simp add: concrete_red_stmt_post_def)
  (* TODO: add semantics for Scope *)
  oops
*)
(*
lemma concrete_post_Label :
  shows "set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> get_state \<omega>)) \<in> S \<Longrightarrow> concrete_red_stmt_post \<Delta> (Custom (Label l)) \<omega> S"
  unfolding concrete_red_stmt_post_def
  apply (rule exI, rule conjI)
   apply (rule ConcreteSemantics.RedCustom)
   apply (rule RedLabel)
  by simp
*)

lemma concrete_post_Skip :
  shows "\<omega> \<in> S \<Longrightarrow> concrete_red_stmt_post \<Delta> Skip \<omega> S"
  unfolding concrete_red_stmt_post_def
  apply (rule exI, rule conjI)
   apply (rule ConcreteSemantics.RedSkip)
  by (auto)


end