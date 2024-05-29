theory Instantiation
  imports AbstractSemantics AbstractSemanticsProperties EquiViper EquiSemAuxLemma
begin

(* TODO: Where to put this? *)
(* TODO: make this a simp lemma? *)
lemma restrict_map_eq_Some :
  "(m |` A) x = Some y \<longleftrightarrow> m x = Some y \<and> x \<in> A"
  by (simp add:restrict_map_def)

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

lemma make_semantic_bexp_Some[simp]:
  shows "make_semantic_bexp \<Delta> b \<omega> = Some vb \<longleftrightarrow> \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool vb)"
  by (simp add:make_semantic_bexp_def split:if_splits; cases vb; auto dest:red_pure_val_unique)

lemma make_semantic_exp_Some[simp]:
  shows "make_semantic_exp \<Delta> b \<omega> = Some v \<longleftrightarrow> \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v"
  by (simp add:make_semantic_exp_def split:if_splits; auto intro:someI dest:red_pure_val_unique)

lemma make_semantic_rexp_Some[simp]:
  shows "make_semantic_rexp \<Delta> r f \<omega> = Some av \<longleftrightarrow> (\<exists> a. (\<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))) \<and> av = (a, f))"
  by (simp add:make_semantic_rexp_def split:if_splits; auto dest:red_pure_val_unique)

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


lift_definition acc_virt :: "heap_loc \<Rightarrow> preal \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" is
"\<lambda> hl p v. ((\<lambda> hl'. if hl = hl' then (pmin 1 p) else 0), [hl \<mapsto> v])"
  apply (simp add:sup_preal.rep_eq wf_pre_virtual_state_def wf_mask_simple_def)
  using all_pos gr_0_is_ppos by blast

lemma acc_virt_get_vm [simp]:
  shows "get_vm (acc_virt hl p v) hl' = (if hl = hl' then pmin 1 p else 0)"
  by (simp add:get_vm_def acc_virt.rep_eq)

lemma acc_virt_get_vm' :
  shows "get_vm (acc_virt hl p v) = (\<lambda> hl'. (if hl = hl' then pmin 1 p else 0))"
  by (rule ext, rule acc_virt_get_vm)

lemma acc_virt_get_vh [simp]:
  "get_vh (acc_virt hl p v) = Map.empty(hl \<mapsto> v)"
  by (simp add:acc_virt.rep_eq get_vh_def)

lemma stabilize_acc_virt :
  assumes "ppos p"
  shows "stabilize (acc_virt hl p v) = acc_virt hl p v"
  apply (rule virtual_state_ext; simp add:vstate_stabilize_structure)
  using assms by (simp add:norm_preal preal_to_real)

definition acc_heap_loc :: "('a, 'a virtual_state) interp \<Rightarrow> vtyp \<Rightarrow> heap_loc \<Rightarrow> real \<Rightarrow> 'a equi_state set" where
"acc_heap_loc \<Delta> ty hl p = {\<omega> | v \<omega>. get_state \<omega> = acc_virt hl (Abs_preal p) v \<and> 0 < p \<and> p \<le> 1 \<and> has_type (domains \<Delta>) ty v }"



lemma acc_heap_loc_Stable [simp] :
  "Stable (acc_heap_loc \<Delta> ty hl p)"
  apply (clarsimp simp add:acc_heap_loc_def)
  apply (rule StableI)
  by (auto simp add: vstate_stabilize_structure restrict_map_eq_Some norm_preal preal_to_real stabilize_acc_virt)


lemma abs_state_star_singletonI :
  assumes "get_store \<omega>' = get_store \<omega>"
  assumes "get_trace \<omega>' = get_trace \<omega>"
  assumes "make_abs_state (get_store \<omega>) (get_trace \<omega>) st \<in> A"
  assumes "Some (get_state \<omega>') = get_state \<omega> \<oplus> st"
  shows "\<omega>' \<in> {\<omega>} \<otimes> A"
  apply (subst in_add_set)
  apply (rule exI, rule exI)
  apply (safe)
    apply (rule refl)
   apply (rule assms(3))
  using assms
  by (smt (verit, best) abs_state_ext_iff get_state_make_abs_state get_store_make_abs_state get_trace_make_abs_state option.discI option.sel plus_state_def set_state_def set_state_make_abs_state)

lemma acc_heap_loc_starI :
  assumes "0 < p"
  assumes "Abs_preal p \<le> get_vm (get_state \<omega>') hl"
  assumes "get_vh (get_state \<omega>') hl = Some v"
  assumes "\<omega> = set_state \<omega>' (del_perm (get_state \<omega>') hl (Abs_preal p))"
  assumes "has_type (domains \<Delta>) ty v"
  shows "\<omega>' \<in> {\<omega>} \<otimes> acc_heap_loc \<Delta> ty hl p"
  apply (rule abs_state_star_singletonI)
  using assms apply (solves \<open>simp\<close>)
  using assms apply (solves \<open>simp\<close>)
    using assms apply (simp add:acc_heap_loc_def)
    apply (rule, safe; assumption?) apply (rule)
     apply (insert get_vm_bound[of "get_state \<omega>'" hl])
     apply (solves \<open>simp add:preal_to_real\<close>)
  using assms apply (simp add:vstate_add_iff acc_virt_get_vm')
  apply (safe)
  subgoal
    by (simp add:fun_plus_iff plus_val_id)
  subgoal
    apply (subgoal_tac "Abs_preal p \<le> 1") defer 1 using get_vm_bound order_trans apply blast
    by (clarsimp simp add:fun_plus_iff preal_plus_iff norm_preal preal_to_real)
  done

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
  by (metis (no_types, lifting) assms(1) assms(2) full_add_charact(2) full_add_defined greater_charact in_set_sum option.discI singletonD x_elem_set_product)

lemma acc_heap_loc_starE :
  assumes "\<omega>' \<in> {\<omega>} \<otimes> acc_heap_loc \<Delta> ty hl p"
  shows "\<exists> v. \<omega>' = set_state \<omega> (add_perm (get_state \<omega>) hl (Abs_preal p) v) \<and> 0 < p \<and> p \<le> 1 \<and> get_vm (get_state \<omega>) hl + Abs_preal p \<le> 1 \<and>
      has_type (domains \<Delta>) ty v \<and> (get_vh (get_state \<omega>) ## [hl \<mapsto> v])"
  apply (insert assms)
  apply (erule abs_state_star_singletonE) subgoal for \<omega>''
    apply (clarsimp simp add:acc_heap_loc_def) subgoal for v
      apply (rule exI[of _ v], safe)
      subgoal
      apply (clarsimp simp add: abs_state_ext_iff vstate_add_iff acc_virt_get_vm')
      apply (rule virtual_state_ext; simp)
        apply (rule ext)
        subgoal for hl'
          apply (drule plus_funE[where l=hl'])
          apply (drule plus_funE[where l=hl'])
          apply (simp add:preal_plus_iff preal_to_real split:if_splits)
          by (smt (verit, best) get_vm_bound less_eq_preal.rep_eq one_preal.rep_eq)
      apply (rule ext) subgoal for x
          apply (drule plus_funE[of _ _ _ x]; simp split:if_splits)
          by (metis commutative option.distinct(1) option.sel plus_option.simps(1) val_option_sum)
        done
      subgoal
        apply (clarsimp simp add: vstate_add_iff acc_virt_get_vm')
        apply (drule plus_funE[where l=hl and x="get_vm _"])
        apply (simp add:preal_plus_iff)
        apply (insert get_vm_bound[of "get_state \<omega>'" "hl"])
        by (simp add:norm_preal preal_to_real)
    apply (simp add:vstate_add_iff defined_def) by metis
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
     (if v = VBool False then (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>) else emp)
                                    )"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A && B\<rangle>) = ((\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) \<otimes> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>))"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A --* B\<rangle>) = ((\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>) --\<otimes> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>))"
(* | "\<Delta> \<Turnstile> \<langle>ForAll ty A\<rangle> \<longleftrightarrow> (\<forall>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)" *)
(* | "\<Delta> \<Turnstile> \<langle>Exists ty A\<rangle> \<longleftrightarrow> (\<exists>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)" *)
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>ImpureAnd A B\<rangle>) = \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<inter> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>"
| "(\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>ImpureOr A B\<rangle>) = \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<union> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>B\<rangle>"


definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state \<Rightarrow> bool" where
  "make_semantic_assertion \<Delta> F A \<omega> \<longleftrightarrow> \<omega> \<in> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>)"

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

fun compile :: "('a, 'a virtual_state) interp \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> stmt \<Rightarrow> ('a equi_state, 'a val, address \<times> field_ident) abs_stmt"
  where
  "compile \<Delta> F stmt.Skip = abs_stmt.Skip"

| "compile \<Delta> F (stmt.If b C1 C2) = abs_stmt.If (make_semantic_bexp \<Delta> b) (compile \<Delta> F C1) (compile \<Delta> F C2)"
| "compile \<Delta> F (stmt.Seq C1 C2) = abs_stmt.Seq (compile \<Delta> F C1) (compile \<Delta> F C2)"

| "compile \<Delta> F (stmt.Scope ty C) = abs_stmt.Scope (make_semantic_vtyp \<Delta> ty) (compile \<Delta> F C)"
| "compile \<Delta> F (stmt.Havoc x) = abs_stmt.Havoc x"
| "compile \<Delta> F (stmt.LocalAssign x e) = abs_stmt.LocalAssign x (make_semantic_exp \<Delta> e)"
| "compile \<Delta> F (stmt.FieldAssign r f e) = abs_stmt.FieldAssign (make_semantic_rexp \<Delta> r f) (make_semantic_exp \<Delta> e)"

| "compile \<Delta> F (stmt.Label l) = abs_stmt.Label l"

| "compile \<Delta> F (stmt.Inhale A) = abs_stmt.Inhale (make_semantic_assertion \<Delta> F A)"
| "compile \<Delta> F (stmt.Exhale A) = abs_stmt.Exhale (make_semantic_assertion \<Delta> F A)"
| "compile \<Delta> F (stmt.Assert A) = abs_stmt.Assert (make_semantic_assertion \<Delta> F A)"
| "compile \<Delta> F (stmt.Assume A) = abs_stmt.Assume (make_semantic_assertion \<Delta> F A)"

| "compile \<Delta> F (stmt.Unfold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> F (stmt.Fold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> F (stmt.Package _ _) = abs_stmt.Skip"
| "compile \<Delta> F (stmt.Apply _ _) = abs_stmt.Skip"

(* TODO: We can take the program as input, and emit the encodings *)
| "compile \<Delta> F (stmt.MethodCall _ _ _) = undefined"
| "compile \<Delta> F (stmt.While b I C) = undefined"


definition has_write_perm_only :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> bool" where
  "has_write_perm_only \<phi> hl \<longleftrightarrow> get_vm \<phi> hl = 1"
(* Could be expressed as "set_value" is frame-preserving
*)

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

global_interpretation ConcreteSemantics: semantics has_value has_write_perm_only set_value
proof
  fix x a b :: "'a virtual_state"
  fix hl :: "address \<times> field_ident"
  fix v :: "'a val"
  show "Some x = a \<oplus> b \<Longrightarrow> sep_algebra_class.stable b \<Longrightarrow> has_write_perm_only a hl \<Longrightarrow> Some (set_value x hl v) = set_value a hl v \<oplus> b"
    sorry

  show "has_write_perm_only a hl \<Longrightarrow> has_write_perm_only b hl \<Longrightarrow> stabilize a = stabilize b" sorry

  show "has_write_perm_only a hl \<Longrightarrow> has_value (set_value a hl v) hl v"
    sorry
qed


definition viper_prog_verifies where
  "viper_prog_verifies Pr \<Delta> F ty C \<omega> \<longleftrightarrow> ConcreteSemantics.verifies ty (compile \<Delta> F C) \<omega>"
(* ty is a type-context *)


lemma make_semantic_assertion_inh :
  "\<langle>make_semantic_assertion \<Delta> F A\<rangle> = (\<langle>\<Delta>,F\<rangle> \<Turnstile> \<langle>A\<rangle>)"
  by (simp add:ConcreteSemantics.inh_def make_semantic_assertion_def)

lemma rel_stable_assertion_make_semantic_assertionI :
 "ConcreteSemantics.rel_stable_assertion \<omega> (make_semantic_assertion \<Delta> F A) = Stable ({\<omega>} \<otimes> (\<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>A\<rangle>))"
  by (simp add:ConcreteSemantics.rel_stable_assertion_def make_semantic_assertion_inh)

section \<open>red_stmt with (overapproximating) postcondition\<close>

definition concrete_red_stmt_post :: "('a val, address \<times> field_ident) abs_type_context \<Rightarrow>
   (('a val, 'a virtual_state) abs_state, 'a val, address \<times> field_ident) abs_stmt \<Rightarrow>
   ('a val, 'a virtual_state) abs_state \<Rightarrow> ('a val, 'a virtual_state) abs_state set \<Rightarrow> bool" where
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
  assumes "ConcreteSemantics.rel_stable_assertion \<omega> A"
  assumes "(Set.filter sep_algebra_class.stable ({\<omega>} \<otimes> \<langle>A\<rangle>)) \<subseteq> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Inhale A) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def by (blast intro: ConcreteSemantics.RedInhale)

lemma concrete_post_Exhale_raw :
  assumes "a \<in> \<langle>A\<rangle>"
  assumes "Some \<omega> = \<omega>' \<oplus> a"
  assumes "sep_algebra_class.stable \<omega>'"
  assumes "\<omega>' \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Exhale A) \<omega> S"
  using assms unfolding concrete_red_stmt_post_def by (blast intro: ConcreteSemantics.RedExhale)

lemma concrete_post_Exhale :
  assumes "stable \<omega>"
  assumes "\<omega> \<in> {\<omega>'} \<otimes> \<langle>A\<rangle>"
  assumes "stabilize \<omega>' \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Exhale A) \<omega> S"
  apply (rule star_to_singleton_stabilizeE)
  using assms apply (simp)
  using assms apply (simp)
  apply (clarsimp simp add: add_set_def)
  apply (rule concrete_post_Exhale_raw; simp?)
   apply (simp add:stabilize_is_stable)
  using assms by (simp)

lemma concrete_post_Assert :
  assumes "\<omega> \<in> \<langle>A\<rangle>"
  assumes "\<omega> \<in> S"
  shows "concrete_red_stmt_post \<Delta> (abs_stmt.Assert A) \<omega> S"
  unfolding concrete_red_stmt_post_def
  using assms apply (simp add:ConcreteSemantics.inh_def)
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
  by (simp)

lemma concrete_post_FieldAssign :
  assumes "r \<omega> = Some hl"
  assumes "e \<omega> = Some v"
  assumes "ConcreteSemantics.has_write_perm (get_state \<omega>) hl"
  assumes "heap_locs \<Delta> hl = Some ty"
  assumes "v \<in> ty"
  assumes "set_state \<omega> (set_value (get_state \<omega>) hl v) \<in> S"
  shows "concrete_red_stmt_post \<Delta> (FieldAssign r e) \<omega> S"
  using assms
  apply (simp add: concrete_red_stmt_post_def)
  apply (rule exI, rule conjI)
   apply (solves \<open>rule ConcreteSemantics.RedFieldAssign; assumption\<close>)
  by (simp)

lemma concrete_post_Havoc :
  assumes "variables \<Delta> x = Some ty"
  assumes "{set_store \<omega> ((get_store \<omega>)(x \<mapsto> v)) | v. v \<in> ty } \<subseteq> S"
  shows "concrete_red_stmt_post \<Delta> (Havoc x) \<omega> S"
  using assms
  apply (simp add: concrete_red_stmt_post_def)
  apply (rule exI, rule conjI)
   apply (solves \<open>rule ConcreteSemantics.RedHavoc; assumption\<close>)
  by (simp)

lemma concrete_post_Scope :
  assumes "concrete_red_stmt_post \<Delta> s (\<omega>) S"
  shows "concrete_red_stmt_post \<Delta> (Scope ty s) \<omega> S"
  using assms
  apply (clarsimp simp add: concrete_red_stmt_post_def)
  (* TODO: add semantics for Scope *)
  oops

lemma concrete_post_Label :
  shows "set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> get_state \<omega>)) \<in> S \<Longrightarrow> concrete_red_stmt_post \<Delta> (Label l) \<omega> S"
  unfolding concrete_red_stmt_post_def
  apply (rule exI, rule conjI)
   apply (rule ConcreteSemantics.RedLabel)
  by (auto)

lemma concrete_post_Skip :
  shows "\<omega> \<in> S \<Longrightarrow> concrete_red_stmt_post \<Delta> Skip \<omega> S"
  unfolding concrete_red_stmt_post_def
  apply (rule exI, rule conjI)
   apply (rule ConcreteSemantics.RedSkip)
  by (auto)


end