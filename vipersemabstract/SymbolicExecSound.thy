theory SymbolicExecSound
  imports Instantiation EquiSemAuxLemma ViperAbstract.AbstractSemanticsProperties SymbolicExecDef ViperCommon.ViperUtil
begin

lemma greater_charact_equi:
  "\<omega>' \<succeq> \<omega> \<longleftrightarrow> get_store \<omega> = get_store \<omega>' \<and> get_trace \<omega>' = get_trace \<omega>  \<and> get_state \<omega>' \<succeq> get_state \<omega>"
  by (metis agreement.collapse get_abs_state_def get_state_def get_trace_def greater_charact greater_prod_eq greater_state_has_greater_parts(2) succ_refl)

lemma val_greater_iff [simp] :
  "(x :: 'a val) \<succeq> y \<longleftrightarrow> x = y"
  by (simp add:greater_def plus_val_def)

lemma preal_greater_iff [simp] :
  "(x :: preal) \<succeq> y \<longleftrightarrow> x \<ge> y"
  apply (simp add:greater_def plus_preal_def)
  using pos_perm_class.sum_larger preal_gte_padd by auto

lemma option_greater_SomeI :
  assumes "x \<succeq> y"
  shows "Some x \<succeq> Some y"
  by (meson assms greater_def plus_optionI)

lemma option_greater_None [simp] :
  "x \<succeq> None"
  by (simp add: greater_def)

lemma greater_option_Some_r :
  "(x :: ('a :: pcm_with_core) option) \<succeq> Some y \<longleftrightarrow> (\<exists> x'. x = Some x' \<and> x' \<succeq> y)"
  apply (cases x; simp add:greater_def)
   apply (smt (verit, ccfv_threshold) asso1 option.discI option_plus_None_r positivity)
  apply (rule; clarsimp)
  subgoal for a c
    apply (cases "c"; simp)
    subgoal apply (rule exI[of _ "|y|"]) by (simp add: core_is_smaller)
    subgoal by (metis (full_types) option.discI option.sel)
    done
  subgoal for a c
    apply (rule exI[of _ "Some c"]; simp)
    by (metis (full_types) not_None_eq)
  done

lemma option_greater_iff :
  "(x :: ('a :: pcm_with_core) option) \<succeq> y \<longleftrightarrow> (\<forall> y'. y = Some y' \<longrightarrow> (\<exists> x'. x = Some x' \<and> x' \<succeq> y'))"
  by (cases "y"; simp add:greater_option_Some_r)

lemma vstate_greater_charact1:
  assumes "get_vm x \<succeq> get_vm y"
  assumes "get_vh x \<succeq> get_vh y"
  shows "x \<succeq> y"
proof -
  obtain cm where "Some (get_vm x) = get_vm y \<oplus> cm"
    using assms unfolding greater_def by blast
  moreover have "wf_pre_virtual_state (cm, get_vh x)"
    apply (rule wf_pre_virtual_stateI)
     apply (metis EquiViper.add_masks_def add.commute calculation gr_0_is_ppos leD pos_perm_class.sum_larger pperm_pnone_pgt vstate_wf_imp)
    by (metis (no_types, lifting) EquiViper.add_masks_def calculation commutative get_vm_bound pgte_transitive pos_perm_class.sum_larger wf_mask_simple_def)
  moreover obtain c where "get_vh c = get_vh x" "get_vm c = cm"
    apply (simp add:get_vm_def get_vh_def)
    using calculation Abs_virtual_state_inverse
    by (metis fst_conv get_vh_def mem_Collect_eq snd_conv)
  ultimately show "?thesis"
    using assms(2)
    apply (simp add: greater_def)
    apply (rule exI[of _ c])
    apply (simp add: vstate_add_iff)
    by (smt (verit, ccfv_threshold) asso1 core_is_pure core_structure(2) vstate_add_iff)
qed

lemma vstate_greater_charact:
  shows "x \<succeq> y \<longleftrightarrow> get_vm x \<succeq> get_vm y \<and> get_vh x \<succeq> get_vh y"
  using vstate_greater_charact1 greater_def vstate_add_iff by metis

lemma greater_uu :
  "st \<succeq> uu"
  apply (simp add:vstate_greater_charact uu_get)
  by (meson empty_heap_identity greater_equiv zero_mask_identity)


definition s2a_heap_typed :: "(field_ident \<rightharpoonup> vtyp) \<Rightarrow> 'a partial_heap \<Rightarrow> bool" where
"s2a_heap_typed F = heap_typed_syn def_domains F"

lemma s2a_heap_typed_lookup :
  assumes "s2a_heap_typed F h"
  assumes "h hl = Some v"
  assumes "F (snd hl) = Some ty"
  shows "v \<in> sem_vtyp def_domains ty"
  using assms by (simp add:s2a_heap_typed_def heap_typed_lookup)

lemma s2a_heap_typed_insert :
  assumes "s2a_heap_typed F h"
  assumes "F (snd hl) = Some ty"
  shows "s2a_heap_typed F (h(hl \<mapsto> v)) \<longleftrightarrow> (v \<in> sem_vtyp def_domains ty)"
  using assms by (auto simp add:s2a_heap_typed_def heap_typed_insert map_comp_Some_iff)

lemma s2a_heap_typed_conc_incl :
  assumes "s2a_heap_typed F (get_vh ch)"
  assumes "ch \<succeq> ch'"
  shows "s2a_heap_typed F (get_vh ch')"
  using assms apply (simp add:s2a_heap_typed_def heap_typed_def)
  by (metis read_field.elims read_field_mono)

section \<open>basic definitions\<close>

definition def_interp :: "('a, 'b) interp" where
"def_interp = undefined\<lparr>funs := \<lambda> _ _ _. None, domains := def_domains\<rparr>"

lemma def_interp_funs [simp] :
  "funs def_interp = (\<lambda> _ _ _. None)"
  by (simp add:def_interp_def)

lemma def_interp_domains [simp] :
  "domains def_interp = def_domains"
  by (simp add:def_interp_def)

definition fields_to_prog :: "(field_ident \<rightharpoonup> vtyp) \<Rightarrow> program" where
"fields_to_prog F = undefined\<lparr>declared_fields := F \<rparr>"

lemma declared_fields_fields_to_prog [simp] :
  "declared_fields (fields_to_prog F) = F"
  by (simp add:fields_to_prog_def)

section \<open>s2a translation functions and well formedness\<close>

definition s2a_heap :: "'a valuation \<Rightarrow> 'a sym_heap \<Rightarrow> 'a virtual_state" where
"s2a_heap V h = the (concretize_heap h V)"

definition s2a_heap_wf :: "(field_name \<rightharpoonup> vtyp) \<Rightarrow> 'a valuation \<Rightarrow> 'a sym_heap \<Rightarrow> bool" where
"s2a_heap_wf F V h = (\<exists> ch. concretize_heap h V = Some ch \<and> s2a_heap_typed F (get_vh ch))"

definition s2a_store :: "'a valuation \<Rightarrow> 'a sym_store \<Rightarrow> (var \<rightharpoonup> 'a val)" where
"s2a_store V \<gamma> = (\<lambda> v. Some (the (v V))) \<circ>\<^sub>m \<gamma>"

definition s2a_store_wf :: "type_context \<Rightarrow> 'a valuation \<Rightarrow> 'a sym_store \<Rightarrow> bool" where
"s2a_store_wf \<Lambda> V \<gamma> = (\<forall> n ty. \<Lambda> n = Some ty \<longrightarrow> (\<exists> t v. \<gamma> n = Some t \<and> t V = Some v \<and> v \<in> sem_vtyp def_domains ty))"

definition s2a_state :: "'a valuation \<Rightarrow> 'a sym_store \<Rightarrow> 'a sym_heap \<Rightarrow> 'a equi_state" where
"s2a_state V \<gamma> h = make_equi_state (s2a_store V \<gamma>) Map.empty (s2a_heap V h)"

definition s2a_state_indep :: "'a sym_state \<Rightarrow> bool" where
"s2a_state_indep \<sigma> = (valu_indep (sym_used \<sigma>) (sym_cond \<sigma>) \<and>
  (\<forall> n. valu_indep (sym_used \<sigma>) (\<lambda> V. the_default SNull (sym_store \<sigma> n) V)) \<and>
  (\<forall> c. c \<in> set (sym_heap \<sigma>) \<longrightarrow> valu_indep (sym_used \<sigma>)
    (\<lambda> V. (chunk_recv c V, chunk_perm c V, chunk_val c V))))"

definition s2a_state_wf :: "type_context \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> 'a valuation \<Rightarrow> 'a sym_state \<Rightarrow> bool" where
"s2a_state_wf \<Lambda> F V \<sigma> = (s2a_store_wf \<Lambda> V (sym_store \<sigma>) \<and> s2a_heap_wf F V (sym_heap \<sigma>) \<and>
  sym_cond \<sigma> V = Some (VBool True) \<and> sym_store_type \<sigma> = \<Lambda> \<and> sym_fields \<sigma> = F \<and> s2a_state_indep \<sigma>)"


lemma s2a_state_wf_store :
  assumes "sym_store \<sigma> n = Some t"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "\<Lambda> n = Some ty"
  shows "\<exists> v. t V = Some v \<and> v \<in> sem_vtyp def_domains ty \<and> valu_indep (sym_used \<sigma>) t"
  using assms apply (clarsimp simp add:s2a_state_wf_def s2a_store_wf_def s2a_state_indep_def)
  by (metis the_default.simps(2))

(* This rule can easily lead to simp loops when unfolding s2a_state_wf_def so it is not added to the simp set. *)
lemma s2a_state_wf_store_type :
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "sym_store_type \<sigma> x = \<Lambda> x"
  using assms by (simp add:s2a_state_wf_def)

lemma s2a_state_wf_fields :
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "sym_fields \<sigma> x = F x"
  using assms by (simp add:s2a_state_wf_def)

lemma s2a_state_get_store [simp] :
  "get_store (s2a_state V \<gamma> h) = s2a_store V \<gamma>"
  by (auto simp add:s2a_state_def)

lemma s2a_store_lookup [simp] :
  "s2a_store V \<gamma> n = Some v \<longleftrightarrow> (\<exists> t. \<gamma> n = Some t \<and> v = the (t V))"
  by (auto simp add:s2a_store_def Map.map_comp_Some_iff)

lemma s2a_store_insert :
  assumes "t V = Some v"
  shows "s2a_store V (\<gamma>(x \<mapsto>t)) = (s2a_store V \<gamma>)(x\<mapsto>v)"
  using assms by (auto simp add:s2a_store_def Map.map_comp_def)

lemma s2a_state_store_shift_and_add :
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "sv V = Some v"
  shows "set_store \<omega> (shift_and_add (get_store \<omega>) v) \<succeq> s2a_state V (shift_and_add (sym_store \<sigma>) sv) (sym_heap \<sigma>)"
  using assms apply (simp add:greater_charact_equi)
  apply (simp add: s2a_state_def s2a_store_def shift_and_add_def Map.map_comp_def)
  by (rule ext; auto; metis)

lemma s2a_wf_store_insert :
  assumes "t V = Some v"
  assumes "\<Lambda> x = Some ty"
  assumes "v \<in> sem_vtyp def_domains ty"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "valu_indep (sym_used \<sigma>) t"
  assumes "\<gamma> = sym_store \<sigma>"
  shows "s2a_state_wf \<Lambda> F V (\<sigma>\<lparr>sym_store := \<gamma>(x \<mapsto> t)\<rparr>)"
  using assms unfolding s2a_state_wf_def s2a_store_wf_def s2a_state_indep_def by (auto)

lemma s2a_wf_store_shift_and_add :
  assumes "t V = Some v"
  assumes "\<Lambda> 0 = Some ty"
  assumes "v \<in> sem_vtyp def_domains ty"
  assumes "s2a_state_wf \<Lambda>0 F V \<sigma>"
  assumes "valu_indep (sym_used \<sigma>) t"
  assumes "\<gamma> = sym_store \<sigma>"
  assumes "T = sym_store_type \<sigma>"
  assumes "\<Lambda>0 = unshift_2 1 \<Lambda>"
  shows "s2a_state_wf \<Lambda> F V (\<sigma>\<lparr>sym_store := shift_and_add \<gamma> t, sym_store_type := shift_and_add T ty\<rparr>)"
  using assms unfolding s2a_state_wf_def s2a_store_wf_def s2a_state_indep_def shift_and_add_def unshift_2_def by (auto)

lemma s2a_state_get_trace [simp] :
  "get_trace (s2a_state V \<gamma> h) = Map.empty"
  by (auto simp add:s2a_state_def)

lemma s2a_state_get_state [simp] :
  "get_state (s2a_state V \<gamma> h) = s2a_heap V h"
  by (auto simp add:s2a_state_def)

lemma s2a_heap_concretize [simp] :
  assumes "concretize_heap h V = Some ch"
  shows "s2a_heap V h = ch"
  using assms by (auto simp add:s2a_heap_def)

lemma val_indep_sym_cond [simp] :
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "us = sym_used \<sigma>"
  shows "valu_indep us (sym_cond \<sigma>)"
  using assms unfolding s2a_state_wf_def s2a_state_indep_def by (auto)

lemma s2a_state_wf_sym_cond_add [simp] :
  assumes "valu_indep (sym_used \<sigma>) t"
  assumes "valu_indep (sym_used \<sigma>) (sym_cond \<sigma>)"
  shows "s2a_state_wf \<Lambda> F V (sym_cond_add \<sigma> t) \<longleftrightarrow>
         s2a_state_wf \<Lambda> F V \<sigma> \<and> t V = Some (VBool True)"
  using assms unfolding s2a_state_wf_def s2a_state_indep_def by (auto simp add: SBinop_eq_Some eval_binop_And_eq_True)

lemma valu_agree_s2a_store :
  assumes "valu_agree (sym_used \<sigma>) V V'"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "s2a_store V (sym_store \<sigma>) = s2a_store V' (sym_store \<sigma>)"
  apply (rule ext)
  using assms apply (simp add:s2a_store_def s2a_state_wf_def map_comp_def split:option.splits)
  by (metis the_default.simps(2) valu_indep_def s2a_state_indep_def)

lemma valu_agree_s2a_store_wf :
  assumes "valu_agree us V V'"
  assumes "(\<forall> n. valu_indep us (\<lambda> V. the_default SNull (\<gamma> n) V))"
  shows "s2a_store_wf \<Lambda> V \<gamma> = s2a_store_wf \<Lambda> V' \<gamma>"
  using assms apply (simp add:s2a_store_wf_def)
  using valu_indepE by (metis the_default.simps(2))

lemma valu_agree_s2a_heap_wf :
  assumes "concretize_heap h V = concretize_heap h V'"
  shows "s2a_heap_wf F V h = s2a_heap_wf F V' h"
  using assms by (simp add:s2a_heap_wf_def)

lemma valu_agree_s2a_heap :
  assumes "valu_agree (sym_used \<sigma>) V V'"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "s2a_heap V (sym_heap \<sigma>) = s2a_heap V' (sym_heap \<sigma>)"
  using assms by (simp add:s2a_heap_def s2a_state_wf_def s2a_state_indep_def valu_agree_concretize_heap)

lemma valu_agree_s2a_state :
  assumes "valu_agree (sym_used \<sigma>) V V'"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>) = s2a_state V' (sym_store \<sigma>) (sym_heap \<sigma>)"
  using assms by (simp add:abs_state_ext_iff valu_agree_s2a_heap valu_agree_s2a_store)

lemma valu_agree_sym_cond :
  assumes "valu_indep us (sym_cond \<sigma>)"
  assumes "valu_agree us V V'"
  shows "sym_cond \<sigma> V = sym_cond \<sigma> V'"
  using assms valu_indepE by auto

subsection \<open>s2a_ctxt\<close>

(* TODO: unify make_context_semantic, s2a_ctxt and t2a_ctxt? *)
definition s2a_ctxt :: "(field_name \<rightharpoonup> vtyp) \<Rightarrow> type_context \<Rightarrow> ('a val, (field_ident \<rightharpoonup> 'a val set)) abs_type_context" where
"s2a_ctxt F \<Lambda> = \<lparr>
   variables = sem_store def_domains \<Lambda>,
   custom_context = sem_fields def_domains F \<rparr>"

lemma s2a_ctxt_variables [simp] :
  assumes "\<Lambda> x = Some ty"
  shows "variables (s2a_ctxt F \<Lambda>) x = Some (sem_vtyp def_domains ty)"
  using assms
  by (simp add:s2a_ctxt_def)

lemma s2a_ctxt_custom_context [simp] :
  assumes "F x = Some ty"
  shows "custom_context (s2a_ctxt F \<Lambda>) x = Some (sem_vtyp def_domains ty)"
  using assms
  by (simp add:s2a_ctxt_def)

subsection \<open>eliminating symbolic execution helper functions\<close>

lemma sym_gen_freshE :
  fixes "f"
  assumes "sym_gen_fresh \<sigma> ty Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "v \<in> sem_vtyp def_domains ty"
  assumes "valu_indep (sym_used \<sigma>) f"
  assumes HP:"\<And> V' \<sigma>' x.
    s2a_state_wf \<Lambda> F V' \<sigma>' \<Longrightarrow>
    \<omega> \<succeq> s2a_state V' (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
    V' x = Some v \<Longrightarrow>
    valu_agree (sym_used \<sigma>) V V' \<Longrightarrow>
    x < sym_used \<sigma>' \<Longrightarrow>
    sym_used \<sigma>' = Suc (sym_used \<sigma>) \<Longrightarrow>
    f V' = f V \<Longrightarrow>
    valu_indep (sym_used \<sigma>') f \<Longrightarrow>
    Q \<sigma>' x \<Longrightarrow>
    P"
  shows "P"
proof (rule HP)
  define \<sigma>' where H\<sigma>' : "\<sigma>' = (sym_cond_add (\<sigma>\<lparr>sym_used := Suc (sym_used \<sigma>)\<rparr>) (SHasType ty (sym_fresh \<sigma>)))"
  define V' where HV' : "V' = V(sym_used \<sigma> \<mapsto> v)"
  have Hag : "valu_agree (sym_used \<sigma>) V V'" by (simp add:valu_agree_def HV')
  show "Q \<sigma>' (sym_fresh \<sigma>)"
    using assms(1) by (simp add:sym_gen_fresh_def H\<sigma>')
  show "valu_agree (sym_used \<sigma>) V V'" by (simp add:Hag)
  show "V' (sym_fresh \<sigma>) = Some v" by (simp add:HV')
  show "sym_fresh \<sigma> < sym_used \<sigma>'" by (simp add:H\<sigma>')
  show "sym_used \<sigma>' = Suc (sym_used \<sigma>)" by (simp add: H\<sigma>')
  show "f V' = f V" using assms(5) Hag by (simp add: valu_indep_def)
  show "valu_indep (sym_used \<sigma>') f" using assms(5) valu_indep_lt H\<sigma>' by auto
  show "s2a_state_wf \<Lambda> F V' \<sigma>'"
    using assms(3,4) Hag apply (simp add:HV' H\<sigma>' s2a_state_wf_def)
    apply (clarsimp simp add: valu_indep_lt SBinop_eq_Some eval_binop_And_eq_True SHasType_eq_Some s2a_state_indep_def
        valu_agree_sym_cond valu_agree_s2a_store_wf)
    apply (safe)
    subgoal by (subst valu_agree_s2a_heap_wf; simp add:valu_agree_concretize_heap)
    subgoal using valu_indep_lt by blast
    subgoal using valu_indep_lt by blast
    done
  show "\<omega> \<succeq> s2a_state V' (sym_store \<sigma>') (sym_heap \<sigma>')"
    apply (simp add:H\<sigma>' HV') apply (subst valu_agree_s2a_state[symmetric]; (rule assms)?)
    by (simp add:HV'[symmetric] Hag)
qed

lemma sym_consolidate_soundE :
  assumes "sym_consolidate \<sigma> Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes HP: "\<And> \<sigma>'.
    \<omega> \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
    s2a_state_wf \<Lambda> F V \<sigma>' \<Longrightarrow>
    sym_used \<sigma>' = sym_used \<sigma> \<Longrightarrow>
    Q \<sigma>' \<Longrightarrow>
    P"
  shows "P"
  using assms(1-3) apply (clarsimp simp add:s2a_state_wf_def s2a_heap_wf_def s2a_state_indep_def)
  apply (erule sym_consolidateE; assumption?)
  apply (rule HP; assumption?; simp?)
  subgoal
    apply (rule succ_trans) apply (assumption)
    by (simp add:greater_charact_equi)
  subgoal
    apply (simp add: s2a_state_wf_def s2a_heap_wf_def s2a_state_indep_def)
    using s2a_heap_typed_conc_incl by blast
  done

lemma s2a_conc_heap_stable :
  assumes "list_all (\<lambda>c. \<exists> p. chunk_perm c V = Some (VPerm p) \<and> 0 < p) cs"
  assumes "concretize_heap cs V = Some ch"
  shows "stable ch"
  using assms
proof (induction cs arbitrary:ch)
  case Nil
  then show ?case by (simp add:stable_virtual_state_def uu_get empty_heap_def)
next
  case (Cons a cs)
  from Cons.prems show ?case
    apply (clarsimp simp add:stable_virtual_state_def bind_eq_Some_conv concretize_chunk_eq_Some acc_virt_plus)
    apply (drule (1) Cons.IH)
    apply (clarsimp simp add:stable_virtual_state_def norm_preal preal_to_real split:if_splits)
    by (metis Rep_preal add.commute add_strict_increasing mem_Collect_eq)
qed

lemma s2a_heap_stable :
  assumes "s2a_heap_wf F V cs"
  assumes "list_all (\<lambda>c. \<exists> p. chunk_perm c V = Some (VPerm p) \<and> 0 < p) cs"
  shows "stable (s2a_heap V cs)"
  using assms by (clarsimp simp add:s2a_heap_wf_def s2a_conc_heap_stable)

lemma s2a_sym_implies_soundE :
  assumes "sym_cond \<sigma> \<turnstile>\<^sub>s t"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "t V = Some (VBool True) \<Longrightarrow> P"
  shows "P"
  using assms unfolding sym_implies_def s2a_state_wf_def by blast

lemma sym_stabilize_soundE :
  assumes "sym_stabilize \<sigma> Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes HP:"\<And> \<sigma>'.
    stabilize \<omega> \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
    s2a_state_wf \<Lambda> F V \<sigma>' \<Longrightarrow>
    sym_used \<sigma>' = sym_used \<sigma> \<Longrightarrow>
    Q \<sigma>' \<Longrightarrow>
    P"
  shows "P"
  using assms(1-3)
  apply (simp add:sym_stabilize_def)
  apply (erule (2) sym_consolidate_soundE)
  apply (clarsimp)
  apply (rule HP; simp?)
  apply (clarsimp simp add:greater_charact_equi)
  apply (subgoal_tac "stable (s2a_heap V (sym_heap \<sigma>'))")
  using max_projection_propE(3) max_projection_prop_stable_stabilize apply blast
  apply (rule s2a_heap_stable)
   apply (clarsimp simp add:s2a_state_wf_def; assumption)
  apply (rule list.pred_mono_strong, assumption)
  apply (erule (1) s2a_sym_implies_soundE)
  by (clarsimp simp add:SBinop_eq_Some SLit_def eval_binop_Lt_perm_l_eq_True)

lemma s2a_heap_consE :
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (c#cs)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "sym_heap \<sigma> = c # cs"
  assumes "F (chunk_field c) = Some ty"
  assumes HP : "\<And> a p v.
     set_state \<omega> (del_perm (get_state \<omega>) (a, chunk_field c) (Abs_preal p)) \<succeq> s2a_state V (sym_store \<sigma>) cs \<Longrightarrow>
     get_vm (get_state \<omega>) (a, chunk_field c) \<ge> Abs_preal p \<Longrightarrow>
     get_vh (get_state \<omega>) (a, chunk_field c) = Some v \<Longrightarrow>
     s2a_state_wf \<Lambda> F V (\<sigma>\<lparr>sym_heap := cs\<rparr>) \<Longrightarrow>
     chunk_recv c V = Some (VRef (Address a)) \<Longrightarrow>
     chunk_val c V = Some v \<Longrightarrow>
     chunk_perm c V = Some (VPerm p) \<Longrightarrow>
     valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V)) \<Longrightarrow>
     0 \<le> p \<Longrightarrow>
     p \<le> 1 \<Longrightarrow>
     v \<in> sem_vtyp def_domains ty \<Longrightarrow>
     P"
  shows "P"
proof -
  obtain ch chh ch0 where Hch : "concretize_heap cs V = Some chh" "concretize_chunk c V = Some ch"
    "Some ch0 = chh \<oplus> ch" "s2a_heap_typed F (get_vh ch0)"
    using assms(2,3) unfolding s2a_state_wf_def s2a_heap_wf_def by (auto simp add:bind_eq_Some_conv)

  obtain a p v where Hc : "chunk_recv c V = Some (VRef (Address a))" "chunk_val c V = Some v"
    "chunk_perm c V = Some (VPerm p)" "ch = acc_virt (a, chunk_field c) (Abs_preal p) v" "0 \<le> p" "p \<le> 1"
  using Hch by (clarsimp simp add:concretize_chunk_eq_Some)

  have Hch0 : "get_vm ch0 = (get_vm chh)((a, chunk_field c) := get_vm chh (a, chunk_field c) + Abs_preal p)"
              "get_vh ch0 = (get_vh chh)((a, chunk_field c) \<mapsto> v)"
    subgoal using Hch Hc by (clarsimp simp add:acc_virt_plus preal_to_real inf.absorb2)
    subgoal using Hch Hc by (clarsimp simp add:acc_virt_plus)
    done

  show "P"
  proof (rule HP)
    show "0 \<le> p" "p \<le> 1" "chunk_perm c V = Some (VPerm p)" "chunk_recv c V = Some (VRef (Address a))"
        "chunk_val c V = Some v" using Hc by (simp)+

    show "set_state \<omega> (del_perm (get_state \<omega>) (a, chunk_field c) (Abs_preal p)) \<succeq> s2a_state V (sym_store \<sigma>) cs"
      using assms(1) Hch apply (clarsimp simp add:greater_charact_equi vstate_greater_charact)
      apply (rule conjI)
      subgoal
        apply (clarsimp simp add:fun_greater_iff Hch0)
        by (smt (verit) less_eq_preal.rep_eq minus_preal.rep_eq plus_preal.rep_eq)
      subgoal using greater_def succ_trans vstate_greater_charact by blast
      done

    show "Abs_preal p \<le> get_vm (get_state \<omega>) (a, chunk_field c)"
      using assms(1) Hch Hch0 apply (clarsimp simp add:greater_charact_equi vstate_greater_charact fun_greater_iff)
      by (smt (verit, best) add.commute order_trans padd_pgte)

    show "get_vh (get_state \<omega>) (a, chunk_field c) = Some v"
      using assms(1) Hch Hch0 apply (clarsimp simp add:greater_charact_equi vstate_greater_charact)
      apply (drule greaterE[of "get_vh _" _ "(a, chunk_field c)"]) by (simp add:greater_option_Some_r)

    show "s2a_state_wf \<Lambda> F V (\<sigma>\<lparr>sym_heap := cs\<rparr>)"
      using assms(2, 3) Hch apply (clarsimp simp add:s2a_state_wf_def s2a_state_indep_def s2a_heap_wf_def)
      using greater_def s2a_heap_typed_conc_incl by fast

    show "valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))"
      using assms(2,3) by (simp add:s2a_state_wf_def s2a_state_indep_def)
    show "v \<in> sem_vtyp def_domains ty"
      apply (rule s2a_heap_typed_lookup[where hl="(a, chunk_field c)"]) using Hch0 Hch assms by (simp)+
  qed
qed

lemma sym_heap_extract_soundE :
  assumes "sym_heap_extract \<sigma> t f po Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "F f = Some ty"
  assumes HP:"\<And> st' \<sigma>' c a p v.
     set_state \<omega> (del_perm (get_state \<omega>) (a, f) p) \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
     s2a_state_wf \<Lambda> F V \<sigma>' \<Longrightarrow>
     get_vm (get_state \<omega>) (a, f) \<ge> p \<Longrightarrow>
     get_vh (get_state \<omega>) (a, f) = Some v \<Longrightarrow>
     t V = Some (VRef (Address a)) \<Longrightarrow>
     (case po of Some p' \<Rightarrow> \<exists> p''. p' V = Some (VPerm p'') \<and> 0 \<le> p'' \<and> p'' \<le> Rep_preal p | None \<Rightarrow> 0 < Rep_preal p) \<Longrightarrow>
     p \<le> 1 \<Longrightarrow>
     chunk_recv c V = t V \<Longrightarrow>
     chunk_field c = f \<Longrightarrow>
     chunk_perm c V = Some (VPerm (Rep_preal p)) \<Longrightarrow>
     chunk_val c V = Some v \<Longrightarrow>
     valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V)) \<Longrightarrow>
     v \<in> sem_vtyp def_domains ty \<Longrightarrow>
     sym_used \<sigma>' = sym_used \<sigma> \<Longrightarrow>
     Q \<sigma>' c \<Longrightarrow>
     P"
  shows "P"
  using assms(1-4)
  apply (clarsimp simp add:sym_heap_extract_def)
  apply (erule (2) sym_consolidate_soundE)
  apply (clarsimp)
  apply (erule (1) s2a_sym_implies_soundE)
  apply (clarsimp simp add:SBinop_eq_Some eval_binop_And_eq_True eval_binop_Eq_eq_True)
  apply (erule (2) s2a_heap_consE)
  apply (simp)
  apply (rule HP; assumption?)
            apply (simp)
           apply (simp)
          apply (simp)
         apply (simp)
  subgoal
    by (cases po; clarsimp simp add:SBinop_eq_Some Abs_preal_inverse
         eval_binop_Lt_perm_r_eq_True eval_binop_Lte_perm_r_eq_True eval_binop_And_eq_True SLit_def)
       apply (simp add:less_eq_preal.rep_eq Abs_preal_inverse one_preal.rep_eq)
      apply (simp)
     apply (simp)
    apply (simp add:Abs_preal_inverse)
   apply (simp)
  apply (simp)
  done

lemma sym_heap_add_soundE :
  assumes "Q (sym_heap_add \<sigma> c)"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "chunk_recv c V = Some (VRef (Address a))"
  assumes "chunk_perm c V = Some (VPerm p)"
  assumes "chunk_val c V = Some v"
  assumes "0 \<le> p" "get_vm (get_state \<omega>) (a, chunk_field c) + Abs_preal p \<le> 1"
  assumes "get_vh (get_state \<omega>) ## [(a, chunk_field c) \<mapsto> v]"
  assumes "valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))"
  assumes "F (chunk_field c) = Some ty" "v \<in> sem_vtyp def_domains ty"
  assumes HP: "\<And> \<sigma>'.
    set_state \<omega> (add_perm (get_state \<omega>) (a, chunk_field c) (Abs_preal p) v) \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
    s2a_state_wf \<Lambda> F V \<sigma>' \<Longrightarrow>
    sym_used \<sigma>' = sym_used \<sigma> \<Longrightarrow>
    Q \<sigma>' \<Longrightarrow>
    P"
  shows "P"
proof (rule HP)
  define hl where Hhl: "hl = (a, chunk_field c)"
  show "Q (sym_heap_add \<sigma> c)"
    using assms(1) by (simp)
  show "sym_used (sym_heap_add \<sigma> c) = sym_used \<sigma>" by (simp)
  obtain chh where Hchh : "concretize_heap (sym_heap \<sigma>) V = Some chh" "s2a_heap_typed F (get_vh chh)"
    using assms(3) apply (simp add:s2a_heap_wf_def s2a_state_wf_def) by blast
  have Hchh_bound: "get_vm chh (a, chunk_field c) + Abs_preal p \<le> 1"
    using assms(2,8) apply (clarsimp simp add:greater_charact_equi vstate_greater_charact Hchh fun_greater_iff)
    using PosReal.padd_mono dual_order.trans by blast
  obtain cch where Hc : "concretize_heap (c # sym_heap \<sigma>) V = Some cch"
             "get_vm cch = (get_vm chh)(hl := get_vm chh hl + Abs_preal p)"
             "get_vh cch = (get_vh chh)(hl \<mapsto> v)"
    subgoal premises HP apply (rule HP)
      using Hchh assms apply (simp add:acc_virt_plus bind_eq_Some_conv concretize_chunk_eq_Some; safe)
           apply (simp add:preal_to_real) apply (metis add.commute all_pos dual_order.trans le_add_same_cancel1 less_eq_preal.rep_eq zero_preal.rep_eq)
          apply (rule refl)
    subgoal
      apply (subgoal_tac "get_vh (get_state (s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>))) ## [(a, chunk_field c) \<mapsto> v]")
       prefer 2 using assms(2) assms(9) greater_charact_equi smaller_compatible vstate_greater_charact apply blast
      by (simp add: Hhl)
    subgoal using Hchh_bound by (simp add:preal_to_real)
    subgoal apply (simp add:Hhl) using Hchh_bound preal_to_real by fastforce
    subgoal by (simp add:Hhl)
    done
  done
  have "s2a_heap_wf F V (c # sym_heap \<sigma>)"
    using assms(2, 8, 11, 12) Hc Hchh by (auto simp add:greater_charact_equi vstate_greater_charact
        Hhl s2a_heap_wf_def s2a_heap_typed_insert)
  then show "s2a_state_wf \<Lambda> F V (sym_heap_add \<sigma> c)"
    using assms(3,10) by (simp add:s2a_state_wf_def s2a_state_indep_def)
  show "set_state \<omega> (add_perm (get_state \<omega>) hl (Abs_preal p) v) \<succeq> s2a_state V (sym_store (sym_heap_add \<sigma> c)) (sym_heap (sym_heap_add \<sigma> c))"
    using assms(2, 8) Hc Hchh apply (clarsimp simp add:greater_charact_equi vstate_greater_charact Hhl)
    by (rule conjI; auto simp add: fun_greater_iff preal_to_real succ_refl)
qed


lemma sym_heap_do_add_soundE :
  assumes "sym_heap_do_add \<sigma> c Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "chunk_recv c V = Some (VRef (Address a))"
  assumes "chunk_perm c V = Some (VPerm p)"
  assumes "chunk_val c V = Some v"
  assumes "0 \<le> p" "get_vm (get_state \<omega>) (a, chunk_field c) + Abs_preal p \<le> 1"
  assumes "get_vh (get_state \<omega>) ## [(a, chunk_field c) \<mapsto> v]"
  assumes "valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))"
  assumes "F (chunk_field c) = Some ty" "v \<in> sem_vtyp def_domains ty"
  assumes HP: "\<And> \<sigma>'.
    set_state \<omega> (add_perm (get_state \<omega>) (a, chunk_field c) (Abs_preal p) v) \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<Longrightarrow>
    s2a_state_wf \<Lambda> F V \<sigma>' \<Longrightarrow>
    sym_used \<sigma>' = sym_used \<sigma> \<Longrightarrow>
    Q \<sigma>' \<Longrightarrow>
    P"
  shows "P"
  using assms(1)
  apply (simp add:sym_heap_do_add_def)
  apply (erule sym_heap_add_soundE; (rule assms(1-12))?)
  apply (erule (2) sym_consolidate_soundE)
  by (rule HP; assumption?; simp)

subsection \<open>sexec_exp sound\<close>

lemma sexec_exp_sound :
  assumes "sexec_exp \<sigma> e Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "pure_exp_typing (fields_to_prog F) \<Lambda> e ty"
  shows "\<exists> t v \<sigma>'. (def_interp \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val v) \<and>
   s2a_state_wf \<Lambda> F V \<sigma>' \<and> \<omega> \<succeq> s2a_state V (sym_store \<sigma>') (sym_heap \<sigma>') \<and>
   t V = Some v \<and> v \<in> sem_vtyp def_domains ty \<and> valu_indep (sym_used \<sigma>) t \<and>
   sym_used \<sigma>' = sym_used \<sigma> \<and> Q \<sigma>' t"
  using assms
proof (induction e arbitrary:\<sigma> Q V ty)
  case (ELit x)
  then show ?case
    apply (simp add:red_pure_simps pure_exp_typing_simps)
    apply (rule conjI) subgoal by (meson prod_cases3) (* TODO: why do we get this strange subgoal?*)
    apply (safe del: exI intro!:exI; assumption?; simp?)
    by (simp add:SLit_def)
next
  case (Var x)
  then show ?case
    apply (simp add:red_pure_simps pure_exp_typing_simps greater_state_has_greater_parts(1))
    apply (clarsimp)
    apply (frule (2) s2a_state_wf_store)
    apply (safe del:exI intro!:exI; assumption?; simp)
    done
next
  case (Unop x1a e)
  from Unop.prems show ?case
    apply (clarsimp simp add:red_pure_simps pure_exp_typing_simps)
    apply (drule (3) Unop.IH)
    apply (clarsimp simp add:eval_unop_typing_agree)
    apply (safe del:exI intro!:exI; assumption?)
    by (auto simp add:SUnop_def)
next
  case (Binop e1 op e2)
  from Binop.prems show ?case
    apply (clarsimp simp add:red_pure_simps pure_exp_typing_simps)
    apply (drule (3) Binop.IH(1))
    apply (cases "binop_lazy_bool op"; clarsimp)
    subgoal (* non-lazy binop *)
      apply (drule (3) Binop.IH(2))
      apply (clarsimp)
      apply (erule (1) s2a_sym_implies_soundE)
      apply (clarsimp simp add:SBinopSafe_eq_Some eval_binop_typing_agree)
      apply (safe del:exI intro!:exI disjI2; assumption?)
      by (simp add:SBinop_eq_Some)+
    subgoal for _ _ a (* lazy binop *)
      apply (clarsimp simp add:binop_lazy_bool_binop_type)
      apply (case_tac "a = ba"; simp)
      subgoal
        apply (rule exI, rule exI, rule conjI)
         apply (rule disjI1, rule exI, rule conjI, assumption)
         apply (simp add:SLit_def SBinop_eq_Some eval_binop_lazy_binop_lazy_bool)
        by (safe del: exI intro!:exI; assumption?; simp add:SLit_def SBinop_eq_Some eval_binop_lazy_binop_lazy_bool)
      subgoal
        apply (drule Binop.IH(2))
           apply (simp)
          apply (simp add:SLit_def SBinop_eq_Some eval_binop_Eq_eq_True SUnop_def)
         apply (assumption)
        apply (clarsimp)
        apply ((rule exI conjI disjI2)+)
          apply (assumption)
         apply ((rule exI conjI disjI2)+)
          apply (assumption)
         apply (simp add:eval_bool_binop_lazy_bool)
        by auto
      done
    done
next
  case (CondExp e1 e2 e3)
  from CondExp.prems show ?case
    apply (clarsimp simp add:red_pure_simps pure_exp_typing_simps)
    apply (drule (3) CondExp.IH(1))
    apply (clarsimp)
    apply (case_tac "b"; simp)
    subgoal
      apply (drule CondExp.IH(2))
         apply (simp+)[3]
      apply (clarsimp)
      apply (safe del:exI intro!:exI disjI1; assumption?; simp)
      done
    subgoal
      apply (drule CondExp.IH(3))
         apply (simp)
        apply (solves \<open>auto simp add:SNot_eq_Some\<close>)
       apply (simp)
      apply (clarsimp)
      apply (safe del:exI intro!:exI disjI2; assumption?; simp)
      done
    done
next
  case (FieldAcc e x2a)
  from FieldAcc.prems show ?case
    apply (clarsimp simp add:red_pure_simps pure_exp_typing_simps)
    apply (drule (3) FieldAcc.IH(1))
    apply (clarsimp)
    apply (erule (3) sym_heap_extract_soundE)
    apply (clarsimp simp add:SLit_def)
    apply (erule (6) sym_heap_do_add_soundE; simp add:preal_to_real)
    subgoal using get_vm_bound preal_to_real by metis
    subgoal by (simp add:compatible_partial_functions_singleton defined_val)
    apply (safe del:exI intro!:exI; assumption?; (simp add:valu_indep_pair add_perm_del_perm preal_to_real)?)
    done
qed (simp add:sfail_def)+

subsection \<open>sproduce sound\<close>

lemma sproduce_sound :
  assumes "sproduce \<sigma> A Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "assertion_typing (fields_to_prog F) \<Lambda> A"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "stable \<omega>"
  shows "Stable ({\<omega>} \<otimes> (\<langle>def_interp, F\<rangle> \<Turnstile> \<langle>A\<rangle>)) \<and>
   (\<forall> \<omega>'. stable (\<omega>') \<longrightarrow> (\<omega>') \<in> {\<omega>} \<otimes> \<langle>def_interp, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<longrightarrow>
    (\<exists> V' \<sigma>'. \<omega>' \<succeq> s2a_state V' (sym_store \<sigma>') (sym_heap \<sigma>') \<and> s2a_state_wf \<Lambda> F V' \<sigma>' \<and> Q \<sigma>'))"
  using assms
proof (induction A arbitrary: \<sigma> \<omega> V Q)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps simp del: Product_Type.split_paired_All)
      apply (drule (3) sexec_exp_sound)
      apply (clarsimp simp del: Product_Type.split_paired_All)
      subgoal for t \<sigma>' b
      apply (simp add: red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq Stable_star del: Product_Type.split_paired_All)
        apply (rule allI) subgoal for \<omega>'
          apply (cases "b"; clarsimp)
          by (safe del:exI intro!:exI; assumption?; auto)
        done
      done
  next
    case (Acc e f ep)
    show ?thesis
    proof (cases ep)
      case (PureExp ep)
      from this Atomic Acc show ?thesis
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps simp del: Product_Type.split_paired_All)
        apply (drule (3) sexec_exp_sound)
        apply (clarsimp simp del: Product_Type.split_paired_All)
        subgoal for ty t \<sigma>' r
          apply (drule (3) sexec_exp_sound)
          apply (clarsimp simp del: Product_Type.split_paired_All)
          subgoal for tp \<sigma>'' p ty'
            apply (rule conjI)
            subgoal
              apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
              apply (rule Stable_ex)+
              apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq split:bool_to_assertion_splits)
              by (rule Stable_star; simp)
            apply (rule allI) subgoal for \<omega>'
              apply (erule (1) s2a_sym_implies_soundE)
              apply (clarsimp simp add:SBinop_eq_Some SNot_eq_Some SLit_def eval_binop_Eq_eq_True s2a_state_wf_fields)
              apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
              apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum split:bool_to_assertion_splits)
              apply (simp add:acc_def add_set_ex_comm_r split:bool_to_assertion_splits if_splits)
              apply (drule acc_heap_loc_starE)
              apply (clarsimp)
              apply (erule (3) sym_gen_freshE[where ?f="\<lambda> V. (t V, tp V)"]; (simp add:valu_indep_pair)?)
              apply (erule (2) sym_heap_do_add_soundE; simp)
                 apply (cases "r"; simp)
                apply (simp add:SVar_def)
               apply (simp add:valu_indep_pair)
              by (auto)
            done
          done
        done
    next
      case Wildcard
      from this Atomic Acc show ?thesis
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps simp del: Product_Type.split_paired_All)
        apply (drule (3) sexec_exp_sound)
        apply (clarsimp simp del: Product_Type.split_paired_All)
        subgoal for ty t \<sigma>' r
          apply (rule conjI)
          subgoal
            apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (rule Stable_ex)+
            apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq split:bool_to_assertion_splits)
            by (rule Stable_star; simp)
          apply (rule allI) subgoal for \<omega>'
            apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum split:bool_to_assertion_splits)
            apply (clarsimp simp add:acc_def add_set_ex_comm_r split:bool_to_assertion_splits if_splits)
            apply (cases "r"; simp)
            apply (drule acc_heap_loc_starE)
            apply (clarsimp) subgoal for p a v
              apply (erule (2) sym_gen_freshE[where v="VPerm p" and f=t]; simp?)
              subgoal for V' \<sigma>'' x
              apply (clarsimp simp add:s2a_state_wf_fields)
                apply (erule (3) sym_gen_freshE[where f="\<lambda> V. (t V, V x)"])
                 apply (simp add:valu_indep_pair; simp add:valu_indep_def valu_agree_def)
              apply (erule sym_heap_do_add_soundE)
                           apply (simp)
                          apply (simp; rule conjI, assumption)
                          apply (simp add:SBinop_eq_Some SLit_def SVar_def)
                         apply (simp)
                        apply (simp add:SVar_def)
                       apply (simp add:SVar_def)
                      apply (simp add:preal_to_real)
                     apply (simp add:preal_to_real)
                    apply (simp)
                   apply (simp add:valu_indep_pair)
                  apply (simp)
                 apply (simp)
                by (auto)
              done
            done
          done
        done
    qed
  next
    case (AccPredicate P es ep)
    from Atomic this show ?thesis by (simp add:sfail_def)
  qed
next
  case (Imp e A)
  from Imp.prems show ?case
    apply (clarsimp simp add:assertion_typing_simps simp del: Product_Type.split_paired_All)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp simp add:add_set_ex_comm_r simp del: Product_Type.split_paired_All)
    subgoal for t \<sigma>' b
      apply (rule conjI)
      subgoal
        apply (rule Stable_ex)
        apply (clarsimp simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq Stable_star)
        apply (cases "b"; simp)
        by (drule Imp.IH[of "(sym_cond_add \<sigma>' t)"]; assumption?; simp?)
      subgoal
        apply (rule allI) subgoal for \<omega>'
          apply (clarsimp)
          apply (clarsimp simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum)
          apply (case_tac "x = VBool b"; simp)
          apply (case_tac "b"; simp)
          subgoal
            by (drule Imp.IH[of "(sym_cond_add \<sigma>' t)"]; assumption?; (simp del: Product_Type.split_paired_All)?)
          subgoal by (safe del:exI intro!:exI; assumption?; (auto simp add:SNot_eq_Some)?)
          done
        done
      done
    done
next
  case (CondAssert e A1 A2)
  from CondAssert.prems show ?case
    apply (clarsimp simp add:assertion_typing_simps simp del: Product_Type.split_paired_All)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp simp add:add_set_ex_comm_r simp del: Product_Type.split_paired_All)
    subgoal for t \<sigma>' b
      apply (rule conjI)
      subgoal
        apply (rule Stable_ex)
        apply (clarsimp simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq Stable_star)
        apply (rule conjI; clarsimp split:bool_to_assertion_splits)
        subgoal
          by (drule CondAssert.IH(1)[of "(sym_cond_add \<sigma>' t)"]; assumption?; simp?)
        by (drule CondAssert.IH(2)[of "(sym_cond_add \<sigma>' (\<not>\<^sub>s t))"]; assumption?; auto simp add:SNot_eq_Some)
      subgoal
        apply (rule allI) subgoal for \<omega>'
          apply (clarsimp)
          apply (clarsimp simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum)
          apply (case_tac "x = VBool b"; clarsimp split:bool_to_assertion_splits)
          apply (case_tac "b"; simp)
          subgoal
            by (drule CondAssert.IH(1)[of "(sym_cond_add \<sigma>' t)"]; assumption?; (simp del: Product_Type.split_paired_All)?)
          subgoal
            by (drule CondAssert.IH(2)[of "(sym_cond_add \<sigma>' (\<not>\<^sub>s t))"]; assumption?; (simp del: Product_Type.split_paired_All)?; auto simp add:SNot_eq_Some)
          done
        done
      done
    done
next
  case (Star A1 A2)
  from Star.prems show ?case
    apply (clarsimp simp add:assertion_typing_simps)
    apply (drule (4) Star.IH(1))
    apply (clarsimp simp add:add_set_asso[symmetric])
    apply (rule conjI)
    subgoal
      apply (rule Stable_star_singleton; assumption?)
      by (metis Star.IH Star.prems(1) sproduce.simps(7))
    subgoal
      apply (clarsimp)
      apply (drule star_to_singleton_stableE; simp?)
      using Star.IH Star.prems(1) sproduce.simps(7) by blast
    done
qed (simp add:sfail_def)+

subsection \<open>sconsume sound\<close>

lemma sconsume_sound :
  assumes "sconsume \<sigma> A Q"
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "assertion_typing (fields_to_prog F) \<Lambda> A"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  shows "\<exists> \<omega>' V' \<sigma>'. \<omega> \<in> {\<omega>'} \<otimes> \<langle>def_interp, F\<rangle> \<Turnstile> \<langle>A\<rangle> \<and> \<omega>' \<succeq> s2a_state V' (sym_store \<sigma>') (sym_heap \<sigma>') \<and>
    s2a_state_wf \<Lambda> F V' \<sigma>' \<and> Q \<sigma>'"
  using assms
proof (induction A arbitrary: \<sigma> \<omega> V Q)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      apply (clarsimp simp del: Product_Type.split_paired_Ex simp add:assertion_typing_simps atomic_assertion_typing_simps)
      apply (drule (3) sexec_exp_sound)
      apply (clarsimp simp del: Product_Type.split_paired_Ex)
      apply (safe del:exI intro!:exI; assumption?)
      apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
      apply (rule red_pure_assert_intro; simp?)
      apply (erule (1) s2a_sym_implies_soundE)
      by (simp)
  next
    case (Acc e f ep)
    show ?thesis
    proof (cases ep)
      case (PureExp ep)
      from this Atomic Acc show ?thesis
        apply (clarsimp simp del: Product_Type.split_paired_Ex simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
        apply (drule (3) sexec_exp_sound)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (drule (3) sexec_exp_sound)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (erule (3) sym_heap_extract_soundE)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (erule (2) sym_heap_do_add_soundE)
                 apply (simp)
                apply (simp add:SBinop_eq_Some)
               apply (simp)
              apply (simp add:preal_to_real)
             apply (simp add:preal_to_real) using get_vm_bound preal_to_real apply (metis add_increasing2 diff_le_eq)
            apply (simp add:compatible_partial_functions_singleton defined_val)
           apply (simp add:valu_indep_pair)
          apply (simp)
         apply (simp)
        apply (simp del: Product_Type.split_paired_Ex)
        apply (subst (asm) add_perm_del_perm_le) apply (simp) apply (simp) apply (simp add:preal_to_real)
        apply (subgoal_tac "(p - Abs_preal (Rep_preal p - ra)) = Abs_preal ra") prefer 2 apply (simp add:preal_to_real)
        apply (safe del:exI intro!:exI; assumption?)
        apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
        apply (rule exI)+
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
        apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
        apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
        apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
        apply (rule bool_to_assertion_intro) apply (simp)
        apply (rule bool_to_assertion_intro) apply (simp)
        apply (simp add:acc_def)
        apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
        apply (rule exI)
        apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
        apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
        apply (rule bool_to_assertion_intro) apply (simp)
        by (rule acc_heap_loc_starI; (simp add:preal_to_real)?)
    next
      case Wildcard
      from this Atomic Acc show ?thesis
        apply (clarsimp simp del: Product_Type.split_paired_Ex simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
        subgoal for ty
          apply (drule (3) sexec_exp_sound)
          apply (clarsimp simp del: Product_Type.split_paired_Ex)
          subgoal for t \<sigma>' r
            apply (erule (3) sym_heap_extract_soundE)
            apply (clarsimp simp del: Product_Type.split_paired_Ex)
            subgoal for \<sigma>'' c a p v
              apply (erule (2) sym_heap_do_add_soundE[where ?p="Rep_preal p / 2"])
                       apply (simp)
                      apply (simp add:SBinop_eq_Some SLit_def)
                     apply (simp)
                    apply (simp add:preal_to_real)
                   apply (simp add:preal_to_real) using get_vm_bound preal_to_real apply (smt (verit, del_insts) divide_pos_pos)
                  apply (simp add:compatible_partial_functions_singleton defined_val)
                 apply (simp add:valu_indep_pair)
                apply (simp)
               apply (simp)
              apply (simp del: Product_Type.split_paired_Ex)
              apply (subst (asm) add_perm_del_perm_le) apply (simp) apply (simp) apply (simp add:preal_to_real)
              apply (subgoal_tac "(p - Abs_preal (Rep_preal p / 2)) = Abs_preal (Rep_preal p / 2)") prefer 2 apply (simp add:preal_to_real)
              apply (safe del:exI intro!:exI; assumption?)
              apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
              apply (rule exI)+
              apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
              apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
              apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (simp add:acc_def)
              apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
              apply (rule exI)
              by (rule acc_heap_loc_starI; (rule refl)?; simp add:preal_to_real)
            done
          done
        done
    qed
  next
    case (AccPredicate P es ep)
    from Atomic this show ?thesis by (simp add:sfail_def)
  qed
next
  case (Imp e A)
  from Imp.prems show ?case
    apply (clarsimp simp del: Product_Type.split_paired_Ex simp add:assertion_typing_simps)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp simp del: Product_Type.split_paired_Ex)
    subgoal for t \<sigma>' b
      apply (cases "b"; simp del: Product_Type.split_paired_Ex)
      subgoal
        apply (drule Imp.IH; (simp del: Product_Type.split_paired_Ex)?)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (simp add:add_set_ex_comm_r add_set_asso[symmetric] del: Product_Type.split_paired_Ex)
        apply (rule exI)+
        apply (rule conjI)
         apply (rule exI[of _ "VBool True"]; simp)
         defer 1 apply fastforce
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (assumption)
        done
      subgoal
        apply (simp add:add_set_ex_comm_r add_set_asso[symmetric] del: Product_Type.split_paired_Ex)
        apply (rule exI)+
        apply (rule conjI)
         apply (rule exI[of _ "VBool False"]; simp del: Product_Type.split_paired_Ex)
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
         apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (simp)
        apply (safe del:exI intro!:exI; assumption?)
        by (auto simp add:SNot_eq_Some)
      done
    done
next
  case (CondAssert e A1 A2)
  from CondAssert.prems show ?case
    apply (clarsimp simp del: Product_Type.split_paired_Ex simp add:assertion_typing_simps)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp simp del: Product_Type.split_paired_Ex)
    subgoal for t \<sigma>' b
      apply (cases "b"; simp del: Product_Type.split_paired_Ex)
      subgoal
        apply (drule CondAssert.IH(1); (simp del: Product_Type.split_paired_Ex)?)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (simp add:add_set_ex_comm_r add_set_asso[symmetric] del: Product_Type.split_paired_Ex)
        apply (rule exI)+
        apply (rule conjI)
         apply (rule exI[of _ "VBool True"]; simp)
         defer 1 apply fastforce
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (assumption)
        done
      subgoal
        apply (drule CondAssert.IH(2); (simp del: Product_Type.split_paired_Ex)?) apply (solves \<open>auto simp add:SNot_eq_Some\<close>)
        apply (clarsimp simp del: Product_Type.split_paired_Ex)
        apply (simp add:add_set_ex_comm_r add_set_asso[symmetric] del: Product_Type.split_paired_Ex)
        apply (rule exI)+
        apply (rule conjI)
         apply (rule exI[of _ "VBool False"]; simp)
         defer 1 apply fastforce
        apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
        apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
        apply (assumption)
        done
      done
    done
next
  case (Star A1 A2)
  from Star.prems show ?case
    apply (clarsimp simp add:assertion_typing_simps)
    apply (drule (3) Star.IH(1))
    apply (clarsimp)
    apply (drule (3) Star.IH(2))
    apply (clarsimp)
    apply (safe del:exI intro!:exI; assumption?)
    apply (simp add:add_set_commm[of "\<langle>def_interp, F\<rangle> \<Turnstile> \<langle>A1\<rangle>"] add_set_asso[symmetric])
    by (rule star_to_singletonI; assumption)
qed (simp add:sfail_def)+

subsection \<open>sexec sound\<close>

lemma add_perm_stabilize_del_perm_set_value :
  assumes "1 \<le> get_vm st hl"
  assumes "p1 = 1" "p2 = 1"
  assumes "stable st"
  shows "add_perm (stabilize (del_perm st hl p1)) hl p2 v = set_value st hl v"
  apply (rule virtual_state_ext; rule ext; simp add:assms vstate_stabilize_structure restrict_map_def)
  subgoal
  using assms apply (simp add:preal_to_real)
  using get_vm_bound preal_to_real by (metis nle_le)
  subgoal  by (metis assms(4) stable_virtual_state_def)
  done

theorem sexec_sound :
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "stable \<omega>"
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "sexec \<sigma> C Q"
  shows "concrete_red_stmt_post (s2a_ctxt F \<Lambda>) (compile False def_interp (\<Lambda>, F) C) \<omega> {\<omega>'.
    \<exists> V' \<sigma>'. \<omega>' \<succeq> s2a_state V' (sym_store \<sigma>') (sym_heap \<sigma>') \<and> s2a_state_wf \<Lambda> F V' \<sigma>' \<and> Q \<sigma>'}"
  using assms
proof (induction C arbitrary: \<sigma> \<omega> V Q)
  case (Inhale A)
  then show ?case
    apply (clarsimp simp add:stmt_typing_simps make_semantic_assertion_gen_def)
    apply (drule (3) sproduce_sound)
    apply (clarsimp)
    apply (rule concrete_post_Inhale)
    subgoal by (simp add: rel_stable_assertion_def)
    by fastforce
next
  case (Exhale A)
  then show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (drule (3) sconsume_sound)
    apply (safe_step) subgoal for \<omega>'
      apply (clarsimp)
      apply (rule concrete_post_Exhale[where \<omega>'=\<omega>'])
        apply (solves \<open>simp\<close>)
      subgoal  by (clarsimp simp add:make_semantic_assertion_gen_def)
      apply (erule (2) sym_stabilize_soundE)
      by blast
    done
next
  case (If e C1 C2)
  from If.prems show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp)
    subgoal for t \<sigma>' b
      apply (rule concrete_post_If[where b=b]; simp)
      apply (cases b; simp)
      by (rule If.IH; assumption?; auto simp add:SNot_eq_Some)+
    done
next
  case (Seq C1 C2)
  from Seq.prems show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (rule concrete_post_Seq)
    apply (rule concrete_red_stmt_post_stable_wf; assumption?)
    apply (rule concrete_red_stmt_post_impl)
     apply (rule Seq.IH(1); assumption)
    apply (clarsimp)
    by (rule Seq.IH(2); assumption?)
next
  case (LocalAssign x e)
  then show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp)
    apply (rule concrete_post_LocalAssign; simp?)
    apply (clarsimp simp add:greater_charact_equi)
    apply (safe del:exI intro!:exI; assumption?; (simp add:s2a_store_insert)?)
    by (rule s2a_wf_store_insert; simp?)
next
  case (FieldAssign e1 f e2)
  then show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp)
    apply (drule (3) sexec_exp_sound)
    apply (clarsimp)
    apply (erule (3) sym_heap_extract_soundE)
    apply (clarsimp simp add:SLit_def)
    apply (subgoal_tac "p = 1") defer 1 apply (metis less_eq_preal.rep_eq one_preal.rep_eq verit_la_disequality)
    apply (rule concrete_post_FieldAssign; simp?)
    subgoal
      apply (simp add:has_write_perm_only_def)
      using get_vm_bound nle_le by blast
    apply (erule (2) sym_stabilize_soundE)
    apply (erule (2) sym_heap_do_add_soundE; (simp add:preal_to_real valu_indep_pair)?; (simp add:preal_to_real vstate_stabilize_structure)?)
    subgoal using get_vm_bound preal_to_real by (metis nle_le)
    subgoal apply (simp add:compatible_partial_functions_singleton defined_val restrict_map_eq_Some norm_preal preal_to_real)
      using get_vm_bound preal_to_real by (metis less_le_not_le)
    apply (safe del:exI intro!:exI; assumption?; simp?)
    by (simp add: add_perm_stabilize_del_perm_set_value preal_to_real stable_get_state)
next
  case (Havoc x)
  then show ?case
    apply (clarsimp simp add:stmt_typing_simps)
    apply (rule concrete_post_Havoc; simp?)
    subgoal
      apply (rule subsetI)
      subgoal for \<omega>'
        apply (clarsimp)
        apply (erule (2) sym_gen_freshE[where ?f="\<lambda> _. ()"])
          apply (solves \<open>simp add:s2a_state_wf_store_type\<close>)
         apply (simp add:valu_indep_def)
        subgoal for _ V' \<sigma>'' xa
          apply (clarsimp simp add:greater_charact_equi)
          apply (rule exI[of _ V'])
          apply (safe del:exI intro!:exI; assumption?; simp?)
           apply (solves \<open>simp add:valu_agree_s2a_store SVar_def s2a_store_insert\<close>)
          by (rule s2a_wf_store_insert; (simp add:SVar_def)?)
        done
      done
    done
next
  case Skip
  then show ?case
    apply (simp)
    apply (rule concrete_post_Skip)
    by (blast)
qed (simp add:sfail_def)+

theorem sexec_verifies :
  assumes "\<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>)"
  assumes "stable \<omega>"
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  assumes "s2a_state_wf \<Lambda> F V \<sigma>"
  assumes "sexec \<sigma> C Q"
  shows "ConcreteSemantics.verifies (s2a_ctxt F \<Lambda>) (compile False def_interp (\<Lambda>, F) C) \<omega>"
  using assms
  apply (simp add: ConcreteSemantics.verifies_def)
  using sexec_sound concrete_red_stmt_post_def by blast

theorem sexec_verifies_set :
  assumes "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> stable \<omega> \<Longrightarrow> typed (s2a_ctxt F \<Lambda>) \<omega> \<Longrightarrow>
    \<exists> \<sigma> V. \<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>) \<and>
      s2a_state_wf \<Lambda> F V \<sigma> \<and> sexec \<sigma> C Q"
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  shows "ConcreteSemantics.verifies_set (s2a_ctxt F \<Lambda>) A (compile False def_interp (\<Lambda>, F) C)"
  using assms
  apply (simp add: ConcreteSemantics.verifies_set_def)
  using sexec_verifies by blast

lemma s2a_state_empty :
  assumes "get_trace \<omega> = Map.empty"
  assumes "get_store \<omega> = Map.empty"
  shows "\<omega> \<succeq> s2a_state Map.empty Map.empty []"
  using assms by (simp add:greater_charact_equi s2a_store_def greater_uu)

lemma s2a_state_wf_empty :
  shows "s2a_state_wf Map.empty F Map.empty
     \<lparr>sym_store = Map.empty, sym_cond = SBool True, sym_heap = [], sym_used = 0, sym_store_type = Map.empty, sym_fields = F\<rparr>"
  apply (simp add:s2a_state_wf_def s2a_store_wf_def s2a_heap_wf_def s2a_heap_typed_def uu_get empty_heap_def s2a_state_indep_def)
  by (simp add:SLit_def)

lemma sinit_sound :
  assumes "sinit tys F Q"
  assumes "\<Lambda> = (\<lambda> v. if v < length tys then Some (tys ! v) else None)"
  assumes "get_trace \<omega> = Map.empty"
  assumes "store_typed (sem_store def_domains \<Lambda>) (get_store \<omega>)"
  assumes "\<And> \<sigma> V.
   \<omega> \<succeq> s2a_state V (sym_store \<sigma>) (sym_heap \<sigma>) \<Longrightarrow>
   s2a_state_wf \<Lambda> F V \<sigma> \<Longrightarrow>
   Q \<sigma> \<Longrightarrow>
   P"
  shows "P"
  using assms
proof (induction tys arbitrary:Q \<Lambda> \<omega> P)
  case Nil
  from Nil.prems(1-4) show ?case
    apply (simp)
    apply (rule Nil.prems(5); assumption?; simp?; (rule s2a_state_empty s2a_state_wf_empty)?; simp?)
    subgoal
      apply (simp add:store_typed_def s2a_ctxt_def)
      by (metis dom_eq_empty_conv)
    done
next
  case (Cons ty tys)
  from Cons.prems(1-4) show ?case
    apply (simp)
    apply (erule Cons.IH[where \<omega>="set_store \<omega> (unshift_2 1 (get_store \<omega>))"]) apply (solves \<open>simp\<close>) apply (solves \<open>simp\<close>)
    subgoal
      apply (simp del:Fun.fun_upd_apply)
      apply (rule store_typed_unshift; assumption?)
      apply (simp add: sem_store_def map_comp_def)
      by (rule ext; simp add:List.nth_append unshift_2_def)
    apply (frule store_typed_lookup[where n="0"]) apply (solves \<open>simp\<close>) apply (clarsimp simp add:List.nth_append)
    apply (erule sym_gen_freshE[where f="SNull"]; assumption?; simp?)
    subgoal for V \<sigma> v V' \<sigma>' x
      apply (rule Cons.prems(5); assumption?; simp del:Fun.fun_upd_apply)
       apply (rule succ_trans) prefer 2
        apply (rule s2a_state_store_shift_and_add; assumption?; simp add:SVar_def)
       apply (simp add: shift_and_add_unshift_id succ_refl)
      apply (rule s2a_wf_store_shift_and_add; assumption?; (simp add:SVar_def)?)
      by (rule ext; simp add:List.nth_append unshift_2_def)
    done
qed

theorem sinit_sexec_verifies_set :
  assumes "stmt_typing (fields_to_prog F) \<Lambda> C"
  assumes "sinit tys F (\<lambda> \<sigma> :: 'a sym_state. sexec \<sigma> C Q)"
  (* TODO: replace with nth_option from TotalUtil? *)
  assumes "\<Lambda> = (\<lambda> v. if v < length tys then Some (tys ! v) else None)"
  assumes "\<And> \<omega>. \<omega> \<in> A \<Longrightarrow> get_trace \<omega> = Map.empty"
  shows "ConcreteSemantics.verifies_set (s2a_ctxt F \<Lambda>) (A :: 'a equi_state set) (compile False def_interp (\<Lambda>, F) C)"
  apply (rule sexec_verifies_set[where Q=Q]; (rule assms)?)
  using assms apply -
  subgoal for \<omega>
    apply (erule (1) sinit_sound[where \<omega>=\<omega>])
    by (auto simp add:TypedEqui.typed_def TypedEqui.typed_store_def s2a_ctxt_def)
  done

end