theory AbstractRefinesTotal
  imports ViperAbstract.Instantiation TotalViper.TotalSemantics ViperAbstract.EquiSemAuxLemma ViperAbstract.AbstractSemanticsProperties
begin

section \<open>general lemmas and definitions\<close>

lemma exh_if_total_unfold :
  "exh_if_total b \<omega> = (if b then RNormal \<omega> else RFailure)"
  by (auto)

lemma RFailure_eq_ex_if_total[simp] :
  "RFailure = exh_if_total b \<omega> \<longleftrightarrow> \<not> b"
  by (cases "b"; simp)

lemma RNormal_eq_ex_if_total[simp] :
  "RNormal \<omega> = exh_if_total b \<omega>' \<longleftrightarrow> b \<and> \<omega> = \<omega>'"
  by (cases "b"; simp)

(* TODO: Better name? *)
definition total_state_mask :: "heap_loc set \<Rightarrow> 'a full_total_state" where
"total_state_mask hls = undefined\<lparr>get_total_full := undefined\<lparr>get_mh_total := (\<lambda> hl. if hl \<in> hls then 1 else 0) \<rparr> \<rparr>"

subsection \<open>abs_state properties\<close>

(* TODO: Make both simp lemmas? *)
declare vstate_stabilize_structure(1)[simp]

lemma stable_dom_get_vh_eq_get_vm :
  assumes "stable st"
  shows "dom (get_vh st) = {hl. ppos (get_vm st hl)}"
  using assms
  by (metis (mono_tags, lifting) Collect_cong dom_def stable_virtual_state_def vstate_wf_ppos)

lemma get_trace_in_star :
  assumes "\<omega>' \<in> {\<omega>} \<otimes> A"
  shows "get_trace \<omega>' = get_trace \<omega>"
  using assms abs_state_star_singletonE by blast

(* TODO: remove? *)
lemma abs_state_defined:
  "a ## b \<longleftrightarrow> get_store a = get_store b \<and> get_trace a = get_trace b \<and> get_state a ## get_state b"
  by (simp add: ag_comp ag_the_ag_same comp_prod get_store_def get_trace_def get_state_def)

(* TODO: remove? *)
lemma get_vh_Some_defined_eq :
  assumes "\<phi>1 ## \<phi>2"
  assumes "get_vh \<phi>1 hl = Some v1"
  assumes "get_vh \<phi>2 hl = Some v2"
  shows "v1 = v2"
  using assms
  apply (clarsimp simp add:defined_def)
  by (smt (verit, best) option.discI plus_funE plus_option.simps(3) plus_val_def vstate_add_iff)

section \<open>Separation logic basics\<close>

subsection \<open>partial_heap_typing\<close>

abbreviation "partial_heap_typing ctxt h \<equiv> ValueAndBasicState.well_typed_heap (program_total ctxt) (absval_interp_total ctxt) h"

lemma partial_heap_typing_stabilize :
  assumes "partial_heap_typing ctxt (get_vh st)"
  shows "partial_heap_typing ctxt (get_vh (stabilize st))"
  using assms by (simp add:ValueAndBasicState.well_typed_heap_def vstate_stabilize_structure(2) restrict_map_eq_Some)

lemma partial_heap_typing_elim :
  assumes "partial_heap_typing ctxt h"
  assumes "h a = Some v"
  assumes "declared_fields (program_total ctxt) (snd a) = Some ty"
  shows "has_type (absval_interp_total ctxt) ty v"
  using assms apply (simp add: ValueAndBasicState.well_typed_heap_def) by (metis option.sel prod.collapse)

lemma partial_heap_typing_insert :
  assumes "declared_fields (program_total ctxt) (snd a) = Some ty"
  assumes "partial_heap_typing ctxt h"
  assumes "has_type (absval_interp_total ctxt) ty v"
  shows "partial_heap_typing ctxt (h (a\<mapsto>v))"
  using assms unfolding ValueAndBasicState.well_typed_heap_def by (auto)

subsection \<open>PosReal\<close>

lemma ppos_pwrite [simp] :
  "PosReal.ppos PosReal.pwrite"
  by (simp add:norm_preal preal_to_real)

lemma get_valid_locs_def_ppos :
  "get_valid_locs \<omega> = {hl. ppos (get_mh_total_full \<omega> hl)}"
  by (simp add:get_valid_locs_def norm_preal)

lemma eq_pnone_not_ppos :
  "p = pnone \<longleftrightarrow> \<not>ppos p"
  apply (simp add: norm_preal preal_to_real)
  apply (transfer)
  by (simp)

lemma pmin_1_id [simp] :
  assumes "wf_mask_simple m"
  shows "pmin 1 \<circ> m = m"
  using assms apply (simp add:wf_mask_simple_def) apply (rule ext; simp)
  using inf.absorb_iff2 by auto

definition epsilon_preal :: "preal \<Rightarrow> preal" where
"epsilon_preal p = (SOME q. 0 < q \<and> q < p)"

lemma epsilon_preal_bounds :
  assumes "p \<noteq> pnone"
  shows "0 < epsilon_preal p \<and> epsilon_preal p < p"
  unfolding epsilon_preal_def
  apply (rule someI_ex)  apply (rule exI[of _ "p / Abs_preal 2"])
  using assms apply (simp add:norm_preal preal_to_real)
  by (transfer; simp)

subsection \<open>red_pure_exps_total\<close>

inductive_simps red_pure_exps_total_simps :
  "red_pure_exps_total ctxt R \<omega>_def (Cons e es) \<omega> r"
  "red_pure_exps_total ctxt R \<omega>_def Nil \<omega> r"

lemma red_pure_exps_total_singleton_None [simp]:
  "red_pure_exps_total ctxt R \<omega>_def [e] \<omega> None \<longleftrightarrow> ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  by (auto simp add:red_pure_exps_total_simps)

lemma red_pure_exps_total_two_None [simp]:
  "red_pure_exps_total ctxt R \<omega>_def [e1, e2] \<omega> None \<longleftrightarrow>
    ctxt, R, \<omega>_def \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<or>
  ((\<exists>v. ctxt, R, \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) \<and>  ctxt, R, \<omega>_def \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure)"
  by (auto simp add:red_pure_exps_total_simps)

subsection \<open>simp and elim rules for inductives\<close>

inductive_cases red_pure_exp_elim:
  "ctxt, R, \<omega>_def \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"

inductive_simps red_pure_exp_simps:
  "ctxt, R, \<omega>_def \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"
  "ctxt, R, \<omega>_def \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>]\<^sub>t v"

inductive_simps red_stmt_total_simps :
  "red_stmt_total ctxt R \<Lambda> (stmt.Inhale e) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Exhale e) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Assert e) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Assume e) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.If e C1 C2) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Seq C1 C2) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.LocalAssign v e) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.FieldAssign e1 f e2) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Havoc v) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.MethodCall ys f es) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.While e I C) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Unfold P es p) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Fold P es p) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Package A1 A2) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Apply A1 A2) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Label l) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Scope v C) \<omega> r"
  "red_stmt_total ctxt R \<Lambda> (stmt.Skip) \<omega> r"

inductive_simps red_inhale_simps :
  "red_inhale ctxt R (Atomic a) \<omega> r"
  "red_inhale ctxt R (Imp p A) \<omega> r"
  "red_inhale ctxt R (CondAssert p A1 A2) \<omega> r"
  "red_inhale ctxt R (ImpureAnd A1 A2) \<omega> r"
  "red_inhale ctxt R (ImpureOr A1 A2) \<omega> r"
  "red_inhale ctxt R (Star A1 A2) \<omega> r"
  "red_inhale ctxt R (Wand A1 A2) \<omega> r"
  "red_inhale ctxt R (ForAll ty A) \<omega> r"
  "red_inhale ctxt R (Exists ty A) \<omega> r"

inductive_simps red_exhale_simps :
  "red_exhale ctxt R \<omega>1 (Atomic a) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (Imp p A) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (CondAssert p A1 A2) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (ImpureAnd A1 A2) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (ImpureOr A1 A2) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (Star A1 A2) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (Wand A1 A2) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (ForAll ty A) \<omega>2 r"
  "red_exhale ctxt R \<omega>1 (Exists ty A) \<omega>2 r"

(* TODO: remove ? *)
inductive_simps red_atomic_assert_simps :
  "red_atomic_assert \<Delta> (Pure e) \<omega> b"
  "red_atomic_assert \<Delta> (Acc e f ep) \<omega> b"
  "red_atomic_assert \<Delta> (AccPredicate P es ep) \<omega> b"

inductive_simps th_result_rel_RFailure [simp] :
  "th_result_rel b1 b2 W RFailure"

section \<open>Fragment of the refinement proof\<close>

fun valid_a2t_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where
    "valid_a2t_exp_no_rec (Perm e f) = False"
  | "valid_a2t_exp_no_rec (PermPred e f) = False"
  | "valid_a2t_exp_no_rec (PExists ty e) = False"
  | "valid_a2t_exp_no_rec (PForall ty e) = False"
  | "valid_a2t_exp_no_rec (FunApp f es) = False"
  | "valid_a2t_exp_no_rec (Let f es) = False"
  | "valid_a2t_exp_no_rec (Unfolding p es e) = False"
  | "valid_a2t_exp_no_rec _ = True"

abbreviation valid_a2t_exp
  where "valid_a2t_exp \<equiv> pure_exp_pred valid_a2t_exp_no_rec"

fun valid_a2t_atomic_assert_no_rec :: "pure_exp atomic_assert \<Rightarrow> bool"
  where
    "valid_a2t_atomic_assert_no_rec (AccPredicate _ _ _) = False"
  | "valid_a2t_atomic_assert_no_rec _ = True"

abbreviation valid_a2t_atomic_assert
  where "valid_a2t_atomic_assert \<equiv> atomic_assert_pred valid_a2t_atomic_assert_no_rec valid_a2t_exp_no_rec"

fun valid_a2t_assert_no_rec :: "ViperLang.assertion \<Rightarrow> bool"
  where
    "valid_a2t_assert_no_rec (ImpureAnd _ _) = False"
  | "valid_a2t_assert_no_rec (ImpureOr _ _) = False"
  | "valid_a2t_assert_no_rec (Wand _ _) = False"
  | "valid_a2t_assert_no_rec (ForAll _ _) = False"
  | "valid_a2t_assert_no_rec (Exists _ _) = False"
  | "valid_a2t_assert_no_rec _ = True"

abbreviation valid_a2t_assert
  where "valid_a2t_assert \<equiv> assert_pred valid_a2t_assert_no_rec valid_a2t_atomic_assert_no_rec valid_a2t_exp_no_rec"

fun valid_a2t_stmt_no_rec :: "stmt \<Rightarrow> bool"
  where
(* Assert currently only works for up-closed propositions, but our propositions are not up-closed. *)
    "valid_a2t_stmt_no_rec (stmt.Assert _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Assume _) = False"
  | "valid_a2t_stmt_no_rec (stmt.MethodCall _ _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.While _ _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Unfold _ _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Fold _ _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Package _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Apply _ _) = False"
  | "valid_a2t_stmt_no_rec (stmt.Scope _ _) = False"
  | "valid_a2t_stmt_no_rec _ = True"

abbreviation valid_a2t_stmt
  where "valid_a2t_stmt \<equiv> stmt_pred valid_a2t_stmt_no_rec valid_a2t_assert valid_a2t_exp"


section \<open>THSem expressions are deterministic\<close>

abbreviation red_pure_exp_det_exp
  where "red_pure_exp_det_exp \<equiv> pure_exp_pred (\<lambda> e. case e of Unfolding _ _ _ \<Rightarrow> False | _ \<Rightarrow> True)"

lemma valid_a2t_exp_implies_red_pure_exp_det_exp [simp]:
  assumes "valid_a2t_exp e"
  shows "red_pure_exp_det_exp e"
  using assms by (induction e; simp)

lemma red_pure_exp_det :
  assumes "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t v1"
  assumes "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t v2"
  assumes "red_pure_exp_det_exp e"
  shows "v1 = v2"
  using assms
proof (induction e arbitrary:v1 v2 \<omega> \<omega>_def)
  case (ELit x) then show ?case by (safe elim!:red_pure_exp_elim; simp)
next
  case (Var x) then show ?case by (safe elim!:red_pure_exp_elim; simp)
next
  case (Unop x1a e) then show ?case by (safe elim!:red_pure_exp_elim; simp; fastforce)
next
  case (Binop e1 x2a e2) then show ?case by (safe elim!:red_pure_exp_elim; simp; fastforce)
next
  case (CondExp e1 e2 e3) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (FieldAcc e x2a) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (Old x1a e) then show ?case by (safe elim!:red_pure_exp_elim; simp)
next
  case (Perm e x2a) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (PermPred x1a x2a) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (FunApp x1a x2a) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case Result then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (Unfolding p es e) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (Let e1 e2) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (PExists x1a e) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
next
  case (PForall x1a e) then show ?case by (safe elim!:red_pure_exp_elim; simp; auto)
qed

section \<open>Abstract sem expressions are deterministic\<close>

section \<open>typing soundness for THSem\<close>

subsection \<open>store typing for THSem\<close>

definition store_typing :: "'a total_context \<Rightarrow> type_env \<Rightarrow> 'a store \<Rightarrow> bool" where
"store_typing ctxt \<Lambda> st \<longleftrightarrow> (\<forall> n ty. \<Lambda> n = Some ty \<longrightarrow>
    (\<exists> v. st n = Some v \<and> has_type (absval_interp_total ctxt) ty v))"

lemma store_typing_elim :
  assumes "store_typing ctxt \<Lambda> st"
  assumes "\<Lambda> n = Some ty"
  shows "(\<exists> v. st n = Some v \<and> has_type (absval_interp_total ctxt) ty v)"
  using assms by (simp add: store_typing_def)

lemma store_typing_insert :
  assumes "\<Lambda> x = Some ty"
  assumes "store_typing ctxt \<Lambda> st"
  assumes "has_type (absval_interp_total ctxt) ty v"
  shows "store_typing ctxt \<Lambda> (st (x\<mapsto>v))"
  using assms unfolding store_typing_def by (auto)

subsection \<open>heap typing for THSem\<close>

(* TODO: combine with total_heap_well_typed or ValueAndBasicState.well_typed_heap? *)
definition heap_typing :: "'a total_context \<Rightarrow> 'a total_heap \<Rightarrow> bool" where
"heap_typing ctxt hh \<longleftrightarrow> (\<forall> a ty. declared_fields (program_total ctxt) (snd a) = Some ty \<longrightarrow>
   has_type (absval_interp_total ctxt) ty (hh a))"

lemma heap_typing_total_heap_well_typed :
  "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh \<longleftrightarrow> heap_typing ctxt hh"
  by (simp add:total_heap_well_typed_def heap_typing_def)

lemma heap_typing_elim :
  assumes "heap_typing ctxt hh"
  assumes "declared_fields (program_total ctxt) (snd a) = Some ty"
  shows "has_type (absval_interp_total ctxt) ty (hh a)"
  using assms by (simp add: heap_typing_def; cases a; simp)


lemma heap_typing_insert :
  assumes "declared_fields (program_total ctxt) (snd a) = Some ty"
  assumes "heap_typing ctxt hh"
  assumes "has_type (absval_interp_total ctxt) ty v"
  shows "heap_typing ctxt (hh (a:=v))"
  using assms unfolding heap_typing_def by (auto)

subsection \<open>state typing\<close>

definition partial_trace_typing :: "'a total_context \<Rightarrow> (string \<rightharpoonup> 'a virtual_state) \<Rightarrow> bool" where
"partial_trace_typing ctxt t = (\<forall> l st. t l = Some st \<longrightarrow> partial_heap_typing ctxt (get_vh st))"

definition trace_typing :: "'a total_context \<Rightarrow> (string \<rightharpoonup> 'a total_state) \<Rightarrow> bool" where
"trace_typing ctxt t = (\<forall> l st. t l = Some st \<longrightarrow> heap_typing ctxt (get_hh_total st))"

definition abs_state_typing :: "'a total_context \<Rightarrow> type_env \<Rightarrow> 'a equi_state \<Rightarrow> bool" where
"abs_state_typing ctxt \<Lambda> \<omega> \<longleftrightarrow> (store_typing ctxt \<Lambda> (get_store \<omega>) \<and>
   partial_heap_typing ctxt (get_vh (get_state \<omega>)) \<and>
   partial_trace_typing ctxt (get_trace \<omega>))"

definition total_state_typing :: "'a total_context \<Rightarrow> type_env \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
"total_state_typing ctxt \<Lambda> \<omega> \<longleftrightarrow> (store_typing ctxt \<Lambda> (get_store_total \<omega>) \<and>
  heap_typing ctxt (get_hh_total (get_total_full \<omega>)) \<and>
  trace_typing ctxt (get_trace_total \<omega>))"

subsection \<open>soundness of expression typing for THSem\<close>

lemma red_pure_exp_typed :
  assumes "pure_exp_typing (program_total ctxt) \<Lambda> e ty"
  \<comment>\<open>assumes "program_total ctxt = Pr"\<close>
  (* TODO: Why can the following not be in an assumes? *)
  shows "total_state_typing ctxt \<Lambda> \<omega> \<Longrightarrow> valid_a2t_exp e \<Longrightarrow>
     \<exists> r. ctxt, R, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r \<and> (\<forall> v. r = Val v \<longrightarrow> has_type (absval_interp_total ctxt) ty v)"
  unfolding total_state_typing_def using assms
proof (induction arbitrary:\<omega>_def \<omega> rule: pure_exp_typing.induct )
  case (TypVar \<Lambda> x ty)
  obtain v where "(get_store_total \<omega>) x = Some v \<and> has_type  (absval_interp_total ctxt) ty v"
    by (insert TypVar store_typing_elim; blast)
  then show ?case by (simp add: red_pure_exp_simps)
next
  case (TypLit lit ty \<Lambda>)
  then show ?case by (simp add: red_pure_exp_simps)
next
  case (TypUnop uop \<tau>1 \<tau> \<Lambda> e)
  obtain r where Hr : "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<and>
        (\<forall>v. r = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau>1 v)" using TypUnop.prems TypUnop.IH by fastforce
  from this TypUnop.hyps show ?case
    apply (simp add: red_pure_exp_simps)
    apply (cases r; clarsimp simp add:eval_unop_typing_agree; rule exI; rule conjI)
       apply (rule disjI1; rule exI; rule exI; safe)
        (* Why does auto solve everything here, but not before? *)
         apply (auto)
    done
next
  case (TypBinop bop \<tau>1 \<tau>2 \<tau> \<Lambda> e1 e2)
  obtain r1 where Hr1 : "ctxt, R, \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t r1 \<and>
        (\<forall>v. r1 = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau>1 v)" using TypBinop by fastforce
  obtain r2 where Hr2 : "ctxt, R, \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t r2 \<and>
        (\<forall>v. r2 = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau>2 v)" using TypBinop by fastforce
  then show ?case
  proof (cases r1)
    case (Val v1)
    show ?thesis
    proof (cases "eval_binop_lazy v1 bop")
      case (Some v)
      from this TypBinop.hyps \<open>r1 = Val v1\<close> Hr1 Hr2 show ?thesis
        apply (simp)
        apply (rule exI)
        apply (safe)
         apply (rule RedBinopLazy; auto; fail)
        apply (auto elim:eval_binop_lazy_type_res)
        done
    next
      case None
      show ?thesis
      proof (cases r2)
        case (Val v2)
        show ?thesis
        proof (cases "eval_binop v1 bop v2 = BinopOpFailure")
          case True
          from this TypBinop.hyps \<open>r1 = Val v1\<close> \<open>r2 = Val v2\<close> \<open>eval_binop_lazy v1 bop = None\<close> Hr1 Hr2 show ?thesis
            apply (simp)
            apply (rule exI)
            apply (safe)
             apply (rule RedBinopOpFailure; auto)
            apply (auto)
            done
        next
          case False
          from this TypBinop.hyps \<open>r1 = Val v1\<close> \<open>r2 = Val v2\<close> \<open>eval_binop_lazy v1 bop = None\<close> Hr1 Hr2 show ?thesis
            apply (simp)
            apply (subst (asm) eval_binop_typing_agree)
               apply (auto)[3]
            apply (safe)
            apply (rule exI)
            apply (safe)
             apply (rule RedBinop)
                apply (auto)
            done
        qed
      next
        case VFailure
        from this TypBinop.hyps \<open>r1 = Val v1\<close> \<open>eval_binop_lazy v1 bop = None\<close> Hr1 Hr2 show ?thesis
          apply (simp)
          apply (safe)
          apply (rule exI)
          apply (safe)
          apply (rule RedBinopRightFailure)
              apply (auto)
          apply (frule binop_type_non_fail_exists; auto)
          done
      qed
    qed
  next
    case VFailure
    from this TypBinop.hyps Hr1 Hr2 show ?thesis
      apply (safe)
      apply (rule exI)
      apply (safe)
       apply (rule RedSubFailure; auto)
      apply (auto)
      done
  qed
next
  case (TypCondExp \<Lambda> b e1 \<tau> e2)
  obtain rb where Hb : "ctxt, R, \<omega>_def \<turnstile> \<langle>b;\<omega>\<rangle> [\<Down>]\<^sub>t rb \<and>
        (\<forall>v. rb = Val v \<longrightarrow> has_type (absval_interp_total ctxt) TBool v)" using TypCondExp by fastforce
  obtain r1 where Hr1 : "ctxt, R, \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t r1 \<and>
        (\<forall>v. r1 = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau> v)" using TypCondExp by fastforce
  obtain r2 where Hr2 : "ctxt, R, \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t r2 \<and>
        (\<forall>v. r2 = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau> v)" using TypCondExp by fastforce
  show ?case
  proof (cases rb)
    case (Val vb)
    obtain bb where "vb = VBool bb" using Hb Val by (auto)
    with Val Hb Hr1 Hr2 show ?thesis
      apply (clarsimp simp add: red_pure_exp_simps)
      apply (cases bb; auto)
      done
  next
    case VFailure
    with Hb show ?thesis
      apply (clarsimp simp add: red_pure_exp_simps; auto)
      done
  qed
next
  case (TypFieldAcc \<Lambda> e f \<tau>)
  obtain r where Hr : "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<and>
        (\<forall>v. r = Val v \<longrightarrow> has_type (absval_interp_total ctxt) TRef v)" using TypFieldAcc by fastforce
  show ?case
  proof (cases r)
    case (Val v)
    show ?thesis
    proof (cases "(THE n. v = VRef n)")
      case (Address a)
      from this Val TypFieldAcc.hyps TypFieldAcc.prems Hr show ?thesis
        apply (clarsimp simp add: red_pure_exp_simps)
        (* TODO: Why does auto fail here with ENTER MATCH? *)
        apply (cases "if_Some (\<lambda>res. (a, f) \<in> get_valid_locs res) \<omega>_def")
         apply (rule exI; rule conjI)
          apply (rule disjI1)
          apply (auto intro:heap_typing_elim)
        done
    next
      case Null
      from this Val TypFieldAcc.hyps Hr show ?thesis
        by (auto simp add: red_pure_exp_simps)
    qed
  next
    case VFailure
    from this TypFieldAcc.hyps Hr show ?thesis
        by (auto simp add: red_pure_exp_simps)
    qed
next
  case (TypOld \<Lambda> e \<tau> lbl)
  show ?case
  proof (cases "get_trace_total \<omega> lbl")
    case (Some \<phi>)
    then obtain r where Hr : "ctxt, R, map_option (get_total_full_update (\<lambda>_. \<phi>)) \<omega>_def \<turnstile> \<langle>e;\<omega>\<lparr>get_total_full := \<phi>\<rparr>\<rangle> [\<Down>]\<^sub>t r \<and>
        (\<forall>v. r = Val v \<longrightarrow> has_type (absval_interp_total ctxt) \<tau> v)"
      using TypOld.prems TypOld.IH[of "\<omega>\<lparr>get_total_full := \<phi>\<rparr>" "map_option (get_total_full_update (\<lambda>_. \<phi>)) \<omega>_def"]
      apply (simp add:trace_typing_def)
      by fastforce
    show ?thesis
    proof (cases r)
      case (Val v)
      from Val Some TypOld.prems Hr show ?thesis by (auto simp add: red_pure_exp_simps)
    next
      case VFailure
      from VFailure Some TypOld.prems Hr show ?thesis by (auto simp add: red_pure_exp_simps)
    qed
  next case None then show ?thesis by (simp add: red_pure_exp_simps)
  qed
next
  case (TypPerm \<Lambda> e f \<tau>)
  obtain r where Hr : "ctxt, R, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<and>
        (\<forall>v. r = Val v \<longrightarrow> has_type (absval_interp_total ctxt) TRef v)" using TypPerm by fastforce
  show ?case
  proof (cases r)
    case (Val v)
    show ?thesis
    proof (cases "(THE n. v = VRef n)")
      case (Address a)
      from this Val TypPerm.hyps TypPerm.prems Hr show ?thesis
        by (clarsimp simp add: red_pure_exp_simps)
    next
      case Null
      from this Val TypPerm.hyps Hr show ?thesis
        by (auto simp add: red_pure_exp_simps)
    qed
  next
    case VFailure
    from this TypPerm.hyps Hr show ?thesis
        by (auto simp add: red_pure_exp_simps)
    qed
next
qed (simp)+

subsection \<open>preservation of store typing by red_stmt_total\<close>


lemma red_inhale_preserves_heap_and_store :
  assumes "red_inhale ctxt R A \<omega> r"
  assumes "RNormal \<omega>' = r"
  shows "get_store_total \<omega>' = get_store_total \<omega> \<and> get_trace_total \<omega>' = get_trace_total \<omega> \<and> get_hh_total (get_total_full \<omega>') = get_hh_total (get_total_full \<omega>)"
  using assms
proof (induction A arbitrary:\<omega> \<omega>' r)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      by (clarsimp simp add:red_inhale_simps split:if_splits)
  next
    case (Acc e f ep)
    from this Atomic show ?thesis
      apply (clarsimp simp add:red_inhale_simps th_result_rel.simps inhale_perm_single_def split:if_splits)
      (* TODO: Why does simp become slow here? *)
      by (safe; simp)
  next
    case (AccPredicate x31 x32 x33)
    from this Atomic show ?thesis
      by (auto simp add:red_inhale_simps th_result_rel.simps inhale_perm_single_pred_def split:if_splits)
  qed
next
  case (Star A1 A2)
  then show ?case
    apply (simp add:red_inhale_simps) by metis
qed (clarsimp simp add:red_inhale_simps; blast)+

lemma red_inhale_preserves_typing :
  assumes "red_inhale ctxt R A \<omega> r"
  assumes "RNormal \<omega>' = r"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>'"
  using assms unfolding total_state_typing_def
  using red_inhale_preserves_heap_and_store by metis


lemma red_exhale_preserves_heap_and_store :
  assumes "red_exhale ctxt R \<omega>0 A \<omega> r"
  assumes "RNormal \<omega>' = r"
  shows "get_store_total \<omega>' = get_store_total \<omega> \<and> get_trace_total \<omega>' = get_trace_total \<omega> \<and> get_hh_total (get_total_full \<omega>') = get_hh_total (get_total_full \<omega>)"
  using assms
proof (induction A arbitrary:\<omega> \<omega>' \<omega>0 r)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      by (clarsimp simp add:red_exhale_simps split:if_splits)
  next
    case (Acc e f ep)
    from this Atomic show ?thesis
      by (clarsimp simp add:red_exhale_simps inhale_perm_single_def split:if_splits)
  next
    case (AccPredicate x31 x32 x33)
    from this Atomic show ?thesis
      by (auto simp add:red_exhale_simps inhale_perm_single_pred_def split:if_splits)
  qed
next
  case (Star A1 A2)
  then show ?case
    apply (simp add:red_exhale_simps) by metis
qed (clarsimp simp add:red_exhale_simps; blast)+

lemma red_exhale_preserves_typing :
  assumes "red_exhale ctxt R \<omega>0 A \<omega> r"
  assumes "RNormal \<omega>' = r"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>'"
  using assms unfolding total_state_typing_def
  using red_exhale_preserves_heap_and_store by metis

lemma havoc_locs_state_preserves_typing :
  assumes "total_state_typing ctxt \<Lambda> \<omega>_exh"
  assumes "\<omega>' \<in> havoc_locs_state ctxt \<omega>_exh P"
  shows "total_state_typing ctxt \<Lambda> \<omega>'"
  using assms
  by (clarsimp simp add:havoc_locs_state_def total_state_typing_def heap_typing_total_heap_well_typed)

lemma red_stmt_total_preserves_typing :
  assumes "red_stmt_total ctxt R \<Lambda> C \<omega> r"
  assumes "RNormal \<omega>' = r"
  assumes "valid_a2t_stmt C"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>'"
  using assms
proof (induction  arbitrary:\<omega>' rule:red_stmt_total.induct)
  case (RedInhale A \<omega> res \<Lambda>)
  then show ?case using red_inhale_preserves_typing by blast
next
  case (RedExhale \<omega> A \<omega>_exh \<omega>' \<Lambda>)
  then show ?case using red_exhale_preserves_typing havoc_locs_state_preserves_typing by fast
next
  case (RedHavoc \<Lambda> x ty v \<omega>)
  then show ?case
    (* TODO: Why is this del: necessary? Where does the beta-expansion that makes the rule apply come from? *)
    apply (simp del: fun_upd_apply add:total_state_typing_def)
    apply (rule store_typing_insert; auto iff:has_type_get_type)
    done
next
  case (RedLocalAssign \<omega> e v \<Lambda> x ty)
  then show ?case
    apply (simp del: fun_upd_apply add:total_state_typing_def)
    apply (rule store_typing_insert; auto iff:has_type_get_type)
    done
next
  case (RedFieldAssign \<omega> e_r addr f e v ty \<Lambda>)
  then show ?case
    apply (simp del: fun_upd_apply add:total_state_typing_def)
    apply (rule heap_typing_insert; auto iff:has_type_get_type)
    done
next
  case (RedLabel \<omega>' \<omega> lbl \<Lambda>)
  then show ?case by (clarsimp split:if_splits simp add:total_state_typing_def trace_typing_def)
qed (simp; blast)+


section \<open>not RFailure iff lemmas\<close>

lemma not_fail_Inhale :
  "\<not> red_stmt_total ctxt R \<Lambda> (stmt.Inhale A) \<omega> RFailure \<longleftrightarrow>
    \<not> red_inhale ctxt R A \<omega> RFailure"
  by (simp add: red_stmt_total_simps)

lemma not_fail_Exhale :
  "\<not> red_stmt_total ctxt R \<Lambda> (stmt.Exhale A) \<omega> RFailure \<longleftrightarrow>
    \<not> red_exhale ctxt R \<omega> A \<omega> RFailure"
  by (metis RedExhaleFailure red_stmt_total_inversion_thms(9) sub_expressions.simps(8))

lemma not_fail_Assert :
  "\<not> red_stmt_total ctxt R \<Lambda> (stmt.Assert A) \<omega> RFailure \<longleftrightarrow>
    \<not> red_exhale ctxt R \<omega> A \<omega> RFailure"
  by (metis RedAssertFailure red_stmt_total_inversion_thms(11) sub_expressions.simps(9))

lemma not_fail_If :
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.If e C1 C2)"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  assumes "valid_a2t_stmt (stmt.If e C1 C2)"
  shows "\<not> red_stmt_total ctxt R \<Lambda> (stmt.If e C1 C2) \<omega> RFailure \<longleftrightarrow>
    (\<exists> b. ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<and>
      \<not> red_stmt_total ctxt R \<Lambda> (if b then C1 else C2) \<omega> RFailure)"
  using assms
  (* TODO: Why is the if in the goal rewritten? *)
  apply (clarsimp simp add:red_stmt_total_simps)
  apply (erule stmt_typing_elim)
  apply (frule red_pure_exp_typed[where ?ctxt="ctxt", where ?R="R", where ?\<omega>_def="Some \<omega>"]; assumption?)
  apply (erule exE)
  apply (case_tac r; clarsimp)
  apply (case_tac n; clarsimp; safe; auto?; drule red_pure_exp_det; assumption?; auto)
  subgoal
    apply (safe; auto?; drule red_pure_exp_det; assumption?; auto)
    done
  done

lemma not_fail_Seq :
  shows "\<not> red_stmt_total ctxt R \<Lambda> (stmt.Seq C1 C2) \<omega> RFailure \<longleftrightarrow>
    \<not> red_stmt_total ctxt R \<Lambda> C1 \<omega> RFailure \<and>
     (\<forall>\<omega>'. red_stmt_total ctxt R \<Lambda> C1 \<omega> (RNormal \<omega>') \<longrightarrow> \<not> red_stmt_total ctxt R \<Lambda> C2 \<omega>' RFailure)"
  by (auto simp add:red_stmt_total_simps)

lemma not_fail_LocalAssign:
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.LocalAssign x e)"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  assumes "valid_a2t_stmt (stmt.LocalAssign x e)"
  shows "\<not> red_stmt_total ctxt R \<Lambda> (stmt.LocalAssign x e) \<omega> RFailure \<longleftrightarrow>
    (\<exists> v ty. \<Lambda> x = Some ty \<and> ctxt, R, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<and> has_type (absval_interp_total ctxt) ty v)"
  using assms
  apply (clarsimp simp add:red_stmt_total_simps)
  apply (erule stmt_typing_elim)
  apply (frule red_pure_exp_typed[where ?ctxt="ctxt", where ?R="R", where ?\<omega>_def="Some \<omega>"]; assumption?)
  apply (safe)
   apply (case_tac r; auto; fail)
  apply (auto dest:red_pure_exp_det)
  done

lemma not_fail_FieldAssign :
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.FieldAssign e1 f e2)"
  assumes "total_state_typing ctxt \<Lambda> \<omega>"
  assumes "valid_a2t_stmt (stmt.FieldAssign e1 f e2)"
  shows "\<not> red_stmt_total ctxt R \<Lambda> (stmt.FieldAssign e1 f e2) \<omega> RFailure \<longleftrightarrow>
    (\<exists> a v ty. declared_fields (program_total ctxt) f = Some ty \<and>
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<and>
     ctxt, R, (Some \<omega>) \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<and>
     (a,f) \<in> get_writeable_locs \<omega> \<and>
     has_type (absval_interp_total ctxt) ty v)"
  using assms
  apply (clarsimp simp add:red_stmt_total_simps)
  apply (erule stmt_typing_elim)
  apply (drule red_pure_exp_typed[where ?e="e1", where ?ctxt="ctxt", where ?R="R", where ?\<omega>_def="Some \<omega>"]; assumption?)
  apply (drule red_pure_exp_typed[where ?e="e2", where ?ctxt="ctxt", where ?R="R", where ?\<omega>_def="Some \<omega>"]; assumption?)
  apply (clarsimp)
  apply (case_tac r; clarsimp; (solves \<open>auto dest:red_pure_exp_det\<close>)?)
  apply (case_tac ra; clarsimp; (solves \<open>auto dest:red_pure_exp_det\<close>)?)
  apply (case_tac n; clarsimp; (solves \<open>auto dest:red_pure_exp_det\<close>)?)
  apply (safe; (solves \<open>auto dest:red_pure_exp_det\<close>)?)
  apply (rule exI, safe) apply (assumption)
  apply (rule exI, safe) apply (assumption)
  apply (auto)
  done

lemma not_fail_Label :
  shows "\<not> red_stmt_total ctxt R \<Lambda> (stmt.Label l) \<omega> RFailure \<longleftrightarrow> True"
  by (auto simp add:red_stmt_total_simps)

lemma not_fail_Skip :
  shows "\<not> red_stmt_total ctxt R \<Lambda> stmt.Skip \<omega> RFailure \<longleftrightarrow> True"
  by (auto simp add:red_stmt_total_simps)

section \<open>total to abstract state\<close>

subsection \<open>restricting abs state \<close>

definition restrict_virtual_state :: "'a virtual_state \<Rightarrow> heap_loc set \<Rightarrow> 'a virtual_state"  (infixl "|`\<^sub>v"  110) where
  "st |`\<^sub>v A = Abs_virtual_state (get_vm st, get_vh st |` (A \<union> {hl. ppos (get_vm st hl)}))"

definition restrict_abs_state :: "'a equi_state \<Rightarrow> heap_loc set \<Rightarrow> 'a equi_state"  (infixl "|`\<^sub>a"  110) where
  "\<omega> |`\<^sub>a A = set_state \<omega> (get_state \<omega> |`\<^sub>v A)"

lemma stabilize_vstate_restrict :
  "stabilize st = st |`\<^sub>v {hl. ppos (get_vm st hl)}"
  by (simp add:stabilize_virtual_state_def restrict_virtual_state_def stabilize2pre_def restrict_map_def)

lemma stabilize_abs_state_restrict :
  "stabilize \<omega> = \<omega> |`\<^sub>a {hl. ppos (get_vm (get_state \<omega>) hl)}"
  by (simp add:stabilize_prod_def stabilize_agreement_def restrict_abs_state_def stabilize_vstate_restrict set_state_def get_state_def get_store_def get_trace_def)

lemma restrict_virtual_state_struct [simp] :
  "get_vh (st |`\<^sub>v A) = get_vh st |` (A \<union> {hl. ppos (get_vm st hl)})"
  "get_vm (st |`\<^sub>v A) = get_vm st"
  apply (insert Rep_virtual_state[of st])
  by (simp_all add:restrict_virtual_state_def get_vh_def get_vm_def wf_pre_virtual_state_def Abs_virtual_state_inverse)

lemma restrict_abs_state_struct [simp] :
  "get_store (\<omega> |`\<^sub>a A) = get_store \<omega>"
  "get_trace (\<omega> |`\<^sub>a A) = get_trace \<omega>"
  "get_state (\<omega> |`\<^sub>a A) = get_state \<omega> |`\<^sub>v A"
  by (simp_all add:restrict_abs_state_def)


subsection \<open>translation of ctxt and state\<close>

definition t2a_ctxt :: "'a total_context \<Rightarrow> type_context \<Rightarrow> ('a val, (field_ident \<rightharpoonup> 'a val set)) abs_type_context" where
"t2a_ctxt ctxt \<Lambda> = \<lparr>
   variables = \<lambda> v. map_option (\<lambda> ty. {v. has_type (absval_interp_total ctxt) ty v}) (\<Lambda> v),
   custom_context = \<lambda> f. map_option (\<lambda> ty. {v. has_type (absval_interp_total ctxt) ty v})
     (declared_fields (program_total ctxt) f) \<rparr>"

lemma t2a_ctxt_variables [simp] :
  assumes "\<Lambda> x = Some ty"
  shows "variables (t2a_ctxt ctxt \<Lambda>) x = Some {v. has_type (absval_interp_total ctxt) ty v}"
  using assms
  by (simp add:t2a_ctxt_def)

lemma t2a_ctxt_custom_context [simp] :
  assumes "declared_fields (program_total ctxt) x = Some ty"
  shows "custom_context (t2a_ctxt ctxt \<Lambda>) x = Some {v. has_type (absval_interp_total ctxt) ty v}"
  using assms
  by (simp add:t2a_ctxt_def)

lift_definition t2a_virtual_state :: "'a total_state \<Rightarrow> 'a virtual_state" is
"\<lambda> st. (pmin 1 \<circ> get_mh_total st, (Some \<circ> get_hh_total st))"
  by (simp add:wf_pre_virtual_state_def wf_mask_simple_def)

definition t2a_state :: "'a full_total_state \<Rightarrow> 'a equi_state" where
"t2a_state \<omega> = make_equi_state
   (get_store_total \<omega>)
   ((\<lambda> x. Some (stabilize (t2a_virtual_state x))) \<circ>\<^sub>m (get_trace_total \<omega>))
   (t2a_virtual_state (get_total_full \<omega>))"

lemma t2a_state_get_store [simp] :
  "get_store (t2a_state \<omega>) = get_store_total \<omega>"
  by (simp add:t2a_state_def)

lemma t2a_state_get_trace [simp] :
  "get_trace (t2a_state \<omega>) =
   ((\<lambda> x. Some (stabilize (t2a_virtual_state x))) \<circ>\<^sub>m (get_trace_total \<omega>))"
  by (simp add:t2a_state_def)

(* Not a simp lemma to not accidentally break the t2a_state abstraction *)
lemma t2a_state_get_state :
  "get_state (t2a_state \<omega>) =
   t2a_virtual_state (get_total_full \<omega>)"
  by (simp add:t2a_state_def)

lemma t2a_state_set_store [simp] :
  "set_store (t2a_state \<omega>) st =
   t2a_state (\<omega>\<lparr>get_store_total := st \<rparr>)"
  by (simp add:t2a_state_def)

lemma t2a_state_set_state [simp] :
  "set_state (t2a_state \<omega>) (t2a_virtual_state \<phi>) =
   t2a_state (\<omega>\<lparr>get_total_full := \<phi>\<rparr>)"
  by (rule full_state_ext; simp add:t2a_state_get_state)

lemma t2a_virtual_state_get_vh[simp] :
  shows "get_vh (t2a_virtual_state \<phi>) hl = Some (get_hh_total \<phi> hl)"
  by (simp add:t2a_virtual_state.rep_eq get_vh_def)

lemma t2a_virtual_state_get_vm[simp] :
  "get_vm (t2a_virtual_state \<phi>) = pmin 1 \<circ> get_mh_total \<phi>"
  by (simp add:t2a_virtual_state.rep_eq get_vm_def)

section \<open>abstract state to total state\<close>

definition ctxt_to_interp :: "'a total_context \<Rightarrow> ('a, 'a virtual_state) ValueAndBasicState.interp" where
"ctxt_to_interp ctxt = undefined\<lparr>domains := absval_interp_total ctxt, funs := (\<lambda> _ _ _. None) \<rparr>"

lemma ctxt_to_interp_domains [simp] :
  "domains (ctxt_to_interp ctxt) = absval_interp_total ctxt"
  by (simp add:ctxt_to_interp_def)

lemma ctxt_to_interp_funs [simp] :
  "funs (ctxt_to_interp ctxt) = (\<lambda> _ _ _. None)"
  by (simp add:ctxt_to_interp_def)

subsection \<open>translation of states\<close>

(* TODO: Weaken this such that one only needs this for abs types that appear in the program? *)
definition abs_type_wf :: "('a \<Rightarrow> abs_type) \<Rightarrow> bool" where
"abs_type_wf \<Delta> = (\<forall> a. \<exists> x. \<Delta> x = a)"

fun well_typed_val :: "('a \<Rightarrow> abs_type) \<Rightarrow> vtyp \<Rightarrow> 'a val" where
  "well_typed_val \<Delta> TInt = VInt undefined"
| "well_typed_val \<Delta> TBool = VBool undefined"
| "well_typed_val \<Delta> TPerm = VPerm undefined"
| "well_typed_val \<Delta> TRef = VRef undefined"
| "well_typed_val \<Delta> (TAbs a) = VAbs (SOME x. \<Delta> x = a)"

lemma well_typed_val_typed :
  assumes "abs_type_wf \<Delta>"
  shows "has_type \<Delta> ty (well_typed_val \<Delta> ty)"
  apply (cases ty; simp)
  apply (rule someI_ex)
  using assms by (simp add:abs_type_wf_def)

definition a2t_state_wf :: "'a total_context \<Rightarrow> (label \<rightharpoonup> 'c :: sep_algebra) \<Rightarrow> bool" where
"a2t_state_wf ctxt t \<longleftrightarrow> abs_type_wf (absval_interp_total ctxt) \<and> (\<forall> l st. t l = Some st \<longrightarrow> stable st)"

definition a2t_extend_heap :: "'a total_context \<Rightarrow> 'a partial_heap \<Rightarrow> 'a total_heap" where
"a2t_extend_heap ctxt h hl = case_option (well_typed_val (absval_interp_total ctxt) (the (declared_fields (program_total ctxt) (snd hl)))) id (h hl)"

definition a2t_extend_state :: "'a total_context \<Rightarrow> 'a virtual_state \<Rightarrow> 'a total_state" where
"a2t_extend_state ctxt st = total_state.make (a2t_extend_heap ctxt (get_vh st)) undefined (get_vm st) undefined"

definition a2t_extend :: "'a total_context \<Rightarrow> 'a equi_state \<Rightarrow> 'a full_total_state" where
"a2t_extend ctxt \<omega> = full_total_state.make (get_store \<omega>) ((\<lambda> x. Some (a2t_extend_state ctxt x)) \<circ>\<^sub>m get_trace \<omega>) (a2t_extend_state ctxt (get_state \<omega>))"

definition a2t_extend_ok :: "'a total_context \<Rightarrow> 'a equi_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
"a2t_extend_ok ctxt \<omega> \<omega>\<^sub>t =
  ((partial_heap_typing ctxt (get_vh (get_state \<omega>)) \<longleftrightarrow> heap_typing ctxt (get_hh_total (get_total_full \<omega>\<^sub>t))) \<and>
  (partial_trace_typing ctxt (get_trace \<omega>) \<longleftrightarrow> trace_typing ctxt (get_trace_total \<omega>\<^sub>t)))"


lemma a2t_extend_heap_typed :
  assumes "abs_type_wf (absval_interp_total ctxt)"
  shows "heap_typing ctxt (a2t_extend_heap ctxt h) = partial_heap_typing ctxt h"
  apply (simp add:a2t_extend_heap_def heap_typing_def ValueAndBasicState.well_typed_heap_def split:option.splits)
  using well_typed_val_typed assms by fastforce

lemma a2t_extend_typed :
  assumes "abs_type_wf (absval_interp_total ctxt)"
  shows "a2t_extend_ok ctxt \<omega> (a2t_extend ctxt \<omega>)"
  using assms apply (simp add:a2t_extend_ok_def a2t_extend_def a2t_extend_state_def a2t_extend_heap_typed
      full_total_state.defs total_state.defs partial_trace_typing_def trace_typing_def map_comp_Some_iff)
  using a2t_extend_heap_typed by fastforce



definition a2t_states :: "'a total_context \<Rightarrow> 'a equi_state \<Rightarrow> 'a full_total_state set" where
"a2t_states ctxt \<omega> = {\<omega>\<^sub>t. \<omega> = t2a_state \<omega>\<^sub>t |`\<^sub>a dom (get_vh (get_state \<omega>)) \<and>
  a2t_extend_ok ctxt \<omega> \<omega>\<^sub>t \<and>
  wf_mask_simple (get_mh_total (get_total_full \<omega>\<^sub>t))}"

definition a2t_state :: "'a total_context \<Rightarrow> 'a equi_state \<Rightarrow> 'a full_total_state" where
"a2t_state ctxt \<omega> = (SOME \<omega>\<^sub>t. \<omega>\<^sub>t \<in> a2t_states ctxt \<omega>)"

lemma a2t_states_in_stable :
  assumes "stable \<omega>"
  shows "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega> \<longleftrightarrow> \<omega> = stabilize (t2a_state \<omega>\<^sub>t) \<and> a2t_extend_ok ctxt \<omega> \<omega>\<^sub>t \<and>
    wf_mask_simple (get_mh_total (get_total_full \<omega>\<^sub>t))"
proof -
  from assms have Hvh: "dom (get_vh (get_state \<omega>)) = {hl. ppos (get_vm (get_state \<omega>) hl)}"
    by (simp add:stable_dom_get_vh_eq_get_vm stable_get_state)
  show "?thesis"
    apply (auto simp add:a2t_states_def Hvh stabilize_abs_state_restrict)
    by (metis restrict_abs_state_struct(3) restrict_virtual_state_struct(2))
qed

lemma a2t_statesI_direct :
  assumes "\<omega> = t2a_state \<omega>\<^sub>t |`\<^sub>a dom (get_vh (get_state \<omega>))"
  assumes "a2t_extend_ok ctxt \<omega> \<omega>\<^sub>t"
  assumes "wf_mask_simple (get_mh_total (get_total_full \<omega>\<^sub>t))"
  shows "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  using assms by (simp add:a2t_states_def)

lemma a2t_statesI_direct_stable :
  assumes "stable \<omega>"
  assumes "\<omega> = stabilize (t2a_state \<omega>\<^sub>t)"
  assumes "a2t_extend_ok ctxt \<omega> \<omega>\<^sub>t"
  assumes "wf_mask_simple (get_mh_total (get_total_full \<omega>\<^sub>t))"
  shows "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  using assms by (simp add:a2t_states_in_stable)

lemma a2t_statesI :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "heap_typing ctxt (get_hh_total (get_total_full \<omega>\<^sub>t))"
  assumes "trace_typing ctxt (get_trace_total \<omega>\<^sub>t)"
  assumes "get_store_total \<omega>\<^sub>t = get_store \<omega>"
  assumes "(\<lambda> x. Some (stabilize (t2a_virtual_state x))) \<circ>\<^sub>m get_trace_total \<omega>\<^sub>t = get_trace \<omega>"
  assumes "get_mh_total (get_total_full \<omega>\<^sub>t) = get_vm (get_state \<omega>)"
  assumes "\<And> hl v. get_vh (get_state \<omega>) hl = Some v \<Longrightarrow> get_hh_total (get_total_full \<omega>\<^sub>t) hl = v"
  shows "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  using assms
  apply (simp add:a2t_states_def)
  apply (simp add:a2t_extend_ok_def abs_state_typing_def)
  apply (rule full_state_ext; simp add:t2a_state_get_state)
  apply (rule virtual_state_ext; simp add:restrict_map_def)
  using vstate_wf_ppos by fastforce

lemma get_store_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "get_store_total \<omega>\<^sub>t = get_store \<omega>"
  using assms apply (simp add:a2t_states_def)
  by (metis restrict_abs_state_struct(1) t2a_state_get_store)

lemma get_trace_a2t_states :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "get_trace \<omega> = (\<lambda> x. Some (stabilize (t2a_virtual_state x))) \<circ>\<^sub>m get_trace_total \<omega>\<^sub>t"
  using assms apply (simp add:a2t_states_def)
  by (metis restrict_abs_state_struct(2) t2a_state_get_trace)

lemma a2t_states_mask_wf :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "wf_mask_simple (get_mh_total (get_total_full \<omega>\<^sub>t))"
  using assms by (simp add:a2t_states_def)

lemma get_mh_total_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "get_mh_total (get_total_full \<omega>\<^sub>t) = get_vm (get_state \<omega>)"
  apply (subgoal_tac "\<exists> A. \<omega> = t2a_state \<omega>\<^sub>t |`\<^sub>a A")
   prefer 2 using assms apply (simp add:a2t_states_def) apply blast
  using assms by (clarsimp simp add:t2a_state_get_state a2t_states_mask_wf)

lemma get_hh_total_lookup_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  assumes "get_vh (get_state \<omega>) hl = Some x"
  shows "get_hh_total (get_total_full \<omega>\<^sub>t) hl = x"
proof -
  from assms have "get_vh (get_state (t2a_state \<omega>\<^sub>t |`\<^sub>a dom (get_vh (get_state \<omega>)))) hl = Some x"
    unfolding a2t_states_def by (simp)
  from this assms(2) show "?thesis"
    by (simp add:restrict_map_eq_Some t2a_state_get_state)
qed

(* This lemma is intended to be used as an frule to add an non-recursive equation for get_hh_total (get_total_full \<omega>\<^sub>t) into the context. *)
lemma get_hh_total_a2t_states_alt :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "\<exists> x. get_hh_total (get_total_full \<omega>\<^sub>t) = (\<lambda> hl. case_option (x hl) id (get_vh (get_state \<omega>) hl))"
  apply (rule exI[of _ "get_hh_total (get_total_full \<omega>\<^sub>t)"]) apply (rule ext)
  using assms by (simp split:option.splits)


lemma heap_typing_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "heap_typing ctxt (get_hh_total (get_total_full \<omega>\<^sub>t)) \<longleftrightarrow>
   partial_heap_typing ctxt (get_vh (get_state \<omega>))"
  using assms unfolding a2t_states_def
  by (clarsimp simp add: a2t_extend_ok_def)

lemma trace_typing_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "trace_typing ctxt (get_trace_total \<omega>\<^sub>t) \<longleftrightarrow>
   partial_trace_typing ctxt (get_trace \<omega>)"
  using assms unfolding a2t_states_def a2t_extend_ok_def
  by (simp)

lemma total_state_typing_a2t_states [simp] :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>\<^sub>t \<longleftrightarrow> abs_state_typing ctxt \<Lambda> \<omega>"
  using assms
  by (simp add:total_state_typing_def abs_state_typing_def)

(* This lemma prevents the recursion in the equation and thus makes it usable with simp *)
lemma a2t_states_in_exE :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  assumes "\<And> st. \<omega> = set_state (t2a_state \<omega>\<^sub>t) st \<Longrightarrow> P"
  shows "P"
  apply (rule assms(2))
   apply (rule full_state_ext)
  using assms(1) by (simp_all add:get_trace_a2t_states)

lemma a2t_states_get_trace_total_None [simp]:
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  shows "get_trace_total \<omega>\<^sub>t l = None \<longleftrightarrow> get_trace \<omega> l = None"
  apply (insert assms) by (erule a2t_states_in_exE; simp add:map_comp_None_iff)

lemma a2t_stateI [intro?] :
  assumes "\<And> x. x \<in> a2t_states ctxt \<omega> \<Longrightarrow> P x"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "P (a2t_state ctxt \<omega>)"
  apply (simp add:a2t_state_def)
  apply (rule assms(1))
  apply (rule someI_ex)
  apply (rule exI[of _ "a2t_extend ctxt \<omega>"])
  apply (rule a2t_statesI_direct)
   prefer 2 using a2t_state_wf_def assms(2) a2t_extend_typed apply blast
  apply (rule full_state_ext; simp add:a2t_extend_def a2t_extend_state_def full_total_state.defs total_state.defs t2a_state_get_state)
  subgoal
    apply (rule virtual_state_ext; simp)
    apply (rule ext)
    by (auto simp add:restrict_map_def a2t_extend_heap_def vstate_wf_ppos split:option.splits)
  subgoal
    apply (rule ext) apply (clarsimp simp add:map_comp_def split:option.splits)
    apply (rule virtual_state_ext; (simp add:vstate_stabilize_structure(2))?)
    apply (rule ext; auto simp add:restrict_map_def a2t_extend_heap_def)
    using vstate_wf_Some apply fastforce
    apply (subgoal_tac "stable x2")
    using stable_dom_get_vh_eq_get_vm apply fastforce
    using assms(2) a2t_state_wf_def by blast
  subgoal
    by (simp add:a2t_extend_def a2t_extend_state_def full_total_state.defs total_state.defs)
  done

lemma a2t_state_in_a2t_states :
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "a2t_state ctxt \<omega> \<in> a2t_states ctxt \<omega>"
  apply (rule a2t_stateI) using assms by (auto)

lemma get_store_total_a2t_state[simp] :
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "get_store_total (a2t_state ctxt \<omega>) = get_store \<omega>"
  by (rule a2t_stateI; simp add:assms)

lemma heap_typing_a2t_state [simp] :
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "heap_typing ctxt (get_hh_total (get_total_full (a2t_state ctxt \<omega>))) \<longleftrightarrow>
   partial_heap_typing ctxt (get_vh (get_state \<omega>))"
  by (rule a2t_stateI; simp add:assms)

lemma total_state_typing_a2t_state [simp] :
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "total_state_typing ctxt \<Lambda> (a2t_state ctxt \<omega>) \<longleftrightarrow> abs_state_typing ctxt \<Lambda> \<omega>"
  by (rule a2t_stateI; simp add:assms)

lemma get_mh_total_a2t_state[simp] :
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "get_mh_total (get_total_full (a2t_state ctxt \<omega>)) = get_vm (get_state \<omega>)"
  by (rule a2t_stateI; simp add:assms)

lemma get_hh_total_lookup_a2t_state [simp] :
  assumes "get_vh (get_state \<omega>) hl = Some x"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "get_hh_total (get_total_full (a2t_state ctxt \<omega>)) hl = x"
  by (rule a2t_stateI; simp add:assms)

lemma a2t2a_state[simp] :
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "stabilize (t2a_state (a2t_state ctxt \<omega>)) = \<omega>"
  by (rule a2t_stateI; simp add:assms a2t_states_in_stable)


subsection \<open>well_typedly\<close>

lemma well_typed_heap_partial_heap_typing :
 "Instantiation.well_typed_heap
     (map_option (make_semantic_vtyp (ctxt_to_interp ctxt)) \<circ>
      declared_fields (program_total ctxt))
     st \<longleftrightarrow>
   partial_heap_typing ctxt (get_vh st)"
  apply (auto simp add:well_typed_heap_def ValueAndBasicState.well_typed_heap_def)
  sorry

lemma in_well_typedly :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  shows "\<omega> \<in> well_typedly (ctxt_to_interp ctxt) (declared_fields (program_total ctxt)) A
     \<longleftrightarrow> \<omega> \<in> A"
  apply (rule)
  subgoal using well_typedly_incl by blast
  subgoal
    apply (simp add:well_typedly_def well_typed_def snd_get_abs_state fst_get_abs_state)
    using assms by (clarsimp simp add:abs_state_typing_def partial_trace_typing_def well_typed_heap_partial_heap_typing)
  done

lemma well_typedly_singleton :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  shows "well_typedly (ctxt_to_interp ctxt) (declared_fields (program_total ctxt)) {\<omega>} = {\<omega>}"
  apply (rule)
   apply (clarsimp simp add:well_typedly_def)
  using assms by (clarsimp simp add: in_well_typedly)


subsection \<open>preservation of a2t_state_wf\<close>

lemma red_stmt_a2t_state_wf :
  assumes "ConcreteSemantics.red_stmt \<Delta> C \<omega> S"
  assumes "stable \<omega> \<and> a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "\<omega>' \<in> S"
  shows "stable \<omega>' \<and> a2t_state_wf ctxt (get_trace \<omega>')"
  using assms
proof (induct rule: ConcreteSemantics.red_stmt_induct_simple)
  case (Inhale A \<omega>' \<omega> \<Delta>)
  then show ?case
    by (metis get_trace_in_star is_in_set_sum)
next
  case (Exhale a A \<omega> \<omega>' \<Delta>)
  then show ?case apply (simp)
    by (metis greater_def greater_state_has_greater_parts(2))
next
  case (Custom \<Delta> C \<omega> S)
  then show ?case proof (cases C)
    case (FieldAssign r g e)
    from Custom this show ?thesis
      apply (clarsimp simp add:stable_get_state[symmetric] a2t_state_wf_def)
      by (metis Custom.hyps(2) Custom.hyps(3) get_state_set_state red_custom_stable stable_get_state)
  next
    case (Label l)
    from Custom this show ?thesis
      by (clarsimp simp add:stable_get_state[symmetric] a2t_state_wf_def)
  qed
next
  case (Havoc \<Delta> x ty \<omega> v)
  then show ?case    
    by (metis ConcreteSemantics.stable_assign_var_state TypedEqui.assign_var_state_def get_trace_set_store)
next
  case (LocalAssign \<Delta> e \<omega> v x)
  then show ?case
    by (metis ConcreteSemantics.stable_assign_var_state TypedEqui.assign_var_state_def get_trace_set_store)

qed


lemma concrete_red_stmt_post_stable_wf :
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "concrete_red_stmt_post \<Delta> C \<omega> {\<omega>'. stable \<omega>' \<longrightarrow> a2t_state_wf ctxt (get_trace \<omega>') \<longrightarrow> \<omega>' \<in> S}"
  shows "concrete_red_stmt_post \<Delta> C \<omega> S"
  using assms unfolding concrete_red_stmt_post_def using red_stmt_a2t_state_wf by blast


subsection \<open>refinement of pure expressions\<close>

lemma red_pure_refines_red_pure_total :
  assumes "valid_a2t_exp e"
  shows "ctxt, R, Some \<omega>\<^sub>t \<turnstile> \<langle>e; \<omega>\<^sub>t\<rangle> [\<Down>]\<^sub>t Val v \<longleftrightarrow> \<Delta> \<turnstile> \<langle>e; stabilize (t2a_state \<omega>\<^sub>t)\<rangle> [\<Down>] Val v"
  using assms
proof (induction e arbitrary:\<omega>\<^sub>t v)
  case (Binop e1 x2a e2)
  then show ?case
    apply (simp add: red_pure_exp_simps red_pure_simps)
    using eval_binop_implies_eval_normal by fastforce
next
  case (FieldAcc e x2a)
  then show ?case
    by (auto simp add: red_pure_exp_simps red_pure_simps t2a_state_get_state get_valid_locs_def_ppos restrict_map_eq_Some
      vstate_stabilize_structure(2) norm_preal preal_to_real split:if_splits)
next
  case (Old x1a e)
  then show ?case
    by (auto simp add: red_pure_exp_simps red_pure_simps Map.map_comp_Some_iff)
next
  case (ELit x)
  then show ?case
    by (metis extended_val.discI red_pure_elim(1) red_pure_exp_simps(1) red_pure_red_pure_exps.RedLit)
qed (simp add: red_pure_exp_simps red_pure_simps)+

lemma ppos_get_mh_total_total_state_mask[simp] :
 "ppos (get_mh_total (get_total_full (total_state_mask A)) hl) \<longleftrightarrow> hl \<in> A"
  apply (simp add:total_state_mask_def)
  using gr_0_is_ppos by blast

abbreviation "a2t_mask \<omega> \<equiv> total_state_mask (dom (get_vh (get_state \<omega>)))"

lemma red_pure_exp_cong_mh :
  assumes "\<And> hl. ppos (get_mh_total (get_total_full \<omega>0) hl) = ppos (get_mh_total (get_total_full \<omega>0') hl)"
  assumes "valid_a2t_exp e"
  shows "ctxt, R, Some \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r \<longleftrightarrow> ctxt, R, Some \<omega>0' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r"
  using assms
proof (induction e arbitrary:\<omega>0 \<omega>0' \<omega> r)
  case (Binop e1 x2a e2)
  (* We need to be careful with the IH as it can lead to simp loops *)
  from Binop.prems Binop.IH[of \<omega>0 \<omega>0'] show ?case
    by (simp add: red_pure_exp_simps)
next
  case (Unop x1a e)
  from Unop.prems Unop.IH[of \<omega>0 \<omega>0'] show ?case
    by (simp add: red_pure_exp_simps)
next
  case (CondExp e1 e2 e3)
  from CondExp.prems CondExp.IH[of \<omega>0 \<omega>0'] show ?case
    by (simp add: red_pure_exp_simps)
next
  case (FieldAcc e x2a)
  from FieldAcc.prems FieldAcc.IH[of \<omega>0 \<omega>0'] show ?case
    by (auto simp add: red_pure_exp_simps get_valid_locs_def_ppos)
next
  case (Old x1a e)
  from Old.prems Old.IH[of "\<omega>0\<lparr>get_total_full := _ \<rparr>" "\<omega>0'\<lparr>get_total_full := _ \<rparr>"] show ?case
    by (auto simp add: red_pure_exp_simps)
qed (simp add: red_pure_exp_simps)+

lemma red_pure_exp_cong_mh_eq :
  assumes "\<And> hl. ppos (get_mh_total (get_total_full \<omega>0) hl) = ppos (get_mh_total (get_total_full \<omega>) hl)"
  assumes "valid_a2t_exp e"
  shows "ctxt, R, Some \<omega>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r \<longleftrightarrow> ctxt, R, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r"
  using assms by (rule red_pure_exp_cong_mh)

lemma red_pure_exp_a2t_mask :
  assumes "stable \<omega>"
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  assumes "valid_a2t_exp e"
  shows "ctxt, R, Some (a2t_mask \<omega>) \<turnstile> \<langle>e; \<omega>\<^sub>t'\<rangle> [\<Down>]\<^sub>t r \<longleftrightarrow> ctxt, R, Some \<omega>\<^sub>t \<turnstile> \<langle>e; \<omega>\<^sub>t'\<rangle> [\<Down>]\<^sub>t r"
  using assms apply (subst red_pure_exp_cong_mh; simp?)
  by (subst stable_dom_get_vh_eq_get_vm; (simp add:stable_get_state)?)

lemma red_pure_refines_red_pure_total_unstable :
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  assumes "valid_a2t_exp e"
  shows "ctxt, R, Some (a2t_mask \<omega>) \<turnstile> \<langle>e; \<omega>\<^sub>t\<rangle> [\<Down>]\<^sub>t Val v \<longleftrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v"
  using assms
proof (induction e arbitrary:\<omega> \<omega>\<^sub>t v)
  case (Binop e1 x2a e2)
  then show ?case
    apply (simp add: red_pure_exp_simps red_pure_simps)
    using eval_binop_implies_eval_normal by fastforce
next
  case (FieldAcc e x2a)
  then show ?case
    apply (auto simp add: red_pure_exp_simps red_pure_simps t2a_state_get_state get_valid_locs_def_ppos split:if_splits)
    by force
next
  case (Old x1a e)
  from Old.prems show ?case
    apply (simp)
    apply (erule a2t_states_in_exE)
    apply (simp add: red_pure_exp_simps red_pure_simps Map.map_comp_Some_iff)
    apply (subst red_pure_exp_cong_mh_eq; simp?)
    apply (subst red_pure_refines_red_pure_total[where ?\<Delta>=\<Delta>])
    by (auto)
next
  case (ELit x)
  then show ?case
    by (metis RedLit2Val_case red_pure_exp_simps(1) red_pure_red_pure_exps.RedLit)
qed (simp add: red_pure_exp_simps red_pure_simps)+

lemma red_exhale_a2t_mask :
  assumes "stable \<omega>"
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt \<omega>"
  assumes "valid_a2t_assert A"
  shows "red_exhale ctxt R (a2t_mask \<omega>) A \<omega>\<^sub>t' r \<longleftrightarrow> red_exhale ctxt R \<omega>\<^sub>t A \<omega>\<^sub>t' r"
  using assms
proof (induction A arbitrary: \<omega>\<^sub>t \<omega>\<^sub>t' r)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      by (simp add:red_exhale_simps red_pure_exp_a2t_mask)
  next
    case (Acc e f ep)
    from Atomic this show ?thesis
      by (cases ep; simp add:red_exhale_simps red_pure_exp_a2t_mask)
  next
    case (AccPredicate e es ep)
    from Atomic this show ?thesis by (simp)
  qed
qed (simp add:red_exhale_simps red_pure_exp_a2t_mask)+

subsection \<open>red_inhale_set lemmas\<close>

definition red_inhale_set :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> (_, _) assert \<Rightarrow>
  'a full_total_state set \<Rightarrow> 'a full_total_state set" where
"red_inhale_set ctxt R A \<Omega> = {\<omega>'. \<exists> \<omega>. \<omega> \<in> \<Omega> \<and> red_inhale ctxt R A \<omega> (RNormal \<omega>')}"


lemma red_inhale_set_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  shows "red_inhale_set ctxt R A \<Omega>1 \<subseteq> red_inhale_set ctxt R A \<Omega>2"
  using assms by (auto simp add:red_inhale_set_def)

lemma red_inhale_set_preserves_typing :
  assumes "\<omega> \<in> red_inhale_set ctxt R A \<Omega>"
  assumes "\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> total_state_typing ctxt \<Lambda> \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>"
  using assms unfolding red_inhale_set_def using red_inhale_preserves_typing by blast

lemma red_inhale_set_preserves_typing_a2t :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>')"
  assumes "a2t_states ctxt \<omega>' \<subseteq> red_inhale_set ctxt R A (a2t_states ctxt \<omega>)"
  shows "abs_state_typing ctxt \<Lambda> \<omega>'"
  unfolding red_inhale_set_def
  apply (subgoal_tac "total_state_typing ctxt \<Lambda> (a2t_state ctxt \<omega>')")
  subgoal by (simp add:assms)
  apply (rule red_inhale_set_preserves_typing)
  apply (insert Set.subsetD[OF assms(3), of "a2t_state ctxt \<omega>'"])
    apply (clarsimp simp add:a2t_state_in_a2t_states assms) apply (assumption)
  using assms by (clarsimp)

definition red_inhale_set_ok :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> (_, _) assert \<Rightarrow>
  'a full_total_state set \<Rightarrow> bool" where
"red_inhale_set_ok ctxt R A \<Omega> \<longleftrightarrow> (\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> \<not> red_inhale ctxt R A \<omega> RFailure)"


lemma red_inhale_set_ok_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  assumes "red_inhale_set_ok ctxt R A \<Omega>2"
  shows "red_inhale_set_ok ctxt R A \<Omega>1"
  using assms by (auto simp add:red_inhale_set_ok_def)


lemma red_inhale_set_okE :
  assumes "red_inhale_set_ok ctxt R A \<Omega>"
  assumes "\<omega> \<in> \<Omega>"
  shows "\<not> red_inhale ctxt R A \<omega> RFailure"
  using assms by (simp add:red_inhale_set_ok_def)


lemma red_inhale_ok_PureE :
  assumes "red_inhale_set_ok ctxt R (Atomic (Pure e)) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Pure e))"
  assumes "stable \<omega>"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Atomic (Pure e))"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_inhale ctxt R (Atomic (Pure e)) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_inhale_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; clarsimp simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  then show "?thesis" by (blast)
qed

lemma red_inhale_set_PureI :
  assumes "stable \<omega>"
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "valid_a2t_assert (Atomic (Pure e))"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_inhale_set ctxt R (Atomic (Pure e)) (a2t_states ctxt \<omega>) = (if b then a2t_states ctxt \<omega> else {})"
  using assms
  apply (auto simp add:red_inhale_set_def red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable dest:red_pure_det)
  by (auto)

lemma red_inhale_ok_AccPureE :
  assumes "red_inhale_set_ok ctxt R (Atomic (Acc e f (PureExp ep))) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Acc e f (PureExp ep)))"
  assumes "stable \<omega>"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Atomic (Acc e f (PureExp ep)))"
  shows  "\<exists> r p. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)) \<and> (\<Delta> \<turnstile> \<langle>ep; \<omega>\<rangle> [\<Down>] Val (VPerm p)) \<and> 0 \<le> p"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_inhale ctxt R (Atomic (Acc e f (PureExp ep))) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_inhale_set_ok_def)
  note calc = calc this
  then
  show "?thesis"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; auto simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
qed


lemma red_inhale_set_AccPureI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)"
  assumes "\<Delta> \<turnstile> \<langle>ep; \<omega>\<rangle> [\<Down>] Val (VPerm p)"
  assumes "stable \<omega>"
  assumes "0 \<le> p"
  assumes "valid_a2t_assert (Atomic (Acc e f (PureExp ep)))"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_inhale_set ctxt R (Atomic (Acc e f (PureExp ep))) (a2t_states ctxt \<omega>) =
    (if r = Null then (if p = 0 then (a2t_states ctxt \<omega>) else {}) else
     Set.bind (a2t_states ctxt \<omega>) (\<lambda> \<omega>'. inhale_perm_single R \<omega>' (the_address r, f) (Some (Abs_preal p))))"
  using assms
  apply (auto simp add:red_inhale_set_def red_inhale_simps th_result_rel.simps
      red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable dest:red_pure_det) (* Long *)
      apply (auto)
  by (metis a2t_statesI_direct_stable assms(3) red_pure_val_unique(1) val.inject(3) val.inject(4))+


lemma red_inhale_ok_AccWildcardE :
  assumes "red_inhale_set_ok ctxt R (Atomic (Acc e f Wildcard)) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Acc e f Wildcard))"
  assumes "stable \<omega>"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Atomic (Acc e f Wildcard))"
  shows  "\<exists> r. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_inhale ctxt R (Atomic (Acc e f Wildcard)) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_inhale_set_ok_def)
  note calc = calc this
  then
  show "?thesis"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
    by (auto)
qed

lemma red_inhale_set_AccWildcardI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)"
  assumes "stable \<omega>"
  assumes "valid_a2t_assert (Atomic (Acc e f Wildcard))"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_inhale_set ctxt R (Atomic (Acc e f Wildcard)) (a2t_states ctxt \<omega>) =
    (if r = Null then {} else
     Set.bind (a2t_states ctxt \<omega>) (\<lambda> \<omega>'. inhale_perm_single R \<omega>' (the_address r, f) None))"
  using assms
  apply (auto simp add:red_inhale_set_def red_inhale_simps th_result_rel.simps
      red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable dest:red_pure_det)
  by (auto)

lemma red_inhale_ok_ImpE :
  assumes "red_inhale_set_ok ctxt R (Imp e A) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Imp e A)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Imp e A)"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and> (b \<longrightarrow> red_inhale_set_ok ctxt R A (a2t_states ctxt \<omega>))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_inhale ctxt R (Imp e A) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_inhale_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    apply (clarsimp simp add:assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; clarsimp simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  have "b \<Longrightarrow> red_inhale_set_ok ctxt R A (a2t_states ctxt \<omega>)"
    unfolding red_inhale_set_ok_def apply (rule, rule) proof -
    fix \<omega>' assume Hin : "\<omega>' \<in> a2t_states ctxt \<omega>" assume b
    show "\<not> red_inhale ctxt R A \<omega>' RFailure"
      apply (insert red_inhale_set_okE[OF assms(1) Hin])
      using calc apply (simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
      using Hin calc \<open>b\<close> by (clarsimp simp add:a2t_states_in_stable)
    qed
  note calc = calc this
  then show "?thesis" by (blast)
qed

lemma red_inhale_set_ImpI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "stable \<omega>"
  assumes "valid_a2t_assert (Imp e A)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_inhale_set ctxt R (Imp e A) (a2t_states ctxt \<omega>) =
     (if b then red_inhale_set ctxt R A (a2t_states ctxt \<omega>) else (a2t_states ctxt \<omega>))"
  using assms
  by (auto simp add:red_inhale_set_def red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable dest:red_pure_det)

lemma red_inhale_ok_CondAssertE :
  assumes "red_inhale_set_ok ctxt R (CondAssert e A1 A2) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (CondAssert e A1 A2)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (CondAssert e A1 A2)"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and>
     red_inhale_set_ok ctxt R (if b then A1 else A2) (a2t_states ctxt \<omega>)"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_inhale ctxt R (CondAssert e A1 A2) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_inhale_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    apply (clarsimp simp add:assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_state ctxt \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; clarsimp simp add:red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  show "?thesis"
    unfolding red_inhale_set_ok_def apply (rule exI, rule, rule calc, safe)
    apply (cut_tac red_inhale_set_okE[OF assms(1)]) prefer 2 apply (assumption)
    apply (clarsimp simp add:red_inhale_set_ok_def red_inhale_simps)
    using calc by (clarsimp simp add:red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable split:if_splits)
qed

lemma red_inhale_set_CondAssertI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "stable \<omega>"
  assumes "valid_a2t_assert (CondAssert e A1 A2)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_inhale_set ctxt R (CondAssert e A1 A2) (a2t_states ctxt \<omega>) =
     red_inhale_set ctxt R (if b then A1 else A2) (a2t_states ctxt \<omega>)"
  using assms
  by (auto simp add:red_inhale_set_def red_inhale_simps red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable dest:red_pure_det)

lemma red_inhale_ok_StarE:
  assumes "red_inhale_set_ok ctxt R (assert.Star A1 A2) (a2t_states ctxt \<omega>)"
  shows "red_inhale_set_ok ctxt R A1 (a2t_states ctxt \<omega>) \<and>
      red_inhale_set_ok ctxt R A2 (red_inhale_set ctxt R A1 (a2t_states ctxt \<omega>))"
  using assms by (auto simp add:red_inhale_set_ok_def red_inhale_set_def red_inhale_simps)

lemma red_inhale_set_StarI :
  shows "red_inhale_set ctxt R (assert.Star A1 A2) \<Omega> =
    (red_inhale_set ctxt R A2 (red_inhale_set ctxt R A1 \<Omega>))"
  by (auto simp add:red_inhale_set_def red_inhale_simps)

subsection \<open>red_exhale_set lemmas\<close>

definition red_exhale_set :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> (_, _) assert \<Rightarrow>
  'a full_total_state set \<Rightarrow> 'a full_total_state set" where
"red_exhale_set ctxt R \<omega>0 A \<Omega> = {\<omega>'. \<exists> \<omega>. \<omega> \<in> \<Omega> \<and> red_exhale ctxt R \<omega>0 A \<omega> (RNormal \<omega>')}"


lemma red_exhale_set_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  shows "red_exhale_set ctxt R \<omega>0 A \<Omega>1 \<subseteq> red_exhale_set ctxt R \<omega>0 A \<Omega>2"
  using assms by (auto simp add:red_exhale_set_def)

lemma red_exhale_set_preserves_typing :
  assumes "\<omega> \<in> red_exhale_set ctxt R \<omega>0 A \<Omega>"
  assumes "\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> total_state_typing ctxt \<Lambda> \<omega>"
  shows "total_state_typing ctxt \<Lambda> \<omega>"
  using assms unfolding red_exhale_set_def using red_exhale_preserves_typing by blast

lemma red_exhale_set_preserves_typing_a2t :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>')"
  assumes "a2t_states ctxt \<omega>' \<subseteq> red_exhale_set ctxt R \<omega>0 A (a2t_states ctxt \<omega>)"
  shows "abs_state_typing ctxt \<Lambda> \<omega>'"
  unfolding red_exhale_set_def
  apply (subgoal_tac "total_state_typing ctxt \<Lambda> (a2t_state ctxt \<omega>')")
  subgoal by (simp add:assms)
  apply (rule red_exhale_set_preserves_typing)
  apply (insert Set.subsetD[OF assms(3), of "a2t_state ctxt \<omega>'"])
    apply (clarsimp simp add:a2t_state_in_a2t_states assms) apply (assumption)
  using assms by (clarsimp)

definition red_exhale_set_ok :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> (_, _) assert \<Rightarrow>
  'a full_total_state set \<Rightarrow> bool" where
"red_exhale_set_ok ctxt R \<omega>0 A \<Omega> \<longleftrightarrow> (\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> \<not> red_exhale ctxt R \<omega>0 A \<omega> RFailure)"


lemma red_exhale_set_ok_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  assumes "red_exhale_set_ok ctxt R \<omega>0 A \<Omega>2"
  shows "red_exhale_set_ok ctxt R \<omega>0 A \<Omega>1"
  using assms by (auto simp add:red_exhale_set_ok_def)


lemma red_exhale_set_okE :
  assumes "red_exhale_set_ok ctxt R \<omega>0 A \<Omega>"
  assumes "\<omega> \<in> \<Omega>"
  shows "\<not> red_exhale ctxt R \<omega>0 A \<omega> RFailure"
  using assms by (simp add:red_exhale_set_ok_def)

lemma red_exhale_ok_PureE :
  assumes "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (Atomic (Pure e)) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Pure e))"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Atomic (Pure e))"
  shows  "(\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool True))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_exhale ctxt R (a2t_mask \<omega>) (Atomic (Pure e)) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_exhale_set_ok_def)
  note calc = calc this
  then have "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool True))"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_exhale_simps exh_if_total_unfold red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
    by (metis (full_types))
  note calc = calc this
  then show "?thesis" by (blast)
qed

lemma red_exhale_set_PureI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool True)"
  assumes "valid_a2t_assert (Atomic (Pure e))"
  shows  "red_exhale_set ctxt R (a2t_mask \<omega>) (Atomic (Pure e)) (a2t_states ctxt \<omega>) = a2t_states ctxt \<omega>"
  using assms
  apply (auto simp add:red_exhale_set_def red_exhale_simps exh_if_total_unfold red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] dest:red_pure_det)
  using red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] by (metis)

lemma red_exhale_ok_ImpE :
  assumes "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (Imp e A) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Imp e A)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Imp e A)"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and> (b \<longrightarrow> red_exhale_set_ok ctxt R (a2t_mask \<omega>) A (a2t_states ctxt \<omega>))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_exhale ctxt R (a2t_mask \<omega>) (Imp e A) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_exhale_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    apply (clarsimp simp add:assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; clarsimp simp add:red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  have "b \<Longrightarrow> red_exhale_set_ok ctxt R (a2t_mask \<omega>) A (a2t_states ctxt \<omega>)"
    unfolding red_exhale_set_ok_def apply (rule, rule) proof -
    fix \<omega>' assume Hin : "\<omega>' \<in> a2t_states ctxt \<omega>" assume b
    show "\<not> red_exhale ctxt R (a2t_mask \<omega>) A \<omega>' RFailure"
      apply (insert red_exhale_set_okE[OF assms(1) Hin])
      using calc apply (simp add:red_exhale_simps Hin red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
      using Hin calc \<open>b\<close> by (clarsimp)
    qed
  note calc = calc this
  then show "?thesis" by (blast)
qed

lemma red_exhale_set_ImpI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "valid_a2t_assert (Imp e A)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_exhale_set ctxt R (a2t_mask \<omega>) (Imp e A) (a2t_states ctxt \<omega>) =
     (if b then red_exhale_set ctxt R (a2t_mask \<omega>) A (a2t_states ctxt \<omega>) else (a2t_states ctxt \<omega>))"
  using assms
  by (auto simp add:red_exhale_set_def red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] dest:red_pure_det)

lemma red_exhale_ok_CondAssertE :
  assumes "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (CondAssert e A1 A2) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (CondAssert e A1 A2)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (CondAssert e A1 A2)"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and>
   red_exhale_set_ok ctxt R (a2t_mask \<omega>) (if b then A1 else A2) (a2t_states ctxt \<omega>)"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_exhale ctxt R (a2t_mask \<omega>) (CondAssert e A1 A2) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_exhale_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    apply (clarsimp simp add:assertion_typing_simps)
    apply (frule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    by (case_tac "r"; clarsimp simp add:red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  have "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (if b then A1 else A2) (a2t_states ctxt \<omega>)"
    unfolding red_exhale_set_ok_def apply (rule, rule) proof -
    fix \<omega>' assume Hin : "\<omega>' \<in> a2t_states ctxt \<omega>"
    show "\<not> red_exhale ctxt R (a2t_mask \<omega>) (if b then A1 else A2) \<omega>' RFailure"
      apply (insert red_exhale_set_okE[OF assms(1) Hin])
      using calc apply (simp add:red_exhale_simps Hin red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
      using Hin calc by (cases "b"; clarsimp)
    qed
  note calc = calc this
  then show "?thesis" by (blast)
qed

lemma red_exhale_set_CondAssertI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "valid_a2t_assert (CondAssert e A1 A2)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows  "red_exhale_set ctxt R (a2t_mask \<omega>) (CondAssert e A1 A2) (a2t_states ctxt \<omega>) =
     (red_exhale_set ctxt R (a2t_mask \<omega>) (if b then A1 else A2) (a2t_states ctxt \<omega>))"
  using assms
  by (auto simp add:red_exhale_set_def red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] dest:red_pure_det)

lemma red_exhale_ok_AccPureE :
  assumes "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (Atomic (Acc e f (PureExp ep))) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Acc e f (PureExp ep)))"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "valid_a2t_assert (Atomic (Acc e f (PureExp ep)))"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows  "\<exists> r p. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)) \<and> (\<Delta> \<turnstile> \<langle>ep; \<omega>\<rangle> [\<Down>] Val (VPerm p)) \<and>
     0 \<le> p \<and> (if r = Null then p = 0 else Abs_preal p \<le> get_vm (get_state \<omega>) (the_address r, f))"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_exhale ctxt R (a2t_mask \<omega>) (Atomic (Acc e f (PureExp ep))) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_exhale_set_ok_def)
  note calc = calc this
  then
  show "?thesis"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
    by (metis PosReal.pgte.rep_eq get_mh_total_a2t_state less_eq_preal.rep_eq)
qed

lemma ppos_pmin_1 :
  "ppos (pmin 1 p) \<longleftrightarrow> ppos p"
  by (simp add:norm_preal preal_to_real)

lemma a2t_states_del_perm :
  "a2t_states ctxt (set_state \<omega> (del_perm (get_state \<omega>) hl p)) =
     (\<lambda> \<omega>\<^sub>t. \<omega>\<^sub>t\<lparr>get_total_full := get_total_full \<omega>\<^sub>t
                     \<lparr>get_mh_total := (get_mh_total (get_total_full \<omega>\<^sub>t))
                        (hl := get_mh_total (get_total_full \<omega>\<^sub>t) hl - p)\<rparr>\<rparr>) ` a2t_states ctxt \<omega>"
  apply (safe; clarsimp simp add:Set.image_iff Bex_def)
  subgoal for \<omega>\<^sub>t
    apply (rule exI[of _ "\<omega>\<^sub>t\<lparr>get_total_full := get_total_full \<omega>\<^sub>t\<lparr>get_mh_total := (get_vm (get_state \<omega>))(hl := get_vm (get_state \<omega>) hl)\<rparr>\<rparr>"])
    apply (clarsimp)
    apply (rule a2t_statesI_direct; (simp add:a2t_extend_ok_def)?)
    apply (rule full_state_ext; simp add:get_trace_a2t_states[symmetric])
    apply (rule virtual_state_ext; simp add:t2a_state_get_state)
    apply (rule ext; simp add:restrict_map_def) using vstate_wf_Some by fastforce
  subgoal for \<omega>\<^sub>t
    apply (rule a2t_statesI_direct; (simp add:a2t_extend_ok_def)?)
    apply (rule full_state_ext; simp add:get_trace_a2t_states[symmetric])
    apply (rule virtual_state_ext; simp add:t2a_state_get_state)
    subgoal
      apply (rule ext; simp)
      by (metis (mono_tags, lifting) eq_pnone_not_ppos get_vm_bound inf.absorb2 minus_preal.abs_eq order_trans ppos_pmin_1 psub_smaller zero_preal_def)
    subgoal
     apply (rule ext; simp add:restrict_map_def ppos_pmin_1)
      by (metis (no_types, opaque_lifting) core_option.cases domIff get_hh_total_lookup_a2t_states preal_sub_ppos vstate_wf_ppos)
    subgoal
      apply (rule wf_mask_simpleI; simp)
      using get_vm_bound by (metis del_perm_get_vm fun_upd_same)
    done
  done

lemma red_exhale_set_AccPureI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)"
  assumes "\<Delta> \<turnstile> \<langle>ep; \<omega>\<rangle> [\<Down>] Val (VPerm p)"
  assumes "0 \<le> p"
  assumes "if r = Null then p = 0 else Abs_preal p \<le> get_vm (get_state \<omega>) (the_address r, f)"
  assumes "valid_a2t_assert (Atomic (Acc e f (PureExp ep)))"
  assumes "\<omega>\<^sub>t \<in> (if r = Null then a2t_states ctxt \<omega> else
     a2t_states ctxt (set_state \<omega> (del_perm (get_state \<omega>) (the_address r, f) (Abs_preal p))))"
  shows  "\<omega>\<^sub>t \<in> red_exhale_set ctxt R (a2t_mask \<omega>) (Atomic (Acc e f (PureExp ep))) (a2t_states ctxt \<omega>)"
  using assms
  apply (clarsimp simp add:red_exhale_set_def red_exhale_simps a2t_states_del_perm Set.image_iff
      red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] split:if_splits)
  subgoal using red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] by blast
  subgoal
    apply (rule exI, safe, assumption, rule exI[of _ "r"]; simp add:red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
    using PosReal.pgte.rep_eq less_eq_preal.rep_eq by blast
  done

lemma red_exhale_ok_AccWildcardE :
  assumes "red_exhale_set_ok ctxt R (a2t_mask \<omega>) (Atomic (Acc e f Wildcard)) (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> (Atomic (Acc e f Wildcard))"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert (Atomic (Acc e f Wildcard))"
  shows  "\<exists> r. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)) \<and> r \<noteq> Null \<and> 0 < get_vm (get_state \<omega>) (the_address r, f)"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_exhale ctxt R (a2t_mask \<omega>) (Atomic (Acc e f Wildcard)) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_exhale_set_ok_def)
  note calc = calc this
  then
  show "?thesis"
    apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps exp_or_wildcard_typing.simps)
    apply (drule red_pure_exp_typed[where ?ctxt="ctxt" and ?R="R" and ?\<omega>="a2t_state ctxt \<omega>" and ?\<omega>_def="Some (a2t_mask \<omega>)"]; simp)
    apply (clarsimp)
    apply (case_tac "r"; clarsimp simp add:red_exhale_simps red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])
    using not_gr_0 by auto
qed

lemma red_exhale_set_AccWildcardI :
  assumes "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef r)"
  assumes "r \<noteq> Null"
  assumes "get_vm (get_state \<omega>) (the_address r, f) \<noteq> pnone"
  assumes "p = epsilon_preal (get_vm (get_state \<omega>) (the_address r, f))"
  assumes "valid_a2t_assert (Atomic (Acc e f Wildcard))"
  assumes  "\<omega>\<^sub>t \<in> a2t_states ctxt (set_state \<omega> (del_perm (get_state \<omega>) (the_address r, f) p))"
  shows "\<omega>\<^sub>t \<in> red_exhale_set ctxt R (a2t_mask \<omega>) (Atomic (Acc e f Wildcard)) (a2t_states ctxt \<omega>)"
  using assms
  apply (clarsimp simp add:red_exhale_set_def red_exhale_simps a2t_states_del_perm Set.image_iff
      red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"] split:if_splits)
  apply (safe del:exI intro!:exI; assumption?; (rule refl)?; (simp add:red_pure_refines_red_pure_total_unstable[where ?\<Delta>="\<Delta>"])?)
  using epsilon_preal_bounds[of "(get_vm (get_state \<omega>) (the_address r, f))"] by blast+

lemma red_exhale_ok_StarE:
  assumes "red_exhale_set_ok ctxt R \<omega>0 (assert.Star A1 A2) (a2t_states ctxt \<omega>)"
  shows "red_exhale_set_ok ctxt R \<omega>0 A1 (a2t_states ctxt \<omega>) \<and>
      red_exhale_set_ok ctxt R \<omega>0 A2 (red_exhale_set ctxt R  \<omega>0 A1 (a2t_states ctxt \<omega>))"
  using assms by (auto simp add:red_exhale_set_ok_def red_exhale_set_def red_exhale_simps)

lemma red_exhale_set_StarI :
  shows "red_exhale_set ctxt R \<omega>0 (assert.Star A1 A2) \<Omega> =
    (red_exhale_set ctxt R \<omega>0 A2 (red_exhale_set ctxt R \<omega>0 A1 \<Omega>))"
  by (auto simp add:red_exhale_set_def red_exhale_simps)

subsection \<open>red_stmt_total_ok lemmas\<close>

definition red_stmt_total_set :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> stmt \<Rightarrow>
  'a full_total_state set \<Rightarrow> 'a full_total_state set" where
"red_stmt_total_set ctxt R \<Lambda> C \<Omega> = {\<omega>'. \<exists> \<omega>. \<omega> \<in> \<Omega> \<and> red_stmt_total ctxt R \<Lambda> C \<omega> (RNormal \<omega>')}"

lemma red_stmt_total_set_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  shows "red_stmt_total_set ctxt R \<Lambda> C \<Omega>1 \<subseteq> red_stmt_total_set ctxt R \<Lambda> C \<Omega>2"
  using assms by (auto simp add:red_stmt_total_set_def)

lemma red_stmt_total_set_preserves_typing :
  assumes "\<omega> \<in> red_stmt_total_set ctxt R \<Lambda> C \<Omega>"
  assumes "\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> total_state_typing ctxt \<Lambda> \<omega>"
  assumes "valid_a2t_stmt C"
  shows "total_state_typing ctxt \<Lambda> \<omega>"
  using assms unfolding red_stmt_total_set_def using red_stmt_total_preserves_typing by blast

lemma red_stmt_total_set_preserves_typing_a2t :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_states ctxt \<omega>' \<subseteq> red_stmt_total_set ctxt R \<Lambda> C (a2t_states ctxt \<omega>)"
  assumes "valid_a2t_stmt C"
  assumes "a2t_state_wf ctxt (get_trace \<omega>')"
  shows "abs_state_typing ctxt \<Lambda> \<omega>'"
  unfolding red_stmt_total_set_def
  apply (subgoal_tac "total_state_typing ctxt \<Lambda> (a2t_state ctxt \<omega>')")
  subgoal by (simp add:assms)
  apply (rule red_stmt_total_set_preserves_typing)
  apply (insert Set.subsetD[OF assms(2), of "a2t_state ctxt \<omega>'"])
    apply (clarsimp simp add:a2t_state_in_a2t_states assms) apply (assumption)
  using assms by (clarsimp)+

definition red_stmt_total_set_ok :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> stmt \<Rightarrow>
  'a full_total_state set \<Rightarrow> bool" where
"red_stmt_total_set_ok ctxt R \<Lambda> C \<Omega> \<longleftrightarrow> (\<forall> \<omega>. \<omega> \<in> \<Omega> \<longrightarrow> \<not> red_stmt_total ctxt R \<Lambda> C \<omega> RFailure)"

lemma red_stmt_total_set_ok_mono :
  assumes "\<Omega>1 \<subseteq> \<Omega>2"
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> C \<Omega>2"
  shows "red_stmt_total_set_ok ctxt R \<Lambda> C \<Omega>1"
  using assms by (auto simp add:red_stmt_total_set_ok_def)


lemma red_stmt_total_set_okE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> C \<Omega>"
  assumes "\<omega> \<in> \<Omega>"
  shows "\<not> red_stmt_total ctxt R \<Lambda> C \<omega> RFailure"
  using assms by (simp add:red_stmt_total_set_ok_def)

lemma red_stmt_total_ok_InhaleE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.Inhale e) (a2t_states ctxt \<omega>)"
  shows  "red_inhale_set_ok ctxt R e (a2t_states ctxt \<omega>)"
  using assms by (simp add:red_stmt_total_set_ok_def red_inhale_set_ok_def not_fail_Inhale a2t_state_in_a2t_states)

lemma red_stmt_total_set_InhaleI :
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.Inhale e) (a2t_states ctxt \<omega>) =
    {\<omega>\<^sub>t'. \<exists> \<omega>\<^sub>t. \<omega>\<^sub>t \<in> a2t_states ctxt \<omega> \<and> red_inhale ctxt R e \<omega>\<^sub>t (RNormal \<omega>\<^sub>t')}"
  by (auto simp add:red_stmt_total_set_def red_stmt_total_simps)

lemma red_stmt_total_ok_ExhaleE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.Exhale e) (a2t_states ctxt \<omega>)"
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.Exhale e)"
  shows "red_exhale_set_ok ctxt R (a2t_mask \<omega>) e (a2t_states ctxt \<omega>)"
  using assms by (simp add:red_stmt_total_set_ok_def not_fail_Exhale red_exhale_set_ok_def red_exhale_a2t_mask)

lemma red_stmt_total_set_ExhaleI :
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.Exhale e)"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.Exhale e) (a2t_states ctxt \<omega>) =
   Set.bind (red_exhale_set ctxt R (a2t_mask \<omega>) e (a2t_states ctxt \<omega>)) (\<lambda> \<omega>_exh.
       havoc_locs_state ctxt \<omega>_exh {loc. ppos (get_vm (get_state \<omega>) loc) \<and>
          get_mh_total (get_total_full \<omega>_exh) loc = PosReal.pnone})"
  using assms apply (auto simp add:red_stmt_total_set_def red_stmt_total_simps red_exhale_set_def red_exhale_a2t_mask gr_0_is_ppos)
  using red_exhale_a2t_mask apply blast
   by fastforce

lemma red_stmt_total_ok_AssertE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.Assert e) (a2t_states ctxt \<omega>)"
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.Assert e)"
  shows "red_exhale_set_ok ctxt R (a2t_mask \<omega>) e (a2t_states ctxt \<omega>)"
  using assms by (simp add:red_stmt_total_set_ok_def not_fail_Assert red_exhale_set_ok_def red_exhale_a2t_mask)

lemma red_stmt_total_set_AssertI :
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.Assert e)"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.Assert e) (a2t_states ctxt \<omega>) = Set.filter (\<lambda> \<omega>\<^sub>t. \<exists> \<omega>\<^sub>t'. red_exhale ctxt R (a2t_mask \<omega>) e \<omega>\<^sub>t (RNormal \<omega>\<^sub>t')) (a2t_states ctxt \<omega>)"
  using assms by (auto simp add:red_stmt_total_set_def red_stmt_total_simps red_exhale_set_def red_exhale_a2t_mask)
  (* by fastforce *)

lemma red_stmt_total_ok_IfE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.If e C1 C2) (a2t_states ctxt \<omega>)"
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.If e C1 C2)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "valid_a2t_stmt (stmt.If e C1 C2)"
  shows  "\<exists> b. (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and> red_stmt_total_set_ok ctxt R \<Lambda> (if b then C1 else C2) (a2t_states ctxt \<omega>)"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_stmt_total ctxt R \<Lambda> (stmt.If e C1 C2) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_stmt_total_set_ok_def)
  note calc = calc this
  then obtain b where "(\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b))"
    by (subst (asm) not_fail_If; auto simp add:red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
  note calc = calc this
  have "red_stmt_total_set_ok ctxt R \<Lambda> (if b then C1 else C2) (a2t_states ctxt \<omega>)"
    unfolding red_stmt_total_set_ok_def apply (rule, rule) proof -
    fix \<omega>' assume Hin : "\<omega>' \<in> a2t_states ctxt \<omega>"
    show "\<not> red_stmt_total ctxt R \<Lambda> (if b then C1 else C2) \<omega>' RFailure"
      apply (insert red_stmt_total_set_okE[OF assms(1) Hin])
      apply (subst (asm) not_fail_If)
      using calc Hin apply (simp)
      using calc Hin apply (simp)
      using calc Hin apply (simp)
      using calc Hin apply (clarsimp simp add:red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] a2t_states_in_stable)
      using red_pure_det by fastforce+
    qed
  note calc = calc this
  then show "?thesis" by (blast)
qed


lemma red_stmt_total_set_IfI :
  assumes "\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VBool b)"
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.If e C1 C2)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.If e C1 C2) (a2t_states ctxt \<omega>) =
    (if b then red_stmt_total_set ctxt R \<Lambda> C1 (a2t_states ctxt \<omega>) else red_stmt_total_set ctxt R \<Lambda> C2 (a2t_states ctxt \<omega>))"
  using assms
  by (auto simp add:red_stmt_total_set_def red_stmt_total_simps a2t_states_in_stable red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"]
           dest:red_pure_det)

lemma red_stmt_total_ok_SeqE:
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.Seq C1 C2) (a2t_states ctxt \<omega>)"
  shows "red_stmt_total_set_ok ctxt R \<Lambda> C1 (a2t_states ctxt \<omega>) \<and>
      red_stmt_total_set_ok ctxt R \<Lambda> C2 (red_stmt_total_set ctxt R \<Lambda> C1 (a2t_states ctxt \<omega>))"
  using assms by (auto simp add:red_stmt_total_set_ok_def red_stmt_total_set_def not_fail_Seq)

lemma red_stmt_total_set_SeqI :
  assumes "stable \<omega>"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.Seq C1 C2) \<Omega> =
    (red_stmt_total_set ctxt R \<Lambda> C2 (red_stmt_total_set ctxt R \<Lambda> C1 \<Omega>))"
  by (auto simp add:red_stmt_total_set_def red_stmt_total_simps a2t_states_in_stable)

lemma red_stmt_total_ok_LocalAssignE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.LocalAssign x e) (a2t_states ctxt \<omega>)"
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.LocalAssign x e)"
  assumes "stable \<omega>"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_stmt (stmt.LocalAssign x e)"
  shows  "\<exists> v ty. \<Lambda> x = Some ty \<and> (\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) \<and> has_type (absval_interp_total ctxt) ty v"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_stmt_total ctxt R \<Lambda> (stmt.LocalAssign x e) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_stmt_total_set_ok_def)
  note calc = calc this
  then show "?thesis"
    by (subst (asm) not_fail_LocalAssign; auto simp add:red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
qed


lemma red_stmt_total_set_LocalAssignI :
  assumes "\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val v"
  assumes "\<Lambda> x = Some ty"
  assumes "has_type (absval_interp_total ctxt) ty v"
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.LocalAssign x e)"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.LocalAssign x e) (a2t_states ctxt \<omega>) =
    {\<omega>\<^sub>t'. \<exists> \<omega>\<^sub>t. \<omega>\<^sub>t \<in> (a2t_states ctxt \<omega>) \<and> \<omega>\<^sub>t' = \<omega>\<^sub>t\<lparr>get_store_total := (get_store_total \<omega>\<^sub>t)(x \<mapsto> v)\<rparr>}"
  using assms by (auto simp add:red_stmt_total_set_def red_stmt_total_simps a2t_states_in_stable
    red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] has_type_get_type dest:red_pure_det)


lemma red_stmt_total_ok_FieldAssignE :
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> (stmt.FieldAssign e1 f e2) (a2t_states ctxt \<omega>)"
  assumes "stmt_typing (program_total ctxt) \<Lambda> (stmt.FieldAssign e1 f e2)"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_stmt (stmt.FieldAssign e1 f e2)"
  shows  "\<exists> a v ty. declared_fields (program_total ctxt) f = Some ty \<and>
        (\<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))) \<and>
        (\<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v) \<and>
        get_vm (get_state \<omega>) (a,f) = pwrite \<and>
        has_type (absval_interp_total ctxt) ty v"
proof -
  note calc = assms a2t_state_in_a2t_states[of ctxt \<omega>]
  hence "\<not> red_stmt_total ctxt R \<Lambda> (stmt.FieldAssign e1 f e2) (a2t_state ctxt \<omega>) RFailure"
    by (simp add: red_stmt_total_set_ok_def)
  note calc = calc this
  then show "?thesis"
    apply (subst (asm) not_fail_FieldAssign)
    by (auto simp add:red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"] get_writeable_locs_def)
qed

lemma red_stmt_total_set_FieldAssignI :
  assumes "declared_fields (program_total ctxt) f = Some ty"
  assumes "\<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VRef (Address a))"
  assumes "\<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v"
  assumes "get_vm (get_state \<omega>) (a,f) = pwrite"
  assumes "has_type (absval_interp_total ctxt) ty v"
  assumes "stable \<omega>"
  assumes "valid_a2t_stmt (stmt.FieldAssign e1 f e2)"
  assumes "\<And> f vals st. interp.funs \<Delta> f vals st = None"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.FieldAssign e1 f e2) (a2t_states ctxt \<omega>) =
    {\<omega>\<^sub>t'. \<exists> \<omega>\<^sub>t. \<omega>\<^sub>t \<in> a2t_states ctxt \<omega> \<and>
      \<omega>\<^sub>t' = \<omega>\<^sub>t\<lparr>get_total_full := get_total_full \<omega>\<^sub>t\<lparr>get_hh_total := (get_hh_total (get_total_full \<omega>\<^sub>t))((a, f) := v)\<rparr>\<rparr>}"
  using assms apply (auto simp add:red_stmt_total_set_def red_stmt_total_simps a2t_states_in_stable get_writeable_locs_def
    t2a_state_get_state has_type_get_type
    red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])
  using red_pure_det by blast+

lemma red_stmt_total_set_HavocI :
  assumes "\<Lambda> x = Some ty"
  shows "red_stmt_total_set ctxt R \<Lambda> (stmt.Havoc x) (a2t_states ctxt \<omega>) =
    {\<omega>\<^sub>t'. \<exists> \<omega>\<^sub>t v. \<omega>\<^sub>t \<in> a2t_states ctxt \<omega> \<and> has_type (absval_interp_total ctxt) ty v \<and>
      \<omega>\<^sub>t' = \<omega>\<^sub>t\<lparr>get_store_total := (get_store_total \<omega>\<^sub>t)(x \<mapsto> v)\<rparr>}"
  using assms by (auto simp add:red_stmt_total_set_def red_stmt_total_simps
     has_type_get_type red_pure_refines_red_pure_total[where ?\<Delta>="\<Delta>"])

lemma red_stmt_total_set_LabelI :
  assumes "stable \<omega>"
  assumes "\<omega>\<^sub>t \<in> a2t_states ctxt (if get_trace \<omega> l = None then set_trace \<omega> ((get_trace \<omega>)(l \<mapsto> get_state \<omega>)) else \<omega>)"
  shows "\<omega>\<^sub>t \<in> red_stmt_total_set ctxt R \<Lambda> (stmt.Label l) (a2t_states ctxt \<omega>)"
  using assms apply (clarsimp simp add:red_stmt_total_set_def red_stmt_total_simps split:if_splits)
  subgoal
    apply (rule exI[of _ "\<omega>\<^sub>t\<lparr>get_trace_total := (get_trace_total \<omega>\<^sub>t)(l := None) \<rparr>"]; simp)
    (* TODO: This is not provable since \<omega>\<^sub>t = \<omega>\<^sub>t\<lparr>get_trace_total := get_trace_total \<omega>\<^sub>t(l \<mapsto> get_total_full \<omega>\<^sub>t)\<rparr> might not hold *)
    sorry
  subgoal by (rule exI[of _ \<omega>\<^sub>t]; simp)
  done

subsection \<open>refinement of Inhale\<close>

lemma red_inhale_refines :
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "stable \<omega>"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "red_inhale_set_ok ctxt (\<lambda> _. True) A (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> A"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert A"
  shows  "Stable ({\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A\<rangle>)) \<and>
     (\<forall> \<omega>'. stable (\<down>\<omega>') \<longrightarrow> (\<down>\<omega>') \<in> ({\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A\<rangle>)) \<longrightarrow> a2t_states ctxt (\<down>\<omega>') \<subseteq> red_inhale_set ctxt (\<lambda> _. True) A (a2t_states ctxt \<omega>))"
  using assms(2-)
proof (induction A arbitrary:\<omega>)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      apply (clarsimp)
      apply (drule red_inhale_ok_PureE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
      apply (clarsimp)
      by (simp add: red_pure_assert_elim Stable_up_close_core_eq red_inhale_set_PureI assms(1))
  next
    case (Acc e f ep)
    show ?thesis
    proof (cases ep)
      case (PureExp ep)
      from this Atomic Acc show ?thesis
        apply (clarsimp)
        apply (drule red_inhale_ok_AccPureE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
        subgoal for ty r p
          apply (rule)
          subgoal
            apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (rule Stable_ex)+
            apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq assms(1) split:bool_to_assertion_splits)
            by (rule Stable_star; simp)
          apply (clarsimp)
          subgoal for \<omega>' \<omega>\<^sub>t'
            apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum assms(1) split:bool_to_assertion_splits)
            apply (simp add:red_inhale_set_AccPureI)
            apply (safe; simp add:acc_def add_set_ex_comm_r split:bool_to_assertion_splits)
            subgoal (* p = 0*)
              apply (simp add:inhale_perm_single_def norm_preal padd_pnone zero_preal_def[symmetric] Bex_def get_vm_bound)
              by (rule exI[of _ "\<omega>\<^sub>t'"]; simp)
            apply (simp add:inhale_perm_single_def)
            apply (drule acc_heap_loc_starE)
            apply (clarsimp simp add:norm_preal Bex_def)
            apply (rule exI[of _ "\<omega>\<^sub>t'\<lparr>get_total_full := get_total_full \<omega>\<^sub>t'
                \<lparr>get_mh_total := (get_vm (get_state \<omega>))
                   ((the_address r, f) := get_vm (get_state \<omega>) (the_address r, f))\<rparr>\<rparr>"])
            apply (simp) apply (safe)
            subgoal for v
              apply (rule a2t_statesI_direct)
              subgoal
                apply (simp add:compatible_partial_functions_singleton defined_val)
                apply (rule full_state_ext; simp add:get_trace_a2t_states[symmetric])
                apply (rule virtual_state_ext; simp add:t2a_state_get_state Fun.fun_upd_comp)
                apply (frule get_hh_total_a2t_states_alt; clarsimp)
                apply (rule ext) subgoal for hl'
                  by (auto simp add:restrict_map_def dest:vstate_wf_Some)
                done
              subgoal
                apply (simp add:a2t_extend_ok_def abs_state_typing_def)
                by (rule partial_heap_typing_insert; simp add:assms(1))
              subgoal by (simp)
              done
            subgoal
              apply (rule full_total_state.equality; simp)
              apply (rule total_state.equality; simp)
              by (rule ext; clarsimp simp add:preal_to_real)
            done
          done
        done
    next
      case Wildcard
      from this Atomic Acc show ?thesis
        apply (clarsimp)
        apply (drule red_inhale_ok_AccWildcardE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
        subgoal for r ty
          apply (rule)
          subgoal
            apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (rule Stable_ex)+
            apply (clarsimp simp add: red_pure_assert_elim up_close_core_sum Stable_up_close_core_eq assms(1) split:bool_to_assertion_splits)
            by (rule Stable_star; simp)
          apply (clarsimp)
          subgoal for \<omega>' \<omega>\<^sub>t'
            apply (clarsimp simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
            apply (clarsimp simp add:red_pure_assert_elim up_close_core_sum assms(1) split:bool_to_assertion_splits)
            apply (simp add:red_inhale_set_AccWildcardI)
            apply (safe; clarsimp simp add:acc_def add_set_ex_comm_r split:bool_to_assertion_splits)
            apply (simp add:inhale_perm_single_def)
            apply (drule acc_heap_loc_starE)
            apply (clarsimp simp add:norm_preal Bex_def)
            subgoal for p v
            apply (rule exI[of _ "\<omega>\<^sub>t'\<lparr>get_total_full := get_total_full \<omega>\<^sub>t'
                \<lparr>get_mh_total := (get_vm (get_state \<omega>))
                   ((the_address r, f) := get_vm (get_state \<omega>) (the_address r, f))\<rparr>\<rparr>"])
            apply (simp) apply (safe)
            subgoal
              apply (rule a2t_statesI_direct)
              subgoal
                apply (simp add:compatible_partial_functions_singleton defined_val)
                apply (frule get_hh_total_a2t_states_alt; clarsimp)
                apply (rule full_state_ext; simp add:get_trace_a2t_states[symmetric])
                apply (rule virtual_state_ext; simp add:t2a_state_get_state Fun.fun_upd_comp)
                apply (rule ext) subgoal for hl'
                  by (auto simp add:restrict_map_def dest:vstate_wf_Some)
                done
              subgoal
                apply (simp add:a2t_extend_ok_def abs_state_typing_def)
                by (rule partial_heap_typing_insert; simp add:assms(1))
              subgoal by (simp)
              done
            subgoal
              apply (rule exI[of _ "Abs_preal p"]; simp add:preal_to_real)
              apply (rule full_total_state.equality; simp)
              apply (rule total_state.equality; simp)
              by (rule ext; clarsimp simp add:preal_to_real)
            done
          done
        done
      done
    qed
  next
    case (AccPredicate P es ep)
    from Atomic this show ?thesis by (simp)
  qed
next
  case (Imp e A)
  from Imp.prems show ?case
    apply (clarsimp)
    apply (drule red_inhale_ok_ImpE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
    apply (clarsimp simp add:add_set_ex_comm_r)
    apply (rule)
    subgoal for b
      apply (rule Stable_ex)
      apply (simp only: add_set_asso[symmetric] red_pure_assert_elim ctxt_to_interp_funs assms(1))
      apply (case_tac "x = VBool b"; clarsimp simp add:up_close_core_sum Stable_up_close_core_eq)
      apply (insert Imp.IH[of \<omega>])
      by (simp add:assertion_typing_simps assms(1))
    apply (clarsimp)
    subgoal for b \<omega>' \<omega>\<^sub>t' x
      apply (simp add:red_inhale_set_ImpI assms(1))
      apply (simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum  assms(1))
      apply (case_tac "x = VBool b"; clarsimp)
      apply (case_tac "b"; simp)
      apply (insert Imp.IH[of \<omega>])
      by (auto simp add:assertion_typing_simps assms(1))
    done
next
  case (CondAssert e A1 A2)
  from CondAssert.prems show ?case
    apply (clarsimp)
    apply (drule red_inhale_ok_CondAssertE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
    apply (clarsimp simp add:add_set_ex_comm_r)
    apply (rule)
    subgoal for b
      apply (rule Stable_ex)
      apply (simp only: add_set_asso[symmetric] red_pure_assert_elim ctxt_to_interp_funs assms(1))
      apply (case_tac "x = VBool b"; clarsimp simp add:up_close_core_sum Stable_up_close_core_eq)
      apply (insert CondAssert.IH[of \<omega>])
      by (simp add:assertion_typing_simps assms(1) split:if_splits)
    apply (clarsimp)
    subgoal for b \<omega>' \<omega>\<^sub>t' x
      apply (simp add:red_inhale_set_CondAssertI assms(1))
      apply (simp add: add_set_asso[symmetric] red_pure_assert_elim up_close_core_sum assms(1))
      apply (case_tac "x = VBool b"; clarsimp)
      apply (case_tac "b"; simp)
      apply (insert CondAssert.IH[of \<omega>])
      by (auto simp add:assertion_typing_simps assms(1))
    done
next
  case (ImpureAnd A1 A2)
  then show ?case by (simp)
next
  case (ImpureOr A1 A2)
  then show ?case by (simp)
next
  case (Star A1 A2)
  note calc = Star.prems
  then have "red_inhale_set_ok ctxt (\<lambda> _. True) A1 (a2t_states ctxt \<omega>)"
      "red_inhale_set_ok ctxt (\<lambda> _. True) A2 (red_inhale_set ctxt (\<lambda> _. True) A1 (a2t_states ctxt \<omega>))" using red_inhale_ok_StarE by blast+
  note calc = calc this
  then have "Stable ({\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A1\<rangle>))"
    using Star.IH(1)[of \<omega>] by (simp add:assertion_typing_simps)+
  note calc = calc this
  then have "\<And> \<omega>'. stable (\<down>\<omega>') \<Longrightarrow> (\<down>\<omega>') \<in> {\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A1\<rangle>) \<Longrightarrow> a2t_states ctxt (\<down>\<omega>') \<subseteq> red_inhale_set ctxt (\<lambda> _. True) A1 (a2t_states ctxt \<omega>)"
    using Star.IH(1)[of \<omega>] by (simp add:assertion_typing_simps)+
  note H\<omega>' = this[of "\<up>_", simplified abs_state_to_from_record]
  have Htyp: "\<And> \<omega>'. stable (\<omega>') \<Longrightarrow> (\<omega>') \<in> {\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A1\<rangle>) \<Longrightarrow> abs_state_typing ctxt \<Lambda> \<omega>'"
    apply (rule red_inhale_set_preserves_typing_a2t)
    using calc apply (simp)
    using calc apply (simp add:get_trace_in_star)
    by (rule H\<omega>'; assumption)
  have Hok: "\<And> \<omega>'. stable (\<omega>') \<Longrightarrow> (\<omega>') \<in> {\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A1\<rangle>) \<Longrightarrow> red_inhale_set_ok ctxt (\<lambda> _. True) A2 (a2t_states ctxt \<omega>')"
    apply (rule red_inhale_set_ok_mono)
     apply (rule H\<omega>'; assumption)
    using calc by (simp)
  from calc have "Stable ({\<omega>} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>Star A1 A2\<rangle>))"
    apply (simp)
    apply (subst add_set_asso[symmetric])
    apply (rule Stable_star_singleton, assumption)
    subgoal for \<omega>'
      apply (insert Star.IH(2)[of \<omega>'])
      apply (insert Htyp[of \<omega>'])
      apply (insert Hok[of \<omega>'])
      by (simp add:assertion_typing_simps get_trace_in_star)
    done
 note calc = calc this
  then show ?case
    apply (simp add:red_inhale_set_StarI)
    apply (rule, rule, rule) subgoal for \<omega>''
      apply (simp add: add_set_asso[symmetric])
      apply (erule star_to_singleton_stableE; assumption?)
      subgoal for \<omega>'
        apply (insert Star.IH(2)[of "\<omega>'"])
        apply (insert Htyp[of "\<omega>'"])
        apply (insert Hok[of "\<omega>'"])
        apply (simp add:assertion_typing_simps get_trace_in_star)
        using red_inhale_set_mono H\<omega>' by blast
      done
    done
next
  case (Wand A1 A2)
  then show ?case by (simp)
next
  case (ForAll x1a A)
  then show ?case by (simp)
next
  case (Exists x1a A)
  then show ?case by (simp)
qed

lemma rel_stable_assertion_make_semantic_assertionI :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "Stable ({\<omega>} \<otimes> \<langle>(ctxt_to_interp ctxt), declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A\<rangle>)"
  shows "rel_stable_assertion \<omega> (make_semantic_assertion (ctxt_to_interp ctxt) (declared_fields (program_total ctxt)) A)"
  using assms apply (simp add:rel_stable_assertion_def make_semantic_assertion_def)
  apply (subst well_typedly_singleton[symmetric]) apply (assumption)
  by (simp add:well_typedly_add_set Stable_well_typedly)

lemma red_inhale_is_stable :
  assumes "stable \<omega>"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "assertion_typing (program_total ctxt) \<Lambda> A"
  assumes "valid_a2t_assert A"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  shows "red_inhale_set_ok ctxt (\<lambda> _. True) A (a2t_states ctxt \<omega>) \<Longrightarrow>
         rel_stable_assertion \<omega> (make_semantic_assertion \<Delta> (declared_fields (program_total ctxt)) A)"
  using assms
  using rel_stable_assertion_make_semantic_assertionI red_inhale_refines
  by blast

lemma inhale_refines :
  assumes "assertion_typing (program_total ctxt) \<Lambda> A"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "red_inhale_set_ok ctxt (\<lambda> _. True) A (a2t_states ctxt \<omega>)"
  assumes "stable \<omega>'"
  assumes "\<omega>' \<in> {\<omega>} \<otimes> make_semantic_assertion \<Delta> (declared_fields (program_total ctxt)) A"
  assumes "\<omega>\<^sub>t' \<in> a2t_states ctxt \<omega>'"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert A"
  shows  "\<exists>\<omega>\<^sub>t. \<omega>\<^sub>t \<in> a2t_states ctxt \<omega> \<and> red_inhale ctxt (\<lambda> _. True) A \<omega>\<^sub>t (RNormal \<omega>\<^sub>t')"
  using assms
  apply (subgoal_tac "\<omega>' \<in> {\<omega>} \<otimes> \<langle>\<Delta>, (declared_fields (program_total ctxt))\<rangle> \<Turnstile> \<langle>A\<rangle>")
  prefer 2 using make_semantic_assertion_in_unfold add_set_mono apply (metis (no_types, opaque_lifting) subset_eq)
  using red_inhale_refines
  by (smt (verit, best) abs_state_to_from_record mem_Collect_eq red_inhale_set_def subset_eq)


subsection \<open>refinement of Exhale\<close>

lemma red_exhale_refines :
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "red_exhale_set_ok ctxt (\<lambda> _. True) (a2t_mask \<omega>) A (a2t_states ctxt \<omega>)"
  assumes "assertion_typing (program_total ctxt) \<Lambda> A"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_assert A"
  shows  "\<exists> \<omega>'. \<omega> \<in> ({\<down>\<omega>'} \<otimes> (\<langle>\<Delta>, declared_fields (program_total ctxt)\<rangle> \<Turnstile> \<langle>A\<rangle>)) \<and> get_vh (get_state (\<down>\<omega>')) = get_vh (get_state \<omega>) \<and>
     a2t_states ctxt (\<down>\<omega>') \<subseteq> red_exhale_set ctxt (\<lambda> _. True) (a2t_mask \<omega>) A (a2t_states ctxt \<omega>)"
  using assms(2-)
proof (induction A arbitrary:\<omega>)
  case (Atomic a)
  show ?case
  proof (cases a)
    case (Pure e)
    from this Atomic show ?thesis
      apply (clarsimp)
      apply (drule red_exhale_ok_PureE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
      apply (clarsimp simp add:red_exhale_set_PureI)
      apply (rule exI[of _ "\<up>_"], safe; simp)
      apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
      by (rule red_pure_assert_intro; simp add:assms(1))
  next
    case (Acc e f ep)
    show ?thesis
    proof (cases ep)
      case (PureExp ep)
      from this Atomic Acc show ?thesis
        apply (clarsimp)
        apply (drule red_exhale_ok_AccPureE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
        subgoal for r ty p
          apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
          apply (cases r; simp)
          subgoal for a
            apply (cases "p = 0")
            subgoal
              apply (rule exI[of _ "\<up>_"], safe)
                apply (rule exI, rule exI, rule exI, rule exI)
                apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
                apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
                apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
                apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
                apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
                apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
                apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
                apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
                apply (rule bool_to_assertion_intro) apply (simp)
                apply (rule bool_to_assertion_intro) apply (simp)
                apply (simp add:acc_def)+
              by (rule red_exhale_set_AccPureI; assumption?; simp)
            apply (rule exI[of _ "\<up>_"], safe)
              apply (rule exI, rule exI, rule exI, rule exI)
              apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
              apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
              apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
              apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
              apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
              apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (simp add:acc_def add_set_ex_comm_r)
              apply (rule exI)
              apply (simp add:add_set_asso[symmetric])
              apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
              apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (cut_tac vstate_wf_Some[of "get_state \<omega>" "(a, f)"]) prefer 2 apply (smt (verit, best) eq_pnone_not_ppos leD not_gr_0 positive_real_preal)
              apply (clarsimp)
              apply (rule acc_heap_loc_starI)
                     apply (simp)
                    apply (simp)
                  apply (simp)
                 apply (simp)
            subgoal apply (clarsimp simp add:assms(1) abs_state_typing_def) by (rule partial_heap_typing_elim; assumption?; simp)
             apply (simp)
            by (rule red_exhale_set_AccPureI; assumption?; simp)
          subgoal
            apply (rule exI[of _ "\<up>_"], safe)
              apply (rule exI, rule exI, rule exI, rule exI)
              apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
              apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
              apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
              apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>ep\<rangle> [\<Down>] _"])
              apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
              apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
              apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (rule bool_to_assertion_intro) apply (simp)
              apply (simp add:acc_def)
               apply (simp)+
            by (rule red_exhale_set_AccPureI; assumption?; simp)
          done
        done
    next
      case Wildcard
      from this Atomic Acc show ?thesis
        apply (clarsimp)
        apply (drule red_exhale_ok_AccWildcardE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
        apply (clarsimp simp add:assertion_typing_simps atomic_assertion_typing_simps)
        subgoal for r ty
          apply (simp add:add_set_ex_comm_r add_set_ex_comm_l add_set_asso[symmetric])
          apply (rule exI[of _ "\<up>_"], safe)
            apply (rule exI, rule exI, rule exI)
            apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
            apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
            apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp add:assms(1)\<close>)
            apply (simp add:add_set_commm[of _ "\<llangle>_\<rrangle>"])
            apply (simp add:add_set_asso[of "\<llangle>_\<rrangle>"])
            apply (rule bool_to_assertion_intro) apply (simp)
            apply (rule bool_to_assertion_intro) apply (simp)
            apply (simp add:acc_def add_set_ex_comm_r)
            apply (rule exI[of _ "Rep_preal (epsilon_preal (get_vm (get_state \<omega>) (the_address r, f)))"])
            apply (cut_tac vstate_wf_Some[of "get_state \<omega>" "(the_address r, f)"])
             prefer 2 apply (smt (verit, best) eq_pnone_not_ppos leD not_gr_0 positive_real_preal)
            apply (clarsimp)
            apply (rule acc_heap_loc_starI)
                using epsilon_preal_bounds preal_to_real apply fastforce
               using epsilon_preal_bounds preal_to_real apply (metis order_less_le)
              apply (simp)
             apply (simp)
            subgoal apply (clarsimp simp add:assms(1) abs_state_typing_def) by (rule partial_heap_typing_elim; assumption?; simp)
             apply (simp)
            apply (simp add:Rep_preal_inverse)
            by (rule red_exhale_set_AccWildcardI; simp)
          done
    qed
  next
    case (AccPredicate P es ep)
    from Atomic this show ?thesis by (simp)
  qed
next
  case (Imp e A)
  from Imp.prems assms(1) show ?case
    apply (clarsimp)
    apply (drule red_exhale_ok_ImpE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
    apply (clarsimp simp add:red_exhale_set_ImpI)
    apply (case_tac "b"; simp)
    subgoal
      apply (cut_tac Imp.IH[of \<omega>]; clarsimp simp add:assertion_typing_simps)
      apply (rule exI[of _ "\<up>_"])
      apply (simp add:add_set_ex_comm_r add_set_asso[symmetric])
      apply (rule)
       apply (rule exI[of _ "VBool True"]; simp)
       apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
       apply (assumption)
      by (auto)
    subgoal
      apply (rule exI[of _ "\<up>_"])
      apply (simp add:add_set_ex_comm_r add_set_asso[symmetric])
      apply (rule)
       apply (rule exI[of _ "VBool False"]; simp)
       apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
       apply (simp)
      by (auto)
    done
next
  case (CondAssert e A1 A2)
  from CondAssert.prems assms(1) show ?case
    apply (clarsimp)
    apply (drule red_exhale_ok_CondAssertE[where ?\<Delta>=\<Delta>]; assumption?; simp?)
    apply (clarsimp simp add:red_exhale_set_CondAssertI)
    apply (case_tac "b"; simp)
    subgoal
      apply (cut_tac CondAssert.IH(1)[of \<omega>]; clarsimp simp add:assertion_typing_simps)
      apply (rule exI[of _ "\<up>_"])
      apply (simp add:add_set_ex_comm_r add_set_asso[symmetric])
      apply (rule)
       apply (rule exI[of _ "VBool True"]; simp)
       apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
       apply (assumption)
      by (auto)
    subgoal
      apply (cut_tac CondAssert.IH(2)[of \<omega>]; clarsimp simp add:assertion_typing_simps)
      apply (rule exI[of _ "\<up>_"])
      apply (simp add:add_set_ex_comm_r add_set_asso[symmetric])
      apply (rule)
       apply (rule exI[of _ "VBool False"]; simp)
       apply (simp add:add_set_commm[of _ "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (simp add:add_set_asso[of "_ \<turnstile> \<langle>e\<rangle> [\<Down>] _"])
       apply (rule red_pure_assert_intro) apply (assumption) apply (solves \<open>simp\<close>)
       apply (assumption)
      by (auto)
    done
next
  case (ImpureAnd A1 A2)
  then show ?case by (simp)
next
  case (ImpureOr A1 A2)
  then show ?case by (simp)
next
  case (Star A1 A2)
  from Star.prems Star.IH(1)[of \<omega>] show ?case
    apply (simp)
    apply (drule red_exhale_ok_StarE)
    apply (clarsimp simp add:assertion_typing_simps) subgoal for \<omega>''
      apply (cut_tac Star.IH(2)[of "\<down>\<omega>''"]; (simp add:get_trace_in_star)?) defer 1
      subgoal by (rule red_exhale_set_preserves_typing_a2t; simp)
      subgoal by (rule red_exhale_set_ok_mono; simp)
      apply (clarsimp) subgoal for \<omega>'
      apply (rule exI[of _ "\<omega>'"]; simp; rule conjI)
        subgoal
          apply (subst add_set_commm[of "\<langle>_,_\<rangle> \<Turnstile> \<langle>A1\<rangle>"])
          apply (simp add:add_set_asso[symmetric])
          by (rule star_to_singletonI; assumption)
        apply (simp add:red_exhale_set_StarI)
        using red_exhale_set_mono by blast
      done
    done
next
  case (Wand A1 A2)
  then show ?case by (simp)
next
  case (ForAll x1a A)
  then show ?case by (simp)
next
  case (Exists x1a A)
  then show ?case by (simp)
qed

subsection \<open>Refinement proof\<close>

(* What is this construction and what should it be called? vimage_set *)
definition vimage_set :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'b set"    (infixr "-`\<^sub>s" 90)
  where "f -`\<^sub>s A = f -` Pow A"

lemma vimage_set_in [simp]:
  "x \<in> f -`\<^sub>s A \<longleftrightarrow> f x \<subseteq> A"
  by (simp add: vimage_set_def)

lemma vimage_set_mono:
  assumes "A \<subseteq> B"
  shows "f -`\<^sub>s A \<subseteq> f -`\<^sub>s B"
  using assms by (auto simp add: vimage_set_def)

lemma a2t_states_set_store :
  assumes "x \<in> a2t_states ctxt (set_store \<omega> st)"
  shows   "x \<in> get_store_total_update (\<lambda>_. st) ` a2t_states ctxt \<omega>"
  using assms
  apply (simp add:image_def Bex_def)
  apply (rule exI[of _ "x\<lparr>get_store_total := get_store \<omega>\<rparr>"]; simp)
  apply (rule a2t_statesI_direct; (simp add: a2t_extend_ok_def)?)
  unfolding a2t_states_def by (clarsimp simp add:abs_state_ext_iff t2a_state_def)

lemma a2t_states_set_value :
  assumes "x \<in> a2t_states ctxt (set_state \<omega> (set_value (get_state \<omega>) hl v))"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "declared_fields (program_total ctxt) (snd hl) = Some ty"
  assumes "has_type (absval_interp_total ctxt) ty v"
  assumes "ppos (get_vm (get_state \<omega>) hl)"
  shows "x \<in> (\<lambda> \<omega>. \<omega>\<lparr>get_total_full := (get_total_full \<omega>)\<lparr>get_hh_total := (get_hh_total (get_total_full \<omega>))(hl := v) \<rparr> \<rparr>) `
          a2t_states ctxt \<omega>"
proof -
  obtain v' where "get_vh (get_state \<omega>) hl = Some v'"
    by (meson assms(6) gr_0_is_ppos option.exhaust_sel vstate_wf_imp)
  from this assms show ?thesis
  apply (simp add:image_def Bex_def)
  apply (rule exI[of _ "x\<lparr>get_total_full := (get_total_full x)\<lparr>get_hh_total :=
       (get_hh_total (get_total_full x))(hl := v')\<rparr>\<rparr>"])
    apply (clarsimp simp add:a2t_extend_ok_def abs_state_ext_iff get_trace_a2t_states[symmetric])
    apply (rule)
    subgoal
      apply (rule a2t_statesI_direct_stable; simp?)
      subgoal
        apply (rule full_state_ext; simp add:get_trace_a2t_states[symmetric] t2a_state_get_state)
        apply (rule virtual_state_ext; simp?)
        apply (simp add:vstate_stabilize_structure(2) restrict_map_def)
        apply (rule ext; auto)
        using  vstate_wf_Some apply fastforce
        using stable_get_state stable_virtual_state_def by blast
      subgoal
        apply (clarsimp simp add:a2t_extend_ok_def abs_state_typing_def)
        apply (rule heap_typing_insert; simp?)
         apply (rule partial_heap_typing_insert; simp?)
        by (rule partial_heap_typing_elim; assumption)
      done
    subgoal
      apply (rule full_total_state.equality; simp)
      apply (rule total_state.equality; simp)
      by (rule ext; simp)
    done
qed

lemma havoc_locs_state_a2t :
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  shows "a2t_states ctxt (stabilize \<omega>) \<subseteq> Set.bind (a2t_states ctxt \<omega>) (\<lambda> \<omega>_exh.
         havoc_locs_state ctxt \<omega>_exh
                  {loc. loc \<in> dom (get_vh (get_state \<omega>)) \<and> \<not> ppos (get_mh_total (get_total_full \<omega>_exh) loc)})" (is "_ \<subseteq> ?P")
proof (rule subsetI)
  fix \<omega>\<^sub>t assume H\<omega>\<^sub>t : "\<omega>\<^sub>t \<in> a2t_states ctxt (stabilize \<omega>)"
  have Hty : "heap_typing ctxt (get_hh_total (get_total_full \<omega>\<^sub>t))"
    using assms H\<omega>\<^sub>t by (simp add: abs_state_typing_def partial_heap_typing_stabilize)
  have "\<omega>\<^sub>t\<lparr>get_total_full := get_total_full \<omega>\<^sub>t\<lparr>get_hh_total :=
      (\<lambda> hl. (case get_vh (get_state \<omega>) hl of Some x \<Rightarrow> x | _ \<Rightarrow> get_hh_total (get_total_full \<omega>\<^sub>t) hl)) \<rparr>\<rparr> \<in> a2t_states ctxt \<omega>"
    apply (rule a2t_statesI[OF assms(1)])
    subgoal using assms Hty apply (clarsimp simp add:heap_typing_def abs_state_typing_def ValueAndBasicState.well_typed_heap_def)
      apply (case_tac "get_vh (get_state \<omega>) (a, b)"; simp)
      by fastforce
    subgoal using assms H\<omega>\<^sub>t by (simp add:abs_state_typing_def)
    subgoal using H\<omega>\<^sub>t by (simp)
    subgoal using H\<omega>\<^sub>t by (simp add:get_trace_a2t_states[symmetric])
    subgoal using H\<omega>\<^sub>t by (simp)
    subgoal using H\<omega>\<^sub>t by (simp)
    done
  from this H\<omega>\<^sub>t Hty assms show "\<omega>\<^sub>t \<in> ?P"
    apply (clarsimp simp add:havoc_locs_state_def havoc_locs_heap_def Bex_def)
    apply (rule exI, safe, assumption)
    apply (simp)
    apply (rule exI[of _ "get_hh_total (get_total_full \<omega>\<^sub>t)"])
    apply (simp add:heap_typing_total_heap_well_typed)
    apply (safe_step)
    apply (safe_step)
    apply (safe_step)
    apply (case_tac "get_vh (get_state \<omega>) (a, b)"; simp)
    apply (rule get_hh_total_lookup_a2t_states, assumption)
    apply (simp add:vstate_stabilize_structure(2) restrict_map_eq_Some)
    by fastforce
qed

theorem abstract_refines_total :
  assumes "R = (\<lambda> _. True)"
  (* TODO: substitute ctxt_to_interp ctxt for \<Delta> in this file instead of using this equality *)
  assumes "\<Delta> = ctxt_to_interp ctxt"
  assumes "red_stmt_total_set_ok ctxt R \<Lambda> C (a2t_states ctxt \<omega>)"
  assumes "stmt_typing (program_total ctxt) \<Lambda> C"
  assumes "abs_state_typing ctxt \<Lambda> \<omega>"
  assumes "stable \<omega>"
  assumes "a2t_state_wf ctxt (get_trace \<omega>)"
  assumes "valid_a2t_stmt C"
  \<comment>\<open>We don't need store_typing in the post condition because red_stmt_total preserves store-typing\<close>
  shows "concrete_red_stmt_post (t2a_ctxt ctxt \<Lambda>) (compile \<Delta> (declared_fields (program_total ctxt)) C) \<omega>
       (a2t_states ctxt -`\<^sub>s (red_stmt_total_set ctxt R \<Lambda> C (a2t_states ctxt \<omega>)))"
  \<comment>\<open>We could also use ` instead of `\<forall>, which would be a weaker (easier to prove) statement for most cases, but for
     sequential composition, it requires showing that red_stmt_total creates a set that is closed under
     a2t_states \<circ> t2a_state\<close>
  using assms(3-)
proof (induction C arbitrary: \<Lambda> \<omega> rule:stmt.induct)
  case (Inhale A)
  from this assms(1-2) show ?case
    apply (simp add:stmt_typing_simps)
    apply (drule red_stmt_total_ok_InhaleE)
    apply (rule concrete_post_Inhale; simp?)
     apply (rule red_inhale_is_stable; assumption?; simp?; rule a2t_state_in_a2t_states)
    apply (clarsimp simp add:red_stmt_total_set_InhaleI)
    using inhale_refines by metis
next
  case (Exhale A)
  from this assms(1) show ?case
    apply (simp add:stmt_typing_simps)
    apply (drule red_stmt_total_ok_ExhaleE; simp?)
    apply (cut_tac red_exhale_refines[where ?\<omega>=\<omega> and ?\<Delta>=\<Delta>]; (simp add:assms(2))?)
    apply (clarsimp)
    subgoal for \<omega>'
      apply (rule concrete_post_Exhale[where ?\<omega>'="\<down>\<omega>'"])
        apply (assumption)
      subgoal
        apply (clarsimp simp add:make_semantic_assertion_def)
        using well_typedly_add_set_l in_well_typedly by blast
      apply (simp add:red_stmt_total_set_ExhaleI)
      apply (insert havoc_locs_state_a2t[of ctxt \<Lambda> "\<down>\<omega>'"])
      apply (drule red_exhale_set_preserves_typing_a2t; assumption?; (simp add:get_trace_in_star)?)
      apply (insert stable_dom_get_vh_eq_get_vm[of "get_state \<omega>"])
       apply (clarsimp simp add:stable_get_state eq_pnone_not_ppos)
      by force
    done
next case (Assert x)
  from this assms(1) show ?case
    apply (simp add:stmt_typing_simps)
    done
(*
    apply (drule red_stmt_total_ok_AssertE; simp?)
    apply (cut_tac red_exhale_refines[where ?\<omega>=\<omega> and ?\<Delta>=\<Delta>]; (simp add:assms(2))?)
    apply (clarsimp)
    subgoal for \<omega>'
      apply (rule concrete_post_Assert)
      subgoal sorry
      apply (simp add:red_stmt_total_set_AssertI)

      unfolding red_exhale_set_def
      apply (clarsimp)
    by (simp)
*)
next case (Assume x) then show ?case by (simp)
next
  case (If e C1 C2)
  note calc = If
  from calc have "stmt_typing (program_total ctxt) \<Lambda> C1" by (clarsimp simp add:stmt_typing_simps)
  note calc = calc this
  from calc have "stmt_typing (program_total ctxt) \<Lambda> C2" by (clarsimp simp add:stmt_typing_simps)
  note calc = calc this
  from calc obtain b where "(\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool b)) \<and> red_stmt_total_set_ok ctxt R \<Lambda> (if b then C1 else C2) (a2t_states ctxt \<omega>)"
    using red_stmt_total_ok_IfE assms(2) by blast
  note calc = calc this
  show ?case
    apply (simp)
  proof (rule concrete_post_If)
    from calc show "make_semantic_bexp \<Delta> e \<omega> = Some b" by (simp; blast)
  next
    show "concrete_red_stmt_post (t2a_ctxt ctxt \<Lambda>) (if b then compile \<Delta> (declared_fields (program_total ctxt)) C1 else compile \<Delta> (declared_fields (program_total ctxt)) C2) \<omega>
        (a2t_states ctxt -`\<^sub>s red_stmt_total_set ctxt R \<Lambda> (stmt.If e C1 C2) (a2t_states ctxt \<omega>))"
(* Why does presburger solve this and non of the other solvers? *)
      using calc apply (clarsimp)
      using calc red_stmt_total_set_IfI[where ?b="b" and ?\<Delta>="\<Delta>", OF _ _ _ assms(2)] by (presburger)
  qed
next
  case (Seq C1 C2)
  note calc = Seq
  hence "stmt_typing (program_total ctxt) \<Lambda> C1" by (clarsimp simp add:stmt_typing_simps)
  note calc = calc this
  hence "stmt_typing (program_total ctxt) \<Lambda> C2" by (clarsimp simp add:stmt_typing_simps)
  note calc = calc this red_stmt_total_ok_SeqE[OF Seq.prems(1)]
  show ?case
    apply (simp)
    apply (rule concrete_post_Seq)
    apply (rule concrete_red_stmt_post_stable_wf) using calc apply (solves \<open>simp\<close>) using calc apply (solves \<open>simp\<close>)
  proof (rule concrete_red_stmt_post_impl)
    show "concrete_red_stmt_post (t2a_ctxt ctxt \<Lambda>) (compile \<Delta> (declared_fields (program_total ctxt)) C1) \<omega>
       (a2t_states ctxt -`\<^sub>s red_stmt_total_set ctxt R \<Lambda> C1 (a2t_states ctxt \<omega>))"
      using calc by simp
  next
    show "a2t_states ctxt -`\<^sub>s red_stmt_total_set ctxt R \<Lambda> C1 (a2t_states ctxt \<omega>) \<subseteq> {\<omega>''.
        sep_algebra_class.stable \<omega>'' \<longrightarrow> a2t_state_wf ctxt (get_trace \<omega>'') \<longrightarrow> \<omega>'' \<in> {\<omega>''.
        concrete_red_stmt_post (t2a_ctxt ctxt \<Lambda>) (compile \<Delta> (declared_fields (program_total ctxt)) C2) \<omega>''
         (a2t_states ctxt -`\<^sub>s red_stmt_total_set ctxt R \<Lambda> (stmt.Seq C1 C2) (a2t_states ctxt \<omega>))}}"
      apply (rule subsetI)
      subgoal for \<omega>'
      apply (clarsimp)
      apply (rule concrete_red_stmt_post_impl)
       apply (rule Seq.IH(2))
      using calc red_stmt_total_set_ok_mono apply (blast)
      using calc apply (blast)
      using calc apply (clarsimp) using calc red_stmt_total_set_preserves_typing_a2t apply metis
        apply (simp)
      using calc apply (simp)
      using calc apply (simp)
      apply (simp add:red_stmt_total_set_SeqI)
      by (rule vimage_set_mono, rule red_stmt_total_set_mono, assumption)
    done
  qed
next
  case (LocalAssign x e)
  note calc = LocalAssign
  then show ?case
    apply (simp)
    apply (drule red_stmt_total_ok_LocalAssignE[where \<Delta>="\<Delta>"]; clarsimp)
    apply (rule concrete_post_LocalAssign; clarsimp?)
       apply (rule)
      apply (assumption)
     apply (simp)
    apply (clarsimp simp add:red_stmt_total_set_LocalAssignI[where \<Delta>="\<Delta>"] assms(2))
    (* The state here would have xa in the goal if we use the different formulation. *)
    apply (drule a2t_states_set_store)
    (* apply (rule exI, rule conjI, assumption) *)
    (* apply (rule exI, rule conjI, assumption) *)
    (* apply (rule conjI, rule) *)
    apply (auto simp add:a2t_states_in_stable has_type_get_type)
    done
next
  case (FieldAssign e1 f e2)
  note calc = FieldAssign
  then show ?case
    apply (simp)
    apply (drule red_stmt_total_ok_FieldAssignE[where \<Delta>="\<Delta>"]; clarsimp)
    apply (rule concrete_post_FieldAssign; clarsimp?)
         apply (blast)
        apply (assumption)
       apply (simp add:has_write_perm_only_def)
      apply (auto)[1]
     apply (clarsimp)
    apply (clarsimp simp add:red_stmt_total_set_FieldAssignI[where \<Delta>="\<Delta>"] assms(2))
    apply (drule a2t_states_set_value)
    by (auto)
next
  case (Havoc x)
  note calc = Havoc
  then obtain ty where "\<Lambda> x = Some ty" by (auto simp add:stmt_typing_simps)
  note calc = calc this
  then show ?case
    apply (simp)
    apply (rule concrete_post_Havoc; clarsimp?)
     apply (blast)
    apply (clarsimp simp add:red_stmt_total_set_HavocI)
    apply (drule a2t_states_set_store)
    by (auto simp add:a2t_states_in_stable)
next
  case (MethodCall x1a x2a x3a)
  then show ?case by (simp)
next
  case (While x1a x2a C)
  then show ?case by (simp)
next
  case (Unfold x1a x2a x3a)
  then show ?case by (simp)
next
  case (Fold x1a x2a x3a)
  then show ?case by (simp)
next
  case (Package x1a x2a)
  then show ?case by (simp)
next
  case (Apply x1a x2a)
  then show ?case by (simp)
next
  case (Label x)
  then show ?case
    apply (clarsimp elim!:stmt_typing_elim)
    apply (rule concrete_post_Label)
    apply (clarsimp)
    apply (rule red_stmt_total_set_LabelI; simp)
    (* TODO: Adapt abstract semantics to match total semantics? enforce that labels are unique? *)
    sorry
next
  case (Scope x1a C)
  then show ?case by (simp)
next
  case Skip
  then show ?case
    apply (clarsimp elim!:stmt_typing_elim)
    apply (rule concrete_post_Skip)
    by (clarsimp simp add:red_stmt_total_set_def red_stmt_total_simps)
qed

end