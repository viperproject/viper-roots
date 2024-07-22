theory SymbolicExecDef
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState
     ViperCommon.Binop ViperCommon.PosPerm ViperCommon.PosReal
     EquiViper EquiSemAuxLemma
begin

section \<open>upstream\<close>
fun binop_result_to_option :: "'a binop_result \<Rightarrow> 'a option" where
  "binop_result_to_option (BinopNormal x) = Some x"
| "binop_result_to_option _ = None"

lemma binop_result_to_option_eq_Some [simp]:
   "binop_result_to_option r = Some va \<longleftrightarrow> r = BinopNormal va"
  by (cases r; simp)

fun binop_lazy_bool :: "binop \<Rightarrow> (bool \<times> bool) option" where
  "binop_lazy_bool Or = Some (True, True)"
| "binop_lazy_bool And = Some (False, False)"
| "binop_lazy_bool BImp = Some (False, True)"
| "binop_lazy_bool _ = None"

lemma eval_binop_lazy_binop_lazy_bool :
  assumes "binop_lazy_bool op = Some r"
  shows "eval_binop_lazy (VBool b) op = Some x \<longleftrightarrow> b = fst r \<and> x = VBool (snd r)"
  using assms by (cases op; cases "b"; auto)

lemma eval_bool_binop_lazy_bool :
  assumes "binop_lazy_bool op = Some r"
  assumes "b1 \<noteq> fst r"
  shows "eval_bool_bool b1 op b2 = BinopNormal x \<longleftrightarrow> x = VBool b2"
  using assms by (cases op; cases "b1"; auto)

(* Remove? *)
definition map_agree :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" where
"map_agree m1 m2 = (\<forall> i a b. m1 i = Some a \<longrightarrow> m2 i = Some b \<longrightarrow> a = b)"


lemma plus_assoc3 :
  assumes "Some abc = ab \<oplus> c"
  assumes "Some ab = a \<oplus> b"
  shows "\<exists>ac. Some ac = a \<oplus> c \<and> Some abc = ac \<oplus> b"
  using assms
  apply (cases "a \<oplus> c")
   apply (metis asso1 asso2 commutative)
  by (metis asso1 commutative)


lemma greater_mono_l:
  assumes "Some h2 = h1 \<oplus> h"
  assumes "h1 \<succeq> h0"
  shows "h2 \<succeq> h0"
  using assms commutative by (metis greater_equiv succ_trans)

lemma binop_lazy_bool_binop_type :
  assumes "binop_lazy_bool op = Some res"
  shows "binop_type op ty1 ty2 ty \<longleftrightarrow> ty1 = TBool \<and> ty2 = TBool \<and> ty = TBool"
  using assms by (cases op; simp add:binop_type.simps)

lemma eval_binop_And_eq_True :
  "eval_binop v1 And v2 = BinopNormal (VBool True) \<longleftrightarrow> v1 = VBool True \<and> v2 = VBool True"
  by (cases v1; cases v2; auto)

lemma eval_binop_Eq_eq_True :
  "eval_binop v1 Eq v2 = BinopNormal (VBool True) \<longleftrightarrow> v1 = v2"
  by (cases v1; cases v2; auto)

lemma eval_binop_Lt_perm_l_eq_True :
  "eval_binop (VPerm p) Lt v = BinopNormal (VBool True) \<longleftrightarrow> (\<exists> p2. v = VPerm p2 \<and> p < p2)"
  by (cases v; auto)

lemma eval_binop_Lt_perm_r_eq_True :
  "eval_binop v1 Lt (VPerm p) = BinopNormal (VBool True) \<longleftrightarrow> (\<exists> p1. v1 = VPerm p1 \<and> p1 < p)"
  by (cases v1; auto)

lemma eval_binop_Lte_perm_r_eq_True :
  "eval_binop v1 Lte (VPerm p) = BinopNormal (VBool True) \<longleftrightarrow> (\<exists> p1. v1 = VPerm p1 \<and> p1 \<le> p)"
  by (cases v1; auto)

section \<open>def\<close>
(*
look into https://arxiv.org/pdf/2311.07559
look into http://malte.schwerhoff.de/docs/phd_thesis.pdf
look at featherweight verifast

idea: 
- use the symbolic execution from gradual viper paper
- add permissions and wildcards, inhale statements (just not part of their syntax)
- remove predicates
- define it as a relation in Isabelle
  - can be executed in the prover with simp
  - can leave decision procedures open/parametric/semantic
  - can have a semantic state consolidation algorithm 
      (the gradual viper paper does not have one since they only have 1 or 0 permission, so their heap chunks are disjoint)

notes on symbolic execution from gradual viper paper:
- I don't understand how exactly their formalization of symbolic execution works. I thought that the
  symbolic execution would construct a derivation of their rules and one would prove that if one has
  such a derivation, then the program is safe or so. But their non-determinism is the wrong way around
  for that. In particular, branching on conditionals is handled with non-deterministic rules, so if
  the symbolic execution could pick the non-determinism it could determine the branching of conditionals
  which does not make sense. Instead it seems like they construct a derivation of their symbolic execution
  rules in their soundness proof.
- On trick to make this work is that they complete their derivation with failure steps like SConsumeAccFailure, which
  allows them to prove e.g. lemma 46. In their case, verification failure is denoted by always failing runtime checks (see 3.3)
- I am not sure if one can extend their setup to permissions since in this case the symbolic execution would need to
  handle all possible ways how a permission can be removed from the heap. Also already for the case where
  heap fragments are non-disjoint, their setup becomes weird (they mention that they prove disjointness of heap fragments).
- I am not sure if one can extend their setting to cases where one wants to give more flexibility to the symbolic execution.
  In particular, we might want to allow an arbitrary state consolidation algorithm. But this would need a different
  kind of non-determinism than the non-determinism from branching \<rightarrow> dual non-det to the rescue!

plan for function:
- add symbolic values to expressions to get symbolic expressions? Or hijack var constructor for symbolic values?
- state: 
  + path condition: boolean valued symbolic expression
  + store: maps vars to symbolic expressions
  + heap: 
    * permissions: map from heap locations to symbolic expressions representing permissions
    * heap: total (?) map from heap locations to symbolic expressions
  + trace: Ignore?
  + counter for generating fresh names for new symbolic expressions

questions:
- how to handle havocing of the heap when one does not have permission anymore?

type: recursive function that takes a program and a state and generates a new state and a list of sideconditions
 *)


subsection \<open>basic definitions\<close>

definition def_domains :: "'a \<Rightarrow> abs_type" where
"def_domains = undefined"

(* C of https://arxiv.org/pdf/2311.07559 *)
subsection \<open>symbolic expressions\<close>
type_synonym sym_val = var
type_synonym 'a valuation = "sym_val \<rightharpoonup> 'a val"

(* We define sym_exp semantically such that = is semantic equality (important for rewriting). *)
type_synonym 'a sym_exp = "'a valuation \<rightharpoonup> 'a val"

definition SLit :: "lit \<Rightarrow> 'a sym_exp" where
"SLit l _ = Some (val_of_lit l)"
abbreviation SBool where "SBool b \<equiv> SLit (LBool b)"
abbreviation SInt where "SInt n \<equiv> SLit (LInt n)"
abbreviation SPerm where "SPerm p \<equiv> SLit (LPerm p)"
abbreviation SNull where "SNull \<equiv> SLit (LNull)"

definition SVar :: "sym_val \<Rightarrow> 'a sym_exp" where
"SVar v V = V v"
definition SUnop :: "unop \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SUnop op t V = Option.bind (t V) (\<lambda> v. binop_result_to_option (eval_unop op v))"
abbreviation SNot ("\<not>\<^sub>s _" [40]40) where "SNot \<equiv> \<lambda> t1. SUnop Not t1"

lemma SNot_eq_Some :
  "SNot t V = Some v \<longleftrightarrow> (\<exists> b. t V = Some (VBool b) \<and> v = VBool (\<not> b))"
  apply (auto simp add:SUnop_def bind_eq_Some_conv) apply (rename_tac "b") by (case_tac "b"; simp)

definition SBinop :: "'a sym_exp \<Rightarrow> binop \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SBinop t1 op t2 V = Option.bind (t1 V) (\<lambda> v1. Option.bind (t2 V) (\<lambda> v2.
   binop_result_to_option (eval_binop v1 op v2)))"
abbreviation SAnd (infixr "\<and>\<^sub>s" 35) where "SAnd \<equiv> \<lambda> t1 t2. SBinop t1 And t2"
abbreviation SEq (infixl "=\<^sub>s" 50) where "SEq \<equiv> \<lambda> t1 t2. SBinop t1 Eq t2"
abbreviation SLt (infix "<\<^sub>s" 50) where "SLt \<equiv> \<lambda> t1 t2. SBinop t1 Lt t2"
abbreviation SLte (infix "\<le>\<^sub>s" 50) where "SLte \<equiv> \<lambda> t1 t2. SBinop t1 Lte t2"
abbreviation SImp (infixr "\<longrightarrow>\<^sub>s" 25) where "SImp \<equiv> \<lambda> t1 t2. SBinop t1 BImp t2"
abbreviation SSub (infixl "-\<^sub>s" 65) where "SSub \<equiv> \<lambda> t1 t2. SBinop t1 Sub t2"
abbreviation SPermDiv (infixl "/\<^sub>s" 70) where "SPermDiv \<equiv> \<lambda> t1 t2. SBinop t1 PermDiv t2"

lemma SBinop_eq_Some :
  "SBinop t1 op t2 V = Some v \<longleftrightarrow> (\<exists> v1 v2. t1 V = Some v1 \<and> t2 V = Some v2 \<and> eval_binop v1 op v2 = BinopNormal v)"
  by (auto simp add:SBinop_def bind_eq_Some_conv)

definition SHasType :: "vtyp \<Rightarrow> sym_val \<Rightarrow> 'a sym_exp" where
"SHasType ty v V = Option.bind (V v) (\<lambda> v'. if v' \<in> sem_vtyp def_domains ty then Some (VBool True) else None)"

lemma SHasType_eq_Some :
  "SHasType ty t V = Some b \<longleftrightarrow> (\<exists> v. V t = Some v \<and> v \<in> sem_vtyp def_domains ty \<and> b = VBool True)"
  by (auto simp add:SHasType_def bind_eq_Some_conv)

definition SBinopSafe :: "'a sym_exp \<Rightarrow> binop \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SBinopSafe t1 op t2 V = Option.bind (t1 V) (\<lambda> v1. Option.bind (t2 V) (\<lambda> v2. 
  if eval_binop v1 op v2 = BinopOpFailure then None else Some (VBool True)))"

lemma SBinopSafe_eq_Some :
  "SBinopSafe t1 op t2 V = Some b \<longleftrightarrow> (\<exists> v1 v2. t1 V = Some v1 \<and> t2 V = Some v2 \<and> eval_binop v1 op v2 \<noteq> BinopOpFailure \<and> b = VBool True)"
  by (auto simp add:SBinopSafe_def bind_eq_Some_conv)

definition sym_implies :: "'a sym_exp \<Rightarrow> 'a sym_exp \<Rightarrow> bool" ("_ \<turnstile>\<^sub>s _" 10) where
"sym_implies t1 t2 = (\<forall> V. t1 V = Some (VBool True) \<longrightarrow> t2 V = Some (VBool True))"

lemma sym_impliesI :
  assumes "\<And> V. t1 V = Some (VBool True) \<Longrightarrow> t2 V = Some (VBool True)"
  shows "sym_implies t1 t2"
  using assms by (simp add:sym_implies_def)

lemma sym_implies_conj :
  "(t \<turnstile>\<^sub>s t1 \<and>\<^sub>s t2) \<longleftrightarrow> (t \<turnstile>\<^sub>s t1) \<and> (t \<turnstile>\<^sub>s t2)"
  by (auto simp add:sym_implies_def SBinop_eq_Some eval_binop_And_eq_True)

subsection \<open>valuation agreement and independence\<close>

definition valu_agree :: "var \<Rightarrow> 'a valuation \<Rightarrow> 'a valuation \<Rightarrow> bool" where
"valu_agree v V1 V2 = (\<forall> v'. v' < v \<longrightarrow> V1 v' = V2 v')"

definition valu_indep :: "var \<Rightarrow> ('a valuation \<Rightarrow> 'b) \<Rightarrow> bool" where
"valu_indep v f = (\<forall> V1 V2. valu_agree v V1 V2 \<longrightarrow> f V1 = f V2)"

lemma valu_indep_pair :
  "valu_indep us (\<lambda> V. (a V, b V)) \<longleftrightarrow> valu_indep us a \<and> valu_indep us b"
  by (auto simp add:valu_indep_def)

lemma valu_indepE :
  assumes "valu_indep us f"
  assumes "valu_agree us V V'"
  shows "f V = f V'"
  using assms by (simp add:valu_indep_def)

lemma valu_indep_lt :
  assumes "valu_indep us1 f"
  assumes "us1 < us2"
  shows "valu_indep us2 f"
  using assms by (auto simp add:valu_indep_def valu_agree_def)

lemma valu_indep_SLit [simp] :
  "valu_indep us (SLit x)"
  by (simp add:valu_indep_def SLit_def)

lemma valu_indep_SVar [simp] :
  assumes "x < us"
  shows "valu_indep us (SVar x)"
  using assms by (auto simp add:valu_indep_def SVar_def valu_agree_def)

lemma valu_indep_SUnop [simp] :
  assumes "valu_indep us t"
  shows "valu_indep us (SUnop op t)"
  using assms by (auto simp add:valu_indep_def SUnop_def)

lemma valu_indep_SBinop [simp] :
  assumes "valu_indep us t1"
  assumes "valu_indep us t2"
  shows "valu_indep us (SBinop t1 op t2)"
  using assms by (auto simp add:valu_indep_def SBinop_def)

lemma valu_indep_SHasType [simp] :
  assumes "v < us"
  shows "valu_indep us (SHasType ty v)"
  using assms by (auto simp add:valu_indep_def SHasType_def valu_agree_def)

subsection \<open>symbolic states\<close>
type_synonym 'a sym_store = "var \<rightharpoonup> 'a sym_exp"
type_synonym 'a path_cond = "'a sym_exp"

record 'a chunk =
  chunk_field :: field_name
  chunk_recv :: "'a sym_exp"
  chunk_perm :: "'a sym_exp"
  chunk_val :: "'a sym_exp"

type_synonym 'a sym_heap = "'a chunk list"

subsection \<open>concrete heaps\<close>

definition concretize_chunk :: "'a chunk \<Rightarrow> 'a valuation \<Rightarrow> 'a virtual_state option" where
"concretize_chunk c V = 
  Option.bind (chunk_recv c V) (\<lambda> ve. 
    if \<not> is_VRef ve then None else
    if \<not> is_address (the_ref ve) then None else
  Option.bind (chunk_perm c V) (\<lambda> vp. 
    if \<not> is_VPerm vp then None else
    if un_VPerm vp < 0 then None else
    if un_VPerm vp > 1 then None else
  Option.bind (chunk_val c V) (\<lambda> vv. 
   Some (acc_virt (the_address (the_ref ve), chunk_field c) (Abs_preal (un_VPerm vp)) vv)
)))"

lemma concretize_chunk_eq_Some :
  "concretize_chunk c V = Some ch \<longleftrightarrow>
     (\<exists> a p v. chunk_recv c V = Some (VRef (Address a)) \<and>
       chunk_perm c V = Some (VPerm p) \<and>
       0 \<le> p \<and> p \<le> 1 \<and>
       chunk_val c V = Some v \<and>
       ch = acc_virt (a, chunk_field c) (Abs_preal p) v)"
  apply (simp add:concretize_chunk_def bind_eq_Some_conv)
  by (smt (verit, ccfv_SIG) is_VPerm_def is_VRef_def is_address_def ref.sel val.sel(3) val.sel(4))

fun concretize_heap :: "'a sym_heap \<Rightarrow> 'a valuation \<Rightarrow> 'a virtual_state option" where
  "concretize_heap [] V = Some uu"
| "concretize_heap (c#cs) V = 
    Option.bind (concretize_chunk c V) (\<lambda> cc. 
    Option.bind (concretize_heap cs V) (\<lambda> ch. ch \<oplus> cc))"

(* We don't want to reduce the cons case by default since instead we want to have the more controlled
  rule concretize_heap_cons_eq_Some, which e.g. orients the "Some ch = ch' \<oplus> cc" in the right way
  compared to used bind_eq_Some_conv. *)
declare concretize_heap.simps(2)[simp del]
lemmas concretize_heap_cons = concretize_heap.simps(2)
lemma concretize_heap_cons_eq_Some [simp] :
  "concretize_heap (c # cs) V = Some ch \<longleftrightarrow> (\<exists> cc ch'. concretize_chunk c V = Some cc \<and> concretize_heap cs V = Some ch' \<and> Some ch = ch' \<oplus> cc)"
  by (auto simp add:concretize_heap.simps(2) bind_eq_Some_conv)

lemma valu_agree_concretize_chunk :
  assumes "valu_agree us V V'"
  assumes "valu_indep us (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))"
  shows "concretize_chunk c V = concretize_chunk c V'"
  apply (insert assms) apply (drule valu_indepE; assumption?)
  unfolding concretize_chunk_def apply (simp) by presburger
  
lemma valu_agree_concretize_heap :
  assumes "valu_agree us V V'"
  assumes "\<forall>c. c \<in> set h \<longrightarrow> valu_indep us (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))"
  shows "concretize_heap h V = concretize_heap h V'"
  using assms
proof (induction h arbitrary:)
  case Nil then show ?case by (simp)
next 
  case (Cons c h) then show ?case apply (simp add:concretize_heap_cons) using valu_agree_concretize_chunk by fastforce
qed

subsection \<open>symbolic state\<close>

record 'a sym_state =
  sym_store :: "'a sym_store"
  sym_cond :: "'a path_cond"
  sym_heap :: "'a sym_heap"
  sym_used :: "nat"
  sym_store_type :: "var \<rightharpoonup> vtyp"
  sym_fields :: "field_name \<rightharpoonup> vtyp"

abbreviation sym_cond_add :: "'a sym_state \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_state" where
"sym_cond_add \<sigma> t \<equiv> \<sigma>\<lparr>sym_cond := t \<and>\<^sub>s sym_cond \<sigma>\<rparr>"

abbreviation sym_heap_add :: "'a sym_state \<Rightarrow> 'a chunk \<Rightarrow> 'a sym_state" where
"sym_heap_add \<sigma> c \<equiv> \<sigma>\<lparr>sym_heap := c # sym_heap \<sigma>\<rparr>"

definition sym_fresh :: "'a sym_state \<Rightarrow> sym_val" where
"sym_fresh \<sigma> = sym_used \<sigma>"
declare sym_fresh_def [simp]

definition sym_gen_fresh :: "'a sym_state \<Rightarrow> vtyp \<Rightarrow> ('a sym_state \<Rightarrow> sym_val \<Rightarrow> bool) \<Rightarrow> bool" where
"sym_gen_fresh \<sigma> ty Q = Q (sym_cond_add (\<sigma>\<lparr>sym_used := Suc (sym_used \<sigma>)\<rparr>) (SHasType ty (sym_fresh \<sigma>))) (sym_fresh \<sigma>)"

definition sym_consolidate :: "'a sym_state \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
"sym_consolidate \<sigma> Q = (\<forall> V ch.
   valu_indep (sym_used \<sigma>) (sym_cond \<sigma>) \<and> (\<forall>c. c \<in> set (sym_heap \<sigma>) \<longrightarrow> valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))) \<longrightarrow>
   sym_cond \<sigma> V = Some (VBool True) \<longrightarrow> concretize_heap (sym_heap \<sigma>) V = Some ch \<longrightarrow>
   (\<exists> g' h' ch'. valu_indep (sym_used \<sigma>) g' \<and> (\<forall>c. c \<in> set h' \<longrightarrow> valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))) \<and>
     g' V = Some (VBool True) \<and> concretize_heap h' V = Some ch' \<and> ch \<succeq> ch' \<and> Q (\<sigma>\<lparr> sym_cond := g', sym_heap := h' \<rparr>)))"

definition sym_heap_do_add :: "'a sym_state \<Rightarrow> 'a chunk \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
"sym_heap_do_add \<sigma> c Q = sym_consolidate (sym_heap_add \<sigma> c) Q"

definition sym_stabilize :: "'a sym_state \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
"sym_stabilize \<sigma> Q = sym_consolidate \<sigma> (\<lambda> \<sigma>'. 
   list_all (\<lambda> c. (sym_cond \<sigma>' \<turnstile>\<^sub>s SPerm 0 <\<^sub>s chunk_perm c)) (sym_heap \<sigma>') \<and> Q \<sigma>')"

definition sym_heap_extract :: "'a sym_state \<Rightarrow> 'a sym_exp \<Rightarrow> field_name \<Rightarrow> 'a sym_exp option \<Rightarrow> ('a sym_state \<Rightarrow> 'a chunk \<Rightarrow> bool) \<Rightarrow> bool" where
"sym_heap_extract \<sigma> te f p Q = sym_consolidate \<sigma> (\<lambda> \<sigma>'. \<exists> c cs. sym_heap \<sigma>' = c # cs \<and> chunk_field c = f \<and>
   (sym_cond \<sigma>' \<turnstile>\<^sub>s te =\<^sub>s chunk_recv c \<and>\<^sub>s 
    (case p of Some tp \<Rightarrow> SPerm 0 \<le>\<^sub>s tp \<and>\<^sub>s tp \<le>\<^sub>s chunk_perm c | None \<Rightarrow> SPerm 0 <\<^sub>s chunk_perm c)) \<and> Q (\<sigma>'\<lparr> sym_heap := cs \<rparr>) c)"


lemma sym_consolidateE :
  assumes "sym_consolidate \<sigma> Q"
  assumes "valu_indep (sym_used \<sigma>) (sym_cond \<sigma>)"
  assumes "(\<forall>c. c \<in> set (sym_heap \<sigma>) \<longrightarrow> valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V)))"
  assumes "sym_cond \<sigma> V = Some (VBool True)"
  assumes "concretize_heap (sym_heap \<sigma>) V = Some ch"
  assumes HP: "\<And> g' h' ch'.
    valu_indep (sym_used \<sigma>) g' \<Longrightarrow>
    (\<forall>c. c \<in> set h' \<longrightarrow> valu_indep (sym_used \<sigma>) (\<lambda>V. (chunk_recv c V, chunk_perm c V, chunk_val c V))) \<Longrightarrow>
    g' V = Some (VBool True) \<Longrightarrow>
    concretize_heap h' V = Some ch' \<Longrightarrow>
    ch \<succeq> ch' \<Longrightarrow>
    Q (\<sigma>\<lparr>sym_cond := g', sym_heap := h'\<rparr>) \<Longrightarrow>
    P"
  shows "P"
  using assms unfolding sym_consolidate_def by blast

lemma sym_consolidate_frame :
  assumes "sym_heap \<sigma> = c # cs"
  assumes "sym_consolidate (\<sigma>\<lparr>sym_heap := cs\<rparr>) (\<lambda> \<sigma>. Q (\<sigma>\<lparr> sym_heap := c # sym_heap \<sigma> \<rparr>))"
  shows "sym_consolidate \<sigma> Q"
  unfolding sym_consolidate_def
  apply (clarsimp simp add: assms(1))
  apply (insert assms(2)) apply (erule sym_consolidateE; simp)
  apply (drule compatible_smaller; assumption?)
  apply (clarsimp)
  apply (safe del:exI intro!:exI; assumption?; simp add:concretize_heap_cons) by fastforce+

lemma sym_consolidate_drop :
  assumes "sym_heap \<sigma> = c # cs"
  assumes "Q (\<sigma>\<lparr>sym_heap := cs\<rparr>)"
  shows "sym_consolidate \<sigma> Q"
  using assms unfolding sym_consolidate_def
  apply (clarsimp simp add: bind_eq_Some_conv)
  using greater_def by fastforce

lemma sym_consolidate_swap :
  assumes "sym_heap \<sigma> = c1 # c2 # cs"
  assumes "Q (\<sigma>\<lparr>sym_heap := c2 # c1 # cs\<rparr>)"
  shows "sym_consolidate \<sigma> Q"
  using assms unfolding sym_consolidate_def
  apply (clarsimp simp add: bind_eq_Some_conv assms(1))
  apply (rule exI[of _ "sym_cond \<sigma>"]; simp)
  apply (rule exI[of _ "c2 # c1 # cs"]; simp)
  using plus_assoc3 succ_refl by fastforce

lemma sym_consolidate_mono :
  assumes "sym_consolidate \<sigma> Q1"
  assumes "\<And> \<sigma>. Q1 \<sigma> \<Longrightarrow> Q2 \<sigma>"
  shows "sym_consolidate \<sigma> Q2"
  using assms unfolding sym_consolidate_def by blast

lemma sym_consolidate_dup :
  assumes "sym_consolidate \<sigma> (\<lambda> \<sigma>. sym_consolidate \<sigma> Q)"
  shows "sym_consolidate \<sigma> Q"
  unfolding sym_consolidate_def
  using assms apply (clarsimp)
  apply (erule (4) sym_consolidateE)
  apply (erule sym_consolidateE; simp)
  using succ_trans by (smt (verit, ccfv_SIG))

subsection \<open>symbolic evaluation\<close>

definition sfail :: "'a \<Rightarrow> bool" where
"sfail _ = False"

fun sexec_exp :: "'a sym_state \<Rightarrow> pure_exp \<Rightarrow> ('a sym_state \<Rightarrow> 'a sym_exp \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "sexec_exp \<sigma> (ELit l) Q = Q \<sigma> (SLit l)"

| "sexec_exp \<sigma> (Var x) Q = (\<exists> t. sym_store \<sigma> x = Some t \<and> Q \<sigma> t)"

| "sexec_exp \<sigma> (Unop op e) Q = sexec_exp \<sigma> e (\<lambda> \<sigma> t. Q \<sigma> (SUnop op t))"

| "sexec_exp \<sigma> (Binop e1 op e2) Q = sexec_exp \<sigma> e1 (\<lambda> \<sigma> t1. 
   case binop_lazy_bool op of 
     Some bres \<Rightarrow> Q (sym_cond_add \<sigma> (t1 =\<^sub>s SBool (fst bres))) (SBool (snd bres)) \<and>
       sexec_exp (sym_cond_add \<sigma> (t1 =\<^sub>s (\<not>\<^sub>s SBool (fst bres)))) e2 Q
   | None \<Rightarrow> sexec_exp \<sigma> e2 (\<lambda> \<sigma> t2. (sym_cond \<sigma> \<turnstile>\<^sub>s SBinopSafe t1 op t2) \<and> Q \<sigma> (SBinop t1 op t2)))"

| "sexec_exp \<sigma> (CondExp e1 e2 e3) Q = sexec_exp \<sigma> e1 (\<lambda> \<sigma> t1.
    sexec_exp (sym_cond_add \<sigma> t1) e2 Q \<and> sexec_exp (sym_cond_add \<sigma> (\<not>\<^sub>s t1)) e3 Q)"

| "sexec_exp \<sigma> (FieldAcc e f) Q = sexec_exp \<sigma> e (\<lambda> \<sigma> te.
    sym_heap_extract \<sigma> te f (Some (SPerm 0)) (\<lambda> \<sigma> c.
    sym_heap_do_add \<sigma> c (\<lambda> \<sigma>.
    Q \<sigma> (chunk_val c))))"

| "sexec_exp \<sigma> (Old l e) Q = sfail (''Not supported expression: Old'')"
| "sexec_exp \<sigma> (Perm v va) Q = sfail (''Not supported expression: Perm'')"
| "sexec_exp \<sigma> (PermPred v va) Q = sfail (''Not supported expression: PermPred'')"
| "sexec_exp \<sigma> (FunApp f es) Q = sfail (''Not supported expression: FunApp'')"
| "sexec_exp \<sigma> Result Q = sfail (''Not supported expression: Result'')"
| "sexec_exp \<sigma> (Unfolding _ _ _) Q = sfail (''Not supported expression: Unfolding'')"
| "sexec_exp \<sigma> (Let _ _) Q = sfail (''Not supported expression: Let'')"
| "sexec_exp \<sigma> (PExists _ _) Q = sfail (''Not supported expression: PExists'')"
| "sexec_exp \<sigma> (PForall _ _) Q = sfail (''Not supported expression: PForall'')"


fun sproduce :: "'a sym_state \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "sproduce \<sigma> (Atomic (Pure e)) Q = sexec_exp \<sigma> e (\<lambda> \<sigma> t. Q (sym_cond_add \<sigma> t))"
| "sproduce \<sigma> (Atomic (Acc e f (PureExp ep))) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> te. sexec_exp \<sigma> ep (\<lambda> \<sigma> tep.
    \<comment> \<open>TODO: weaken this?\<close>
    (sym_cond \<sigma> \<turnstile>\<^sub>s \<not>\<^sub>s (tep =\<^sub>s SPerm 0)) \<and> (
      \<exists> ty. sym_fields \<sigma> f = Some ty \<and> sym_gen_fresh \<sigma> ty (\<lambda> \<sigma> tv.
       sym_heap_do_add \<sigma> \<lparr> chunk_field = f, chunk_recv = te, chunk_perm = tep, chunk_val = (SVar tv) \<rparr> Q))))"
| "sproduce \<sigma> (Atomic (Acc e f Wildcard)) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> te. sym_gen_fresh \<sigma> TPerm (\<lambda> \<sigma> tp.
      \<exists> ty. sym_fields \<sigma> f = Some ty \<and> sym_gen_fresh \<sigma> ty (\<lambda> \<sigma> tv.
      sym_heap_do_add (sym_cond_add \<sigma> (SPerm 0 <\<^sub>s SVar tp))
        \<lparr> chunk_field = f, chunk_recv = te, chunk_perm = (SVar tp), chunk_val = (SVar tv) \<rparr> Q)))"
| "sproduce \<sigma> (Atomic (AccPredicate _ _ _)) Q = sfail (''Not supported produce: AccPredicate'')"
| "sproduce \<sigma> (Imp e A) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. Q (sym_cond_add \<sigma> (\<not>\<^sub>s t)) \<and> sproduce (sym_cond_add \<sigma> t) A Q)"
| "sproduce \<sigma> (CondAssert e A1 A2) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. sproduce (sym_cond_add \<sigma> t) A1 Q \<and> sproduce (sym_cond_add \<sigma> (\<not>\<^sub>s t)) A2 Q)"
| "sproduce \<sigma> (Star A1 A2) Q = sproduce \<sigma> A1 (\<lambda> \<sigma>. sproduce \<sigma> A2 Q)"
| "sproduce \<sigma> (Wand A1 A2) Q = sfail (''Not supported produce: Wand'')"
| "sproduce \<sigma> (ImpureAnd A1 A2) Q = sfail (''Not supported produce: ImpureAnd'')"
| "sproduce \<sigma> (ImpureOr A1 A2) Q =  sfail (''Not supported produce: ImpureOr'')"
| "sproduce \<sigma> (ForAll _ _) Q =  sfail (''Not supported produce: ForAll'')"
| "sproduce \<sigma> (Exists _ _) Q =  sfail (''Not supported produce: Exists'')"

fun sconsume :: "'a sym_state \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "sconsume \<sigma> (Atomic (Pure e)) Q = sexec_exp \<sigma> e (\<lambda> \<sigma> t. (sym_cond \<sigma> \<turnstile>\<^sub>s t) \<and> Q \<sigma>)"
| "sconsume \<sigma> (Atomic (Acc e f (PureExp ep))) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> te. sexec_exp \<sigma> ep (\<lambda> \<sigma> tep. sym_heap_extract \<sigma> te f (Some tep) (\<lambda> \<sigma> c.
      sym_heap_do_add \<sigma> (c\<lparr> chunk_perm := chunk_perm c -\<^sub>s tep \<rparr>) Q)))"
| "sconsume \<sigma> (Atomic (Acc e f Wildcard)) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> te. sym_heap_extract \<sigma> te f None (\<lambda> \<sigma> c. 
     sym_heap_do_add \<sigma> (c\<lparr> chunk_perm := SPermDiv (chunk_perm c) (SPerm 2) \<rparr>) Q))"
| "sconsume \<sigma> (Atomic (AccPredicate _ _ _)) Q = sfail (''Not supported consume: AccPredicate'')"
| "sconsume \<sigma> (Imp e A) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. Q (sym_cond_add \<sigma> (\<not>\<^sub>s t)) \<and> sconsume (sym_cond_add \<sigma> t) A Q)"
| "sconsume \<sigma> (CondAssert e A1 A2) Q =
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. sconsume (sym_cond_add \<sigma> t) A1 Q \<and> sconsume (sym_cond_add \<sigma> (\<not>\<^sub>s t)) A2 Q)"
| "sconsume \<sigma> (Star A1 A2) Q = sconsume \<sigma> A1 (\<lambda> \<sigma>. sconsume \<sigma> A2 Q)"
| "sconsume \<sigma> (Wand A1 A2) Q = sfail (''Not supported consume: Wand'')"
| "sconsume \<sigma> (ImpureAnd A1 A2) Q = sfail (''Not supported consume: ImpureAnd'')"
| "sconsume \<sigma> (ImpureOr A1 A2) Q = sfail (''Not supported consume: ImpureOr'')"
| "sconsume \<sigma> (ForAll _ _) Q = sfail (''Not supported consume: ForAll'')"
| "sconsume \<sigma> (Exists _ _) Q = sfail (''Not supported consume: Exists'')"

fun sexec :: "'a sym_state \<Rightarrow> stmt \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "sexec \<sigma> (stmt.Inhale A) Q = sproduce \<sigma> A Q"
| "sexec \<sigma> (stmt.Exhale A) Q = sconsume \<sigma> A (\<lambda> \<sigma>. sym_stabilize \<sigma> Q)"
| "sexec \<sigma> (stmt.Assert A) Q = sfail (''Not supported statement: Assert'')"
| "sexec \<sigma> (stmt.Assume A) Q = sfail (''Not supported statement: Assume'')"
| "sexec \<sigma> (stmt.If e s1 s2) Q = 
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. sexec (sym_cond_add \<sigma> t) s1 Q \<and> sexec (sym_cond_add \<sigma> (\<not>\<^sub>s t)) s2 Q)"
| "sexec \<sigma> (stmt.Seq s1 s2) Q = sexec \<sigma> s1 (\<lambda> \<sigma>. sexec \<sigma> s2 Q)"
| "sexec \<sigma> (stmt.LocalAssign v e) Q = (sym_store \<sigma> v \<noteq> None \<and> 
    sexec_exp \<sigma> e (\<lambda> \<sigma> t. Q (\<sigma>\<lparr>sym_store := sym_store \<sigma>(v \<mapsto> t) \<rparr>)))"
| "sexec \<sigma> (stmt.Havoc v) Q = (\<exists> ty. sym_store_type \<sigma> v = Some ty \<and>
    sym_gen_fresh \<sigma> ty (\<lambda> \<sigma> t. Q (\<sigma>\<lparr>sym_store := sym_store \<sigma>(v \<mapsto> (SVar t)) \<rparr>)))"
| "sexec \<sigma> (stmt.FieldAssign e f e2) Q = sexec_exp \<sigma> e (\<lambda> \<sigma> t. sexec_exp \<sigma> e2 (\<lambda> \<sigma> t2. 
    sym_heap_extract \<sigma> t f (Some (SPerm 1)) (\<lambda> \<sigma> c.
\<comment> \<open>We need to ensure that there are no chunks for t with permission 0 left.
 TODO: do something weaker than stabilize, e.g. check that there are no chunks for t\<close>
    sym_stabilize \<sigma> (\<lambda> \<sigma>.
    sym_heap_do_add \<sigma> (c\<lparr>chunk_val := t2\<rparr>) Q))))"
| "sexec \<sigma> stmt.Skip Q = Q \<sigma>"
| "sexec \<sigma> (stmt.MethodCall _ _ _) Q = sfail (''Not supported statement: MethodCall'')"
| "sexec \<sigma> (stmt.While _ _ _) Q = sfail (''Not supported statement: While'')"
| "sexec \<sigma> (stmt.Fold _ _ _) Q = sfail (''Not supported statement: Fold'')"
| "sexec \<sigma> (stmt.Unfold _ _ _) Q = sfail (''Not supported statement: Unfold'')"
| "sexec \<sigma> (stmt.Package _ _) Q = sfail (''Not supported statement: Package'')"
| "sexec \<sigma> (stmt.Apply _ _) Q = sfail (''Not supported statement: Apply'')"
| "sexec \<sigma> (stmt.Label _) Q = sfail (''Not supported statement: Label'')"
| "sexec \<sigma> (stmt.Scope _ _) Q = sfail (''Not supported statement: Scope'')"

fun sinit :: "vtyp list \<Rightarrow> (field_name \<rightharpoonup> vtyp) \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "sinit [] fs Q = Q \<lparr>sym_store = Map.empty, sym_cond = SBool True, sym_heap = [],
     sym_used = 0, sym_store_type = Map.empty, sym_fields = fs\<rparr>"
| "sinit (ty#tys) fs Q =
    sinit tys fs (\<lambda> \<sigma>.
    sym_gen_fresh \<sigma> ty (\<lambda> \<sigma> v. Q (\<sigma>
     \<lparr> sym_store := shift_and_add (sym_store \<sigma>) (SVar v),
       sym_store_type := shift_and_add (sym_store_type \<sigma>) ty \<rparr>)))"

(* old
(* C of https://arxiv.org/pdf/2311.07559 *)
type_synonym sym_val = var
type_synonym 'a valuation = "sym_val \<rightharpoonup> 'a val"

(* We define sym_exp semantically such that = is semantic equality (important for rewriting). *)
(* TODO: Should this be total or partial? The gradual typing paper defines it as partial, but then later treats it as total. *)
type_synonym 'a sym_exp = "'a valuation \<rightharpoonup> 'a val"

definition SLit :: "lit \<Rightarrow> 'a sym_exp" where
"SLit l _ = Some (val_of_lit l)"
abbreviation SBool where "SBool b \<equiv> SLit (LBool b)"
abbreviation SInt where "SInt n \<equiv> SLit (LInt n)"
abbreviation SPerm where "SPerm p \<equiv> SLit (LPerm p)"

definition SVal :: "sym_val \<Rightarrow> 'a sym_exp" where
"SVal v V = V v"
definition SUnop :: "unop \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SUnop op t V = Option.bind (t V) (\<lambda> v. binop_result_to_option (eval_unop op v))"
abbreviation SNot ("\<not>\<^sub>s _" [40]40) where "SNot \<equiv> \<lambda> t1. SUnop Not t1"

definition SBinop :: "'a sym_exp \<Rightarrow> binop \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SBinop t1 op t2 V = Option.bind (t1 V) (\<lambda> v1. Option.bind (t2 V) (\<lambda> v2.
   binop_result_to_option (eval_binop v1 op v2)))"
abbreviation SAnd (infixr "\<and>\<^sub>s" 35) where "SAnd \<equiv> \<lambda> t1 t2. SBinop t1 And t2"
abbreviation SEq (infixl "=\<^sub>s" 50) where "SEq \<equiv> \<lambda> t1 t2. SBinop t1 Eq t2"
abbreviation SLt (infix "<\<^sub>s" 50) where "SLt \<equiv> \<lambda> t1 t2. SBinop t1 Lt t2"
abbreviation SLte (infix "\<le>\<^sub>s" 50) where "SLte \<equiv> \<lambda> t1 t2. SBinop t1 Lte t2"
abbreviation SImp (infixr "\<longrightarrow>\<^sub>s" 25) where "SImp \<equiv> \<lambda> t1 t2. SBinop t1 BImp t2"
abbreviation SSub (infixl "-\<^sub>s" 65) where "SSub \<equiv> \<lambda> t1 t2. SBinop t1 Sub t2"

definition SCondExp :: "'a sym_exp \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_exp" where
"SCondExp t1 t2 t3 V = Option.bind (t1 V) (\<lambda> v1. case v1 of VBool b \<Rightarrow> if b then t2 V else t3 V | _ \<Rightarrow> None)"

(* TODO: total or partial? *)
type_synonym 'a sym_store = "var \<Rightarrow> 'a sym_exp"
type_synonym 'a path_cond = "'a sym_exp"

record 'a chunk =
  chunk_field :: field_name
  chunk_recv :: "'a sym_exp"
  chunk_perm :: "'a sym_exp"
  chunk_val :: "'a sym_exp"

type_synonym 'a sym_heap = "'a chunk multiset"

record 'a sym_state =
  sym_cond :: "'a path_cond"
  sym_heap :: "'a sym_heap"
  sym_store :: "'a sym_store"
  sym_used :: "sym_val list" (* list to make clear that it is finite *)

definition sym_fresh :: "'a sym_state \<Rightarrow> sym_val" where
"sym_fresh \<sigma> = (SOME v. v \<notin> set (sym_used \<sigma>))"

definition sym_fresh_next :: "'a sym_state \<Rightarrow> 'a sym_state" where
"sym_fresh_next \<sigma> = \<sigma>\<lparr>sym_used := sym_fresh \<sigma> # sym_used \<sigma>\<rparr>"

definition sym_valid :: "'a sym_exp \<Rightarrow> bool" ("\<turnstile>\<^sub>s _" 10) where
"sym_valid t = (\<forall> V. t V = Some (VBool True))"

inductive seval_exp :: "'a sym_state \<Rightarrow> pure_exp \<Rightarrow> 'a sym_exp \<Rightarrow> 'a sym_state \<Rightarrow> bool"
  ("_ \<turnstile> _ [\<Down>] _ \<stileturn> _" [51,0,0,51] 81)
  where
  SEvalLit: "\<sigma> \<turnstile> ELit l [\<Down>] SLit l \<stileturn> \<sigma>"
| SEvalVar: "\<sigma> \<turnstile> Var x [\<Down>] sym_store \<sigma> x \<stileturn> \<sigma>"
| SEvalUnop: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Unop op e [\<Down>] SUnop op t \<stileturn> \<sigma>'"
| SEvalBinopLazyEq: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1 \<stileturn> \<sigma>'; binop_lazy_bool op = Some bres \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Binop e1 op e2 [\<Down>] SBool (snd bres) \<stileturn> \<sigma>'\<lparr>sym_cond := sym_cond \<sigma>' \<and>\<^sub>s t1 =\<^sub>s SBool (fst bres) \<rparr>"
| SEvalBinopLazyNotEq: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1 \<stileturn> \<sigma>'; binop_lazy_bool op = Some bres; \<sigma>'\<lparr>sym_cond := sym_cond \<sigma>' \<and>\<^sub>s t1 =\<^sub>s SBool (\<not> (fst bres)) \<rparr> \<turnstile> e2 [\<Down>] t2 \<stileturn> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Binop e1 op e2 [\<Down>] t2 \<stileturn> \<sigma>''"
| SEvalBinop: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1 \<stileturn> \<sigma>'; binop_lazy_bool op = None; \<sigma>' \<turnstile> e2 [\<Down>] t2 \<stileturn> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Binop e1 op e2 [\<Down>] SBinop t1 op t2 \<stileturn> \<sigma>''"
(* TODO: Does this make sense? This is like in the paper, but I am it makes sense as it forces the symbolic execution to choose a path instead of allowing to verify both paths*)
| SEvalCondExpTrue: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1 \<stileturn> \<sigma>'; \<sigma>'\<lparr>sym_cond := sym_cond \<sigma>' \<and>\<^sub>s t1 \<rparr>  \<turnstile> e2 [\<Down>] t2 \<stileturn> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> CondExp e1 e2 e3 [\<Down>] t2 \<stileturn> \<sigma>''"
| SEvalCondExpFalse: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1 \<stileturn> \<sigma>'; \<sigma>'\<lparr>sym_cond := sym_cond \<sigma>' \<and>\<^sub>s \<not>\<^sub>s t1 \<rparr>  \<turnstile> e3 [\<Down>] t3 \<stileturn> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> CondExp e1 e2 e3 [\<Down>] t3 \<stileturn> \<sigma>''"
| SEvalField: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> \<sigma>'; c \<in># sym_heap \<sigma>'; chunk_field c = f; \<turnstile>\<^sub>s sym_cond \<sigma>' \<longrightarrow>\<^sub>s SPerm 0 <\<^sub>s (chunk_perm c) \<and>\<^sub>s t =\<^sub>s chunk_recv c \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> FieldAcc e f [\<Down>] chunk_val c \<stileturn> \<sigma>'"
(* TODO: old expressions *)

inductive seval_exp_det :: "'a sym_state \<Rightarrow> pure_exp \<Rightarrow> 'a sym_exp \<Rightarrow> bool"
 ("_ \<turnstile> _ [\<Down>] _" [51,0,51] 81)
  where
  SEvalDetLit: "\<sigma> \<turnstile> ELit l [\<Down>] SLit l"
| SEvalDetVar: "\<sigma> \<turnstile> Var x [\<Down>] sym_store \<sigma> x"
| SEvalDetUnop: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Unop op e [\<Down>] SUnop op t"
| SEvalDetBinop: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1; \<sigma>' \<turnstile> e2 [\<Down>] t2 \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Binop e1 op e2 [\<Down>] SBinop t1 op t2"
| SEvalDetCondExp: "\<lbrakk> \<sigma> \<turnstile> e1 [\<Down>] t1; \<sigma> \<turnstile> e2 [\<Down>] t2; \<sigma> \<turnstile> e3 [\<Down>] t3 \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> CondExp e1 e2 e3 [\<Down>] SCondExp t1 t2 t3"
| SEvalDetField: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t; c \<in># sym_heap \<sigma>; chunk_field c = f; \<turnstile>\<^sub>s sym_cond \<sigma> \<longrightarrow>\<^sub>s SPerm 0 <\<^sub>s chunk_perm c \<and>\<^sub>s t =\<^sub>s chunk_recv c \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> FieldAcc e f [\<Down>] chunk_val c"
(* TODO: old expressions *)

inductive sproduce :: "'a sym_state \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a sym_state \<Rightarrow> bool"
 ("_ \<turnstile> _ \<Zdres> _" [51,0,51] 81)
  where
  SProducePure: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> _ \<rbrakk> \<Longrightarrow> \<sigma> \<turnstile> Atomic (Pure e) \<Zdres> \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s t \<rparr>"
| SProduceAccPure: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] te \<stileturn> _; \<sigma> \<turnstile> ep [\<Down>] tep \<stileturn> _ \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Atomic (Acc e f (PureExp ep)) \<Zdres> (sym_fresh_next \<sigma>)\<lparr> sym_heap := sym_heap \<sigma> \<union># {# chunk.make f te tep (SVal (sym_fresh \<sigma>)) #}  \<rparr>"
(* TODO: How to produce wildcards? *)
| SProduceImpTrue: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> _; \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s t\<rparr> \<turnstile> A \<Zdres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Imp e A \<Zdres> \<sigma>' "
| SProduceImpFalse: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> _ \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Imp e A \<Zdres> \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s \<not>\<^sub>s t\<rparr>"
| SProduceCondTrue: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> _; \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s t\<rparr> \<turnstile> A1 \<Zdres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> CondAssert e A1 A2 \<Zdres> \<sigma>'"
| SProduceCondFalse: "\<lbrakk> \<sigma> \<turnstile> e [\<Down>] t \<stileturn> _; \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s \<not>\<^sub>s t\<rparr> \<turnstile> A2 \<Zdres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> CondAssert e A1 A2 \<Zdres> \<sigma>'"
| SProduceStar: "\<lbrakk> \<sigma> \<turnstile> A1 \<Zdres> \<sigma>'; \<sigma>' \<turnstile> A2 \<Zdres> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma> \<turnstile> Star A1 A2 \<Zdres> \<sigma>''"


inductive sconsume :: "'a sym_state \<Rightarrow> 'a sym_state \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a sym_state \<Rightarrow> bool"
 ("_, _ \<turnstile> _ \<Zrres> _" [51, 0,0,51] 81)
  where
  SConsumePure: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] t; \<turnstile>\<^sub>s sym_cond \<sigma> \<longrightarrow>\<^sub>s t \<rbrakk> \<Longrightarrow> \<sigma>, \<sigma>E \<turnstile> Atomic (Pure e) \<Zrres> \<sigma>"
| SConsumeAccPure: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] te; \<sigma>E \<turnstile> ep [\<Down>] tep; sym_heap \<sigma> = h' \<union># {# c #};
    \<turnstile>\<^sub>s sym_cond \<sigma> \<longrightarrow>\<^sub>s tep \<le>\<^sub>s chunk_perm c \<and>\<^sub>s te =\<^sub>s chunk_recv c  \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> Atomic (Acc e f (PureExp ep)) \<Zrres> \<sigma>\<lparr> sym_heap := h' \<union># {# c\<lparr>chunk_perm := chunk_perm c -\<^sub>s tep\<rparr> #}  \<rparr>"
(* TODO: How to consume wildcards? *)
| SConsumeImpTrue: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] t; g' = (sym_cond \<sigma> \<and>\<^sub>s t); \<sigma>\<lparr>sym_cond := g\<rparr>, \<sigma>E\<lparr>sym_cond := g\<rparr> \<turnstile> A \<Zrres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> Imp e A \<Zrres> \<sigma>' "
| SConsumeImpFalse: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] t \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> Imp e A \<Zrres> \<sigma>\<lparr> sym_cond := sym_cond \<sigma> \<and>\<^sub>s \<not>\<^sub>s t\<rparr>"
| SConsumeCondTrue: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] t; g' = (sym_cond \<sigma> \<and>\<^sub>s t); \<sigma>\<lparr>sym_cond := g\<rparr>, \<sigma>E\<lparr>sym_cond := g\<rparr> \<turnstile> A1 \<Zrres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> CondAssert e A1 A2 \<Zrres>  \<sigma>'"
| SConsumeCondFalse: "\<lbrakk> \<sigma>E \<turnstile> e [\<Down>] t; g' = (sym_cond \<sigma> \<and>\<^sub>s \<not>\<^sub>s t); \<sigma>\<lparr>sym_cond := g\<rparr>, \<sigma>E\<lparr>sym_cond := g\<rparr> \<turnstile> A2 \<Zrres> \<sigma>' \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> CondAssert e A1 A2 \<Zrres>  \<sigma>'"
| SConsumeStar: "\<lbrakk> \<sigma>, \<sigma>E \<turnstile> A1 \<Zrres> \<sigma>'; \<sigma>', \<sigma>E\<lparr>sym_cond := sym_cond \<sigma>'\<rparr> \<turnstile> A2 \<Zrres> \<sigma>'' \<rbrakk> \<Longrightarrow>
   \<sigma>, \<sigma>E \<turnstile> Star A1 A2 \<Zrres> \<sigma>''"
 *)
end