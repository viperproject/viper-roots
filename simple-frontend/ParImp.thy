theory ParImp
  imports ViperCommon.SepAlgebra ViperCommon.SepLogic ViperAbstract.Instantiation VHelper
begin

(* Maybe adapt state model to instantiation, just remove mask... *)

definition field_val :: "string" where
  "field_val = ''val''"

term "x :: int equi_state"
(*
  :: "(nat \<Rightarrow> int val option) agreement \<times> (char list \<Rightarrow> int virtual_state option) agreement \<times> int virtual_state"
*)

(*
type_synonym val = int
type_synonym var = nat
type_synonym heap_loc = int
type_synonym heap = "heap_loc \<rightharpoonup> val" (* concrete heap *)
type_synonym stack = "var \<Rightarrow> val"
*)
type_synonym stack = "var \<rightharpoonup> int val"
type_synonym heap = "int partial_heap"
(* address are nat here... *)
type_synonym state = "stack \<times> heap"

(*
datatype binop =
  Add | Sub | Mult | IntDiv | PermDiv | Mod
| Eq | Neq
| Gt | Gte | Lt | Lte
| Or | BImp | And

*)
datatype int_binop = Add | Sub | Mult | Mod

fun interp_int_binop :: "int_binop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "interp_int_binop Add = (+)"
| "interp_int_binop Sub = (-)"
| "interp_int_binop Mult = (*)"
| "interp_int_binop Mod = (mod)"

datatype exp =
Evar var
| Elit int
| Ebinop exp int_binop exp

datatype bexp =
Beq exp exp
| Band bexp bexp
| Bnot bexp

type_synonym f_assertion = "int equi_state set"

datatype cmd =
  Cskip
| Cassign var exp
| Cread var var (* second var needs to be a non-null ref *)
| Cwrite var exp
| Calloc var exp
| Cfree var
| Cseq cmd cmd
| Cpar "(pure_exp, pure_exp atomic_assert) assert" cmd "(pure_exp, pure_exp atomic_assert) assert"
       "(pure_exp, pure_exp atomic_assert) assert" cmd "(pure_exp, pure_exp atomic_assert) assert" ("{_} _ {_} || {_} _ {_}")
| Cif bexp cmd cmd
| Cwhile bexp "(pure_exp, pure_exp atomic_assert) assert" cmd


primrec edenot :: "exp \<Rightarrow> stack \<Rightarrow> int"
  where
  "edenot (Evar v) s = the_int (the (s v))"
| "edenot (Elit n) s = n"
| "edenot (Ebinop e1 op e2) s = interp_int_binop op (edenot e1 s) (edenot e2 s)"

primrec
  bdenot :: "bexp \<Rightarrow> stack \<Rightarrow> bool" where
  "bdenot (Beq e1 e2) s = (edenot e1 s = edenot e2 s)"
| "bdenot (Band b1 b2) s = (bdenot b1 s \<and> bdenot b2 s)"
| "bdenot (Bnot b) s = (\<not> bdenot b s)"

(*
| RedLocalAssign: "\<lbrakk>variables \<Delta> x = Some ty; e \<omega> = Some v; v \<in> ty \<rbrakk> \<Longrightarrow>
   red_stmt \<Delta> (LocalAssign x e) \<omega> ({assign_var_state x (Some v) \<omega>})"
*)
term "TypedEqui.assign_var_state"
                   
inductive red :: "cmd \<Rightarrow> state \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> bool"
  ("\<langle>_, _\<rangle> \<rightarrow> \<langle>_, _\<rangle>" [51,0] 81)
  where
  red_Seq1[intro]: "\<langle>Cseq Cskip C, \<sigma>\<rangle> \<rightarrow> \<langle>C, \<sigma>\<rangle>"
| red_Seq2[elim]: "\<langle>C1, \<sigma>\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle> \<Longrightarrow> \<langle>Cseq C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>Cseq C1' C2, \<sigma>'\<rangle>"
| red_If1[intro]: "bdenot b (fst \<sigma>) \<Longrightarrow> \<langle>Cif b C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C1, \<sigma>\<rangle>"
| red_If2[intro]: "\<not> bdenot b (fst \<sigma>) \<Longrightarrow> \<langle>Cif b C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C2, \<sigma>\<rangle>"
| red_Par1[elim]: "\<lbrakk> \<langle>C1, \<sigma>\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle> \<rbrakk> \<Longrightarrow> \<langle>{A1} C1 {B1} || {A2} C2 {B2}, \<sigma>\<rangle> \<rightarrow> \<langle>{A1} C1' {B1} || {A2} C2 {B2}, \<sigma>'\<rangle>" 
| red_Par2[elim]: "\<lbrakk> \<langle>C2, \<sigma>\<rangle> \<rightarrow> \<langle>C2', \<sigma>'\<rangle> \<rbrakk> \<Longrightarrow> \<langle>{A1} C1 {B1} || {A2} C2 {B2}, \<sigma>\<rangle> \<rightarrow> \<langle>{A1} C1 {B1} || {A2} C2' {B2}, \<sigma>'\<rangle>"
| red_Par3[intro]: "\<langle>{_} Cskip {_} || {_} Cskip {_}, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>\<rangle>"
| red_Loop[intro]: "\<langle>Cwhile b I C, \<sigma>\<rangle> \<rightarrow> \<langle>Cif b (Cseq C (Cwhile b I C)) Cskip, \<sigma>\<rangle>"
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x \<mapsto> VInt (edenot e s)), h) \<rbrakk> \<Longrightarrow> \<langle>Cassign x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"

| red_Alloc[intro]: "\<lbrakk> \<sigma> = (s,h); (l, field_val) \<notin> dom h; \<sigma>' = (s(x \<mapsto> VRef (Address l)), h((l, field_val) \<mapsto> VInt (edenot e s))) \<rbrakk> 
  \<Longrightarrow> \<langle>Calloc x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Read[intro]:  "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); h (l, field_val) = Some (VInt v); \<sigma>' = (s(x \<mapsto> VInt v), h) \<rbrakk>
  \<Longrightarrow> \<langle>Cread x r, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Free[intro]:  "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); \<sigma>' = (s, h((l, field_val) := None)) \<rbrakk> \<Longrightarrow> \<langle>Cfree r, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Write[intro]: "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); (l, field_val) \<in> dom h; \<sigma>' = (s, h((l, field_val) \<mapsto> VInt (edenot e s))) \<rbrakk>
  \<Longrightarrow> \<langle>Cwrite r e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"

inductive_cases red_par_cases: "\<langle>{P1} C1 {Q1} || {P2} C2 {Q2}, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_seq_cases: "\<langle>Cseq C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_write_cases: "\<langle>Cwrite r e, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_if_cases: "\<langle>Cif b C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_while_cases: "\<langle>Cwhile b I C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_alloc_cases: "\<langle>Calloc r e, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_assign_cases: "\<langle>Cassign x e, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_free_cases: "\<langle>Cfree r, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_read_cases: "\<langle>Cread x r, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"


subsubsection \<open>Abort semantics\<close>

definition get_address where
  "get_address x = the_address (the_ref (the x))"

lemma get_address_simp[simp]:
  shows "get_address (Some (VRef (Address l))) = l"
  by (simp add: get_address_def)

primrec
  accesses :: "cmd \<Rightarrow> stack \<Rightarrow> address set"
where
    "accesses Cskip            s = {}"
  | "accesses (Cassign x E)    s = {}"
  | "accesses (Cread x r)      s = { get_address (s r) }"
  | "accesses (Cwrite r E)    s = { get_address (s r) }"
  | "accesses (Calloc x E)     s = {}"
  | "accesses (Cfree r)     s = {get_address (s r)}"
  | "accesses (Cseq C1 C2)     s = accesses C1 s"
  | "accesses ({_} C1 {_} || {_} C2 {_})     s = accesses C1 s \<union> accesses C2 s"
  | "accesses (Cif B C1 C2)    s = {}"
  | "accesses (Cwhile B I C)     s = {}"

primrec
  writes :: "cmd \<Rightarrow> stack \<Rightarrow> address set"
where
    "writes Cskip            s = {}"
  | "writes (Cassign x E)    s = {}"
  | "writes (Cread x r)      s = {}"
  | "writes (Cwrite r E)    s = {get_address (s r)}"
  | "writes (Calloc x E)     s = {}"
  | "writes (Cfree r)     s = {get_address (s r)}"
  | "writes (Cseq C1 C2)     s = writes C1 s"
  | "writes ({_} C1 {_} || {_} C2 {_})     s = writes C1 s \<union> writes C2 s"
  | "writes (Cif B C1 C2)    s = {}"
  | "writes (Cwhile B I C)     s = {}"

inductive
  aborts :: "cmd \<Rightarrow> state \<Rightarrow> bool"
where
  aborts_Seq[intro]:   "aborts C1 \<sigma> \<Longrightarrow> aborts (Cseq C1 C2) \<sigma>" 
| aborts_Par1[intro]:  "aborts C1 \<sigma> \<Longrightarrow> aborts ({_} C1 {_} || {_} C2 {_}) \<sigma>" 
| aborts_Par2[intro]:  "aborts C2 \<sigma> \<Longrightarrow> aborts ({_} C1 {_} || {_} C2 {_}) \<sigma>"

| aborts_Race1[intro]:  "\<not> disjoint (accesses C1 (fst \<sigma>)) (writes C2 (fst \<sigma>)) \<Longrightarrow> aborts ({_} C1 {_} || {_} C2 {_}) \<sigma>"
| aborts_Race2[intro]:  "\<not> disjoint (writes C1 (fst \<sigma>)) (accesses C2 (fst \<sigma>)) \<Longrightarrow> aborts ({_} C1 {_} || {_} C2 {_}) \<sigma>"

| aborts_Read[intro]:  "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cread x r) \<sigma>"
| aborts_Write[intro]: "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cwrite r E) \<sigma>"
| aborts_Free[intro]:  "\<lbrakk> fst \<sigma> r = Some (VRef (Address l)); (l, field_val) \<notin> dom (snd \<sigma>) \<rbrakk> \<Longrightarrow> aborts (Cfree r) \<sigma>"

| aborts_ReadNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cread x r) \<sigma>"
| aborts_WriteNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cwrite r e) \<sigma>"
| aborts_FreeNull[intro]: "fst \<sigma> r = Some (VRef Null) \<Longrightarrow> aborts (Cfree r) \<sigma>"


inductive_cases aborts_write_elim[elim]: "aborts (Cwrite r e) \<sigma>"
inductive_cases aborts_par_elim[elim]: "aborts ({P1} C1 {Q1} || {P2} C2 {Q2}) \<sigma>"
inductive_cases aborts_seq_elim[elim]: "aborts (Cseq C1 C2) \<sigma>"
inductive_cases aborts_while_elim[elim]: "aborts (Cwhile b I C) \<sigma>"
inductive_cases aborts_if_elim[elim]: "aborts (Cif b C1 C2) \<sigma>"
inductive_cases aborts_alloc_elim[elim]: "aborts (Calloc r e) \<sigma>"
inductive_cases aborts_assign_elim[elim]: "aborts (Cassign x e) \<sigma>"
inductive_cases aborts_free_elim[elim]: "aborts (Cfree r) \<sigma>"
inductive_cases aborts_read_elim[elim]: "aborts (Cread x r) \<sigma>"



subsection \<open>Free variables, updated variables and substitutions\<close>

text \<open>The free variables of expressions, boolean expressions, and
commands are defined as expected:\<close>

primrec
  fvE :: "exp \<Rightarrow> var set"
where
  "fvE (Evar v) = {v}"
| "fvE (Elit n) = {}"
| "fvE (Ebinop e1 _ e2) = (fvE e1 \<union> fvE e2)"

primrec
  fvB :: "bexp \<Rightarrow> var set"
where
  "fvB (Beq e1 e2)  = (fvE e1 \<union> fvE e2)"
| "fvB (Band b1 b2) = (fvB b1 \<union> fvB b2)"
| "fvB (Bnot b)     = (fvB b)"

primrec
  fvC :: "cmd \<Rightarrow> var set"
where
  "fvC (Cskip)          = {}"
| "fvC (Cassign v E)    = ({v} \<union> fvE E)"
| "fvC (Cread x r)    = ({x, r})"
| "fvC (Cwrite r E) = ({r} \<union> fvE E)"
| "fvC (Calloc r E)   = ({r} \<union> fvE E)"
| "fvC (Cfree r)   = {r}"
| "fvC (Cseq C1 C2)     = (fvC C1 \<union> fvC C2)"
| "fvC ({_} C1 {_} || {_} C2 {_})     = (fvC C1 \<union> fvC C2)"
| "fvC (Cif B C1 C2)    = (fvB B \<union> fvC C1 \<union> fvC C2)"
| "fvC (Cwhile B I C)     = (fvB B \<union> fvC C)"


text \<open>Below, we define the set of syntactically updated variables 
  of a command. This set overapproximates the set of variables that
  are actually updated during the command's execution.\<close>

primrec
  wrC :: "cmd \<Rightarrow> var set"
where
  "wrC (Cskip)         = {}"
| "wrC (Cassign v E)   = {v}"
| "wrC (Cread v E)     = {v}"
| "wrC (Cwrite E1 E2)  = {}"
| "wrC (Calloc v E)    = {v}"
| "wrC (Cfree E)    = {}"
| "wrC (Cseq C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC ({_} C1 {_} || {_} C2 {_})    = (wrC C1 \<union> wrC C2)"
| "wrC (Cif B C1 C2)   = (wrC C1 \<union> wrC C2)"
| "wrC (Cwhile B I C)    = (wrC C)"

primrec
  wrL :: "cmd \<Rightarrow> var list"
where
  "wrL (Cskip)         = []"
| "wrL (Cassign v E)   = [v]"
| "wrL (Cread v E)     = [v]"
| "wrL (Cwrite E1 E2)  = []"
| "wrL (Calloc v E)    = [v]"
| "wrL (Cfree E)    = []"
| "wrL (Cseq C1 C2)    = (wrL C1 @ wrL C2)"
| "wrL ({_} C1 {_} || {_} C2 {_})    = (wrL C1 @ wrL C2)"
| "wrL (Cif B C1 C2)   = (wrL C1 @ wrL C2)"
| "wrL (Cwhile B I C)    = (wrL C)"

lemma wrL_wrC_same:
  "set (wrL C) = wrC C"
  by (induct C) auto

text \<open>We also define the operation of substituting an expression for
a variable in expressions.\<close>

primrec
  subE :: "var \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp"
where
  "subE x E (Evar y)      = (if x = y then E else Evar y)"
| "subE x E (Elit n)      = Elit n"
| "subE x E (Ebinop e1 op e2) = Ebinop (subE x E e1) op (subE x E e2)"

primrec
  subB :: "var \<Rightarrow> exp \<Rightarrow> bexp \<Rightarrow> bexp"
where
  "subB x E (Beq e1 e2)  = Beq (subE x E e1) (subE x E e2)"
| "subB x E (Band b1 b2) = Band (subB x E b1) (subB x E b2)"
| "subB x E (Bnot b)     = Bnot (subB x E b)"

text \<open>Basic properties of substitutions:\<close>

lemma subE_assign:
 "edenot (subE x E e) s = edenot e (s(x \<mapsto> VInt (edenot E s)))"
by (induct e, simp_all)

lemma subB_assign:
 "bdenot (subB x E b) s = bdenot b (s(x \<mapsto> VInt (edenot E s)))"
by (induct b, simp_all add: subE_assign fun_upd_def)

lemma skip_simps[simp]: 
  "\<not> red Cskip \<sigma> C' \<sigma>'"
  "\<not> aborts Cskip \<sigma>"
  by (auto elim: aborts.cases red.cases)

lemma disjoint_minus: "disjoint (X - Z) Y = disjoint X (Y - Z)"
  by (auto simp add: disjoint_def)

subsection \<open>Basic properties of the semantics\<close>

lemma writes_accesses: "writes C s \<subseteq> accesses C s"
by (induct C arbitrary: s, auto)

text \<open>Proposition 4.1: Properties of basic properties of @{term red}.\<close>

lemma red_properties: 
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> 
     fvC C' \<subseteq> fvC C
   \<and> wrC C' \<subseteq> wrC C
   \<and> agrees (- wrC C) (fst \<sigma>') (fst \<sigma>)"
by (erule red.induct, auto simp add: agrees_def)

text \<open>Proposition 4.2: Semantics does not depend on variables not free in the term\<close>

lemma exp_agrees: "agrees (fvE E) s s' \<Longrightarrow> edenot E s = edenot E s'"
by (simp add: agrees_def, induct E, auto)

lemma bexp_agrees: "agrees (fvB B) s s' \<Longrightarrow> bdenot B s = bdenot B s'"
by (induct B, auto simp add: exp_agrees)

lemma accesses_agrees: "agrees (fvC C) s s' \<Longrightarrow> accesses C s = accesses C s'"
  by (induct C arbitrary: s s', simp_all add: exp_agrees, clarsimp)

lemma writes_agrees: "agrees (fvC C) s s' \<Longrightarrow> writes C s = writes C s'"
  by (induct C arbitrary: s s', simp_all add: exp_agrees, clarsimp)


lemma agrees_add:
  assumes "agrees X s s'"
      and "v1 = v2"
    shows "agrees X (s(x \<mapsto> VInt v1)) (s(x \<mapsto> VInt v2))"
  using agrees_refl assms(2) by auto

lemma red_agrees[rule_format]:
  assumes "red C \<sigma> C' \<sigma>'"
      and "agrees X (fst \<sigma>) s"
      and "snd \<sigma> = h"
      and "fvC C \<subseteq> X"
    shows "\<exists>s' h'. red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
  using assms
proof (induct arbitrary: X s rule: red.induct)
  case (red_Seq2 C1 \<sigma> C1' \<sigma>' C2)
  then show ?case using fvC.simps(7) le_sup_iff red.red_Seq2
    by metis
next
  case (red_If1 b \<sigma> C1 C2)
  then show ?case
    by (metis Un_upper1 agrees_search(3) bexp_agrees fst_conv fvC.simps(9) red.red_If1)
next
  case (red_If2 b \<sigma> C1 C2)
  then show ?case
    by (metis (no_types, lifting) agrees_search(2) agrees_simps(4) bexp_agrees fst_conv fvC.simps(9) red.red_If2)
next
  case (red_Par1 C1 \<sigma> C1' \<sigma>' C2)
  then show ?case
    by (metis fvC.simps(8) le_sup_iff red.red_Par1)
next
  case (red_Par2 C2 \<sigma> C2' \<sigma>' C1)
  then show ?case
    by (metis fvC.simps(8) le_sup_iff red.red_Par2)
next
  case (red_Assign \<sigma> s0 h0 \<sigma>' x e)
  have "edenot e s0 = edenot e s"
    by (metis agrees_search(3) agrees_simps(4) exp_agrees fst_eqD fvC.simps(2) red_Assign.hyps(1) red_Assign.prems(1) red_Assign.prems(3))
  then have "\<langle>Cassign x e, (s, h)\<rangle> \<rightarrow> \<langle>Cskip, (s(x := Some (VInt (edenot e s))), h)\<rangle>"
    by auto
  moreover have "agrees X (fst \<sigma>') (s(x := Some (VInt (edenot e s))))"
    by (smt (verit) \<open>edenot e s0 = edenot e s\<close> agrees_def fst_eqD fun_upd_other fun_upd_same red_Assign.hyps(1) red_Assign.hyps(2) red_Assign.prems(1))
  ultimately show ?case
    by (metis red_Assign.hyps(1) red_Assign.hyps(2) red_Assign.prems(2) snd_conv)
next
  case (red_Alloc \<sigma> s0 h0 l \<sigma>' x e)
  then have "edenot e s0 = edenot e s"
    by (metis agrees_search(2) agrees_simps(4) exp_agrees fstI fvC.simps(5) red_Alloc.hyps(1))
  then have "\<langle>Calloc x e, (s, snd \<sigma>)\<rangle> \<rightarrow> \<langle>Cskip, (s(x \<mapsto> VRef (Address l)), (snd \<sigma>)((l, field_val) \<mapsto> VInt (edenot e s)))\<rangle>"
    using red.red_Alloc
    by (metis red_Alloc.hyps(1) red_Alloc.hyps(2) sndI)
  moreover have "agrees X (fst \<sigma>') (s(x \<mapsto> VRef (Address l)))"
    by (smt (verit) agrees_def fst_conv fun_upd_other fun_upd_same red_Alloc)
  ultimately show ?case
    by (metis \<open>edenot e s0 = edenot e s\<close> red_Alloc.hyps(1) red_Alloc.hyps(3) red_Alloc.prems(2) snd_conv)
next
  case (red_Read \<sigma> s0 h0 r l v \<sigma>' x)
  moreover have "agrees X (fst \<sigma>') (s(x \<mapsto> VInt v))"
    by (smt (verit, ccfv_SIG) agrees_def fst_eqD fun_upd_other fun_upd_same red_Read.hyps(1) red_Read.hyps(4) red_Read.prems(1))
  moreover have "s r = Some (VRef (Address l))"
    by (metis agrees_search(3) agrees_simps(3) fstI fvC.simps(3) red_Read.hyps(1) red_Read.hyps(2) red_Read.prems(1) red_Read.prems(3))
  ultimately show ?case using red.red_Read[of _ s h r l v _ x]
    by (metis snd_conv)
next
  case (red_Free \<sigma> s0 h0 r l \<sigma>')
  then have "s r = Some (VRef (Address l))"
    by (metis agrees_search(3) agrees_simps(2) fst_eqD fvC.simps(6))
  then have "\<langle>Cfree r, (s, h)\<rangle> \<rightarrow> \<langle>Cskip, (s, h0((l, field_val) := None))\<rangle>"    
    using red_Free.hyps(1) red_Free.prems(2) by auto
  then show ?case
    by (metis fst_eqD red_Free.hyps(1) red_Free.hyps(3) red_Free.prems(1) snd_eqD)
next
  case (red_Write \<sigma> s0 h0 r l \<sigma>' e)
  then have "edenot e s0 = edenot e s"
    by (metis agrees_search(2) agrees_simps(4) exp_agrees fstI fvC.simps(4))
  then have "\<langle>Cwrite r e, (s, h)\<rangle> \<rightarrow> \<langle>Cskip, (s, h((l, field_val) \<mapsto> VInt (edenot e s0)))\<rangle>"
    by (smt (verit, del_insts) agrees_search(2) agrees_simps(2) agrees_simps(4) domIff fst_eqD fvC.simps(4) red.red_Write red_Write.hyps(1) red_Write.hyps(2) red_Write.hyps(3) red_Write.prems(1) red_Write.prems(2) red_Write.prems(3) snd_conv)
  then show ?case
    by (metis fst_eqD red_Write.hyps(1) red_Write.hyps(4) red_Write.prems(1) red_Write.prems(2) snd_conv)
qed (auto)


lemma aborts_agrees[rule_format]:
  assumes "aborts C \<sigma>"
     and "agrees (fvC C) (fst \<sigma>) s'"
     and "snd \<sigma> = h'"
   shows "aborts C (s', h')"
  using assms
proof (induct rule: aborts.induct)
  case (aborts_Race1 C1 \<sigma> C2)
  then show ?case
    using aborts.aborts_Race1 accesses_agrees writes_agrees by fastforce
next
  case (aborts_Race2 C1 \<sigma> C2)
  then show ?case
    by (metis aborts.aborts_Race2 accesses_agrees agrees_simps(4) fst_conv fvC.simps(8) writes_agrees)
next
  case (aborts_Read E \<sigma> x)
  then show ?case
    by (metis aborts.aborts_Read agrees_simps(3) fst_conv fvC.simps(3) snd_conv)
next
  case (aborts_Write E \<sigma> E')
  then show ?case
    by (metis Un_insert_left aborts.aborts_Write agrees_simps(3) fst_conv fvC.simps(4) snd_conv)
next
  case (aborts_Free E \<sigma>)
  then show ?case
    by (metis (mono_tags, lifting) aborts.aborts_Free agrees_def fst_conv fvC.simps(6) singletonI snd_conv)
qed (auto)

text \<open>Corollaries of Proposition 4.2, useful for automation.\<close>

corollary exp_agrees2[simp]:
  "x \<notin> fvE E \<Longrightarrow> edenot E (s(x := v)) = edenot E s"
  by (rule exp_agrees, simp add: agrees_def)

corollary bexp_agrees2[simp]:
  "x \<notin> fvB B \<Longrightarrow> bdenot B (s(x := v)) = bdenot B s"
by (rule bexp_agrees, simp add: agrees_def)

definition vints where
  "vints = { VInt v |v. True }"

definition vrefs where
  "vrefs = { VRef v |v. True }"

fun well_typed_cmd_aux where
  "well_typed_cmd_aux _ Cskip \<longleftrightarrow> True"
| "well_typed_cmd_aux \<Delta> (Cseq C1 C2) \<longleftrightarrow> well_typed_cmd_aux \<Delta> C1 \<and> well_typed_cmd_aux \<Delta> C2"
| "well_typed_cmd_aux \<Delta> (Cassign x e) \<longleftrightarrow> variables \<Delta> x = Some vints"
| "well_typed_cmd_aux \<Delta> (Cread x r) \<longleftrightarrow> variables \<Delta> x = Some vints \<and> variables \<Delta> r = Some vrefs"
| "well_typed_cmd_aux \<Delta> (Cwrite r e) \<longleftrightarrow> variables \<Delta> r = Some vrefs"
| "well_typed_cmd_aux \<Delta> (Calloc r e) \<longleftrightarrow> variables \<Delta> r = Some vrefs"
| "well_typed_cmd_aux \<Delta> (Cfree r) \<longleftrightarrow> variables \<Delta> r = Some vrefs"
| "well_typed_cmd_aux \<Delta> (Cif _ C1 C2) \<longleftrightarrow> well_typed_cmd_aux \<Delta> C1 \<and> well_typed_cmd_aux \<Delta> C2"
| "well_typed_cmd_aux \<Delta> ({_} C1 {_} || {_} C2 {_}) \<longleftrightarrow> well_typed_cmd_aux \<Delta> C1 \<and> well_typed_cmd_aux \<Delta> C2"
| "well_typed_cmd_aux \<Delta> (Cwhile _ _ C) \<longleftrightarrow> well_typed_cmd_aux \<Delta> C"

(*
lemma update_store_typed:
  assumes "TypedEqui.typed_store \<Delta> s"
      and "variables \<Delta> x = Some V"
      and "v \<in> V"
    shows "TypedEqui.typed_store \<Delta> (s(x \<mapsto> v))"
  sledgehammer
*)

lemma red_keeps_typed_store:
  assumes "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      and "TypedEqui.typed_store \<Delta> (fst \<sigma>)"
      and "well_typed_cmd_aux \<Delta> C"
    shows "TypedEqui.typed_store \<Delta> (fst \<sigma>')"
  using assms
proof (induct rule: red.induct)
  case (red_Assign \<sigma> s h \<sigma>' x e)
  then show ?case
    using TypedEqui.typed_store_update[OF red_Assign(3), of x vints "VInt (edenot e s)"]
    by (metis (mono_tags, lifting) CollectI fstI vints_def well_typed_cmd_aux.simps(3))
next
  case (red_Alloc \<sigma> s h l \<sigma>' x e)
  then show ?case
    using TypedEqui.typed_store_update[OF red_Alloc(4), of x vrefs "VRef (Address l)"]
    by (metis (mono_tags, lifting) CollectI fst_eqD vrefs_def well_typed_cmd_aux.simps(6))
next
  case (red_Read \<sigma> s h r l v \<sigma>' x)
  then show ?case
    using TypedEqui.typed_store_update[OF red_Read(5), of x vints "VInt v"]
    by (metis (mono_tags, lifting) CollectI fstI vints_def well_typed_cmd_aux.simps(4))
qed (simp_all)


definition type_ctxt_heap where
  "type_ctxt_heap = (\<lambda>f. if f = field_val then Some vints else None)"

lemma red_keeps_well_typed_cmd:
  assumes "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    and "well_typed_concrete_heap type_ctxt_heap (snd \<sigma>)"
  shows "well_typed_concrete_heap type_ctxt_heap (snd \<sigma>')"
  using assms
proof (induct rule: red.induct)
  case (red_Alloc \<sigma> s h l \<sigma>' x e)
  then show ?case
    using well_typed_concrete_heap_update[OF red_Alloc(4), of "(l, field_val)" vints "VInt (edenot e s)"]
    by (simp add: type_ctxt_heap_def vints_def)
next
  case (red_Write \<sigma> s h r l \<sigma>' e)
  then show ?case
    using well_typed_concrete_heap_update[OF red_Write(5), of "(l, field_val)" vints "VInt (edenot e s)"]
    by (simp add: type_ctxt_heap_def vints_def)
qed (auto)

lemma well_typed_cmd_red:
  assumes "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      and "well_typed_cmd_aux \<Delta> C"
    shows "well_typed_cmd_aux \<Delta> C'"
  using assms
  by (induct rule: red.induct) (auto)


end
