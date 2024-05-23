theory ParImp
  imports ViperCommon.SepAlgebra ViperCommon.SepLogic "../vipersemabstract/Instantiation" VHelper
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

datatype exp =
Evar var
| Elit int
| Ebinop exp "int \<Rightarrow> int \<Rightarrow> int" exp

datatype bexp =
Beq exp exp
| Band bexp bexp
| Bnot bexp

datatype cmd =
  Cskip
| Cassign var exp
| Cread var var (* second var needs to be a non-null ref *)
| Cwrite var exp 
| Calloc var exp
| Cdispose var
| Cseq cmd cmd
| Cpar cmd cmd (infixl "||" 60)
| Cif bexp cmd cmd
| Cwhile bexp cmd


primrec edenot :: "exp \<Rightarrow> stack \<Rightarrow> int"
  where
  "edenot (Evar v) s = the_int (the (s v))"
| "edenot (Elit n) s = n"
| "edenot (Ebinop e1 op e2) s = op (edenot e1 s) (edenot e2 s)"

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
| red_If1[intro]: "bdenot b (fst \<sigma>) \<Longrightarrow> \<langle>Cif B C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C1, \<sigma>\<rangle>"
| red_If2[intro]: "\<not> bdenot b (fst \<sigma>) \<Longrightarrow> \<langle>Cif B C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C2, \<sigma>\<rangle>"
| red_Par1[elim]: "\<lbrakk> \<langle>C1, \<sigma>\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle> \<rbrakk> \<Longrightarrow> \<langle>C1 || C2, \<sigma>\<rangle> \<rightarrow> \<langle>C1' || C2, \<sigma>'\<rangle>" 
| red_Par2[elim]: "\<lbrakk> \<langle>C2, \<sigma>\<rangle> \<rightarrow> \<langle>C2', \<sigma>'\<rangle> \<rbrakk> \<Longrightarrow> \<langle>C1 || C2, \<sigma>\<rangle> \<rightarrow> \<langle>C1 || C2', \<sigma>'\<rangle>"
| red_Par3[intro]: "\<langle>Cskip || Cskip, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>\<rangle>"
| red_Loop[intro]: "\<langle>Cwhile b C, \<sigma>\<rangle> \<rightarrow> \<langle>Cif b (Cseq C (Cwhile b C)) Cskip, \<sigma>\<rangle>"
| red_Assign[intro]:"\<lbrakk> \<sigma> = (s,h); \<sigma>' = (s(x \<mapsto> VInt (edenot e s)), h) \<rbrakk> \<Longrightarrow> \<langle>Cassign x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"

| red_Alloc[intro]: "\<lbrakk> \<sigma> = (s,h); (l, field_val) \<notin> dom h; \<sigma>' = (s(x \<mapsto> VRef (Address l)), h((l, field_val) \<mapsto> VInt (edenot e s))) \<rbrakk> 
  \<Longrightarrow> \<langle>Calloc x e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Read[intro]:  "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); h (l, field_val) = Some (VInt v); \<sigma>' = (s(x \<mapsto> VInt v), h) \<rbrakk>
  \<Longrightarrow> \<langle>Cread x r, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Free[intro]:  "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); \<sigma>' = (s, h((l, field_val) := None)) \<rbrakk> \<Longrightarrow> \<langle>Cdispose r, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"
| red_Write[intro]: "\<lbrakk> \<sigma> = (s,h); s r = Some (VRef (Address l)); (l, field_val) \<in> dom h; \<sigma>' = (s, h((l, field_val) \<mapsto> VInt (edenot e s))) \<rbrakk>
  \<Longrightarrow> \<langle>Cwrite r e, \<sigma>\<rangle> \<rightarrow> \<langle>Cskip, \<sigma>'\<rangle>"

inductive_cases red_par_cases: "\<langle>Cpar C1 C2, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
inductive_cases red_write_cases: "\<langle>Cwrite r e, \<sigma>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"


subsubsection \<open>Abort semantics\<close>

definition get_address where
  "get_address x = the_address (the_ref (the x))"

lemma get_address_simp:
  assumes "x = Some (VRef (Address l))"
  shows "get_address x = l"
  by (simp add: assms get_address_def)

primrec
  accesses :: "cmd \<Rightarrow> stack \<Rightarrow> address set"
where
    "accesses Cskip            s = {}"
  | "accesses (Cassign x E)    s = {}"
  | "accesses (Cread x r)      s = { get_address (s r) }"
  | "accesses (Cwrite r E)    s = { get_address (s r) }"
  | "accesses (Calloc x E)     s = {}"
  | "accesses (Cdispose r)     s = {get_address (s r)}"
  | "accesses (Cseq C1 C2)     s = accesses C1 s"
  | "accesses (C1 || C2)     s = accesses C1 s \<union> accesses C2 s"
  | "accesses (Cif B C1 C2)    s = {}"
  | "accesses (Cwhile B C)     s = {}"

primrec
  writes :: "cmd \<Rightarrow> stack \<Rightarrow> address set"
where
    "writes Cskip            s = {}"
  | "writes (Cassign x E)    s = {}"
  | "writes (Cread x r)      s = {}"
  | "writes (Cwrite r E)    s = {get_address (s r)}"
  | "writes (Calloc x E)     s = {}"
  | "writes (Cdispose r)     s = {get_address (s r)}"
  | "writes (Cseq C1 C2)     s = writes C1 s"
  | "writes (C1 || C2)     s = writes C1 s \<union> writes C2 s"
  | "writes (Cif B C1 C2)    s = {}"
  | "writes (Cwhile B C)     s = {}"

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


inductive_cases aborts_write_elim[elim]: "aborts (Cwrite r e) \<sigma>"

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
| "fvC (Cdispose r)   = {r}"
| "fvC (Cseq C1 C2)     = (fvC C1 \<union> fvC C2)"
| "fvC (Cpar C1 C2)     = (fvC C1 \<union> fvC C2)"
| "fvC (Cif B C1 C2)    = (fvB B \<union> fvC C1 \<union> fvC C2)"
| "fvC (Cwhile B C)     = (fvB B \<union> fvC C)"


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
| "wrC (Cdispose E)    = {}"
| "wrC (Cseq C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cpar C1 C2)    = (wrC C1 \<union> wrC C2)"
| "wrC (Cif B C1 C2)   = (wrC C1 \<union> wrC C2)"
| "wrC (Cwhile B C)    = (wrC C)"


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

subsection \<open>Variable erasure\<close>

text \<open>The following function erases all assignments and reads to
  variables in the set @{term X}.\<close>

(* TODO: What is the point? *)
primrec 
  rem_vars :: "var set \<Rightarrow> cmd \<Rightarrow> cmd"
where
    "rem_vars X Cskip          = Cskip"
  | "rem_vars X (Cassign x E)  = (if x \<in> X then Cseq Cskip Cskip else Cassign x E)"
  | "rem_vars X (Cread x E)    = (if x \<in> X then Cseq Cskip Cskip else Cread x E)"
  | "rem_vars X (Cwrite E E')  = Cwrite E E'"
  | "rem_vars X (Calloc x E)   = Calloc x E"
  | "rem_vars X (Cdispose E)   = Cdispose E"
  | "rem_vars X (Cseq C1 C2)   = Cseq (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cpar C1 C2)   = Cpar (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cif B C1 C2)  = Cif B (rem_vars X C1) (rem_vars X C2)"
  | "rem_vars X (Cwhile B C)   = Cwhile B (rem_vars X C)"


text \<open>Properties of variable erasure:\<close>

lemma accesses_remvars: "accesses (rem_vars X C) s \<subseteq> accesses C s"
by (induct C arbitrary: X s, simp_all, fast)

lemma writes_remvars[simp]:
  "writes (rem_vars X C) = writes C"
by (rule ext, induct C arbitrary: X, simp_all)

lemma skip_simps[simp]: 
  "\<not> red Cskip \<sigma> C' \<sigma>'"
  "\<not> aborts Cskip \<sigma>"
  "(rem_vars X C = Cskip) \<longleftrightarrow> (C = Cskip)"
  "(Cskip = rem_vars X C) \<longleftrightarrow> (C = Cskip)"
  by (auto elim: aborts.cases red.cases)
   (induct C, auto split: if_split_asm)+

lemma disjoint_minus: "disjoint (X - Z) Y = disjoint X (Y - Z)"
  by (auto simp add: disjoint_def)

lemma aux_red[rule_format]:
  "red C \<sigma> C' \<sigma>' \<Longrightarrow> \<forall>X C1. C = rem_vars X C1 \<longrightarrow> disjoint X (fvC C) \<longrightarrow> \<not> aborts C1 \<sigma> \<longrightarrow>
   (\<exists>C2 s2. red C1 \<sigma> C2 (s2,snd \<sigma>') \<and> rem_vars X C2 = C' \<and> agrees (-X) (fst \<sigma>') s2)"
  sorry
(*
apply (erule_tac red.induct, simp_all, tactic \<open>ALLGOALS (clarify_tac @{context})\<close>)
apply (case_tac C1, simp_all split: if_split_asm, (fastforce simp add: agrees_def)+)
apply (case_tac[1-5] C1a, simp_all split: if_split_asm, (fastforce intro: agrees_refl)+)
apply (case_tac[!] C1, simp_all split: if_split_asm)
apply (tactic \<open>TRYALL (clarify_tac @{context})\<close>, simp_all add: disjoint_minus [THEN sym])
apply (fastforce simp add: agrees_def)+
apply (intro exI conjI, rule_tac v=v in red_Alloc, (fastforce simp add: agrees_def)+)
done
*)

lemma aborts_remvars:
  "aborts (rem_vars X C) \<sigma> \<Longrightarrow> aborts C \<sigma>"
apply (induct C arbitrary: X \<sigma>, erule_tac[!] aborts.cases, simp_all split: if_split_asm)
apply (tactic \<open>TRYALL (fast_tac @{context})\<close>)
apply (clarsimp, rule, erule contrapos_nn, simp, erule disjoint_search, rule accesses_remvars)+
done

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



lemma red_agrees[rule_format]:
  assumes "red C \<sigma> C' \<sigma>'"
      and "agrees X (fst \<sigma>) s"
      and "snd \<sigma> = h"
      and "fvC C \<subseteq> X"
    shows "\<exists>s' h'. red C (s, h) C' (s', h') \<and> agrees X (fst \<sigma>') s' \<and> snd \<sigma>' = h'"
  using assms
proof (induct rule: red.induct)
  case (red_If1 b \<sigma> B C1 C2)
  then show ?case
    using bdenot.simps(3) by blast
next
  case (red_If2 b \<sigma> B C1 C2)
  then show ?case using bdenot.simps(3) by blast
next
  case (red_Assign \<sigma> s h \<sigma>' x e)
  then show ?case sorry
next
  case (red_Read \<sigma> s h e v \<sigma>' x)
  then show ?case sorry
next
  case (red_Write \<sigma> s h e \<sigma>' e')
  then show ?case sorry
next
  case (red_Alloc \<sigma> s h v \<sigma>' x e)
  then show ?case sorry
next
  case (red_Free \<sigma> s h \<sigma>' e)
  then show ?case sorry
qed (auto)


lemma aborts_agrees[rule_format]:
  assumes "aborts C \<sigma>"
     and "agrees (fvC C) (fst \<sigma>) s'"
     and "snd \<sigma> = h'"
   shows "aborts C (s', h')"
  using assms
proof (induct rule: aborts.induct)
  case (aborts_Race1 C1 \<sigma> C2)
  then show ?case sorry
next
  case (aborts_Race2 C1 \<sigma> C2)
  then show ?case sorry
next
  case (aborts_Read E \<sigma> x)
  then show ?case sorry
next
  case (aborts_Write E \<sigma> E')
  then show ?case sorry
next
  case (aborts_Free E \<sigma>)
  then show ?case sorry
qed (auto)
(*
by (erule aborts.induct, simp_all, auto simp add: writes_agrees accesses_agrees exp_agrees, 
    auto simp add: agrees_def)
*)
text \<open>Corollaries of Proposition 4.2, useful for automation.\<close>

corollary exp_agrees2[simp]:
  "x \<notin> fvE E \<Longrightarrow> edenot E (s(x := v)) = edenot E s"
by (rule exp_agrees, simp add: agrees_def)

corollary bexp_agrees2[simp]:
  "x \<notin> fvB B \<Longrightarrow> bdenot B (s(x := v)) = bdenot B s"
by (rule bexp_agrees, simp add: agrees_def)




end