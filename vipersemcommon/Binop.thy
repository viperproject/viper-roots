theory Binop
imports ViperLang ValueAndBasicState 
begin

datatype (discs_sels) 'a binop_result = BinopTypeFailure | BinopOpFailure | BinopNormal 'a 
text \<open>Binary operealion result, where \<^const>\<open>BinopTypeFailure\<close> indicates that one of the operands has an
incorrect type, \<^const>\<open>BinopOpFailure\<close> indicates that the (well-typed) operealion failed and
\<^term>\<open>BinopNormal res\<close> indicates that the operealion's result is \<^term>\<open>res\<close> \<close>

subsection \<open>Euclidean division and modulo\<close>

text \<open>Viper's division semantics is determined by SMTLIB's division semantics.
For integer division SMTLIB's division semantics is given by the Euclidean division if the divisor is 
nonzero and undefined (but fixed) otherwise.
The Euclidean division \<open>a eucl_div b\<close> is the value \<open>q\<close> such that \<open>a = q*b+r\<close> where \<open>0 \<le> r < |b|\<close>.
Isabelle's built-in integer division is the flooring division (exact division and then rounded to
infinity). 

In the following, we give definitions that express the Euclidean division (and modulo)
in terms of Isabelle's division. The following formulas were originally taken from Boogie's semantics. 

Also, see the theory HOL.SMT, which uses similar equations to express the SMT division and modulo.
\<close>

definition eucl_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "eucl_div a b \<equiv> if b > 0 then a div b else -(a div -b)"

definition eucl_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "eucl_mod a b \<equiv> if b > 0 then a mod b else a mod -b"

text \<open>Isabelle's built-in division fixes division by 0 to 0, so we have a case distinction here.
\<^const>\<open>undefined\<close> in Isabelle is just some fixed (but unknown) value of the correct type.\<close>

definition smt_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "smt_div i1 i2 = (if i2 \<noteq> 0 then eucl_div i1 i2 else undefined)"

definition smt_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "smt_mod i1 i2 = (if i2 \<noteq> 0 then eucl_mod i1 i2 else undefined)"


subsection \<open>Evaluation functions\<close>

fun eval_unop :: "unop \<Rightarrow> 'a val \<Rightarrow> ('a val) binop_result" where
  "eval_unop Not (VBool b) = BinopNormal (VBool (\<not> b))"
| "eval_unop Minus (VInt i) = BinopNormal (VInt (- i))"
| "eval_unop Minus (VPerm r) = BinopNormal (VPerm (- r))"
| "eval_unop _ _ = BinopTypeFailure"

fun eval_int_int:: "int \<Rightarrow> binop \<Rightarrow> int \<Rightarrow> ('a val) binop_result" where
  "eval_int_int a Eq b = BinopNormal (VBool (a = b))"
| "eval_int_int a Neq b = BinopNormal (VBool (a \<noteq> b))"

| "eval_int_int a Add b = BinopNormal (VInt (a + b))"
| "eval_int_int a Sub b = BinopNormal (VInt (a - b))"
| "eval_int_int a Mult b = BinopNormal (VInt (a * b))"
| "eval_int_int a IntDiv b = (if b \<noteq> 0 then BinopNormal (VInt (smt_div a b) ) else BinopOpFailure)"
| "eval_int_int a PermDiv b = (if b \<noteq> 0 then BinopNormal (VPerm (a / b)) else BinopOpFailure)"
| "eval_int_int a Mod b = (if b \<noteq> 0 then BinopNormal (VInt (smt_mod a b)) else BinopOpFailure)"
| "eval_int_int a Gt b = BinopNormal (VBool (a > b))"
| "eval_int_int a Gte b = BinopNormal (VBool (a \<ge> b))"
| "eval_int_int a Lt b = BinopNormal (VBool (a < b))"
| "eval_int_int a Lte b = BinopNormal (VBool (a \<le> b))"
| "eval_int_int _ _ _ = BinopTypeFailure"

fun eval_perm_perm:: "real \<Rightarrow> binop \<Rightarrow> real \<Rightarrow> ('a val) binop_result" where
  "eval_perm_perm a Eq b = BinopNormal (VBool (a = b))"
| "eval_perm_perm a Neq b = BinopNormal (VBool (a \<noteq> b))"

| "eval_perm_perm a Add b = BinopNormal (VPerm (a + b))"
| "eval_perm_perm a Sub b = BinopNormal (VPerm (a - b))"
| "eval_perm_perm a Mult b = BinopNormal (VPerm (a * b))"
| "eval_perm_perm a PermDiv b = (if b \<noteq> 0 then BinopNormal (VPerm (a / b)) else BinopOpFailure)"

| "eval_perm_perm a Gt b = BinopNormal (VBool (a > b))"
| "eval_perm_perm a Gte b = BinopNormal (VBool (a \<ge> b))"
| "eval_perm_perm a Lt b = BinopNormal (VBool (a < b))"
| "eval_perm_perm a Lte b = BinopNormal (VBool (a \<le> b))"
| "eval_perm_perm _ _ _ = BinopTypeFailure"

fun eval_bool_bool:: "bool \<Rightarrow> binop \<Rightarrow> bool \<Rightarrow> ('a val) binop_result" where
  "eval_bool_bool a Eq b = BinopNormal (VBool (a = b))"
| "eval_bool_bool a Neq b = BinopNormal (VBool (a \<noteq> b))"
| "eval_bool_bool a  Or b = BinopNormal (VBool (a \<or> b))"
| "eval_bool_bool a And b = BinopNormal (VBool (a \<and> b))"
| "eval_bool_bool a BImp b = BinopNormal (VBool (a \<longrightarrow> b))"
| "eval_bool_bool _ _ _ = BinopTypeFailure"

fun eval_int_perm :: "int \<Rightarrow> binop \<Rightarrow> real \<Rightarrow> ('a val) binop_result" where
  "eval_int_perm a Mult b = BinopNormal (VPerm (a * b))"
| "eval_int_perm a PermDiv b = (if b \<noteq> 0 then BinopNormal (VPerm (a / b)) else BinopOpFailure)"
| "eval_int_perm _ _ _ = BinopTypeFailure" \<comment>\<open>we do not lift the remaining operealions for now 
                                             (also not permitted by the Viper type checker)\<close>

fun eval_perm_int :: "real \<Rightarrow> binop \<Rightarrow> int \<Rightarrow> ('a val) binop_result" where
  "eval_perm_int a Mult b = BinopNormal (VPerm (a * b))"
| "eval_perm_int a PermDiv b = (if b \<noteq> 0 then BinopNormal (VPerm (a / (real_of_int b))) else BinopOpFailure)"
| "eval_perm_int _ _ _ = BinopTypeFailure" \<comment>\<open>we do not lift the remaining operealions for now 
                                             (also not permitted by the Viper type checker)\<close>

fun eval_ref_ref :: "ref \<Rightarrow> binop \<Rightarrow> ref \<Rightarrow> ('a val) binop_result" where
  "eval_ref_ref a Eq b =  BinopNormal (VBool (a = b))"
| "eval_ref_ref a Neq b = BinopNormal (VBool (a \<noteq> b))"
| "eval_ref_ref _ _ _ = BinopTypeFailure"

fun eval_abs_abs :: "'a \<Rightarrow> binop \<Rightarrow> 'a \<Rightarrow> ('a val) binop_result" where
  "eval_abs_abs a Eq b =  BinopNormal (VBool (a = b))"
| "eval_abs_abs a Neq b = BinopNormal (VBool (a \<noteq> b))"
| "eval_abs_abs _ _ _ = BinopTypeFailure"

text\<open>For \<^const>\<open>eval_abs_abs\<close>, we support equality and inequality of abstract values that potentially 
have different domain types, which is more liberal than the Viper type checker and thus fine. 
We could allow equality and inequality for all combinations of values, but for now we stay closer to 
the type checker for the non-abstract values. 
Side remark: There was a case where the more liberal equality made things simpler. If we run into 
such a case again, we can rethink how (in)equality is reduced.\<close>

fun eval_binop :: "'a val \<Rightarrow> binop \<Rightarrow> 'a val \<Rightarrow> ('a val) binop_result" where
  "eval_binop (VInt a) op (VInt b) = eval_int_int a op b"
| "eval_binop (VPerm a) op (VPerm b) = eval_perm_perm a op b"
| "eval_binop (VBool a) op (VBool b) = eval_bool_bool a op b"
| "eval_binop (VInt a) op (VPerm b) = eval_int_perm a op b"
| "eval_binop (VPerm a) op (VInt b) = eval_perm_int a op b"
| "eval_binop (VRef a) op (VRef b) = eval_ref_ref a op b"
| "eval_binop (VAbs a) op (VAbs b) = eval_abs_abs a op b"
| "eval_binop _ _ _ = BinopTypeFailure" \<comment>\<open>we do not lift the remaining operealions for now 
                                             (also not permitted by the Viper type checker)\<close>

lemma eval_binop_eq:
  assumes "(is_VBool v1 \<and> is_VBool v2) \<or> (is_VInt v1 \<and> is_VInt v2) \<or> (is_VPerm v1 \<and> is_VPerm v2) \<or>
           (is_VRef v1 \<and> is_VRef v2) \<or> (is_VAbs v1 \<and> is_VAbs v2)"
  shows "eval_binop v1 Eq v2 = BinopNormal (VBool (v1 = v2))"
  using assms
  by (cases v1; cases v2; auto)
            
lemma eval_binop_neq:
  assumes "(is_VBool v1 \<and> is_VBool v2) \<or> (is_VInt v1 \<and> is_VInt v2) \<or> (is_VPerm v1 \<and> is_VPerm v2) \<or>
           (is_VRef v1 \<and> is_VRef v2) \<or> (is_VAbs v1 \<and> is_VAbs v2)"
  shows "eval_binop v1 Neq v2 = BinopNormal (VBool (v1 \<noteq> v2))"
  using assms
  by (cases v1; cases v2; auto)

lemma eval_binop_failure: "eval_binop v1 bop v2 = BinopOpFailure \<Longrightarrow> bop \<in> {IntDiv, PermDiv, Mod}"  
  by (erule eval_binop.elims; simp_all; cases bop; auto)

lemma eval_binop_failure_int: "bop \<in> {IntDiv, Mod} \<Longrightarrow> eval_binop v1 bop v2 = BinopOpFailure \<Longrightarrow> v2 = VInt(0)"
  by (erule eval_binop.elims) (auto split: if_split_asm)

lemma eval_binop_failure_perm: "bop = PermDiv \<Longrightarrow> eval_binop v1 bop v2 = BinopOpFailure \<Longrightarrow> v2 = VPerm(0) \<or> v2 = VInt(0)"
  by (erule eval_binop.elims) (auto split: if_split_asm)

lemma eval_binop_not_failure: " bop \<notin> {IntDiv, PermDiv, Mod} \<Longrightarrow> eval_binop v1 bop v2 \<noteq> BinopOpFailure"  
  using eval_binop_failure
  by blast

lemma eval_binop_not_failure_2: "bop \<in> {IntDiv, Mod, PermDiv} \<Longrightarrow> eval_binop v1 bop v2 = BinopNormal v' \<Longrightarrow> v2 \<noteq> VPerm(0) \<and> v2 \<noteq> VInt(0)"
  by (erule eval_binop.elims) (auto split: if_split_asm)

text \<open>The result \<^term>\<open>Some (v1,v2)\<close> expresses that the binary operealor is lazy in the case where
the first operand is \<^term>\<open>v1\<close> and the result of the binary operealor evaluation in this case is \<^term>\<open>v2\<close>.\<close>

fun binop_lazy :: "binop \<Rightarrow> ('a val \<times> 'a val) option" where 
  "binop_lazy Or = Some (VBool True, VBool True)"
| "binop_lazy And = Some (VBool False, VBool False)"
| "binop_lazy BImp = Some (VBool False, VBool True)"
| "binop_lazy _ = None"

fun eval_binop_lazy :: "'a val \<Rightarrow> binop \<Rightarrow> ('a val) option" where
  "eval_binop_lazy (VBool True) Or = Some (VBool True)"
| "eval_binop_lazy (VBool False) And = Some (VBool False)"
| "eval_binop_lazy (VBool False) BImp = Some (VBool True)"
| "eval_binop_lazy _ _ = None"

lemma eval_binop_lazy_iff: "binop_lazy bop = Some (v1,v2) \<longleftrightarrow> eval_binop_lazy v1 bop = Some v2"
  apply rule
  apply (erule binop_lazy.elims; simp)
  apply (erule eval_binop_lazy.elims; simp)
  done

lemma eval_binop_lazy_iff_2: "binop_lazy bop = None \<longleftrightarrow> (\<forall>v1. eval_binop_lazy v1 bop = None)"
  apply rule
  apply (erule binop_lazy.elims; simp)
  apply (cases bop) 
  apply simp_all
  by ( metis eval_binop_lazy.simps(1-3) option.distinct(1))+

subsection \<open>Binop Properties\<close>

lemma eval_binop_lazy_some_bool:
  assumes "eval_binop_lazy a op = Some x"
  shows "\<exists>b. a = VBool b"
  using assms by (cases a) auto

lemma op_bimp_and_or_reduces_bool:
  assumes "op = Or \<or> op = And \<or> op = BImp"
      and "is_BinopNormal (eval_binop a op b)"
    shows "\<exists>b'. b = VBool b'"
  apply (cases op)  
  using assms apply auto
  by (cases a; cases b, auto)+

lemma eval_binop_implies_eval_normal:
  assumes "eval_binop_lazy a op = Some x"
      and "eval_binop a op b = BinopNormal y"
    shows "x = y"
  apply (cases op)
  using assms(1) apply auto
    apply (insert assms(2))
    apply (cases "a = VBool True")  
     apply (cases "\<exists>vb. b = VBool vb")
      apply fastforce
     apply (metis binop_result.disc(3) op_bimp_and_or_reduces_bool)
    apply (metis (full_types) eval_binop_lazy.simps(17) eval_binop_lazy_some_bool option.distinct(1))
   apply (cases "a = VBool False")
    apply (cases "\<exists>vb. b= VBool vb")
     apply fastforce    
    apply (metis binop_result.disc(3) op_bimp_and_or_reduces_bool)  
  using eval_binop_lazy_some_bool apply fastforce
  apply (cases "a = VBool False")
   apply (cases "\<exists>vb. b= VBool vb")
    apply fastforce
   apply (metis assms(2) binop_result.disc(3) op_bimp_and_or_reduces_bool)
  using eval_binop_lazy_some_bool by fastforce


end