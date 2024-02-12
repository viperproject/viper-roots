section \<open>Basic definitions for Viper values, states, and semantics\<close>

text \<open>The meaning of a Viper state and the behaviour of Viper statements depends on different parameters 
(for example, whether predicates are treated equi- or isorecursively). This theory provides the 
definitions that should be used by actual instantiations of the Viper state and of a Viper semantics.
This includes a definition of the Viper values.\<close>

theory ValueAndBasicState
imports ViperLang PosPerm HOL.Real
begin

subsection \<open>Heap locations, references, and other basic types\<close>

type_synonym address = "nat" (* Infinite but countable *)
type_synonym field_name = "string"
type_synonym heap_loc = "address \<times> field_name"

text \<open>Viper labels\<close>
type_synonym label = "string"

datatype ref = is_address: Address (the_address: address) | Null

subsection \<open>Viper (extended) values\<close>

text \<open>The abstract type parameter in the values is the carrier type for domain values\<close>
datatype (discs_sels) 'a val = VInt int | VBool bool | VPerm real | VRef ref | VAbs 'a

type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)

fun val_of_lit :: "lit \<Rightarrow> 'a val" where
  "val_of_lit (LBool b) = VBool b"
| "val_of_lit (LInt n) = VInt n"
| "val_of_lit (LPerm r) = VPerm r"
| "val_of_lit LNull = VRef Null"


text \<open>Predicate location\<close>
type_synonym 'a predicate_loc = "predicate_ident \<times> 'a val list"

text \<open>Some expressions may be not be well-defined and thus, they do not reduce to any "normal" value in
\<^typ>\<open>'a val\<close>. To capture this, we define extended values, which are either a normal value or a failure
value. Failure represents one of the following:

- Reading x.f without permission
- Dividing by 0
- Label that does not exist
- Function calls that do not satisfy the precondition (abstract)
- Function calls in general is just "reducing"?
\<close>
datatype 'a extended_val = Val (the_val: "'a val") | VFailure

    
subsection \<open>Masks\<close>

text \<open>Abstract permission ('p::pos_perm) masks\<close>
type_synonym ('b, 'p) abstract_mask = "'b \<Rightarrow> 'p"

text \<open>Depending on the treatment of predicates and wands, a Viper state may contain different kinds of 
permission ('p::pos_perm) masks. \<^typ>\<open>('b, 'p::pos_perm) abstract_mask\<close> captures the general type.\<close>

definition zero_mask :: "('b, 'p::pos_perm) abstract_mask" where "zero_mask hl = pnone"
definition add_masks :: "('b, 'p::pos_perm) abstract_mask \<Rightarrow> ('b, 'p::pos_perm) abstract_mask \<Rightarrow> ('b, 'p::pos_perm) abstract_mask" where
  "add_masks \<pi>1 \<pi>2 hl = (\<pi>1 hl + \<pi>2 hl)"

lemma padd_pos:
  assumes "p \<noteq> pnone"
  shows "p + q \<noteq> pnone"
  by (metis assms leD pperm_pnone_pgt sum_larger)

lemma add_masks_pos: 
  assumes "\<pi>1 hl \<noteq> pnone"
  shows "(add_masks \<pi>1 \<pi>2) hl \<noteq> pnone"
  using assms
  unfolding add_masks_def
  by (simp add: padd_pos)

lemma add_masks_comm: "add_masks \<pi>1 \<pi>2 = add_masks \<pi>2 \<pi>1"
  unfolding add_masks_def
  by (simp add: add.commute)

lemma add_masks_assoc: "add_masks (add_masks \<pi>1 \<pi>2) \<pi>3 = add_masks \<pi>1 (add_masks \<pi>2 \<pi>3)"
  unfolding add_masks_def
  by (simp add: add.commute add.left_commute)

lemma add_masks_zero_mask: "add_masks m zero_mask = m"
  unfolding add_masks_def zero_mask_def
  by simp

text \<open>Heap permission ('p::pos_perm) mask\<close>
type_synonym 'p mask = "(heap_loc, 'p) abstract_mask"

text \<open>Partial heap\<close>
type_synonym 'a partial_heap = "heap_loc \<rightharpoonup> 'a val"

definition wf_mask_simple :: "('p::pos_perm) mask \<Rightarrow> bool" where
  "wf_mask_simple \<pi> \<longleftrightarrow> (\<forall>hl. pwrite \<ge> (\<pi> hl))"

lemma wf_mask_simpleI:
  assumes "\<And>hl. pwrite \<ge> \<pi> hl"
  shows "wf_mask_simple \<pi>"
  by (simp add: assms wf_mask_simple_def)

text \<open>Every kind of Viper semantics contains a permission ('p::pos_perm) mask for heap values, which is modelled by
\<^typ>\<open>('p::pos_perm) mask\<close>. Such a heap permission ('p::pos_perm) mask is well-formed iff there is at most one permission to each
heap location (\<^const>\<open>wf_mask_simple\<close>)\<close>

lemma wf_zero_mask: "wf_mask_simple zero_mask"
  unfolding zero_mask_def wf_mask_simple_def
  using all_pos by blast

lemma zero_mask_neutral: "add_masks m zero_mask = m"
  unfolding add_masks_def zero_mask_def
  by simp

lemma padd_pgte: "(p::('p::pos_perm)) + q \<ge> p"
  using sum_larger by blast

lemma pgte_transitive: "(p::('p::pos_perm)) \<ge> q \<Longrightarrow> q \<ge> r \<Longrightarrow> p \<ge> r"
  by auto

lemma wf_mask_simple_false_preserved:
  assumes "\<not> wf_mask_simple m"
  shows "\<not> wf_mask_simple (add_masks m m')"  
  by (metis add_masks_def assms dual_order.trans padd_pgte wf_mask_simple_def)

text \<open>To handle propagation of failure: If one sub_pure_exp fails, then the whole expression fails\<close>

fun sub_pure_exp :: "pure_exp \<Rightarrow> pure_exp set" where
  "sub_pure_exp (Unop _ e) = {e}"
| "sub_pure_exp (Binop e _ _) = {e}"
| "sub_pure_exp (FieldAcc e _) = {e}"
| "sub_pure_exp (Let e _) = {e}"
| "sub_pure_exp (Perm e _) = {e}"
| "sub_pure_exp (CondExp e _ _) = {e}"
| "sub_pure_exp (PermPred _ exps) = List.set exps"
| "sub_pure_exp (FunApp _ exps) = List.set exps"
| "sub_pure_exp (Unfolding _ exps e) = List.set exps \<union> {e}"
| "sub_pure_exp _ = {}"

definition predicate_body :: "program \<Rightarrow> predicate_ident \<Rightarrow> assertion" where
  "predicate_body Pr p = the (predicate_decl.body (the (program.predicates Pr p)))"

subsection \<open>Old states\<close>

abbreviation old_label :: label
  where "old_label \<equiv> ''old''"

text \<open>The formalization only supports labeled old expressions \<^term>\<open>Old lbl e\<close>. To express standard
old expressions, we use the predefined label \<^const>\<open>old_label\<close>. That is, standard old expressions 
are expressed as \<^term>\<open>Old old_label e\<close>.
TODO: well-formedness check should ensure that \<^const>\<open>old_label\<close> is never defined as a new label in
the program.\<close>

section \<open>Interpretation: Functions, predicates, types (interp and type context)\<close>

text \<open>'v represents the type of the "domain" values, and 'a the type of Viper resource states\<close>

record ('v, 'a) interp =
  domains :: "'v \<Rightarrow> abs_type"
  predicates :: "'v predicate_loc \<rightharpoonup> 'a set"
  funs :: "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'a \<rightharpoonup> 'v val"

type_synonym type_context = "var \<rightharpoonup> vtyp"

section \<open>Basic defintions for types\<close>

fun set_from_type :: "('v \<Rightarrow> abs_type) \<Rightarrow> vtyp \<Rightarrow> 'v val set" where
  "set_from_type \<Delta> TInt = {VInt n |n. True}"
| "set_from_type \<Delta> TBool = {VBool True, VBool False}"
| "set_from_type \<Delta> TPerm = {VPerm r |r. True}"
| "set_from_type \<Delta> TRef = {VRef r |r. True}"
| "set_from_type \<Delta> (TAbs t) = {VAbs v |v. \<Delta> v = t}"

definition has_type :: "('v \<Rightarrow> abs_type) \<Rightarrow> vtyp \<Rightarrow> 'v val \<Rightarrow> bool" where
  "has_type \<Delta> t v \<longleftrightarrow> v \<in> set_from_type \<Delta> t"

fun get_type :: "('v \<Rightarrow> abs_type) \<Rightarrow> 'v val \<Rightarrow> vtyp" where
  "get_type \<Delta> (VInt _) = TInt"
| "get_type \<Delta> (VBool _) = TBool"
| "get_type \<Delta> (VPerm _) = TPerm"
| "get_type \<Delta> (VRef _) = TRef"
| "get_type \<Delta> (VAbs v) = TAbs (\<Delta> v)"

lemma has_type_get_type:
  "has_type \<Delta> t v \<longleftrightarrow> get_type \<Delta> v = t"
  unfolding has_type_def
  by (cases t; cases v; auto)

lemma has_type_simps [simp]:
  "has_type \<Delta> ty (VInt n) \<longleftrightarrow> ty = TInt"
  "has_type \<Delta> TInt v \<longleftrightarrow> (\<exists> n. v = VInt n)"
  "has_type \<Delta> ty (VBool b) \<longleftrightarrow> ty = TBool"
  "has_type \<Delta> TBool v \<longleftrightarrow> (\<exists> n. v = VBool n)"
  "has_type \<Delta> ty (VPerm p) \<longleftrightarrow> ty = TPerm"
  "has_type \<Delta> TPerm v \<longleftrightarrow> (\<exists> n. v = VPerm n)"
  "has_type \<Delta> ty (VRef r) \<longleftrightarrow> ty = TRef"
  "has_type \<Delta> TRef v \<longleftrightarrow> (\<exists> n. v = VRef n)"
  "has_type \<Delta> ty (VAbs t) \<longleftrightarrow> (\<exists> a. ty = TAbs a \<and> \<Delta> t = a)"
  "has_type \<Delta> (TAbs a) v \<longleftrightarrow> (\<exists> t. v = VAbs t \<and> \<Delta> t = a)"
  by ((cases ty)?; auto simp add:has_type_def)+

lemma has_type_val_of_lit [simp]:
  "has_type \<Delta> ty (val_of_lit lit) \<longleftrightarrow> ty = type_of_lit lit"
  by (cases lit; auto)

(* Fields are well-typed *)
(* Maybe say that a location is allocated or not *)
definition well_typed_heap :: "program \<Rightarrow> ('v \<Rightarrow> abs_type) \<Rightarrow> 'v partial_heap \<Rightarrow> bool" where
  "well_typed_heap Pr \<Delta> h \<longleftrightarrow> (\<forall>hl f. declared_fields Pr f \<noteq> None \<and> h (hl, f) \<noteq> None \<longrightarrow> has_type \<Delta> (the (declared_fields Pr f)) (the (h (hl, f))))"

end