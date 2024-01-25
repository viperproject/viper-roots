theory DeBruijn
  imports Main ValueAndBasicState ViperLang
begin

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

(* Fields are well-typed *)
(* Maybe say that a location is allocated or not *)
definition well_typed_heap :: "program \<Rightarrow> ('v \<Rightarrow> abs_type) \<Rightarrow> 'v partial_heap \<Rightarrow> bool" where
  "well_typed_heap Pr \<Delta> h \<longleftrightarrow> (\<forall>hl f. declared_fields Pr f \<noteq> None \<and> h (hl, f) \<noteq> None \<longrightarrow> has_type \<Delta> (the (declared_fields Pr f)) (the (h (hl, f))))"

definition shift :: "nat \<Rightarrow> (var \<Rightarrow> 'a option) \<Rightarrow> var \<Rightarrow> 'a option"
  where "shift n f x \<equiv> if x < n then None else f (x-n)"

definition unshift :: "nat \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> (var \<rightharpoonup> 'v)" where
  "unshift n \<sigma> m = \<sigma> (m - n)"

definition unshift_2 :: "nat \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> (var \<rightharpoonup> 'v)" where \<comment>\<open>TODO: this definition makes more sense than \<^const>\<open>unshift\<close>\<close>
  "unshift_2 n \<sigma> m = \<sigma> (m + n)"

definition shift_and_add :: "(var \<rightharpoonup> 'v) \<Rightarrow> 'v \<Rightarrow> (var \<rightharpoonup> 'v)" where
  "shift_and_add \<sigma> x = (\<lambda>m. \<sigma> (m - 1))(0 \<mapsto> x)"

lemma shift_1_shift_and_add: "shift_and_add f y = (shift 1 f)(0 \<mapsto> y)"
  unfolding shift_def shift_and_add_def
  by auto

lemma unshift_shift_id: "unshift_2 n (shift n f) = f"
  unfolding unshift_2_def shift_def
  by simp

lemma unshift_shift_id_2:
  assumes "\<And>x. x \<ge> n \<Longrightarrow> g x = shift n f x"
  shows "unshift_2 n g = f"
  using assms
  unfolding shift_def unshift_2_def
  by simp

lemma unshift_shift_and_add_id: "unshift_2 (Suc 0) (shift_and_add f x) = f"
  apply (rule unshift_shift_id_2)
  unfolding shift_and_add_def shift_def
  by simp

lemma ran_shift: "ran (shift n f) \<subseteq> ran f"
  unfolding shift_def ran_def
  by auto

lemma ran_shift_and_add: "ran (shift_and_add f y) = ran f \<union> {y}"
  unfolding shift_and_add_def ran_def
  by force


(*
definition unshift_type_context :: "(var \<rightharpoonup> 'v) \<Rightarrow> 'v \<Rightarrow> (var \<rightharpoonup> 'v)" where
  "unshift_type_context \<sigma> x = (\<lambda>m. \<sigma> (Suc m))"
*)
definition declare_var :: "('v \<Rightarrow> abs_type) \<Rightarrow> vtyp \<Rightarrow> 'v store \<Rightarrow> 'v store set" where
  "declare_var \<Delta> ty \<sigma> = {shift_and_add \<sigma> v |v. v \<in> set_from_type \<Delta> ty}"

definition assign :: "'v store \<Rightarrow> var \<Rightarrow> 'v val \<Rightarrow> 'v store" where
  "assign \<sigma> x v  = \<sigma>(x := Some v)"

definition havoc_var :: "('v \<Rightarrow> abs_type) \<Rightarrow> var \<Rightarrow> vtyp \<Rightarrow> 'v store \<Rightarrow> 'v store set" where
  "havoc_var \<Delta> x ty \<sigma> = {assign \<sigma> x v |v. v \<in> set_from_type \<Delta> ty}"

fun havoc_var_state :: "('v \<Rightarrow> abs_type) \<Rightarrow> var \<Rightarrow> vtyp \<Rightarrow> ('v store \<times> 'a) \<Rightarrow> ('v store \<times> 'a) set" where
  "havoc_var_state \<Delta> x ty (\<sigma>, \<gamma>) = {(assign \<sigma> x v, \<gamma>) |v. v \<in> set_from_type \<Delta> ty}"

fun havoc_list :: "('v \<Rightarrow> abs_type) \<Rightarrow> (var \<times> vtyp) list \<Rightarrow> 'v store \<Rightarrow> 'v store set" where
  "havoc_list \<Delta> [] \<sigma> = {\<sigma>}"
| "havoc_list \<Delta> ((x, ty) # q) \<sigma> = (\<Union>\<sigma>' \<in> havoc_list \<Delta> q \<sigma>. havoc_var \<Delta> x ty \<sigma>')"

fun havoc_list_state :: "('v \<Rightarrow> abs_type) \<Rightarrow> (var \<times> vtyp) list \<Rightarrow> ('v store \<times> 'a) \<Rightarrow> ('v store \<times> 'a) set" where
  "havoc_list_state \<Delta> l (\<sigma>, \<gamma>) = { (\<sigma>', \<gamma>) |\<sigma>'. \<sigma>' \<in> havoc_list \<Delta> l \<sigma> }"

fun declare_var_list :: "('v \<Rightarrow> abs_type) \<Rightarrow> vtyp list \<Rightarrow> 'v store \<Rightarrow> 'v store set" where
  "declare_var_list \<Delta> [] \<sigma> = {\<sigma>}"
| "declare_var_list \<Delta> (ty # q) \<sigma> = (\<Union>\<sigma>'\<in>declare_var_list \<Delta> q \<sigma>. declare_var \<Delta> ty \<sigma>')"

(* The first element of the list is gonna be n - 1, ..., the last one 0. *)
fun shift_and_add_list :: "(var \<rightharpoonup> 'v) \<Rightarrow> 'v list \<Rightarrow> (var \<rightharpoonup> 'v)" where
  "shift_and_add_list \<sigma> [] = \<sigma>"
| "shift_and_add_list \<sigma> (v # q) = shift_and_add_list (shift_and_add \<sigma> v) q"

(* The first element of the list is gonna be 0, the second one 1, etc. *)
fun shift_and_add_list_alt :: "(var \<rightharpoonup> 'v) \<Rightarrow> 'v list \<Rightarrow> (var \<rightharpoonup> 'v)" where
  "shift_and_add_list_alt \<sigma> [] = \<sigma>"
| "shift_and_add_list_alt \<sigma> (v # q) = shift_and_add (shift_and_add_list_alt \<sigma> q) v"

fun shift_up_substitution :: "(var \<rightharpoonup> var) \<Rightarrow> (var \<rightharpoonup> var)" where
  "shift_up_substitution \<sigma> 0 = Some 0"
| "shift_up_substitution \<sigma> (Suc n) = \<sigma> n"

fun substitute_pure_exp :: "(var \<rightharpoonup> var) \<Rightarrow> pure_exp \<Rightarrow> pure_exp" where
  "substitute_pure_exp \<sigma> (ELit lit) = ELit lit"
| "substitute_pure_exp \<sigma> (Var v) = Var (the (\<sigma> v))"
| "substitute_pure_exp \<sigma> (Unop u p) = Unop u (substitute_pure_exp \<sigma> p)"
| "substitute_pure_exp \<sigma> (Binop p1 b p2) = Binop (substitute_pure_exp \<sigma> p1) b (substitute_pure_exp \<sigma> p2)"
| "substitute_pure_exp \<sigma> (CondExp p1 p2 p3) =
  CondExp (substitute_pure_exp \<sigma> p1) (substitute_pure_exp \<sigma> p2) (substitute_pure_exp \<sigma> p3)"
| "substitute_pure_exp \<sigma> (FieldAcc e f) = FieldAcc (substitute_pure_exp \<sigma> e) f"
| "substitute_pure_exp \<sigma> (Old l e) = Old l (substitute_pure_exp \<sigma> e)"
| "substitute_pure_exp \<sigma> (Perm e f) = Perm (substitute_pure_exp \<sigma> e) f"
| "substitute_pure_exp \<sigma> (PermPred p exps) = PermPred p (map (substitute_pure_exp \<sigma>) exps)"
| "substitute_pure_exp \<sigma> (FunApp f exps) = FunApp f (map (substitute_pure_exp \<sigma>) exps)"
| "substitute_pure_exp \<sigma> Result = Var (the (\<sigma> 0))" (* Should be considered as 0 *)
| "substitute_pure_exp \<sigma> (Unfolding p exps e) = Unfolding p (map (substitute_pure_exp \<sigma>) exps) (substitute_pure_exp \<sigma> e)"
| "substitute_pure_exp \<sigma> (Let e1 e2) = Let (substitute_pure_exp \<sigma> e1) (substitute_pure_exp (shift_up_substitution \<sigma>) e2)"
| "substitute_pure_exp \<sigma> (PExists vtyp e) = PExists vtyp (substitute_pure_exp (shift_up_substitution \<sigma>) e)"
| "substitute_pure_exp \<sigma> (PForall vtyp e) = PForall vtyp (substitute_pure_exp (shift_up_substitution \<sigma>) e)"

fun substitute_pure_or_wildcard :: "(var \<rightharpoonup> var) \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> pure_exp exp_or_wildcard" where
  "substitute_pure_or_wildcard \<sigma> (PureExp p) = PureExp (substitute_pure_exp \<sigma> p)"
| "substitute_pure_or_wildcard \<sigma> Wildcard = Wildcard"

fun substitute_atomic_assert :: "(var \<rightharpoonup> var) \<Rightarrow> pure_exp atomic_assert \<Rightarrow> pure_exp atomic_assert" where
  "substitute_atomic_assert \<sigma> (Pure p) = Pure (substitute_pure_exp \<sigma> p)"
| "substitute_atomic_assert \<sigma> (Acc e f p) = Acc (substitute_pure_exp \<sigma> e) f (substitute_pure_or_wildcard \<sigma> p)"
| "substitute_atomic_assert \<sigma> (AccPredicate P exps p) = AccPredicate P (map (substitute_pure_exp \<sigma>) exps) 
  (substitute_pure_or_wildcard \<sigma> p)"

fun substitute_assertion :: "(var \<rightharpoonup> var) \<Rightarrow> assertion \<Rightarrow> assertion" where
  "substitute_assertion \<sigma> (Atomic A) = Atomic (substitute_atomic_assert \<sigma> A)"
| "substitute_assertion \<sigma> (Imp b A) = Imp (substitute_pure_exp \<sigma> b) (substitute_assertion \<sigma> A)"
| "substitute_assertion \<sigma> (CondAssert b A1 A2) = CondAssert (substitute_pure_exp \<sigma> b) (substitute_assertion \<sigma> A1) (substitute_assertion \<sigma> A2)"
| "substitute_assertion \<sigma> (A && B) = (substitute_assertion \<sigma> A) && (substitute_assertion \<sigma> B)"
| "substitute_assertion \<sigma> (A --* B) = (substitute_assertion \<sigma> A) --* (substitute_assertion \<sigma> B)"
| "substitute_assertion \<sigma> (ForAll vtyp A) = ForAll vtyp (substitute_assertion (shift_up_substitution \<sigma>) A)"

definition shift_down_set :: "var set \<Rightarrow> var set" where
  "shift_down_set S = { x - 1 |x. x \<in> S \<and> x \<ge> 1 }"

definition to_sub :: "var list \<Rightarrow> (var \<rightharpoonup> var)" where
  "to_sub l x = (if x < length l then Some (l ! x) else None)"

fun get_list_vtyp :: "('v \<Rightarrow> abs_type) \<Rightarrow> 'v store \<Rightarrow> var list \<Rightarrow> vtyp list" where
  "get_list_vtyp _ _ [] = []"
| "get_list_vtyp \<Delta> \<sigma> (x # q) = (get_type \<Delta> (the (\<sigma> x))) # (get_list_vtyp \<Delta> \<sigma> q)"


definition same_store :: "'v store \<times> 'a \<Rightarrow> 'v store \<times> 'a \<Rightarrow> bool" where
  "same_store \<omega> \<omega>' \<longleftrightarrow> fst \<omega> = fst \<omega>'"

(* 'v : abstract value
- 'a : separation algebra type (only heap and mask)
*)
fun shift_and_add_state :: "'v store \<times> 'a \<Rightarrow> 'v val \<Rightarrow> 'v store \<times> 'a" where
  "shift_and_add_state (\<sigma>, \<gamma>) x = (shift_and_add \<sigma> x, \<gamma>)"

fun unshift_state :: "nat \<Rightarrow> 'v store \<times> 'a \<Rightarrow> 'v store \<times> 'a" where
  "unshift_state n (\<sigma>, \<gamma>) = (unshift n \<sigma>, \<gamma>)"

(*
fun shift_and_add_list_state :: "'v store \<times> 'a \<Rightarrow> 'v val list \<Rightarrow> 'v store \<times> 'a" where
  "shift_and_add_list_state (\<sigma>, \<gamma>) [] = (\<sigma>, \<gamma>)"
| "shift_and_add_list_state (\<sigma>, \<gamma>) (t # q) = shift_and_add_list_state (shift_and_add \<sigma> t, \<gamma>) q"
*)

fun shift_and_add_list_state :: "'v store \<times> 'a \<Rightarrow> 'v val list \<Rightarrow> 'v store \<times> 'a" where
  "shift_and_add_list_state (\<sigma>, \<gamma>) l = (shift_and_add_list \<sigma> l, \<gamma>)"

fun shift_and_add_list_state_alt :: "'v store \<times> 'a \<Rightarrow> 'v val list \<Rightarrow> 'v store \<times> 'a" where
  "shift_and_add_list_state_alt (\<sigma>, \<gamma>) l = (shift_and_add_list_alt \<sigma> l, \<gamma>)"

definition all_states_forall :: "('v, 'b) interp \<Rightarrow> 'v store \<times> 'a \<Rightarrow> vtyp \<Rightarrow> ('v store \<times> 'a) set" where
  "all_states_forall \<Delta> \<omega> ty = {shift_and_add_state \<omega> v |v. v \<in> set_from_type (domains \<Delta>) ty }"


subsection \<open>\<^const>\<open>shift_and_add_list\<close>\<close>

lemma shift_and_add_list_lookup: 
  shows "shift_and_add_list m vs i = (if (i < length vs) then Some (rev vs ! i) else m (i - length vs))"
proof (induction vs arbitrary: m)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a vs)
  then show ?case
    by (simp add: shift_and_add_def nth_append)
qed

lemma shift_and_add_list_lookup_1: 
  assumes "i < length vs"
  shows "shift_and_add_list m vs i = Some (rev vs ! i)"
  using assms shift_and_add_list_lookup
  by meson  

lemma shift_and_add_list_lookup_2: 
  assumes "i \<ge> length vs"
  shows "shift_and_add_list m vs i = m (i - length vs)"
  using assms shift_and_add_list_lookup
  by (metis linorder_not_less)

subsection \<open>\<^const>\<open>shift_and_add_list_alt\<close>\<close>

lemma shift_and_add_list_alt_lookup:
  shows "shift_and_add_list_alt m vs i = (if (i < length vs) then Some (vs ! i) else m (i - length vs))"
proof (induction vs arbitrary: m i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a vs)
  let ?shift_m_vs = "(shift_and_add_list_alt m vs)"

  have "shift_and_add_list_alt m (a # vs) i = 
        shift_and_add ?shift_m_vs a i"
    by simp

  have "?shift_m_vs i = (if i < length vs then Some (vs ! i) else m (i - length vs))"
    by (simp add: Cons.IH)

  show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis 
      by (simp add: shift_and_add_def)      
  next
    case False
    hence "shift_and_add_list_alt m (a # vs) i = ?shift_m_vs (i-1)"
      by (simp add: shift_and_add_def)

    thus ?thesis
      using Cons.IH[where ?m=m and ?i="i-1"]
      by (metis (no_types, opaque_lifting) False Suc_eq_plus1 diff_Suc_1 diff_Suc_eq_diff_pred diff_less gr0I length_Cons less_diff_conv less_numeral_extra(1) nat_neq_iff not_less_eq nth_Cons_pos verit_comp_simplify1(1))
  qed    
qed

lemma shift_and_add_list_alt_lookup_1: 
  assumes "i < length vs"
  shows "shift_and_add_list_alt m vs i = Some (vs ! i)"
  using assms shift_and_add_list_alt_lookup
  by meson  

lemma shift_and_add_list_alt_lookup_2: 
  assumes "i \<ge> length vs"
  shows "shift_and_add_list_alt m vs i = m (i - length vs)"
  using assms shift_and_add_list_alt_lookup
  by (metis linorder_not_less)

end