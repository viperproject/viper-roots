theory WellFormedness
  imports ViperLang
begin

definition forbidden_labels :: "label set" where
  "forbidden_labels = {label_lhs, empty_label}"

record restriction =
  perm_exp :: bool
  assume_impure :: bool
  inhale_exhale :: bool
  contravariant_recursion :: bool
  wands :: bool
  wildcards :: bool

record wf_context =
  restr :: restriction
  FunPost :: bool
  RHSWand :: bool
  var_context :: nat

(* 
TODO: Take into account other contexts like:
- even if perm is allowed, not allowed everywhere:
-- annotation
-- loop condition
*)

definition add_var_context :: "wf_context \<Rightarrow> nat \<Rightarrow> wf_context" where
  "add_var_context \<Gamma> n = \<Gamma>\<lparr> var_context := var_context \<Gamma> + n \<rparr>"

definition inside_wand :: "wf_context \<Rightarrow> wf_context" where
  "inside_wand \<Gamma> = \<Gamma>\<lparr> restr := (restr \<Gamma>)\<lparr> inhale_exhale := False, perm_exp := False \<rparr> \<rparr>"

(* An expression is well-defined if:
- variables are defined
- fields exist
- predicates exist TODO
- functions exist TODO
 *)
fun wf_pure_exp :: "program \<Rightarrow> wf_context \<Rightarrow> pure_exp \<Rightarrow> bool"
  and wf_pred_exp :: "program \<Rightarrow> wf_context \<Rightarrow> predicate_ident \<Rightarrow> pure_exp list \<Rightarrow> bool"
  where
  "wf_pred_exp Pr \<Gamma> p l \<longleftrightarrow> list_all (wf_pure_exp Pr \<Gamma>) l \<and> predicates Pr p \<noteq> None" (* TODO: Right number of args *)
| "wf_pure_exp Pr \<Gamma> (ELit _) \<longleftrightarrow> True"
| "wf_pure_exp Pr \<Gamma> (Var x) \<longleftrightarrow> x < var_context \<Gamma>"
| "wf_pure_exp Pr \<Gamma> (Unop _ e) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e"
| "wf_pure_exp Pr \<Gamma> (Binop a _ b) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> a \<and> wf_pure_exp Pr \<Gamma> b"
| "wf_pure_exp Pr \<Gamma> (FieldAcc e f) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e \<and> declared_fields Pr f \<noteq> None"
| "wf_pure_exp Pr \<Gamma> (Old l e) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e \<and> (l = label_lhs \<longrightarrow> RHSWand \<Gamma>)"
| "wf_pure_exp Pr \<Gamma> (Perm e f) \<longleftrightarrow> perm_exp (restr \<Gamma>) \<and> wf_pure_exp Pr \<Gamma> e \<and> declared_fields Pr f \<noteq> None"
| "wf_pure_exp Pr \<Gamma> (PermPred p l) \<longleftrightarrow> perm_exp (restr \<Gamma>) \<and> wf_pred_exp Pr \<Gamma> p l"
| "wf_pure_exp Pr \<Gamma> (FunApp f l) \<longleftrightarrow> list_all (wf_pure_exp Pr \<Gamma>) l" (* TODO: Right number of args *)
| "wf_pure_exp _ \<Gamma> Result \<longleftrightarrow> FunPost \<Gamma>"
| "wf_pure_exp Pr \<Gamma> (Unfolding p l e) \<longleftrightarrow> wf_pred_exp Pr \<Gamma> p l \<and> wf_pure_exp Pr \<Gamma> e"
| "wf_pure_exp Pr \<Gamma> (PExists ty e) = wf_pure_exp Pr (add_var_context \<Gamma> 1) e"
| "wf_pure_exp Pr \<Gamma> (Let ty e) = wf_pure_exp Pr (add_var_context \<Gamma> 1) e"
(*
| "wf_pure_exp Pr \<Gamma> (PForall ty e) = wf_pure_exp Pr (add_var_context \<Gamma> 1) e"
*)

(*
fun wf_assertion :: "program \<Rightarrow> wf_context \<Rightarrow> assertion \<Rightarrow> bool" where
  "wf_assertion Pr \<Gamma> (Pure e) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e"
| "wf_assertion Pr \<Gamma> (Acc e f p) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e \<and> declared_fields Pr f \<noteq> None \<and> wf_pure_exp Pr \<Gamma> p"
| "wf_assertion Pr \<Gamma> (Imp b A) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> b \<and> wf_assertion Pr \<Gamma> A"
| "wf_assertion Pr \<Gamma> (A --* B) \<longleftrightarrow> wands (restr \<Gamma>) \<and> wf_assertion Pr (inside_wand \<Gamma>) A \<and> wf_assertion Pr (inside_wand \<Gamma>\<lparr> RHSWand := True \<rparr>) B"
| "wf_assertion Pr \<Gamma> (A && B) \<longleftrightarrow> wf_assertion Pr \<Gamma> A \<and> wf_assertion Pr \<Gamma> B"
| "wf_assertion Pr \<Gamma> (ForAll ty A) \<longleftrightarrow> wf_assertion Pr \<Gamma> A"
| "wf_assertion Pr \<Gamma> (AccWildcard e f) \<longleftrightarrow> wildcards (restr \<Gamma>) \<and> wf_pure_exp Pr \<Gamma> e \<and> declared_fields Pr f \<noteq> None"
| "wf_assertion Pr \<Gamma> (AccPredicate p l f) \<longleftrightarrow> wf_pred_exp Pr \<Gamma> p l \<and> wf_pure_exp Pr \<Gamma> f"
| "wf_assertion Pr \<Gamma> (AccPredicateWildcard p l) \<longleftrightarrow> wildcards (restr \<Gamma>) \<and> wf_pred_exp Pr \<Gamma> p l"
| "wf_assertion Pr \<Gamma> (InhaleExhale A B) \<longleftrightarrow> inhale_exhale (restr \<Gamma>) \<and> wf_assertion Pr \<Gamma> A \<and> wf_assertion Pr \<Gamma> B"
*)

(* Labels are forgotten when inside a method body or a loop body *)
fun collect_labs :: "stmt \<Rightarrow> label set" where
  "collect_labs (Label l) = {l}"
| "collect_labs (If _ a b) = (collect_labs a \<union> collect_labs b)"
| "collect_labs (Seq a b) = (collect_labs a \<union> collect_labs b)"
| "collect_labs (Scope l s) = collect_labs s"
| "collect_labs _ = {}"

(*
(* TODO: Adapt context *)
fun wf_stmt_aux :: "program \<Rightarrow> wf_context \<Rightarrow> label set \<Rightarrow> stmt \<Rightarrow> bool" where
  "wf_stmt_aux Pr \<Gamma> labs (If b s1 s2) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> b \<and> wf_stmt_aux Pr \<Gamma> labs s1 \<and> wf_stmt_aux Pr \<Gamma> (labs \<union> collect_labs s1) s2"
| "wf_stmt_aux Pr \<Gamma> labs (Seq a b) \<longleftrightarrow> wf_stmt_aux Pr \<Gamma> labs a \<and> wf_stmt_aux Pr \<Gamma> (labs \<union> collect_labs a) b"
| "wf_stmt_aux Pr \<Gamma> labs (Label l) \<longleftrightarrow> (l \<notin> labs \<union> forbidden_labels)"
| "wf_stmt_aux Pr \<Gamma> labs (LocalAssign x e) \<longleftrightarrow> x < var_context \<Gamma> \<and> wf_pure_exp Pr \<Gamma> e"
| "wf_stmt_aux Pr \<Gamma> labs (FieldAssign e1 f e2) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> e1 \<and> declared_fields Pr f \<noteq> None \<and> wf_pure_exp Pr \<Gamma> e2"

| "wf_stmt_aux Pr \<Gamma> labs (Scope l s) \<longleftrightarrow> wf_stmt_aux Pr (add_var_context \<Gamma> (length l)) labs s"

| "wf_stmt_aux Pr \<Gamma> labs (Inhale A) \<longleftrightarrow> wf_assertion Pr \<Gamma> A"
| "wf_stmt_aux Pr \<Gamma> labs (Exhale A) \<longleftrightarrow> wf_assertion Pr \<Gamma> A"
| "wf_stmt_aux Pr \<Gamma> labs (Assert A) \<longleftrightarrow> wf_assertion Pr \<Gamma> A"
| "wf_stmt_aux Pr \<Gamma> labs (Assume A) \<longleftrightarrow> wf_assertion Pr \<Gamma> A \<and> (\<not> assume_impure (restr \<Gamma>) \<longrightarrow> is_pure A)"

| "wf_stmt_aux Pr \<Gamma> labs (Fold pred arg p) \<longleftrightarrow> predicates Pr pred \<noteq> None \<and> list_all (wf_pure_exp Pr \<Gamma>) arg \<and> wf_pure_exp Pr \<Gamma> p"
| "wf_stmt_aux Pr \<Gamma> labs (Unfold pred arg p) \<longleftrightarrow> predicates Pr pred \<noteq> None \<and> list_all (wf_pure_exp Pr \<Gamma>) arg \<and> wf_pure_exp Pr \<Gamma> p"
| "wf_stmt_aux Pr \<Gamma> labs (Apply A B) \<longleftrightarrow> wf_assertion Pr \<Gamma> A \<and> wf_assertion Pr \<Gamma> B"
| "wf_stmt_aux Pr \<Gamma> labs (Package A B) \<longleftrightarrow> wf_assertion Pr \<Gamma> A \<and> wf_assertion Pr \<Gamma> B"

| "wf_stmt_aux Pr \<Gamma> labs (MethodCall x name y) \<longleftrightarrow> (\<exists>m. methods Pr name = Some m \<and> length x = length (args m) \<and> length y = length (rets m))"
| "wf_stmt_aux Pr \<Gamma> labs (While b I s) \<longleftrightarrow> wf_pure_exp Pr \<Gamma> b \<and> wf_assertion Pr \<Gamma> I \<and> wf_stmt_aux Pr \<Gamma> labs s"

| "wf_stmt_aux Pr \<Gamma> labs Skip \<longleftrightarrow> True"
*)


end