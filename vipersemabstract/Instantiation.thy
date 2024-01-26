theory Instantiation
  imports AbstractSemantics EquiViper EquiSemAuxLemma
begin

definition make_semantic_bexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'a equi_state bexp" where
  "make_semantic_bexp \<Delta> b \<omega> =
  (if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool True) then Some True
  else if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val (VBool False) then Some False
  else None)"

definition make_semantic_exp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> ('a equi_state, 'a val) exp" where
  "make_semantic_exp \<Delta> b \<omega> = (if \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] VFailure then None
  else Some (SOME v. \<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v))"

definition make_semantic_rexp :: "('a, ('a virtual_state)) interp \<Rightarrow> pure_exp \<Rightarrow> field_ident \<Rightarrow> ('a equi_state, address \<times> field_ident) exp" where
  "make_semantic_rexp \<Delta> r f \<omega> = (if \<exists>v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v))
  then Some (SOME v. \<Delta> \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] Val (VRef (Address v)), f)
  else None)"


definition make_semantic_assertion :: "('a, 'a virtual_state) interp \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state \<Rightarrow> bool" where
  "make_semantic_assertion \<Delta> A \<omega> \<longleftrightarrow> \<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle>"

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

fun compile :: "('a, 'a virtual_state) interp \<Rightarrow> stmt \<Rightarrow> ('a equi_state, 'a val, address \<times> field_ident) abs_stmt"
  where
  "compile \<Delta> stmt.Skip = abs_stmt.Skip"

| "compile \<Delta> (stmt.If b C1 C2) = abs_stmt.If (make_semantic_bexp \<Delta> b) (compile \<Delta> C1) (compile \<Delta> C2)"
| "compile \<Delta> (stmt.Seq C1 C2) = abs_stmt.Seq (compile \<Delta> C1) (compile \<Delta> C2)"

| "compile \<Delta> (stmt.Scope ty C) = abs_stmt.Scope (make_semantic_vtyp \<Delta> ty) (compile \<Delta> C)"
| "compile \<Delta> (stmt.Havoc x) = abs_stmt.Havoc x"
| "compile \<Delta> (stmt.LocalAssign x e) = abs_stmt.LocalAssign x (make_semantic_exp \<Delta> e)"
| "compile \<Delta> (stmt.FieldAssign r f e) = abs_stmt.FieldAssign (make_semantic_rexp \<Delta> r f) (make_semantic_exp \<Delta> e)"

| "compile \<Delta> (stmt.Label l) = abs_stmt.Label l"

| "compile \<Delta> (stmt.Inhale A) = abs_stmt.Inhale (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Exhale A) = abs_stmt.Exhale (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Assert A) = abs_stmt.Assert (make_semantic_assertion \<Delta> A)"
| "compile \<Delta> (stmt.Assume A) = abs_stmt.Assume (make_semantic_assertion \<Delta> A)"

| "compile \<Delta> (stmt.Unfold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Fold _ _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Package _ _) = abs_stmt.Skip"
| "compile \<Delta> (stmt.Apply _ _) = abs_stmt.Skip"

(* TODO: We can take the program as input, and emit the encodings *)
| "compile \<Delta> (stmt.MethodCall _ _ _) = undefined"
| "compile \<Delta> (stmt.While b I C) = undefined"


(*
type_synonym 'a equi_state = "('a trace \<times> 'a virtual_state, 'a val) state"
*)
definition has_write_perm_only :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> bool" where
  "has_write_perm_only \<phi> hl \<longleftrightarrow> get_vm \<phi> hl = 1"
(* Could be expressed as "set_value" is frame-preserving
*)

definition has_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> bool" where
  "has_value \<phi> hl v \<longleftrightarrow> get_vh \<phi> hl = Some v"

definition set_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" where
  "set_value \<phi> hl v = Abs_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"

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
  "viper_prog_verifies Pr \<Delta> ty C \<omega> \<longleftrightarrow> ConcreteSemantics.verifies ty (compile \<Delta> C) \<omega>"
(* ty is a type-context *)



end