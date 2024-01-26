theory ViperLang
  imports Main HOL.Real
begin

(* TODO:
- Add perm expressions
- Add predicates
- Add wf_state (Viper state)
- Add function calls
- Add domains
- Add pure exists and forall
*)

(* No way to express references, domains *)
datatype lit = LBool bool | LInt int | LNull | LPerm real

abbreviation NoPerm where "NoPerm \<equiv> LPerm 0"
abbreviation WritePerm where "WritePerm \<equiv> LPerm 1"


datatype binop =
  Add | Sub | Mult | IntDiv | PermDiv | Mod
| Eq | Neq
| Gt | Gte | Lt | Lte
| Or | BImp | And

datatype unop = Not | Minus

type_synonym predicate_ident = string
type_synonym method_ident = string
type_synonym field_ident = string
type_synonym function_ident = string
type_synonym label = string
type_synonym var = nat

type_synonym abs_type = string

datatype vtyp = TInt | TBool | TPerm | TRef | TAbs abs_type

primrec type_of_lit :: "lit \<Rightarrow> vtyp"
  where
   "type_of_lit (LBool b) = TBool"
 | "type_of_lit (LInt i) = TInt"
 | "type_of_lit (LPerm _) = TPerm"
 | "type_of_lit LNull = TRef"

datatype pure_exp =
  ELit lit
  | Var var
  | Unop unop pure_exp
  | Binop pure_exp binop pure_exp
  | CondExp pure_exp pure_exp pure_exp
  | FieldAcc pure_exp field_ident
  | Old label pure_exp

  | Perm pure_exp field_ident
  | PermPred predicate_ident "pure_exp list"

  | FunApp function_ident "pure_exp list"
  | Result (* Only for functions *)

\<comment>\<open>unfolding P(l) in e\<close>
  | Unfolding predicate_ident "pure_exp list" pure_exp

  | Let pure_exp pure_exp
  | PExists vtyp pure_exp
  | is_pforall: PForall vtyp pure_exp

datatype 'p exp_or_wildcard = PureExp 'p | Wildcard

datatype 'p atomic_assert =
  is_pure_atomic: Pure 'p
  | Acc 'p field_ident "'p exp_or_wildcard"
  | AccPredicate predicate_ident "'p list" "'p exp_or_wildcard"
(* AccPredicate "name of predicate" "arguments" "permission amount" *)

datatype ('p, 'atm) assert =
  Atomic 'atm
  | Imp 'p "('p, 'atm) assert"
  | CondAssert 'p "('p, 'atm) assert" "('p, 'atm) assert"
(*
  | InhaleExhale "('p, 'atm) assert" "('p, 'atm) assert"
*)
  | ImpureAnd "('p, 'atm) assert" "('p, 'atm) assert"
  | ImpureOr "('p, 'atm) assert" "('p, 'atm) assert"

  | Star "('p, 'atm) assert" "('p, 'atm) assert" (infixl "&&" 60)
  | Wand "('p, 'atm) assert" "('p, 'atm) assert" (infixl "--*" 60)

  | is_forall: ForAll vtyp "('p, 'atm) assert"
  | Exists vtyp "('p, 'atm) assert"

text \<open>Assertions \<^typ>\<open>('p, 'atm) assert\<close> are parametrized by the pure expressions \<^typ>\<open>'p\<close> as well as the
atomic assertions \<^typ>\<open>'atm\<close> (assertions without impure connectives). Note that the atomic assertions usually include
the pure assertions.\<close>

text\<open>We prove the following instantiation for Viper assertions.\<close>
type_synonym assertion = "(pure_exp, pure_exp atomic_assert) assert"

term "(Atomic (AccPredicate name [] Wildcard)) :: assertion"


fun is_pure :: "assertion \<Rightarrow> bool" where
  "is_pure (Atomic e) \<longleftrightarrow> is_pure_atomic e"
| "is_pure (Imp _ A) \<longleftrightarrow> is_pure A"
| "is_pure (CondAssert _ A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (A && B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ImpureAnd A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ImpureOr A B) \<longleftrightarrow> is_pure A \<and> is_pure B"
| "is_pure (ForAll _ A) \<longleftrightarrow> is_pure A"
| "is_pure (Exists _ A) \<longleftrightarrow> is_pure A"
| "is_pure (Wand _ _) \<longleftrightarrow> False"

(* currently missing:
- x := new(_)
- goto
- inhale-exhale
*)

datatype stmt =

\<comment>\<open>Assertions\<close>
  Inhale assertion | Exhale assertion | Assert assertion | Assume assertion
\<comment>\<open>assume A not valid in the theoretical semantics\<close>

\<comment>\<open>Control structures\<close>
| If pure_exp stmt stmt | Seq stmt stmt

\<comment>\<open>Assignments\<close>
| LocalAssign var pure_exp | FieldAssign pure_exp field_ident pure_exp | Havoc var

\<comment>\<open>Calls and loops\<close>
| MethodCall "var list" method_ident "pure_exp list" (* y1,y2,... := m(e1, e2, ...) *)
| While pure_exp assertion stmt (* While (b) invariant I {s} *)

\<comment>\<open>Verifier directives\<close>
| Unfold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Fold predicate_ident "pure_exp list" "pure_exp exp_or_wildcard"
| Package assertion assertion
| Apply assertion assertion

\<comment>\<open>Misc\<close>
| Label label | Scope vtyp stmt | Skip

(* method m(x) returns y req P ens Q *)
record method_decl =
  args :: "vtyp list"
  rets :: "vtyp list"
  pre :: assertion
  post :: assertion
  body :: "stmt option" (* Abstract or concrete *)

record predicate_decl =
  args :: "vtyp list"
  body :: "assertion option"

record function_decl =
  args :: "vtyp list"
  ret :: vtyp
  pre :: assertion
  post :: "assertion option" (* difference between post (terminating) and no post? *)
  body :: "pure_exp option" (* Abstract or concrete *)

record program =
  methods :: "method_ident \<rightharpoonup> method_decl"
  predicates :: "predicate_ident \<rightharpoonup> predicate_decl"
  funs :: "function_ident \<rightharpoonup> function_decl"
  declared_fields :: "field_ident \<rightharpoonup> vtyp"
  domains :: nat (* TODO *)

(* well-formed program:
- Method calls are well-formed (method exists, right number of args and return, right types
- Same for functions calls
- Fields exist (+ typing)
- Predicate (like methods)
- Domain (typing?)
- Typing
- Variables that do not exist

\<Longrightarrow> If a program is well-formed and well-typed, all expressions must reduce
*)

(* Well-definedness:
- Variables are defined
- Same number of variables for args and rets in method calls
- labels are unique in a method body
- all methods called exist
- No "lhs" (wands) or "default" (methods, loops?) label
- No contravariant recursion for predicates
- Right fields
*)

definition label_lhs :: "label" where
  "label_lhs = ''lhs''"

definition empty_label :: "label" where
  "empty_label = ''''"

record configuration =
  angelic_exhale :: bool
  executable :: bool
  annotation :: "bool option" (* None = angelic, false = ignored, true = used *)
  ghost_assert :: bool (* fold unfold apply package: either assert, or skip *)

datatype RedType = RInhale | RExhale





section \<open>Shorthands\<close>

(*
fun n_scope :: "vtyp list \<Rightarrow> stmt \<Rightarrow> stmt" where
  "n_scope [] s = s"
| "n_scope (t # q) s = Scope t (n_scope q s)"
*)

fun n_havoc :: "var list \<Rightarrow> stmt" where
  "n_havoc [] = Skip"
| "n_havoc (x # q) = Seq (Havoc x) (n_havoc q)"

fun n_forall :: "vtyp list \<Rightarrow> assertion \<Rightarrow> assertion" where
  "n_forall [] A = A"
| "n_forall (t # q) A = ForAll t (n_forall q A)"

fun n_forall_pure :: "vtyp list \<Rightarrow> pure_exp \<Rightarrow> pure_exp" where
  "n_forall_pure [] e = e"
| "n_forall_pure (t # q) e = PForall t (n_forall_pure q e)"

end
