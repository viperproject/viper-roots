theory ViperTyping
imports ViperLang DeBruijn
begin

type_synonym type_env = "var \<rightharpoonup> vtyp"

\<comment>\<open>
The Viper language formalization does not distinguish perm and integer addition/subtraction/multiplcation
at the syntax level, while the Viper AST does. We might want to reconsider this.
\<close>
inductive binop_type :: "binop \<Rightarrow> vtyp \<Rightarrow> vtyp \<Rightarrow> vtyp \<Rightarrow> bool"
  where
  \<comment>\<open>numerical operators\<close>
   NumericalInt: "\<lbrakk> bop \<in> {Add, Sub, Mult, Mod, IntDiv} \<rbrakk> \<Longrightarrow> binop_type bop TInt TInt TInt"
   (* Viper's type checker seems to reject perm division a/b when a is an integer and b is a permission,
      not sure why. It is not rejected here. *)
  | PermDiv: "\<lbrakk> (\<tau>1,\<tau>2) \<in> {(TInt, TInt), (TPerm, TInt), (TInt, TPerm), (TPerm, TPerm)} \<rbrakk> \<Longrightarrow>
                   binop_type PermDiv \<tau>1 \<tau>2 TPerm"
  | PermIntMult: "\<lbrakk> (\<tau>1,\<tau>2) \<in> {(TPerm, TInt), (TInt, TPerm)} \<rbrakk> \<Longrightarrow>
                   binop_type Mult \<tau>1 \<tau>2 TPerm"
  | NumericalPerm: "\<lbrakk> bop \<in> {Add, Sub, Mult, PermDiv} \<rbrakk> \<Longrightarrow> binop_type bop TPerm TPerm TPerm"

  \<comment>\<open>relational operators\<close>
  | Relational: "\<lbrakk> \<tau> \<in> {TInt, TPerm}; bop \<in> {Gt, Gte, Lt, Lte} \<rbrakk> \<Longrightarrow> binop_type bop \<tau> \<tau> TBool"

  \<comment>\<open>boolean operators\<close>
  | Boolean: "\<lbrakk> bop \<in> {Or, And, BImp} \<rbrakk> \<Longrightarrow> binop_type bop TBool TBool TBool"

  \<comment>\<open>equality and inequality\<close>
  | EqAndNeqAbs: "\<lbrakk> bop \<in> {Eq, Neq}; \<tau>1 = TAbs a1; \<tau>2 = TAbs a2 \<rbrakk> \<Longrightarrow> binop_type bop \<tau>1 \<tau>2 TBool"
  | EqAndNeq: "\<lbrakk> bop \<in> {Eq, Neq} \<rbrakk> \<Longrightarrow> binop_type bop \<tau> \<tau> TBool"

inductive_cases binop_type_elim : "binop_type op ty1 ty2 ty3"

inductive unop_type :: "unop \<Rightarrow> vtyp \<Rightarrow> vtyp \<Rightarrow> bool"
  where
    "unop_type Not TBool TBool"
  | "unop_type Minus TInt TInt"
  | "unop_type Minus TPerm TPerm"

inductive_cases unop_type_elim : "unop_type op ty1 ty2"

text \<open>Syntactic typing relation for expressions. TODO: typing rule for \<^const>\<open>ViperLang.Result\<close>\<close>

inductive pure_exp_typing :: "program \<Rightarrow> type_env \<Rightarrow> pure_exp \<Rightarrow> vtyp \<Rightarrow> bool"
  for Pr :: program
  where
    TypVar: "\<lbrakk> \<Lambda> x = Some ty \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Lambda> (Var x) ty"
  | TypLit: "\<lbrakk> type_of_lit lit = ty \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Lambda> (ELit lit) ty"
  | TypUnop:
    "\<lbrakk> unop_type uop \<tau>1 \<tau>;
       pure_exp_typing Pr \<Lambda> e \<tau>1 \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (Unop uop e) \<tau>"
  | TypBinop:
    "\<lbrakk> binop_type bop \<tau>1 \<tau>2 \<tau>;
       pure_exp_typing Pr \<Lambda> e1 \<tau>1;
       pure_exp_typing Pr \<Lambda> e2 \<tau>2 \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (Binop e1 bop e2) \<tau>"
  | TypCondExp:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> b TBool;
       pure_exp_typing Pr \<Lambda> e1 \<tau>;
       pure_exp_typing Pr \<Lambda> e2 \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (CondExp b e1 e2) \<tau>"
  | TypFieldAcc:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> rcv TRef;
       declared_fields Pr f = Some \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (FieldAcc rcv f) \<tau>"
  | TypOld:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> e \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (Old lbl e) \<tau>"
  | TypPerm:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> rcv TRef;
       declared_fields Pr f = Some \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (Perm rcv f) TPerm"
  | TypPermPred:
    "\<lbrakk> ViperLang.predicates Pr pid = Some pdecl;
       predicate_decl.args pdecl = ts;
       list_all2 (pure_exp_typing Pr \<Lambda>) es ts \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (PermPred pid es) TPerm"
  | TypFunApp:
    "\<lbrakk> ViperLang.funs Pr f = Some fdecl;
       function_decl.args fdecl = ts;
       list_all2 (pure_exp_typing Pr \<Lambda>) es ts \<rbrakk> \<Longrightarrow>
        pure_exp_typing Pr \<Lambda> (FunApp f es) TPerm"
  | TypUnfolding:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> ubody \<tau> \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Lambda> (Unfolding p es ubody) \<tau>"
  | TypLet:
    "\<lbrakk> pure_exp_typing Pr \<Lambda> e \<tau>1;
      pure_exp_typing Pr (shift_and_add \<Lambda> \<tau>1) lbody \<tau> \<rbrakk> \<Longrightarrow>
      pure_exp_typing Pr \<Lambda> (Let e lbody) \<tau>"
  | TypExists:
    "\<lbrakk> pure_exp_typing Pr (shift_and_add \<Lambda> \<tau>x) qbody TBool \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (PExists \<tau>x qbody) TBool"
  | TypForall:
     "\<lbrakk> pure_exp_typing Pr (shift_and_add \<Lambda> \<tau>x) qbody TBool \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Lambda> (PForall \<tau>x qbody) TBool"

inductive exp_or_wildcard_typing :: "program \<Rightarrow> type_env \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> vtyp \<Rightarrow> bool"
  for Pr :: program and \<Lambda> :: type_env
  where
    TypPureExp: "\<lbrakk> pure_exp_typing Pr \<Lambda> e ty \<rbrakk> \<Longrightarrow> exp_or_wildcard_typing Pr \<Lambda> (PureExp e) ty"
  | TypWildcard: "exp_or_wildcard_typing Pr \<Lambda> Wildcard TPerm"

inductive atomic_assertion_typing :: "program \<Rightarrow> type_env \<Rightarrow> pure_exp atomic_assert \<Rightarrow> bool"
  for Pr :: program and \<Lambda> :: type_env
  where
    TypPure: "\<lbrakk> pure_exp_typing Pr \<Lambda> e TBool \<rbrakk> \<Longrightarrow> atomic_assertion_typing Pr \<Lambda> (Pure e)"
  | TypAcc:
    "\<lbrakk> f \<in> dom (declared_fields Pr);
       pure_exp_typing Pr \<Lambda> e TRef;
       exp_or_wildcard_typing Pr \<Lambda> p TPerm \<rbrakk> \<Longrightarrow>
       atomic_assertion_typing Pr \<Lambda> (Acc e f p)"
  | TypAccPredicate:
    "\<lbrakk> program.predicates Pr P = Some def;
       list_all2 (pure_exp_typing Pr \<Lambda>) es (predicate_decl.args def);
       exp_or_wildcard_typing Pr \<Lambda> e TPerm \<rbrakk> \<Longrightarrow>
       atomic_assertion_typing Pr \<Lambda> (AccPredicate P es p)"

inductive assertion_typing :: "program \<Rightarrow> type_env \<Rightarrow> assertion \<Rightarrow> bool"
  for Pr :: program
  where
    TypAtomic: "\<lbrakk> atomic_assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow> assertion_typing Pr \<Lambda> (Atomic A)"
  | TypImp: "\<lbrakk> pure_exp_typing Pr \<Lambda> e TBool; assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (Imp e A)"
  | TypCondAssert: "\<lbrakk> pure_exp_typing Pr \<Lambda> e TBool; assertion_typing Pr \<Lambda> A1;
      assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow> assertion_typing Pr \<Lambda> (CondAssert e A1 A2)"
  | TypImpureAnd: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (ImpureAnd A1 A2)"
  | TypImpureOr: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (ImpureOr A1 A2)"
  | TypStar: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (Star A1 A2)"
  | TypWand: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (Wand A1 A2)"
  | TypForAll: "\<lbrakk> assertion_typing Pr (shift_and_add \<Lambda> \<tau>x) A \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (ForAll \<tau>x A)"
  | TypExists: "\<lbrakk> assertion_typing Pr (shift_and_add \<Lambda> \<tau>x) A \<rbrakk> \<Longrightarrow>
      assertion_typing Pr \<Lambda> (Exists \<tau>x A)"

inductive stmt_typing :: "program \<Rightarrow> type_env \<Rightarrow> stmt \<Rightarrow> bool"
  for Pr :: program
  where
    TypInhale: "\<lbrakk> assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Inhale A)"
  | TypExhale: "\<lbrakk> assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Exhale A)"
  | TypAssert: "\<lbrakk> assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Assert A)"
  | TypAssume: "\<lbrakk> assertion_typing Pr \<Lambda> A \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Assume A)"
  | TypIf: "\<lbrakk> pure_exp_typing Pr \<Lambda> e TBool; stmt_typing Pr \<Lambda> C1; stmt_typing Pr \<Lambda> C2 \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (If e C1 C2)"
  | TypSeq: "\<lbrakk> stmt_typing Pr \<Lambda> C1; stmt_typing Pr \<Lambda> C2 \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (Seq C1 C2)"
  | TypLocalAssign: "\<lbrakk> \<Lambda> x = Some ty; pure_exp_typing Pr \<Lambda> e ty \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (LocalAssign x e)"
  | TypFieldAssign: "
    \<lbrakk> declared_fields Pr f = Some ty;
      pure_exp_typing Pr \<Lambda> e1 TRef;
      pure_exp_typing Pr \<Lambda> e2 ty \<rbrakk> \<Longrightarrow>
      stmt_typing Pr \<Lambda> (FieldAssign e1 f e2)"
  | TypHavoc: "\<lbrakk> \<Lambda> x = Some ty \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Havoc x)"
  | TypMethodCall:
    "\<lbrakk> program.methods Pr f = Some def;
       list_all2 (pure_exp_typing Pr \<Lambda>) es (method_decl.args def);
       list_all2 (\<lambda> y r. \<Lambda> y = Some r) ys (method_decl.rets def) \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (MethodCall ys f es)"
  | TypWhile: "\<lbrakk> pure_exp_typing Pr \<Lambda> e TBool; assertion_typing Pr \<Lambda> A; stmt_typing Pr \<Lambda> C \<rbrakk> \<Longrightarrow>
      stmt_typing Pr \<Lambda> (While e A C)"
  | TypUnfold:
    "\<lbrakk> program.predicates Pr P = Some def;
       list_all2 (pure_exp_typing Pr \<Lambda>) es (predicate_decl.args def);
       exp_or_wildcard_typing Pr \<Lambda> p TPerm \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (Unfold P es p)"
  | TypFold:
    "\<lbrakk> program.predicates Pr P = Some def;
       list_all2 (pure_exp_typing Pr \<Lambda>) es (predicate_decl.args def);
       exp_or_wildcard_typing Pr \<Lambda> p TPerm \<rbrakk> \<Longrightarrow>
       stmt_typing Pr \<Lambda> (Fold P es p)"
  | TypPackage: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (Package A1 A2)"
  | TypApply: "\<lbrakk> assertion_typing Pr \<Lambda> A1; assertion_typing Pr \<Lambda> A2 \<rbrakk> \<Longrightarrow>
     stmt_typing Pr \<Lambda> (Apply A1 A2)"
  | TypLabel: "stmt_typing Pr \<Lambda> (Label l)"
  | TypScope: "\<lbrakk> stmt_typing Pr (shift_and_add \<Lambda> \<tau>x) C \<rbrakk> \<Longrightarrow> stmt_typing Pr \<Lambda> (Scope \<tau>x C)"
  | TypSkip: "stmt_typing Pr \<Lambda> Skip"

inductive_cases stmt_typing_elim :
  "stmt_typing Pr \<Lambda> (stmt.Inhale e)"
  "stmt_typing Pr \<Lambda> (stmt.Exhale e)"
  "stmt_typing Pr \<Lambda> (stmt.Assert e)"
  "stmt_typing Pr \<Lambda> (stmt.Assume e)"
  "stmt_typing Pr \<Lambda> (stmt.If e C1 C2)"
  "stmt_typing Pr \<Lambda> (stmt.Seq C1 C2)"
  "stmt_typing Pr \<Lambda> (stmt.LocalAssign v e)"
  "stmt_typing Pr \<Lambda> (stmt.FieldAssign e f e)"
  "stmt_typing Pr \<Lambda> (stmt.Havoc v)"
  "stmt_typing Pr \<Lambda> (stmt.MethodCall ys f es)"
  "stmt_typing Pr \<Lambda> (stmt.While e I C)"
  "stmt_typing Pr \<Lambda> (stmt.Unfold P es p)"
  "stmt_typing Pr \<Lambda> (stmt.Fold P es p)"
  "stmt_typing Pr \<Lambda> (stmt.Package A1 A2)"
  "stmt_typing Pr \<Lambda> (stmt.Apply A1 A2)"
  "stmt_typing Pr \<Lambda> (stmt.Label l)"
  "stmt_typing Pr \<Lambda> (stmt.Scope v C)"
  "stmt_typing Pr \<Lambda> (stmt.Skip)"

end