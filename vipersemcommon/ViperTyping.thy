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
  | NumericalPerm: "\<lbrakk> bop \<in> {Add, Sub, Mult} \<rbrakk> \<Longrightarrow> binop_type bop TPerm TPerm TPerm"

  \<comment>\<open>relational operators\<close>
  | Relational: "\<lbrakk> \<tau> \<in> {TInt, TPerm}; bop \<in> {Gt, Gte, Lt, Lte} \<rbrakk> \<Longrightarrow> binop_type bop \<tau> \<tau> TBool"
  
  \<comment>\<open>boolean operators\<close>
  | Boolean: "\<lbrakk> bop \<in> {Or, And, BImp} \<rbrakk> \<Longrightarrow> binop_type bop TBool TBool TBool"
  
  \<comment>\<open>equality and inequality\<close>
  | EqAndNeq: "\<lbrakk> bop \<in> {Eq, Neq} \<rbrakk> \<Longrightarrow> binop_type bop \<tau> \<tau> TBool"

inductive unop_type :: "unop \<Rightarrow> vtyp \<Rightarrow> vtyp \<Rightarrow> bool"
  where
    "unop_type Not TBool TBool"
  | "unop_type Minus TInt TInt"
  | "unop_type Minus TPerm TPerm"

text \<open>Syntactic typing relation for expressions. TODO: typing rule for \<^const>\<open>ViperLang.Result\<close>\<close>

inductive pure_exp_typing :: "program \<Rightarrow> type_env \<Rightarrow> pure_exp \<Rightarrow> vtyp \<Rightarrow> bool"
  for Pr :: program
  where 
    TypVar: "\<lbrakk> \<Delta> x = Some ty \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Delta> (Var x) ty"
  | TypLit: "\<lbrakk> type_of_lit lit = ty \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Delta> (ELit lit) ty"
  | TypUnop: 
    "\<lbrakk> unop_type uop \<tau>1 \<tau>; 
       pure_exp_typing Pr \<Delta> e \<tau>1 \<rbrakk> \<Longrightarrow> 
       pure_exp_typing Pr \<Delta> (Unop uop e) \<tau>"
  | TypBinop: 
    "\<lbrakk> binop_type bop \<tau>1 \<tau>2 \<tau>;
       pure_exp_typing Pr \<Delta> e1 \<tau>1;
       pure_exp_typing Pr \<Delta> e2 \<tau>2 \<rbrakk> \<Longrightarrow> 
       pure_exp_typing Pr \<Delta> (Binop e1 bop e2) \<tau>"
  | TypCondExp:
    "\<lbrakk> pure_exp_typing Pr \<Delta> b TBool;
       pure_exp_typing Pr \<Delta> e1 \<tau>;
       pure_exp_typing Pr \<Delta> e2 \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Delta> (CondExp b e1 e2) \<tau>"
  | TypFieldAcc:
    "\<lbrakk> pure_exp_typing Pr \<Delta> rcv TRef;
       declared_fields Pr f = Some \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Delta> (FieldAcc rcv f) \<tau>"
  | TypOld:
    "\<lbrakk> pure_exp_typing Pr \<Delta> e \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Delta> (Old lbl e) \<tau>"
  | TypPerm:
    "\<lbrakk> pure_exp_typing Pr \<Delta> rcv TRef;
       declared_fields Pr f = Some \<tau> \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Delta> (Perm rcv f) TPerm"
  | TypPermPred:
    "\<lbrakk> ViperLang.predicates Pr pid = Some pdecl;
       predicate_decl.args pdecl = ts;
       list_all2 (pure_exp_typing Pr \<Delta>) es ts \<rbrakk> \<Longrightarrow>
       pure_exp_typing Pr \<Delta> (PermPred pid es) TPerm"
  | TypFunApp:
    "\<lbrakk> ViperLang.funs Pr f = Some fdecl;
       function_decl.args fdecl = ts;
       list_all2 (pure_exp_typing Pr \<Delta>) es ts \<rbrakk> \<Longrightarrow>
        pure_exp_typing Pr \<Delta> (FunApp f es) TPerm"
  | TypUnfolding:
    "\<lbrakk> pure_exp_typing Pr \<Delta> ubody \<tau> \<rbrakk> \<Longrightarrow> pure_exp_typing Pr \<Delta> (Unfolding p es ubody) \<tau>"
  | TypLet:
    "\<lbrakk> pure_exp_typing Pr \<Delta> e \<tau>1;  
      pure_exp_typing Pr (shift_and_add \<Delta> \<tau>1) lbody \<tau> \<rbrakk> \<Longrightarrow> 
      pure_exp_typing Pr \<Delta> (Let e lbody) \<tau>"
  | TypExists:
    "\<lbrakk> pure_exp_typing Pr (shift_and_add \<Delta> \<tau>x) qbody TBool \<rbrakk> \<Longrightarrow> 
       pure_exp_typing Pr \<Delta> (PExists \<tau>x qbody) TBool"
  | TypForall:
     "\<lbrakk> pure_exp_typing Pr (shift_and_add \<Delta> \<tau>x) qbody TBool \<rbrakk> \<Longrightarrow> 
       pure_exp_typing Pr \<Delta> (PForall \<tau>x qbody) TBool"


end