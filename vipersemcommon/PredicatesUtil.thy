theory PredicatesUtil
imports ViperLang HOL.Real
begin
(*
fun real_to_expr :: "real \<Rightarrow> pure_exp"
  where "real_to_expr r = (let q = quotient_of r in 
                                  (Binop (ELit (LInt (fst q))) PermDiv (ELit (LInt (snd q)))))"
*)
fun real_to_expr :: "real \<Rightarrow> pure_exp" where
  "real_to_expr r = ELit (LPerm r)"

text \<open>Here multiplication of Wildcard with a negative amount gives wildcard\<close>
fun real_mult_permexpr :: "real \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> pure_exp exp_or_wildcard"
  where 
    "real_mult_permexpr p Wildcard = (if p = 0 then PureExp (ELit NoPerm) else (if p > 0 then Wildcard else undefined))"
  | "real_mult_permexpr p (PureExp e) = PureExp (Binop (real_to_expr p) Mult e)"

fun syntactic_mult :: "real \<Rightarrow> assertion \<Rightarrow> assertion"
  where 
    "syntactic_mult p (Atomic (Pure e)) = (Atomic (Pure e))"
  | "syntactic_mult p (Atomic (Acc e_r f e_p)) = (Atomic (Acc e_r f (real_mult_permexpr p e_p)))"
  | "syntactic_mult p (Atomic (AccPredicate pred_id e_args e_p)) = 
       (Atomic (AccPredicate pred_id e_args (real_mult_permexpr p e_p)))"
  | "syntactic_mult p (Imp e A) = (Imp e (syntactic_mult p A))"
  | "syntactic_mult p (Star A B) = Star (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (ForAll ty A) = (ForAll ty (syntactic_mult p A))"
  | "syntactic_mult p (Exists ty A) = (Exists ty (syntactic_mult p A))"
  | "syntactic_mult p (ImpureAnd A B) = ImpureAnd (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (ImpureOr A B) = ImpureOr (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (A --* B) = (syntactic_mult p A) --* (syntactic_mult p B)"

end