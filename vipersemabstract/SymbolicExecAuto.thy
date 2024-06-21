theory SymbolicExecAuto
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState ViperCommon.Binop ViperCommon.PosPerm
    ViperCommon.PosReal SymbolicExecDef
begin

(* if provable *)
definition pif :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
"pif b c1 c2 = ((b \<and> c1) \<or> c2)"

lemma pifI1 :
  assumes "b"
  assumes "c1"
  shows "pif b c1 c2"
  using assms by (simp add:pif_def)

lemma pifI2 :
  assumes "c2"
  shows "pif b c1 c2"
  using assms by (simp add:pif_def)

method pif methods m =
  (rule pifI1, solves \<open>m\<close> | rule pifI2)

lemma pif_test :
  shows "b ==> pif c A1 (pif b A2 A3)"
  apply (pif simp)
  apply (pif simp)  
  oops

named_theorems sexec_intro
declare conjI [sexec_intro]

named_theorems sexec_simp
lemmas [sexec_simp] =
  sym_gen_fresh_def 

named_theorems sexec_solve_intro
declare sym_impliesI [sexec_solve_intro]

named_theorems sexec_solve_simp
lemmas [sexec_solve_simp] =
   SBinop_eq_Some
   SNot_eq_Some (* replace with SUnop_eq_Some? *)
   bind_eq_Some_conv
   SLit_def
   SVar_def
   SHasType_eq_Some
  (* TODO: use a more precise lemma that does not rely on the reduction of eval_binop *)
   SBinopSafe_eq_Some

method sexec_solve =
  (auto intro!:sexec_solve_intro simp add:sexec_solve_simp)[]

method sexec_step =
  (simp add:sexec_simp |
   rule sexec_intro | 
   (match conclusion in "pif _ _ _" \<Rightarrow> \<open>pif sexec_solve\<close>))

method sexec =
  sexec_step+


lemma sym_consolidate_nopI:
  assumes "Q \<sigma>"
  shows "sym_consolidate \<sigma> Q"
  using assms apply (cases \<sigma>; simp add:sym_consolidate_def) using succ_refl by fastforce

lemma sym_heap_do_add_nopI [sexec_intro]:
  assumes "Q (sym_heap_add \<sigma> c)"
  shows "sym_heap_do_add \<sigma> c Q"
  using assms sym_consolidate_nopI apply (simp add:sym_heap_do_add_def) by fastforce


fun sym_heap_extract_fun :: "'a sym_state \<Rightarrow> 'a chunk list \<Rightarrow> 'a sym_exp \<Rightarrow>
    field_name \<Rightarrow> ('a sym_state \<Rightarrow> 'a chunk \<Rightarrow> bool) \<Rightarrow> bool" where
  "sym_heap_extract_fun \<sigma> [] te f Q = sfail (''heap extract failed'', \<sigma>, te, f, Q)"
| "sym_heap_extract_fun \<sigma> (c#cs) te f Q =
    pif (f = chunk_field c \<and> (sym_cond \<sigma> \<turnstile>\<^sub>s te =\<^sub>s chunk_recv c))
     (Q (\<sigma>\<lparr>sym_heap := cs\<rparr>) c)
     (sym_heap_extract_fun \<sigma> cs te f (\<lambda> \<sigma>. Q (sym_heap_add \<sigma> c)))"

lemma sym_heap_extract_fun_sound [sexec_intro]:
  assumes "sym_heap_extract_fun \<sigma> cs0 te f Q"
  shows "sym_consolidate (\<sigma>\<lparr> sym_heap := cs0 \<rparr>) (\<lambda> \<sigma>. \<exists> c cs. sym_heap \<sigma> = c # cs \<and> chunk_field c = f \<and> (sym_cond \<sigma> \<turnstile>\<^sub>s te =\<^sub>s chunk_recv c) \<and> Q (\<sigma>\<lparr>sym_heap := cs\<rparr>) c)"
using assms
proof (induction cs0 arbitrary: \<sigma> Q)
  case Nil then show ?case by (simp add:sfail_def)
next
  case (Cons a cs0)
  from Cons.prems show ?case
    apply (simp add:pif_def)
    apply (safe)
    subgoal by (rule sym_consolidate_nopI; simp)
    subgoal
      apply (drule Cons.IH)
      apply (rule sym_consolidate_dup)
      apply (rule sym_consolidate_frame; simp)
      apply (rule sym_consolidate_mono, assumption)
      apply (clarsimp)
      by (rule sym_consolidate_swap; simp)
    done
qed

lemma sym_heap_extract_to_funI [sexec_intro]:
  assumes "sym_heap_extract_fun \<sigma> (sym_heap \<sigma>) te f (\<lambda> \<sigma>' c.
    (sym_cond \<sigma>' \<turnstile>\<^sub>s case p of Some p \<Rightarrow> SPerm 0 \<le>\<^sub>s p \<and>\<^sub>s p \<le>\<^sub>s chunk_perm c | None \<Rightarrow> SPerm 0 <\<^sub>s chunk_perm c) \<and> Q \<sigma>' c)"
  shows "sym_heap_extract \<sigma> te f p Q"
  using assms apply (simp add:sym_heap_extract_def)
  apply (drule sym_heap_extract_fun_sound)
  apply (simp)
  apply (rule sym_consolidate_mono) apply (assumption)
  by (clarsimp simp add:sym_implies_conj)


fun sym_stabilize_fun :: "'a sym_state \<Rightarrow> 'a chunk list \<Rightarrow> ('a sym_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "sym_stabilize_fun \<sigma> [] Q = Q (\<sigma>\<lparr> sym_heap := [] \<rparr>)"
| "sym_stabilize_fun \<sigma> (c#cs) Q =
    pif (sym_cond \<sigma> \<turnstile>\<^sub>s SPerm 0 <\<^sub>s chunk_perm c)
      (sym_stabilize_fun \<sigma> cs (\<lambda> \<sigma>. Q (sym_heap_add \<sigma> c)))
      (sym_stabilize_fun \<sigma> cs Q)"

lemma sym_stabilize_fun_preserves_cond :
  assumes "sym_stabilize_fun \<sigma> cs Q"
  shows "sym_stabilize_fun \<sigma> cs (\<lambda> \<sigma>'. sym_cond \<sigma> = sym_cond \<sigma>' \<and> Q \<sigma>')"
  using assms by (induction cs arbitrary:\<sigma> Q; auto simp add:pif_def)

lemma sym_stabilize_to_funI_ind :
  assumes "sym_stabilize_fun \<sigma> cs Q"
  shows "sym_stabilize (\<sigma>\<lparr>sym_heap := cs\<rparr>) Q"
  using assms
proof (induction "cs" arbitrary: \<sigma> Q)
  case Nil
  then show ?case by (auto intro: sym_consolidate_nopI simp add: sym_stabilize_def)
next
  case (Cons a cs)
  show ?case
    unfolding sym_stabilize_def
    using Cons.prems apply (simp add:pif_def) apply (safe)
    subgoal
      apply (rule sym_consolidate_frame; simp)
      apply (rule sym_consolidate_mono)
       apply (rule Cons.IH[unfolded sym_stabilize_def])
       apply (rule sym_stabilize_fun_preserves_cond, assumption)
      by (clarsimp)
    subgoal
      apply (rule sym_consolidate_dup)
      apply (rule sym_consolidate_drop; simp)
      apply (drule Cons.IH)
      apply (simp add:sym_stabilize_def)
      done
    done
qed

lemma sym_stabilize_to_funI [sexec_intro]:
  assumes "sym_stabilize_fun \<sigma> (sym_heap \<sigma>) Q"
  shows "sym_stabilize \<sigma> Q"
  using assms sym_stabilize_to_funI_ind by fastforce


(*
var x : bool
inhale x
exhale x
*)
schematic_goal sexec_test1 :
  "sinit [TBool] Map.empty (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Atomic (Pure (Var 0))))
         (stmt.Exhale (Atomic (Pure (Var 0)))))
   (\<lambda> \<sigma>. \<sigma> = ?G))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
inhale x == 1
exhale x > 0
*)
schematic_goal sexec_test2 :
  "sinit [TInt] Map.empty (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Atomic (Pure (Binop (Var 0) Eq (ELit (LInt 1))))))
         (stmt.Exhale (Atomic (Pure (Binop (Var 0) Gt (ELit (LInt 0)))))))
   (\<lambda> \<sigma>. \<sigma> = ?G))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done
  
(*
inhale x == (y ? 1 : 2)
exhale x > 0
*)
lemma sexec_test3 :
  "sinit [TInt, TBool] Map.empty (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Atomic (Pure (Binop (Var 0) Eq (CondExp (Var 1) (ELit (LInt 1)) (ELit (LInt 2)))))))
         (stmt.Exhale (Atomic (Pure (Binop (Var 0) Gt (ELit (LInt 0)))))))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
inhale acc(x.f)
exhale acc(x.f, 1/2) && acc(x.f, 1/2)
*)
lemma sexec_test4 :
  "sinit [TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Atomic (Acc (Var 0) f (PureExp (ELit WritePerm)))))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
         (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
  ))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
inhale acc(x.f) && x.f == 1
exhale acc(x.f, 1/2)
exhale acc(x.f, 1/2) && x.f > 0
*)
lemma sexec_test5 :
  "sinit [TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Star (Atomic (Acc (Var 0) f (PureExp (ELit WritePerm))))
                       (Atomic (Pure (Binop (FieldAcc (Var 0) f) Eq (ELit (LInt 1)))))))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
         (stmt.Exhale (Star (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2))))))
                       (Atomic (Pure (Binop (FieldAcc (Var 0) f) Gt (ELit (LInt 0)))))))
  ))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
inhale acc(x.f) && x.f == 1
exhale acc(x.f, 1/2)
exhale acc(x.f, 1/2)
exhale x.f > 0
*)
lemma sexec_test6 :
  "sinit [TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Star (Atomic (Acc (Var 0) f (PureExp (ELit WritePerm))))
                       (Atomic (Pure (Binop (FieldAcc (Var 0) f) Eq (ELit (LInt 1)))))))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
         (stmt.Exhale (Atomic (Pure (Binop (FieldAcc (Var 0) f) Gt (ELit (LInt 0))))))
  )))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  oops

(*
inhale acc(x.f, wildcard) && x.f == 1
exhale acc(x.f, wildcard)
exhale acc(x.f, wildcard)
exhale x.f > 0
*)
lemma sexec_test6 :
  "sinit [TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Star (Atomic (Acc (Var 0) f Wildcard))
                       (Atomic (Pure (Binop (FieldAcc (Var 0) f) Eq (ELit (LInt 1)))))))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f Wildcard)))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f Wildcard)))
         (stmt.Exhale (Atomic (Pure (Binop (FieldAcc (Var 0) f) Gt (ELit (LInt 0))))))
  )))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
x := 0
y := 1
havoc x
exhale y == 1
x := 0
exhale x == 0
*)
lemma sexec_test7 :
  "sinit [TInt, TInt] Map.empty (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.LocalAssign 0 (ELit (LInt 0)))
    (stmt.Seq (stmt.LocalAssign 1 (ELit (LInt 1)))
    (stmt.Seq (stmt.Havoc 0)
    (stmt.Seq (stmt.Exhale (Atomic (Pure (Binop (Var 1) Eq (ELit (LInt 1))))))
    (stmt.Seq (stmt.LocalAssign 0 (ELit (LInt 0)))
    (stmt.Seq (stmt.Exhale (Atomic (Pure (Binop (Var 0) Eq (ELit (LInt 0))))))
  stmt.Skip))))))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  by (sexec)

(*
inhale acc(x.f)
x.f := 1
exhale acc(x.f, 1/2)
exhale acc(x.f, 1/2) && x.f > 0
*)
lemma sexec_test8 :
  "sinit [TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Atomic (Acc (Var 0) f (PureExp (ELit WritePerm)))))
    (stmt.Seq (stmt.FieldAssign (Var 0) f (ELit (LInt 1)))
    (stmt.Seq (stmt.Exhale (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2)))))))
         (stmt.Exhale (Star (Atomic (Acc (Var 0) f (PureExp (ELit (LPerm (1/2))))))
                       (Atomic (Pure (Binop (FieldAcc (Var 0) f) Gt (ELit (LInt 0)))))))
  )))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done

(*
inhale acc(x.f) && acc(y.f)
inhale z == x || z == y
exhale acc(z.f)
*)
lemma sexec_test9 :
  "sinit [TRef, TRef, TRef] [f \<mapsto> TInt] (\<lambda> \<sigma>.
   sexec \<sigma>
    (stmt.Seq (stmt.Inhale (Star (Atomic (Acc (Var 0) f (PureExp (ELit WritePerm)))) (Atomic (Acc (Var 1) f (PureExp (ELit WritePerm))))))
    (stmt.Seq (stmt.Inhale (Atomic (Pure (Binop (Binop (Var 2) Eq (Var 0)) Or (Binop (Var 2) Eq (Var 1))))))
         (stmt.Exhale (Atomic (Acc (Var 2) f (PureExp (ELit WritePerm)))))
  ))
  (\<lambda> \<sigma>. True))"
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
   apply (sexec_solve)
  apply (sexec)
  done
end