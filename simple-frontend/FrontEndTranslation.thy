theory FrontEndTranslation
  imports CSL_IDF
begin

type_synonym v_stmt = "(int equi_state, int val, int custom) abs_stmt"

fun translate :: "cmd \<Rightarrow> (v_stmt \<times> v_stmt set)" where
  "translate (Calloc r e) = ((Havoc r;; Inhale (full_ownership_with_val r e)), {})"
| "translate ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (P1 \<otimes> P2);; ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (Q1 \<otimes> Q2)),
  let r1 = translate C1 in let r2 = translate C2 in
  { (Inhale P1;; fst r1;; Exhale Q1), (Inhale P2;; fst r2;; Exhale Q2) } \<union> snd r1 \<union> snd r2)"




(*
| RulePar: "\<lbrakk> disjoint (fvC C1 \<union> fvA Q1) (wrC C2); disjoint (fvC C2 \<union> fvA Q2) (wrC C1); self_framing P1; self_framing P2;
    \<turnstile>CSL [P1] C1 [Q1]; \<turnstile>CSL [P2] C2 [Q2] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P1 \<otimes> P2] C1 || C2 [Q1 \<otimes> Q2]"
*)


end