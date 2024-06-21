theory FrontEndTranslation
  imports CSL_IDF
begin

type_synonym v_stmt = "(int equi_state, int val, int custom) abs_stmt"

fun translate :: "cmd \<Rightarrow> (v_stmt \<times> v_stmt set)" where
  "translate Cskip = (Skip, {})"
| "translate (Calloc r e) = ((Havoc r;; Inhale (full_ownership_with_val r e)), {})"
| "translate ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  ((Exhale (P1 \<otimes> P2);; ConcreteSemantics.havoc_list (wrL C1 @ wrL C2);; Inhale (Q1 \<otimes> Q2)),
  let r1 = translate C1 in let r2 = translate C2 in
  { (Inhale P1;; fst r1;; Exhale Q1), (Inhale P2;; fst r2;; Exhale Q2) } \<union> snd r1 \<union> snd r2)"

thm ConcreteSemantics.Viper_implies_SL_proof
thm emp_star_right_id

definition has_Viper_proof where
  "has_Viper_proof \<Delta> Cv \<longleftrightarrow> (\<exists>B. ConcreteSemantics.SL_proof \<Delta> emp Cv B)"

definition translation_has_proof where
  "translation_has_proof \<Delta> P C Q \<longleftrightarrow> (\<exists>B. ConcreteSemantics.SL_proof \<Delta> P (fst (translate C)) (B \<otimes> Q)) \<and>
  (\<forall>Cv \<in> snd (translate C). has_Viper_proof \<Delta> Cv)"

lemma translation_has_proofI:
  assumes "\<exists>B. ConcreteSemantics.SL_proof \<Delta> P (fst (translate C)) (B \<otimes> Q)"
      and "\<And>Cv. Cv \<in> snd (translate C) \<Longrightarrow> has_Viper_proof \<Delta> Cv"
    shows "translation_has_proof \<Delta> P C Q"
  by (simp add: assms(1) assms(2) translation_has_proof_def)


lemma has_proof_with_inhale_exhale:
  assumes "has_Viper_proof \<Delta> (Inhale P;; C;; Exhale Q)"
  shows "\<exists>R B. ConcreteSemantics.SL_proof \<Delta> P C R \<and> entails R (B \<otimes> Q)"
proof -
  obtain B where "ConcreteSemantics.SL_proof \<Delta> emp ((Inhale P;; C);; Exhale Q) B"
    using assms has_Viper_proof_def by blast
  then show ?thesis
  proof (rule ConcreteSemantics.SL_proof_Seq_elim)
    fix R1 assume asm0: "ConcreteSemantics.SL_proof \<Delta> emp (abs_stmt.Inhale P ;; C) R1"
      "ConcreteSemantics.SL_proof \<Delta> R1 (abs_stmt.Exhale Q) B"
    then have "entails R1 (B \<otimes> Q)" by auto (* ConcreteSemantics.SL_proof_Exhale_elim[OF asm0(2)] *)
    show "\<exists>R B. ConcreteSemantics.SL_proof \<Delta> P C R \<and> entails R (B \<otimes> Q)"
    proof (rule ConcreteSemantics.SL_proof_Seq_elim[OF asm0(1)])
      fix R0 assume asm1: "ConcreteSemantics.SL_proof \<Delta> emp (abs_stmt.Inhale P) R0"
        "ConcreteSemantics.SL_proof \<Delta> R0 C R1"
      then have "ConcreteSemantics.SL_proof \<Delta> P C R1"
        by auto
      then show "\<exists>R B. ConcreteSemantics.SL_proof \<Delta> P C R \<and> entails R (B \<otimes> Q)"
        using \<open>entails R1 (B \<otimes> Q)\<close> by blast
    qed
  qed
qed

lemma translation_convert_proof:
  assumes "translation_has_proof \<Delta> P C Q"
      and "well_typed_cmd \<Delta> C"
  shows "\<exists>R. \<Delta> \<turnstile>CSL [P] C [Q \<otimes> R]" (* should have every assertion up_closed, and thus no R *)
  using assms
proof (induct C arbitrary: P Q)
  case Cskip
  then obtain B where "ConcreteSemantics.SL_proof \<Delta> P Skip (B \<otimes> Q)"
    unfolding translation_has_proof_def by force
  then show ?case
    by (metis ConcreteSemantics.SL_proof_Skip_elim RuleSkip add_set_commm)
next
  case (Cassign x1 x2)
  then show ?case sorry
next
  case (Cread x1 x2)
  then show ?case sorry
next
  case (Cwrite x1 x2)
  then show ?case sorry
next
  case (Calloc r e)
  then obtain B where "ConcreteSemantics.SL_proof \<Delta> P (Havoc r;; Inhale (full_ownership_with_val r e)) (B \<otimes> Q)"
    unfolding translation_has_proof_def by force
  then have "ConcreteSemantics.SL_proof \<Delta> P (Havoc r) (TypedEqui.exists_assert \<Delta> r P)
  \<and> ConcreteSemantics.SL_proof \<Delta> (TypedEqui.exists_assert \<Delta> r P) (Inhale (full_ownership_with_val r e)) (B \<otimes> Q)
  \<and> TypedEqui.self_framing_typed \<Delta> P"
    by (metis ConcreteSemantics.SL_proof_Havoc_elim ConcreteSemantics.SL_proof_Seq_elim)
  then have "B \<otimes> Q = TypedEqui.exists_assert \<Delta> r P \<otimes> full_ownership_with_val r e"
    by blast

  have "\<Delta> \<turnstile>CSL [UNIV \<otimes> TypedEqui.exists_assert \<Delta> r P] Calloc r e [full_ownership_with_val r e \<otimes> TypedEqui.exists_assert \<Delta> r P]"
  proof (rule RuleFrame)
    have "r \<notin> fvE e" sorry (* should come from well-definedness *)
    then show "\<Delta> \<turnstile>CSL [UNIV] Calloc r e [full_ownership_with_val r e]"
      using RuleAlloc[of r e] by simp
    show "disjoint (fvA (TypedEqui.exists_assert \<Delta> r P)) (wrC (Calloc r e))" sorry (* Should come from fvA *)
    show "TypedEqui.self_framing_typed \<Delta> UNIV"
      using TypedEqui.self_framing_typed_def by blast
    show "TypedEqui.self_framing_typed \<Delta> (TypedEqui.exists_assert \<Delta> r P)"
      using \<open>ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Havoc r) (TypedEqui.exists_assert \<Delta> r P) \<and> ConcreteSemantics.SL_proof \<Delta> (TypedEqui.exists_assert \<Delta> r P) (abs_stmt.Inhale (full_ownership_with_val r e)) (B \<otimes> Q) \<and> TypedEqui.self_framing_typed \<Delta> P\<close> by auto
    show "TypedEqui.typed_assertion \<Delta> (TypedEqui.exists_assert \<Delta> r P)"
      using \<open>ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Havoc r) (TypedEqui.exists_assert \<Delta> r P) \<and> ConcreteSemantics.SL_proof \<Delta> (TypedEqui.exists_assert \<Delta> r P) (abs_stmt.Inhale (full_ownership_with_val r e)) (B \<otimes> Q) \<and> TypedEqui.self_framing_typed \<Delta> P\<close> by blast
    show "TypedEqui.typed_assertion \<Delta> UNIV" sorry (* TODO: Adapt to typed true *)
  qed

  moreover have "UNIV \<otimes> TypedEqui.exists_assert \<Delta> r P = P"
    sorry (* Comes from P mono *)
  moreover have "TypedEqui.typed_assertion \<Delta> P \<and> variables \<Delta> r \<noteq> None"
  proof
    show "TypedEqui.typed_assertion \<Delta> P"
      using \<open>ConcreteSemantics.SL_proof \<Delta> P (abs_stmt.Havoc r) (TypedEqui.exists_assert \<Delta> r P) \<and> ConcreteSemantics.SL_proof \<Delta> (TypedEqui.exists_assert \<Delta> r P) (abs_stmt.Inhale (full_ownership_with_val r e)) (B \<otimes> Q) \<and> TypedEqui.self_framing_typed \<Delta> P\<close> by blast
    show "variables \<Delta> r \<noteq> None" (* Should come from the well-typedness of the program *)
      using Calloc.prems(2) by auto
  qed
  then have "entails P (TypedEqui.exists_assert \<Delta> r P)"
 (* TODO: Should work, and be given by AbstractSem *)
    using ConcreteSemantics.SL_proof_Havoc_elim_entails[of \<Delta> P r "TypedEqui.exists_assert \<Delta> r P"]    
    using ConcreteSemantics.exists_assert_entails by blast

  then show "\<exists>R. \<Delta> \<turnstile>CSL [P] Calloc r e [Q \<otimes> R]" using RuleCons
    by (metis \<open>B \<otimes> Q = TypedEqui.exists_assert \<Delta> r P \<otimes> full_ownership_with_val r e\<close> add_set_commm calculation(1) calculation(2))
next
  case (Cfree x)
  then show ?case sorry
next
  case (Cseq C1 C2)
  then show ?case sorry
next
  case (Cpar P1 C1 Q1 P2 C2 Q2)
  have "translation_has_proof \<Delta> P1 C1 Q1"
  proof (rule translation_has_proofI)
    show "\<exists>B. ConcreteSemantics.SL_proof \<Delta> P1 (fst (translate C1)) (B \<otimes> Q1)"
      using has_proof_with_inhale_exhale

  then obtain R1 R2 where "
(*
    translation_has_proof \<Delta> ?P C1 ?Q \<Longrightarrow> \<exists>R. \<turnstile>CSL [?P] C1 [?Q \<otimes> R]
    translation_has_proof \<Delta> ?P C2 ?Q \<Longrightarrow> \<exists>R. \<turnstile>CSL [?P] C2 [?Q \<otimes> R]
    translation_has_proof \<Delta> P {P1} C1 {Q1} || {P2} C2 {Q2} Q
*)
(*
\<exists>R. \<turnstile>CSL [P] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> R]
*)
  then show "\<exists>R. \<turnstile>CSL [P] {P1} C1 {Q1} || {P2} C2 {Q2} [Q \<otimes> R]" sorry
next
  case (Cif x1 C1 C2)
  then show ?case sorry
next
  case (Cwhile x1 C)
  then show ?case sorry
qed



lemma parallel_translation_correct:
  assumes "translation_has_proof \<Delta> ({P1} C1 {Q1} || {P2} C2 {Q2})"
  shows "\<exists>B. \<turnstile>CSL [P] C [B "
  sorry


(*
| RulePar: "\<lbrakk> disjoint (fvC C1 \<union> fvA Q1) (wrC C2); disjoint (fvC C2 \<union> fvA Q2) (wrC C1); self_framing P1; self_framing P2;
    \<turnstile>CSL [P1] C1 [Q1]; \<turnstile>CSL [P2] C2 [Q2] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P1 \<otimes> P2] C1 || C2 [Q1 \<otimes> Q2]"
*)


end