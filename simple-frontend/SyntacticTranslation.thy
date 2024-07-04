theory SyntacticTranslation
  imports FrontEndTranslation
begin

fun translate_binop :: "int_binop \<Rightarrow> binop" where
  "translate_binop Add = binop.Add"
| "translate_binop Sub = binop.Sub"
| "translate_binop Mult = binop.Mult"

fun translate_exp where
  "translate_exp (Evar x) = Var x"
| "translate_exp (Elit l) = ELit (LInt l)"
| "translate_exp (Ebinop e1 op e2) = Binop (translate_exp e1) (translate_binop op) (translate_exp e2)"

fun translate_bexp where
  "translate_bexp (Beq e1 e2) = Binop (translate_exp e1) Eq (translate_exp e2)"
| "translate_bexp (Band e1 e2) = Binop (translate_bexp e1) And (translate_bexp e2)"
| "translate_bexp (Bnot e) = Unop Not (translate_bexp e)"

(*
record ('v, 'a) interp =
  domains :: "'v \<Rightarrow> abs_type"
  predicates :: "'v predicate_loc \<rightharpoonup> 'a set"
  funs :: "function_ident \<Rightarrow> 'v val list \<Rightarrow> 'a \<rightharpoonup> 'v val"

record ('v, 'c) abs_type_context =
  variables :: "var \<rightharpoonup> 'v abs_vtyp"
  custom_context :: 'c
*)
(*
custom_context \<Delta> = type_ctxt_heap
*)
lemma translation_correct_exp:
  assumes "TypedEqui.typed type_ctxt_front_end \<omega>"
(* Also needs something about typed program! *)
  shows "make_semantic_exp \<Delta> (translate_exp e) \<omega> = semantify_exp e \<omega>"
  unfolding make_semantic_exp_def semantify_exp_def
proof (induct e)
  case (Evar x)
(* One can be none, the other one not... *)
  then show ?case sorry
next
  case (Elit x)
  show ?case sorry
(*
  proof (rule ext)
    fix \<omega>
    have "(if \<exists>v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v then Some (SOME v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v) else None)
      = Some (SOME v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v)"
      by (metis RedLit translate_exp.simps(2))
    also have "... = Some (VInt x)"
      using someI[of "\<lambda>v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v" "VInt x"]
    proof -
      have "\<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val (VInt x)"
        by (metis RedLitInt2Val_case calculation option.distinct(1) translate_exp.simps(2) val_of_lit.simps(2))
      then have "\<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val (SOME v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v)"
        using someI by metis
      then show ?thesis
        using \<open>\<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val (VInt x)\<close> red_pure_val_unique(1) by blast
    qed
    finally show "(if \<exists>v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v then Some (SOME v. \<Delta> \<turnstile> \<langle>translate_exp (Elit x);\<omega>\<rangle> [\<Down>] Val v) else None) =
         Some (VInt (edenot (Elit x) (get_store \<omega>)))"
      by fastforce
  qed
*)
next
  case (Ebinop e1 bop e2)
  then show ?case sorry
qed

lemma translation_correct_bexp:
  assumes "TypedEqui.typed type_ctxt_front_end \<omega>"
(* Also needs something about typed program! *)
  shows "make_semantic_bexp \<Delta> (translate_bexp e) \<omega> = semantify_bexp e \<omega>"
  unfolding make_semantic_bexp_def semantify_bexp_def
proof (induct e)
  case (Beq e1 e2)
  then show ?case sorry
next
  case (Band e1 e2)
  then show ?case sorry
next
  case (Bnot e)
  then show ?case sorry
qed

definition syntactic_translate_addr :: "var \<Rightarrow> pure_exp" where
  "syntactic_translate_addr r = Var r"

definition syntactic_translate_heap_loc :: "var \<Rightarrow> pure_exp" where
  "syntactic_translate_heap_loc r = FieldAcc (Var r) field_val"

lemma sound_translate_addr:
  "make_semantic_rexp \<Delta> (syntactic_translate_addr r) = semantify_addr r"
proof (rule ext)
  fix \<omega> show "make_semantic_rexp \<Delta> (syntactic_translate_addr r) \<omega> = semantify_addr r \<omega>"
    unfolding make_semantic_rexp_def semantify_addr_def syntactic_translate_addr_def
    by (smt (verit) Eps_cong RedVar RedVar2Val_case)
qed

lemma sound_translate_heap_loc:
  "make_semantic_exp \<Gamma> (syntactic_translate_heap_loc r) = semantify_heap_loc r"
proof (rule ext)
  fix \<omega> show "make_semantic_exp \<Gamma> (syntactic_translate_heap_loc r) \<omega> = semantify_heap_loc r \<omega>"
    unfolding make_semantic_exp_def syntactic_translate_heap_loc_def semantify_heap_loc_def
    by (smt (verit) RedAccField2Val_case RedVar RedVar2Val_case get_address_simp option.sel red_pure_simps(6) someI_ex)
qed

lemma make_semantic_star:
  "make_semantic_assertion \<Delta> F (A && B) = make_semantic_assertion \<Delta> F A \<otimes> make_semantic_assertion \<Delta> F B"
  by (simp add: make_semantic_assertion_def well_typedly_add_set)

lemma make_semantic_inter_1:
  "make_semantic_assertion \<Delta> F (I && Atomic (Pure (Unop Not (translate_bexp b)))) = (make_semantic_assertion \<Delta> F I) \<inter> assertify_bexp (Bnot b)"
  sorry

(*
lemma make_semantic_inter_2:
  "make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (translate_bexp b))) = (make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic I) \<inter> assertify_bexp b"
proof
  show "make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (translate_bexp b))) \<subseteq> make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic I \<inter> assertify_bexp b"
    unfolding make_semantic_assertion_def well_typedly_def
  proof
    fix \<omega> assume "\<omega> \<in> Set.filter (typed (make_context_semantic \<Delta> type_ctxt_front_end_syntactic)) (\<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle>)"
    then obtain i p where ip: "Some \<omega> = i \<oplus> p" "i \<in> \<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I\<rangle>" "p \<in> \<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>Atomic (Pure (translate_bexp b))\<rangle>"     
      by (smt (verit, ccfv_threshold) member_filter sat_set.simps(4) snd_conv type_ctxt_front_end_syntactic_def x_elem_set_product)
    then have "pure p"
      by (metis CollectD Instantiation.atomic_assert.simps(1) Int_iff corely_def emp_core_def red_pure_assert_def sat_set.simps(1))
    then have "\<omega> \<in> \<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I\<rangle>"
      using ip(1-2)
      sorry (* TODO: Prove *)
    moreover have "get_store \<omega> = get_store p"
      by (metis \<open>Some \<omega> = i \<oplus> p\<close> commutative full_add_charact(1))
    moreover have "typed type_ctxt_front_end \<omega>" using make_context_semantic_type_ctxt
      by (metis \<open>\<omega> \<in> Set.filter (typed (make_context_semantic \<Delta> type_ctxt_front_end_syntactic)) (\<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle>)\<close> member_filter)
    then have "TypedEqui.typed type_ctxt_front_end p"
      by (metis TypedEqui.typed_smaller commutative greater_def ip(1))
    then have "bdenot b (get_store p)"
      using translation_correct_bexp[of p _ b] ip(3)
      unfolding semantify_bexp_def make_semantic_bexp_def assertify_bexp_def sat_set.simps atomic_assert.simps red_pure_assert_def
        corely_def
      by (metis Int_Collect inf.commute option.inject)
    ultimately have "\<omega> \<in> assertify_bexp b"
      using translation_correct_bexp[of _ _ b] ip(3) unfolding semantify_bexp_def make_semantic_bexp_def assertify_bexp_def
      by simp
    then show "\<omega> \<in> Set.filter (typed (make_context_semantic \<Delta> type_ctxt_front_end_syntactic)) (\<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I\<rangle>) \<inter> assertify_bexp b"
      by (simp add: \<open>\<omega> \<in> \<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I\<rangle>\<close> \<open>typed type_ctxt_front_end \<omega>\<close> make_context_semantic_type_ctxt)
  qed
  show "make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic I \<inter> assertify_bexp b
    \<subseteq> make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic (I && Atomic (Pure (translate_bexp b)))"
    unfolding make_semantic_assertion_def assertify_bexp_def well_typedly_def
  proof
    fix \<omega>
    assume asm0: "\<omega> \<in> Set.filter (typed (make_context_semantic \<Delta> type_ctxt_front_end_syntactic)) (\<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I\<rangle>) \<inter>
             {\<omega> |\<omega>. bdenot b (get_store \<omega>)}"
    moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
      using core_is_smaller by auto
    moreover have "TypedEqui.typed type_ctxt_front_end \<omega>"
      by (metis IntD1 asm0 make_context_semantic_type_ctxt member_filter)
    then have "|\<omega>| \<in> \<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>Atomic (Pure (translate_bexp b))\<rangle>"
      using translation_correct_bexp[of _ _ b] asm0
      unfolding sat_set.simps atomic_assert.simps red_pure_assert_def corely_def semantify_bexp_def make_semantic_bexp_def
      by (metis (no_types, lifting) Int_iff TypedEqui.typed_core core_charact(1) core_in_emp_core mem_Collect_eq option.distinct(1) option.inject)
    ultimately show "\<omega> \<in> Set.filter (typed (make_context_semantic \<Delta> type_ctxt_front_end_syntactic))
               (\<langle>\<Delta>, snd type_ctxt_front_end_syntactic\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle>)"
      using x_elem_set_product
      by (smt (verit, ccfv_threshold) IntD1 member_filter sat_set.simps(4) snd_conv type_ctxt_front_end_syntactic_def)
  qed
qed
*)
(*
lemma full_ownership_translation_sound:
  "make_semantic_assertion \<Delta> type_ctxt_front_end_syntactic (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1)))))
  = typed_stabilize (full_ownership r)"
  unfolding make_semantic_assertion_def well_typedly_def full_ownership_def sat_set.simps atomic_assert.simps
    TypedEqui.Stabilize_typed_def red_pure_assert_def corely_def emp_core_def
  apply simp
proof -
  have "(\<Union>x xa xb.
         \<Delta> \<turnstile> \<langle>Var r\<rangle> [\<Down>] Val (VRef x) \<otimes> \<llangle>snd type_ctxt_front_end_syntactic field_val = Some xb\<rrangle> \<otimes>
         (\<Union>p'. \<Delta> \<turnstile> \<langle>ELit WritePerm\<rangle> [\<Down>] Val (VPerm p') \<otimes> \<llangle>xa = Some p'\<rrangle>) \<otimes>
         acc \<Delta> xb x field_val xa) =
 (Stabilize {\<omega>. \<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1})" (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix \<omega> assume asm0: "\<omega> \<in> ?A"
      then obtain x xa xb where "\<omega> \<in> \<Delta> \<turnstile> \<langle>Var r\<rangle> [\<Down>] Val (VRef x) \<otimes> \<llangle>snd type_ctxt_front_end_syntactic field_val = Some xb\<rrangle> \<otimes>
           (\<Union>p'. \<Delta> \<turnstile> \<langle>ELit WritePerm\<rangle> [\<Down>] Val (VPerm p') \<otimes> \<llangle>xa = Some p'\<rrangle>) \<otimes>
           acc \<Delta> xb x field_val xa"
        by (smt (z3) UN_iff snd_conv type_ctxt_front_end_syntactic_def)
      then show "\<omega> \<in> ?B"
        sorry
    qed
    show "?B \<subseteq> ?A"
    proof
      fix \<omega> assume asm0: "\<omega> \<in> ?B"
      then obtain l where "get_store (stabilize \<omega>) r = Some (VRef (Address l))" "get_m (stabilize \<omega>) (l, field_val) = 1"
        by auto

      then show "\<omega> \<in> ?A" sorry
    qed
  qed
  then show "Set.filter (typed tcfe)
     (\<Union>x xa xb.
         {\<omega>. \<Delta> \<turnstile> \<langle>Var r;\<omega>\<rangle> [\<Down>] Val (VRef x)} \<inter> Collect pure \<otimes> \<llangle>snd type_ctxt_front_end_syntactic field_val = Some xb\<rrangle> \<otimes>
         (\<Union>p'. {\<omega>. \<Delta> \<turnstile> \<langle>ELit WritePerm;\<omega>\<rangle> [\<Down>] Val (VPerm p')} \<inter> Collect pure \<otimes> \<llangle>xa = Some p'\<rrangle>) \<otimes>
         acc \<Delta> xb x field_val xa) =
    Set.filter (typed tcfe) (Stabilize {\<omega>. \<exists>l. get_store \<omega> r = Some (VRef (Address l)) \<and> get_m \<omega> (l, field_val) = 1})"
    unfolding red_pure_assert_def corely_def emp_core_def
    by fastforce
qed
*)

lemma full_ownership_with_val_sound:
  "make_semantic_assertion \<Delta> F (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1)))) && Atomic (Pure (FieldAcc (Var r) field_val)))
  = typed_stabilize (full_ownership_with_val r e)"
  (* Does not hold if make_semantic_assertion does not use well_typedly*)
  oops


fun translate_syn where
  "translate_syn \<Delta> F Cskip = (stmt.Skip, {})"
| "translate_syn \<Delta> F (Cassign x e) = (stmt.LocalAssign x (translate_exp e), {})"

| "translate_syn \<Delta> F (Calloc r e) = ((stmt.Seq (stmt.Havoc r)
  (stmt.Inhale (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1)))) && Atomic (Pure (FieldAcc (Var r) field_val))))), {})"

| "translate_syn \<Delta> F (Cfree r) = (stmt.Exhale (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1))))), {})"

| "translate_syn \<Delta> F (Cwrite r e) = (stmt.FieldAssign (syntactic_translate_addr r) field_val (translate_exp e), {})"

| "translate_syn \<Delta> F (Cread x r) = (stmt.LocalAssign x (syntactic_translate_heap_loc r), {})"

| "translate_syn \<Delta> F (Cseq C1 C2) = (let r1 = translate_syn \<Delta> F C1 in let r2 = translate_syn \<Delta> F C2 in
  (stmt.Seq (fst r1) (fst r2), snd r1 \<union> snd r2))"

| "translate_syn \<Delta> F (Cif b C1 C2) =
  (stmt.If (translate_bexp b) (fst (translate_syn \<Delta> F C1)) (fst (translate_syn \<Delta> F C2)), snd (translate_syn \<Delta> F C1) \<union> snd (translate_syn \<Delta> F C2))"

| "translate_syn \<Delta> F ({P1} C1 {Q1} || {P2} C2 {Q2}) =
  (stmt.Seq (stmt.Seq
    (stmt.Exhale (P1 && P2))
    (n_havoc (wrL C1 @ wrL C2)))
    (stmt.Inhale (Q1 && Q2)),
  let r1 = translate_syn \<Delta> F C1 in let r2 = translate_syn \<Delta> F C2 in
  { stmt.Seq (stmt.Seq (stmt.Inhale P1) (fst r1)) (stmt.Exhale Q1),
    stmt.Seq (stmt.Seq (stmt.Inhale P2) (fst r2)) (stmt.Exhale Q2)}
    \<union> snd r1 \<union> snd r2)"

| "translate_syn \<Delta> F (Cwhile b I C) =
  (stmt.Seq (stmt.Seq (stmt.Exhale I) (n_havoc (wrL C))) (stmt.Inhale (I && Atomic (Pure (Unop Not (translate_bexp b))))),
  { stmt.Seq (stmt.Seq (stmt.Inhale (I && Atomic (Pure (translate_bexp b)))) (fst (translate_syn \<Delta> F C))) (stmt.Exhale I) }
  \<union> snd (translate_syn \<Delta> F C))"

lemma havoc_list_n_havoc_same:
  "compile \<Delta> F (n_havoc l) = ConcreteSemantics.havoc_list l"
  by (induct l) simp_all

thm ConcreteSemantics.verifies_set_def ConcreteSemantics.verifies_def

inductive_simps ConcreteSemantics_red_stmt_simps :
  "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.LocalAssign x e) \<omega> S"
  "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Exhale A) \<omega> S"
  "ConcreteSemantics.red_stmt \<Delta> (abs_stmt.Inhale A) \<omega> S"
  "ConcreteSemantics.red_stmt \<Delta> (C1;;C2) \<omega> S"
  "ConcreteSemantics.red_stmt \<Delta> (Custom (custom.FieldAssign e1 f e2)) \<omega> S"

lemma make_semantic_exp_implies_semantify_exp :
  assumes "make_semantic_exp \<Delta> (translate_exp e) \<omega> = Some v"
  assumes "typed tcfe \<omega>"
  (* TODO: also needs to e has integer type *)
  shows "semantify_exp e \<omega> = Some v"
  using assms
proof (induction e arbitrary:v)
  case (Evar x)
  then show ?case
    apply (simp add:semantify_exp_def red_pure_simps)
    sorry
next
  case (Elit x)
  then show ?case by (simp add:semantify_exp_def red_pure_simps)
next
  case (Ebinop e1 op e2)
  then show ?case
    by (cases "op"; clarsimp simp add:semantify_exp_def red_pure_simps; fastforce)
qed

lemma red_stmt_LocalAssign_mono :
  assumes "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.LocalAssign x e1) \<omega> S"
  assumes "\<And> v. e1 \<omega> = Some v \<Longrightarrow> e2 \<omega> = Some v"
  shows "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.LocalAssign x e2) \<omega> S"
  using assms by (clarsimp simp add:ConcreteSemantics_red_stmt_simps)

lemma red_stmt_FieldAssign_mono :
  assumes "ConcreteSemantics.red_stmt \<Gamma> (Custom (custom.FieldAssign e1 f e2)) \<omega> S"
  assumes "\<And> v. e2 \<omega> = Some v \<Longrightarrow> e2' \<omega> = Some v"
  shows "ConcreteSemantics.red_stmt \<Gamma> (Custom (custom.FieldAssign e1 f e2')) \<omega> S"
  using assms by (clarsimp simp add:ConcreteSemantics_red_stmt_simps red_custom_stmt.simps)

lemma red_stmt_Seq_mono :
  assumes "ConcreteSemantics.red_stmt \<Gamma> (C1;;C2) \<omega> S"
  assumes "\<And> S'. ConcreteSemantics.red_stmt \<Gamma> C1 \<omega> S' \<Longrightarrow> 
       ConcreteSemantics.red_stmt \<Gamma> C1' \<omega> S' \<and> (\<forall> \<omega>' S''. \<omega>' \<in> S' \<longrightarrow>
      ConcreteSemantics.red_stmt \<Gamma> C2 \<omega>' S'' \<longrightarrow> ConcreteSemantics.red_stmt \<Gamma> C2' \<omega>' S'')"
  shows "ConcreteSemantics.red_stmt \<Gamma> (C1';;C2') \<omega> S"
  using assms
  apply (clarsimp simp add:ConcreteSemantics_red_stmt_simps ConcreteSemantics.sequential_composition.simps)
  by blast

lemma red_stmt_Exhale_mono :
  assumes "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.Exhale A1) \<omega> S"
  assumes "\<And> \<omega>'. stable \<omega>' \<Longrightarrow> \<omega> \<in> {\<omega>'} \<otimes> A1 \<Longrightarrow> \<omega> \<in> {\<omega>'} \<otimes> A2"
  shows "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.Exhale A2) \<omega> S"
  using assms
  apply (clarsimp simp add:ConcreteSemantics_red_stmt_simps add_set_def)
  by blast

lemma red_stmt_Inhale_mono :
  assumes "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.Inhale A1) \<omega> S"
  assumes "rel_stable_assertion \<omega> A1 \<Longrightarrow> rel_stable_assertion \<omega> A2"
  assumes "Set.filter stable ({\<omega>} \<otimes> A1) = Set.filter stable ({\<omega>} \<otimes> A2)"
  assumes "\<And> \<omega>'. stable \<omega>' \<Longrightarrow> \<omega> \<in> {\<omega>'} \<otimes> A1 \<Longrightarrow> \<omega> \<in> {\<omega>'} \<otimes> A2"
  shows "ConcreteSemantics.red_stmt \<Gamma> (abs_stmt.Inhale A2) \<omega> S"
  using assms
  by (clarsimp simp add:ConcreteSemantics_red_stmt_simps)

lemma translation_refines:
  assumes "ConcreteSemantics.red_stmt tcfe (compile \<Delta> F (fst (translate_syn \<Delta> F C))) \<omega> S"
      and "typed tcfe \<omega>"
      and "stable \<omega>"
  shows "ConcreteSemantics.red_stmt tcfe (fst (translate \<Delta> C)) \<omega> S"
  using assms
proof (induct C arbitrary: \<omega> S)
  case (Cassign x1 x2)
  then show ?case
    apply (simp)
    apply (rule red_stmt_LocalAssign_mono) apply (assumption)
    by (rule make_semantic_exp_implies_semantify_exp)
next
  case (Cwrite x1 x2)
  then show ?case
    apply (simp add:sound_translate_addr)
    apply (rule red_stmt_FieldAssign_mono) apply (assumption)
    by (rule make_semantic_exp_implies_semantify_exp)
next
  case (Calloc x1 x2)
  then show ?case
    apply (simp)
    apply (rule red_stmt_Seq_mono) apply (assumption)
    apply (rule) apply (assumption)
    apply (rule; simp)
    sorry
next
  case (Cfree x)
  then show ?case
    apply (simp)
    apply (rule red_stmt_Exhale_mono) apply (assumption)
    sorry
next
  case (Cseq C1 C2)
  then show ?case
    apply (simp add:)
    sorry
next
  case (Cpar x1 C1 x3 x4 C2 x6a)
  then show ?case sorry
next
  case (Cif x1 C1 C2)
  then show ?case sorry
next
  case (Cwhile x1 x2 C)
  then show ?case sorry
qed (simp_all add: sound_translate_heap_loc)

(*
      and "ConcreteSemantics.verifies_set tcfe (atrue tcfe) (Inhale P;; fst (translate \<Gamma> C);; Exhale Q)"
      and "\<And>Cv. Cv \<in> snd (translate \<Gamma> C) \<Longrightarrow> ConcreteSemantics.verifies_set tcfe (atrue tcfe) Cv"
*)

(* main theorem *)
(* does not hold since the sets are not actually equal *)
(*
lemma translation_same:
  "compile \<Delta> F (fst (translate_syn \<Delta> F C)) = fst (translate \<Delta> C) \<and> compile \<Delta> F ` (snd (translate_syn \<Delta> F C)) = snd (translate \<Delta> C)"
proof (induct C)
  case (Cassign x1 x2)
  then show ?case using translation_correct_exp compile.simps(5) translate.simps(2) translate_syn.simps(2)
    by simp
next
  case (Cread x1 x2)
  then show ?case unfolding translate.simps translate_syn.simps
    using sound_translate_heap_loc by force
next
  case (Cwrite x1 x2)
  then show ?case unfolding translate.simps translate_syn.simps
    using sound_translate_addr translation_correct_exp by auto
next
  case (Calloc x1 x2)
  then show ?case unfolding translate.simps translate_syn.simps
    by (simp add: full_ownership_with_val_sound)
next
  case (Cfree x)
  then show ?case unfolding translate.simps translate_syn.simps
    using full_ownership_translation_sound by force
next
  case (Cseq C1 C2)
  then show ?case
    by (metis compile.simps(3) fst_eqD image_Un snd_eqD translate.simps(7) translate_syn.simps(7))
next
  case (Cpar x1 C1 x3 x4 C2 x6a)
  show ?case
  proof
    show "compile \<Delta> F (fst (translate_syn \<Delta> F {x1} C1 {x3} || {x4} C2 {x6a})) = fst (translate \<Delta> F {x1} C1 {x3} || {x4} C2 {x6a})"
      unfolding translate.simps translate_syn.simps
      by (simp add: havoc_list_n_havoc_same make_semantic_star)
    show "compile \<Delta> F ` snd (translate_syn \<Delta> F {x1} C1 {x3} || {x4} C2 {x6a}) = snd (translate \<Delta> F {x1} C1 {x3} || {x4} C2 {x6a})"
      unfolding translate.simps translate_syn.simps 
      apply (simp add: make_semantic_star)
      by (metis Cpar.hyps(1) Cpar.hyps(2) compile.simps(3) compile.simps(6) compile.simps(7) image_Un image_insert)
  qed
next
  case (Cif x1 C1 C2)
  then show ?case unfolding translate.simps translate_syn.simps
    by (simp add: image_Un translation_correct_bexp)
next
  case (Cwhile x1 x2 C)
  show ?case
  proof
    show "compile \<Delta> F (fst (translate_syn \<Delta> F (Cwhile x1 x2 C))) = fst (translate \<Delta> F (Cwhile x1 x2 C))"
      unfolding translate.simps translate_syn.simps
      by (simp add: havoc_list_n_havoc_same make_semantic_inter_1)
    show "compile \<Delta> F ` snd (translate_syn \<Delta> F (Cwhile x1 x2 C)) = snd (translate \<Delta> F (Cwhile x1 x2 C))"
      unfolding translate.simps translate_syn.simps
      apply (simp add: havoc_list_n_havoc_same make_semantic_inter_2)
      using Cwhile by presburger
  qed
qed (simp_all)
*)



end