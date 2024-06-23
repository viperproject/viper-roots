theory SyntacticTranslation
  imports FrontEndTranslation
begin

fun translate_binop :: "int_binop \<Rightarrow> binop" where
  "translate_binop Add = binop.Add"
| "translate_binop Sub = binop.Sub"
| "translate_binop Mult = binop.Mult"
| "translate_binop Mod = binop.Mod"

fun translate_exp where
  "translate_exp (Evar x) = Var x"
| "translate_exp (Elit l) = ELit (LInt l)"
| "translate_exp (Ebinop e1 op e2) = Binop (translate_exp e1) (translate_binop op) (translate_exp e2)"

term binop.Add

fun translate_bexp where
  "translate_bexp (Beq e1 e2) = Binop (translate_exp e1) Eq (translate_exp e2)"
| "translate_bexp (Band e1 e2) = Binop (translate_bexp e1) And (translate_bexp e2)"
| "translate_bexp (Bnot e) = Unop Not (translate_bexp e)"

lemma translation_correct_exp:
  "make_semantic_exp \<Delta> (translate_exp e) = semantify_exp e"
  unfolding make_semantic_exp_def semantify_exp_def
proof (induct e)
  case (Evar x)
  then show ?case sorry
next
  case (Elit x)
(* One can be none, the other one not... *)
  then show ?case sorry
next
  case (Ebinop e1 x2a e2)
  then show ?case sorry
qed

lemma translation_correct_bexp:
  "make_semantic_bexp \<Delta> (translate_bexp e) = semantify_bexp e"
  sorry

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
  "make_semantic_exp \<Delta> (syntactic_translate_heap_loc r) = semantify_heap_loc r"
proof (rule ext)
  fix \<omega> show "make_semantic_exp \<Delta> (syntactic_translate_heap_loc r) \<omega> = semantify_heap_loc r \<omega>"
    unfolding make_semantic_exp_def syntactic_translate_heap_loc_def semantify_heap_loc_def
    by (smt (verit) RedAccField2Val_case RedVar RedVar2Val_case get_address_simp option.sel red_pure_simps(6) someI_ex)
qed

lemma make_semantic_star:
  "make_semantic_assertion \<Delta> F (A && B) = make_semantic_assertion \<Delta> F A \<otimes> make_semantic_assertion \<Delta> F B"
  by (simp add: make_semantic_assertion_def well_typedly_add_set)

lemma make_semantic_inter_1:
  "make_semantic_assertion \<Delta> F (I && Atomic (Pure (Unop Not (translate_bexp b)))) = (make_semantic_assertion \<Delta> F I) \<inter> assertify_bexp (Bnot b)"
  sorry

lemma make_semantic_inter_2:
  "make_semantic_assertion \<Delta> F (I && Atomic (Pure (translate_bexp b))) = (make_semantic_assertion \<Delta> F I) \<inter> assertify_bexp b"
proof
  show "make_semantic_assertion \<Delta> F (I && Atomic (Pure (translate_bexp b))) \<subseteq> make_semantic_assertion \<Delta> F I \<inter> assertify_bexp b"
    unfolding make_semantic_assertion_def well_typedly_def
  proof
    fix \<omega> assume "\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle> \<inter> {\<omega> |\<omega>. well_typed (map_option (make_semantic_vtyp \<Delta>) \<circ> F) (get_abs_state \<omega>)}"
    then obtain i p where ip: "Some \<omega> = i \<oplus> p" "i \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I\<rangle>" "p \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>Atomic (Pure (translate_bexp b))\<rangle>"
      by (smt (verit, ccfv_SIG) IntD1 sat_set.simps(4) x_elem_set_product)
    then have "\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I\<rangle>" (* up_closed, p is pure *)
      sorry
    moreover have "get_store \<omega> = get_store p"
      by (metis \<open>Some \<omega> = i \<oplus> p\<close> commutative full_add_charact(1))
    moreover have "bdenot b (get_store p)"
      using translation_correct_bexp[of \<Delta> b] ip(3)
      unfolding semantify_bexp_def make_semantic_bexp_def assertify_bexp_def sat_set.simps atomic_assert.simps red_pure_assert_def
        corely_def
      by (metis (no_types, lifting) CollectD IntD1 option.inject)

    ultimately have "\<omega> \<in> assertify_bexp b"
      using translation_correct_bexp[of \<Delta> b] ip(3) unfolding semantify_bexp_def make_semantic_bexp_def assertify_bexp_def
      by simp
    then show "\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I\<rangle> \<inter> {\<omega> |\<omega>. well_typed (map_option (make_semantic_vtyp \<Delta>) \<circ> F) (get_abs_state \<omega>)} \<inter> assertify_bexp b"
      using \<open>\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle> \<inter> {\<omega> |\<omega>. well_typed (map_option (make_semantic_vtyp \<Delta>) \<circ> F) (get_abs_state \<omega>)}\<close>
      using \<open>\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I\<rangle>\<close> by blast
  qed
  show "make_semantic_assertion \<Delta> F I \<inter> assertify_bexp b \<subseteq> make_semantic_assertion \<Delta> F (I && Atomic (Pure (translate_bexp b)))"
    unfolding make_semantic_assertion_def assertify_bexp_def well_typedly_def
  proof
    fix \<omega>
    assume asm0: "\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I\<rangle> \<inter> {\<omega> |\<omega>. well_typed (map_option (make_semantic_vtyp \<Delta>) \<circ> F) (get_abs_state \<omega>)} \<inter> {\<omega> |\<omega>. bdenot b (get_store \<omega>)}"
    moreover have "Some \<omega> = \<omega> \<oplus> |\<omega>|"
      using core_is_smaller by auto
    moreover have "|\<omega>| \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>Atomic (Pure (translate_bexp b))\<rangle>"
      using translation_correct_bexp[of \<Delta> b] asm0
      unfolding sat_set.simps atomic_assert.simps red_pure_assert_def corely_def semantify_bexp_def make_semantic_bexp_def
      by (metis (no_types, lifting) Int_Collect Int_iff core_charact(1) core_in_emp_core option.distinct(1) option.inject)
    ultimately show "\<omega> \<in> \<langle>\<Delta>, F\<rangle> \<Turnstile> \<langle>I && Atomic (Pure (translate_bexp b))\<rangle> \<inter> {\<omega> |\<omega>. well_typed (map_option (make_semantic_vtyp \<Delta>) \<circ> F) (get_abs_state \<omega>)}"
      using x_elem_set_product by fastforce
  qed
qed


lemma full_ownership_translation_sound:
  "make_semantic_assertion \<Delta> F (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1))))) = Stabilize (full_ownership r)"
  sorry

lemma full_ownership_with_val_sound:
  "make_semantic_assertion \<Delta> F (Atomic (Acc (Var r) field_val (PureExp (ELit (LPerm 1)))) && Atomic (Pure (FieldAcc (Var r) field_val)))
  = full_ownership_with_val r e"
  sorry


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

(* main theorem *)
lemma translation_same:
  "compile \<Delta> F (fst (translate_syn \<Delta> F C)) = fst (translate \<Delta> F C) \<and> compile \<Delta> F ` (snd (translate_syn \<Delta> F C)) = snd (translate \<Delta> F C)"
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




end