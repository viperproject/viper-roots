theory FixedPointEquiSem
  imports PredInterpCompleteLattice EquiSemAuxLemma
begin

section \<open>Restrictions on Predicates\<close>

subsection \<open>No Old Expression\<close>

fun no_old_pure :: "pure_exp \<Rightarrow> bool"
  and no_old_pure_exps :: "pure_exp list \<Rightarrow> bool" where

  NoOldPureExps: "no_old_pure_exps es \<longleftrightarrow> list_all no_old_pure es"

| "no_old_pure (Old _ _) \<longleftrightarrow> False"
| NoOldLit: "no_old_pure (ELit _) \<longleftrightarrow> True"
| NoOldVar: "no_old_pure (Var _) \<longleftrightarrow> True"
| NoOldUnop: "no_old_pure (Unop _ e) \<longleftrightarrow> no_old_pure e"
| NoOldBinop: "no_old_pure (Binop e _ e') \<longleftrightarrow> no_old_pure e \<and> no_old_pure e'"
| NoOldCondExp: "no_old_pure (CondExp e1 e2 e3) \<longleftrightarrow> no_old_pure e1 \<and> no_old_pure e2 \<and> no_old_pure e3"
| NoOldField: "no_old_pure (FieldAcc e _) \<longleftrightarrow> no_old_pure e"
| NoOldPerm: "no_old_pure (Perm e _) \<longleftrightarrow> no_old_pure e"
| NoOldPermPred: "no_old_pure (PermPred _ es) \<longleftrightarrow> no_old_pure_exps es"
| NoOldFunApp: "no_old_pure (FunApp _ es) \<longleftrightarrow> no_old_pure_exps es"
| NoOldResult: "no_old_pure Result \<longleftrightarrow> True"
| NoOldUnfolding: "no_old_pure (Unfolding _ es e) \<longleftrightarrow> no_old_pure_exps es \<and> no_old_pure e"
| NoOldLet: "no_old_pure (Let e1 e2) \<longleftrightarrow> no_old_pure e1 \<and> no_old_pure e2"
| NoOldExists: "no_old_pure (PExists _ e) \<longleftrightarrow> no_old_pure e"
| NoOldForall: "no_old_pure (PForall _ e) \<longleftrightarrow> no_old_pure e"

lemma no_old_in_sub:
  shows "no_old_pure E \<Longrightarrow> \<forall>e \<in> sub_pure_exp E. no_old_pure e"
proof (induct rule: pure_exp.induct)
  case (ELit x)
  then show ?case
    by simp
next
  case (Var x)
  then show ?case
    by simp
next
  case (Unop x1a x2a)
  then show ?case
    by simp
next
  case (Binop x1a x2a x3)
  then show ?case
    by fastforce
next
  case (CondExp x1a x2a x3)
  then show ?case
    by (metis NoOldCondExp singletonD sub_pure_exp.simps(6))
next
  case (FieldAcc x1a x2a)
  then show ?case
    by simp
next
  case (Old x1a x2a)
  then show ?case
    by simp
next
  case (Perm x1a x2a)
  then show ?case
    by simp
next
  case (PermPred x1a x2a)
  then show ?case
    by (metis NoOldPermPred all_nth_imp_all_set list_all_length no_old_pure_exps.elims(2) sub_pure_exp.simps(7))
next
  case (FunApp x1a x2a)
  then show ?case
    by (metis NoOldFunApp in_set_conv_decomp_last list.pred_inject(2) list_all_append no_old_pure_exps.elims(2) sub_pure_exp.simps(8))
next
  case Result
  then show ?case
    by simp
next
  case (Unfolding x1a x2a x3)
  then show ?case
    by (metis NoOldUnfolding UnE all_nth_imp_all_set empty_iff insert_iff list_all_length no_old_pure_exps.elims(2) sub_pure_exp.simps(9))
next
  case (Let x1a x2a)
  then show ?case
    by fastforce
next
  case (PExists x1a x2a)
  then show ?case
    by simp
next
  case (PForall x1a x2a)
  then show ?case
    by simp
qed

lemma red_no_old_pure_indep_trace:
    shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v \<Longrightarrow> get_store \<omega> = get_store \<omega>' \<Longrightarrow> get_state \<omega> = get_state \<omega>' \<Longrightarrow> no_old_pure e \<Longrightarrow> \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] v"
      and "red_pure_exps \<Delta> \<omega> exps vals \<Longrightarrow> get_store \<omega> = get_store \<omega>' \<Longrightarrow> get_state \<omega> = get_state \<omega>' \<Longrightarrow> no_old_pure_exps exps \<Longrightarrow> red_pure_exps \<Delta> \<omega>' exps vals"
proof (induct arbitrary: \<omega>' and \<omega>' rule: red_pure_red_pure_exps.inducts)
(* first \<omega>' refers to reducing single expression case, second refers to reducing expression list case. "and" in between indicates they bound first and second conclusion respectively *)
  case (RedPureExps c \<omega> exps vals)
    have "\<And>e v. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) \<and> (\<forall>x. get_store \<omega> = get_store x \<longrightarrow> get_state \<omega> = get_state x \<longrightarrow> no_old_pure e \<longrightarrow> c \<turnstile> \<langle>e;x\<rangle> [\<Down>] Val v) \<Longrightarrow> (no_old_pure e \<longrightarrow> c \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val v)"
      using RedPureExps.prems(1) RedPureExps.prems(2) by blast
    then have "list_all2 (\<lambda>e v. no_old_pure e \<longrightarrow> c \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val v) exps vals"
      by (smt (verit) RedPureExps.hyps list_all2_mono)
    then show ?case
      by (metis (mono_tags) NoOldPureExps RedPureExps.prems(3) list_all2_extract_premise red_pure_exps.simps)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLit)
next
  case (RedVar \<omega> n v \<Delta>)
  then show ?case sorry
(*
    by (metis get_store_def red_pure_red_pure_exps.RedVar surj_pair)
*)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    by (meson NoOldUnop red_pure_red_pure_exps.RedUnop)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    by (meson NoOldBinop red_pure_red_pure_exps.RedBinopLazy)
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (meson NoOldBinop red_pure_red_pure_exps.RedBinop)
next
  case (RedOld \<omega> l \<phi> \<Delta> e v)
  then show ?case
    by auto
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  have s_not_change: "get_store (shift_and_add_equi_state \<omega> v1) = get_store (shift_and_add_equi_state \<omega>' v1)"
    by (metis greater_state_has_greater_parts(1) neutral_smallest)
  have v_not_change: "get_state (shift_and_add_equi_state \<omega> v1) = get_state (shift_and_add_equi_state \<omega>' v1)"
    by (simp add: RedLet.prems(2) shift_and_add_keep_vstate)
  have e1_eval_v1: "\<Delta> \<turnstile> \<langle>e1;\<omega>'\<rangle> [\<Down>] Val v1"
    using RedLet.hyps(2) RedLet.prems(1) RedLet.prems(2) RedLet.prems(3) by auto
  have "\<Delta> \<turnstile> \<langle>e2;shift_and_add_equi_state \<omega>' v1\<rangle> [\<Down>] r"
    using RedLet.hyps(4) RedLet.prems(3) s_not_change v_not_change by auto
  then show ?case
    using e1_eval_v1 red_pure_red_pure_exps.RedLet by blast
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case sorry
(*
  by (metis NoOldExists get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedExistsTrue shift_and_add_equi_state.simps)
*)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case sorry
(*
    by (metis NoOldExists get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedExistsFalse shift_and_add_equi_state.simps)
*)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case sorry
(*
    by (metis NoOldForall get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedForallTrue shift_and_add_equi_state.simps)
*)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case sorry
(*
    by (metis NoOldForall get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedForallFalse shift_and_add_equi_state.simps)
*)
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPermNull)
next
  case (RedResult \<omega> v \<Delta>)
  then show ?case sorry
(*
    by (metis get_store_def red_pure_red_pure_exps.RedResult)
*)
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    by (metis NoOldBinop red_pure_red_pure_exps.RedBinopRightFailure)
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (meson NoOldBinop red_pure_red_pure_exps.RedBinopFailure)
next
  case (RedOldFailure \<omega> l \<Delta> e)
  then show ?case
    by simp
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case sorry
(*
    by (metis NoOldExists get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedExistsFailure shift_and_add_equi_state.elims)
*)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case sorry
(*
    by (metis NoOldForall get_store_def get_state_def old.prod.exhaust red_pure_red_pure_exps.RedForallFailure shift_and_add_equi_state.elims)
*)
next
  case (RedPropagateFailure e e' \<Delta> \<omega>)
  then show ?case
    by (simp add: no_old_in_sub red_pure_red_pure_exps.RedPropagateFailure)
next
  case (RedField \<Delta> e \<omega> a read_field f v)
  then show ?case
    by (metis NoOldField red_pure_red_pure_exps.RedField)
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  then show ?case
    by (metis NoOldFunApp red_pure_red_pure_exps.RedFunApp)
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case
    by (metis NoOldFunApp red_pure_red_pure_exps.RedFunAppFailure)
qed


fun no_old_exp_or_wildcard :: "pure_exp exp_or_wildcard \<Rightarrow> bool" where
"no_old_exp_or_wildcard (PureExp e) = no_old_pure e" |
"no_old_exp_or_wildcard Wildcard = True"

fun no_old_atomic_assert :: "pure_exp atomic_assert \<Rightarrow> bool" where
  NoOldPure: "no_old_atomic_assert (Pure atm) \<longleftrightarrow> no_old_pure atm"
| NoOldAcc: "no_old_atomic_assert (Acc x _ p) \<longleftrightarrow> no_old_pure x \<and> no_old_exp_or_wildcard p"
| NoOldAccPred: "no_old_atomic_assert (AccPredicate _ as p) \<longleftrightarrow> no_old_pure_exps as \<and> no_old_exp_or_wildcard p"

lemma red_no_old_atomic_assert_indep_trace:
    shows "red_atomic_assert \<Delta> a \<omega> b \<Longrightarrow> no_old_atomic_assert a \<Longrightarrow> get_store \<omega> = get_store \<omega>' \<Longrightarrow> get_state \<omega> = get_state \<omega>' \<Longrightarrow> red_atomic_assert \<Delta> a \<omega>' b"
proof (induct arbitrary: \<omega>' rule: red_atomic_assert.induct)
  case (RedAtomicPure \<Delta> e \<omega> b)
  then show ?case
    by (meson NoOldPure red_atomic_assert.RedAtomicPure red_no_old_pure_indep_trace(1))
next
  case (RedAtomicAcc \<Delta> e \<omega> r p v f)
  have no_old_perm: "no_old_pure p"
    using RedAtomicAcc.prems(1) by auto
  have no_old_ref: "no_old_pure e"
    using RedAtomicAcc.prems(1) by auto
  have perm_red: "\<Delta> \<turnstile> \<langle>p; \<omega>'\<rangle> [\<Down>] Val (VPerm v)"
    by (metis RedAtomicAcc.hyps(2) RedAtomicAcc.prems(2) RedAtomicAcc.prems(3) no_old_perm red_no_old_pure_indep_trace(1))
  have ref_red: "\<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val (VRef r)"
    by (metis RedAtomicAcc.hyps(1) RedAtomicAcc.prems(2) RedAtomicAcc.prems(3) no_old_ref red_no_old_pure_indep_trace(1))
  have same_mask: "get_m \<omega> = get_m \<omega>'"
    by (metis RedAtomicAcc.prems(3) get_m.simps get_pv.cases get_state_def)
  then show ?case sorry
(*
    by (simp add: RedAtomicAcc.hyps(3) perm_red red_atomic_assert.RedAtomicAcc ref_red)
*)
next
  case (RedAtomicAccZero \<Delta> e \<omega> uu p f)
  have perm_red: "\<Delta> \<turnstile> \<langle>p; \<omega>'\<rangle> [\<Down>] Val (VPerm 0)"
    by (metis NoOldAcc RedAtomicAccZero.hyps(2) RedAtomicAccZero.prems(1) RedAtomicAccZero.prems(2) RedAtomicAccZero.prems(3) no_old_exp_or_wildcard.simps(1) red_no_old_pure_indep_trace(1))
  have ref_red: "\<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val (VRef uu)"
    by (metis NoOldAcc RedAtomicAccZero.hyps(1) RedAtomicAccZero.prems(1) RedAtomicAccZero.prems(2) RedAtomicAccZero.prems(3) red_no_old_pure_indep_trace(1))
  show ?case
    using perm_red red_atomic_assert.RedAtomicAccZero ref_red by blast
next
  case (RedAtomicAccWildcard \<Delta> e \<omega> a f)
  then have ref_red: "\<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val (VRef (Address a))"
    by (meson NoOldAcc red_no_old_pure_indep_trace(1))
  have "get_m \<omega> = get_m \<omega>'"
    by (metis RedAtomicAccWildcard.prems(3) get_m.simps get_pv.cases get_state_def)
  then show ?case sorry
(*
    by (simp add: red_atomic_assert.RedAtomicAccWildcard ref_red)
*)
next
  case (RedAtomicAccWildcardNull \<Delta> e \<omega> f)
  then have "\<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>] Val (VRef Null)"
    using NoOldAcc red_no_old_pure_indep_trace(1) by blast
  then show ?case
    by (simp add: red_atomic_assert.RedAtomicAccWildcardNull)
next
  case (RedAtomicAccNeg \<Delta> p \<omega> v e f)
  then have "\<Delta> \<turnstile> \<langle>p; \<omega>'\<rangle> [\<Down>] Val (VPerm v)"
    by (meson NoOldAcc no_old_exp_or_wildcard.simps(1) red_no_old_pure_indep_trace(1))
  then show ?case
    by (simp add: RedAtomicAccNeg.hyps(2) red_atomic_assert.RedAtomicAccNeg)
next
  case (RedAtomicPred \<Delta> \<omega> exps vals p v P A)
  have args_red: "red_pure_exps \<Delta> \<omega>' exps vals"
    using NoOldAccPred RedAtomicPred.hyps(1) RedAtomicPred.prems(1) RedAtomicPred.prems(2) RedAtomicPred.prems(3) red_no_old_pure_indep_trace(2) by blast
  have perm_red: "\<Delta> \<turnstile> \<langle>p; \<omega>'\<rangle> [\<Down>] Val (VPerm v)"
    using NoOldAccPred RedAtomicPred.hyps(2) RedAtomicPred.prems(1) RedAtomicPred.prems(2) RedAtomicPred.prems(3) no_old_exp_or_wildcard.simps(1) red_no_old_pure_indep_trace(1) by blast
  show ?case
    using RedAtomicPred.hyps(3) RedAtomicPred.hyps(4) RedAtomicPred.prems(3) args_red perm_red red_atomic_assert.RedAtomicPred by fastforce
next
  case (RedAtomicPredWildcard \<Delta> \<omega> exps vals P A)
  then have "red_pure_exps \<Delta> \<omega>' exps vals"
    by (meson NoOldAccPred red_no_old_pure_indep_trace(2))
  then show ?case
    using RedAtomicPredWildcard.hyps(2) RedAtomicPredWildcard.prems(3) red_atomic_assert.RedAtomicPredWildcard by fastforce
next
  case (RedAtomicPredNeg \<Delta> p \<omega> v P exps)
  then have "\<Delta> \<turnstile> \<langle>p; \<omega>'\<rangle> [\<Down>] Val (VPerm v)"
    by (meson NoOldAccPred no_old_exp_or_wildcard.simps(1) red_no_old_pure_indep_trace(1))
  then show ?case
    by (simp add: RedAtomicPredNeg.hyps(2) red_atomic_assert.RedAtomicPredNeg)
qed

fun no_old_assertion :: "assertion \<Rightarrow> bool" where
  NoOldAtomic: "no_old_assertion (Atomic a) \<longleftrightarrow> no_old_atomic_assert a"
| NoOldImp: "no_old_assertion (Imp e a) \<longleftrightarrow> no_old_pure e \<and> no_old_assertion a"
| NoOldCondAssert: "no_old_assertion (CondAssert e A B) \<longleftrightarrow> no_old_pure e \<and> no_old_assertion A \<and> no_old_assertion B"
| NoOldImpAnd: "no_old_assertion (ImpureAnd a1 a2) \<longleftrightarrow> no_old_assertion a1 \<and> no_old_assertion a2"
| NoOldImpOr: "no_old_assertion (ImpureOr a1 a2) \<longleftrightarrow> no_old_assertion a1 \<and> no_old_assertion a2"
| NoOldStar: "no_old_assertion (a1 && a2) \<longleftrightarrow> no_old_assertion a1 \<and> no_old_assertion a2"
| NoOldWand: "no_old_assertion (a1 --* a2) \<longleftrightarrow> no_old_assertion a1 \<and> no_old_assertion a2"
| NoOldImpForall: "no_old_assertion (ForAll _ a) \<longleftrightarrow> no_old_assertion a"
| NoOldImpExists: "no_old_assertion (Exists _ a) \<longleftrightarrow> no_old_assertion a"

lemma red_no_old_assertion_indep_trace:
    shows "\<Delta> \<Turnstile> \<langle>a; \<omega>\<rangle> \<Longrightarrow> no_old_assertion a \<Longrightarrow> get_store \<omega> = get_store \<omega>' \<Longrightarrow> get_state \<omega> = get_state \<omega>' \<Longrightarrow> \<Delta> \<Turnstile> \<langle>a; \<omega>'\<rangle>"
proof (induct arbitrary: \<omega>' rule: sat.induct)
  case (1 \<Delta> A \<omega>)
  then show ?case
    using NoOldAtomic red_no_old_atomic_assert_indep_trace sat.simps(1) by blast
next
  case (2 \<Delta> b A \<omega>)
  then show ?case
    by (metis NoOldImp red_no_old_pure_indep_trace(1) sat.simps(2))
next
  case (3 \<Delta> b A B \<omega>)
  show ?case 
    apply simp
    apply (rule exI)
    apply (intro conjI)
    using 3 red_no_old_pure_indep_trace(1) NoOldCondAssert 
    sorry
next
  case (4 \<Delta> A B \<omega>)
  then show ?case
  proof -
    obtain a b where
          sep_conj: "Some \<omega> = a \<oplus> b"
      and sat_a: "\<Delta> \<Turnstile> \<langle>A; a\<rangle>"
      and sat_b: "\<Delta> \<Turnstile> \<langle>B; b\<rangle>"
      using "4.prems"(1) by auto
    obtain a' where
          a'_s: "get_store a' = get_store a"
      and a'_t: "get_trace a' = get_trace \<omega>'"
      and a'_v: "get_state a' = get_state a"      
      by (metis full_add_defined option.discI u_neutral)
    obtain b' where
          b'_s: "get_store b' = get_store b"
      and b'_t: "get_trace b' = (\<lambda>l. None)"
      and b'_v: "get_state b' = get_state b"
      sorry
(*
      by auto
*)
    have s_plus: "Some (get_store \<omega>') = get_store a' \<oplus> get_store b'"
      by (metis "4.prems"(3) a'_s b'_s sep_conj state_add_iff)
    have v_plus: "Some (get_state \<omega>') = get_state a' \<oplus> get_state b'"
      by (metis "4.prems"(4) a'_v b'_v sep_conj state_add_iff)
    have t_plus: "Some (get_trace \<omega>') = get_trace a' \<oplus> get_trace b'"
      sorry
(*
TODO
Not true anymore, since the trace is an agreement...
      by (simp add: a'_t b'_t lambda_None_is_identity)
*)
    have "Some \<omega>' = a' \<oplus> b'"
      by (simp add: s_plus state_add_iff t_plus v_plus)
    moreover have "\<Delta> \<Turnstile> \<langle>A; a'\<rangle>"
      using "4.hyps"(1) "4.prems"(2) a'_s a'_v sat_a by auto
    moreover have "\<Delta> \<Turnstile> \<langle>B; b'\<rangle>"
      using "4.hyps"(2) "4.prems"(2) b'_s b'_v sat_b by auto
    ultimately show ?thesis
      using sat.simps(4) by blast
  qed
next
  case (5 \<Delta> A B \<omega>)
  then show ?case
  proof -
    have no_old_A: "no_old_assertion A"
      using "5.prems"(2) by auto
    have no_old_B: "no_old_assertion B"
      using "5.prems"(2) by auto
    have "\<And>b a. (Some b = \<omega>' \<oplus> a) \<and> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>)"
    proof -
      fix b' a'
      show "(Some b' = \<omega>' \<oplus> a') \<and> (\<Delta> \<Turnstile> \<langle>A; a'\<rangle>) \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; b'\<rangle>)"
      proof
        assume assm: "Some b' = \<omega>' \<oplus> a' \<and> \<Delta> \<Turnstile> \<langle>A; a'\<rangle>"
        obtain a where
              as: "get_store a = get_store a'"
          and at: "get_trace a = (\<lambda>l. None)"
          and av: "get_state a = get_state a'"
          sorry
(*
          by auto
*)
        then have implies_A: "(\<Delta> \<Turnstile> \<langle>A; a\<rangle>)"
          by (metis "5.hyps"(1) assm no_old_A)
        obtain b where
              bs: "get_store b = get_store b'"
          and bt: "get_trace b = get_trace \<omega>"
          and bv: "get_state b = get_state b'"
          sorry
(*
          by auto
*)
        have "Some (get_store b) = get_store \<omega> \<oplus> get_store a"
          by (metis "5.prems"(3) as bs assm state_add_iff)
        moreover have "Some (get_state b) = get_state \<omega> \<oplus> get_state a"
          by (metis "5.prems"(4) assm av bv state_add_iff)
        moreover have "Some (get_trace b) = get_trace \<omega> \<oplus> get_trace a"
          sorry
(*
          by (simp add: at bt lambda_None_is_identity)
*)
        ultimately have b_omega_a: "Some b = \<omega> \<oplus> a"
          by (simp add: state_add_iff)
        then have "\<Delta> \<Turnstile> \<langle>B; b\<rangle>"
          using "5.prems"(1) implies_A sat.simps(5) by blast
        then show "\<Delta> \<Turnstile> \<langle>B; b'\<rangle>"
          using "5.hyps"(2) b_omega_a bs bv implies_A no_old_B by blast
      qed
    qed
    then show ?thesis
      using sat.simps(5) by blast
  qed
next
  case (6 \<Delta> ty A \<omega>)
  have "\<forall>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>' v\<rangle>"
  proof
    fix v
    assume v_type_correct: "v \<in> set_from_type (domains \<Delta>) ty"
    then have "\<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>"
      using "6.prems"(1) by auto
    moreover have "no_old_assertion A"
      using "6.prems"(2) by auto
    moreover have "get_store (shift_and_add_equi_state \<omega> v) = get_store (shift_and_add_equi_state \<omega>' v)"
      by (metis greater_state_has_greater_parts(1) neutral_smallest)
    moreover have "get_state (shift_and_add_equi_state \<omega> v) = get_state (shift_and_add_equi_state \<omega>' v)"
      by (simp add: "6.prems"(4) shift_and_add_keep_vstate)
    ultimately show "\<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>' v\<rangle>"
      using "6.hyps" v_type_correct by blast
  qed
  then show ?case
    by simp
next
  case (7 \<Delta> ty A \<omega>)
  then obtain v where
        v_type_correct: "v \<in> set_from_type (domains \<Delta>) ty"
    and v_sat: "\<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>"
    by (metis sat.simps(7))
  moreover have "no_old_assertion A"
    using "7.prems"(2) by auto
  moreover have "get_store (shift_and_add_equi_state \<omega> v) = get_store (shift_and_add_equi_state \<omega>' v)"
    by (metis greater_state_has_greater_parts(1) neutral_smallest)
  moreover have "get_state (shift_and_add_equi_state \<omega> v) = get_state (shift_and_add_equi_state \<omega>' v)"
    by (simp add: "7.prems"(4) shift_and_add_keep_vstate)
  ultimately have "\<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>' v\<rangle>"
    using "7.hyps" by blast
  then have "\<exists>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega>' v\<rangle>"
    using v_type_correct by auto
  then show ?case
    by simp
next
  case (8 \<Delta> A B \<omega>)
  then show ?case
    by simp
next
  case (9 \<Delta> A B \<omega>)
  then show ?case
    by (metis NoOldImpOr sat.simps(9))
qed


subsection \<open>No \<exists>, \<or>\<close>

fun no_exists_or :: "assertion \<Rightarrow> bool" where
  "no_exists_or (Atomic _) \<longleftrightarrow> True"
| "no_exists_or (Imp _ a) \<longleftrightarrow> no_exists_or a"
| "no_exists_or (ImpureAnd a1 a2) \<longleftrightarrow> no_exists_or a1 \<and> no_exists_or a2"
| "no_exists_or (ImpureOr _ _) \<longleftrightarrow> False"
| "no_exists_or (a1 && a2) \<longleftrightarrow> no_exists_or a1 \<and> no_exists_or a2"
| "no_exists_or (a1 --* a2) \<longleftrightarrow> no_exists_or a1 \<and> no_exists_or a2"
| "no_exists_or (ForAll _ a) \<longleftrightarrow> no_exists_or a"
| "no_exists_or (Exists _ _) \<longleftrightarrow> False"


subsection \<open>Not Abstract\<close>

definition predicate_not_abstract :: "predicate_decl \<Rightarrow> bool" where
"predicate_not_abstract p \<longleftrightarrow> predicate_decl.body p \<noteq> None"


subsection \<open>Recursion at Positive Position\<close>

fun pos_neg_assertion :: "bool \<Rightarrow> assertion \<Rightarrow> bool" where
(* first argument b indicates which position this assertion is at *)
  "pos_neg_assertion b (Atomic A) \<longleftrightarrow> is_pure_atomic A \<or> b"
| "pos_neg_assertion b (Imp _ A) \<longleftrightarrow> pos_neg_assertion b A"
| "pos_neg_assertion b (ImpureAnd A B) \<longleftrightarrow> pos_neg_assertion b A \<and> pos_neg_assertion b B"
| "pos_neg_assertion b (ImpureOr A B) \<longleftrightarrow> pos_neg_assertion b A \<and> pos_neg_assertion b B"
| "pos_neg_assertion b (Star A B) \<longleftrightarrow> pos_neg_assertion b A \<and> pos_neg_assertion b B"
| "pos_neg_assertion b (Wand A B) \<longleftrightarrow> pos_neg_assertion (\<not>b) A \<and> pos_neg_assertion b B"
| "pos_neg_assertion b (ForAll _ A) \<longleftrightarrow> pos_neg_assertion b A"
| "pos_neg_assertion b (Exists _ A) \<longleftrightarrow> pos_neg_assertion b A"
| "pos_neg_assertion b (CondAssert _ A B) \<longleftrightarrow> pos_neg_assertion b A \<and> pos_neg_assertion b B"

definition pos_acc_assertion :: "assertion \<Rightarrow> bool" where
  "pos_acc_assertion A = pos_neg_assertion True A"


subsection \<open>Predicates Exist\<close>
\<comment> \<open>Predicate names mentioned in any predicate's body should correspond to defined predicates in the program\<close>

definition predicate_exists :: "program \<Rightarrow> predicate_ident \<Rightarrow> bool" where
  "predicate_exists P ident \<longleftrightarrow> program.predicates P ident \<noteq> None"

fun pred_exists_atomic_assert :: "program \<Rightarrow> pure_exp atomic_assert \<Rightarrow> bool" where
  "pred_exists_atomic_assert P (AccPredicate ident _ _) \<longleftrightarrow> predicate_exists P ident"
| "pred_exists_atomic_assert P _ \<longleftrightarrow> True"

fun predicates_exist_assertion :: "program \<Rightarrow> assertion \<Rightarrow> bool" where
  "predicates_exist_assertion P (Atomic atm) \<longleftrightarrow> pred_exists_atomic_assert P atm"
| "predicates_exist_assertion P (Imp _ A) \<longleftrightarrow> predicates_exist_assertion P A"
| "predicates_exist_assertion P (ImpureAnd A B) \<longleftrightarrow> predicates_exist_assertion P A \<and> predicates_exist_assertion P B"
| "predicates_exist_assertion P (ImpureOr A B) \<longleftrightarrow> predicates_exist_assertion P A \<and> predicates_exist_assertion P B"
| "predicates_exist_assertion P (Star A B) \<longleftrightarrow> predicates_exist_assertion P A \<and> predicates_exist_assertion P B"
| "predicates_exist_assertion P (Wand A B) \<longleftrightarrow> predicates_exist_assertion P A \<and> predicates_exist_assertion P B"
| "predicates_exist_assertion P (ForAll _ A) \<longleftrightarrow> predicates_exist_assertion P A"
| "predicates_exist_assertion P (Exists _ A) \<longleftrightarrow> predicates_exist_assertion P A"
| "predicates_exist_assertion P (CondAssert _ _ A) \<longleftrightarrow> predicates_exist_assertion P A"


subsection \<open>Predicate Well-defined\<close>

text \<open>
Well-definess of a predicate identity includes:
- identity corresponds to a predicate in the program
- the predicate is not abstract (body exists)
- predicate identities in its body all correspond to predicates in the program (alternative requirement)
- predicate identities in its body are at positive position
- no "old" expression in body
\<close>

definition wd_pred_asst :: "assertion \<Rightarrow> bool" where
  "wd_pred_asst A \<longleftrightarrow> pos_acc_assertion A \<and> no_old_assertion A \<and>
      no_exists_or A"

definition wd_pred :: "predicate_decl \<Rightarrow> bool" where
  "wd_pred p \<longleftrightarrow> predicate_not_abstract p \<and>
    (let A = the (predicate_decl.body p) in
      \<comment> \<open>alternative requirement: predicates_exist_assertion p A\<close>
      wd_pred_asst A)"

(* All predicates in program are well-defined. Thus no abstract predicates in any predicate body *)
definition wd_pred_prog :: "program \<Rightarrow> bool" where
  "wd_pred_prog P \<longleftrightarrow> (\<forall>ident decl. program.predicates P ident = Some decl \<longrightarrow> wd_pred decl)"


section \<open>Interpretation Update Function\<close>

lemma red_atomic_assert_mono_inc:
  shows "red_atomic_assert \<Delta> e \<omega> res \<Longrightarrow> predicates \<Delta> \<preceq> predicates \<Delta>' \<Longrightarrow> domains \<Delta> = domains \<Delta>' \<Longrightarrow> funs \<Delta> = funs \<Delta>' \<Longrightarrow> res = Some True \<Longrightarrow> red_atomic_assert \<Delta>' e \<omega> res"
proof (induct rule: red_atomic_assert.induct)
  case (RedAtomicPure \<Delta> e \<omega> b)
  then show ?case
    by (meson red_atomic_assert.RedAtomicPure red_pure_indep_interp_pred(1))
next
  case (RedAtomicAcc \<Delta> e \<omega> r p v f)
  then have "\<Delta>' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>] Val (VRef r)"
    by (metis red_pure_indep_interp_pred(1))
  moreover have "\<Delta>' \<turnstile> \<langle>p;\<omega>\<rangle> [\<Down>] Val (VPerm v)"
    by (metis RedAtomicAcc.hyps(2) RedAtomicAcc.prems(2) RedAtomicAcc.prems(3) red_pure_indep_interp_pred(1))
  ultimately show ?case
    using RedAtomicAcc.hyps(3) red_atomic_assert.RedAtomicAcc by blast
next
  case (RedAtomicAccZero \<Delta> e \<omega> uu p f)
  then show ?case
    by (meson red_atomic_assert.RedAtomicAccZero red_pure_indep_interp_pred(1))
next
  case (RedAtomicAccWildcard \<Delta> e \<omega> a f)
  then show ?case
    by (meson red_atomic_assert.RedAtomicAccWildcard red_pure_indep_interp_pred(1))
next
  case (RedAtomicAccWildcardNull \<Delta> e \<omega> f)
  then show ?case
    by simp
next
  case (RedAtomicAccNeg \<Delta> p \<omega> v e f)
  then show ?case
    by simp
next
  case (RedAtomicPred \<Delta> \<omega> exps vals p v P A)
  then have "red_pure_exps \<Delta>' \<omega> exps vals"
    by (meson red_pure_indep_interp_pred(2))
  moreover have "\<Delta>' \<turnstile> \<langle>p;\<omega>\<rangle> [\<Down>] Val (VPerm v)"
    by (metis RedAtomicPred.hyps(2) RedAtomicPred.prems(2) RedAtomicPred.prems(3) red_pure_indep_interp_pred(1))
  moreover obtain A' where
        "predicates \<Delta>' (P, vals) = Some A'"
    and "A \<subseteq> A'"
    by (metis RedAtomicPred.hyps(4) RedAtomicPred.prems(1) smaller_pred_interp_def smaller_vstate_set_opt.elims(1) smaller_vstate_set_opt.simps(3))
  ultimately have "red_atomic_assert \<Delta>' (AccPredicate P exps (PureExp p)) \<omega> (Some (0 < v \<longrightarrow> (\<exists>a \<in> A'. get_state \<omega> = Abs_preal v \<odot> a)))"
    by (simp add: RedAtomicPred.hyps(3) red_atomic_assert.RedAtomicPred)
  moreover have "0 < v \<longrightarrow> (\<exists>a \<in> A'. get_state \<omega> = Abs_preal v \<odot> a)"
    using RedAtomicPred.prems(4) \<open>A \<subseteq> A'\<close> by auto
  ultimately have "red_atomic_assert \<Delta>' (AccPredicate P exps (PureExp p)) \<omega> (Some True)"
    by simp
  then show ?case
    by (simp add: RedAtomicPred.prems(4))
next
  case (RedAtomicPredWildcard \<Delta> \<omega> exps vals P A)
  then have "red_pure_exps \<Delta>' \<omega> exps vals"
    by (meson red_pure_indep_interp_pred(2))
  moreover obtain A' where
        "predicates \<Delta>' (P, vals) = Some A'"
    and "A \<subseteq> A'"
    by (metis RedAtomicPredWildcard.hyps(2) RedAtomicPredWildcard.prems(1) smaller_pred_interp_def smaller_vstate_set_opt.elims(1) smaller_vstate_set_opt.simps(3))
  ultimately have "red_atomic_assert \<Delta>' (AccPredicate P exps Wildcard) \<omega> (Some (\<exists>a \<in> A'. \<exists>\<alpha>'. 0 < \<alpha>' \<and> get_state \<omega> = \<alpha>' \<odot> a))"
    using red_atomic_assert.RedAtomicPredWildcard by blast
  moreover have "\<exists>a \<in> A'. \<exists>\<alpha>. 0 < \<alpha> \<and> get_state \<omega> = \<alpha> \<odot> a"
    using RedAtomicPredWildcard.prems(4) \<open>A \<subseteq> A'\<close> by auto
  ultimately have "red_atomic_assert \<Delta>' (AccPredicate P exps Wildcard) \<omega> (Some True)"
    by simp
  then show ?case
    using RedAtomicPredWildcard.prems(4) by auto
next
  case (RedAtomicPredNeg \<Delta> p \<omega> v P exps)
  then show ?case
    by simp
qed

lemma red_pure_atomic_assert_indep_pred_interp:
  assumes "domains \<Delta> = domains \<Delta>'"
      and "funs \<Delta> = funs \<Delta>'"
      and "is_pure_atomic A"
      and "red_atomic_assert \<Delta> A \<omega> res"
    shows "red_atomic_assert \<Delta>' A \<omega> res"
proof -
  obtain e where "A = Pure e"
    by (meson assms(3) is_pure_atomic_def)
  then obtain b where
        "res = Some b"
    and "red_pure \<Delta> e \<omega> (Val (VBool b))"
    using RedPure_case assms(4) by blast
  then have "red_pure \<Delta>' e \<omega> (Val (VBool b))"
    using assms(1) assms(2) red_pure_indep_interp_pred(1) by blast
  then show ?thesis
    by (simp add: RedAtomicPure \<open>A = Pure e\<close> \<open>res = Some b\<close>)
qed

lemma sat_mono_inc_for_atomic_assertion:
  assumes "domains \<Delta> = domains \<Delta>'"
      and "funs \<Delta> = funs \<Delta>'"
      and "predicates \<Delta> \<preceq> predicates \<Delta>'"
    shows "\<Delta> \<Turnstile> \<langle>Atomic A; \<omega>\<rangle> \<Longrightarrow> \<Delta>' \<Turnstile> \<langle>Atomic A; \<omega>\<rangle>"
  using assms(1) assms(2) assms(3) red_atomic_assert_mono_inc sat.simps(1) by blast

lemma sat_indep_pred_interp_for_pure_atomic_assertion:
  assumes "domains \<Delta> = domains \<Delta>'"
      and "funs \<Delta> = funs \<Delta>'"
      and "is_pure_atomic A"
    shows "\<Delta> \<Turnstile> \<langle>Atomic A; \<omega>\<rangle> \<longleftrightarrow> \<Delta>' \<Turnstile> \<langle>Atomic A; \<omega>\<rangle>"
  by (metis assms(1) assms(2) assms(3) red_pure_atomic_assert_indep_pred_interp sat.simps(1))

lemma mono_sat_assertion:
  assumes "pos_neg_assertion b A"
  shows "(b \<longrightarrow> inc_sat_assertion D F A) \<and> (\<not>b \<longrightarrow> dec_sat_assertion D F A)"
  using assms
proof (induct A arbitrary: b)
  case (Atomic x)
  let ?A = "Atomic x"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
        by (metis interp.select_convs(1) interp.select_convs(2) interp.select_convs(3) sat_mono_inc_for_atomic_assertion)
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    then have "is_pure_atomic x"
      using Atomic by auto
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
        by (metis \<open>is_pure_atomic x\<close> interp.select_convs(1) interp.select_convs(3) sat_indep_pred_interp_for_pure_atomic_assertion)
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (Imp x1a A)
  let ?A = "Imp x1a A"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then obtain v where "?I \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v"
        by auto
      then have "?I' \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v"
        by (metis interp.select_convs(1) interp.select_convs(3) red_pure_indep_interp_pred(1))
      moreover have "v = VBool True \<longrightarrow> (?I' \<Turnstile> \<langle>A; \<omega>\<rangle>)"
      proof
        assume "v = VBool True"
        then have "?I \<Turnstile> \<langle>A; \<omega>\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> \<open>?I \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v\<close> red_pure_val_unique(1) sat.simps(2) by blast
        moreover have "inc_sat_assertion D F A"
          using Imp.hyps Imp.prems True by auto
        then have "?I' \<Turnstile> \<langle>A; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> calculation inc_sat_assertion_def by blast
        then show "?I' \<Turnstile> \<langle>A; \<omega>\<rangle>"
          by simp
      qed
      ultimately show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
        by auto
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then obtain v where "?I' \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v"
        by auto
      then have "?I \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v"
        by (metis interp.select_convs(1) interp.select_convs(3) red_pure_indep_interp_pred(1))
      moreover have "v = VBool True \<longrightarrow> (?I \<Turnstile> \<langle>A; \<omega>\<rangle>)"
      proof
        assume "v = VBool True"
        then have "?I' \<Turnstile> \<langle>A; \<omega>\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> \<open>?I' \<turnstile> \<langle>x1a; \<omega>\<rangle> [\<Down>] Val v\<close> red_pure_val_unique(1) sat.simps(2) by blast
        moreover have "dec_sat_assertion D F A"
          using Imp.hyps Imp.prems False by auto
        then have "?I \<Turnstile> \<langle>A; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> calculation dec_sat_assertion_def by blast
        then show "?I \<Turnstile> \<langle>A; \<omega>\<rangle>"
          by simp
      qed
      ultimately show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
        by auto
    qed
    then show ?thesis
      by (simp add: False)
  qed
next
  case (CondAssert x1a A1 A2)
  then show ?case sorry
next
  case (ImpureAnd A1 A2)
  let ?A = "ImpureAnd A1 A2"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "?I \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(8) by blast
        moreover have "inc_sat_assertion D F A1"
          using ImpureAnd.hyps(1) ImpureAnd.prems True by auto
        ultimately have "?I' \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        have "?I \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(8) by blast
        moreover have "inc_sat_assertion D F A2"
          using ImpureAnd.hyps(2) ImpureAnd.prems True by auto
        ultimately have "?I' \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        then show ?thesis
          using \<open>?I' \<Turnstile> \<langle>A1; \<omega>\<rangle>\<close> by auto
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "?I' \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(8) by blast
        moreover have "dec_sat_assertion D F A1"
          using ImpureAnd.hyps(1) ImpureAnd.prems False by auto
        ultimately have "?I \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        have "?I' \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(8) by blast
        moreover have "dec_sat_assertion D F A2"
          using ImpureAnd.hyps(2) ImpureAnd.prems False by auto
        ultimately have "?I \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        then show ?thesis
          using \<open>?I \<Turnstile> \<langle>A1; \<omega>\<rangle>\<close> by auto
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (ImpureOr A1 A2)
  let ?A = "ImpureOr A1 A2"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "inc_sat_assertion D F A1"
          using ImpureOr.hyps(1) ImpureOr.prems True by auto
        then have "?I \<Turnstile> \<langle>A1; \<omega>\<rangle> \<Longrightarrow> ?I' \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        have "inc_sat_assertion D F A2"
          using ImpureOr.hyps(2) ImpureOr.prems True by auto
        then have "?I \<Turnstile> \<langle>A2; \<omega>\<rangle> \<Longrightarrow> ?I' \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        then show ?thesis
          using \<open>?I \<Turnstile> \<langle>A1; \<omega>\<rangle> \<Longrightarrow> ?I' \<Turnstile> \<langle>A1; \<omega>\<rangle>\<close> \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(9) by blast
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "dec_sat_assertion D F A1"
          using ImpureOr.hyps(1) ImpureOr.prems False by auto
        then have "?I' \<Turnstile> \<langle>A1; \<omega>\<rangle> \<Longrightarrow> ?I \<Turnstile> \<langle>A1; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        have "dec_sat_assertion D F A2"
          using ImpureOr.hyps(2) ImpureOr.prems False by auto
        then have "?I' \<Turnstile> \<langle>A2; \<omega>\<rangle> \<Longrightarrow> ?I \<Turnstile> \<langle>A2; \<omega>\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        then show ?thesis
          using \<open>?I' \<Turnstile> \<langle>A1; \<omega>\<rangle> \<Longrightarrow> ?I \<Turnstile> \<langle>A1; \<omega>\<rangle>\<close> \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(9) by blast
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (Star A1 A2)
  let ?A = "Star A1 A2"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        obtain a b where
              "Some \<omega> = a \<oplus> b"
          and "?I \<Turnstile> \<langle>A1; a\<rangle>"
          and "?I \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(4) by blast
        have "inc_sat_assertion D F A1"
          using Star.hyps(1) Star.prems True by auto
        then have "?I' \<Turnstile> \<langle>A1; a\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> \<open>?I \<Turnstile> \<langle>A1; a\<rangle>\<close> inc_sat_assertion_def by blast
        have "inc_sat_assertion D F A2"
          using Star.hyps(2) Star.prems True by auto
        then have "?I' \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> \<open>?I \<Turnstile> \<langle>A2; b\<rangle>\<close> inc_sat_assertion_def by blast
        then show ?thesis
          using \<open>Some \<omega> = a \<oplus> b\<close> \<open>?I' \<Turnstile> \<langle>A1; a\<rangle>\<close> sat.simps(4) by blast
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        obtain a b where
              "Some \<omega> = a \<oplus> b"
          and "?I' \<Turnstile> \<langle>A1; a\<rangle>"
          and "?I' \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(4) by blast
        have "dec_sat_assertion D F A1"
          using Star.hyps(1) Star.prems False by auto
        then have "?I \<Turnstile> \<langle>A1; a\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> \<open>?I' \<Turnstile> \<langle>A1; a\<rangle>\<close> dec_sat_assertion_def by blast
        have "dec_sat_assertion D F A2"
          using Star.hyps(2) Star.prems False by auto
        then have "?I \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> \<open>?I' \<Turnstile> \<langle>A2; b\<rangle>\<close> dec_sat_assertion_def by blast
        then show ?thesis
          using \<open>Some \<omega> = a \<oplus> b\<close> \<open>?I \<Turnstile> \<langle>A1; a\<rangle>\<close> sat.simps(4) by blast
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (Wand A1 A2)
  let ?A = "Wand A1 A2"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof (rule sat_wand_rule)
        fix a b :: "'a equi_state"
        assume "Some b = \<omega> \<oplus> a"
           and "?I' \<Turnstile> \<langle>A1; a\<rangle>"
        moreover have "dec_sat_assertion D F A1"
          using True Wand.hyps(1) Wand.prems by auto
        ultimately have "?I \<Turnstile> \<langle>A1; a\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        then have "?I \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>Some b = \<omega> \<oplus> a\<close> \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(5) by blast
        moreover have "inc_sat_assertion D F A2"
          using True Wand.hyps(2) Wand.prems by auto
        ultimately show "?I' \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof (rule sat_wand_rule)
        fix a b :: "'a equi_state"
        assume "Some b = \<omega> \<oplus> a"
           and "?I \<Turnstile> \<langle>A1; a\<rangle>"
        moreover have "inc_sat_assertion D F A1"
          using False Wand.hyps(1) Wand.prems by auto
        ultimately have "?I' \<Turnstile> \<langle>A1; a\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        then have "?I' \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>Some b = \<omega> \<oplus> a\<close> \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> sat.simps(5) by blast
        moreover have "dec_sat_assertion D F A2"
          using False Wand.hyps(2) Wand.prems by auto
        ultimately show "?I \<Turnstile> \<langle>A2; b\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (ForAll x1a A)
  let ?A = "ForAll x1a A"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof (rule sat_forall_rule)
        fix v'
        assume "v' \<in> set_from_type (domains ?I') x1a"
        then have "?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> by auto
        moreover have "inc_sat_assertion D F A"
          using ForAll.hyps ForAll.prems True by auto
        ultimately show "?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof (rule sat_forall_rule)
        fix v'
        assume "v' \<in> set_from_type (domains ?I) x1a"
        then have "?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> by auto
        moreover have "dec_sat_assertion D F A"
          using ForAll.hyps ForAll.prems False by auto
        ultimately show "?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed

next
  case (Exists x1a A)
  let ?A = "Exists x1a A"
  show ?case
  proof (cases b)
    case True
    have "inc_sat_assertion D F ?A"
    proof (rule inc_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "\<exists>v' \<in> set_from_type D x1a. ?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>?I \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> by auto
        then obtain v' where
              "v' \<in> set_from_type D x1a"
          and "?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          by auto
        moreover have "inc_sat_assertion D F A"
          using Exists.hyps Exists.prems True by auto
        ultimately have "?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
        then have "\<exists>v' \<in> set_from_type D x1a. ?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>v' \<in> set_from_type D x1a\<close> by auto
        then show ?thesis
          by simp
      qed
    qed
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "dec_sat_assertion D F ?A"
    proof (rule dec_sat_assertion_rule)
      fix \<Delta> \<Delta>' :: "'a pred_interp"
      fix \<omega> :: "'a equi_state"
      let ?I = "\<lparr>interp.domains = D, predicates = \<Delta>, funs = F\<rparr>"
      let ?I' = "\<lparr>interp.domains = D, predicates = \<Delta>', funs = F\<rparr>"
      assume "\<Delta> \<preceq> \<Delta>'"
         and "?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      then show "?I \<Turnstile> \<langle>?A; \<omega>\<rangle>"
      proof -
        have "\<exists>v' \<in> set_from_type D x1a. ?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>?I' \<Turnstile> \<langle>?A; \<omega>\<rangle>\<close> by auto
        then obtain v' where
              "v' \<in> set_from_type D x1a"
          and "?I' \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          by auto
        moreover have "dec_sat_assertion D F A"
          using Exists.hyps Exists.prems False by auto
        ultimately have "?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
        then have "\<exists>v' \<in> set_from_type D x1a. ?I \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v'\<rangle>"
          using \<open>v' \<in> set_from_type D x1a\<close> by auto
        then show ?thesis
          by simp
      qed
    qed
    then show ?thesis
      by (simp add: False)
  qed
qed

fun shift_and_add_list_equi_state :: "'v equi_state \<Rightarrow> 'v val list \<Rightarrow> 'v equi_state" where
  "shift_and_add_list_equi_state ((\<sigma>, \<tau>), \<gamma>) l = ((Ag (shift_and_add_list (the_ag \<sigma>) l), \<tau>), \<gamma>)"


definition assertion_upt :: "'v domain_interp \<Rightarrow> 'v fun_interp \<Rightarrow> assertion \<Rightarrow> 'v val list \<Rightarrow> 'v pred_interp \<Rightarrow> 'v virtual_state set" where
  "assertion_upt D F A v \<Delta> = (let I = \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> in
    {\<omega>. I \<Turnstile> \<langle>A; shift_and_add_list_equi_state ((Ag (\<lambda>n. None), Ag (\<lambda>l. None)), \<omega>) v\<rangle>})"

lemma mono_assertion_upt:
  assumes "pos_neg_assertion b A"
  shows "(b \<longrightarrow> inc_assertion_upt (assertion_upt D F A v)) \<and> (\<not>b \<longrightarrow> dec_assertion_upt (assertion_upt D F A v))"
proof (cases b)
  case True
  have "inc_assertion_upt (assertion_upt D F A v)"
  proof (rule inc_assertion_upt_rule)
    fix \<Delta> \<Delta>' :: "'a pred_interp"
    fix \<omega> :: "'a virtual_state"
    let ?I = "\<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr>"
    let ?I' = "\<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr>"
    let ?\<omega> = "shift_and_add_list_equi_state ((Ag (\<lambda>n. None), Ag (\<lambda>l. None)), \<omega>) v"
    assume "\<Delta> \<preceq> \<Delta>'"
       and "\<omega> \<in> assertion_upt D F A v \<Delta>"
    then have "?I \<Turnstile> \<langle>A; ?\<omega>\<rangle>"
      by (simp add: assertion_upt_def)
    moreover have "inc_sat_assertion D F A"
      using True assms mono_sat_assertion by auto
    ultimately have "?I' \<Turnstile> \<langle>A; ?\<omega>\<rangle>"
      using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_sat_assertion_def by blast
    then show "\<omega> \<in> assertion_upt D F A v \<Delta>'"
      by (simp add: assertion_upt_def)
  qed
  then show ?thesis
    by (simp add: True)
next
  case False
  have "dec_assertion_upt (assertion_upt D F A v)"
  proof (rule dec_assertion_upt_rule)
    fix \<Delta> \<Delta>' :: "'a pred_interp"
    fix \<omega> :: "'a virtual_state"
    let ?I = "\<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr>"
    let ?I' = "\<lparr> domains = D, predicates = \<Delta>', funs = F \<rparr>"
    let ?\<omega> = "shift_and_add_list_equi_state ((Ag (\<lambda>n. None), Ag (\<lambda>l. None)), \<omega>) v"
    assume "\<Delta> \<preceq> \<Delta>'"
       and "\<omega> \<in> assertion_upt D F A v \<Delta>'"
    then have "?I' \<Turnstile> \<langle>A; ?\<omega>\<rangle>"
      by (simp add: assertion_upt_def)
    moreover have "dec_sat_assertion D F A"
      using False assms mono_sat_assertion by auto
    ultimately have "?I \<Turnstile> \<langle>A; ?\<omega>\<rangle>"
      using \<open>\<Delta> \<preceq> \<Delta>'\<close> dec_sat_assertion_def by blast
    then show "\<omega> \<in> assertion_upt D F A v \<Delta>"
      by (simp add: assertion_upt_def)
  qed
  then show ?thesis
    by (simp add: False)
qed

definition typeMatch :: "'v domain_interp \<Rightarrow> 'v val \<Rightarrow> vtyp \<Rightarrow> bool" where
  "typeMatch D v t \<longleftrightarrow> get_type D v = t"

definition typeListMatch :: "'v domain_interp \<Rightarrow> 'v val list \<Rightarrow> vtyp list \<Rightarrow> bool" where
  "typeListMatch D xs ys = list_all2 (typeMatch D) xs ys"

definition predicate_args :: "program \<Rightarrow> predicate_ident \<Rightarrow> vtyp list" where
  "predicate_args Pr p = predicate_decl.args (the (program.predicates Pr p))"

definition predInterpDomain :: "program \<Rightarrow> 'v domain_interp \<Rightarrow> 'v fun_interp \<Rightarrow> 'v predicate_loc set" where
  "predInterpDomain P D F = {l. predicate_exists P (fst l) \<and> (let arg = predicate_args P (fst l) in typeListMatch D (snd l) arg)}"

lemma predInterpDomain_iff:
  shows "l \<in> predInterpDomain P D F \<longleftrightarrow> predicate_exists P (fst l) \<and> (let arg = predicate_args P (fst l) in typeListMatch D (snd l) arg)"
  by (simp add: predInterpDomain_def)

definition predInterpUpdate :: "program \<Rightarrow> 'v domain_interp \<Rightarrow> 'v fun_interp \<Rightarrow> 'v pred_interp \<Rightarrow> 'v pred_interp" where
  "predInterpUpdate P D F \<Delta> l =
    (let ident = fst l in (let v = snd l in \<comment> \<open> ident :: predicate_ident, v :: 'v val list \<close>
      (if predicate_exists P ident then
        (let arg = predicate_args P ident in  \<comment> \<open> arg :: vtyp list \<close>
          (if typeListMatch D v arg then
            (let pred = predicate_body P ident in  \<comment> \<open> pred :: assertion \<close>
              \<comment> \<open> I = \<lparr> domains = D, predicates = \<Delta>, funs = F \<rparr> :: ('v, 'v virtual_state) interp \<close>
              Some (assertion_upt D F pred v \<Delta>) \<comment> \<open>{\<omega>. I \<Turnstile> \<langle>pred; shift_and_add_list_equi_state (\<lambda>n. None, \<lambda>l. None, \<omega>) v\<rangle>}\<close>)
          else None))
      else None)))"
(* If # of variables appeared in predicate body exceeds # of arguments, then None is always returned in places of these variables, and monotonicity still preserves *)

lemma predInterpUpdate_domain:
  shows "l \<in> predInterpDomain P D F \<Longrightarrow> predInterpUpdate P D F \<Delta> l = (let pred = predicate_body P (fst l) in Some (assertion_upt D F pred (snd l) \<Delta>))"
    and "l \<notin> predInterpDomain P D F \<Longrightarrow> predInterpUpdate P D F \<Delta> l = None"
proof -
  assume "l \<in> predInterpDomain P D F"
  then show "predInterpUpdate P D F \<Delta> l = (let pred = predicate_body P (fst l) in Some (assertion_upt D F pred (snd l) \<Delta>))"
    by (simp add: predInterpDomain_iff predInterpUpdate_def)
next
  assume "l \<notin> predInterpDomain P D F"
  then show "predInterpUpdate P D F \<Delta> l = None"
  proof cases
    assume "predicate_exists P (fst l)"
    then have "\<not>(let arg = predicate_args P (fst l) in typeListMatch D (snd l) arg)"
      using \<open>l \<notin> predInterpDomain P D F\<close> predInterpDomain_iff by blast
    then show ?thesis
      by (smt (verit, del_insts) predInterpUpdate_def)
  next
    assume "\<not>(predicate_exists P (fst l))"
    then show ?thesis
      by (simp add: predInterpUpdate_def)
  qed
qed

theorem mono_inc_predInterpUpdate:
  assumes "wd_pred_prog P"
  shows "mono_inc (predInterpUpdate P D F)"
proof (rule mono_inc_rule)
  fix \<Delta> \<Delta>' :: "'a pred_interp"
  fix l :: "'a predicate_loc"
  assume "\<Delta> \<preceq> \<Delta>'"
  show "predInterpUpdate P D F \<Delta> l \<sqsubseteq> predInterpUpdate P D F \<Delta>' l"
  proof cases
    assume "l \<in> predInterpDomain P D F"
    obtain ident v where "ident = fst l" and "v = snd l"
      by simp
    obtain A where "A = predicate_body P ident"
      by simp
    have "predicate_exists P ident"
      using \<open>ident = fst l\<close> \<open>l \<in> predInterpDomain P D F\<close> predInterpDomain_iff by blast
    then obtain p where "program.predicates P ident = Some p"
      using predicate_exists_def by auto
    then have "wd_pred p"
      using assms wd_pred_prog_def by auto
    then have "wd_pred_asst A"
      by (simp add: \<open>A = predicate_body P ident\<close> \<open>program.predicates P ident = Some p\<close> predicate_body_def wd_pred_def)
    then have "pos_acc_assertion A"
      by (simp add: wd_pred_asst_def)
    then have "pos_neg_assertion True A"
      by (simp add: pos_acc_assertion_def)
    then have "assertion_upt D F A v \<Delta> \<subseteq> assertion_upt D F A v \<Delta>'"
      using \<open>\<Delta> \<preceq> \<Delta>'\<close> inc_assertion_upt_def mono_assertion_upt by blast
    moreover have "predInterpUpdate P D F \<Delta> l = Some (assertion_upt D F A v \<Delta>)"
      by (metis \<open>ident = fst l\<close> \<open>l \<in> predInterpDomain P D F\<close> \<open>A = predicate_body P ident\<close> \<open>v = snd l\<close> predInterpUpdate_domain(1))
    moreover have "predInterpUpdate P D F \<Delta>' l = Some (assertion_upt D F A v \<Delta>')"
      by (metis \<open>ident = fst l\<close> \<open>l \<in> predInterpDomain P D F\<close> \<open>A = predicate_body P ident\<close> \<open>v = snd l\<close> predInterpUpdate_domain(1))
    ultimately show ?thesis
      by simp
  next
    assume "l \<notin> predInterpDomain P D F"
    then have "predInterpUpdate P D F \<Delta> l = None"
      by (metis predInterpUpdate_domain(2))
    then show ?thesis
      by simp
  qed
qed



end