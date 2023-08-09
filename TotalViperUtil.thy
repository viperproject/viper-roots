section \<open>Utility functions and lemmas for Viper\<close>

theory TotalViperUtil
imports Viper.ValueAndBasicState Viper.DeBruijn Viper.ViperUtil TotalUtil
begin

fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"

subsection \<open>Positive rationals (TODO: move to Viper theory?)\<close>

lemma prat_non_negative: "\<And>q. Rep_prat q \<ge> 0"
  by (transfer) simp

lemma padd_aux:
  assumes "p_rat \<ge> 0"
      and "q_real = real_of_rat (Rep_prat q)"
    shows "q_real + real_of_rat p_rat = real_of_rat (Rep_prat (padd q (Abs_prat p_rat)))"
  using assms 
  by (simp add: Abs_prat_inverse of_rat_add plus_prat.rep_eq)

lemma psub_aux:
  assumes "p_rat \<ge> 0"
      and "real_of_rat p_rat \<le> q_real"
      and "q_real = real_of_rat (Rep_prat q)"
        shows "q_real - real_of_rat p_rat = real_of_rat (Rep_prat (q - (Abs_prat p_rat)))"
  using assms
  apply (subst \<open>q_real = _\<close>)
  apply (unfold minus_prat_def)
  apply (simp add: Abs_prat_inverse of_rat_diff)
  using add.group_left_neutral add_le_imp_le_diff leD leI of_rat_add of_rat_diff of_rat_less  padd_aux 
  by (metis add_0 zero_prat.rep_eq)  

lemma prat_positive_transfer:
  assumes "real_of_rat (Rep_prat qpos) = r" and
          "pgt qpos pnone"
        shows "r > 0"
  using assms
  apply transfer
  by simp

subsection \<open>Recursive predicates on assertions\<close>

subsubsection \<open>General predicates\<close>

fun pure_exp_pred_rec :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> pure_exp \<Rightarrow> bool" and
    pure_exp_pred :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> pure_exp \<Rightarrow> bool"
    where
  "pure_exp_pred p e \<longleftrightarrow> (p e \<and> pure_exp_pred_rec p e)"
| "pure_exp_pred_rec p (Var x) \<longleftrightarrow> True"
| "pure_exp_pred_rec p (ELit lit) \<longleftrightarrow> True"
| "pure_exp_pred_rec p (Unop uop e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Binop e1 bop e2) \<longleftrightarrow> pure_exp_pred p e1 \<and> pure_exp_pred p e2"
| "pure_exp_pred_rec p (CondExp cond e1 e2) \<longleftrightarrow> pure_exp_pred p cond \<and> pure_exp_pred p e1 \<and> pure_exp_pred p e2"
| "pure_exp_pred_rec p (FieldAcc e f) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Old lbl e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (Perm e f) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (PermPred pname es) \<longleftrightarrow> list_all (pure_exp_pred p) es"
| "pure_exp_pred_rec p (FunApp f es) \<longleftrightarrow> list_all (pure_exp_pred p) es"
| "pure_exp_pred_rec p Result \<longleftrightarrow> True"
| "pure_exp_pred_rec p (Unfolding pname es e) \<longleftrightarrow> list_all (pure_exp_pred p) es \<and> pure_exp_pred p e"
| "pure_exp_pred_rec p (pure_exp.Let e e_body) \<longleftrightarrow> pure_exp_pred p e \<and> pure_exp_pred p e_body"
| "pure_exp_pred_rec p (PExists ty e) \<longleftrightarrow> pure_exp_pred p e"
| "pure_exp_pred_rec p (PForall ty e) \<longleftrightarrow> pure_exp_pred p e"

fun
  atomic_assert_pred :: "(pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert) \<Rightarrow> bool" and
  atomic_assert_pred_rec :: "(pure_exp \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert) \<Rightarrow> bool"
  where 
  "atomic_assert_pred p_atm p_e A_atm \<longleftrightarrow> p_atm A_atm \<and> atomic_assert_pred_rec p_e A_atm"
| "atomic_assert_pred_rec p_e (Pure e) \<longleftrightarrow> pure_exp_pred p_e e"
| "atomic_assert_pred_rec p_e (Acc e f Wildcard) \<longleftrightarrow> pure_exp_pred p_e e"
| "atomic_assert_pred_rec p_e (Acc e1 f (PureExp e2)) \<longleftrightarrow> pure_exp_pred p_e e1 \<and> pure_exp_pred p_e e2"
| "atomic_assert_pred_rec p_e (AccPredicate pname es Wildcard) \<longleftrightarrow> list_all (pure_exp_pred p_e) es"
| "atomic_assert_pred_rec p_e (AccPredicate pname es (PureExp e2)) \<longleftrightarrow> (list_all (pure_exp_pred p_e) es) \<and> pure_exp_pred p_e e2"

fun assert_pred :: "(assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> bool" and
    assert_pred_rec :: "(assertion \<Rightarrow> bool) \<Rightarrow> (pure_exp atomic_assert \<Rightarrow> bool) \<Rightarrow> (pure_exp \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow>  bool"
  where 
  "assert_pred p_assert p_atm p_e A \<longleftrightarrow> p_assert A \<and> assert_pred_rec p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Atomic A_atm) \<longleftrightarrow> atomic_assert_pred p_atm p_e A_atm"
| "assert_pred_rec p_assert p_atm p_e (Imp e A) \<longleftrightarrow> pure_exp_pred p_e e \<and> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (A && B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ImpureAnd A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ImpureOr A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"
| "assert_pred_rec p_assert p_atm p_e (ForAll _ A) \<longleftrightarrow> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Exists _ A) \<longleftrightarrow> assert_pred p_assert p_atm p_e A"
| "assert_pred_rec p_assert p_atm p_e (Wand A B) \<longleftrightarrow> assert_pred p_assert p_atm p_e A \<and> assert_pred p_assert p_atm p_e B"


subsubsection \<open>Common instantiations\<close>

text \<open>No permission introspection\<close>

fun no_perm_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where 
    "no_perm_pure_exp_no_rec (Perm e f) = False"
  | "no_perm_pure_exp_no_rec (PermPred e f) = False"
  | "no_perm_pure_exp_no_rec _ = True"

abbreviation no_perm_pure_exp
  where "no_perm_pure_exp \<equiv> pure_exp_pred no_perm_pure_exp_no_rec"

abbreviation no_perm_assertion
  where "no_perm_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_perm_pure_exp_no_rec"

fun no_unfolding_pure_exp_no_rec :: "pure_exp \<Rightarrow> bool"
  where 
    "no_unfolding_pure_exp_no_rec (Unfolding p es e) = False"
  | "no_unfolding_pure_exp_no_rec _ = True"

abbreviation no_unfolding_pure_exp
  where "no_unfolding_pure_exp \<equiv> pure_exp_pred no_unfolding_pure_exp_no_rec"

abbreviation no_unfolding_assertion
  where "no_unfolding_assertion \<equiv> assert_pred (\<lambda>_. True) (\<lambda>_. True) no_unfolding_pure_exp_no_rec"

subsection \<open>Free variables\<close>

fun free_var_pure_exp :: "pure_exp \<Rightarrow> var set"
  where
  "free_var_pure_exp (Var x) = {x}"
| "free_var_pure_exp (ELit lit) = {}"
| "free_var_pure_exp Result = {}"
| "free_var_pure_exp (Unop uop e) = free_var_pure_exp e"
| "free_var_pure_exp (Binop e1 bop e2) = free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_pure_exp (CondExp cond e1 e2) = free_var_pure_exp cond \<union> free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_pure_exp (FieldAcc e f) = free_var_pure_exp e"
| "free_var_pure_exp (Old lbl e) = free_var_pure_exp e"
| "free_var_pure_exp (Perm e f) = free_var_pure_exp e"
| "free_var_pure_exp (PermPred pname es) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_pure_exp (FunApp f es) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_pure_exp (Unfolding pname es e) = \<Union> (set (map free_var_pure_exp es)) \<union> free_var_pure_exp e"
| "free_var_pure_exp (pure_exp.Let e e_body) = free_var_pure_exp e \<union> (shift_down_set (free_var_pure_exp e_body))" 
| "free_var_pure_exp (PExists ty e) = shift_down_set (free_var_pure_exp e)"
| "free_var_pure_exp (PForall ty e) = shift_down_set (free_var_pure_exp e)"

fun
  free_var_atomic_assert :: "pure_exp atomic_assert \<Rightarrow> var set" where  
  "free_var_atomic_assert (Pure e) = free_var_pure_exp e"
| "free_var_atomic_assert (Acc e f Wildcard) = free_var_pure_exp e"
| "free_var_atomic_assert (Acc e1 f (PureExp e2)) = free_var_pure_exp e1 \<union> free_var_pure_exp e2"
| "free_var_atomic_assert (AccPredicate pname es Wildcard) = \<Union> (set (map free_var_pure_exp es))"
| "free_var_atomic_assert (AccPredicate pname es (PureExp e2)) = \<Union> (set (map free_var_pure_exp es)) \<union> free_var_pure_exp e2"

fun free_var_assertion :: "assertion \<Rightarrow> var set"  where  
  "free_var_assertion (Atomic atm) = free_var_atomic_assert atm"
| "free_var_assertion (Imp e A) = free_var_pure_exp e \<union> free_var_assertion A"
| "free_var_assertion (A && B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ImpureAnd A B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ImpureOr A B) = free_var_assertion A \<union> free_var_assertion B"
| "free_var_assertion (ForAll _ A) = free_var_assertion A"
| "free_var_assertion (Exists _ A) = free_var_assertion A"
| "free_var_assertion (Wand A B) = free_var_assertion A \<union> free_var_assertion B"

end