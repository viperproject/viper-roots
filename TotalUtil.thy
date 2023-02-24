theory TotalUtil
imports TotalStateUtil HOL.Real
begin

fun map_result_2 :: "('a \<Rightarrow> ('a set) option) \<Rightarrow> ('a set) option \<Rightarrow> ('a set) option"
  where 
    "map_result_2 f None = None"
  | "map_result_2 f (Some xs) = (if \<exists>x \<in> xs. f x = None then None else Some (\<Union>x \<in> xs. the (f x))) "

fun map_option_2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "map_option_2 f y None = y"
  | "map_option_2 f _ (Some x) = f x"

fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"

primrec option_fold :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "option_fold f e (Some x) = f x"
  | "option_fold f e None = e"

fun nth_option :: "'a list => nat => 'a option"
  where "nth_option xs n = (if n < length xs then Some (nth xs n) else None)"

abbreviation option_if :: "bool \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "option_if b opt \<equiv> if b then opt else None"

abbreviation Some_if :: "bool \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "Some_if b x \<equiv> option_if b (Some x)"

text \<open>Some helper definitions for trivial Viper programs\<close>

fun f_None :: "'a \<Rightarrow> 'b option"
  where "f_None _ = None"

definition Pr_trivial :: ViperLang.program
  where 
    "Pr_trivial \<equiv> \<lparr> methods = f_None, predicates = f_None, funs = f_None, declared_fields = f_None, domains = 0 \<rparr>"

subsection \<open>\<open>if_Some\<close>\<close>

text \<open>interface for \<open>if_Some\<close> was initially defined by Benjamin Bonneau\<close>

(*
primrec if_Some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
    "if_Some f (Some x) = f x"
  | "if_Some f  None = True"*)

abbreviation has_Some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "has_Some f \<equiv> option_fold f False"

lemma has_SomeI:
  "opt = Some x \<and> f x \<Longrightarrow> has_Some f opt"
  by simp

lemma has_SomeD:
  "has_Some f opt \<Longrightarrow> opt = Some x \<Longrightarrow> f x"
  by simp

lemma has_Some_iff:
  "(has_Some f opt) = (\<exists>x. opt = Some x \<and> f x)"  
  by (cases opt; simp)

lemma has_Some_imp:
  "has_Some P opt \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> has_Some Q opt"
  by (cases opt; simp)

lemma has_Some_mono_strong:
  "has_Some P opt \<Longrightarrow> (\<And>x. opt = Some x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> has_Some Q opt"
  by (cases opt; simp)

lemma has_Some_mono[mono]:
  "P \<le> Q \<Longrightarrow> has_Some P opt \<le> has_Some Q opt"
  by (cases opt; auto)

lemma[fundef_cong]:
  "x = y \<Longrightarrow> (\<And>z. y = Some z \<Longrightarrow> P z = Q z) \<Longrightarrow> has_Some P x = has_Some Q y"
  by (cases y; simp)

abbreviation if_Some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "if_Some \<equiv> pred_option"

lemma if_SomeI:
  "(\<And>x. opt = Some x \<Longrightarrow> f x) \<Longrightarrow> if_Some f opt"
  by (cases opt; simp)
lemma if_SomeIex:
  "opt = Some x \<Longrightarrow> f x \<Longrightarrow> if_Some f opt"
  by (cases opt; simp)
lemma if_SomeD:
  "if_Some f opt \<Longrightarrow> opt = Some x \<Longrightarrow> f x"
  by simp
lemma if_Some_iff:
  "(if_Some f opt) = (\<forall>x. opt = Some x \<longrightarrow> f x)"
  by (cases opt; simp)

lemma if_Some_split:
  "P (if_Some f opt) = ((opt = None \<longrightarrow> P True) \<and> (\<forall>x. opt = Some x \<longrightarrow> P (f x)))"
  by (cases opt; simp)
lemma if_Some_split_asm:
  "P (if_Some f opt) = (\<not> ((opt = None \<and> \<not> P True) \<or> (\<exists>x. opt = Some x \<and> \<not> P (f x))))"
  by (cases opt; simp)

lemma if_Some_imp:
  "if_Some P opt \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> if_Some Q opt"
  by (cases opt; simp)
lemma if_Some_mono_strong:
  "if_Some P opt \<Longrightarrow> (\<And>x. opt = Some x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> if_Some Q opt"
  by (cases opt; simp)
lemma if_Some_mono[mono]:
  "P \<le> Q \<Longrightarrow> if_Some P opt \<le> if_Some Q opt"
  by (cases opt; auto)
lemma[fundef_cong]:
  "x = y \<Longrightarrow> (\<And>z. y = Some z \<Longrightarrow> P z = Q z) \<Longrightarrow> if_Some P x = if_Some Q y"
  by (cases y; simp)

subsection \<open>Positive rationals\<close>

lemma prat_positive_transfer:
  assumes "real_of_rat (Rep_prat qpos) = r" and
          "pgt qpos pnone"
        shows "r > 0"
  using assms
  apply transfer
  by simp

end