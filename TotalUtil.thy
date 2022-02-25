theory TotalUtil
imports Viper.ViperLang Viper.ValueAndBasicState TotalStateUtil
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

fun option_fold :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "option_fold f e (Some x) = f x"
  | "option_fold f e None = e"

fun nth_option :: "'a list => nat => 'a option"
  where "nth_option xs n = (if n < length xs then Some (nth xs n) else None)"

abbreviation option_if :: "bool \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "option_if b opt \<equiv> if b then opt else None"

abbreviation Some_if :: "bool \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "Some_if b x \<equiv> option_if b (Some x)"

subsection \<open>\<open>if_Some\<close>\<close>

text \<open>interface for \<open>if_Some\<close> was initially defined by Benjamin Bonneau\<close>

primrec if_Some :: "'a option \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
    "if_Some (Some x) f = f x"
  | "if_Some None     f = True"

lemma if_SomeI:
  "(\<And>x. opt = Some x \<Longrightarrow> f x) \<Longrightarrow> if_Some opt f"
  by (cases opt; simp)
lemma if_SomeIex:
  "opt = Some x \<Longrightarrow> f x \<Longrightarrow> if_Some opt f"
  by (cases opt; simp)
lemma if_SomeD:
  "if_Some opt f \<Longrightarrow> opt = Some x \<Longrightarrow> f x"
  by simp
lemma if_Some_iff:
  "(if_Some opt f) = (\<forall>x. opt = Some x \<longrightarrow> f x)"
  by (cases opt; simp)

lemma if_Some_split:
  "P (if_Some opt f) = ((opt = None \<longrightarrow> P True) \<and> (\<forall>x. opt = Some x \<longrightarrow> P (f x)))"
  by (cases opt; simp)
lemma if_Some_split_asm:
  "P (if_Some opt f) = (\<not> ((opt = None \<and> \<not> P True) \<or> (\<exists>x. opt = Some x \<and> \<not> P (f x))))"
  by (cases opt; simp)

lemma if_Some_imp:
  "if_Some opt P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> if_Some opt Q"
  by (cases opt; simp)
lemma if_Some_mono_strong:
  "if_Some opt P \<Longrightarrow> (\<And>x. opt = Some x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> if_Some opt Q"
  by (cases opt; simp)
lemma if_Some_mono[mono]:
  "P \<le> Q \<Longrightarrow> if_Some opt P \<le> if_Some opt Q"
  by (cases opt; auto)
lemma[fundef_cong]:
  "x = y \<Longrightarrow> (\<And>z. y = Some z \<Longrightarrow> P z = Q z) \<Longrightarrow> if_Some x P = if_Some y Q"
  by (cases y; simp)

end