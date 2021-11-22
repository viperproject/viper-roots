theory TotalUtil
imports Viper.ViperLang Viper.ValueAndBasicState TotalStateUtil
begin

fun map_result_2 :: "(mask \<Rightarrow> (mask set) option) \<Rightarrow> (mask set) option \<Rightarrow> (mask set) option"
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

end