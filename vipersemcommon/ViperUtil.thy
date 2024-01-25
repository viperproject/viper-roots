theory ViperUtil
imports Main
begin

instantiation option :: (order) order
begin

definition less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  where "a \<le> b \<equiv> 
         a = None \<or>
         (\<exists>v1 v2. a = Some v1 \<and> b = Some v2 \<and> v1 \<le> v2)"

definition less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  where "a < b \<equiv> 
           (a = None \<and> b \<noteq> None) \<or>
           (\<exists>v1 v2. a = Some v1 \<and> b = Some v2 \<and> v1 < v2)"

instance
proof
  fix x y z :: "'a option"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_option_def less_option_def
    by auto

  show "x \<le> x"
    unfolding less_eq_option_def less_option_def
    by auto
    
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_option_def less_option_def
    by force

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_option_def less_option_def
    by auto
qed
end

lemma less_eq_None [simp]: "None \<le> a"
  by (simp add: less_eq_option_def)

lemma less_eq_Some [simp]: "a \<le> b \<Longrightarrow> Some a \<le> Some b"
  by (simp add: less_eq_option_def)

lemma less_None [simp]: "None < Some a"
  by (simp add: less_option_def)

lemma less_Some [simp]: "a < b \<Longrightarrow> Some a < Some b"
  by (simp add: less_option_def)

end