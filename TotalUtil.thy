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

definition pred_eq
  where "pred_eq x v = (x = v)"

lemma pred_eq_refl: "pred_eq a a"
  by (simp add: pred_eq_def)

lemma rev_iffD1_def: "P \<Longrightarrow> P \<equiv> Q \<Longrightarrow> Q"
  by blast

text \<open>Disjointness helper lemmas\<close>

lemma list_all_ran_map_of: 
  assumes "list_all (\<lambda> x. P (snd x)) xs"
  shows "\<forall>y \<in> ran (map_of xs). P y"
proof (rule ballI)
  fix y
  assume "y \<in> ran (map_of xs)"
  from this obtain x where "(map_of xs) x = Some y "
    unfolding ran_def
    by blast

  hence "(x,y) \<in> set xs"
    by (simp add: map_of_SomeD)

  thus "P y"
    using assms
    by (metis list.pred_set snd_conv)
qed

lemma not_satisfies_prop_in_set:
  assumes "\<forall>x \<in> xs. P x" and
          "\<not> P y"
        shows "y \<notin> xs"
  using assms
  by force

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

subsection \<open>positive rationals (TODO: move to Viper theory?)\<close>

lemma prat_non_negative: "\<And>q. Rep_prat q \<ge> 0"
  by (transfer) simp

lemma padd_aux:
  assumes "p_rat \<ge> 0" and
          "q_real = real_of_rat (Rep_prat q)"
        shows "q_real + real_of_rat p_rat = real_of_rat (Rep_prat (padd q (Abs_prat p_rat)))"
  using assms
  by (simp add: Abs_prat_inverse padd.rep_eq of_rat_add)

lemma psub_aux:
  assumes "p_rat \<ge> 0" and
          "real_of_rat p_rat \<le> q_real" and
          "q_real = real_of_rat (Rep_prat q)"
        shows "q_real - real_of_rat p_rat = real_of_rat (Rep_prat (psub q (Abs_prat p_rat)))"
  using assms
  apply (subst \<open>q_real = _\<close>)
  apply (unfold psub_def)
  apply (simp add: Abs_prat_inverse of_rat_diff)
  by (metis add.group_left_neutral add_le_imp_le_diff leD leI of_rat_add of_rat_diff of_rat_less padd.rep_eq padd_aux pnone.rep_eq)
  
subsection \<open>uncurry\<close>

fun uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c"
  where "uncurry f = (\<lambda>a. f (fst a) (snd a))"

lemma uncurry_case_prod: "uncurry = case_prod"
  by fastforce

subsection \<open>Positive rationals\<close>

lemma prat_positive_transfer:
  assumes "real_of_rat (Rep_prat qpos) = r" and
          "pgt qpos pnone"
        shows "r > 0"
  using assms
  apply transfer
  by simp

subsection \<open>Disjoint lists\<close>

definition disjoint_list :: " ('a set) list \<Rightarrow> bool"
  where "disjoint_list xs = (\<forall>i j. 0 \<le> i \<and> i < length xs \<and> 0 \<le> j \<and> j < length xs \<and> i \<noteq> j \<longrightarrow> disjnt (xs ! i) (xs ! j))"

lemma disjoint_list_app_disj:
  assumes "disjoint_list (xs@ys)" and
          "x \<in> set xs" and
          "y \<in> set ys"
        shows "disjnt x y"
proof -
  from \<open>x \<in> set xs\<close> obtain i where "0 \<le> i" and "i < length xs" and "x = xs ! i"
    by (metis bot_nat_0.extremum in_set_conv_nth)
  hence xElem: "x = (xs@ys) ! i"
    using List.nth_append
    by metis

  from \<open>y \<in> set ys\<close> obtain j where "0 \<le> j" and "j < length ys" and "y = ys ! j"
    by (metis bot_nat_0.extremum in_set_conv_nth)
  hence "y = (xs@ys) ! (length xs + j)"
    using List.nth_append
    by auto

  with xElem \<open>0 \<le> i\<close> \<open>i < length xs\<close> \<open>0 \<le> j\<close> \<open>j < length ys\<close> show ?thesis
    using assms
    unfolding disjoint_list_def
    by (simp add: add.commute)
qed

lemma disjoint_list_add:
  assumes Disj: "disjoint_list (xs@(M#ys))" and
          Fresh: "\<forall>A \<in> set (xs@ys). m \<notin> A"
        shows "disjoint_list (xs@((M \<union> {m})#ys))"
  unfolding disjoint_list_def
proof (rule allI | rule impI)+
  fix i j
  assume Bounds: "0 \<le> i \<and> i < length (xs @ (M \<union> {m}) # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> {m}) # ys) \<and> i \<noteq> j"
  hence "i \<noteq> j"
    by simp

  have DisjXsM: "\<And>x. x \<in> set xs \<Longrightarrow> disjnt x (M \<union> {m})"
    using assms disjoint_list_app_disj
    by fastforce

  have DisjXsYs: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> disjnt x y"
    using Disj disjoint_list_app_disj
    by fastforce

  have DisjYsM: "\<And>y. y \<in> set ys \<Longrightarrow> disjnt (M \<union> {m}) y"
  proof -
    fix y
    assume "y \<in> set ys"
    from Disj have "disjoint_list ((xs@[M])@ys)" 
      by simp
    hence "disjnt M y"
      using \<open>y \<in> _\<close> disjoint_list_app_disj
      by fastforce
    thus "disjnt (M \<union> {m}) y"
      using Fresh \<open>y \<in> set ys\<close> by fastforce
  qed  

  have ElemYsAux: "\<And>j. length xs < j \<Longrightarrow> j < length (xs @ (M \<union> {m}) # ys) \<Longrightarrow> (xs @ ((M \<union> {m}) # ys)) ! j \<in> set ys"
  proof -
    fix j
    assume "length xs < j" and "j < length (xs @ (M \<union> {m}) # ys)"

    hence "j \<ge> length (xs @ [M \<union> {m}])"
            by simp 

   let ?b = "(xs @ ((M \<union> {m}) # ys)) ! j"
          
    have Eq: "(xs @ (M \<union> {m}) # ys) = ((xs @ [M \<union> {m}]) @ ys)"
      by simp
 
    from \<open>j \<ge> length (xs @ [M \<union> {m}])\<close> \<open>j < length (xs @ (M \<union> {m}) # ys)\<close> obtain j' where
       "?b = ys ! j'" and "j' = j - (length (xs @ [M \<union> {m}]))"
      using Eq List.nth_append[where ?ys=ys] 
      by (metis linorder_not_less)            
      
    thus "?b \<in> set ys"
      using \<open>j \<ge> length (xs @ [M \<union> {m}])\<close> and \<open>j < length (xs @ (M \<union> {m}) # ys)\<close>
      by simp
  qed


  have Aux: "\<And>i j. 0 \<le> i \<and> i < length (xs @ (M \<union> {m}) # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> {m}) # ys) \<and> i \<noteq> j \<Longrightarrow>
               i < length xs  \<Longrightarrow> disjnt ((xs @ (M \<union> {m}) # ys) ! i) ((xs @ (M \<union> {m}) # ys) ! j)"
  proof -
    fix i j
    assume Bounds: "0 \<le> i \<and> i < length (xs @ (M \<union> {m}) # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> {m}) # ys) \<and> i \<noteq> j"
    hence "i \<noteq> j"
      by simp
    assume A: "i < length xs"
    show "disjnt ((xs @ (M \<union> {m}) # ys) ! i) ((xs @ (M \<union> {m}) # ys) ! j)" (is "disjnt ?a ?b")
    proof -
      from A
      have "?a \<in> set xs"
        using List.nth_append
        by (metis nth_mem)

      with A have "?a = (xs @ M # ys) ! i"
        using List.nth_append
        by metis

    then show ?thesis
    proof (cases "0 \<le> j \<and> j < length xs")
      case True 
        hence "?b \<in> set xs"
        using List.nth_append
        by (metis nth_mem)

      with True have "?b = (xs @ M # ys) ! j"
        using List.nth_append
        by metis
      with \<open>?a = _\<close> 
      show ?thesis
        using Disj A Bounds \<open>0 \<le> j \<and> j < length xs\<close> \<open>i \<noteq> j\<close>
        unfolding disjoint_list_def
        by simp                
    next
      case False
        with Bounds have "length xs \<le> j" and "j < length (xs @ (M \<union> {m}) # ys)"
          by auto

        show ?thesis
        proof (cases "j = length xs")
          case True
          hence "?b = (M \<union> {m})"
            by simp
          then show ?thesis 
            using DisjXsM \<open>?a \<in> set xs\<close>
            by simp
        next
          case False
          hence "?b \<in> set ys"
            using ElemYsAux \<open>j < length (xs @ (M \<union> {m}) # ys)\<close> \<open>length xs \<le> j\<close> by fastforce  

          with \<open>?a \<in> set xs\<close>  show ?thesis
            using DisjXsYs
            by simp
        qed
      qed
    qed
  qed

  show "disjnt ((xs @ (M \<union> {m}) # ys) ! i) ((xs @ (M \<union> {m}) # ys) ! j)" (is "disjnt ?a ?b")
  proof (cases "i < length xs")
    case True
    then show ?thesis using Aux[OF Bounds]
      by simp      
  next
    case False
    hence "i \<ge> length xs"
      by simp

    show ?thesis 
    proof (cases "j < length xs")
      case True
      \<comment>\<open>We have already shown the symmetric case\<close>
      then show ?thesis 
        using Aux Bounds disjnt_sym
        by blast
    next
      case False
      hence "j \<ge> length xs"
        by simp
      \<comment>\<open>Now we prove the case where \<^term>\<open>i = length xs\<close> and thus \<^term>\<open>j > length xs\<close>. We can then prove
        the case where  \<^term>\<open>i > length xs\<close> and \<^term>\<open>j = length xs\<close> by symmetry\<close>

      have Aux2: "\<And>i j. i = length xs \<Longrightarrow> j > length xs \<Longrightarrow> j < length (xs @ (M \<union> {m}) # ys) \<Longrightarrow> i \<noteq> j \<Longrightarrow>
                disjnt ((xs @ (M \<union> {m}) # ys) ! i) ((xs @ (M \<union> {m}) # ys) ! j)"
      proof -
        fix i j
        assume "i = length xs" and "length xs < j" and "j < length (xs @ (M \<union> {m}) # ys)" and "i \<noteq> j"
        show "disjnt ((xs @ (M \<union> {m}) # ys) ! i) ((xs @ (M \<union> {m}) # ys) ! j)" (is "disjnt ?a ?b")
        proof -
          from \<open>i = length xs\<close> have "?a = M \<union> {m}"
            by simp

          have "?b \<in> set ys"
            using ElemYsAux \<open>j < length (xs @ (M \<union> {m}) # ys)\<close> \<open>length xs < j\<close> 
            by blast

          thus ?thesis
            using \<open>?a = _\<close> DisjYsM
            by simp
        qed
      qed

      show ?thesis
      proof (cases "i = length xs")
        case True
        thus ?thesis
          using Aux2 \<open>j \<ge> length xs\<close>  Bounds
          by auto                              
      next
        case False
        show ?thesis 
        proof (cases "j = length xs")
          case True
          then show ?thesis using Aux2 \<open>i \<ge> length xs\<close> Bounds
            by (metis disjnt_sym order_le_neq_trans)
        next
          case False
          have Eq: "length (xs @ M # ys) = length (xs @ (M \<union> {m}) # ys)" 
            by simp

          have "disjnt ((xs @ M # ys) ! i) ((xs @ M # ys) ! j)"
            using Disj \<open>i \<noteq> j\<close> \<open>i \<ge> length xs\<close> \<open>j \<ge> length xs\<close>
            unfolding disjoint_list_def 
            apply (simp only: Eq)
            using Bounds by blast
            

          moreover have "?a = (xs @ M # ys) ! i" and "?b = (xs @ M # ys) ! j"                    
             apply (metis \<open>i \<noteq> length xs\<close> list_update_length nth_list_update_neq)
            by (metis False list_update_length nth_list_update_neq)             
          ultimately show ?thesis
            by argo                        
        qed
      qed
    qed
  qed
qed

lemma disjoint_list_subset: 
  assumes "disjoint_list xs" and
          "length xs = length xs'" and
          "\<And> i j. 0 \<le> i \<Longrightarrow> i < length xs \<Longrightarrow> xs' ! i \<subseteq> xs ! i"
        shows "disjoint_list xs'"
  using assms
  unfolding disjoint_list_def
  by (metis disjnt_subset1 disjnt_subset2)

end