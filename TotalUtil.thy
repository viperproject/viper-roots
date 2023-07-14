theory TotalUtil
imports Viper.ValueAndBasicState Viper.DeBruijn HOL.Real "HOL-Library.Multiset"
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

lemma Some_Some_ifD:
  assumes "Some x = Some_if P y"
  shows "P"
  using assms
  by (metis option.distinct(1))

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

lemma list_all_map_of: 
  assumes "list_all (\<lambda> y. P (fst y) (snd y)) xs"
  shows "\<forall>a b. map_of xs a = Some b \<longrightarrow> P a b"
proof (rule allI | rule impI)+
  fix a b
  assume "map_of xs a = Some b"

  hence "(a, b) \<in> set xs"
    by (simp add: map_of_SomeD)

  moreover from assms have "\<forall> (a',b') \<in> set xs. P a' b'"
    using list_all_iff assms
    by (metis case_prod_beta')

  ultimately show "P a b"
    by blast
qed    

lemma not_satisfies_prop_in_set:
  assumes "\<forall>x \<in> xs. P x" and
          "\<not> P y"
        shows "y \<notin> xs"
  using assms
  by force

lemma list_all2_revD:
  assumes "list_all2 P xs ys"
  shows "list_all2 P (rev xs) (rev ys)"
  using assms
  by simp

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

subsection \<open>Positive rationals (TODO: move to Viper theory?)\<close>

lemma prat_non_negative: "\<And>q. Rep_prat q \<ge> 0"
  by (transfer) simp

lemma padd_aux:
  assumes "p_rat \<ge> 0" and
          "q_real = real_of_rat (Rep_prat q)"
        shows "q_real + real_of_rat p_rat = real_of_rat (Rep_prat (padd q (Abs_prat p_rat)))"
  using assms 
  by (simp add: Abs_prat_inverse of_rat_add plus_prat.rep_eq)

lemma psub_aux:
  assumes "p_rat \<ge> 0" and
          "real_of_rat p_rat \<le> q_real" and
          "q_real = real_of_rat (Rep_prat q)"
        shows "q_real - real_of_rat p_rat = real_of_rat (Rep_prat (q - (Abs_prat p_rat)))"
  using assms
  apply (subst \<open>q_real = _\<close>)
  apply (unfold minus_prat_def)
  apply (simp add: Abs_prat_inverse of_rat_diff)
  using add.group_left_neutral add_le_imp_le_diff leD leI of_rat_add of_rat_diff of_rat_less  padd_aux 
  by (metis add_0 zero_prat.rep_eq)  
  
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

lemma disjoint_list_add_set:
  assumes Disj: "disjoint_list (xs@(M#ys))" and
          Fresh: "\<forall>A \<in> set (xs@ys). disjnt M' A"
        shows "disjoint_list (xs@((M \<union> M')#ys))"
  unfolding disjoint_list_def
proof (rule allI | rule impI)+
  fix i j
  assume Bounds: "0 \<le> i \<and> i < length (xs @ (M \<union> M') # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> M') # ys) \<and> i \<noteq> j"
  hence "i \<noteq> j"
    by simp

  have DisjXsM: "\<And>x. x \<in> set xs \<Longrightarrow> disjnt x (M \<union> M')"
    using assms disjoint_list_app_disj
    by (metis UnCI disjnt_Un2 disjnt_sym list.set_intros(1) set_append)

  have DisjXsYs: "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> disjnt x y"
    using Disj disjoint_list_app_disj
    by fastforce

  have DisjYsM: "\<And>y. y \<in> set ys \<Longrightarrow> disjnt (M \<union> M') y"
  proof -
    fix y
    assume "y \<in> set ys"
    from Disj have "disjoint_list ((xs@[M])@ys)" 
      by simp
    hence "disjnt M y"
      using \<open>y \<in> _\<close> disjoint_list_app_disj
      by fastforce
    thus "disjnt (M \<union> M') y"
      using Fresh \<open>y \<in> set ys\<close> 
      by (metis UnCI disjnt_Un2 disjnt_sym set_append)
  qed  

  have ElemYsAux: "\<And>j. length xs < j \<Longrightarrow> j < length (xs @ (M \<union> M') # ys) \<Longrightarrow> (xs @ ((M \<union> M') # ys)) ! j \<in> set ys"
  proof -
    fix j
    assume "length xs < j" and "j < length (xs @ (M \<union> M') # ys)"

    hence "j \<ge> length (xs @ [M \<union> M'])"
            by simp 

   let ?b = "(xs @ ((M \<union> M') # ys)) ! j"
          
    have Eq: "(xs @ (M \<union> M') # ys) = ((xs @ [M \<union> M']) @ ys)"
      by simp
 
    from \<open>j \<ge> length (xs @ [M \<union> M'])\<close> \<open>j < length (xs @ (M \<union> M') # ys)\<close> obtain j' where
       "?b = ys ! j'" and "j' = j - (length (xs @ [M \<union> M']))"
      using Eq List.nth_append[where ?ys=ys] 
      by (metis linorder_not_less)            
      
    thus "?b \<in> set ys"
      using \<open>j \<ge> length (xs @ [M \<union> M'])\<close> and \<open>j < length (xs @ (M \<union> M') # ys)\<close>
      by simp
  qed

  have Aux: "\<And>i j. 0 \<le> i \<and> i < length (xs @ (M \<union> M') # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> M') # ys) \<and> i \<noteq> j \<Longrightarrow>
               i < length xs  \<Longrightarrow> disjnt ((xs @ (M \<union> M') # ys) ! i) ((xs @ (M \<union> M') # ys) ! j)"
  proof -
    fix i j
    assume Bounds: "0 \<le> i \<and> i < length (xs @ (M \<union> M') # ys) \<and> 0 \<le> j \<and> j < length (xs @ (M \<union> M') # ys) \<and> i \<noteq> j"
    hence "i \<noteq> j"
      by simp
    assume A: "i < length xs"
    show "disjnt ((xs @ (M \<union> M') # ys) ! i) ((xs @ (M \<union> M') # ys) ! j)" (is "disjnt ?a ?b")
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
        with Bounds have "length xs \<le> j" and "j < length (xs @ (M \<union> M') # ys)"
          by auto

        show ?thesis
        proof (cases "j = length xs")
          case True
          hence "?b = (M \<union> M')"
            by simp
          then show ?thesis 
            using DisjXsM \<open>?a \<in> set xs\<close>
            by simp
        next
          case False
          hence "?b \<in> set ys"
            using ElemYsAux \<open>j < length (xs @ (M \<union> M') # ys)\<close> \<open>length xs \<le> j\<close> by fastforce  

          with \<open>?a \<in> set xs\<close>  show ?thesis
            using DisjXsYs
            by simp
        qed
      qed
    qed
  qed

  show "disjnt ((xs @ (M \<union> M') # ys) ! i) ((xs @ (M \<union> M') # ys) ! j)" (is "disjnt ?a ?b")
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

      have Aux2: "\<And>i j. i = length xs \<Longrightarrow> j > length xs \<Longrightarrow> j < length (xs @ (M \<union> M') # ys) \<Longrightarrow> i \<noteq> j \<Longrightarrow>
                disjnt ((xs @ (M \<union> M') # ys) ! i) ((xs @ (M \<union> M') # ys) ! j)"
      proof -
        fix i j
        assume "i = length xs" and "length xs < j" and "j < length (xs @ (M \<union> M') # ys)" and "i \<noteq> j"
        show "disjnt ((xs @ (M \<union> M') # ys) ! i) ((xs @ (M \<union> M') # ys) ! j)" (is "disjnt ?a ?b")
        proof -
          from \<open>i = length xs\<close> have "?a = M \<union> M'"
            by simp

          have "?b \<in> set ys"
            using ElemYsAux \<open>j < length (xs @ (M \<union> M') # ys)\<close> \<open>length xs < j\<close> 
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
          have Eq: "length (xs @ M # ys) = length (xs @ (M \<union> M') # ys)" 
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

lemma disjoint_list_add:
  assumes Disj: "disjoint_list (xs@(M#ys))" and
          Fresh: "\<forall>A \<in> set (xs@ys). m \<notin> A"
        shows "disjoint_list (xs@((M \<union> {m})#ys))"
  apply (rule disjoint_list_add_set)
  using assms 
  by auto

lemma disjoint_list_subset: 
  assumes "disjoint_list xs" and
          "length xs = length xs'" and
          "\<And> i j. 0 \<le> i \<Longrightarrow> i < length xs \<Longrightarrow> xs' ! i \<subseteq> xs ! i"
        shows "disjoint_list xs'"
  using assms
  unfolding disjoint_list_def
  by (metis disjnt_subset1 disjnt_subset2)

lemma disjoint_list_subset_list_all2: 
  assumes "disjoint_list xs" and
          "list_all2 (\<lambda>x y. x \<subseteq> y) xs' xs"
        shows "disjoint_list xs'"
  apply (rule disjoint_list_subset[OF assms(1)])
   apply (simp add: list_all2_lengthD[OF assms(2)])
  by (simp add: list_all2_nthD2[OF assms(2)])

lemma disjoint_list_replace_set:
  assumes Disj: "disjoint_list (xs@(M#ys))" and
          Fresh: "\<forall>A \<in> set (xs@ys). disjnt M' A"
        shows "disjoint_list (xs@(M'#ys))"
proof -
  from assms have "disjoint_list (xs@((M \<union> M')#ys))"
    using disjoint_list_add_set
    by blast
  thus ?thesis
  proof (rule disjoint_list_subset)
    fix i j
    assume "0 \<le> i" and "i < length (xs @ (M \<union> M') # ys)"
    thus "(xs @ M' # ys) ! i \<subseteq> (xs @ (M \<union> M') # ys) ! i "
      by (metis antisym_conv1 list_update_length nless_le nth_append_length nth_list_update_neq sup.orderI sup.right_idem)
  qed simp
qed
    

lemma count_multiset_at_least_two:
  assumes "xs ! i = xs ! j" and 
          "i \<noteq> j" and
          "i < length xs" and "j < length xs"
        shows "count (mset xs) (xs ! i) \<ge> 2"
  using assms
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
  proof (cases i)
    case 0
    thus ?thesis 
      using 0 Cons
      by auto
  next
    case (Suc i')
    hence "(a # xs) ! i = xs ! i'"
      by simp
    show ?thesis
    proof (cases j)
      case 0
      then show ?thesis 
        using Cons
        by auto
    next
      case (Suc j')
      hence "(a # xs) ! j = xs ! j'"
        by simp

      have "i' \<noteq> j'"
        using \<open>i \<noteq> j\<close> \<open>i = Suc i'\<close> \<open>j = Suc j'\<close>
        by fast

      moreover have "xs ! i' = xs ! j'"
        using Cons \<open>(a # xs) ! i = xs ! i'\<close> \<open>(a # xs) ! j = xs ! j'\<close> by fastforce

      moreover have "i' < length xs"
        using \<open>i < _\<close> \<open>i = Suc i'\<close> \<open>j < _\<close> \<open>j = Suc j'\<close>
        by simp
      moreover have "j' < length xs"
        using \<open>j < _\<close> \<open>j = Suc j'\<close>
        by simp

      ultimately have *:"2 \<le> count (mset xs) (xs ! i')"
        using Cons.IH
        by blast
        
      have "count (mset (a # xs)) ((a # xs) ! i) \<ge> count (mset xs) ((a #xs) ! i) "
        by simp
      then show ?thesis 
        using \<open>(a # xs) ! i = xs ! i'\<close> *
        by simp        
    qed
  qed
qed

lemma count_at_least_two_different_elem: 
  assumes "count (mset xs) a \<ge> 2" and 
            "xs ! i = a" and "i < length xs"
          shows "\<exists>j. j < length xs \<and> j \<noteq> i \<and> xs ! j = a"
proof -
  have "xs = take i xs @ xs ! i # drop (Suc i) xs" (is "xs = ?ts @ xs ! i # ?ds")
    using \<open>i < _\<close> List.id_take_nth_drop
    by blast

  hence "count (mset xs) a = count (mset ?ts) a + count (mset (xs ! i # ?ds)) a"
    by (metis count_union mset_append)

  also have "... = count (mset ?ts) a + 1 + count (mset ?ds) a"
    using \<open>xs ! i = a\<close>
    by simp
  finally have *:"count (mset ?ts) a \<ge> 1 \<or> count (mset ?ds) a \<ge> 1"
    using \<open>count (mset xs) a \<ge> 2\<close>
    by linarith

  show ?thesis
  proof (cases rule: disjE[OF *])
    case 1
    hence "a \<in># mset ?ts"
      by simp
    from this obtain j where "?ts ! j = a" and "j < length ?ts"
      using in_set_conv_nth set_mset_mset
      by metis
    thus ?thesis
      by auto      
  next
    case 2
    hence "a \<in># mset ?ds"
      by simp
    from this obtain j where "?ds ! j = a" and "j < length ?ds"
      using in_set_conv_nth set_mset_mset
      by metis
    hence "xs ! (j+(Suc i)) = a"
      using nth_drop
      by (simp add: add.commute)
    thus ?thesis      
      by (metis Suc_n_not_le_n \<open>j < length (drop (Suc i) xs)\<close> drop_drop drop_eq_Nil2 leD le_add2 linorder_le_less_linear)
  qed
qed
 
lemma disjoint_list_sublist:
  assumes "disjoint_list xs" and
         Sub: "mset xs' \<subseteq># mset xs" 
        shows "disjoint_list xs'"
  unfolding disjoint_list_def
proof clarify
  fix i j
  assume *: "0 \<le> i" "i < length xs'" "0 \<le> j" "j < length xs'" "i \<noteq> j"

  let ?a = "xs' ! i" and ?b = "xs' ! j"

  from * have "?a \<in># mset xs'"
    by simp

  hence "?a \<in># mset xs"
    using Sub
    by (meson mset_subset_eqD)

  from this obtain i' where "?a = xs ! i'" and "i' < length xs"
    by (metis in_set_conv_nth set_mset_mset)

  from * have "?b \<in># mset xs'"
    by simp

  hence "?b \<in># mset xs"
    using Sub
    by (meson mset_subset_eqD)

  show "disjnt (xs' ! i) (xs' ! j)"
  proof (cases "?a = ?b")
    case True
    hence "count (mset xs') ?a \<ge> 2"
      using \<open>i \<noteq> j\<close> and \<open>?a \<in># mset xs'\<close> \<open>?b \<in># mset xs'\<close> \<open>i < _\<close> \<open>j < _\<close> count_multiset_at_least_two
      by blast
    hence "count (mset xs) ?a \<ge> 2"
      using Sub
      by (meson le_trans mset_subset_eq_count)
    
    from this obtain j' where "xs ! i' = xs ! j'" and "j' < length xs" and "j' \<noteq> i'"
      using count_at_least_two_different_elem
      by (metis \<open>i' < length xs\<close> \<open>xs' ! i = xs ! i'\<close>)
    then show ?thesis 
      using \<open>i' < _\<close> assms
      unfolding disjoint_list_def
      by (metis True \<open>xs' ! i = xs ! i'\<close> bot_nat_0.extremum)      
  next
    case False
    from \<open>?b \<in># mset xs\<close> obtain j' where "?b = xs ! j'" and "j' < length xs"
      by (metis in_set_conv_nth set_mset_mset)

    with False \<open>?a = xs ! i'\<close> have "i' \<noteq> j'" 
      by auto

    then show ?thesis 
      using assms \<open>i' < length xs\<close> \<open>j' < length xs\<close> \<open>?a = xs ! i'\<close> \<open>?b = xs ! j'\<close>
      unfolding disjoint_list_def
      by simp
  qed
qed

subsection \<open>Maps\<close>

lemma map_add_le_dom_disjoint: 
  assumes "dom m1 \<inter> dom m3 = {}" and
          "m2 \<subseteq>\<^sub>m m3" 
  shows "m1 ++ m2 \<subseteq>\<^sub>m m1 ++ m3"
  using assms
  by (metis map_add_comm map_add_le_mapE map_add_le_mapI map_add_subsumed2 map_le_map_add)

lemma map_upds_distinct_nth:
  assumes "distinct xs" and 
          "x = xs ! i" and
          "i < length xs" and
          "length xs = length ys"
  shows "(m(xs [\<mapsto>] ys)) x = Some (ys ! i)"
using assms
proof (induction xs arbitrary: m i ys)
  case Nil
  then show ?case by simp \<comment>\<open>contradiction\<close>
next
  case (Cons a xs)
    from this obtain b ys' where "ys = b#ys'"
      by (metis list.set_cases nth_mem)

    from Cons have "x \<in> set (a # xs)"
      using nth_mem by blast

  show ?case 
  proof (cases "a = x")
    case True
    from Cons have "i = 0"
      by (metis True length_greater_0_conv list.discI nth_Cons_0 nth_eq_iff_index_eq)
    then show ?thesis 
      using \<open>a = x\<close> Cons \<open>ys = _\<close>
      by simp
  next
    case False

    with Cons have "i > 0"
      by (metis bot_nat_0.not_eq_extremum nth_Cons_0)    

    let ?m' = "m(a \<mapsto> b)"
    have "(m(a # xs [\<mapsto>] ys)) x = (?m'(xs [\<mapsto>] ys')) x"
      using map_upds_Cons \<open>ys = _\<close>
      by simp

    have "... = Some (ys' ! (i-1))"
      apply (rule Cons.IH)
      using \<open>distinct (a#xs)\<close>
         apply simp
      using Cons
        apply (meson \<open>0 < i\<close> nth_Cons_pos)
      using Cons
       apply (metis Suc_diff_1 \<open>0 < i\<close> length_Cons not_less_eq)
      using \<open>length (a # xs) = length ys\<close> \<open>ys = _\<close>
      by simp

    thus ?thesis
      using \<open>ys = _\<close> \<open>0 < i\<close>
      by fastforce
  qed   
qed

lemma map_upds_distinct_rev:
  assumes "distinct xs" and "length xs = length ys"
  shows "[xs [\<mapsto>] ys] = [rev xs [\<mapsto>] rev ys]"
  using assms
  unfolding map_upds_def
  apply simp
  by (metis distinct_rev length_rev map_fst_zip map_of_inject_set set_rev zip_rev)

subsection \<open>Distinct\<close>

lemma distinct_map_inj_on_subset:
assumes 
        "distinct ys"
        "map f ys = ys'" and
        "set ys \<subseteq> dom f" and
        "inj_on f (dom f)"
      shows "distinct ys'"
  using assms distinct_map inj_on_subset
  by blast

lemma distinct_map_the_inj_on_subset:
assumes 
        "distinct ys"
        "map (the \<circ> f) ys = ys'" and
        "set ys \<subseteq> dom f" and
        "inj_on f (dom f)"
      shows "distinct ys'"
proof -
  let ?zs = "map f ys"

  have "map (the \<circ> f) ys  = map the ?zs"
    by simp

  have "distinct ?zs"
    using distinct_map_inj_on_subset assms
    by blast

  from \<open>set ys \<subseteq> _\<close> obtain zs_elems
    where "?zs = map Some zs_elems"
    by (smt (verit, ccfv_threshold) \<open>distinct (map f ys)\<close> distinct_map domIff ex_map_conv f_the_inv_into_f list.set_map option.exhaust the_inv_into_into)

  with \<open>distinct ?zs\<close> have "distinct zs_elems"
    using distinct_map by auto

  thus ?thesis
    using \<open>?zs = _\<close> \<open>map (the \<circ> f) ys = ys'\<close> 
                    \<open>map (the \<circ> f) ys = map the ?zs\<close> 
    by fastforce
qed

lemma inj_on_upt_distinct:
  assumes "distinct ys" and 
          "length ys = length [0..<j]"
  shows "inj_on [[0..<j] [\<mapsto>] ys] (set [0..<j])"
  unfolding inj_on_def
proof (rule ballI | rule impI)+
  fix a b
  assume "a \<in> set [0..<j]" and "b \<in> set [0..<j]" and
         fun_val_eq: "[[0..<j] [\<mapsto>] ys] a = [[0..<j] [\<mapsto>] ys] b" 

  hence a_nth: "a = [0..<j] ! a" and b_nth: "b = [0..<j] ! b"
    by simp_all

  from \<open>a \<in> _\<close> and \<open>b \<in> _\<close> have "a < length [0..<j]" and "b < length [0..<j]"
    by simp_all

  let ?f = "[[0..<j] [\<mapsto>] ys]"

  have "?f a = Some (ys ! a)"
    using map_upds_distinct_nth[OF distinct_upt a_nth \<open>a < _\<close>, where ?m=Map.empty and ?ys = ys] \<open>length ys = _\<close>
    by argo

  moreover have "?f b = Some (ys ! b)"
    using map_upds_distinct_nth[OF distinct_upt b_nth \<open>b < _\<close>, where ?m=Map.empty and ?ys = ys] \<open>length ys = _\<close>
    by argo
    
  ultimately show "a = b"
    using \<open>a < _\<close> \<open>b < _\<close> \<open>distinct ys\<close>
    by (metis fun_val_eq \<open>length ys = _\<close> nth_eq_iff_index_eq option.inject)
qed

lemma map_the_inj_not_in:
  assumes "ys' = map (the \<circ> f) ys" and
          Inj: "inj_on f (dom f)" and
          "a \<notin> set ys" and
          "f a = Some b" and
          "set ys \<subseteq> dom f"
        shows "b \<notin> set ys'"
proof
  assume "b \<in> set ys'"

  from this obtain i where
    "b  = ys' ! i" and
    "(the \<circ> f) (ys ! i) = (ys' ! i)" and
    "i < length ys"
    by (metis \<open>ys' = _\<close> in_set_conv_nth length_map nth_map)

  hence "f (ys ! i) = Some (ys' ! i)"
    using \<open>set ys \<subseteq> _\<close>
    by (metis IntD2 Int_absorb2 comp_apply domD nth_mem option.sel)

  thus False
    using Inj \<open>b = _\<close> \<open>i < _\<close>    
    by (metis \<open>a \<notin> _\<close> \<open>f a = Some b\<close> domIff inj_on_contraD nth_mem option.distinct(1))
qed

definition map_upd_set \<comment>\<open>make this a definition?\<close>
  where "map_upd_set A B f \<equiv> A ++ (\<lambda>x. if x \<in> B then Some (f x) else None)"

lemma map_upd_set_dom:
  shows "dom (map_upd_set m B f) = dom m \<union> B"
  by (auto simp: map_upd_set_def)

lemma map_upd_set_subset:
  assumes "B' \<subseteq> B" and "B \<inter> dom A = {}"
  shows "map_upd_set A B' f \<subseteq>\<^sub>m map_upd_set A B f"
  unfolding map_le_def map_upd_set_def
  by (smt (z3) Diff_Diff_Int Diff_iff assms(1) assms(2) domIff empty_iff map_add_None map_add_def subsetD)

lemma map_upd_set_subset2:
  assumes "dom A \<inter> B = {}"
  shows "A \<subseteq>\<^sub>m map_upd_set A B f"
  unfolding map_upd_set_def
  by (smt (verit) assms disjoint_iff domIff map_add_dom_app_simps(3) map_le_def)

lemma map_upd_set_lookup_1:
  assumes "x \<in> B"
  shows "map_upd_set A B f x = Some (f x)"
  using assms
  by (simp add: map_upd_set_def)

lemma map_upd_set_lookup_2:
  assumes "x \<notin> B"
  shows "map_upd_set A B f x = A x"
  using assms
  unfolding map_upd_set_def
  by (simp add: map_add_def)

subsection \<open>Strictly Ordered Lists\<close>

\<comment>\<open>TODO: the passification metatheory contains a more specific version of this --> move this to 
  a theory in Boogie proof gen and then reuse the definitions in the passification metatheory\<close>

lemma distinct_helper: \<comment>\<open>copied from passification metatheory --> TODO: merge\<close>
  assumes A1:"(x, fx) \<in> set xs" and 
          A2:"(y, fy) \<in> set xs" and
          "x \<noteq> y"
          "distinct (map snd xs)"
        shows "fx \<noteq> fy"  
proof -
  thm distinct_conv_nth
  from A1 obtain i where "i < length xs" and  "xs ! i = (x, fx)"
    by (meson in_set_conv_nth)
  moreover from A2 obtain j where "j < length xs" and "xs ! j = (y, fy)"
    by (meson in_set_conv_nth)
  ultimately show ?thesis using \<open>x \<noteq> y\<close> \<open>distinct (map snd xs)\<close> distinct_conv_nth
    by (metis eq_snd_iff length_map nth_map prod.inject)
qed

fun strictly_ordered_list :: "('a :: linorder) list \<Rightarrow> bool"
  where 
    "strictly_ordered_list [] = True"
  | "strictly_ordered_list [x] = True"
  | "strictly_ordered_list (x#y#zs) = (x < y \<and> strictly_ordered_list (y#zs))"

lemma strictly_ordered_list_smaller: "strictly_ordered_list (a#xs) \<Longrightarrow> (\<forall> b \<in> (set xs).a < b)"
  by (induction arbitrary:a rule: strictly_ordered_list.induct) auto

lemma strictly_ordered_list_distinct: "strictly_ordered_list xs \<Longrightarrow> distinct xs"
proof (induction rule: strictly_ordered_list.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y zs)
  then show ?case 
    by (meson distinct.simps(2) less_imp_neq strictly_ordered_list.simps(3) strictly_ordered_list_smaller)
qed

lemma strictly_ordered_list_inj:
  assumes "strictly_ordered_list (map snd xs)"
  shows "inj_on (map_of xs) (dom (map_of xs))"
  unfolding inj_on_def
proof clarify
  fix x0 y0 x1 y1
  assume "map_of xs x0 = Some y0" and
         "map_of xs x1 = Some y1" and
         "map_of xs x0 = map_of xs x1"

  thus "x0 = x1"
    using assms
    by (metis distinct_helper map_of_SomeD strictly_ordered_list_distinct)
qed

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