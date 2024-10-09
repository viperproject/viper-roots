theory VHelper imports Main begin

section \<open>Viktor's basic lemmas\<close>

text \<open> 
  This section contains many trivial theorems mostly for doing
  unification-based forward reasoning.
\<close>

text \<open> (Adapted to Isabelle 2016-1 by Qin Yu and James Brotherston) \<close>

lemma allD: " \<lbrakk> \<forall>a. P a \<rbrakk> \<Longrightarrow> P a" by (erule allE)+
lemma all2D: " \<lbrakk> \<forall>a b. P a b \<rbrakk> \<Longrightarrow> P a b" by (erule allE)+
lemma all3D: " \<lbrakk> \<forall>a b c. P a b c \<rbrakk> \<Longrightarrow> P a b c" by (erule allE)+
lemma all4D: " \<lbrakk> \<forall>a b c d. P a b c d \<rbrakk> \<Longrightarrow> P a b c d" by (erule allE)+
lemma all5D: " \<lbrakk> \<forall>a b c d e. P a b c d e \<rbrakk> \<Longrightarrow> P a b c d e" by (erule allE)+

lemmas impD = mp
lemma all_impD: "\<lbrakk> \<forall>a. P a \<longrightarrow> Q a; P a \<rbrakk>\<Longrightarrow> Q a"  by (drule allD mp)+
lemma all2_impD: "\<lbrakk> \<forall>a b. P a b \<longrightarrow> Q a b; P a b \<rbrakk>\<Longrightarrow> Q a b"  by (drule allD mp)+
lemma all3_impD: "\<lbrakk> \<forall>a b c. P a b c \<longrightarrow> Q a b c; P a b c \<rbrakk>\<Longrightarrow> Q a b c"  by (drule allD mp)+
lemma all4_impD: "\<lbrakk> \<forall>a b c d. P a b c d \<longrightarrow> Q a b c d; P a b c d \<rbrakk>\<Longrightarrow> Q a b c d"  by (drule allD mp)+
lemma all5_impD: "\<lbrakk> \<forall>a b c d e. P a b c d e \<longrightarrow> Q a b c d e; P a b c d e \<rbrakk>\<Longrightarrow> Q a b c d e"  by (drule allD mp)+

lemma imp2D: "\<lbrakk> P \<longrightarrow> Q \<longrightarrow> R; P; Q \<rbrakk> \<Longrightarrow> R" by (drule (1) mp)+ 
lemma all_imp2D: "\<lbrakk> \<forall>a. P a \<longrightarrow> Q a \<longrightarrow> R a; P a; Q a \<rbrakk>\<Longrightarrow> R a"  by (drule allD | drule (1) mp)+
lemma all2_imp2D: "\<lbrakk> \<forall>a b. P a b \<longrightarrow> Q a b \<longrightarrow> R a b; P a b; Q a b \<rbrakk>\<Longrightarrow> R a b"  by (drule allD | drule (1) mp)+
lemma all3_imp2D: "\<lbrakk> \<forall>a b c. P a b c \<longrightarrow> Q a b c \<longrightarrow> R a b c; P a b c; Q a b c \<rbrakk>\<Longrightarrow> R a b c"  by (drule allD | drule (1) mp)+
lemma all4_imp2D: "\<lbrakk> \<forall>a b c d. P a b c d \<longrightarrow> Q a b c d \<longrightarrow> R a b c d; P a b c d; Q a b c d \<rbrakk>\<Longrightarrow> R a b c d"  by (drule allD | drule (1) mp)+
lemma all5_imp2D: "\<lbrakk> \<forall>a b c d e. P a b c d e \<longrightarrow> Q a b c d e \<longrightarrow> R a b c d e; P a b c d e; Q a b c d e \<rbrakk>\<Longrightarrow> R a b c d e"  by (drule allD | drule (1) mp)+

lemma imp3D: "\<lbrakk> P \<longrightarrow> Q \<longrightarrow> R \<longrightarrow> S; P; Q; R \<rbrakk> \<Longrightarrow> S" by (drule (1) mp)+ 
lemma imp4D: "\<lbrakk> P \<longrightarrow> Q \<longrightarrow> R \<longrightarrow> S \<longrightarrow> T; P; Q; R; S \<rbrakk> \<Longrightarrow> T" by (drule (1) mp)+ 
lemma imp5D: "\<lbrakk> P \<longrightarrow> Q \<longrightarrow> R \<longrightarrow> S \<longrightarrow> T \<longrightarrow> U; P; Q; R; S; T \<rbrakk> \<Longrightarrow> U" by (drule (1) mp)+ 

lemma mallD: "\<lbrakk>\<And>a. PROP P a \<rbrakk> \<Longrightarrow> PROP P a" .
lemma mall2D: "\<lbrakk>\<And>a b. PROP P a b \<rbrakk> \<Longrightarrow> PROP P a b" .
lemma mall3D: "\<lbrakk>\<And>a b c. PROP P a b c \<rbrakk> \<Longrightarrow> PROP P a b c" .
lemma mall4D: "\<lbrakk>\<And>a b c d. PROP P a b c d \<rbrakk> \<Longrightarrow> PROP P a b c d" .
lemma mall5D: "\<lbrakk>\<And>a b c d e. PROP P a b c d e \<rbrakk> \<Longrightarrow> PROP P a b c d e" .

lemma mimpD: "\<lbrakk>PROP P \<Longrightarrow> PROP Q; PROP P \<rbrakk> \<Longrightarrow> PROP Q".
lemma mall_impD: "\<lbrakk>\<And>a. PROP P a \<Longrightarrow> PROP Q a; PROP P a \<rbrakk> \<Longrightarrow> PROP Q a" .
lemma mall2_impD: "\<lbrakk>\<And>a b. PROP P a b \<Longrightarrow> PROP Q a b; PROP P a b \<rbrakk> \<Longrightarrow> PROP Q a b" .
lemma mall3_impD: "\<lbrakk>\<And>a b c. PROP P a b c \<Longrightarrow> PROP Q a b c; PROP P a b c \<rbrakk> \<Longrightarrow> PROP Q a b c" .
lemma mall4_impD: "\<lbrakk>\<And>a b c d. PROP P a b c d \<Longrightarrow> PROP Q a b c d; PROP P a b c d \<rbrakk> \<Longrightarrow> PROP Q a b c d" .
lemma mall5_impD: "\<lbrakk>\<And>a b c d e. PROP P a b c d e \<Longrightarrow> PROP Q a b c d e; PROP P a b c d e \<rbrakk> \<Longrightarrow> PROP Q a b c d e" .

lemma mimp2D: "\<lbrakk>PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R; PROP P; PROP Q \<rbrakk> \<Longrightarrow> PROP R".
lemma mall_imp2D: "\<lbrakk>\<And>a. PROP P a \<Longrightarrow> PROP Q a \<Longrightarrow> PROP R a; PROP P a; PROP Q a \<rbrakk> \<Longrightarrow> PROP R a" .
lemma mall2_imp2D: "\<lbrakk>\<And>a b. PROP P a b \<Longrightarrow> PROP Q a b \<Longrightarrow> PROP R a b; PROP P a b; PROP Q a b \<rbrakk> \<Longrightarrow> PROP R a b" .
lemma mall3_imp2D: "\<lbrakk>\<And>a b c. PROP P a b c \<Longrightarrow> PROP Q a b c \<Longrightarrow> PROP R a b c; PROP P a b c; PROP Q a b c \<rbrakk> \<Longrightarrow> PROP R a b c" .
lemma mall4_imp2D: "\<lbrakk>\<And>a b c d. PROP P a b c d \<Longrightarrow> PROP Q a b c d \<Longrightarrow> PROP R a b c d; PROP P a b c d; PROP Q a b c d \<rbrakk> \<Longrightarrow> PROP R a b c d" .
lemma mall5_imp2D: "\<lbrakk>\<And>a b c d e. PROP P a b c d e \<Longrightarrow> PROP Q a b c d e \<Longrightarrow> PROP R a b c d e; PROP P a b c d e; PROP Q a b c d e \<rbrakk> \<Longrightarrow> PROP R a b c d e".

lemma mimp3D: "\<lbrakk>PROP P \<Longrightarrow> PROP Q \<Longrightarrow> PROP R \<Longrightarrow> PROP S; PROP P; PROP Q; PROP R \<rbrakk> \<Longrightarrow> PROP S".
lemma mimp4D: "\<lbrakk>\<lbrakk>PROP P; PROP Q; PROP R; PROP S\<rbrakk> \<Longrightarrow> PROP T; PROP P; PROP Q; PROP R; PROP S \<rbrakk> \<Longrightarrow> PROP T".
lemma mimp5D: "\<lbrakk>\<lbrakk>PROP P; PROP Q; PROP R; PROP S; PROP T\<rbrakk> \<Longrightarrow> PROP U; PROP P; PROP Q; PROP R; PROP S; PROP T \<rbrakk> \<Longrightarrow> PROP U".

lemma ex2I: "P x y \<Longrightarrow> \<exists>x y. P x y" by (rule exI)+ 
lemma ex3I: "P x y z \<Longrightarrow> \<exists>x y z. P x y z" by (rule exI)+ 

text \<open> Every HOL type is inhabited. \<close>

definition 
  default_value :: "'a"
where 
  "default_value \<equiv> \<some>x. True"


subsubsection \<open> Formalization of disjointness \<close>

definition disjoint :: "('a set) \<Rightarrow> ('a set) \<Rightarrow> bool" 
where "disjoint h1 h2 = (h1 \<inter> h2 = {})"

lemma disjoint_simps[simp]:
 "disjoint {} x"
 "disjoint x {}"
 "disjoint (x \<union> y) z = (disjoint x z \<and> disjoint y z)"
 "disjoint x (y \<union> z) = (disjoint x y \<and> disjoint x z)"
unfolding disjoint_def by auto

lemma disjoint_search[elim]: 
  "disjoint y x \<Longrightarrow> disjoint x y"
  "\<lbrakk>disjoint z y; x \<subseteq> z\<rbrakk> \<Longrightarrow> disjoint x y"
  "\<lbrakk>disjoint y z; x \<subseteq> z\<rbrakk> \<Longrightarrow> disjoint x y"
  "\<lbrakk>disjoint x z; y \<subseteq> z\<rbrakk> \<Longrightarrow> disjoint x y"
  "\<lbrakk>disjoint z x; y \<subseteq> z\<rbrakk> \<Longrightarrow> disjoint x y"
unfolding disjoint_def by auto

lemma disjoint_commute: "disjoint y x = disjoint x y"
unfolding disjoint_def by auto

lemma map_add_commute: "disjoint (dom x) (dom y) \<Longrightarrow> y ++ x = x ++ y"
unfolding disjoint_def by (auto intro: map_add_comm)

declare map_add_assoc [simp del]

lemma map_add_left_commute: 
  "\<lbrakk> disjoint (dom a) (dom c); disjoint (dom a) (dom b) \<rbrakk> \<Longrightarrow> b ++ (a ++ c) = a ++ (b ++ c)"
by (subst map_add_assoc, subst map_add_commute, simp_all add: map_add_assoc)

lemmas 
  hsimps = disjoint_commute map_add_commute map_add_left_commute 
           map_add_assoc [THEN sym]

lemma map_add_cancel:
   "\<lbrakk> g ++ f = h ++ f; disjoint (dom g) (dom f); disjoint (dom h) (dom f) \<rbrakk> \<Longrightarrow> g = h"
apply (rule ext, drule_tac x=x in fun_cong, clarsimp simp add: map_add_def disjoint_def split: option.splits)
apply ((drule_tac f="\<lambda>S. x \<in> S" in arg_cong, clarsimp)+, case_tac "h x", auto)
done

lemma dom_eqD: "\<lbrakk> dom m = X; x \<notin> X \<rbrakk> \<Longrightarrow> m x = None" by auto

lemma map_add_del[simp]: "(f ++ g) (x := None) = f(x := None) ++ g(x := None)"
by (rule ext, auto split: option.splits simp add: map_add_def)

lemma disjoint_del[simp]: "disjoint {x} (dom f) \<Longrightarrow> f(x := None) = f"
by (rule ext, auto simp add: disjoint_def)

subsubsection \<open> Formalization of equality on subset of domain \<close>

definition 
  agrees :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
where
  "agrees X s s' \<equiv> \<forall>x \<in> X. s x = s' x"

lemma agrees_simps[simp]: 
  "agrees {} s s'"
  "agrees {x} s s' = (s x = s' x)"
  "agrees (insert x X) s s' = (s x = s' x \<and> agrees X s s')"
  "agrees (X \<union> Y) s s' = (agrees X s s' \<and> agrees Y s s')"
unfolding agrees_def by auto

lemma agrees_refl: "agrees X s s"
by (simp add: agrees_def)

lemma agreesC: 
  "agrees X x y = agrees X y x"
unfolding agrees_def by auto

lemma agrees_search[elim]: 
  "agrees X x y \<Longrightarrow> agrees X y x"
  "\<lbrakk>agrees X x y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> agrees Y x y"
  "\<lbrakk>agrees X x y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> agrees Y y x"
  "\<lbrakk>a \<notin> X \<rbrakk> \<Longrightarrow> agrees X x (x(a:=b))"
unfolding agrees_def by auto

lemma agrees_minusD[elim]:
  "agrees (-X) x y \<Longrightarrow> disjoint X Y \<Longrightarrow> agrees Y x y"
by (auto simp add: agrees_def disjoint_def)


subsubsection \<open> Formalization of list difference \<close>

primrec
  list_minus :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_minus l []       = l"
| "list_minus l (x # xs) = removeAll x (list_minus l xs)" 

lemma removeAllC: "removeAll y (removeAll x z) = removeAll x (removeAll y z)"
by (induct z, auto)

lemma remove1_removeAll: "remove1 y (removeAll x z) = removeAll x (remove1 y z)"
by (induct z, auto, simp add: remove1_idem)

lemma list_minus_removeAll: "list_minus (removeAll a x) y = removeAll a (list_minus x y)" 
by (induct y, simp_all add: removeAllC)

lemma list_minus_removeAll2:
  "list_minus (removeAll a x) (removeAll a y) = removeAll a (list_minus x y)" 
by (induct y, simp, clarsimp simp add: removeAllC) 

lemma list_minus_remove1: "list_minus (remove1 a x) y = remove1 a (list_minus x y)" 
by (induct y, simp_all add: removeAllC remove1_removeAll)

lemma list_minus_app: "list_minus x (y @ z) = list_minus (list_minus x y) z"
by (induct y, simp_all add: list_minus_removeAll)

lemma list_minusC: "list_minus (list_minus x z) y = list_minus (list_minus x y) z"
by (induct y, simp_all add: list_minus_removeAll)

lemma list_minus1:
  "disjoint (set x) (set z) \<Longrightarrow> list_minus (x @ list_minus z w) z = x"
apply (induct z arbitrary: w, simp_all, induct_tac w, simp_all)
apply (subst list_minus_removeAll [THEN sym], simp_all)
apply (erule_tac x="a # w" in meta_allE, drule mimpD, fast)
apply (subst removeAll_id, simp add: disjoint_def, simp)
apply (simp add: list_minus_removeAll [THEN sym])
done

lemma list_minus2:
  "disjoint (set z) (set x) \<Longrightarrow> list_minus (list_minus z w @ x) z = x"
apply (induct z arbitrary: w, simp_all)
 apply (induct_tac w, simp_all)
apply (subst list_minus_removeAll [THEN sym], simp_all)
apply (erule_tac x="a # w" in meta_allE, drule mimpD, fast)
apply (subst removeAll_id, simp add: disjoint_def, simp)
apply (simp add: list_minus_removeAll [THEN sym])
done

lemma list_minus_appr:
  "disjoint (set x) (set z) \<Longrightarrow> list_minus (x @ z) (y @ z) = list_minus x y"
by (induct y arbitrary: x, simp_all, erule list_minus1 [where w="[]", simplified])

lemma list_minus_appl:
  "disjoint (set z) (set x) \<Longrightarrow> list_minus (z @ x) (z @ y) = list_minus x y"
by (simp add: list_minus_app list_minus2 [where w="[]", simplified])

lemma set_list_minus[simp]:
  "set (list_minus x y) = set x - set y"
by (induct y arbitrary: x, auto)

lemma list_minus_removeAll_irr: 
  "a \<notin> set x \<Longrightarrow> list_minus x (removeAll a y) = list_minus x y" 
by (induct y, simp_all add: removeAllC, clarify)
   (subst list_minus_removeAll2 [THEN sym], simp)

end
