theory SepAlgebra
  imports SepAlgebraDef
begin

section \<open>Instantiations of PCMs\<close>

subsection \<open>Product\<close>

instantiation prod :: (pcm, pcm) pcm
begin

definition plus_prod where "plus_prod a b = (let x = fst a \<oplus> fst b in let y = snd a \<oplus> snd b in
  if x = None \<or> y = None then None else Some (the x, the y))"

lemma plus_prodIAlt:
  assumes "Some x = fst a \<oplus> fst b"
      and "Some y = snd a \<oplus> snd b"
    shows "a \<oplus> b = Some (x, y)"
proof -
  have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    using assms(1) assms(2) option.discI[of "fst a \<oplus> fst b" x] option.discI[of "snd a \<oplus> snd b" y] plus_prod_def[of a b]    
    by presburger
  then show ?thesis
    by (metis assms(1) assms(2) option.sel)
qed

lemma plus_prodI:
  assumes "Some (fst x) = fst a \<oplus> fst b"
      and "Some (snd x) = snd a \<oplus> snd b"
    shows "Some x = a \<oplus> b"
proof -
  have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    using assms(1) assms(2) option.discI[of "fst a \<oplus> fst b" "fst x"] option.discI[of "snd a \<oplus> snd b" "snd x"] plus_prod_def[of a b]    
    by presburger
  then show ?thesis
    by (metis assms(1) assms(2) option.sel prod.collapse)
qed

lemma plus_prodE:
  assumes "a \<oplus> b = Some x"
  shows "fst a \<oplus> fst b = Some (fst x) \<and> snd a \<oplus> snd b = Some (snd x)"
proof -
  have "fst a \<oplus> fst b \<noteq> None \<and> snd a \<oplus> snd b \<noteq> None"
    using assms option.discI plus_prod_def[of a b] by fastforce
  then have "a \<oplus> b = Some (the (fst a \<oplus> fst b), the (snd a \<oplus> snd b))"
    by (simp add: plus_prodIAlt)
  then show ?thesis
    by (simp add: \<open>fst a \<oplus> fst b \<noteq> None \<and> snd a \<oplus> snd b \<noteq> None\<close> assms)
qed

instance proof
  fix a b c ab bc :: "'a :: pcm \<times> 'b :: pcm"
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative plus_prod_def)
  assume "a \<oplus> b = Some ab \<and> b \<oplus> c = None"
  show "ab \<oplus> c = None"
  proof (cases "fst b \<oplus> fst c")
    case None
    then show ?thesis
      by (metis (mono_tags, opaque_lifting) \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> asso2 option.exhaust option.simps(3) plus_prodE)
  next
    case (Some aa)
    then have "snd b \<oplus> snd c = None"
      by (metis \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> option.distinct(1) option.exhaust plus_prodIAlt)
    then show ?thesis
      by (metis (mono_tags, opaque_lifting) \<open>a \<oplus> b = Some ab \<and> b \<oplus> c = None\<close> asso2 not_None_eq plus_prodE)
  qed
next
  fix a b c ab bc :: "'a :: pcm \<times> 'b :: pcm"
  assume "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
  then have "fst a \<oplus> fst b = Some (fst ab) \<and> fst b \<oplus> fst c = Some (fst bc) \<and> snd a \<oplus> snd b = Some (snd ab) \<and> snd b \<oplus> snd c = Some (snd bc)"
    using plus_prodE by blast
  then have "fst ab \<oplus> fst c = fst a \<oplus> fst bc \<and> snd ab \<oplus> snd c = snd a \<oplus> snd bc"
    by (meson asso1)
  then show "ab \<oplus> c = a \<oplus> bc"
    by (simp add: plus_prod_def)
next
  fix a b c :: "'a :: pcm \<times> 'b :: pcm"

  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "Some (fst a) = fst a \<oplus> fst a \<and> Some (snd a) = snd a \<oplus> snd a"
    using plus_prodE[of a b] plus_prodE[of c c] positivity
    by metis
  then show "Some a = a \<oplus> a"
    using plus_prodIAlt by fastforce
qed


lemma greater_prod_eq:
  "x \<succeq> y \<longleftrightarrow> (fst x \<succeq> fst y) \<and> (snd x \<succeq> snd y)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain r where "Some x = y \<oplus> r"
    using greater_def by blast
  then have "Some (fst x) = fst y \<oplus> fst r \<and> Some (snd x) = snd y \<oplus> snd r"
    by (metis SepAlgebra.plus_prodE)
  then show ?B
    by (meson greater_def)
next
  assume ?B
  then obtain r1 r2 where "Some (fst x) = fst y \<oplus> r1 \<and> Some (snd x) = snd y \<oplus> r2"
    by (meson greater_def)
  then have "Some x = y \<oplus> (r1, r2)"
    using SepAlgebra.plus_prodIAlt by fastforce
  then show ?A
    using greater_def by auto
qed

lemma greater_prodI:
  assumes "fst x \<succeq> fst y"
      and "snd x \<succeq> snd y"
    shows "x \<succeq> y"
  by (simp add: assms(1) assms(2) greater_prod_eq)

lemma comp_prod:
  "a ## b \<longleftrightarrow> (fst a ## fst b \<and> snd a ## snd b)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain x where "Some x = a \<oplus> b"
    by (metis defined_def not_Some_eq)
  then have "Some (fst x) = fst a \<oplus> fst b \<and> Some (snd x) = snd a \<oplus> snd b"
    by (metis SepAlgebra.plus_prodE)
  then show ?B
    by (metis defined_def option.discI)
next
  assume ?B
  then obtain r1 r2 where "Some r1 = fst a \<oplus> fst b \<and> Some r2 = snd a \<oplus> snd b"
    by (metis defined_def option.exhaust_sel)
  then show ?A
    using defined_def SepAlgebra.plus_prodIAlt by fastforce
qed    

lemma compatible_prodI:
  assumes "fst a ## fst b"
      and "snd a ## snd b"
    shows "a ## b"
  using assms(1) assms(2) comp_prod by blast

end

subsection \<open>Function\<close>

datatype 'v agreement = Ag (the_ag: 'v)


instantiation agreement :: (type) pcm
begin

definition plus_agreement :: "'a agreement \<Rightarrow> 'a agreement \<Rightarrow> 'a agreement option" where
  "plus_agreement a b = (if a = b then Some a else None)"

lemma plus_AgI:
  fixes \<omega> :: "'v agreement"
  assumes "\<omega> = a"
      and "\<omega> = b"
    shows "Some \<omega> = a \<oplus> b"
  by (metis SepAlgebra.plus_agreement_def assms(1) assms(2))

instance proof
  fix a b c ab bc :: "'a agreement"
  show "a \<oplus> b = b \<oplus> a"
    using plus_agreement_def by presburger
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (metis option.sel plus_agreement_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (metis option.sel plus_agreement_def)
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a "
    by (metis plus_agreement_def)
qed

lemma greater_Ag:
  fixes a b :: "'a agreement"
  shows "a \<succeq> b \<longleftrightarrow> a = b"
  by (simp add: SepAlgebra.plus_agreement_def greater_def)

lemma plus_AgE:
  fixes \<omega> :: "'v agreement"
  assumes "Some \<omega> = a \<oplus> b"
  shows "the_ag \<omega> = the_ag a \<and> the_ag \<omega> = the_ag b"
  by (metis SepAlgebra.plus_agreement_def assms option.discI option.sel)

end


instantiation preal :: pcm
begin

definition plus_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal option" where
  "plus_preal a b = Some (a + b)"

lemma preal_plus_iff :
  "Some (z :: preal) = x \<oplus> y \<longleftrightarrow> z = x + y"
  using SepAlgebra.plus_preal_def by auto

instance proof
  fix a b c ab bc :: preal
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: plus_preal_def add.commute)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    using plus_preal_def add.assoc by force
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (simp add: plus_preal_def)
  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "c = 0"
    by (metis (no_types, opaque_lifting) PosReal.padd_cancellative plus_preal_def add_0 option.sel)
  then show "Some a = a \<oplus> a"
    by (metis plus_preal_def \<open>a \<oplus> b = Some c\<close> add.commute add.right_neutral nle_le option.inject pos_perm_class.sum_larger)
qed

lemma preal_plusE:
  assumes "Some (x :: preal) = a \<oplus> b"
  shows "x = a + b"
  using assms preal_plus_iff by auto

end

instantiation prat :: pcm
begin

definition plus_prat :: "prat \<Rightarrow> prat \<Rightarrow> prat option" where
  "plus_prat a b = Some (a + b)"

instance proof
  fix a b c ab bc :: prat
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: plus_prat_def add.commute)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    using plus_prat_def add.assoc by force
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (simp add: plus_prat_def)
  assume "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "c = 0"
    by (metis Rep_prat_inject plus_prat_def add_cancel_right_right option.sel plus_prat.rep_eq zero_prat.rep_eq)
  then show "Some a = a \<oplus> a"
    by (metis PosRat.pgte.rep_eq PosRat.sum_larger Rep_prat_inject plus_prat_def \<open>a \<oplus> b = Some c\<close> add_0 nle_le option.inject)
qed

end



instantiation "fun" :: (type, pcm) pcm
begin

definition compatible_fun where
  "compatible_fun a b \<longleftrightarrow> (\<forall>l. a l \<oplus> b l \<noteq> None)"

lemma compatible_funI:
  assumes "\<And>l. a l \<oplus> b l \<noteq> None"
  shows "compatible_fun a b"
  by (simp add: assms compatible_fun_def)

lemma compatible_funE:
  assumes "compatible_fun a b"
  shows "a l \<oplus> b l \<noteq> None"
  by (meson assms compatible_fun_def)

definition plus_fun where
  "plus_fun a b = (if compatible_fun a b then Some (\<lambda>l. the (a l \<oplus> b l)) else None)"

lemma plus_funI:
  assumes "\<And>l. Some (x l) = a l \<oplus> b l"
    shows "Some x = a \<oplus> b"
proof -
  obtain ab where "Some ab = a \<oplus> b"
    by (metis assms compatible_fun_def option.discI plus_fun_def)
  moreover have "ab = x"
  proof (rule ext)
    fix l show "ab l = x l"
      by (metis (mono_tags, lifting) assms calculation option.discI option.sel plus_fun_def)
  qed
  ultimately show ?thesis
    by auto
qed

lemma plus_funE:
  assumes "Some x = a \<oplus> b"
  shows "Some (x l) = a l \<oplus> b l"
  by (metis (no_types, lifting) assms compatible_funE option.discI option.exhaust_sel option.sel plus_fun_def)

lemma fun_plus_iff :
  "Some z = x \<oplus> y \<longleftrightarrow> (\<forall> l. Some (z l) = x l \<oplus> y l)"
  by (meson plus_funE plus_funI)

instance proof

  fix a b c ab bc :: "'a \<Rightarrow> 'b :: pcm"
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative compatible_fun_def plus_fun_def)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  proof -
    assume asm0: "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
    show "ab \<oplus> c = a \<oplus> bc"
    proof (cases "ab \<oplus> c")
      case None
      then obtain l where "ab l \<oplus> c l = None"
        by (metis compatible_fun_def option.discI plus_fun_def)
      then have "a l \<oplus> bc l = None"
        using plus_funE[of ab a b] plus_funE[of bc b c] asm0 asso1
        by metis
      then show ?thesis
        by (metis None compatible_fun_def plus_fun_def)
    next
      case (Some f)
      have "compatible_fun a bc"
      proof (rule compatible_funI)
        fix l
        have "ab l \<oplus> c l \<noteq> None"
          by (metis Some compatible_funE option.discI plus_fun_def)
        then show "a l \<oplus> bc l \<noteq> None"
          using asso1[of "a l" "b l" "ab l" "c l" "bc l"]
          by (metis asm0 plus_funE)
      qed
      then obtain f' where "Some f' = a \<oplus> bc"
        by (simp add: plus_fun_def)
      moreover have "f = f'"
      proof (rule ext)
        fix l 
        have "ab l \<oplus> c l = a l \<oplus> bc l"
          using asso1[of "a l" "b l" "ab l" "c l" "bc l"]
          by (metis plus_funE asm0)
        then show "f l = f' l"
          by (metis (no_types, lifting) Some calculation option.discI option.sel plus_fun_def)
      qed
      ultimately show ?thesis
        using Some by force
    qed
  qed
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    by (metis (mono_tags, lifting) asso2 compatible_fun_def option.discI option.exhaust_sel option.sel plus_fun_def)

  assume asm0: "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  have "compatible_fun a a"
  proof (rule compatible_funI)
    fix l show "a l \<oplus> a l \<noteq> None"
      using asm0(1) asm0(2) asso2[of "b l" "a l" ]
        commutative[of "a l"] plus_fun_def[of c c] plus_fun_def[of a b]
      by (metis option.discI plus_funE)
  qed
  then obtain aa where "Some aa = a \<oplus> a"
    by (simp add: plus_fun_def)
  moreover have "aa = a"
  proof (rule ext)
    fix l show "aa l = a l"
      by (metis (mono_tags, lifting) asm0(1) asm0(2) calculation compatible_fun_def option.discI option.exhaust_sel option.sel plus_fun_def positivity)
  qed
  ultimately show "Some a = a \<oplus> a" by simp
qed

lemma greaterI:
  fixes a :: "'a \<Rightarrow> 'b"
  assumes "\<And>l. a l \<succeq> b l"
  shows "a \<succeq> b"
proof -
  let ?r = "\<lambda>l. SOME r. Some (a l) = b l \<oplus> r"
  have "Some a = b \<oplus> ?r"
  proof (rule plus_funI)
    fix l
    show "Some (a l) = b l \<oplus> ?r l"
      using someI_ex assms greater_def by fast
  qed
  then show ?thesis
    using greater_def by blast
qed

lemma greaterE:
  assumes "a \<succeq> b"
  shows "a l \<succeq> b l"
  by (meson SepAlgebra.plus_funE assms greater_def)

lemma fun_greater_iff :
  "f \<succeq> g \<longleftrightarrow> (\<forall> x. f x \<succeq> g x)"
  using SepAlgebra.greaterI greaterE by metis

end

subsection \<open>Option\<close>

instantiation option :: (pcm) pcm
begin

fun plus_option where
  "plus_option None x = Some x"
| "plus_option x None = Some x"
| "plus_option (Some a) (Some b) = (let r = a \<oplus> b in if r = None then None else Some r)"

lemma plus_optionI:
  assumes "x = Some xx"
      and "y = Some yy"
      and "Some a = xx \<oplus> yy"
    shows "Some (Some a) = x \<oplus> y"
  using assms(1) assms(2) assms(3) option.discI by fastforce

lemma plus_option_Some_None:
  "Some x \<oplus> Some y = None \<longleftrightarrow> x \<oplus> y = None"
  using option.discI by fastforce

lemma plus_optionE:
  assumes "x = Some xx"
      and "a = Some aa"
      and "b = Some bb"
      and "Some x = a \<oplus> b"
    shows "Some xx = aa \<oplus> bb"
  using plus_option.simps(3)[of aa bb]
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) option.discI option.inject)

lemma option_plus_None_r [simp] :
  "Some z = x \<oplus> None \<longleftrightarrow> z = x"
  by (cases "x"; simp)

instance proof
  fix a b c ab bc :: "('a :: pcm) option"

  show "a \<oplus> b = b \<oplus> a"
    apply (cases a)
    apply (metis option.discI plus_option.elims)
    by (metis commutative option.exhaust plus_option.simps(1) plus_option.simps(2) plus_option.simps(3))

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    apply (cases a; cases b; cases c)
           apply simp_all
       apply fastforce+
     apply (cases ab)
        apply force
       apply force
    apply (cases ab; cases bc)
    apply (metis (mono_tags) option.discI option.inject)
    apply (metis (mono_tags, lifting) option.discI option.inject)
     apply (metis (mono_tags, lifting) option.discI option.inject)
  proof -
    fix a' b' c' ab' bc'
    assume "(let r = a' \<oplus> b' in if r = None then None else Some r) = Some ab \<and>
       (let r = b' \<oplus> c' in if r = None then None else Some r) = Some bc"
      "a = Some a'" "b = Some b'" "c = Some c'" "ab = Some ab'" "bc = Some bc'"
    then have "ab' \<oplus> c' = a' \<oplus> bc'"
      using asso1[of a' b' ab' c' bc']
      by (metis (mono_tags, lifting) option.discI option.inject)
    then show "ab \<oplus> Some c' = Some a' \<oplus> bc"
      by (simp add: \<open>ab = Some ab'\<close> \<open>bc = Some bc'\<close>)
  qed
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    apply (cases a; cases b; cases c; cases ab)
    apply auto[14]
    using option.discI option.sel plus_option.simps(3)[of "the a" "the b"]
    apply (metis (full_types))
    by (metis plus_option_Some_None asso2 plus_optionE)
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
    apply (cases a; cases b; cases c)
           apply auto[6]
     apply (metis plus_optionI plus_option_Some_None not_Some_eq option.inject)
    by (metis plus_optionE plus_optionI positivity)
qed

end


lemma compatible_partial_functions:
  fixes a :: "'a \<rightharpoonup> ('b :: pcm)"
  shows "a ## b \<longleftrightarrow> (\<forall>l xa xb. a l = Some xa \<and> b l = Some xb \<longrightarrow> xa ## xb)" (is "?A \<longleftrightarrow> ?B")
proof
  assume asm0: ?B
  have "compatible_fun a b"
  proof (rule compatible_funI)
    fix l show "a l \<oplus> b l \<noteq> None"
      apply (cases "a l")
      apply force
      apply (cases "b l")
      apply simp
      using asm0 defined_def by force
  qed
  then show ?A
    by (simp add: defined_def plus_fun_def)
next
  assume asm0: ?A
  show "\<forall>l xa xb. a l = Some xa \<and> b l = Some xb \<longrightarrow> xa ## xb"
  proof (clarify)
    fix l xa xb assume asm1: "a l = Some xa" "b l = Some xb"
    moreover have "a l \<oplus> b l \<noteq> None"
      by (meson asm0 compatible_fun_def defined_def plus_fun_def)
    ultimately show "xa ## xb"
      using defined_def by fastforce
  qed
qed

lemma compatible_partial_functions_singleton :
 "f ## [x \<mapsto> v] \<longleftrightarrow> (\<forall> v'. f x = Some v' \<longrightarrow> v' ## v)"
  by (simp add: compatible_partial_functions)

lemma result_sum_partial_functions:
  assumes "Some x = a \<oplus> b"
  shows "a l = None \<Longrightarrow> x l = b l"
    and "b l = None \<Longrightarrow> x l = a l"
    and "a l = Some va \<and> b l = Some vb \<Longrightarrow> x l = va \<oplus> vb"
    apply (metis (no_types, lifting) assms option.discI option.sel plus_fun_def plus_option.elims)

   apply (metis (mono_tags, opaque_lifting) assms commutative option.inject plus_funE plus_option.simps(1))
  using assms option.discI option.inject plus_funE[of x a b] plus_option.simps(3)[of va vb]
  by (metis (full_types))

(*
subsection \<open>Sum\<close>

instantiation sum :: (pcm, pcm) pcm
begin

fun plus_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> ('a + 'b) option" where
  "plus_sum (Inl a) (Inl b) = (let r = a \<oplus> b in if r = None then None else Some (Inl (the r)))"
| "plus_sum (Inr a) (Inr b) = (let r = a \<oplus> b in if r = None then None else Some (Inr (the r)))"
| "plus_sum _ _ = None"

instance proof

  fix a b c ab bc :: "('a :: pcm) + ('b :: pcm)"
  show "a \<oplus> b = b \<oplus> a"
    apply (cases a)
    apply (cases b)
      apply (simp_all add: commutative)
    apply (cases b)
     apply (simp_all add: commutative)
    done

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    apply (cases ab; cases bc)
    
       apply (cases bc)
    

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None" 
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
qed

end
*)



section \<open>Instantiations of PCMs with core\<close>

subsection \<open>Agreement\<close>

instantiation agreement :: (type) pcm_with_core
begin

definition core_agreement :: "'a agreement \<Rightarrow> 'a agreement" where
  "core_agreement x = x"

instance proof
  fix a b c x y :: "'a agreement"
  show "Some x = x \<oplus> |x|"
    by (simp add: core_agreement_def plus_agreement_def)
  show "Some |x| = |x| \<oplus> |x|"
    by (simp add: \<open>Some x = x \<oplus> |x|\<close> core_agreement_def)
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    using commutative core_agreement_def by auto
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    by (simp add: core_agreement_def)
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    using core_agreement_def by auto
qed

end


subsection \<open>Product\<close>

instantiation prod :: (pcm_with_core, pcm_with_core) pcm_with_core
begin

definition core_def: "|a| = ( |fst a|, |snd a| )"

instance proof
  fix x y a b c :: "'a :: pcm_with_core \<times> 'b :: pcm_with_core"

  show "Some a = a \<oplus> |a|"
    by (simp add: core_def core_is_smaller plus_prodIAlt)

  show "Some |a| = |a| \<oplus> |a|"
    by (metis (mono_tags, opaque_lifting) core_def plus_prodIAlt core_is_pure fst_eqD snd_eqD)

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
  proof -
    assume asm0: "Some x = x \<oplus> c"
    then obtain r1 r2 where "Some |fst x| = fst c \<oplus> r1" "Some |snd x| = snd c \<oplus> r2"
      by (metis core_max plus_prodE)
    then show "\<exists>r. Some |x| = c \<oplus> r"
      by (metis core_def fst_eqD plus_prodIAlt snd_conv)
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using plus_prodE[of a b c] core_def[of a] core_def[of b] core_def[of c]
      plus_prodIAlt[of "fst |c|" "|a|" "|b|"] core_sum eq_snd_iff  prod.sel(1) by metis
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis plus_prodE cancellative core_def prod.collapse prod.sel(1) prod.sel(2))
qed

end

subsection \<open>Function\<close>

instantiation "fun" :: (type, pcm_with_core) pcm_with_core
begin

definition core_fun: "core_fun f l = |f l|"

instance proof
  fix x y a b c :: "'a \<Rightarrow> 'b"
  show "Some x = x \<oplus> |x|"
  proof -
    have "compatible_fun x |x|"
    proof (rule compatible_funI)
      fix l show "x l \<oplus> |x| l \<noteq> None"
        by (simp add: core_fun core_is_smaller option.discI)
    qed
    then obtain xx where "Some xx = x \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = x"
    proof (rule ext)
      fix l show "xx l = x l"
        by (metis (mono_tags, lifting) \<open>compatible_fun x |x|\<close> calculation core_fun core_is_smaller option.sel plus_fun_def)
    qed
    ultimately show ?thesis by blast
  qed

  show "Some |x| = |x| \<oplus> |x|"
  proof -
    have "compatible_fun ( |x| ) |x|"
    proof (rule compatible_funI)
      fix l show "|x| l \<oplus> |x| l \<noteq> None"
        by (metis core_fun core_is_pure option.discI)
    qed
    then obtain xx where "Some xx = |x| \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = |x|"
    proof (rule ext)
      fix l show "xx l = |x| l"        
        by (metis (mono_tags, lifting) \<open>compatible_fun ( |x| ) |x|\<close> calculation core_fun core_is_pure option.sel plus_fun_def)
    qed
    ultimately show ?thesis by simp
  qed

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
  proof -
    assume asm0: "Some x = x \<oplus> c"
    have "compatible_fun c |x|"
    proof (rule compatible_funI)
      fix l show "c l \<oplus> |x| l \<noteq> None"
        by (metis (mono_tags, lifting) \<open>Some x = x \<oplus> |x|\<close> asm0 asso2 compatible_funE option.simps(3) plus_fun_def)
    qed
    then obtain xx where "Some xx = c \<oplus> |x|"
      by (simp add: plus_fun_def)
    moreover have "xx = |x|"
    proof (rule ext)
      fix l
      have "Some (x l) = (x l) \<oplus> (c l)"
        by (metis (mono_tags, lifting) asm0 compatible_funE option.discI option.expand option.sel plus_fun_def)
      then show "xx l = |x| l"
        using core_fun[of x l] core_is_pure[of "x l"] core_max[of "x l" "c l"]
         plus_fun_def[of c "|x|"] \<open>compatible_fun c |x|\<close> asso1[of "c l" _]
          calculation
          option.sel
          positivity[of _ _ "|x l|"]
        by metis
    qed
    ultimately show "\<exists>r. Some |x| = c \<oplus> r"
      by blast
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
  proof -
    assume asm0: "Some c = a \<oplus> b"
    have "compatible_fun ( |a| ) |b|"
    proof (rule compatible_funI)
      fix l 
      have "Some (c l) = a l \<oplus> b l"
        by (metis (mono_tags, lifting) asm0 compatible_funE option.discI option.exhaust_sel option.sel plus_fun_def)
      then show "|a| l \<oplus> |b| l \<noteq> None"
        by (metis core_fun core_sum is_none_simps(1) is_none_simps(2))
    qed
    then obtain x where "Some x = |a| \<oplus> |b|"
      by (simp add: plus_fun_def)
    moreover have "x = |c|"
    proof (rule ext)
      fix l 
      show "x l = |c| l"
        using asm0 calculation core_fun[of _ l] core_sum[of "c l" "a l" "b l"] option.sel plus_funE[of c a b] plus_funE[of x]
        by (metis (mono_tags))
    qed
    ultimately show "Some |c| = |a| \<oplus> |b|" by simp
  qed

  assume asm0: "Some a = b \<oplus> x" "Some a = b \<oplus> y" "|x| = |y|"
  show "x = y"
  proof (rule ext)
    fix l 
    have "Some (a l) = b l \<oplus> x l \<and> Some (a l) = b l \<oplus> y l \<and> |x l| = |y l|"
      by (metis (mono_tags, lifting) asm0(1) asm0(2) asm0(3) compatible_funE core_fun option.discI option.exhaust_sel option.sel plus_fun_def)
    then show "x l = y l"
      using cancellative by blast
  qed
qed

end

subsection \<open>Option\<close>

instantiation option :: (pcm_with_core) pcm_with_core
begin

fun core_option where
  "core_option None = None"
| "core_option (Some x) = Some |x|"

lemma core_option_None:
  "|x| = None \<longleftrightarrow> x = None"
  using core_option.elims by blast

lemma core_option_Some:
  "|x| \<noteq> None \<longleftrightarrow> x \<noteq> None"
  by (simp add: core_option_None)

instance proof
  fix x y a b c :: "'a option"
  show "Some x = x \<oplus> |x|"
    apply (cases x)    
     apply simp
    using core_is_smaller core_option.simps(2) plus_optionI by blast


  show "Some |x| = |x| \<oplus> |x|"
    apply (cases x)
     apply simp    
    using core_is_pure plus_optionI by fastforce


  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    apply (cases x)
    apply force
    apply (cases c)
     apply simp
    by (metis core_max core_option.simps(2) plus_optionE plus_optionI)

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    apply (cases a; cases b; cases c)
           apply auto[6]
     apply (metis option.distinct(1) option.exhaust_sel option.inject plus_optionI plus_option_Some_None)
  proof -
    fix a' b' c' assume "Some c = a \<oplus> b" "a = Some a'" "b = Some b'" "c = Some c'"
    then have "Some |c'| = |a'| \<oplus> |b'|"
      using core_sum plus_optionE by blast
    then show "Some |c| = |a| \<oplus> |b|"
      using \<open>a = Some a'\<close> \<open>b = Some b'\<close> \<open>c = Some c'\<close> plus_optionI by fastforce
  qed
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    apply (cases a; cases b; cases x; cases y)
                   apply auto[7]
            apply (metis option.collapse option.inject option.simps(3) plus_optionI plus_option_Some_None)
           apply auto[5]
      apply (metis core_option_None)
    apply auto[1]
  proof -
    fix a' b' x' y'
    assume "Some a = b \<oplus> x" "Some a = b \<oplus> y" "|x| = |y|" "a = Some a'" "b = Some b'" "x = Some x'" "y = Some y'"
    then have "x' = y'" using cancellative[of a' b' x' y']
      by (metis core_option.simps(2) option.inject plus_optionE)
    then show "x = y"
      by (simp add: \<open>x = Some x'\<close> \<open>y = Some y'\<close>)
  qed
qed

end


(*
subsection \<open>Sum\<close>

instantiation sum :: (pcm_with_core, pcm_with_core) pcm_with_core
begin

fun core_sum where
  "core_sum (Inl x) = Inl |x|"
| "core_sum (Inr x) = Inr |x|"

instance proof
  fix x y a b c :: "'a + 'b"
  show "Some x = x \<oplus> |x|"
  proof (cases x)
    case (Inl a)
    then have "Some a = a \<oplus> |a|"
      by (simp add: core_is_smaller)
    then show ?thesis
      using Inl option.discI by fastforce
  next
    case (Inr b)
    then have "Some b = b \<oplus> |b|"
      by (simp add: core_is_smaller)
    then show ?thesis
      using Inr option.discI by fastforce
  qed
  show "Some |x| = |x| \<oplus> |x|"
  proof (cases x)
    case (Inl a)
    then have "Some |a| = |a| \<oplus> |a|"
      by (simp add: core_is_pure)
    then show ?thesis
      using Inl option.discI by fastforce
  next
    case (Inr b)
    then have "Some |b| = |b| \<oplus> |b|"
      by (simp add: core_is_pure)
    then show ?thesis
      using Inr option.discI by fastforce
  qed

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"

  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
   
qed

end


instantiation sum :: (pcm_mult, pcm_mult) pcm_mult
begin

fun mult_sum :: "preal \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'b)" where
  "mult_sum \<alpha> (Inl x) = Inl (\<alpha> \<odot> x)"
| "mult_sum \<alpha> (Inr x) = Inr (\<alpha> \<odot> x)"

(* TODO *)
instance

end

*)


lemma padd_pnone:
  "padd x pnone = x"
  by simp


instantiation prat :: pcm_with_core
begin

definition core_prat :: "prat \<Rightarrow> prat" where
  "core_prat a = 0"

instance proof
  fix a b c x y :: prat
  show "Some x = x \<oplus> |x|"
    by (simp add: core_prat_def padd_pnone plus_prat_def)
  show "Some |x| = |x| \<oplus> |x|"
    using core_prat_def padd_pnone plus_prat_def by force
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    by (metis PosRat.padd_cancellative plus_prat_def \<open>Some x = x \<oplus> |x|\<close> \<open>Some |x| = |x| \<oplus> |x|\<close> add.commute option.sel)
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using \<open>Some |x| = |x| \<oplus> |x|\<close> core_prat_def by auto
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis PosRat.padd_cancellative plus_prat_def add.commute option.sel)
qed

end

instantiation preal :: pcm_with_core
begin

definition core_preal :: "preal \<Rightarrow> preal" where
  "core_preal a = 0"

instance proof
  fix a b c x y :: preal
  show "Some x = x \<oplus> |x|"
    by (simp add: core_preal_def padd_pnone plus_preal_def)
  show "Some |x| = |x| \<oplus> |x|"
    using core_preal_def padd_pnone plus_preal_def by force
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    by (metis PosReal.padd_cancellative plus_preal_def \<open>Some x = x \<oplus> |x|\<close> \<open>Some |x| = |x| \<oplus> |x|\<close> add.commute option.sel)
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using \<open>Some |x| = |x| \<oplus> |x|\<close> core_preal_def by auto
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    by (metis PosReal.padd_cancellative plus_preal_def add.commute option.sel)
qed

end



section \<open>Instantiations of PCMs with multiplication\<close>

instantiation preal :: pcm_mult
begin

definition mult_preal :: "preal \<Rightarrow> preal \<Rightarrow> preal" where "mult_preal = (*)"

instance proof
  fix \<alpha> \<beta> a b x :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_preal_def)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult.assoc mult_preal_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    by (simp add: plus_preal_def distrib_left mult.commute mult_preal_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: plus_preal_def distrib_left mult_preal_def)
qed

end

instantiation prod :: (pcm_mult, pcm_mult) pcm_mult
begin

definition mult_prod :: "preal \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" where
  "mult_prod \<alpha> x = (\<alpha> \<odot> fst x, \<alpha> \<odot> snd x)"

instance proof
  fix a b x :: "'a \<times> 'b"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_prod_def unit_mult)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult_mult mult_prod_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    apply (rule plus_prodI)
    apply (simp add: mult_prod_def distrib_scala_mult)
    by (simp add: mult_prod_def distrib_scala_mult)
  assume "Some x = a \<oplus> b"
  then have "Some (\<alpha> \<odot> fst x) = (\<alpha> \<odot> fst a) \<oplus> (\<alpha> \<odot> fst b) \<and> Some (\<alpha> \<odot> snd x) = (\<alpha> \<odot> snd a) \<oplus> (\<alpha> \<odot> snd b)"
    by (metis distrib_state_mult plus_prodE)
  then show "Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (metis fst_eqD mult_prod_def plus_prodIAlt snd_eqD)
qed

end

instantiation "fun" :: (type, pcm_mult) pcm_mult
begin

definition mult_fun where "mult_fun \<alpha> f x = \<alpha> \<odot> f x"

instance proof
  fix f a b :: "'a \<Rightarrow> 'b"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> f = f"
  proof (rule ext)
    fix x show "(pwrite \<odot> f) x = f x"
      by (simp add: mult_fun_def unit_mult)
  qed
  show "\<alpha> \<odot> (\<beta> \<odot> f) = pmult \<alpha> \<beta> \<odot> f"
  proof (rule ext)
    fix x show "(\<alpha> \<odot> (\<beta> \<odot> f)) x = (pmult \<alpha> \<beta> \<odot> f) x"
      by (simp add: mult_fun_def mult_mult)
  qed

  have "compatible_fun (\<alpha> \<odot> f) (\<beta> \<odot> f)"
    by (metis (mono_tags, lifting) compatible_fun_def distrib_scala_mult mult_fun_def option.discI)
  then obtain ff where "Some ff = \<alpha> \<odot> f \<oplus> \<beta> \<odot> f"
    by (simp add: plus_fun_def)
  moreover have "ff = padd \<alpha> \<beta> \<odot> f"
  proof (rule ext)
    fix x
    show "ff x = (padd \<alpha> \<beta> \<odot> f) x"
      by (metis (mono_tags, lifting) \<open>compatible_fun (\<alpha> \<odot> f) (\<beta> \<odot> f)\<close> calculation distrib_scala_mult mult_fun_def option.sel plus_fun_def)
  qed
  ultimately show "Some (padd \<alpha> \<beta> \<odot> f) = \<alpha> \<odot> f \<oplus> \<beta> \<odot> f"
    by blast


  assume asm0: "Some f = a \<oplus> b"
  have "compatible_fun (\<alpha> \<odot> a) (\<alpha> \<odot> b)"
  proof (rule compatible_funI)
    fix l show "(\<alpha> \<odot> a) l \<oplus> (\<alpha> \<odot> b) l \<noteq> None"
      by (metis asm0 distrib_state_mult mult_fun_def option.simps(3) plus_funE)
  qed
  then obtain ff where "Some ff = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: plus_fun_def)
  moreover have "ff = \<alpha> \<odot> f"
  proof (rule ext)
    fix x show "ff x = (\<alpha> \<odot> f) x"
      using asm0 calculation distrib_state_mult mult_fun_def option.sel plus_funE[of _ a b] plus_funE[of _ "\<alpha> \<odot> a" "\<alpha> \<odot> b"]
      by metis
  qed
  ultimately show "Some (\<alpha> \<odot> f) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by blast
qed

end

instantiation option :: (pcm_mult) pcm_mult
begin

fun mult_option :: "preal \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "mult_option \<alpha> None = None"
| "mult_option \<alpha> (Some x) = Some (\<alpha> \<odot> x)"

(* TODO *)
instance proof
  fix x a b :: "'a option"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (metis mult_option.elims unit_mult)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (metis mult_option.simps(1) mult_mult mult_option.simps(2) not_Some_eq)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    apply (cases x)
    apply simp
    using distrib_scala_mult plus_optionI by fastforce
  assume asm0: "Some x = a \<oplus> b"
  show "Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
  proof (cases "a \<noteq> None \<and> b \<noteq> None \<and> x \<noteq> None")
    case True
    then obtain aa bb xx where "a = Some aa \<and> b = Some bb \<and> x = Some xx"
      by blast
    then have "Some xx = aa \<oplus> bb"
      using asm0 plus_optionE by blast
    then have "Some (\<alpha> \<odot> xx) = \<alpha> \<odot> aa \<oplus> \<alpha> \<odot> bb"
      by (simp add: distrib_state_mult)
    then show ?thesis
      using mult_option.simps(2) \<open>a = Some aa \<and> b = Some bb \<and> x = Some xx\<close> option.discI by fastforce
  next
    case False
    then show ?thesis
      apply (cases a)
      using asm0 apply force
      apply (cases b)
      using asm0 apply auto[1]
      apply (cases x)
      apply (metis asm0 asso1 option.distinct(1) option.inject plus_option.simps(1) positivity)
      by simp
  qed
qed

end



instantiation agreement :: (type) pcm_mult
begin

definition mult_agreement :: "preal \<Rightarrow> 'a agreement \<Rightarrow> 'a agreement" where
  "mult_agreement \<alpha> x = x"

(* TODO *)
instance proof
  fix x a b :: "'a agreement"
  fix \<alpha> \<beta> :: preal
  show "pwrite \<odot> x = x"
    by (simp add: mult_agreement_def)
  show "\<alpha> \<odot> (\<beta> \<odot> x) = pmult \<alpha> \<beta> \<odot> x"
    by (simp add: mult_agreement_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (\<alpha> \<odot> x) = \<alpha> \<odot> a \<oplus> \<alpha> \<odot> b"
    by (simp add: mult_agreement_def)
  show "Some (padd \<alpha> \<beta> \<odot> x) = \<alpha> \<odot> x \<oplus> \<beta> \<odot> x"
    by (simp add: mult_agreement_def plus_agreement_def)
qed

end




section \<open>Instantiations of SepAlgebra\<close>


subsection \<open>Agreement\<close>

instantiation agreement :: (type) sep_algebra
begin

definition stable_agreement :: "'a agreement \<Rightarrow> bool" where
  "stable_agreement x \<longleftrightarrow> True"

definition stabilize_agreement :: "'a agreement \<Rightarrow> 'a agreement" where
  "stabilize_agreement x = x"

instance proof
  fix a b c x :: "'a agreement"

  show "sep_algebra_class.stable (stabilize x)"
    by (simp add: stable_agreement_def)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    by (simp add: stabilize_agreement_def)
  show "Some x = stabilize x \<oplus> |x|"
    by (simp add: core_is_smaller stabilize_agreement_def)
  show "sep_algebra_class.stable x \<Longrightarrow> stabilize x = x"
    by (simp add: stabilize_agreement_def)
  show "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b"
    by (metis option.distinct(1) plus_agreement_def plus_option_Some_None)
qed


end

lemma stabilize_ag:
  "stabilize (Ag x) = Ag x"
  by (simp add: stabilize_agreement_def)

subsection \<open>Product\<close>


instantiation prod :: (sep_algebra, sep_algebra) sep_algebra
begin

definition stabilize_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "stabilize_prod a = ( stabilize (fst a), stabilize (snd a) )"

definition stable_prod :: "'a \<times> 'b \<Rightarrow> bool" where
  "stable_prod a \<longleftrightarrow> stable (fst a) \<and> stable (snd a)"

instance
proof
  fix x a b c:: "'a :: sep_algebra \<times> 'b :: sep_algebra"
  show "sep_algebra_class.stable x \<Longrightarrow> stabilize x = x"
    by (simp add: SepAlgebra.stable_prod_def already_stable stabilize_prod_def)
  show "sep_algebra_class.stable (stabilize x)"
    by (simp add: SepAlgebra.stable_prod_def stabilize_is_stable stabilize_prod_def)
  show "Some x = stabilize x \<oplus> |x|"
    by (simp add: core_def decompose_stabilize_pure plus_prodI stabilize_prod_def)
  assume "Some x = a \<oplus> b"
  then have "Some (fst x) = fst a \<oplus> fst b \<and> Some (snd x) = snd a \<oplus> snd b"
    by (metis plus_prodE)
  then show "Some (stabilize x) = stabilize a \<oplus> stabilize b"
    by (simp add: plus_prodI stabilize_prod_def stabilize_sum)
next
  fix a b c:: "'a :: sep_algebra \<times> 'b :: sep_algebra"
  assume "Some a = b \<oplus> stabilize |c|"
  then have "fst a = fst b \<and> snd a = snd b"
    by (metis core_def fst_conv plus_prodE snd_eqD stabilize_core_emp stabilize_prod_def)
  then show "a = b"
    using prod.expand by blast
qed

end


instantiation "fun" :: (type, sep_algebra) sep_algebra
begin

definition stabilize_fun: "stabilize_fun f l = stabilize  (f l)"

definition stable_fun: "stable_fun f \<longleftrightarrow> (\<forall>l. stable (f l))"

instance
proof
  fix x a b c :: "'a \<Rightarrow> 'b :: sep_algebra"
  show "sep_algebra_class.stable (stabilize x)"
    by (simp add: stabilize_fun stable_fun)
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    by (smt (verit, ccfv_SIG) plus_funE plus_funI stabilize_fun stabilize_sum)
  show "Some x = stabilize x \<oplus> |x|"
    by (metis (mono_tags, lifting) core_fun decompose_stabilize_pure plus_funI stabilize_fun)
  show "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b"
  proof -
    assume "Some a = b \<oplus> stabilize |c|"
    then have "\<forall>aa f. Some f \<noteq> Some a \<or> Some (f aa) = b aa \<oplus> stabilize |c aa|"
      by (simp add: core_fun plus_funE stabilize_fun)
    then show ?thesis
      using stabilize_core_emp by fastforce
  qed
  assume "sep_algebra_class.stable x"
  show "stabilize x = x"
  proof (rule ext)
    fix l show "stabilize x l = x l"
      by (metis \<open>sep_algebra_class.stable x\<close> already_stable stabilize_fun stable_fun)
  qed
qed

end

(*
instantiation "option" :: (sep_algebra) sep_algebra
begin

fun stabilize_option where
  "stabilize_option None = None"
| "stabilize_option (Some x) = Some (stabilize x)"

fun stable_option where
  "stable_option None \<longleftrightarrow> True"
| "stable_option (Some x) \<longleftrightarrow> stable x"

instance proof
  fix x a b c :: "'a option"
  show "sep_algebra_class.stable x \<Longrightarrow> stabilize x = x"
    by (metis already_stable stabilize_option.elims stable_option.simps(2))
  show "sep_algebra_class.stable (stabilize x)"
    by (metis option.inject stabilize_is_stable stabilize_option.elims stable_option.elims(3) stable_option.simps(1))
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    apply (cases x; cases a; cases b)
           apply auto[3]
        apply (smt (verit, del_insts) option.sel option.simps(3) plus_option.simps(3))
       apply auto[3]
    by (smt (verit, ccfv_threshold) option.discI option.inject plus_option.elims stabilize_option.simps(2) stabilize_sum)
  show "Some x = stabilize x \<oplus> |x|"
    apply (cases x)
     apply auto[1]
    using decompose_stabilize_pure plus_optionI by fastforce
  show "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b" (* false *)

end
*)





end