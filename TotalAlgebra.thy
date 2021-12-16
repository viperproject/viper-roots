theory TotalAlgebra
imports TotalStateUtil Viper.SepAlgebra
begin


subsection \<open>Addition and multiplication of total states\<close>

text \<open>Total states are compatible only if their heaps are the same.\<close>
definition compatible_pre_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> bool"
  where
    "compatible_pre_total \<phi>1 \<phi>2 =    
         ( get_h_pre_total \<phi>1 = get_h_pre_total \<phi>2 \<and>
           wf_mask_simple (add_masks (get_mh_pre_total \<phi>1) (get_mh_pre_total \<phi>2)))"

definition pre_plus_total :: "'a pre_total_state \<Rightarrow> 'a pre_total_state \<Rightarrow> 'a pre_total_state option" where
  "pre_plus_total \<phi>1 \<phi>2 =
    (if compatible_pre_total \<phi>1 \<phi>2 then
       Some (get_h_pre_total \<phi>1, 
            ( add_masks (get_mh_pre_total \<phi>1) (get_mh_pre_total \<phi>2),
              add_masks (get_mp_pre_total \<phi>1) (get_mp_pre_total \<phi>2)))
     else None)"

definition compatible_total :: "'a total_state \<Rightarrow> 'a total_state \<Rightarrow> bool"
  where
    "compatible_total \<phi>1 \<phi>2 =    
         ( get_h_total \<phi>1 = get_h_total \<phi>2 \<and>
           wf_mask_simple (add_masks (get_mh_total \<phi>1) (get_mh_total \<phi>2)))"

fun add_m_total :: "mask \<times> 'a predicate_mask \<Rightarrow> mask \<times> 'a predicate_mask \<Rightarrow> mask \<times> 'a predicate_mask"
  where "add_m_total m1 m2 = (add_masks (fst m1) (fst m2), add_masks (snd m1) (snd m2))"

definition plus_total :: "'a total_state \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state option" (infixl "|\<oplus>|\<^sub>t" 60)  where
  "\<phi>1 |\<oplus>|\<^sub>t \<phi>2 =
    (if compatible_total \<phi>1 \<phi>2 then
        Some (update_m_total \<phi>1 (add_m_total (get_m_total \<phi>1) (get_m_total \<phi>2) ) 
             )
     else None)"

lemma comm_compatible_pre_total: "compatible_pre_total \<phi>1 \<phi>2 = compatible_pre_total \<phi>2 \<phi>1"
  unfolding compatible_pre_total_def
  by (auto simp: add_masks_comm)

lemma comm_compatible_total: "compatible_total \<phi>1 \<phi>2 = compatible_total \<phi>2 \<phi>1"
  unfolding compatible_total_def
  by (auto simp: add_masks_comm)

lemma pre_plus_total_wf : "pre_plus_total \<phi>1 \<phi>2 = Some \<phi>3  \<Longrightarrow> wf_mask_simple (get_mh_pre_total \<phi>3)"
  unfolding pre_plus_total_def compatible_pre_total_def
  by (auto split: if_split_asm)

lemma pre_plus_total_same_h : "pre_plus_total \<phi>1 \<phi>2 = Some \<phi>3  \<Longrightarrow> get_h_pre_total \<phi>1 = get_h_pre_total \<phi>2"
  unfolding pre_plus_total_def compatible_pre_total_def
  by (auto split: if_split_asm)


lemma comm_plus_total: "a |\<oplus>|\<^sub>t b = b |\<oplus>|\<^sub>t a"
  unfolding plus_total_def
  by (simp split: if_split add: add_masks_comm compatible_total_def update_m_total_def)

lemma plus_total_defined_h_eq_1:
  assumes "a |\<oplus>|\<^sub>t b = Some c"
  shows "get_h_total a = get_h_total b"
  using assms
  unfolding plus_total_def
  by (simp add:compatible_total_def split: if_split_asm)

lemma plus_total_defined_h_eq_2:
  assumes "a |\<oplus>|\<^sub>t b = Some c"
  shows "get_h_total a = get_h_total c"
  using assms
  unfolding plus_total_def
  apply (simp add:compatible_total_def split: if_split_asm)
  by (metis fst_conv get_h_pre_total.simps get_h_total.simps get_h_update_m_total)

lemma plus_total_m: 
  assumes "\<phi>1 |\<oplus>|\<^sub>t \<phi>2 = Some \<phi>3"
  shows "get_m_total \<phi>3 = (add_m_total (get_m_total \<phi>1) (get_m_total \<phi>2))"
  using assms
  unfolding plus_total_def
  apply (simp split: if_split_asm del: get_mh_total.simps get_mp_total.simps get_m_total.simps)
  using compatible_total_def get_m_update_m_total by fastforce


lemma plus_total_defined: "a |\<oplus>|\<^sub>t b \<noteq> None \<longleftrightarrow> compatible_total a b"
  unfolding plus_total_def
  by (simp split: if_split)

lemma assoc1_plus_total: 
  assumes "a |\<oplus>|\<^sub>t b = Some ab" and "b |\<oplus>|\<^sub>t c = Some bc"
  shows "ab |\<oplus>|\<^sub>t c = a |\<oplus>|\<^sub>t bc"
proof -
  from assms have Heq1: "get_h_total a = get_h_total b" "get_h_total b = get_h_total c"
    by (simp_all only: plus_total_defined_h_eq_1 )
  from assms have Heq2: "get_h_total a = get_h_total ab" "get_h_total b = get_h_total bc"
    by (simp_all only: plus_total_defined_h_eq_2)
  
  from assms have Meq1: "get_m_total ab  = add_m_total (get_m_total a) (get_m_total b)"
    by (simp only: plus_total_m)

  from assms have Meq2: "get_m_total bc  = add_m_total (get_m_total b) (get_m_total c)"
    by (simp only: plus_total_m)

  show ?thesis
  proof (cases "ab |\<oplus>|\<^sub>t c = None")
  case True
    hence "\<not> compatible_total ab c"
      using plus_total_defined by blast
    hence "\<not> wf_mask_simple (add_masks (get_mh_total ab) (get_mh_total c))"
      using Heq1 Heq2 compatible_total_def by fastforce
    then show ?thesis
      using Meq1 Meq2 add_masks_assoc
      by (metis (no_types, lifting) add_m_total.simps compatible_total_def fstI get_m_mh_mp_total plus_total_def)
next
  case False
  hence "compatible_total ab c"
      using plus_total_defined by blast
  hence "compatible_total a bc"
    unfolding compatible_total_def
      using Heq1 Heq2 Meq1 Meq2 add_masks_assoc
      by (metis add_m_total.simps fst_conv get_mh_from_m_total) 
    from this obtain y where PEq1: "a |\<oplus>|\<^sub>t bc = Some y"
      using plus_total_defined by blast
     from \<open>ab |\<oplus>|\<^sub>t c \<noteq> None\<close> obtain x where PEq2:"ab |\<oplus>|\<^sub>t c = Some x"
      using plus_total_defined by blast
    have "x = y"
      apply (rule total_state_eq)           
       apply (subst plus_total_m[OF PEq1])
       apply (subst plus_total_m[OF PEq2])
       apply (subst Meq1)
       apply (subst Meq2)
       apply (simp add: add_masks_assoc)
      by (metis Heq2(1) PEq1 PEq2 plus_total_defined_h_eq_2)
    thus ?thesis
      by (simp add: PEq1 PEq2)
  qed
qed

lemma assoc2_plus_total:
  assumes "a |\<oplus>|\<^sub>t b = Some ab" and "b |\<oplus>|\<^sub>t c = None"
  shows "ab |\<oplus>|\<^sub>t c = None"
proof -
  from assms(2) have "\<not> compatible_total b c"
    using plus_total_defined by blast
  hence "get_h_total b \<noteq> get_h_total c \<or> \<not> wf_mask_simple (add_masks (get_mh_total b) (get_mh_total c))"
    by (simp add: compatible_total_def)
  thus ?thesis
  proof
    assume "get_h_total b \<noteq> get_h_total c"
    hence "get_h_total c \<noteq> get_h_total ab"
      using assms(1) plus_total_defined_h_eq_1 plus_total_defined_h_eq_2
      by fastforce
    thus "ab |\<oplus>|\<^sub>t c = None"
      by (simp add: compatible_total_def plus_total_def)
  next
    assume "\<not> wf_mask_simple (add_masks (get_mh_total b) (get_mh_total c))"
    hence "\<not> wf_mask_simple (add_masks (add_masks (get_mh_total a) (get_mh_total b)) (get_mh_total c))"
      using wf_mask_simple_false_preserved add_masks_comm add_masks_assoc
      by metis
    thus ?thesis
      using plus_total_m assms(1)
      by (metis (no_types, lifting) add_m_total.elims compatible_total_def fstI get_mh_from_m_total plus_total_defined)
  qed
qed

lemma assoc3_plus_total:
  assumes "a |\<oplus>|\<^sub>t b = None" and "b |\<oplus>|\<^sub>t c = Some bc"
  shows "a |\<oplus>|\<^sub>t bc = None"
  using assms comm_plus_total assoc2_plus_total
  by metis

text \<open>Multiplication of states (TODO: duplication in Viper.EquiViper)\<close>
definition mult_mask :: "prat \<Rightarrow> mask \<Rightarrow> mask" where
  "mult_mask p \<pi> x = pmult p (\<pi> x)"

definition multiplicable_mask :: "prat \<Rightarrow> mask \<Rightarrow> bool" where
  "multiplicable_mask p \<pi> \<longleftrightarrow> (\<forall>hl. lte (pmult p (\<pi> hl)) pwrite)"

definition update_mh_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mh_total \<phi> mh = Abs_total_state (get_h_total \<phi>, (mh, get_mp_total \<phi>))"

definition mult_total :: "prat \<Rightarrow> 'a total_state \<Rightarrow> 'a total_state option" (infixl "|\<odot>|\<^sub>t" 70) where
  "\<alpha> |\<odot>|\<^sub>t \<phi> = (if multiplicable_mask \<alpha> (get_mh_total \<phi>) then 
                   Some (update_mh_total \<phi> (mult_mask \<alpha> (get_mh_total \<phi>))) else None
               )"

definition core_total :: "'a total_state \<Rightarrow> 'a total_state"
  where "core_total \<phi> = update_m_total \<phi> (zero_mask, zero_mask)"

lemma add_core_total: "x |\<oplus>|\<^sub>t core_total x = Some x"
  unfolding core_total_def plus_total_def
  apply (simp split: if_split del: get_m_total.simps)
  apply (rule conjI)
   apply (rule impI)
   apply (metis (no_types, hide_lams) compatible_total_def fst_conv get_h_update_m_total get_m_mh_mp_total get_m_update_m_total snd_conv total_state_eq wf_zero_mask zero_mask_neutral)
  apply (unfold compatible_total_def)
  apply (rule conjI)
   apply (metis fst_conv get_h_update_m_total wf_zero_mask)
  apply (unfold wf_mask_simple_def)
  by (metis fst_conv get_m_update_m_total get_mask_total_wf get_mh_from_m_total wf_mask_simple_def wf_zero_mask zero_mask_neutral)

definition stable_total :: "'a total_state \<Rightarrow> bool"
  where "stable_total _ = True"

definition stabilize_total :: "'a total_state \<Rightarrow> 'a total_state"
  where "stabilize_total = id"

global_interpretation TotalViper: sep_algebra plus_total mult_total core_total stable_total stabilize_total
  unfolding sep_algebra_def
  apply (intro conjI)
              apply (simp add: comm_plus_total)
             apply (blast intro: assoc1_plus_total)
            apply (blast intro: assoc2_plus_total)
           apply (blast intro: assoc3_plus_total)
          apply (blast intro: HOL.sym[OF add_core_total])


  

end