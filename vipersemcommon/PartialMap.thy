theory PartialMap
  imports Main
begin

type_synonym ('a, 'b) map = "'a \<rightharpoonup> 'b"

fun compatible_options :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "compatible_options (Some a) (Some b) \<longleftrightarrow> a = b"
| "compatible_options _ _ \<longleftrightarrow> True"

fun merge_option :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b option \<Rightarrow> 'b option \<Rightarrow> 'b option" where
  "merge_option _ None None = None"
| "merge_option _ (Some a) None = Some a"
| "merge_option _ None (Some b) = Some b"
| "merge_option f (Some a) (Some b) = Some (f a b)"

definition merge_options :: "('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('b, 'c) map \<Rightarrow> ('b, 'c) map \<Rightarrow> ('b, 'c) map" where
  "merge_options f a b p = merge_option f (a p) (b p)"

definition compatible_maps :: "('a, 'b) map \<Rightarrow> ('a, 'b) map \<Rightarrow> bool" where
  "compatible_maps h1 h2 \<longleftrightarrow> (\<forall>hl. compatible_options (h1 hl) (h2 hl))"

lemma compatible_mapsI:
  assumes "\<And>x a b. h1 x = Some a \<and> h2 x = Some b \<Longrightarrow> a = b"
  shows "compatible_maps h1 h2"
  by (metis assms compatible_maps_def compatible_options.elims(3))

definition map_included :: "('a, 'b) map \<Rightarrow> ('a, 'b) map \<Rightarrow> bool" where
  "map_included h1 h2 \<longleftrightarrow> (\<forall>x. h1 x \<noteq> None \<longrightarrow> h1 x = h2 x)"

lemma map_includedI:
  assumes "\<And>x r. h1 x = Some r \<Longrightarrow> h2 x = Some r"
  shows "map_included h1 h2"
  by (metis assms map_included_def option.exhaust)

lemma compatible_maps_empty:
  "compatible_maps h (Map.empty)"
  by (simp add: compatible_maps_def)

lemma compatible_maps_comm:
  "compatible_maps h1 h2 \<longleftrightarrow> compatible_maps h2 h1" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis compatible_mapsI compatible_maps_def compatible_options.simps(1))
  show "?B \<Longrightarrow> ?A"
    by (metis compatible_mapsI compatible_maps_def compatible_options.simps(1))
qed

lemma add_heaps_asso:
  "(h1 ++ h2) ++ h3 = h1 ++ (h2 ++ h3)"
  by auto

lemma compatible_maps_same:
  assumes "compatible_maps ha hb"
      and "ha x = Some y"
    shows "(ha ++ hb) x = Some y"
  by (metis (no_types, lifting) assms(1) assms(2) compatible_maps_def compatible_options.simps(1) domD map_add_dom_app_simps(1) map_add_dom_app_simps(3))

lemma compatible_maps_refl:
  "compatible_maps h h"
  using compatible_maps_def compatible_options.elims(3) by fastforce

lemma map_invo:
  "h ++ h = h"
  by (simp add: map_add_subsumed2)

lemma included_then_compatible_maps:
  assumes "map_included h1 h"
      and "map_included h2 h"
    shows "compatible_maps h1 h2"
proof (rule compatible_mapsI)
  fix x a b
  assume "h1 x = Some a \<and> h2 x = Some b"
  then show "a = b"
    by (metis assms(1) assms(2) map_included_def option.discI option.inject)
qed

lemma map_included_then_sum:
  assumes "map_included h1 h2"
  shows "h1 ++ h2 = h2"
  by (meson assms domIff map_add_subsumed1 map_included_def map_le_def)

lemma commut_charact:
  assumes "compatible_maps h1 h2"
  shows "h1 ++ h2 = h2 ++ h1"
proof (rule ext)
  fix x
  show "(h1 ++ h2) x = (h2 ++ h1) x"
    using assms(1) compatible_maps_def[of h1 h2]
    by (metis compatible_maps_comm compatible_maps_same map_add_None map_add_find_right not_Some_eq)
qed


lemma compatible_maps_asso:
  "compatible_maps a b \<and> compatible_maps (a ++ b) c \<longleftrightarrow> compatible_maps b c \<and> compatible_maps a (b ++ c)" (is "?LHS \<longleftrightarrow> ?RHS")
proof (rule iffI)
  assume "?LHS"

  show "?RHS"
  proof (rule conjI)
    show "compatible_maps b c"
      apply (rule compatible_mapsI)
      using \<open>?LHS\<close>[simplified compatible_maps_def]
      by (metis compatible_options.simps(1) map_add_find_right)
  next
    show "compatible_maps a (b ++ c)"
      apply (rule compatible_mapsI)
      by (metis \<open>?LHS\<close> compatible_maps_def compatible_maps_same compatible_options.simps(1) map_add_SomeD)
  qed
next
  assume "?RHS"

  show "?LHS"
    unfolding compatible_maps_def
    by (metis \<open>?RHS\<close> compatible_maps_def commut_charact compatible_options.simps(3) domIff map_add_dom_app_simps(1) map_add_dom_app_simps(3))
qed

lemma positivity_maps:
  assumes "a ++ b = Map.empty"
  shows "a = Map.empty \<and> b = Map.empty"
  using assms by auto

lemma map_included_equiv:
  "map_included b a \<longleftrightarrow> (\<exists>c. compatible_maps b c \<and> a = b ++ c)"
  by (metis commut_charact included_then_compatible_maps map_add_find_right map_includedI map_included_then_sum)

end
