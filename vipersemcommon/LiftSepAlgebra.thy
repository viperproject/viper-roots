theory LiftSepAlgebra
  imports SepAlgebra PartialMap ViperLang
begin

type_synonym 'v ag_store = "(var \<rightharpoonup> 'v) agreement"
type_synonym 'a ag_trace = "(label \<rightharpoonup> 'a) agreement"

type_synonym ('v, 'a) abs_state = "('v ag_store \<times> 'a ag_trace) \<times> 'a"

(* all should come from the fact that 'v is agreement *)

subsection \<open>Normal states\<close>

(* TODO: rename get_ into abs_? *)
(* TODO: Should state be renamed to heap? get_state on abs_state sounds like the identity *)
(* TODO: define this via record instead of getter and setter functions? This would require proving the
class instances for the record (via isomorphism?), but one would get nice getters and setters automatically *)
definition get_store :: "('v, 'a) abs_state \<Rightarrow> (var \<rightharpoonup> 'v)" where "get_store \<omega> = the_ag (fst (fst \<omega>))"
definition get_trace :: "('v, 'a) abs_state \<Rightarrow> (label \<rightharpoonup> 'a)" where "get_trace \<omega> = the_ag (snd (fst \<omega>))"
definition get_state :: "('v, 'a) abs_state \<Rightarrow> 'a" where "get_state \<omega> = snd \<omega>"
definition set_store :: "('v, 'a) abs_state \<Rightarrow> (var \<rightharpoonup> 'v) \<Rightarrow> ('v, 'a) abs_state" where
  "set_store \<omega> s = ((Ag s, Ag (get_trace \<omega>)), get_state \<omega>)"
definition set_trace :: "('v, 'a) abs_state \<Rightarrow> (label \<rightharpoonup> 'a) \<Rightarrow> ('v, 'a) abs_state" where
  "set_trace \<omega> t = ((Ag (get_store \<omega>), Ag t), get_state \<omega>)"
definition set_state :: "('v, 'a) abs_state \<Rightarrow> 'a \<Rightarrow> ('v, 'a) abs_state" where
  "set_state \<omega> s = ((Ag (get_store \<omega>), Ag (get_trace \<omega>)), s)"

lemma get_store_set_store [simp] :
  "get_store (set_store \<omega> st) = st"
  by (simp add:get_store_def set_store_def)
lemma get_store_set_trace [simp] :
  "get_store (set_trace \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_trace_def)
lemma get_store_set_state [simp] :
  "get_store (set_state \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_state_def)

lemma get_trace_set_store [simp] :
  "get_trace (set_store \<omega> st) = get_trace \<omega>"
  by (simp add:get_trace_def set_store_def)
lemma get_trace_set_trace [simp] :
  "get_trace (set_trace \<omega> t) = t"
  by (simp add:get_trace_def set_trace_def)
lemma get_trace_set_state [simp] :
  "get_trace (set_state \<omega> st) = get_trace \<omega>"
  by (simp add:get_trace_def set_state_def)

lemma get_state_set_store [simp] :
  "get_state (set_store \<omega> st) = get_state \<omega>"
  by (simp add:get_state_def set_store_def)
lemma get_state_set_trace [simp] :
  "get_state (set_trace \<omega> st) = get_state \<omega>"
  by (simp add:get_state_def set_trace_def)
lemma get_state_set_state [simp] :
  "get_state (set_state \<omega> st) = st"
  by (simp add:get_state_def set_state_def)


definition make_abs_state :: "(var \<rightharpoonup> 'v) \<Rightarrow> (label \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> ('v, 'a) abs_state" where
"make_abs_state s t st = set_store (set_trace (set_state undefined st) t) s"

lemma get_store_make_abs_state[simp] :
  "get_store (make_abs_state s t st) = s"
  by (simp add:make_abs_state_def)
lemma get_trace_make_abs_state[simp] :
  "get_trace (make_abs_state s t st) = t"
  by (simp add:make_abs_state_def)
lemma get_state_make_abs_state[simp] :
  "get_state (make_abs_state s t st) = st"
  by (simp add:make_abs_state_def)
lemma set_store_make_abs_state[simp] :
  "set_store (make_abs_state s t st) s' = make_abs_state s' t st"
  by (simp add:make_abs_state_def set_store_def get_trace_def get_state_def)
lemma set_trace_make_abs_state[simp] :
  "set_trace (make_abs_state s t st) t' = make_abs_state s t' st"
  by (simp add:make_abs_state_def set_trace_def set_store_def get_trace_def get_store_def get_state_def)
lemma set_state_make_abs_state[simp] :
  "set_state (make_abs_state s t st) st' = make_abs_state s t st'"
  by (simp add:make_abs_state_def set_trace_def set_state_def set_store_def get_trace_def get_store_def get_state_def)

(*
lemma pcm_agreement_compatible:
  fixes a :: "('v  :: pcm_agreement) ag_store"
  shows "a ## b \<longleftrightarrow> compatible_maps a b" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?B
  have "compatible_fun a b"
  proof (rule compatible_funI)
    fix l
    show "a l \<oplus> b l \<noteq> None"
      by (smt (verit, ccfv_SIG) \<open>compatible_maps a b\<close> compatible_maps_def compatible_options.simps(1) option.distinct(1) pcm_agreement_class.plus_agreement plus_option.elims)
  qed                                                                                                                                         
  then show ?A
    by (simp add: defined_def plus_fun_def)
next
  assume ?A
  show ?B
  proof (rule compatible_mapsI)
    fix l va vb assume asm0: "a l = Some va \<and> b l = Some vb"
    then show "va = vb"
      by (metis \<open>a ## b\<close> compatible_partial_functions defined_def not_Some_eq pcm_agreement_class.plus_agreement)
  qed
qed

lemma pcm_agreement_sum:
  fixes a :: "('v  :: pcm_agreement) ag_store"
  assumes "Some x = a \<oplus> b"
  shows "x = a ++ b"
proof (rule ext)
  fix l
  show "x l = (a ++ b) l"
  proof (cases "b l")
    case None
    then show ?thesis
      by (metis assms domIff map_add_dom_app_simps(3) result_sum_partial_functions(2))
  next
    case (Some vb)
    then have "x l = Some vb \<or> x l = None"
      by (smt (verit, ccfv_SIG) assms option.exhaust pcm_agreement_class.plus_agreement result_sum_partial_functions(1) result_sum_partial_functions(3))
    then show ?thesis
      by (smt (verit, ccfv_threshold) Some assms compatible_funE map_add_find_right option.distinct(1) option.sel plus_fun_def plus_option.elims)
  qed
qed

*)

lemma ag_the_ag_same:
  "a = b \<longleftrightarrow> the_ag a = the_ag b"
  using agreement.expand by blast

lemma ag_comp:
  fixes x :: "'v agreement"
  shows "x ## y \<longleftrightarrow> x = y"
  by (simp add: defined_def plus_agreement_def)

lemma comp_prod:
  "a ## b \<longleftrightarrow> (fst a ## fst b \<and> snd a ## snd b)" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain x where "Some x = a \<oplus> b"
    by (metis defined_def not_Some_eq)
  then have "Some (fst x) = fst a \<oplus> fst b \<and> Some (snd x) = snd a \<oplus> snd b"
    by (metis plus_prodE)
  then show ?B
    by (metis defined_def option.discI)
next
  assume ?B
  then obtain r1 r2 where "Some r1 = fst a \<oplus> fst b \<and> Some r2 = snd a \<oplus> snd b"
    by (metis defined_def option.exhaust_sel)
  then show ?A
    using defined_def plus_prodIAlt by fastforce
qed    

lemma get_store_trace_comp:
  "fst a ## fst b \<longleftrightarrow> get_store a = get_store b \<and> get_trace a = get_trace b" (is "?A \<longleftrightarrow> ?B")
  by (simp add: ag_comp ag_the_ag_same comp_prod get_store_def get_trace_def)

lemma plus_state_def:
  "\<omega>1 \<oplus> \<omega>2 = (let r = (get_state \<omega>1 \<oplus> get_state \<omega>2) in
  (if get_store \<omega>1 = get_store \<omega>2 \<and> get_trace \<omega>1 = get_trace \<omega>2 \<and> r \<noteq> None then Some ((Ag (get_store \<omega>1), Ag (get_trace \<omega>1)), the r)
  else None))" (is "?A = ?B")
proof (cases "\<omega>1 \<oplus> \<omega>2")
  case None
  then have "get_state \<omega>1 \<oplus> get_state \<omega>2 = None \<or> get_store \<omega>1 \<noteq> get_store \<omega>2 \<or> get_trace \<omega>1 \<noteq> get_trace \<omega>2"
    by (metis comp_prod defined_def get_state_def get_store_trace_comp)
  then show ?thesis
    using None by auto
next
  case (Some x)
  then have asm0: "get_store \<omega>1 = get_store \<omega>2 \<and> get_state \<omega>1 \<oplus> get_state \<omega>2 \<noteq> None \<and> get_trace \<omega>1 = get_trace \<omega>2"
    by (metis comp_prod defined_def get_store_trace_comp get_state_def option.simps(3))
  then obtain r where "Some r = get_state \<omega>1 \<oplus> get_state \<omega>2"
    by force
  moreover have "fst \<omega>1 \<oplus> fst \<omega>2 = Some (Ag (get_store \<omega>1), Ag (get_trace \<omega>1))"
    by (metis (no_types, opaque_lifting) agreement.exhaust_sel asm0 core_is_smaller fst_conv get_store_def get_store_trace_comp get_trace_def greater_def smaller_compatible_core surjective_pairing)
  ultimately show ?thesis
    by (smt (z3) asm0 get_state_def option.sel plus_prodIAlt)
qed


(*
fun mult_state :: "'b \<Rightarrow> ('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state option" (infixl "\<odot>" 70) where
  "\<alpha> \<odot> \<omega> = (let r = (\<alpha> \<odot> get_state \<omega>) in if r = None then None else Some (get_store \<omega>, get_t \<omega>, the r))"
*)
(*
definition core_trace :: "'a trace \<Rightarrow> 'a trace" where
  "core_trace \<tau> l = (if \<tau> l = None then None else Some (core (the (\<tau> l))))"
*)

lemma full_core_def:
  "|\<omega>| = ((Ag (get_store \<omega>), Ag (get_trace \<omega>)),  |get_state \<omega>| )"
  by (smt (verit) agreement.exhaust_sel core_def core_is_smaller fst_conv get_state_def get_store_def get_trace_def option.discI plus_state_def snd_conv)

(*
lemma full_stable_def:
  "stable \<omega> \<longleftrightarrow> stable (get_state \<omega>)" (is "?A \<longleftrightarrow> ?B")
  sorry

fun full_stabilize :: "('v, 'a) abs_state \<Rightarrow> ('v, 'a) abs_state" where
  "full_stabilize \<omega> = (get_store \<omega>, stabilize (get_state \<omega>))"
*)

lemma full_add_defined:
  "\<omega>1 \<oplus> \<omega>2 \<noteq> None \<longleftrightarrow> ((get_state \<omega>1) \<oplus> (get_state \<omega>2) \<noteq> None \<and> get_store \<omega>1 = get_store \<omega>2 \<and> get_trace \<omega>1 = get_trace \<omega>2)"
  using plus_state_def[of \<omega>1 \<omega>2] option.discI
  by (smt (verit, del_insts))

lemma full_add_charact:
  assumes "Some x = a \<oplus> b"
  shows "get_store x = get_store a"
      and "Some (get_state x) = (get_state a) \<oplus> (get_state b)"
proof -
  show "get_store x = get_store a"
    by (smt (verit) agreement.exhaust_sel assms fst_conv get_store_def option.discI option.sel plus_state_def)
  show "Some (get_state x) = (get_state a) \<oplus> (get_state b)" 
    by (smt assms get_state_def option.exhaust_sel option.sel option.simps(3) plus_state_def snd_conv)
qed

(*
lemma compatible_traces_commutative:
  "compatible_traces a b \<longleftrightarrow> compatible_traces b a"
  sorry

lemma sum_traces_commutative:
  "compatible_traces a b \<Longrightarrow> sum_traces a b = sum_traces b a"
  sorry

lemma compatible_traces_asso:
  "compatible_traces a b \<and> compatible_traces (sum_traces a b) c
  \<longleftrightarrow> compatible_traces b c \<and> compatible_traces a (sum_traces b c)"
  sorry

lemma sum_traces_asso:
  "compatible_traces a b \<and> compatible_traces (sum_traces a b) c \<Longrightarrow>
  sum_traces (sum_traces a b) c = sum_traces a (sum_traces b c)"
  sorry
*)

lemma full_state_ext:
  assumes "get_store a = get_store b"
      and "get_state a = get_state b"
      and "get_trace a = get_trace b"
    shows "a = b"
  by (metis agreement.exhaust_sel assms get_state_def get_store_def get_trace_def prod_eqI)


(*
lemma sum_trace_core:
  "compatible_traces \<tau> (core_trace \<tau>)"
  "sum_traces \<tau> (core_trace \<tau>) = \<tau>"
  sorry
*)


(*
lemma core_trace_sum:
  "sum_traces (core_trace \<tau>) (core_trace \<tau>) = core_trace \<tau>"
  sorry

lemma core_trace_invo:
  "core_trace (core_trace \<tau>) = core_trace \<tau>"
  sorry
*)

(*
lemma add_ag_stores:
  fixes c :: "('v :: pcm_agreement) ag_store"
  shows "Some c = c \<oplus> c"
proof -
  have "compatible_fun c c"
  proof (rule compatible_funI)
    fix l show "c l \<oplus> c l \<noteq> None"
      apply (cases "c l")
       apply simp
      by (smt (verit, del_insts) option.distinct(1) pcm_agreement_class.plus_agreement plus_option.simps(3))
  qed
  then obtain cc where "Some cc = c \<oplus> c"
    by (simp add: plus_fun_def)
  moreover have "cc = c"
    using calculation map_invo pcm_agreement_sum by blast
  ultimately show ?thesis by simp
qed

*)

lemma add_defined_lift:
  fixes s :: "'v ag_store"
  assumes "Some c = a \<oplus> b"
  shows "Some (s, c) = (s, a) \<oplus> (s, b)"
proof -
  have "Some s = s \<oplus> s"
    by (simp add: plus_agreement_def)
  then show ?thesis using plus_prodIAlt assms 
    by fastforce
qed

(*
lemma full_stabilize_is_smaller:
  "\<exists>r. Some x = full_stabilize x \<oplus> r"
proof -
  obtain \<sigma> xx where "x = (\<sigma>, xx)" by (metis surj_pair)
  then obtain rr where "Some xx = stabilize xx \<oplus> rr"
    using stabilize_is_smaller by blast
  then have "Some x = full_stabilize x \<oplus> (\<sigma>, rr)"
    by (simp add: \<open>x = (\<sigma>, xx)\<close> add_defined_lift get_store_def get_state_def)
  then show ?thesis
    by blast
qed


lemma full_stabilize_is_stable:
  "full_stable (full_stabilize x)"
  by (simp add: get_state_def stabilize_is_stable)

lemma full_stabilize_max:
  assumes "Some x = a \<oplus> b"
      and "full_stable a"
    shows "\<exists>r. Some (full_stabilize x) = a \<oplus> r"
proof -
  obtain \<sigma>x \<sigma>a \<sigma>b xx aa bb where "x = (\<sigma>x, xx)" "a = (\<sigma>a, aa)" "b = (\<sigma>b, bb)"
    by (meson surj_pair)
  then have "Some xx = aa \<oplus> bb"
    by (metis assms(1) full_add_charact(2) get_state_def snd_conv)
  then obtain rr where "Some (stabilize xx) = aa \<oplus> rr" 
    by (metis \<open>a = (\<sigma>a, aa)\<close> assms(2) full_stable.elims(2) get_state_def stabilize_max snd_conv)
  then have "Some (full_stabilize x) = a \<oplus> (\<sigma>x, rr)"
    using \<open>a = (\<sigma>a, aa)\<close> \<open>x = (\<sigma>x, xx)\<close> add_defined_lift assms(1) fst_conv full_add_charact
      full_sa_axioms full_stabilize.elims option.distinct(1) option.sel plus_state_def snd_conv
    using fst_conv full_stabilize.simps get_store_def get_state_def option.distinct(1) option.sel plus_state_def snd_conv
    \<open>a = (\<sigma>a, aa)\<close> \<open>b = (\<sigma>b, bb)\<close> \<open>x = (\<sigma>x, xx)\<close> assms(1) fst_conv full_sa.plus_state_def full_sa_axioms
    full_stabilize.elims get_store_def get_state_def option.distinct(1) option.sel snd_conv map_add_assoc
    by (smt (verit) compatible_maps_asso compatible_maps_refl map_invo)
  then show ?thesis
    by blast
qed
*)

(*
lemma full_stabilize_sum:
  assumes "Some c = a \<oplus> b"
  shows "Some (full_stabilize c) = full_stabilize a \<oplus> full_stabilize b"
  by (smt add_defined_lift assms full_add_charact(1) full_add_charact(5) full_add_charact(5) full_add_defined full_stabilize.simps stabilize_sum)
*)

(*
definition full_add_set (infixl "\<otimes>" 60) where "full_add_set = SA.add_set"
definition full_defined (infixl "##" 60) where "full_defined = SA.defined"
definition full_greater (infixl "\<succeq>" 50) where "full_greater = SA.greater"
definition full_greater_set (infixl "\<ggreater>" 50) where "full_greater_set = SA.greater_set"
definition full_minus (infixl "\<ominus>" 63) where "full_minus = SA.minus"
definition full_mono where "full_mono = SA.mono_prop"
*)

(*
definition larger_trace :: "'a trace \<Rightarrow> 'a trace \<Rightarrow> bool" where
  "larger_trace a b \<longleftrightarrow> (\<forall>l \<phi>. b l = Some \<phi> \<longrightarrow> (\<exists>\<phi>'. a l = Some \<phi>' \<and> \<phi>' \<succeq> \<phi>))"

lemma larger_traceI:
  assumes "\<And>l \<phi>. b l = Some \<phi> \<Longrightarrow> (\<exists>\<phi>'. a l = Some \<phi>' \<and> \<phi>' \<succeq> \<phi>)"
  shows "larger_trace a b"
  by (simp add: assms larger_trace_def)

lemma larger_trace_equiv:
  "larger_trace a b \<longleftrightarrow> (\<exists>c. compatible_traces b c \<and> a = sum_traces b c)"
  sorry
*)

lemma ag_store_greater:
  fixes s :: "'v ag_store"
  shows "s' \<succeq> s \<longleftrightarrow> s = s'"
  by (metis ag_comp smaller_compatible_core succ_refl)

lemma ag_trace_greater:
  fixes s :: "'v ag_trace"
  shows "s' \<succeq> s \<longleftrightarrow> s = s'"
  by (metis ag_comp smaller_compatible_core succ_refl)

lemma greater_charact:
  "\<omega>' \<succeq> \<omega> \<longleftrightarrow> get_store \<omega> = get_store \<omega>' \<and> get_state \<omega>' \<succeq> get_state \<omega> \<and> get_trace \<omega> = get_trace \<omega>'" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis (no_types, opaque_lifting) get_state_def get_store_trace_comp greater_prod_eq smaller_compatible)
  assume ?B
  then have "Ag (get_store \<omega>') \<succeq> Ag (get_store \<omega>) \<and> get_state \<omega>' \<succeq> get_state \<omega> \<and> Ag (get_trace \<omega>') \<succeq> Ag (get_trace \<omega>)"
    by (simp add: succ_refl)
  then show ?A
    by (simp add: get_state_def get_store_def get_trace_def greater_prod_eq)
qed

lemma core_charact:
  shows "get_store |\<omega>| = get_store \<omega>"
    and "get_trace |\<omega>| = get_trace \<omega>"
    and "get_state |\<omega>| = |get_state \<omega>|"
  by (simp_all add: full_core_def get_store_def get_state_def get_trace_def)

(*
lemma mult_charact:
  assumes "Some \<omega>' = \<alpha> \<odot> \<omega>"
    shows "Some (get_state \<omega>') = \<alpha> \<odot> (get_state \<omega>)"
      and "get_t \<omega>' = get_t \<omega>"
      and "get_store \<omega>' = get_store \<omega>"
  apply (smt assms get_state_def mult_state.elims option.exhaust_sel option.sel option.simps(3) snd_conv) 
  apply (smt assms fst_conv get_t_def mult_state.elims option.sel option.simps(3) snd_conv) 
proof -
  have "\<forall>b p. if b \<odot> get_state p = None then b \<odot> p = None else b \<odot> p = Some (get_store p, get_t p, the (b \<odot> get_state p))"
    by fastforce
  then show "get_store \<omega>' = get_store \<omega>"
    by (metis (no_types) assms fst_conv get_store_def option.distinct(1) option.inject)
qed
*)


(*
lemma dom_union:
  assumes "Some x = a \<oplus> b"
  shows "dom x = dom a \<union> dom b"
(is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
    using assms result_sum_partial_functions(1) by fastforce
  show "?B \<subseteq> ?A"
    by (smt (verit, ccfv_threshold) Un_iff assms compatible_fun_def domIff option.distinct(1) option.sel plus_fun_def plus_option.elims subsetI)
qed

lemma ag_stores_compatible:
  fixes a :: "('v :: pcm_agreement) ag_store"
  assumes "a ## b"
      and "a l = Some va"
      and "b l = Some vb"
    shows "va = vb"
  by (metis assms(1) assms(2) assms(3) compatible_maps_def compatible_options.simps(1) pcm_agreement_compatible)
*)


end