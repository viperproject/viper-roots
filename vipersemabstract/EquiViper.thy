theory EquiViper
  imports Main ViperCommon.PosPerm ViperCommon.ValueAndBasicState ViperCommon.PartialMap ViperCommon.Binop ViperCommon.DeBruijn
  ViperCommon.PosReal ViperCommon.SepAlgebra AbstractSemantics
begin

subsection \<open>Unbounded equi states\<close>

type_synonym 'a unbounded_state = "heap_loc \<Rightarrow> (preal, 'a val) PermValue"

definition empty_heap where
  "empty_heap l = ZeroNone"

lemma empty_heap_unit[simp]:
  "h \<oplus> empty_heap = Some h"
  "empty_heap \<oplus> h = Some h"
  by (metis commutative empty_heap_def plus_PermValue.simps(1) plus_funI)+


definition get_unbounded_heap :: "'a unbounded_state \<Rightarrow> heap_loc \<rightharpoonup> 'a val" where
  "get_unbounded_heap \<phi> l = (case \<phi> l of ZeroNone \<Rightarrow> None | Pair p v \<Rightarrow> Some v)"

definition get_unbounded_mask :: "'a unbounded_state \<Rightarrow> preal mask" where
  "get_unbounded_mask \<phi> l = (case \<phi> l of ZeroNone \<Rightarrow> 0 | Pair p v \<Rightarrow> p)"

lemma pos_perm_implies_heap_value:
  assumes "get_unbounded_mask \<phi> l > 0"
  shows "get_unbounded_heap \<phi> l \<noteq> None"
  using assms unfolding get_unbounded_mask_def get_unbounded_heap_def
  by (cases "\<phi> l") simp_all


lemma compatible_unbounded_heaps_iff:
  "\<phi>1 ## \<phi>2 \<longleftrightarrow> compatible_maps (get_unbounded_heap \<phi>1) (get_unbounded_heap \<phi>2)"
  sorry

lemma add_derive:
  assumes "Some \<phi> = \<phi>1 \<oplus> \<phi>2"
  shows "get_unbounded_heap \<phi> = get_unbounded_heap \<phi>1 ++ get_unbounded_heap \<phi>2"
    and "get_unbounded_mask \<phi> = add_masks (get_unbounded_mask \<phi>1) (get_unbounded_mask \<phi>2)"
    apply (rule ext)
  sorry

subsection \<open>Unbounded equi states\<close>


definition bounded :: "'a unbounded_state \<Rightarrow> bool" where
  "bounded st \<longleftrightarrow> (\<forall>hl p v. st hl = Pair p v \<longrightarrow> p \<le> 1)"

lemma boundedI:
  assumes "\<And>hl p v. h hl = Pair p v \<Longrightarrow> p \<le> 1"
  shows "bounded h"
  using assms bounded_def by blast


lemma bounded_empty[simp]:
  "bounded empty_heap"
  by (simp add: bounded_def empty_heap_def)

typedef 'a bounded_state = "{ \<phi> :: 'a unbounded_state |\<phi>. bounded \<phi> }"
  using bounded_empty by blast


setup_lifting type_definition_bounded_state

definition get_vh :: "'a bounded_state \<Rightarrow> 'a partial_heap" where "get_vh \<phi> = snd (Rep_unbounded_state \<phi>)"
definition get_vm :: "'a bounded_state \<Rightarrow> preal mask" where "get_vm \<phi> = fst (Rep_unbounded_state \<phi>)"

lemma unbounded_state_ext:
  assumes "get_vh a = get_vh b"
      and "get_vm a = get_vm b"
    shows "a = b"
  by (metis Rep_unbounded_state_inject assms(1) assms(2) get_vh_def get_vm_def prod.expand)













subsection \<open>Additions\<close>

lemma masks_can_always_be_added:
  "(a :: preal mask) ## b"
  by (simp add: compatible_fun_def defined_def plus_fun_def plus_preal_def)

lemma add_masks_def:
  assumes "Some (\<pi>:: preal mask) = \<pi>1 \<oplus> \<pi>2"
  shows "\<pi> hl = \<pi>1 hl + \<pi>2 hl"
  using assms plus_funE plus_preal_def by fastforce

text \<open>Two equi_states can be added iff their heaps are compatible\<close>

lemma pre_wf_plus_def:
  "(\<pi>' :: preal mask, h') ## (\<pi>, h) \<longleftrightarrow> h' ## h"
  by (simp add: comp_prod masks_can_always_be_added)


(*
definition set_vh where
  "set_vh \<phi> h = Abs_unbounded_state (get_vm \<phi>, h)"
definition set_vm where
  "set_vm \<phi> m = Abs_unbounded_state (m, get_vh \<phi>)"
*)

lift_definition uu :: "'a unbounded_state" is "uuu"
  using wf_uuu by (simp add: uuu_def)

lemma uu_get :
  shows "get_vm uu = zero_mask" "get_vh uu = empty_heap"
  by (simp_all add:get_vm_def get_vh_def uu.rep_eq uuu_def)

(*
lemma sum_wf_is_wf:
  assumes "wf_pre_unbounded_state a"
      and "wf_pre_unbounded_state b"
      and "Some x = a \<oplus> b"
    shows "wf_pre_unbounded_state x"
*)

fun read_field :: "'a unbounded_state \<Rightarrow> heap_loc \<Rightarrow> 'a val option"
  where "read_field \<phi> loc = get_vh \<phi> loc"

lemma wf_mask_simple_get_vm [simp] :
  "wf_mask_simple (get_vm x)"
  by (metis Rep_unbounded_state get_vm_def mem_Collect_eq wf_pre_unbounded_state_def)

lemma get_vm_bound :
  "get_vm x hl \<le> 1"
  using wf_mask_simple_get_vm wf_mask_simple_def by blast

subsection \<open>Addition of virtual equi_states\<close>


instantiation unbounded_state :: (type) pcm
begin


lift_definition plus_unbounded_state :: "'a unbounded_state \<Rightarrow> 'a unbounded_state \<Rightarrow> 'a unbounded_state option"
  is "(\<lambda> st1 st2. Option.bind (st1 \<oplus> st2) (\<lambda> x. if wf_mask_simple (fst x) then Some x else None))"
  apply (simp add: bind_split wf_pre_unbounded_state_def del:Product_Type.split_paired_All)
proof clarify
  fix a b aa ba ab bb ac bc
  assume asm0: "\<forall>hl. PosReal.ppos (fst (a, b) hl) \<longrightarrow> (\<exists>y. snd (a, b) hl = Some y)"
                "\<forall>hl. PosReal.ppos (fst (aa, ba) hl) \<longrightarrow> (\<exists>y. snd (aa, ba) hl = Some y)"
                "(a, b) \<oplus> (aa, ba) = Some (ab, bb)" "PosReal.ppos (fst (ab, bb) (ac, bc))"
  then have "a (ac, bc) > 0 \<or> aa (ac, bc) > 0"
    using plus_prodE preal_plusE
    by (metis (mono_tags, lifting) add.right_neutral fst_conv gr_0_is_ppos plus_funE pperm_pnone_pgt)
  then have "\<exists>y. b (ac, bc) = Some y \<or> ba (ac, bc) = Some y"
    by (metis asm0(1) asm0(2) fst_conv gr_0_is_ppos snd_conv)
  then have "\<exists>y. b (ac, bc) \<oplus> ba (ac, bc) = Some y"
    by (metis asm0(3) plus_funE plus_prodE snd_conv)
  then show "\<exists>y. snd (ab, bb) (ac, bc) = Some y"
    by (smt (verit) \<open>\<exists>y. b (ac, bc) = Some y \<or> ba (ac, bc) = Some y\<close> asm0(3) option.discI option.sel plus_funE plus_option.elims plus_prodE snd_conv)
qed

lemma compatible_unbounded_state_implies_pre_unbounded_state:
  assumes "Some x = a \<oplus> b"
  shows "Some (Rep_unbounded_state x) = Rep_unbounded_state a \<oplus> Rep_unbounded_state b"
  using assms apply (transfer) by (clarsimp split:bind_splits if_splits)

lemma compatible_unbounded_state_implies_pre_unbounded_state_rev:
  assumes "Some (Rep_unbounded_state x) = Rep_unbounded_state a \<oplus> Rep_unbounded_state b"
  shows "Some x = a \<oplus> b"
  using assms apply (transfer) by (clarsimp simp add:wf_pre_unbounded_state_def split:bind_splits if_splits)

lemma unbounded_state_plus_None :
  "a \<oplus> b = None \<longleftrightarrow> Rep_unbounded_state a \<oplus> Rep_unbounded_state b = None \<or> \<not> wf_mask_simple (the (get_vm a \<oplus> get_vm b))"
  by (smt (verit) EquiViper.plus_unbounded_state.rep_eq bind.bind_lunit bind_eq_None_conv fst_conv get_vm_def option.map_disc_iff plus_prod_def)

instance proof
  fix a b c ab bc :: "'a unbounded_state"
  let ?a = "Rep_unbounded_state a"
  let ?b = "Rep_unbounded_state b"
  let ?c = "Rep_unbounded_state c"
  let ?ab = "Rep_unbounded_state ab"
  let ?bc = "Rep_unbounded_state bc"

  show "a \<oplus> b = b \<oplus> a"
    by (simp add: commutative plus_unbounded_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    by (smt (verit, del_insts) EquiViper.compatible_unbounded_state_implies_pre_unbounded_state asso1 map_fun_apply plus_unbounded_state_def)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    apply (clarsimp simp add:unbounded_state_plus_None)
    apply (safe)
     apply (metis EquiViper.compatible_unbounded_state_implies_pre_unbounded_state asso2 option.discI)
  proof -
    fix aa ba
    assume asm0: "a \<oplus> b = Some ab" "wf_mask_simple (the (get_vm ab \<oplus> get_vm c))"
       "Rep_unbounded_state ab \<oplus> Rep_unbounded_state c = Some (aa, ba)" "\<not> wf_mask_simple (the (get_vm b \<oplus> get_vm c))"
    then obtain hl where "the (get_vm b \<oplus> get_vm c) hl > 1"
      by (meson not_less wf_mask_simple_def)
    then have "get_vm b hl + get_vm c hl > 1"
      by (smt (verit, ccfv_SIG) SepAlgebra.plus_preal_def option.sel plus_funI plus_fun_def)
    moreover have "the (get_vm ab \<oplus> get_vm c) hl \<ge> get_vm ab hl + get_vm c hl"
      by (metis (no_types, lifting) EquiViper.add_masks_def asm0(3) get_vm_def nle_le option.sel plus_prodE)
    moreover have "get_vm ab hl \<ge> get_vm b hl"
      by (metis (no_types, lifting) EquiViper.add_masks_def EquiViper.compatible_unbounded_state_implies_pre_unbounded_state \<open>a \<oplus> b = b \<oplus> a\<close> asm0(1) get_vm_def plus_prodE pos_perm_class.sum_larger)      
    moreover have "the (get_vm ab \<oplus> get_vm c) hl \<le> 1"
      using asm0(2) wf_mask_simple_def by blast
    ultimately show False
      by (simp add: leD less_eq_preal.rep_eq plus_preal.rep_eq)
  qed
  assume asm0: "a \<oplus> b = Some c" "Some c = c \<oplus> c"
  then have "Some ?c = ?a \<oplus> ?b \<and> Some ?c = ?c \<oplus> ?c"
    by (metis compatible_unbounded_state_implies_pre_unbounded_state)
  then show "Some a = a \<oplus> a"
    by (metis compatible_unbounded_state_implies_pre_unbounded_state_rev positivity)

qed

end















subsection \<open>Normal equi_states\<close>

type_synonym 'a ag_trace = "(label \<rightharpoonup> 'a unbounded_state) agreement"

(* Normal equi_state *)

(*
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)
*)
(*
type_synonym 'a trace = "label \<rightharpoonup> 'a unbounded_state"
*)
type_synonym 'a equi_state = "('a val, ('a ag_trace \<times> 'a unbounded_state)) abs_state"
                                    
(*
= 'a val ag_store \<times> ('a unbounded_state \<times> 'a trace)"
'a val ag_store = (var \<rightharpoonup> 'a val) agreement"
*)

(*
fun get_store :: "'a equi_state \<Rightarrow> (var \<rightharpoonup> 'a val)" where "get_store \<omega> = get_store \<omega>"
fun get_t :: "'a equi_state \<Rightarrow> 'a trace" where "get_t \<omega> = fst (snd \<omega>)"
*)
(*
definition get_trace :: "('v, 'a) abs_state \<Rightarrow> (label \<rightharpoonup> 'a)" where "get_trace \<omega> = the_ag (snd (fst \<omega>))"

*)
definition get_state :: "'a equi_state \<Rightarrow> 'a unbounded_state" where "get_state \<omega> = snd (snd \<omega>)"
definition get_trace :: "'a equi_state \<Rightarrow> (label \<rightharpoonup> 'a unbounded_state)" where "get_trace \<omega> = the_ag (fst (snd \<omega>))"
definition set_state :: "'a equi_state \<Rightarrow> 'a unbounded_state \<Rightarrow> 'a equi_state" where
  "set_state \<omega> \<phi> = (Ag (get_store \<omega>), (Ag (get_trace \<omega>), \<phi>))"
definition set_trace :: "'a equi_state \<Rightarrow> (label \<rightharpoonup> 'a unbounded_state) \<Rightarrow> 'a equi_state" where
  "set_trace \<omega> \<tau> = (Ag (get_store \<omega>), (Ag \<tau>, get_state \<omega>))"

lemma get_store_set_trace [simp] :
  "get_store (set_trace \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_trace_def)
lemma get_store_set_state [simp] :
  "get_store (set_state \<omega> st) = get_store \<omega>"
  by (simp add:get_store_def set_state_def)

lemma get_trace_set_store [simp] :
  "get_trace (set_store \<omega> st) = get_trace \<omega>"
  by (simp add: get_abs_state_def get_trace_def set_store_def)
lemma get_trace_set_trace [simp] :
  "get_trace (set_trace \<omega> t) = t"
  by (simp add:get_trace_def set_trace_def)
lemma get_trace_set_state [simp] :
  "get_trace (set_state \<omega> st) = get_trace \<omega>"
  by (simp add:get_trace_def set_state_def)

lemma get_state_set_store [simp] :
  "get_state (set_store \<omega> st) = get_state \<omega>"
  by (metis get_abs_state_def get_abs_state_set_store get_state_def)
lemma get_state_set_trace [simp] :
  "get_state (set_trace \<omega> st) = get_state \<omega>"
  by (simp add:get_state_def set_trace_def)
lemma get_state_set_state [simp] :
  "get_state (set_state \<omega> st) = st"
  by (simp add:get_state_def set_state_def)


lemma snd_get_abs_state :
  "snd (get_abs_state \<omega>) = get_state \<omega>"
  by (simp add: get_abs_state_def get_state_def)

lemma fst_get_abs_state :
  "the_ag (fst (get_abs_state \<omega>)) = get_trace \<omega>"
  by (simp add: get_abs_state_def get_trace_def)

(*
(* TODO vipersemabstract/EquiSemAuxLemma.thy *)


*)

abbreviation get_h where "get_h \<omega> \<equiv> get_vh (get_state \<omega>)"
abbreviation get_m where "get_m \<omega> \<equiv> get_vm (get_state \<omega>)"


fun get_pv :: "'a equi_state \<Rightarrow> 'a pre_unbounded_state" where "get_pv \<omega> = Rep_unbounded_state (get_state \<omega>)"

definition shift_and_add_equi_state where
  "shift_and_add_equi_state \<omega> x = set_store \<omega> (shift_and_add (get_store \<omega>) x)"

subsection \<open>Assertions\<close>

inductive red_pure :: "('v, ('v unbounded_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state \<Rightarrow> 'v extended_val \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>] _)" [51,0,0,0] 81)
  and red_pure_exps :: "('v, ('v unbounded_state)) interp \<Rightarrow> 'v equi_state \<Rightarrow> pure_exp list \<Rightarrow> 'v val list \<Rightarrow> bool"
  where
  RedPureExps: "\<lbrakk> list_all2 (\<lambda>e v. c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vals \<rbrakk> \<Longrightarrow> red_pure_exps c \<omega> exps vals"

\<comment>\<open>Independent of SA\<close>
| RedLit: "\<Delta> \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>] Val (val_of_lit l)"
| RedVar: "\<lbrakk> get_store \<omega> n = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Var n; \<omega>\<rangle> [\<Down>] Val v"

| RedUnop: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v ; eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>] Val v'"

| RedBinopLazy: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] Val v"

| RedBinop: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v2 ; eval_binop v1 bop v2 = BinopNormal v \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] Val v"

| RedOld: "\<lbrakk> get_trace \<omega> l = Some \<phi> ; \<Delta> \<turnstile> \<langle>e; set_state \<omega> \<phi>\<rangle> [\<Down>] v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Old l e; \<omega>\<rangle> [\<Down>] v" (* Implicitly propagates failures *)

| RedLet: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; shift_and_add_equi_state \<omega> v1\<rangle> [\<Down>] r \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>] r"


| RedExistsTrue: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty ;
  \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool True) ;
  \<And>v'. v' \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v'\<rangle> [\<Down>] Val (VBool b) \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] Val (VBool True)"


| RedExistsFalse: "\<lbrakk> \<And>v. v \<in> set_from_type (domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool False) \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] Val (VBool False)"
| RedForallTrue: "\<lbrakk> \<And>v. v \<in> set_from_type (domains \<Delta>) ty \<longrightarrow> \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool True) \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] Val (VBool True)"
| RedForallFalse: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty ;
    \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] Val (VBool False);
    \<And>v'. v' \<in> set_from_type (domains \<Delta>) ty \<Longrightarrow> \<exists>b. \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v'\<rangle> [\<Down>] Val (VBool b) \<rbrakk>

  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] Val (VBool False)"
| RedCondExpTrue: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VBool True) ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] r \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>] r"

| RedCondExpFalse: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val (VBool False) ; \<Delta> \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>] r \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>] r"
| RedPermNull: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef Null) \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>] Val (VPerm 0)"

| RedResult: "\<lbrakk> get_store \<omega> 0 = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>] Val v"



| RedBinopRightFailure: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] VFailure ;  eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] VFailure"
| RedBinopFailure: "\<lbrakk> \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>] Val v1 ; \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>] Val v2 ; eval_binop v1 bop v2 = BinopOpFailure ; eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>] VFailure" (* Division by 0 *)
| RedOldFailure: "\<lbrakk> get_trace \<omega> l = None \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Old l e ; \<omega>\<rangle> [\<Down>] VFailure"
| RedExistsFailure: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty; \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] VFailure \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>] VFailure"
| RedForallFailure: "\<lbrakk> v \<in> set_from_type (domains \<Delta>) ty; \<Delta> \<turnstile> \<langle>e; shift_and_add_equi_state \<omega> v\<rangle> [\<Down>] VFailure \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>] VFailure"
| RedPropagateFailure: "\<lbrakk> e \<in> sub_pure_exp e' ; \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow>  \<Delta> \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>] VFailure"



(* Dependent on the parameters *)
| RedField: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef (Address a)) ; read_field (get_state \<omega>) (a, f) = Some v \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>] Val v"

| RedFunApp: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (funs \<Delta>) f vals (get_state \<omega>) = Some v \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>] Val v"
| RedFunAppFailure: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (funs \<Delta>) f vals (get_state \<omega>) = None \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>] VFailure"


(*
(*
| RedPermField: "\<lbrakk> \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VRef (Address a)) \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_preal (get_m \<omega> (a, f))))"
| RedPermPred: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_preal (get_m \<omega> (p, vals))))"
*)

(*
| RedUnfolding: "\<lbrakk> red_pure_exps \<Delta> (\<sigma>, \<tau>, \<phi>) exps vals ; unfold_pure \<phi> (P, vals) = Some \<phi>' ; \<Delta> \<turnstile> \<langle>e; (\<sigma>, \<tau>, \<phi>')\<rangle> [\<Down>] r \<rbrakk>
   \<Longrightarrow> \<Delta> \<turnstile> \<langle>Unfolding P exps e; (\<sigma>, \<tau>, \<phi>)\<rangle> [\<Down>] r"
| RedUnfoldingFail: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; unfold_pure (get_state \<omega>) (P, vals) = None \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> \<langle>Unfolding P exps e; \<omega>\<rangle> [\<Down>] VFailure"
*)
*)

inductive_cases red_pure_elim:
  "\<Delta> \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>] v"

inductive_simps red_pure_simps:
  "\<Delta> \<turnstile> \<langle>ELit x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Var x;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unop op e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Binop e1 op e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>CondExp e1 e2 e3;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FieldAcc e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Old l e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Perm e f;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PermPred p es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>FunApp f es;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Result;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Unfolding p es e;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>Let e1 e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PExists ty e2;\<omega>\<rangle> [\<Down>] v"
  "\<Delta> \<turnstile> \<langle>PForall ty e2;\<omega>\<rangle> [\<Down>] v"


text \<open>The following lemma proves that the meaning of pure expressions is independent from the interpretation of predicates.\<close>

lemma red_pure_indep_interp_pred:
  assumes "funs \<Delta> = funs \<Delta>'"
      and "domains \<Delta> = domains \<Delta>'"
    shows "\<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v \<Longrightarrow> \<Delta>' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] v"
      and "red_pure_exps \<Delta> \<omega> exps vals \<Longrightarrow> red_pure_exps \<Delta>' \<omega> exps vals"
  using assms
proof (induct rule: red_pure_red_pure_exps.inducts)
  case (RedPureExps c \<omega> exps vals)
  then show ?case
    by (simp add: list_all2_mono red_pure_red_pure_exps.RedPureExps)
next
  case (RedLit \<Delta> l uu)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLit)
next
  case (RedVar \<omega> n v \<Delta>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedVar)
next
  case (RedUnop \<Delta> e \<omega> v unop v')
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedUnop)
next
  case (RedBinopLazy \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopLazy)
next
  case (RedBinop \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinop)
next
  case (RedOld \<omega> l \<phi> \<Delta> e v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedOld)
next
  case (RedLet \<Delta> e1 \<omega> v1 e2 r)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedLet)
next
  case (RedExistsTrue v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsTrue)
next
  case (RedExistsFalse \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsFalse)
next
  case (RedForallTrue \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallTrue)
next
  case (RedForallFalse v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallFalse)
next
  case (RedCondExpTrue \<Delta> e1 \<omega> e2 r e3)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpTrue)
next
  case (RedCondExpFalse \<Delta> e1 \<omega> e3 r e2)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedCondExpFalse)
next
  case (RedPermNull \<Delta> e \<omega> f)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPermNull)
next
  case (RedResult \<omega> v \<Delta>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedResult)
next
  case (RedBinopRightFailure \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopRightFailure)
next
  case (RedBinopFailure \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedBinopFailure)
next
  case (RedOldFailure \<omega> l \<Delta> e)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedOldFailure)
next
  case (RedExistsFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedExistsFailure)
next
  case (RedForallFailure v \<Delta> ty e \<omega>)
  then show ?case
    by (metis red_pure_red_pure_exps.RedForallFailure)
next
  case (RedPropagateFailure e e' \<Delta> \<omega>)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedPropagateFailure)
next
  case (RedField \<Delta> e \<omega> a f v)
  then show ?case
    by (simp add: red_pure_red_pure_exps.RedField)
next
  case (RedFunApp \<Delta> \<omega> exps vals f v)
  then show ?case
    by (metis red_pure_red_pure_exps.RedFunApp)
next
  case (RedFunAppFailure \<Delta> \<omega> exps vals f)
  then show ?case
    by (metis red_pure_red_pure_exps.RedFunAppFailure)
qed


definition wd_pure :: "('v, ('v unbounded_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state \<Rightarrow> bool" where
  "wd_pure c e \<omega> \<longleftrightarrow> (\<exists>v. (c \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v))"

definition wd_pure_set :: "('v, ('v unbounded_state)) interp \<Rightarrow> pure_exp \<Rightarrow> 'v equi_state set \<Rightarrow> bool" where
  "wd_pure_set c e A \<longleftrightarrow> (\<forall>\<omega> \<in> A. wd_pure c e \<omega>)"

fun red_pure_bool where
  "red_pure_bool \<Delta> e \<omega> = (if wd_pure \<Delta> e \<omega> then
  if \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val (VBool True) then Some True else Some False
  else None)"

inductive red_atomic_assert :: "('v, ('v unbounded_state)) interp \<Rightarrow> pure_exp atomic_assert \<Rightarrow> 'v equi_state \<Rightarrow> bool option \<Rightarrow> bool" where

  RedAtomicPure: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VBool b)) \<rbrakk> \<Longrightarrow> red_atomic_assert \<Delta> (Pure e) \<omega> (Some b)"

\<comment>\<open>acc(e.f, p)\<close>
| RedAtomicAcc: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef r)) ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v > 0 \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> (Some (is_address r \<and> get_m \<omega> (the_address r, f) \<ge> Abs_preal v))"
| RedAtomicAccZero: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef _)) ; red_pure \<Delta> p \<omega> (Val (VPerm 0)) \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> (Some True)"

| RedAtomicAccWildcard: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef (Address a))) \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (Acc e f Wildcard) \<omega> (Some (get_m \<omega> (a, f) > 0))"
| RedAtomicAccWildcardNull: "\<lbrakk> red_pure \<Delta> e \<omega> (Val (VRef Null)) \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (Acc e f Wildcard) \<omega> (Some False)"
| RedAtomicAccNeg: "\<lbrakk> red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v < 0 \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (Acc e f (PureExp p)) \<omega> None"

\<comment>\<open>acc(P(exps), p)\<close>
(*
| RedAtomicPred: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v \<ge> 0 ; predicates \<Delta> (P, vals) = Some A \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> (Some (v > 0 \<longrightarrow> (\<exists>a \<in> A. get_state \<omega> = (Abs_preal v) \<odot> a)))"
| RedAtomicPredWildcard: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; (predicates \<Delta>) (P, vals) = Some A \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps Wildcard) \<omega> (Some (\<exists>a \<in> A. \<exists>\<alpha>. \<alpha> > 0 \<and> get_state \<omega> = \<alpha> \<odot> a))"
| RedAtomicPredNeg: "\<lbrakk> red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v < 0 \<rbrakk>
  \<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> None"
*)

(*
| RedAtomicPredNone: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; red_pure \<Delta> p \<omega> (Val (VPerm v)) ; v \<ge> 0 ;
  footprint_predicate (get_state \<omega>) (P, vals) (rat_to_b v) = None \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps (PureExp p)) \<omega> (Some (v = 0))"
| RedAtomicPredWildcardNone: "\<lbrakk> red_pure_exps \<Delta> \<omega> exps vals ; footprint_predicate (get_state \<omega>) (P, vals) f = None \<rbrakk>
\<Longrightarrow> red_atomic_assert \<Delta> (AccPredicate P exps Wildcard) \<omega> (Some False)"
*)

(*
lemma no_old_indep_trace:
  assumes "no_old e"
  and       "fst x = fst x'" and
        "get_state x = get_state x'"
  shows "e x = Some v \<longleftrightarrow> e x' = Some v"
  
*)

(*
inductive red_atomic_assert :: "('v, ('v unbounded_state)) interp \<Rightarrow> pure_exp atomic_assert \<Rightarrow> 'v equi_state \<Rightarrow> bool option \<Rightarrow> bool" where
*)

fun sat :: "('a, 'a unbounded_state) interp
     \<Rightarrow> (pure_exp, pure_exp atomic_assert) assert \<Rightarrow> 'a equi_state \<Rightarrow> bool"

(* :: "'c \<Rightarrow> ('p, 'i) assert \<Rightarrow> 'a \<Rightarrow> bool" *) ("_ \<Turnstile> ((\<langle>_;_\<rangle>))" [52,0,0] 84) where
  "\<Delta> \<Turnstile> \<langle>Atomic A; \<omega>\<rangle> \<longleftrightarrow> red_atomic_assert \<Delta> A \<omega> (Some True)"
| "sat \<Delta> (Imp b A) \<omega> \<longleftrightarrow>  (\<exists>v. (\<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v) \<and> (v = VBool True \<longrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle>)))"
| "(\<Delta> \<Turnstile> \<langle>CondAssert b A B; \<omega>\<rangle>) \<longleftrightarrow> (\<exists>v. (\<Delta> \<turnstile> \<langle>b; \<omega>\<rangle> [\<Down>] Val v) \<and> (v = VBool True  \<longrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle>)) \<and> 
                                                                  (v = VBool False \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>))
                                    )"
| "(\<Delta> \<Turnstile> \<langle>A && B; \<omega>\<rangle>) \<longleftrightarrow> (\<exists>a b. ((Some \<omega> = a \<oplus> b) \<and> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<and> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>)))"
| "(\<Delta> \<Turnstile> \<langle>A --* B; \<omega>\<rangle>) \<longleftrightarrow> (\<forall>b a. Some b = \<omega> \<oplus> a \<and> (\<Delta> \<Turnstile> \<langle>A; a\<rangle>) \<longrightarrow> (\<Delta> \<Turnstile> \<langle>B; b\<rangle>))"
| "\<Delta> \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle> \<longleftrightarrow> (\<forall>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)"
| "\<Delta> \<Turnstile> \<langle>Exists ty A; \<omega>\<rangle> \<longleftrightarrow> (\<exists>v \<in> set_from_type (domains \<Delta>) ty. \<Delta> \<Turnstile> \<langle>A; shift_and_add_equi_state \<omega> v\<rangle>)"
| "(\<Delta> \<Turnstile> \<langle>ImpureAnd A B; \<omega>\<rangle>) \<longleftrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> \<and> \<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>)"
| "(\<Delta> \<Turnstile> \<langle>ImpureOr A B; \<omega>\<rangle>) \<longleftrightarrow> (\<Delta> \<Turnstile> \<langle>A; \<omega>\<rangle> \<or> \<Delta> \<Turnstile> \<langle>B; \<omega>\<rangle>)"


(*
| "c \<Turnstile> \<langle>ForAll ty A; \<omega>\<rangle> \<longleftrightarrow> (\<forall>l. finite_sublist (set_from_type c ty) l \<and> length l \<ge> 1 \<longrightarrow>
  (\<exists>part. multi_plus part \<omega> \<and> length l = length part \<and> list_all2 (\<lambda>v a. (c \<Turnstile> \<langle>A; shift_and_add_equi_state a v\<rangle>)) l part))"
*)


section \<open>Restrictions\<close>

fun all_predicate_have_bodies where
  "all_predicate_have_bodies Pr \<longleftrightarrow> (\<forall>P decl. program.predicates Pr P = Some decl \<longrightarrow> predicate_decl.body decl \<noteq> None)"
(*
fun wf_exp where
  "wf_exp _ = undefined"
*)

fun wf_assert where
  "wf_assert Pr (AccPredicate P arg p) \<longleftrightarrow> (program.predicates Pr P \<noteq> None)"


fun no_predicate where
  "no_predicate (A && B) \<longleftrightarrow> no_predicate A \<and> no_predicate B"
| "no_predicate (Atomic (AccPredicate _ _ _)) \<longleftrightarrow> False"

fun wf_assertion where
  "wf_assertion Pr (A && B) \<longleftrightarrow> wf_assertion Pr A \<and> wf_assertion Pr B"
| "wf_assertion Pr (A --* B) \<longleftrightarrow> wf_assertion Pr A \<and> wf_assertion Pr B \<and> no_predicate A"


lemma predicate_body_good_case:
  assumes "program.predicates Pr p = Some P"
      and "predicate_decl.body P = Some A"
    shows "predicate_body Pr p = A"
  using assms predicate_body_def
  by simp


















(* DUMP OF a part of LiftSepAlgebra *)

subsection \<open>Normal states\<close>

(* TODO: rename get_ into abs_? *)
(* TODO: Should state be renamed to heap? get_state on abs_state sounds like the identity *)
(* TODO: define this via record instead of getter and setter functions? This would require proving the
class instances for the record (via isomorphism?), but one would get nice getters and setters automatically *)

lemma full_state_ext:
  assumes "get_store a = get_store b"
      and "get_state a = get_state b"
      and "get_trace a = get_trace b"
    shows "a = b"
  by (metis agreement.exhaust_sel assms get_state_def get_store_def get_trace_def prod_eqI)

lemma abs_state_ext_iff :
  "\<omega>1 = \<omega>2 \<longleftrightarrow> get_store \<omega>1 = get_store \<omega>2 \<and> get_trace \<omega>1 = get_trace \<omega>2 \<and> get_state \<omega>1 = get_state \<omega>2"
  using full_state_ext by blast


definition make_equi_state :: "(var \<rightharpoonup> 'a val) \<Rightarrow> (label \<rightharpoonup> 'a unbounded_state) \<Rightarrow> 'a unbounded_state \<Rightarrow> 'a equi_state" where
  "make_equi_state s t st = set_store (set_trace (set_state undefined st) t) s"

lemma get_store_make_equi_state[simp] :
  "get_store (make_equi_state s t st) = s"
  by (simp add:make_equi_state_def)
lemma get_trace_make_equi_state[simp] :
  "get_trace (make_equi_state s t st) = t"
  by (simp add:make_equi_state_def)
lemma get_state_make_equi_state[simp] :
  "get_state (make_equi_state s t st) = st"
  by (simp add:make_equi_state_def)
lemma set_store_make_equi_state[simp] :
  "set_store (make_equi_state s t st) s' = make_equi_state s' t st"
  by (simp add: EquiViper.full_state_ext)
lemma set_trace_make_equi_state[simp] :
  "set_trace (make_equi_state s t st) t' = make_equi_state s t' st"
  by (simp add: EquiViper.full_state_ext)
lemma set_state_make_equi_state[simp] :
  "set_state (make_equi_state s t st) st' = make_equi_state s t st'"
  by (simp add: EquiViper.full_state_ext)









end
