theory TotalSemantics
imports Viper.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

(*datatype 'a result = Failure | Set (select_set: "'a full_total_state set")*)

datatype 'a standard_result = RMagic | RFailure | RNormal "'a full_total_state"

fun update_store_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> x v = ((get_store_total \<omega>)(x \<mapsto> v), get_trace_total \<omega>, get_hm_total_full \<omega>)"

lemma update_store_total_trace_same: "get_trace_total (update_store_total \<omega> x v) = get_trace_total \<omega>"
  by simp

lemma update_store_total_hm_same: "get_hm_total_full (update_store_total \<omega> x v) = get_hm_total_full \<omega>"
  by simp

lemma update_store_total_heap_same: "get_heap_total_full (update_store_total \<omega> x v) = get_heap_total_full \<omega>"
  by simp

lemma update_store_total_mask_same: "get_mask_total_full (update_store_total \<omega> x v) = get_mask_total_full \<omega>"
  by simp

definition update_heap_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_heap_total mh l v = Abs_total_state ((get_mask_total mh), (get_heap_total mh)(l := v))"

definition update_mask_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mask_total mh m' = Abs_total_state (m', get_heap_total mh)"

lemma Abs_total_state_inverse_2:
  assumes "wf_pre_total_state (m,h)"
  shows "Rep_total_state (Abs_total_state (m,h)) = (m,h)"
  using assms Abs_total_state_inverse
  by blast

lemma get_update_mask_total: 
  assumes "wf_mask_simple m0"
  shows   "get_mask_total (update_mask_total mh m0) = m0"
  unfolding update_mask_total_def
  using assms
  by (simp add: Abs_total_state_inverse_2)

lemma update_mask_total_multiple: 
  assumes "wf_mask_simple m0" and "wf_mask_simple m2"
  shows   "update_mask_total (update_mask_total mh m0) m1 = update_mask_total mh m1"
  unfolding update_mask_total_def  
  using assms
  by (simp add: Abs_total_state_inverse_2)

lemma update_heap_total_mask_same: "get_mask_total (update_heap_total \<phi> l v) = get_mask_total \<phi>"
  unfolding update_heap_total_def
  by (metis Abs_total_state_inverse_2 fst_conv get_mask_total.simps get_mask_total_wf wf_pre_total_state.simps)

lemma Rep_total_state_inj: "Rep_total_state a = Rep_total_state b \<Longrightarrow> a = b"
  by (metis Rep_total_state_inverse)

lemma update_heap_total_overwrite: "update_heap_total (update_heap_total mh l v1) l v2 = update_heap_total mh l v2"
  apply (rule total_state_eq)
   apply (simp only: update_heap_total_mask_same)
  by (metis Abs_total_state_inverse_2 fun_upd_upd get_heap_total.simps get_mask_total_wf snd_conv update_heap_total_def wf_pre_total_state.simps)

lemma update_heap_total_lookup_1: "get_heap_total (update_heap_total \<phi> l v) l = v"
  by (metis (no_types, lifting) Abs_total_state_inverse_2 fun_upd_eqD fun_upd_triv get_heap_total.simps get_mask_total_wf snd_conv update_heap_total_def wf_pre_total_state.simps)

lemma update_heap_total_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_heap_total (update_heap_total \<phi> l1 v) l2 = get_heap_total \<phi> l2"
  by (metis (no_types, lifting) Abs_total_state_inverse_2 fun_upd_idem_iff fun_upd_triv fun_upd_twist get_heap_total.elims get_mask_total_wf sndI update_heap_total_def wf_pre_total_state.simps)

fun update_heap_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_heap_total_full \<omega> l v = (get_store_total \<omega>, get_trace_total \<omega>, update_heap_total (get_hm_total_full \<omega>) l v )"

lemma update_heap_total_full_lookup_1: "get_heap_total_full (update_heap_total_full \<phi> l v) l = v"
  by (metis get_heap_total_full.simps get_hm_total_full.simps snd_conv update_heap_total_full.simps update_heap_total_lookup_1)

lemma update_heap_total_full_lookup_2: "l1 \<noteq> l2 \<Longrightarrow> get_heap_total_full (update_heap_total_full \<phi> l1 v) l2 = get_heap_total_full \<phi> l2"
  by (metis get_heap_total_full.simps get_hm_total_full.simps snd_conv update_heap_total_full.simps update_heap_total_lookup_2)

lemma update_heap_total_overwrite_full: "update_heap_total_full (update_heap_total_full \<omega> l v1) l v2 = update_heap_total_full \<omega> l v2"
  apply (rule full_total_state_eq)
     apply simp
    apply simp
   apply (simp add: update_heap_total_overwrite)
  by (metis get_hm_total_full.elims get_mask_total_full.elims snd_conv update_heap_total_full.simps update_heap_total_mask_same)
  
fun update_mask_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mask_total_full \<omega> m = (get_store_total \<omega>, get_trace_total \<omega>, update_mask_total (get_hm_total_full \<omega>) m)"

lemma update_heap_total_full_mask_same: "get_mask_total_full (update_heap_total_full \<omega> l v) = get_mask_total_full \<omega>"
  by (metis get_hm_total_full.simps get_mask_total_full.simps snd_conv update_heap_total_full.simps update_heap_total_mask_same)

lemma get_update_mask_total_full: 
  assumes "wf_mask_simple m0"
  shows   "get_mask_total_full (update_mask_total_full mh m0) = m0"
  using assms get_update_mask_total
  by auto

lemma update_mask_total_full_same:
  "(update_mask_total_full \<omega> (get_mask_total_full \<omega>)) = \<omega>"
  by (simp add: update_mask_total_def Rep_total_state_inverse)

lemma update_mask_total_same_heap: 
  assumes "wf_mask_simple m"
  shows "get_heap_total (update_mask_total \<phi> m) = get_heap_total \<phi>"
  unfolding update_mask_total_def
  using assms
  by (simp add: Abs_total_state_inverse)

lemma update_mask_total_full_same_heap: 
  assumes "wf_mask_simple m"
  shows "get_heap_total_full (update_mask_total_full \<phi> m) = get_heap_total_full \<phi>"
  using assms update_mask_total_same_heap
  by auto
  
lemma update_mask_total_full_multiple: 
  assumes "wf_mask_simple m0"
  shows   "update_mask_total_full (update_mask_total_full \<omega> m0) m1 = update_mask_total_full \<omega> m1"
  using assms
  using update_mask_total_multiple by fastforce  

definition singleton_total_pred :: "heap_loc \<Rightarrow> (prat \<Rightarrow> 'a val \<Rightarrow> bool) \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_pred l P \<sigma> \<tau> = { (\<sigma>, \<tau>, Abs_total_state (m,h)) |m h. P (m l) (h l)}"

(*
lemma singleton_total_pred_sat: 
  assumes "\<omega> \<in> singleton_total_pred l P \<sigma> \<tau>"
  shows "P ( (get_mask_total_full \<omega>) l) ((get_heap_total_full \<omega>) l)"
proof -
  obtain \<sigma> \<tau> \<phi> where "\<omega> = (\<sigma>,\<tau>,\<phi>)"
    using prod_cases3 by blast
  with assms have "P ((get_mask_total \<phi>) l) ((get_heap_total \<phi>) l)"
    
  from assms 
  have 
  show ?thesis
    apply simp
    apply clarify
*)

(*
definition singleton_total :: "bool \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a val \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total havoc_new l p v \<sigma> \<tau> = singleton_total_pred l (\<lambda> p' v'. p = p' \<and> (\<not>havoc_new \<longrightarrow> v = v')) \<sigma> \<tau>"
*)

definition singleton_total :: "bool \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a val \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total havoc_new l p v \<sigma> \<tau> = 
           { \<omega> | \<omega>. get_store_total \<omega> = \<sigma> \<and> get_trace_total \<omega> = \<tau> \<and> 
                    get_mask_total_full \<omega> = (zero_mask(l := p)) \<and> (\<not>havoc_new \<longrightarrow> get_heap_total_full \<omega> l = v)}"

definition singleton_total_wildcard :: "bool \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_wildcard havoc_new l v \<sigma> \<tau> =
           { \<omega> | \<omega> p. p \<noteq> pnone \<and> get_store_total \<omega> = \<sigma> \<and> get_trace_total \<omega> = \<tau> \<and> 
                    get_mask_total_full \<omega> = (zero_mask(l := p)) \<and> (\<not>havoc_new \<longrightarrow> get_heap_total_full \<omega> l = v)}"

(*

lemma single_total_havoc_false_plus:
"plus_total_full_set {\<omega>} (singleton_total False hl p v \<sigma> \<tau>) = { update_mask_total_full \<omega> (\<lambda>hl. p) }" (is "?A = ?B")
proof 
  show "?A \<subseteq> ?B"
  proof
    fix \<omega>'
    assume "\<omega>' \<in> plus_total_full_set {\<omega>} (singleton_total False hl p v \<sigma> \<tau>)"
    from this obtain \<omega>r where "\<omega> |\<oplus>|\<^sub>t \<omega>r = Some \<omega>'" and ElemSingle:"\<omega>r \<in> singleton_total False hl p v \<sigma> \<tau>"
      unfolding plus_total_full_set_def
      by auto
    from ElemSingle have "get_total_
*)    



definition singleton_total_only_mask :: "heap_loc \<Rightarrow> prat \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_only_mask l p \<sigma> \<tau> = singleton_total_pred l (\<lambda> p' v'. p = p') \<sigma> \<tau>"
(*
fun map_result :: "(('a full_total_state) \<Rightarrow> 'a result) \<Rightarrow> 'a result \<Rightarrow> 'a result"
  where 
    "map_result f Failure = Failure"
  | "map_result f (Set xs) = (if \<exists>x \<in> xs. f x = Failure then Failure else Set (\<Union>x \<in> xs. select_set (f x))) "
*)

fun map_result_2 :: "(mask \<Rightarrow> (mask set) option) \<Rightarrow> (mask set) option \<Rightarrow> (mask set) option"
  where 
    "map_result_2 f None = None"
  | "map_result_2 f (Some xs) = (if \<exists>x \<in> xs. f x = None then None else Some (\<Union>x \<in> xs. the (f x))) "


fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"



(*
definition inhale_perm :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a total_state set"
  where "inhale_perm \<phi> l p = {\<phi>'| \<phi>'. 
                wf_mask_simple (get_mask_total \<phi>') \<and> 
                (get_mask_total \<phi>') = (get_mask_total \<phi>)(l := padd p (get_mask_total \<phi> l)) \<and>
                if (get_mask_total \<phi> l) > pnone then (get_heap_total \<phi>') = get_heap_total \<phi> else \<exists>v. }"
*)
(*
definition inhale_perm :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a total_state set"
  where "inhale_perm \<omega> l p = 
      {\<omega>'| \<omega>'. get_mask_total_full \<omega> = (get_mask_total_full \<omega>)[l := (get_mask_total_full \<omega>)+p]}"
*)

fun option_fold :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "option_fold f e (Some x) = f x"
  | "option_fold f e None = e"

definition inhale_perm_single :: "bool \<Rightarrow>'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> prat option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single havoc_new \<omega> l p_opt =
      {\<omega>'| \<omega>' q v. get_store_total \<omega>' = get_store_total \<omega> \<and>
               get_trace_total \<omega>' = get_trace_total \<omega> \<and>
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mask_total_full \<omega> l) q) \<and>
               get_mask_total_full \<omega>' = (get_mask_total_full \<omega>)(l := (padd (get_mask_total_full \<omega> l) q)) \<and>               
               get_heap_total_full \<omega>' =
                   (if havoc_new \<and> (get_mask_total_full \<omega> l) = pnone then 
                      (get_heap_total_full \<omega>)(l := v) 
                    else
                       get_heap_total_full \<omega>)
       }"


inductive red_inhale :: "program \<Rightarrow> 'a interp \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow>  'a standard_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and havoc_new :: bool
  where 
  (** sep. conj **)
   InhSepNormal: 
   "\<lbrakk> red_inhale Pr \<Delta> havoc_new inh_assume A \<omega> (RNormal \<omega>''); 
      red_inhale Pr \<Delta> havoc_new inh_assume B \<omega>'' res\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (A && B) \<omega> res"
 | InhSepFailureMagic: 
   "\<lbrakk> red_inhale Pr \<Delta> havoc_new inh_assume A \<omega> resA; 
      resA = RFailure \<or> resA = RMagic \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (A && B) \<omega> resA"
  (** if-else **)
 | InhImpTrue: 
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_inhale Pr \<Delta> havoc_new inh_assume A \<omega> res \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (Imp e A) \<omega> res" 
 | InhImpFalse:  
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> havoc_new inh_assume (Imp e A) \<omega> (RNormal \<omega>)"
 | InhImpFailure: 
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow> 
     red_inhale Pr \<Delta> havoc_new inh_assume (Imp e A) \<omega>  RFailure"
(** inhale/assume acc(e.f, p) **) (* Pr, \<Delta> \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l) *)
(* \<omega>' \<in> plus_total_full_set {\<omega>} 
                        ((singleton_total havoc_new (a,f) (Abs_prat p) (get_heap_total_full \<omega> (a,f)) (get_store_total \<omega>) (get_trace_total \<omega>)))*)
 | InhAcc: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); p \<ge> 0; 
       wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>;
       \<omega>' \<in> inhale_perm_single havoc_new \<omega> (a,f) (Some (Abs_prat p))\<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> havoc_new False (Atomic (Acc e_r f e_p)) \<omega> (RNormal \<omega>')"
 | AssumeAcc: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a))); 
       Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p)); 
       p \<ge> 0; 
       wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega> \<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> havoc_new True (Atomic (Acc e_r f e_p)) \<omega> (if ((Rep_prat (get_mask_total_full \<omega> (a,f))) \<ge> p) then RNormal \<omega> else RMagic)"
 | InhAssumeAccFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (Acc e_r f e_p)) \<omega> RMagic"
 | InhAssumeAccFail2: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
      (\<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> p < 0)\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (Acc e_r f e_p)) \<omega> RFailure"
(** inhale/assume acc(e.f, wildcard) **)
(*  \<omega>' \<in> plus_total_full_set {\<omega>} 
        singleton_total_wildcard havoc_new (r,f) (get_heap_total_full \<omega> (r,f)) (get_store_total \<omega>) (get_trace_total \<omega>)) *)
 | InhAccWildcard: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       (wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>);
       \<omega>' \<in> inhale_perm_single havoc_new \<omega> (a,f) None \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> havoc_new False (Atomic (AccWildcard e_r f)) \<omega> (RNormal \<omega>')"
(* incorrect semantics of assume, since assume A && B is not the same as assume A; assume B *)
 | AssumeAccWildcard: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
      (wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>) \<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> havoc_new True (Atomic (AccWildcard e_r f)) \<omega> (if (pgt (get_mask_total_full \<omega> (a,f)) pnone) then RNormal \<omega> else RMagic)"
  | InhAssumeAccWildcardFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
    red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (AccWildcard e_r f)) \<omega> RMagic"
 | InhAssumeAccWildcardFail2: 
     "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); 
        Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (AccWildcard e_r f)) \<omega> RFailure"
(** others **)
 | InhInhaleExhale: 
    "\<lbrakk> red_inhale Pr \<Delta> havoc_new inh_assume A \<omega> res \<rbrakk> \<Longrightarrow> 
       red_inhale Pr \<Delta> havoc_new inh_assume (InhaleExhale A B) \<omega> res"
  | InhPureNormalMagic: 
    "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>;  
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"
  | InhPureFail: 
    "\<lbrakk> \<not>wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (Pure e)) \<omega> RFailure"

lemma AssumeAccNormal:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a)))" and
          "Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VPerm p))" and
          "p \<ge> 0" and
          "(wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>)" and
          "(wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>)" and
          "((Rep_prat (get_mask_total_full \<omega> (a,f))) \<ge> p)"
        shows  "red_inhale Pr \<Delta> havoc_new True (Atomic (Acc e_r f e_p)) \<omega> (RNormal \<omega>)"
  using AssumeAcc[OF assms(1-5)] assms(6)
  by presburger

lemma AssumeAccWildcardNormal:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VRef (Address a)))" and
          "(wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>)" and
          "pgt (get_mask_total_full \<omega> (a,f)) pnone"
  shows  "red_inhale Pr \<Delta> havoc_new True (Atomic (AccWildcard e_r f)) \<omega> (RNormal \<omega>)"
  using AssumeAccWildcard[OF assms(1-2)] assms(3)
  by presburger

lemma InhPureNormal:
  assumes "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and
          "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        shows "red_inhale Pr \<Delta> havoc_new inh_assume (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using InhPureNormalMagic[OF assms]
  by simp

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {l |l. pgt (get_mask_total_full \<omega> l) pnone}"

(*
fun handle_exhale_2 :: "program \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> mask \<Rightarrow> (mask set) option"
  where
    "handle_exhale_2 Pr \<omega>_orig (A && B) m = 
       map_result_2 (handle_exhale_2 Pr \<omega>_orig B) (handle_exhale_2 Pr \<omega>_orig A m)"
  | "handle_exhale_2 Pr \<omega>_orig (Imp e A) m = 
       (if (red_pure_exp_total Pr e (update_mask_total_full \<omega>_orig m)) = VBool True then (handle_exhale_2 Pr \<omega>_orig A m) else Some {m})"
  | "handle_exhale_2 Pr \<omega>_orig (Atomic (Acc e_r f e_p)) m = 
       (let \<omega> = (update_mask_total_full \<omega>_orig m);
            a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>)) 
        in            
            if (p \<ge> 0 \<and> (wd_pure_exp_total Pr (CExhale (get_valid_locs \<omega>_orig)) e_r \<omega>) \<and> a_opt \<noteq> None) \<and> pgte (get_mask_total_full \<omega> ((the a_opt),f) ) (Abs_prat p) then            
             Some  { ( m(((the a_opt),f) := Abs_prat ( (Rep_prat (m((the a_opt, f)))) - p)) ) }
            else 
             None)     
      "
  | "handle_exhale_2 Pr \<omega>_orig (Atomic (AccWildcard e_r f)) m =
       (let \<omega> = (update_mask_total_full \<omega>_orig m);
            a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>);
            cur_p = m(the a_opt, f)
        in 
          if ((wd_pure_exp_total Pr (CExhale (get_valid_locs \<omega>)) e_r \<omega>) \<and> a_opt \<noteq> None) \<and> pgt cur_p pnone then
             Some {m((the a_opt,f) := Abs_prat((Rep_prat cur_p) - p'))| p'. p' > 0 \<and> p' < Rep_prat cur_p}
          else None)"
  | "handle_exhale_2 Pr \<omega>_orig (InhaleExhale A B) m = handle_exhale_2 Pr \<omega>_orig B m"
  | "handle_exhale_2 Pr \<omega>_orig (Atomic (Pure e)) m =
         (let \<omega> = (update_mask_total_full \<omega>_orig m) in
          (if wd_pure_exp_total Pr (CExhale (get_valid_locs \<omega>)) e \<omega> \<and> (un_VBool (red_pure_exp_total Pr e \<omega>)) then 
              Some {m}
          else None))"
  | "handle_exhale_2 Pr \<omega>_orig (ForAll v va) \<omega> = undefined"
  | "handle_exhale_2 Pr \<omega>_orig (Atomic (AccPredicate va vb vc)) \<omega> = undefined"
  | "handle_exhale_2 Pr \<omega>_orig (Atomic (AccPredicateWildcard va vb)) \<omega> = undefined"
  | "handle_exhale_2 Pr \<omega>_orig (A --* B) \<omega> = undefined"
*)

datatype exhale_result = ExhaleNormal mask | ExhaleFailure

inductive red_exhale :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> mask \<Rightarrow> exhale_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and \<omega>0 :: "'a full_total_state"
  where 

\<comment>\<open>exhale A && B\<close>
   ExhSepNormal: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A \<omega> (ExhaleNormal m''); 
      red_exhale Pr \<Delta> \<omega>0 B m'' res\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m res"
 | ExhSepFailureMagic: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A m ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m ExhaleFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
 | ExhImpTrue: 
   "\<lbrakk> \<omega> = update_mask_total_full \<omega>_orig m;
      wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>0)) e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_exhale Pr \<Delta> \<omega>0 A m res \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Imp e A) m res" 
 | ExhImpFalse:  
   "\<lbrakk> \<omega> = update_mask_total_full \<omega>_orig m;
      wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>0)) e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_exhale Pr \<Delta> \<omega>0 (Imp e A) m (ExhaleNormal m)"
 | ExhImpFailure:
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>0)) e (update_mask_total_full \<omega>_orig m) \<rbrakk> \<Longrightarrow> 
     red_exhale Pr \<Delta> \<omega>0 (Imp e A) m ExhaleFailure"

\<comment>\<open>exhale acc(e.f, p)\<close>
 | ExhAcc: 
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       p \<ge> 0; 
       pgte (m(a,f)) (Abs_prat p);
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_p \<omega>;
       m' = m( (a,f) := Abs_prat ( (Rep_prat (m((a, f)))) - p) ) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f e_p)) m (ExhaleNormal m')"
  | ExhAccFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
      (r = Null \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega> \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_p \<omega> \<or> p < 0)\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f e_p)) m ExhaleFailure"
  | ExhAccFail2:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_p \<omega>;
       p \<ge> 0; 
       \<not> (pgte (m(a,f)) (Abs_prat p)) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f e_p)) m ExhaleFailure"

\<comment>\<open>exhale acc(e.f, wildcard)\<close>
 \<comment>\<open>Exhaling wildcard removes some non-zero permission this is less than the current permission held\<close>
  | ExhAccWildcard:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       p > 0; 
       pgt (m(a,f)) (Abs_prat p);
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       m' = m( (a,f) := Abs_prat ( (Rep_prat (m((a, f)))) - p) ) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (AccWildcard e_r f)) m (ExhaleNormal m')"
  | ExhAccWildcardFail1:
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
      (r = Null \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>)\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (AccWildcard e_r f)) m ExhaleFailure"
  | ExhAccWildcardFail2:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       (m(a,f)) = pnone \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (AccWildcard e_r f)) m ExhaleFailure"
 
\<comment>\<open>exhale other cases\<close>
  | ExhInhaleExhale: 
    "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 B \<omega> res \<rbrakk> \<Longrightarrow> 
       red_exhale Pr \<Delta> \<omega>0 (InhaleExhale A B) m res"  
  | ExhPure:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m; 
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>;  
       Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Pure e)) m (if b then ExhaleNormal m else ExhaleFailure)"
  | ExhPureFail:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m; 
       \<not> (wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega>) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Pure e)) m ExhaleFailure"

record conf =
  havoc_inhale :: bool


(* alternative:
definition havoc_undef_locs :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state set"
  where "havoc_undef_locs \<omega> m = {\<omega>'| \<omega>'. \<forall>l. pgt (m l) pnone \<longrightarrow> get_heap_total_full \<omega> l = get_heap_total_full \<omega>' l}"
*)
definition havoc_undef_locs :: "'a total_heap \<Rightarrow> mask \<Rightarrow> 'a total_heap set"
  where "havoc_undef_locs h m = {h' | h'. \<forall>l. pgt (m l) pnone \<longrightarrow> h' l = h l}"

definition exhale_state :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state set"
  where "exhale_state \<omega> m = {\<omega>' | \<omega>'. get_store_total \<omega>' = get_store_total \<omega> \<and>
                                      get_trace_total \<omega>' = get_trace_total \<omega> \<and>
                                      get_mask_total_full \<omega>' = m \<and>
                                      get_heap_total_full \<omega>' \<in> havoc_undef_locs (get_heap_total_full \<omega>) m}"


fun map_option_2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
  where 
    "map_option_2 f y None = y"
  | "map_option_2 f _ (Some x) = f x"
      

(* Currently, red_stmt_total_single is a function. But if angelism is added, then it would not be a 
function *) (* inhale (acc(x.f) && x.f = 5 \<Longrightarrow> 0/0 = 0/0) *)
inductive red_stmt_total_single_set :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> (stmt+unit) \<times> ('a standard_result) \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and conf :: conf where
   RedSkip: " red_stmt_total_single_set Pr \<Delta> conf Skip \<omega> (Inr (), RNormal \<omega>)" 
 | RedInhale: 
   "\<lbrakk> red_inhale Pr \<Delta> (havoc_inhale conf) False A \<omega> res \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Inhale A) \<omega> (Inr (), res)"
 | RedExhale: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) (ExhaleNormal m');
      \<omega>' \<in> exhale_state \<omega> m' \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Exhale A) \<omega> (Inr (), RNormal \<omega>')"
 | RedExhaleFailure:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Exhale A) \<omega> (Inr (), RFailure)"
 | RedAssert:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) (ExhaleNormal m') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Assert A) \<omega> (Inr (), RNormal \<omega>)"
 | RedAssertFailure:
   "\<lbrakk> red_exhale Pr \<Delta> \<omega> A (get_mask_total_full \<omega>) ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Assert A) \<omega> (Inr (), RFailure)"
\<comment>\<open>TODO: Add semantics for \<^term>\<open>Assume A\<close>. Should be the same as \<^term>\<open>Assert A\<close>, except that 
        \<^term>\<open>Assert A\<close> goes to failure iff \<^term>\<open>Assume A\<close> goes to magic. The back-ends implement it
        differently correctly. \<close>
 (*| RedAssume: "red_stmt_total_single_set Pr conf (Assume A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) True A \<omega>))"*)
(* | RedExhale: "red_stmt_total_single_set Pr conf (Exhale A) \<omega> 
                     (Inr (), map_option_2 (\<lambda>xs. Set (\<Union>m \<in> xs. exhale_state \<omega> m)) Failure (handle_exhale_2 Pr \<omega> A (get_total_mask_full \<omega>)))"*)
 | RedLocalAssign:
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<rbrakk> \<Longrightarrow> 
     red_stmt_total_single_set Pr \<Delta> conf (LocalAssign x e) \<omega> (Inr (), (RNormal (update_store_total \<omega> x v)))"
 | RedLocalAssignFailure: 
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow> 
   red_stmt_total_single_set Pr \<Delta> conf (LocalAssign x e) \<omega> (Inr (), RFailure)"
 | RedFieldAssign: 
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>; 
      wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr));
      get_mask_total_full \<omega> (addr,f) \<noteq> pnone;
      Pr, \<Delta>  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> conf (FieldAssign e_r f e) \<omega> (Inr (), (RNormal (update_heap_total_full \<omega> (addr,f) v)))"
 | RedFieldAssignFailure: 
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> 
      \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<or> 
      (Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null)) \<or> 
      get_mask_total_full \<omega> (addr,f) \<noteq> pnone \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> conf (FieldAssign e_r f e) \<omega> (Inr (), RFailure)"
 | RedIfTrue: 
   "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> conf (If e_b s1 s2) \<omega> (Inl s1, RNormal \<omega>)"
 | RedIfFalse: 
   "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
      wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow> 
      red_stmt_total_single_set Pr \<Delta> conf (If e_b s1 s2) \<omega> (Inl s2, RNormal \<omega>)"
 | RedIfFailure:
    "\<lbrakk> \<not>wd_pure_exp_total Pr \<Delta> CInhale e_b \<omega> \<rbrakk> \<Longrightarrow>
       red_stmt_total_single_set Pr \<Delta> conf (If e_b s1 s2) \<omega> (Inr (), RFailure)"
 | RedSeq1:
   "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: 
   "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
      red_stmt_total_single_set Pr \<Delta> conf (Seq s1 s2) \<omega> (Inl s2, r'')"

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a standard_result"

inductive red_stmt_total_single :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where 
    NormalSingleStep: "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s \<omega> res \<rbrakk> \<Longrightarrow> 
       red_stmt_total_single Pr \<Delta> conf ((Inl s, RNormal \<omega>)) res"

abbreviation red_stmt_total_multi :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "red_stmt_total_multi Pr \<Delta> conf \<equiv> rtranclp (red_stmt_total_single Pr \<Delta> conf)"

definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_mask_total_full \<omega> = zero_mask"

fun is_failure_config :: "'a stmt_config \<Rightarrow> bool"
  where "is_failure_config config \<longleftrightarrow> (snd config) = RFailure"

fun is_normal_config :: "'a stmt_config \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "is_normal_config config \<omega> \<longleftrightarrow> (snd config) = RNormal \<omega>"

(* todo: incorporate precondition *)
(* first argument is just there to fix 'a *)
definition stmt_verifies_total :: "'a \<Rightarrow> program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow>  bool"
  where "stmt_verifies_total dummy Pr \<Delta> conf s \<equiv> 
         \<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
           red_stmt_total_multi Pr \<Delta> conf ((Inl s, RNormal \<omega>)) r \<longrightarrow> \<not>is_failure_config r"


subsection \<open>Havoc at exhale is sufficient\<close>

definition equal_on_mask :: "mask \<Rightarrow> 'a total_heap \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "equal_on_mask m h1 h2 \<equiv> \<forall> l. m(l) \<noteq> pnone \<longrightarrow> h1(l) = h2(l)"

lemma equal_on_mask_refl: "equal_on_mask m h h"
  by (simp add: equal_on_mask_def)

type_synonym 'a simulation_rel = "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"

(*
lemma havoc_equiv:
  assumes "stmt_verifies_total dummy Pr \<lparr>havoc_inhale = false\<rparr> s"
  shows "stmt_verifies_total dummy Pr \<lparr>havoc_inhale = true\<rparr> s"
  oops
*)

subsection \<open>Backwards simulation\<close>

(*definition lift_simulation_rel :: "'a simulation_rel \<Longrightarrow> *)

definition lift_sim_rel :: "'a simulation_rel \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "lift_sim_rel R w1 w2 \<equiv>
            (is_failure_config w1 \<and> is_failure_config w2 \<and> fst w1 = fst w2) \<or>
            (\<exists>\<omega>1 \<omega>2. is_normal_config w1 \<omega>1 \<and> is_normal_config w2 \<omega>2 \<and> R \<omega>1 \<omega>2 \<and> fst w1 = fst w2)"

lemma lift_sim_rel_fail: "lift_sim_rel R w1 w2 \<Longrightarrow> is_failure_config w1 \<Longrightarrow> is_failure_config w2"
  by (simp add: lift_sim_rel_def)

lemma lift_sim_rel_fail_2: "lift_sim_rel R w1 w2 \<Longrightarrow> is_failure_config w1 \<Longrightarrow> fst w1 = fst w2 \<and> snd w2 = RFailure"
  by (simp add: lift_sim_rel_def)

lemma lift_sim_rel_fail_3: "lift_sim_rel R w1 w2 \<Longrightarrow> w1 = (Inr (), RFailure) \<Longrightarrow> w2 = (Inr (), RFailure)"
  unfolding lift_sim_rel_def
  by (metis is_failure_config.elims(2) is_failure_config.elims(3) lift_sim_rel_def lift_sim_rel_fail prod.exhaust_sel snd_conv)

lemma lift_sim_rel_normal: "lift_sim_rel R w1 w2 \<Longrightarrow> is_normal_config w1 \<omega>1 \<Longrightarrow> 
                              fst w1 = fst w2 \<and> (\<exists>\<omega>2. is_normal_config w2 \<omega>2 \<and> R \<omega>1 \<omega>2)"
  unfolding lift_sim_rel_def by auto

lemma lift_sim_rel_not_magic: "lift_sim_rel R w1 w2 \<Longrightarrow> snd w1 \<noteq> RMagic \<and> snd w2 \<noteq> RMagic"
  unfolding lift_sim_rel_def by fastforce

lemma red_stmt_total_start_normal:
  assumes "red_stmt_total_single Pr \<Delta> conf w1 w2"
  shows "\<exists>\<omega>. is_normal_config w1 \<omega>"
  using assms
  by (cases) auto

lemma backwards_simulation_aux:
  assumes "red_stmt_total_multi Pr \<Delta> conf ((Inl s, RNormal \<omega>)) w" and
          single_step:"\<And> s \<omega> w' w2'. red_stmt_total_single Pr \<Delta> conf (Inl s, RNormal \<omega>) w' \<Longrightarrow> lift_sim_rel R w' w2' \<Longrightarrow>                               
                      \<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'"
 shows "\<And>w2'. lift_sim_rel R w w2' \<Longrightarrow> \<exists> \<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'"
using assms(1)
proof (induction rule: rtranclp_induct)
  case base   
    from this obtain \<omega>2' where "w2' = (Inl s, RNormal \<omega>2')" and "R \<omega> \<omega>2'"
    unfolding lift_sim_rel_def
    by (metis fstI is_failure_config.elims(2) is_normal_config.elims(2) prod.collapse snd_conv standard_result.distinct(5) standard_result.inject)
  show ?case
    apply (rule exI)
    apply (rule conjI[OF \<open>R \<omega> \<omega>2'\<close>])
    by (simp add: \<open>w2' = _\<close>)        
next
  case (step y z)
  from this obtain s'' \<omega>'' where "y = (Inl s'', RNormal \<omega>'')"
    by (meson red_stmt_total_single.cases)
  with step.hyps step.prems single_step obtain \<omega>2'' where "R \<omega>'' \<omega>2''" and
    RedW2'':"red_stmt_total_single Pr2 \<Delta> conf2 (Inl s'', RNormal \<omega>2'') w2'"
    by blast
  hence "lift_sim_rel R y (Inl s'', RNormal \<omega>2'')"
    unfolding lift_sim_rel_def
    using \<open>y = _\<close>
    by simp
  with step.IH obtain \<omega>2 where "R \<omega> \<omega>2" and 
    "red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) (Inl s'', RNormal \<omega>2'')"
    by blast
  then show ?case
    using RedW2''
    by fastforce
qed

lemma result_normal_exhaust: 
   "w \<noteq> RMagic \<Longrightarrow> w \<noteq> RFailure \<Longrightarrow> \<exists>\<omega>. w = RNormal \<omega>"
  by (cases w) auto

lemma stmt_config_normal_exhaust:
  assumes "\<not>is_failure_config w" and "snd w \<noteq> RMagic"
  shows "\<exists>\<omega>. is_normal_config w \<omega>"
proof -
  from assms have "\<exists>\<omega>. snd w = RNormal \<omega>"
    using result_normal_exhaust
    by auto
  thus ?thesis
    by simp
qed

lemma lift_total_rel:
  assumes "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'"
  shows "\<forall>w :: 'a stmt_config. snd w \<noteq> RMagic \<longrightarrow> (\<exists>w'. lift_sim_rel R w w')"
proof (rule allI, rule impI)+
  fix w :: "'a stmt_config"
  assume *:"snd w \<noteq> RMagic"
  show "\<exists>w'. lift_sim_rel R w w'"
  proof (cases "is_failure_config w")
    case False   
    from stmt_config_normal_exhaust[OF False *] obtain \<omega> where NormW:"is_normal_config w \<omega>"
      by auto
    moreover obtain \<omega>' where "R \<omega> \<omega>'" using assms 
      by blast
    show ?thesis 
      apply (rule exI[where ?x="(fst w, RNormal \<omega>')"])
      apply (unfold lift_sim_rel_def)
      using NormW \<open>R \<omega> \<omega>'\<close>
      by auto
  qed (auto simp: lift_sim_rel_def)
qed   

lemma backwards_simulation:
  assumes initial_rel: "\<And> \<omega> \<omega>2. is_empty_total \<omega> \<Longrightarrow> R \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2" and
          total_rel: "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'" and
          single_step:"\<And> s \<omega> w' w2'. red_stmt_total_single Pr \<Delta> conf (Inl s, RNormal \<omega>) w' \<Longrightarrow> lift_sim_rel R w' w2' \<Longrightarrow>                               
                      \<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2'" and
        verif:"stmt_verifies_total (dummy :: 'a) Pr2 \<Delta> conf2 s"
 shows "stmt_verifies_total (dummy :: 'a) Pr \<Delta> conf s"
  unfolding stmt_verifies_total_def    
proof ( (rule allI | rule impI) +)
  fix \<omega>::"'a full_total_state" and w'
  assume "is_empty_total \<omega>" and Red:"red_stmt_total_multi Pr \<Delta> conf (Inl s, RNormal \<omega>) w'"
  show "\<not> (is_failure_config w')"
  proof (cases "snd w' \<noteq> RMagic")
    case True
    from this obtain w2 where RelResult:"lift_sim_rel R w' w2" using lift_total_rel[OF assms(2)]
      by blast
    from this Red obtain \<omega>2 where "R \<omega> \<omega>2" and "red_stmt_total_multi Pr2 \<Delta> conf2 (Inl s, RNormal \<omega>2) w2"
      using backwards_simulation_aux single_step
      by blast
    then show ?thesis
      using verif initial_rel[OF \<open>is_empty_total \<omega>\<close> \<open>R \<omega> \<omega>2\<close>] RelResult lift_sim_rel_fail
      unfolding stmt_verifies_total_def
      by blast      
  qed (simp)
qed

definition havoc_rel :: "'a simulation_rel"
  where "havoc_rel \<omega> \<omega>' \<equiv> get_mask_total_full \<omega> = get_mask_total_full \<omega>' \<and> 
                          equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>') \<and>
                          get_store_total \<omega> = get_store_total \<omega>'"

lemma init_havoc_rel: "is_empty_total \<omega> \<Longrightarrow> havoc_rel \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2"
  by (simp add: havoc_rel_def is_empty_total_def)

lemma total_havoc_rel: "\<exists> \<omega>'. havoc_rel \<omega> \<omega>'"
  by (rule exI[where ?x=\<omega>]) (simp add: havoc_rel_def equal_on_mask_refl)

lemma havoc_rel_same_store: "havoc_rel \<omega> \<omega>' \<Longrightarrow> get_store_total \<omega> = get_store_total \<omega>'"
  by (simp add: havoc_rel_def)

lemma havoc_rel_same_mask: "havoc_rel \<omega> \<omega>' \<Longrightarrow> get_mask_total_full \<omega> = get_mask_total_full \<omega>'"
  by (simp add: havoc_rel_def)

lemma havoc_rel_refl: "havoc_rel \<omega> \<omega>"
  by (simp add: equal_on_mask_refl havoc_rel_def)

lemma havoc_rel_sym: "havoc_rel \<omega> \<omega>' \<Longrightarrow> havoc_rel \<omega>' \<omega>"
  by (simp add: havoc_rel_def equal_on_mask_def)

lemma wd_not_fail:
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>"
  shows "v \<noteq> VFailure"
  using assms
proof (induction)
  case (RedCondExpFalse Pr \<Delta> e1 \<omega> e3 r e2)
  then show ?case sorry (* need determinism *)
next
  case (RedBinopFailure Pr \<Delta> e1 \<omega> v1 e2 v2 bop)
  hence "wd_binop bop v1 v2" by simp
  then show ?case sorry
next
  case (RedOldFailure t l Pr \<Delta> e uz va)
  then show ?case sorry
next
  case (RedPropagateFailure e e' Pr \<Delta> \<omega>)
  then show ?case sorry
qed auto

lemma havoc_rel_expr_eval_same: 
  assumes "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v" and "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and "havoc_rel \<omega> \<omega>'"
  shows "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t v"
  using assms
proof (induction)
case (RedLit Pr \<Delta> l uu)
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
  case (RedVar \<sigma> n v Pr \<Delta> uv uw)
  hence "get_store_total \<omega>' = \<sigma>"
    unfolding havoc_rel_def by simp
  from this obtain \<pi> \<phi> where "\<omega>' = (\<sigma>,\<phi>,\<pi>)"
    using get_store_total.elims 
    by (metis prod.exhaust_sel)
  then show ?case using RedVar
    by (auto intro!: red_pure_exp_total.intros)
next
case (RedUnop Pr \<Delta> e \<omega> v unop v')
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
  case (RedBinopLazy Pr \<Delta> e1 \<omega> v1 bop v e2)
  then show ?case by (auto intro!: red_pure_exp_total.intros)
next
case (RedBinop Pr \<Delta> e1 \<omega> v1 e2 v2 bop v)
  then show ?case 
   by (meson red_pure_exp_total.RedBinop wd_pure_exp_total.simps(4))
next
  case (RedCondExpTrue Pr \<Delta> e1 \<omega> e2 r e3)
  then show ?case 
    by (meson red_pure_exp_total.RedCondExpTrue wd_pure_exp_total.simps(5))
next
  case (RedCondExpFalse Pr \<Delta> e1 \<omega> e3 r e2)
  then show ?case 
    sorry (* need to show determinism of expression evaluation *)
next
  case (RedPermNull Pr \<Delta> e \<omega> f)
  then show ?case by auto    
next
  case (RedResult \<sigma> v Pr \<Delta> ux uy)
  then show ?case by auto
next
  case (RedBinopRightFailure Pr \<Delta> e1 \<omega> v1 e2 bop)
  then show ?case 
    using red_pure_exp_total.RedBinopRightFailure wd_pure_exp_total.simps(4) by blast
next
  case (RedBinopFailure Pr \<Delta> e1 \<omega> v1 e2 v2 bop)
  then show ?case 
    by (meson red_pure_exp_total.RedBinopFailure wd_pure_exp_total.simps(4))
next
case (RedOldFailure t l Pr \<Delta> e uz va)
  then show ?case by auto
next
  case (RedPropagateFailure e e' Pr \<Delta> \<omega>)
  then show ?case sorry
next
  case (RedField Pr \<Delta> e \<omega> a \<phi> f v)
  thus ?case
    using red_pure_exp_total.RedField wd_pure_exp_total.simps(6) by blast
next
  case (RedPerm Pr \<Delta> e \<omega> a f)
  then show ?case
    by (metis havoc_rel_def red_pure_exp_total.RedPerm wd_pure_exp_total.simps(8))
qed

lemma havoc_rel_wd_same:
  assumes "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and "havoc_rel \<omega> \<omega>'"
  shows "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>'"
  using assms havoc_rel_sym[OF assms(2)]
  apply (induction Pr \<Delta> CInhale e \<omega> rule: wd_pure_exp_total.induct)
                apply clarsimp
               apply clarsimp
              apply clarsimp
             apply clarsimp
             apply (blast dest: havoc_rel_expr_eval_same)
            apply clarsimp
            apply (blast dest: havoc_rel_expr_eval_same)
           apply (metis havoc_rel_expr_eval_same havoc_rel_same_mask wd_pure_exp_total.simps(6))
           apply (simp add: havoc_rel_expr_eval_same havoc_rel_same_mask)
         apply clarsimp+
  done

lemma havoc_rel_backwards:
  assumes "\<omega>' \<in> inhale_perm_single True \<omega> (a, f) p_opt" and 
          "havoc_rel \<omega>' \<omega>2'"
  shows "havoc_rel \<omega> (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  using assms
proof -
  let ?m = "get_mask_total_full \<omega>"
  let ?h = "get_heap_total_full \<omega>"
  let ?m' = "get_mask_total_full \<omega>'"
  let ?h' = "get_heap_total_full \<omega>'"
  let ?h2' = "get_heap_total_full \<omega>2'"
  from \<open>havoc_rel \<omega>' \<omega>2'\<close> have "equal_on_mask ?m' ?h' ?h2'"
    using havoc_rel_def by blast

  from \<open>\<omega>' \<in> inhale_perm_single _ _ _ _\<close> obtain v q where
    AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) q))" and
    UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)" and
    SameStore: "get_store_total \<omega>' = get_store_total \<omega>"
    unfolding inhale_perm_single_def
    by auto
  
  have EqOnMask:"equal_on_mask ?m ?h ?h2'"
    unfolding equal_on_mask_def
  proof clarify
    fix hl    
    assume SomePerm:"?m hl \<noteq> pnone"
    hence "?m' hl \<noteq> pnone"
      using AddPerm padd_pos
      by auto      
    hence "?h' hl = ?h2' hl" using \<open>equal_on_mask ?m' ?h' ?h2'\<close>
      unfolding equal_on_mask_def
      by blast
    thus "?h hl = ?h2' hl" 
      using SomePerm UpdateHeap
      by (metis fun_upd_apply)      
  qed

  thus ?thesis
    unfolding havoc_rel_def
    apply (intro conjI)
      apply (metis get_mask_total_full_wf get_update_mask_total_full)
     apply (metis EqOnMask get_mask_total_full_wf update_mask_total_full_same_heap)
    apply (metis (no_types, hide_lams) SameStore \<open>havoc_rel \<omega>' \<omega>2'\<close> get_mask_total_full_wf havoc_rel_same_store old.prod.inject update_mask_total_full.simps update_mask_total_full_multiple)
    done
qed

lemma havoc_inhale_normal_rel:
  assumes "red_inhale Pr \<Delta> True inh_assume A \<omega> res" and "res = RNormal \<omega>'" and "havoc_rel \<omega>' \<omega>2'" 
  shows "red_inhale Pr \<Delta> False inh_assume A (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) (RNormal \<omega>2') \<and> havoc_rel \<omega> (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  using assms
proof (induction arbitrary: \<omega>' \<omega>2')
  case (InhSepNormal inh_assume A \<omega> \<omega>'' B res)
  thus ?case
    by (metis get_mask_total_full_wf red_inhale.InhSepNormal update_mask_total_full_multiple)
next
  case (InhImpTrue e \<omega> inh_assume A res)
  let ?\<omega>2="(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  from InhImpTrue.IH[OF \<open>res = _\<close> \<open>havoc_rel \<omega>' _\<close>] have
    A1:"red_inhale Pr \<Delta> False inh_assume A ?\<omega>2 (RNormal \<omega>2')" and
    "havoc_rel \<omega> ?\<omega>2"
    by auto
  moreover have A2:"Pr, \<Delta> \<turnstile> \<langle>e;?\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)" using InhImpTrue havoc_rel_expr_eval_same
    by blast
  show ?case
    apply (rule conjI)
     apply (rule red_inhale.InhImpTrue)
       apply (rule havoc_rel_wd_same)
        apply (rule \<open>wd_pure_exp_total Pr \<Delta> _ _ _\<close>)
       apply (rule \<open>havoc_rel \<omega> ?\<omega>2\<close>)
      apply (rule A2)
     apply (rule A1)
    apply (rule \<open>havoc_rel \<omega> ?\<omega>2\<close>)
    done
next
  case (InhImpFalse e \<omega> inh_assume A)
  hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"
    by (metis Rep_total_state_inverse get_heap_total_full.simps get_hm_total_full.simps get_hm_total_full_comp get_store_total.simps get_trace_total.simps havoc_rel_same_mask prod.exhaust_sel standard_result.inject update_mask_total_def update_mask_total_full.simps)
  from InhImpFalse have HRel:"havoc_rel \<omega> \<omega>2'" by simp
  show ?case 
    apply (rule conjI)
    apply (subst StateEq)
     apply (rule red_inhale.InhImpFalse)
       apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ _ _\<close> HRel])
     apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)\<close> \<open>wd_pure_exp_total _ _ _ _ _\<close> ])
     apply (rule HRel)
    apply (subst StateEq)
    apply (rule HRel)
    done
next
  case (InhAcc e_r \<omega> a e_p p \<omega>' f \<omega>'')
    from InhAcc have "havoc_rel \<omega>' \<omega>2'" by simp
    let ?m = "get_mask_total_full \<omega>"
    let ?h = "get_heap_total_full \<omega>"
    let ?m' = "get_mask_total_full \<omega>'"
    let ?h' = "get_heap_total_full \<omega>'"
    from \<open>\<omega>' \<in> _\<close> obtain v where
      AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) (Abs_prat p)))" and
      UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)"
      unfolding inhale_perm_single_def
      by auto

  let ?\<omega>2 = "update_mask_total_full \<omega>2' ?m"
  let ?h2 = "get_heap_total_full ?\<omega>2"
  let ?h2' = "get_heap_total_full \<omega>2'"  
  have "?h2 = ?h2'"
    using update_mask_total_full_same_heap get_mask_total_full_wf
    by blast  

  have HRel:"havoc_rel \<omega> ?\<omega>2"
    using \<open>\<omega>' \<in> _\<close> \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_backwards
    by blast

  have "red_inhale Pr \<Delta> False False (Atomic (Acc e_r f e_p)) ?\<omega>2 (RNormal \<omega>2')"
    apply rule
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
        apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>\<close> HRel]) 
       apply (rule \<open>0 \<le> p\<close>)
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
     apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>\<close> HRel])
    apply (unfold inhale_perm_single_def)
    apply rule
    apply (rule exI)+
    apply (intro conjI)
          apply (rule HOL.refl)
         apply simp
        apply simp
       apply simp
      apply (metis AddPerm fun_upd_same get_mask_total_full_wf get_update_mask_total_full wf_mask_simple_def)
     apply (metis AddPerm HRel \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_def)
    using \<open>get_heap_total_full (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = get_heap_total_full \<omega>2'\<close> apply auto
    done  
  then show ?case using HRel
    by simp
next
  case (AssumeAcc e_r \<omega> a e_p p f)
  hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"      
    by (metis havoc_rel_same_mask standard_result.distinct(3) standard_result.inject update_mask_total_full_same) 
  from AssumeAcc have HRel:"havoc_rel \<omega> \<omega>2'"
    by (metis standard_result.distinct(3) standard_result.inject)
  show ?case 
    apply (rule conjI)
    apply (subst StateEq)
     apply (rule AssumeAccNormal)
          apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_p \<omega>\<close> HRel])
        apply (rule \<open>0 \<le> p\<close>)
       apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_p \<omega>\<close> HRel])
     apply (metis AssumeAcc.prems(1) HRel havoc_rel_same_mask standard_result.distinct(3))
    apply (subst StateEq, rule HRel)
    done
next
  case (InhAccWildcard e_r \<omega> a \<omega>' f \<omega>'')
    from InhAccWildcard have "havoc_rel \<omega>' \<omega>2'" by simp
    let ?m = "get_mask_total_full \<omega>"
    let ?h = "get_heap_total_full \<omega>"
    let ?m' = "get_mask_total_full \<omega>'"
    let ?h' = "get_heap_total_full \<omega>'"
    from \<open>\<omega>' \<in> inhale_perm_single _ _ _ _\<close> obtain v p where
      AddPerm:"?m' = ?m((a,f) := (padd (?m (a,f)) p))" and
              "p \<noteq> pnone" and
      UpdateHeap:"?h' = (if ?m (a,f) = pnone then ?h((a,f) := v) else ?h)"
      unfolding inhale_perm_single_def
      by auto

  let ?\<omega>2 = "update_mask_total_full \<omega>2' ?m"
  let ?h2 = "get_heap_total_full ?\<omega>2"
  let ?h2' = "get_heap_total_full \<omega>2'"  
  have "?h2 = ?h2'"
    using update_mask_total_full_same_heap get_mask_total_full_wf
    by blast

  have HRel:"havoc_rel \<omega> ?\<omega>2"
    using \<open>\<omega>' \<in> _\<close> \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_backwards
    by blast

  have "red_inhale Pr \<Delta> False False (Atomic (AccWildcard e_r f)) ?\<omega>2 (RNormal \<omega>2')"
    apply rule
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))\<close> \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<close> HRel])
    apply (unfold inhale_perm_single_def)
    apply rule
    apply (rule exI)+
    apply (intro conjI)
          apply (rule HOL.refl)
         apply simp
        apply simp
       apply simp
       apply (rule \<open>p \<noteq> pnone\<close>)
      apply (metis AddPerm fun_upd_same get_mask_total_full_wf get_update_mask_total_full wf_mask_simple_def)
     apply (metis AddPerm HRel \<open>havoc_rel \<omega>' \<omega>2'\<close> havoc_rel_def)
    using \<open>get_heap_total_full (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = get_heap_total_full \<omega>2'\<close> apply auto
    done  
  then show ?case using HRel
    by simp
next
  case (AssumeAccWildcard e_r \<omega> a f)
    hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"      
      by (metis havoc_rel_same_mask standard_result.distinct(3) standard_result.inject update_mask_total_full_same) 
    from AssumeAccWildcard have HRel:"havoc_rel \<omega> \<omega>2'"
      by (metis standard_result.distinct(3) standard_result.inject)
    show ?case
      apply (rule conjI)
      apply (subst StateEq)
       apply (rule AssumeAccWildcardNormal)
         apply (rule havoc_rel_expr_eval_same[OF \<open>Pr, \<Delta> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
        apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
       apply (metis AssumeAccWildcard.prems(1) HRel havoc_rel_same_mask standard_result.distinct(3))
      apply (subst StateEq, rule HRel)
      done
next
  case (InhInhaleExhale inh_assume A \<omega> res B)
  then show ?case 
    using red_inhale.InhInhaleExhale by blast
next
  case (InhPureNormalMagic e \<omega> b inh_assume)
  hence StateEq:"(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = \<omega>2'"      
    by (metis havoc_rel_same_mask standard_result.distinct(3) standard_result.inject update_mask_total_full_same) 
  from InhPureNormalMagic have HRel:"havoc_rel \<omega> \<omega>2'"
    by (metis standard_result.distinct(3) standard_result.inject)
  show ?case
    apply (rule conjI)
    apply (subst StateEq)
     apply (rule InhPureNormal)
      apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
     apply (rule havoc_rel_expr_eval_same[OF _ \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
    using \<open>Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> InhPureNormalMagic.prems(1) standard_result.distinct(3)
    apply (simp split: if_split_asm)
    apply (subst StateEq, rule HRel)
    done
qed (auto)

method inh_fail_basic_tac for \<omega> :: "'a full_total_state" uses local_assms intro = 
  (rule exI[where ?x=\<omega>], 
   rule conjI[OF havoc_rel_refl],
   insert local_assms,
   blast intro!:intro)

lemma havoc_inhale_failure_rel:
  assumes "red_inhale Pr \<Delta> True inh_assume A \<omega> res" and "res = RFailure"
  shows "\<exists> \<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_inhale Pr \<Delta> False inh_assume A \<omega>2 RFailure"
  using assms
proof (induction)
  case (InhSepNormal inh_assume A \<omega> \<omega>A B res)
  from this obtain \<omega>B where
     "havoc_rel \<omega>A \<omega>B" and "red_inhale Pr \<Delta> False inh_assume B \<omega>B RFailure"
    by auto
  thus ?case
    using havoc_inhale_normal_rel InhSepNormal.hyps(1) red_inhale.InhSepNormal by blast
next
  case (InhSepFailureMagic inh_assume A \<omega> resA B)
  then show ?case 
    using red_inhale.InhSepFailureMagic by blast
next
  case (InhImpTrue e \<omega> inh_assume A res)
  then show ?case 
    by (meson InhImpFailure havoc_rel_expr_eval_same red_inhale.InhImpTrue)
next
  case (InhImpFailure e \<omega> inh_assume A)
  then show ?case 
  by (meson havoc_rel_sym havoc_rel_wd_same red_inhale.InhImpFailure total_havoc_rel)
next
  case (AssumeAcc e_r \<omega> a e_p p f)
  then show ?case by (simp split: if_split_asm)
next
case (InhAssumeAccFail2 e_r \<omega> a e_p p inh_assume f)
  show ?case 
    by (inh_fail_basic_tac \<omega> local_assms:local.InhAssumeAccFail2 intro: red_inhale.InhAssumeAccFail2)
next
case (AssumeAccWildcard e_r \<omega> a f)
  then show ?case by (simp split: if_split_asm)
next
  case (InhAssumeAccWildcardFail2 e_r \<omega> a e_p p inh_assume f)
    show ?case 
     by (inh_fail_basic_tac \<omega> local_assms:local.InhAssumeAccWildcardFail2 intro: red_inhale.InhAssumeAccWildcardFail2)   
next
  case (InhInhaleExhale inh_assume A \<omega> res B)
  then show ?case
  using red_inhale.InhInhaleExhale by blast
next
  case (InhPureNormalMagic e \<omega> b inh_assume)
  then show ?case by (simp split: if_split_asm)
next
  case (InhPureFail e \<omega> inh_assume)
  show ?case 
    by (inh_fail_basic_tac \<omega> local_assms:local.InhPureFail intro: red_inhale.InhPureFail)
qed auto

lemma havoc_rel_store_update:
  assumes "havoc_rel (update_store_total \<omega> x v) \<omega>1"
  shows "\<exists>\<omega>2. \<omega>1 = update_store_total \<omega>2 x v"
  using assms
  unfolding havoc_rel_def
  by (metis Rep_total_state_inverse fstI fun_upd_same fun_upd_triv get_heap_total_full.simps get_hm_total_full_comp update_mask_total_def update_mask_total_full.simps update_mask_total_full_same update_store_total.elims)

lemma havoc_rel_store_update_3:
  assumes "havoc_rel (update_store_total \<omega> x v) \<omega>2'"
  shows "\<exists>\<omega>2. \<omega>2' = update_store_total \<omega>2 x v \<and> havoc_rel \<omega> \<omega>2"
proof -
  from assms obtain \<omega>2_first where "\<omega>2' = update_store_total \<omega>2_first x v" 
    using havoc_rel_store_update by blast
  hence *:"get_mask_total_full \<omega>2' = get_mask_total_full \<omega>2_first"
    by (simp add: update_store_total_mask_same)
  have **:"equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>2_first)"
    using assms \<open>\<omega>2' = _\<close> update_store_total_heap_same update_store_total_mask_same
    unfolding havoc_rel_def
    by fastforce
 
  let ?\<omega>2 = "(get_store_total \<omega>, get_trace_total \<omega>2_first, get_hm_total_full \<omega>2_first)"
  have "havoc_rel \<omega> ?\<omega>2"
    unfolding havoc_rel_def
    apply (intro conjI)
       using * assms havoc_rel_same_mask apply fastforce
     using ** apply simp
    apply simp
    done

  show ?thesis
    apply (rule exI[where ?x="?\<omega>2"])
    apply (rule conjI)
     apply (rule full_total_state_eq)
        using \<open>\<omega>2' = _\<close>
        apply (metis Pair_inject assms havoc_rel_same_store update_mask_total_full.simps update_mask_total_full_same update_store_total.simps)
       apply (simp add: \<open>\<omega>2' = _\<close>)
      apply (simp add: \<open>\<omega>2' = _\<close>)
     apply (metis \<open>havoc_rel \<omega> _\<close> assms havoc_rel_same_mask update_store_total_mask_same)
    using \<open>havoc_rel \<omega> _\<close> by auto
qed

lemma havoc_rel_heap_update:
  assumes "havoc_rel (update_heap_total_full \<omega> l v) \<omega>2'" and "get_mask_total_full \<omega> l \<noteq> pnone"
  shows "\<exists>\<omega>2. \<omega>2' = (update_heap_total_full \<omega>2 l v) \<and> havoc_rel \<omega> \<omega>2"
proof -
  let ?h ="get_heap_total_full \<omega>"
  let ?\<omega>2="update_heap_total_full \<omega>2' l (?h l)"

  from assms have HeapLoc:"get_heap_total_full \<omega>2' l = v"
    apply (unfold havoc_rel_def)
    apply (unfold equal_on_mask_def)
    by (metis update_heap_total_full_lookup_1 update_heap_total_full_mask_same)

  show ?thesis
    apply (rule exI[where ?x="?\<omega>2"])
    apply (rule conjI)
     apply (rule full_total_state_eq)
        apply simp
       apply simp
      apply (simp only: update_heap_total_overwrite_full)
      apply (rule HOL.ext)
      apply (case_tac "x = l")
       apply (simp only: update_heap_total_full_lookup_1)
       apply (rule HeapLoc)
      apply (rule HOL.sym[OF update_heap_total_full_lookup_2])
      apply simp
     apply (simp only: update_heap_total_full_mask_same)
    unfolding havoc_rel_def
    apply (intro conjI)
     apply (simp only: update_heap_total_full_mask_same)
      apply (metis assms(1) havoc_rel_same_mask update_heap_total_full_mask_same)
    apply (smt (z3) assms equal_on_mask_def havoc_rel_def update_heap_total_full_lookup_1 update_heap_total_full_lookup_2 update_heap_total_full_mask_same)
    by (metis assms(1) fstI get_store_total.simps havoc_rel_same_store update_heap_total_full.simps)
qed


lemma step_havoc_rel:
  assumes "red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=True\<rparr> (Inl s,  RNormal \<omega>) w'" and 
          "lift_sim_rel havoc_rel w' w2'"
  (*shows   "(is_failure_config w' \<longrightarrow> (\<exists>\<omega>2 w2'. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> m\<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) w2' \<and> is_failure_config w2')) \<and>
                (\<forall> s' \<omega>' \<omega>2'. is_normal_config w' \<omega>' \<longrightarrow> havoc_rel \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) (Inl s', RNormal \<omega>2')))"*)
  shows "\<exists>\<omega>2. havoc_rel \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=False\<rparr> (Inl s, RNormal \<omega>2) w2'"
  using assms
  proof (cases)
    case NormalSingleStep
    then show ?thesis using assms(2)
    proof (induction arbitrary: w2')
      case RedSkip
      then show ?case
       by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.elims(2) lift_sim_rel_def prod.exhaust_sel red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedSkip snd_conv standard_result.distinct(5) standard_result.inject)
    next
    case (RedInhale A \<omega> res)
    show ?case
    proof (cases res)
    case RMagic
    then show ?thesis 
      using assms(2) lift_sim_rel_not_magic
      by (metis RedInhale.prems snd_conv)
    next
      case RFailure
      with RedInhale have "w2' = (Inr (), RFailure)"
        unfolding lift_sim_rel_def
        using RedInhale.prems lift_sim_rel_fail_3 by blast
      with RFailure RedInhale NormalSingleStep assms(2) havoc_inhale_failure_rel
      show ?thesis
        by (metis conf.select_convs(1) red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedInhale)
    next
      case (RNormal \<omega>')
      with RedInhale obtain \<omega>2' where "w2' = (Inr (), RNormal \<omega>2')" and "havoc_rel \<omega>' \<omega>2'"
        unfolding lift_sim_rel_def      
        by (metis fst_conv is_failure_config.simps is_normal_config.elims(2) snd_conv standard_result.distinct(5) standard_result.inject surjective_pairing)
      with \<open>res = _\<close> RedInhale assms(2) havoc_inhale_normal_rel
      obtain \<omega>2 where "havoc_rel \<omega> \<omega>2" and "red_inhale Pr \<Delta> False False A \<omega>2 (RNormal \<omega>2')"
        by (metis (full_types) conf.select_convs(1))
      then show ?thesis
        by (metis \<open>w2' = (Inr (), RNormal \<omega>2')\<close> conf.select_convs(1) local.RedInhale(1) red_stmt_total_single.NormalSingleStep red_stmt_total_single_set.RedInhale)
    qed
    next
      case (RedExhale A m' \<omega>')
      then show ?case sorry
    next
      case (RedExhaleFailure A)
      then show ?case sorry
    next
      case (RedAssert A m')
      then show ?case sorry
    next
      case (RedAssertFailure A)
      then show ?case sorry
    next
      case (RedLocalAssign e \<omega> v x)
      from assms(2) obtain \<omega>2' \<omega>2 where "w2' = (Inr (), RNormal \<omega>2')" and 
        "\<omega>2' = update_store_total \<omega>2 x v" and HRel:"havoc_rel \<omega> \<omega>2"
        using havoc_rel_store_update_3
        unfolding lift_sim_rel_def      
        by (metis RedLocalAssign.prems fst_conv is_normal_config.simps lift_sim_rel_normal snd_conv surjective_pairing)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>, subst \<open>\<omega>2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        done
    next
      case (RedLocalAssignFailure e \<omega> x)
      have "w2' = (Inr (), RFailure)" 
        using RedLocalAssignFailure.prems lift_sim_rel_fail_3 by blast
      show ?case
        apply (rule exI[where ?x = \<omega>])
        apply (rule conjI[OF havoc_rel_refl])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
        by (rule \<open>\<not>_\<close>)
    next
      case (RedFieldAssign e_r \<omega> e addr f v)
      from assms(2) havoc_rel_heap_update \<open>get_mask_total_full \<omega> (addr, f) \<noteq> pnone\<close> obtain \<omega>2 where
        HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inr (), RNormal (update_heap_total_full \<omega>2 (addr, f) v))"
        unfolding lift_sim_rel_def
        by (metis RedFieldAssign.prems fst_conv is_normal_config.simps lift_sim_rel_normal snd_conv surjective_pairing)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
            apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
          apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
          apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_r \<omega>\<close> HRel])
         apply (metis \<open>get_mask_total_full \<omega> (addr, f) \<noteq> pnone\<close> HRel havoc_rel_same_mask)
        apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e \<omega>\<close> HRel])
        done
    next
      case (RedFieldAssignFailure e_r \<omega> e f)
      hence "w2' = (Inr (), RFailure)"
        using lift_sim_rel_fail_3 by blast       
      show ?case
        apply (rule exI)
        apply (rule conjI[OF havoc_rel_refl])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule) 
        apply (rule RedFieldAssignFailure(1))
        done    
    next
      case (RedIfTrue e_b \<omega> s1 s2)
      from this obtain \<omega>2 where HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inl s1, RNormal \<omega>2)"      
        by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.simps lift_sim_rel_def prod.exhaust_sel snd_conv standard_result.distinct(5) standard_result.inject)
      show ?case 
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        done
    next
      case (RedIfFalse e_b \<omega> s1 s2)
        from this obtain \<omega>2 where HRel:"havoc_rel \<omega> \<omega>2" and "w2' = (Inl s2, RNormal \<omega>2)"      
        by (metis (no_types, lifting) assms(2) fst_conv is_failure_config.simps is_normal_config.simps lift_sim_rel_def prod.exhaust_sel snd_conv standard_result.distinct(5) standard_result.inject)
      show ?case
        apply (rule exI)
        apply (rule conjI[OF HRel])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
         apply (rule havoc_rel_expr_eval_same[OF \<open>_, _ \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t _\<close> \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        apply (rule havoc_rel_wd_same[OF \<open>wd_pure_exp_total _ _ _ e_b \<omega>\<close> HRel])
        done
    next 
      case (RedIfFailure e_b s1 s2)
      hence "w2' = (Inr (), RFailure)"
        using assms(2) lift_sim_rel_fail_3 by blast
      show ?case
        apply (rule exI)
        apply (rule conjI[OF havoc_rel_refl])
        apply (subst \<open>w2' = _\<close>)
        apply (rule, rule)
        apply (rule \<open>\<not>_\<close>)
        done
    next
      case (RedSeq1 s1 \<omega> s'' r'' s2)      
      from \<open>lift_sim_rel _ _ w2'\<close> obtain r2' where "w2' = (Inl (Seq s'' s2), r2')"
        unfolding lift_sim_rel_def
        by (metis eq_fst_iff)
      from \<open>w2' = _\<close> \<open>lift_sim_rel _ _ w2'\<close> have Rel:"lift_sim_rel havoc_rel (Inl s'', r'') (Inl s'', r2')"
        unfolding lift_sim_rel_def
        by auto
      from RedSeq1.IH[OF Rel] show ?case 
        by (metis Inl_inject Pair_inject \<open>w2' = _\<close> red_stmt_total_single.NormalSingleStep red_stmt_total_single.cases red_stmt_total_single_set.RedSeq1)        
    next
      case (RedSeq2 s1 \<omega> r'' s2)      
      from \<open>lift_sim_rel _ _ w2'\<close> obtain r2' where "w2' = (Inl s2, r2')"
        unfolding lift_sim_rel_def
        by (metis fst_conv surjective_pairing)
      from \<open>w2' = _\<close> \<open>lift_sim_rel _ _ w2'\<close> have Rel:"lift_sim_rel havoc_rel (Inr (), r'') (Inr (), r2')"
        unfolding lift_sim_rel_def
        by auto
      from RedSeq2.IH[OF Rel] show ?case
        by (metis \<open>w2' = _\<close> prod.inject red_stmt_total_single.NormalSingleStep red_stmt_total_single.cases red_stmt_total_single_set.RedSeq2 sum.inject(1))     
    qed
qed


end