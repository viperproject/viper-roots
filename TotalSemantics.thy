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

fun update_trace_total :: "'a full_total_state \<Rightarrow> 'a total_trace \<Rightarrow> 'a full_total_state"
  where "update_trace_total \<omega> \<pi> = (get_store_total \<omega>, \<pi>, get_hm_total_full \<omega>)"

lemma update_trace_total_store_same: "get_store_total (update_trace_total \<omega> \<pi>) = get_store_total \<omega>"
  by simp

lemma update_trace_total_hm_same: "get_hm_total_full (update_trace_total \<omega> \<pi>) = get_hm_total_full \<omega>"
  by simp

lemma update_trace_total_heap_same: "get_heap_total_full (update_trace_total \<omega> \<pi>) = get_heap_total_full \<omega>"
  by simp

lemma update_trace_total_mask_same: "get_mask_total_full (update_trace_total \<omega> \<pi>) = get_mask_total_full \<omega>"
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

definition singleton_total_only_mask :: "heap_loc \<Rightarrow> prat \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_only_mask l p \<sigma> \<tau> = singleton_total_pred l (\<lambda> p' v'. p = p') \<sigma> \<tau>"

fun map_result_2 :: "(mask \<Rightarrow> (mask set) option) \<Rightarrow> (mask set) option \<Rightarrow> (mask set) option"
  where 
    "map_result_2 f None = None"
  | "map_result_2 f (Some xs) = (if \<exists>x \<in> xs. f x = None then None else Some (\<Union>x \<in> xs. the (f x))) "


fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"

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


inductive red_inhale :: "program \<Rightarrow> 'a interp \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow>  'a standard_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and havoc_new :: bool
  where 
  (** sep. conj **)
   InhSepNormal: 
   "\<lbrakk> red_inhale Pr \<Delta> havoc_new A \<omega> (RNormal \<omega>''); 
      red_inhale Pr \<Delta> havoc_new B \<omega>'' res\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (A && B) \<omega> res"
 | InhSepFailureMagic: 
   "\<lbrakk> red_inhale Pr \<Delta> havoc_new A \<omega> resA; 
      resA = RFailure \<or> resA = RMagic \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (A && B) \<omega> resA"
  (** if-else **)
 | InhImpTrue: 
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_inhale Pr \<Delta> havoc_new A \<omega> res \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (Imp e A) \<omega> res" 
 | InhImpFalse:  
   "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> havoc_new (Imp e A) \<omega> (RNormal \<omega>)"
 | InhImpFailure: 
   "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow> 
     red_inhale Pr \<Delta> havoc_new (Imp e A) \<omega>  RFailure"
(** inhale/assume acc(e.f, p) **) (* Pr, \<Delta> \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l) *)
(* \<omega>' \<in> plus_total_full_set {\<omega>} 
                        ((singleton_total havoc_new (a,f) (Abs_prat p) (get_heap_total_full \<omega> (a,f)) (get_store_total \<omega>) (get_trace_total \<omega>)))*)
 | InhAcc: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); p \<ge> 0; 
       wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> CInhale e_p \<omega>;
       \<omega>' \<in> inhale_perm_single havoc_new \<omega> (a,f) (Some (Abs_prat p))\<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f e_p)) \<omega> (RNormal \<omega>')"
 | InhAssumeAccFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f e_p)) \<omega> RMagic"
 | InhAssumeAccFail2: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
      (\<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> p < 0)\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f e_p)) \<omega> RFailure"
(** inhale/assume acc(e.f, wildcard) **)
(*  \<omega>' \<in> plus_total_full_set {\<omega>} 
        singleton_total_wildcard havoc_new (r,f) (get_heap_total_full \<omega> (r,f)) (get_store_total \<omega>) (get_trace_total \<omega>)) *)
 | InhAccWildcard: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       (wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>);
       \<omega>' \<in> inhale_perm_single havoc_new \<omega> (a,f) None \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> havoc_new (Atomic (AccWildcard e_r f)) \<omega> (RNormal \<omega>')"
  | InhAssumeAccWildcardFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
    red_inhale Pr \<Delta> havoc_new (Atomic (AccWildcard e_r f)) \<omega> RMagic"
 | InhAssumeAccWildcardFail2: 
     "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); 
        Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> havoc_new (Atomic (AccWildcard e_r f)) \<omega> RFailure"
(** others **)
 | InhInhaleExhale: 
    "\<lbrakk> red_inhale Pr \<Delta> havoc_new A \<omega> res \<rbrakk> \<Longrightarrow> 
       red_inhale Pr \<Delta> havoc_new (InhaleExhale A B) \<omega> res"
  | InhPureNormalMagic: 
    "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>;  
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"
  | InhPureFail: 
    "\<lbrakk> \<not>wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (Atomic (Pure e)) \<omega> RFailure"

lemma InhPureNormal:
  assumes "wd_pure_exp_total Pr \<Delta> CInhale e \<omega>" and
          "Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        shows "red_inhale Pr \<Delta> havoc_new (Atomic (Pure e)) \<omega> (RNormal \<omega>)"
  using InhPureNormalMagic[OF assms]
  by simp

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {l |l. pgt (get_mask_total_full \<omega> l) pnone}"

datatype exhale_result = ExhaleNormal mask | ExhaleFailure

inductive red_exhale :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> mask \<Rightarrow> exhale_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp" and \<omega>0 :: "'a full_total_state"
  where 

\<comment>\<open>exhale A && B\<close>
   ExhSepNormal: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A m (ExhaleNormal m''); 
      red_exhale Pr \<Delta> \<omega>0 B m'' res\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m res"
 | ExhSepFailureMagic: 
   "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 A m ExhaleFailure \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (A && B) m ExhaleFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
 | ExhImpTrue: 
   "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
      wd_pure_exp_total Pr \<Delta> (CExhale (get_valid_locs \<omega>0)) e \<omega>; 
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True); 
      red_exhale Pr \<Delta> \<omega>0 A m res \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Imp e A) m res" 
 | ExhImpFalse:  
   "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
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
    "\<lbrakk> red_exhale Pr \<Delta> \<omega>0 B m res \<rbrakk> \<Longrightarrow> 
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

lemma exhale_state_same_store: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_store_total \<omega>' = get_store_total \<omega>"
  by (simp add: exhale_state_def)

lemma exhale_state_same_trace: "\<omega>' \<in> exhale_state \<omega> m \<Longrightarrow> get_trace_total \<omega>' = get_trace_total \<omega>"
  by (simp add: exhale_state_def)

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
   "\<lbrakk> red_inhale Pr \<Delta> (havoc_inhale conf) A \<omega> res \<rbrakk> \<Longrightarrow>
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

end