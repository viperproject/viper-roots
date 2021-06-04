theory TotalSemantics
imports Viper.ViperLang TotalExpressions
begin

(*datatype 'a result = Failure | Set (select_set: "'a full_total_state set")*)

datatype 'a standard_result = RMagic | RFailure | RNormal "'a full_total_state"

fun update_store_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> x v = ((get_store_total \<omega>)(x \<mapsto> v), get_trace_total \<omega>, get_hm_total_full \<omega>)"

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

fun update_heap_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_heap_total_full \<omega> l v = (get_store_total \<omega>, get_trace_total \<omega>, update_heap_total (get_hm_total_full \<omega>) l v )"

fun update_mask_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mask_total_full \<omega> m = (get_store_total \<omega>, get_trace_total \<omega>, update_mask_total (get_hm_total_full \<omega>) m)"

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

term update_mask_total_full

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
 (*| RedInhale: "red_stmt_total_single_set Pr conf (Inhale A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) False A \<omega>))"*)
 | RedInhale: "\<lbrakk> red_inhale Pr \<Delta> (havoc_inhale conf) False A \<omega> res \<rbrakk> \<Longrightarrow>
                 red_stmt_total_single_set Pr \<Delta> conf (Inhale A) \<omega> (Inr (), res)"
 (*| RedAssume: "red_stmt_total_single_set Pr conf (Assume A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) True A \<omega>))"*)
(* | RedExhale: "red_stmt_total_single_set Pr conf (Exhale A) \<omega> 
                     (Inr (), map_option_2 (\<lambda>xs. Set (\<Union>m \<in> xs. exhale_state \<omega> m)) Failure (handle_exhale_2 Pr \<omega> A (get_total_mask_full \<omega>)))"*)
 | RedSeq1: "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single_set Pr \<Delta> conf (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single_set Pr \<Delta> conf (Seq s1 s2) \<omega> (Inl s2, r'')"
 | RedLocalAssign: "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v) \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr \<Delta> conf (LocalAssign x e) \<omega> (Inr (), (RNormal (update_store_total \<omega> x v)))"
 | RedLocalAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<rbrakk> \<Longrightarrow> red_stmt_total_single_set Pr \<Delta> conf (LocalAssign x e) \<omega> (Inr (), RFailure)"
 | RedFieldAssign: "\<lbrakk> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>; 
                      wd_pure_exp_total Pr \<Delta> CInhale e \<omega>; 
                      Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr));
                      Pr, \<Delta>  \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr \<Delta> conf (FieldAssign e_r f e) \<omega> (Inr (), (RNormal (update_heap_total_full \<omega> (addr,f) v)))"
 | RedFieldAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> \<not> wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<or> (Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null)) \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr \<Delta> conf (FieldAssign e_r f e) \<omega> (Inr (), RFailure)"
 | RedIfTrue: "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single_set Pr \<Delta> conf (If e_b s1 s2) \<omega> (Inl s1, RNormal \<omega>)"
 | RedIfFalse: "\<lbrakk> Pr,\<Delta> \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single_set Pr \<Delta> conf (If e_b s1 s2) \<omega> (Inl s2, RNormal \<omega>)"

(* datatype 'a stmt_config_2 = Failure2 | Normal "((stmt + unit) \<times> 'a full_total_state) set" *)


(*datatype 'a single_result = Normal "(stmt + unit) \<times> 'a full_total_state" | MagicSingle | FailureSingle*)

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a standard_result"


inductive red_stmt_total_single :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where 
    NormalSingleStep: "\<lbrakk> red_stmt_total_single_set Pr \<Delta> conf s \<omega> res \<rbrakk> \<Longrightarrow> 
       red_stmt_total_single Pr \<Delta> conf ((Inl s, RNormal \<omega>)) res"

definition red_stmt_total_multi :: "program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "red_stmt_total_multi Pr \<Delta> conf = rtranclp (red_stmt_total_single Pr \<Delta> conf)"

definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_mask_total_full \<omega> = zero_mask"

fun is_failure_config :: "'a stmt_config \<Rightarrow> bool"
  where "is_failure_config config \<longleftrightarrow> (snd config) = RFailure"

(* todo: incorporate precondition *)
(* first argument is just there to fix 'a *)
definition stmt_verifies_total :: "'a full_total_state \<Rightarrow> program \<Rightarrow> 'a interp \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow>  bool"
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

lemma backwards_simulation:
  assumes initial_rel: "\<And> \<omega> \<omega>2. is_empty_total \<omega> \<Longrightarrow> R \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2" and
          total_rel: "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'" and
          step:"\<And> s \<omega> w. red_stmt_total_single Pr \<Delta> conf (Inl s, RNormal \<omega>) r \<Longrightarrow>
                (is_failure_config r  \<longrightarrow> (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Normal (Inl s, \<omega>2)) FailureSingle)) \<and>
                (\<forall> s' \<omega>' \<omega>2'. (r = (m, RNormal \<omega>') \<longrightarrow> R \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 \<Delta> conf2 (Normal (Inl s, \<omega>2)) (Normal (Inl s', \<omega>2')))))"
        assumes "stmt_verifies_total dummy Pr2 \<Delta> conf2 s"
 shows "stmt_verifies_total dummy Pr \<Delta> conf s"
 sorry

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

lemma havoc_rel_heap_equal_on_mask: "havoc_rel \<omega> \<omega>' \<Longrightarrow> equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>')"
  unfolding havoc_rel_def
  oops 

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

lemma handle_inhale_sep_aux: 
  assumes "handle_inhale Pr h inh_assume (A&&B) \<omega> = Set W'" and "\<omega>' \<in> W'"
  shows "\<exists>W'' \<omega>'' W2'. handle_inhale Pr h inh_assume A \<omega> = Set W'' \<and> \<omega>'' \<in> W'' \<and> handle_inhale Pr h inh_assume B \<omega>'' = Set W2' \<and> \<omega>' \<in> W2'"
  sorry

lemma handle_inhale_sep_aux_2:
  assumes "handle_inhale Pr h inh_assume A \<omega> = Set WA" and "\<omega>a \<in> WA" and "handle_inhale Pr h inh_assume B \<omega>a = Set WB" and "\<omega>b \<in> WB" and
          "handle_inhale Pr h inh_assume (A&&B) \<omega> = Set W"
  shows "\<omega>b \<in> W"
  sorry

lemma handle_inhale_havoc_failure_preservation:
  assumes "handle_inhale Pr True inh_assume A \<omega> = Set W'"
  shows "\<exists>W2'. handle_inhale Pr False inh_assume A \<omega> = Set W2'"
  sorry

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

lemma havoc_inhale_rel:
  assumes "red_inhale Pr \<Delta> True inh_assume A \<omega> res" and "res = RNormal \<omega>'" and "havoc_rel \<omega>' \<omega>2'" (*and "supported_subset A"*)
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

lemma step_havoc_rel:
  assumes "red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=True\<rparr> (Normal (Inl s, \<omega>)) w"
  shows   "(w = RFailure \<longrightarrow> (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<Delta> \<lparr>havoc_inhale=False\<rparr> (RNormal (Inl s, \<omega>2)) R)) \<and>
                (\<forall> s' \<omega>' \<omega>2'. (w = RNormal (Inl s', \<omega>') \<longrightarrow> R \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<lparr>havoc_inhale=False\<rparr> (RNormal (Inl s, \<omega>2)) (RNormal (Inl s', \<omega>2')))))"
  using assms
proof (cases)
  case (NormalSingleStep m' W' \<omega>')
  from NormalSingleStep(2) show ?thesis 
  proof cases
  case RedSkip
  show ?thesis
    by (simp add: local.NormalSingleStep(1) local.RedSkip(2))
  next
    case (RedInhale A)
    then show ?thesis sorry
  next
  case (RedAssume A)
    then show ?thesis sorry
  next
    case (RedExhale A get_total_mask_full)
    then show ?thesis sorry
  next
  case (RedSeq1 s1 s'' s2)
  then show ?thesis sorry
  next
  case (RedSeq2 s1 s2)
  then show ?thesis sorry
  next
    case (RedLocalAssign e v x)
    then show ?thesis sorry
  next
  case (RedFieldAssign e_r e addr v f)
    then show ?thesis sorry
  next
    case (RedIfTrue e_b s1 s2)
    then show ?thesis sorry
  next
    case (RedIfFalse e_b s1 s2)
    then show ?thesis sorry
  qed
next
  case (FailureSingleStep m')
  then show ?thesis sorry
qed

lemma havoc_conf_equiv:
  assumes "stmt_verifies_total dummy Pr \<lparr>havoc_inhale=False\<rparr> s"
  shows "stmt_verifies_total dummy Pr \<lparr>havoc_inhale=True\<rparr> s"
proof (rule backwards_simulation)
  
  




(*
inductive red_stmt_total_single_2 :: "'a program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> 'a stmt_config_2  \<Rightarrow> 'a stmt_config_2 \<Rightarrow> bool" where
  "red_stmt_total_single_2 Pr conf s Normal C1 C2 =
         (\<forall> "
*)

(*datatype 'a stmt_config_2 = SmallStepFailure | Normal "( (stmt + unit) \<times> 'a result) set"*)

(*type_synonym 'a stmt_config_3 = "((stmt + unit) \<times> *)
(*
fun small_step_lifted :: "'a program \<Rightarrow> conf \<Rightarrow> 'a stmt_config_2 \<Rightarrow> 'a stmt_config_2 \<Rightarrow> bool"
  where 
    "small_step_lifted Pr conf S S' = 
*)         
(*
  | "small_step_lifted Pr conf (Normal S) = 
       (if (\<exists>s \<omega> m'. (Inl s, \<omega>) \<in> S \<and> red_stmt_total_single Pr conf s \<omega> (m', Failure)) then
          SmallStepFailure
       else 
         Normal {(m', \<omega>') | s \<omega> m' \<omega>' W'. (Inl s, \<omega>) \<in> S \<and> \<omega>' \<in> W' \<and> red_stmt_total_single Pr conf s \<omega> (m', Set W')})"
*)

(*
fun small_step_lifted :: "'a program \<Rightarrow> conf \<Rightarrow> 'a stmt_config_2 \<Rightarrow> 'a stmt_config_2"
  where 
    "small_step_lifted Pr conf SmallStepFailure = SmallStepFailure"
  | "small_step_lifted Pr conf (Normal S) = 
       (if (\<exists>s \<omega> m'. (Inl s, \<omega>) \<in> S \<and> red_stmt_total_single Pr conf s \<omega> (m', Failure)) then
          SmallStepFailure
       else 
         Normal {(m', \<omega>') | s \<omega> m' \<omega>' W'. (Inl s, \<omega>) \<in> S \<and> \<omega>' \<in> W' \<and> red_stmt_total_single Pr conf s \<omega> (m', Set W')})"
*)
(*
definition small_step_multi :: "'a program \<Rightarrow> conf \<Rightarrow> 'a stmt_config_2 \<Rightarrow> 'a stmt_config_2 \<Rightarrow> bool"
  where "small_step_multi Pr conf = rtranclp (small_step_lifted Pr conf)"

definition ver_total :: "'a program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> ('a full_total_state) set \<Rightarrow> bool" where
  "ver Pr conf s \<omega> \<longleftrightarrow> (\<exists>r. red_stmt_total_single Pr conf s \<omega> (Set r))"
*)

end