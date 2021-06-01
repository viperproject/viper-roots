theory TotalSemantics
imports Viper.ViperLang TotalExpressions
begin

datatype fail = WellDefFail | StandardFail

datatype 'a result = Failure | Set (select_set: "'a full_total_state set")


(*
definition field_assign_virtual :: "'a virtual_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" where
  "field_assign_virtual \<phi> hl v = Abs_virtual_state (get_vm \<phi>, (get_vh \<phi>)(hl := Some v))"

fun field_assign :: "'a state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a state" where
  "field_assign (\<sigma>, \<tau>, \<phi>) hl v = (\<sigma>, \<tau>, field_assign_virtual \<phi> hl v)"
*)

fun update_store_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_store_total (\<sigma>, \<pi>, \<phi>) x v = (\<sigma>(x \<mapsto> v), \<pi>, \<phi>)"

definition update_heap_total :: "'a total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a total_state"
  where "update_heap_total mh l v = Abs_total_state ((get_mask_total mh), (get_heap_total mh)(l := v))"

definition update_mask_total :: "'a total_state \<Rightarrow> mask \<Rightarrow> 'a total_state"
  where "update_mask_total mh m' = Abs_total_state (m', get_heap_total mh)"

lemma Abs_total_state_inverse_2:
  assumes "wf_pre_total_state (m,h)"
  shows "Rep_total_state (Abs_total_state (m,h)) = (m,h)"
  using assms Abs_total_state_inverse
  by blast

lemma update_mask_total_multiple: 
  assumes "wf_mask_simple m0" and "wf_mask_simple m2"
  shows   "update_mask_total (update_mask_total mh m0) m1 = update_mask_total mh m1"
  unfolding update_mask_total_def  
  using assms
  by (simp add: Abs_total_state_inverse_2)

fun update_heap_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_heap_total_full (\<sigma>, \<pi>, \<phi>) l v = (\<sigma>, \<pi>, update_heap_total \<phi> l v )"

fun update_mask_total_full :: "'a full_total_state \<Rightarrow> mask \<Rightarrow> 'a full_total_state"
  where "update_mask_total_full (\<sigma>, \<pi>, \<phi>) m = (\<sigma>, \<pi>, update_mask_total \<phi> m)"

lemma update_mask_total_full_multiple: 
  assumes "wf_mask_simple m0"
  shows   "update_mask_total_full (update_mask_total_full \<omega> m0) m1 = update_mask_total_full \<omega> m1"
  using assms
  by (metis get_mask_total_full.cases update_mask_total_full.simps update_mask_total_multiple)

definition singleton_total_pred :: "heap_loc \<Rightarrow> (prat \<Rightarrow> 'a val \<Rightarrow> bool) \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_pred l P \<sigma> \<tau> = { (\<sigma>, \<tau>, Abs_total_state (m,h)) |m h. P (m l) (h l)}"

definition singleton_total :: "bool \<Rightarrow> heap_loc \<Rightarrow> prat \<Rightarrow> 'a val \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total havoc_new l p v \<sigma> \<tau> = singleton_total_pred l (\<lambda> p' v'. p = p' \<and> (\<not>havoc_new \<longrightarrow> v = v')) \<sigma> \<tau>"

definition singleton_total_only_mask :: "heap_loc \<Rightarrow> prat \<Rightarrow> 'a store \<Rightarrow> 'a total_trace \<Rightarrow> ('a full_total_state) set"
  where "singleton_total_only_mask l p \<sigma> \<tau> = singleton_total_pred l (\<lambda> p' v'. p = p') \<sigma> \<tau>"

fun map_result :: "(('a full_total_state) \<Rightarrow> 'a result) \<Rightarrow> 'a result \<Rightarrow> 'a result"
  where 
    "map_result f Failure = Failure"
  | "map_result f (Set xs) = (if \<exists>x \<in> xs. f x = Failure then Failure else Set (\<Union>x \<in> xs. select_set (f x))) "

fun map_result_2 :: "(mask \<Rightarrow> (mask set) option) \<Rightarrow> (mask set) option \<Rightarrow> (mask set) option"
  where 
    "map_result_2 f None = None"
  | "map_result_2 f (Some xs) = (if \<exists>x \<in> xs. f x = None then None else Some (\<Union>x \<in> xs. the (f x))) "


fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"


datatype 'a inh_exh_result = InhExhFailure | InhExhNormal "'a full_total_state"

(*
inductive red_inhale :: "program \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow>  'a inh_exh_result \<Rightarrow> bool"
  where 
   "\<lbrakk> red_inhale Pr havoc_new inh_assume A \<omega> (InhExhNormal \<omega>''); 
      red_inhale Pr havoc_new inh_assume B \<omega>'' (InhExhNormal \<omega>')\<rbrakk> \<Longrightarrow>
    red_inhale Pr havoc_new inh_assume (A && B) \<omega> (InhExhNormal \<omega>')"
 | "\<lbrakk> red_inhale Pr havoc_new inh_assume A \<omega> InhExhFailure \<rbrakk> \<Longrightarrow>
    red_inhale Pr havoc_new inh_assume (A && B) \<omega> InhExhFailure"
 | "\<lbrakk> red_inhale Pr havoc_new inh_assume A \<omega> (InhExhNormal \<omega>''); 
      red_inhale Pr havoc_new inh_assume B \<omega>'' InhExhFailure \<rbrakk> \<Longrightarrow>
    red_inhale Pr havoc_new inh_assume (A && B) \<omega> InhExhFailure"
 | "\<lbrakk> a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>); p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>)) \<rbrakk> \<Longrightarrow>
*)

fun handle_inhale :: "program \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
  where 
(** Connectives **)
    "handle_inhale Pr havoc_new inh_assume (A && B) \<omega> = 
       map_result (handle_inhale Pr havoc_new inh_assume B) (handle_inhale Pr havoc_new inh_assume A \<omega>)"
  | "handle_inhale Pr havoc_new inh_assume (Imp e A) \<omega> = 
        (if (red_pure_exp_total Pr e \<omega>) = VBool True then (handle_inhale Pr havoc_new inh_assume A \<omega>) else Set {\<omega>})"
(** Inhale specific **)
  (** Not assume **)
  | "handle_inhale Pr havoc_new False (Atomic (Acc e_r f e_p)) \<omega> =
       (let a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>))
        in 
            (if p \<ge> 0 \<and> (wd_pure_exp_total Pr CInhale e_r \<omega>) then 
               if a_opt \<noteq> None then
                 Set (plus_total_set {\<omega>} 
                        ((singleton_total havoc_new (the a_opt,f) (Abs_prat p) (get_heap_total_full \<omega> (the a_opt,f)) (get_store_total \<omega>) (get_trace_total \<omega>))))
               else Set {}
             else Failure))"
  | "handle_inhale Pr havoc_new False (Atomic (AccWildcard e_r f)) \<omega> =
        (let r = the_address (red_pure_exp_total Pr e_r \<omega>) in
            if (wd_pure_exp_total Pr CInhale e_r \<omega>) then
              Set (plus_total_set {\<omega>} 
                  ((singleton_total_pred (r,f) (\<lambda>p v. (pgt p pnone) \<and> (\<not>havoc_new \<longrightarrow> v = get_heap_total_full \<omega> (r,f))) (get_store_total \<omega>) (get_trace_total \<omega>))))
            else Failure)"
  (** Assume **)
  | "handle_inhale Pr havoc_new True (Atomic (Acc e_r f e_p)) \<omega> =
       (let a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>))
        in 
            if p \<ge> 0 \<and> (wd_pure_exp_total Pr CInhale e_r \<omega>) then
              if a_opt \<noteq> None then
                if ((Rep_prat (get_mask_total_full \<omega> (the a_opt,f))) \<ge> p) then Set {\<omega>} else Set {\<omega>}
              else Set {}
            else Failure)"
  | "handle_inhale Pr havoc_new True (Atomic (AccWildcard e_r f)) \<omega> =
        (let r = the_address (red_pure_exp_total Pr e_r \<omega>) in
          if (wd_pure_exp_total Pr CInhale e_r \<omega>) then
            if ((Rep_prat (get_mask_total_full \<omega> (r,f))) > 0) then Set {\<omega>} else Set {\<omega>}
          else Failure)"
  (** Same for both with and without Assume **)
  | "handle_inhale Pr havoc_new inh_assume (InhaleExhale A B) \<omega> = handle_inhale Pr havoc_new inh_assume A \<omega>"
  | "handle_inhale Pr havoc_new inh_assume (Atomic (Pure e)) \<omega> =
        (if wd_pure_exp_total Pr CInhale e \<omega> then  
          (if (red_pure_exp_total Pr e \<omega>) = VBool True then Set {\<omega>} else Set {})
         else Failure)"
(* todo *)
  | "handle_inhale Pr havoc_new inh_assume (ForAll v va) \<omega> = undefined"
  | "handle_inhale Pr havoc_new inh_assume (Atomic (AccPredicate va vb vc)) \<omega> = undefined"
  | "handle_inhale Pr havoc_new inh_assume (Atomic (AccPredicateWildcard va vb)) \<omega> = undefined"
  | "handle_inhale Pr havoc_new inh_assume (A --* B) \<omega> = undefined"


fun handle_exhale :: "program \<Rightarrow> heap_loc set \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
  where
    "handle_exhale Pr def_locs (A && B) \<omega> = 
       map_result (handle_exhale Pr def_locs B) (handle_exhale Pr def_locs A \<omega>)"
  | "handle_exhale Pr def_locs (Imp e A) \<omega> = 
       (if (red_pure_exp_total Pr e \<omega>) = VBool True then (handle_exhale Pr def_locs A \<omega>) else Set {\<omega>})"
  | "handle_exhale Pr def_locs (Atomic (Acc e_r f e_p)) \<omega> = 
       (let a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>)) 
        in            
            if (p \<ge> 0 \<and> (wd_pure_exp_total Pr (CExhale def_locs) e_r \<omega>) \<and> a_opt \<noteq> None) \<and> pgte (get_mask_total_full \<omega> ((the a_opt),f) ) (Abs_prat p) then            
             Set {\<omega>'| \<omega>' \<omega>_r. \<omega>_r \<in> singleton_total_only_mask ((the a_opt),f) (Abs_prat p) (get_store_total \<omega>) (get_trace_total \<omega>) \<and> \<omega>' |\<oplus>|\<^sub>t \<omega>_r = Some \<omega>}
            else 
             Failure)     
      "
  | "handle_exhale Pr def_locs (Atomic (AccWildcard e_r f)) \<omega> =
       (let a_opt = get_address_opt (red_pure_exp_total Pr e_r \<omega>)
        in 
          if ((wd_pure_exp_total Pr (CExhale def_locs) e_r \<omega>) \<and> a_opt \<noteq> None) \<and> pgt (get_mask_total_full \<omega> ((the a_opt),f) ) pnone then
           Set {\<omega>'| \<omega>' \<omega>_r. \<omega>_r \<in> (singleton_total_pred (the a_opt,f) (\<lambda>p v. pgt ((get_mask_total_full \<omega>) (the a_opt,f)) p) (get_store_total \<omega>) (get_trace_total \<omega>)) \<and>
                        \<omega>' |\<oplus>|\<^sub>t \<omega>_r = Some \<omega> }
          else Failure)"
  | "handle_exhale Pr def_locs (InhaleExhale A B) \<omega> = handle_exhale Pr def_locs B \<omega>"
  | "handle_exhale Pr def_locs (Atomic (Pure e)) \<omega> =
         (if wd_pure_exp_total Pr (CExhale def_locs) e \<omega> \<and> (un_VBool (red_pure_exp_total Pr e \<omega>))then 
             Set {\<omega>}
          else Failure)"
  | "handle_exhale Pr def_locs (ForAll v va) \<omega> = undefined"
  | "handle_exhale Pr def_locs (Atomic (AccPredicate va vb vc)) \<omega> = undefined"
  | "handle_exhale Pr def_locs (Atomic (AccPredicateWildcard va vb)) \<omega> = undefined"
  | "handle_exhale Pr def_locs (A --* B) \<omega> = undefined"


definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {l |l. pgt (get_mask_total_full \<omega> l) pnone}"

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

record conf =
  havoc_inhale :: bool


(* alt:
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
inductive red_stmt_total_single_set :: "program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> (stmt+unit) \<times> ('a result) \<Rightarrow> bool" where
   RedSkip: " red_stmt_total_single_set Pr conf Skip \<omega> (Inr (), Set {\<omega>})"
 | RedInhale: "red_stmt_total_single_set Pr conf (Inhale A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) False A \<omega>))"
 | RedAssume: "red_stmt_total_single_set Pr conf (Assume A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) True A \<omega>))"
 | RedExhale: "red_stmt_total_single_set Pr conf (Exhale A) \<omega> 
                     (Inr (), map_option_2 (\<lambda>xs. Set (\<Union>m \<in> xs. exhale_state \<omega> m)) Failure (handle_exhale_2 Pr \<omega> A (get_total_mask_full \<omega>)))"
 | RedSeq1: "\<lbrakk> red_stmt_total_single_set Pr conf s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single_set Pr conf (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: "\<lbrakk> red_stmt_total_single_set Pr conf s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single_set Pr conf (Seq s1 s2) \<omega> (Inl s2, r'')"
 | RedLocalAssign: "\<lbrakk> wd_pure_exp_total Pr CInhale e \<omega>; Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t = v \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr conf (LocalAssign x e) \<omega> (Inr (), (Set {update_store_total \<omega> x v}))"
 | RedLocalAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr CInhale e \<omega> \<rbrakk> \<Longrightarrow> red_stmt_total_single_set Pr conf (LocalAssign x e) \<omega> (Inr (), Failure)"
 | RedFieldAssign: "\<lbrakk> wd_pure_exp_total Pr CInhale e_r \<omega>; 
                      wd_pure_exp_total Pr CInhale e \<omega>; 
                      Pr \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t = VRef (Address addr);
                      Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t = v \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr conf (FieldAssign e_r f e) \<omega> (Inr (), (Set {update_heap_total_full \<omega> (addr,f) v}))"
 | RedFieldAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr CInhale e_r \<omega> \<or> \<not> wd_pure_exp_total Pr CInhale e \<omega> \<or> (Pr \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t) = (VRef Null) \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single_set Pr conf (FieldAssign e_r f e) \<omega> (Inr (), Failure)"
 | RedIfTrue: "\<lbrakk> Pr \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool True \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single_set Pr conf (If e_b s1 s2) \<omega> (Inl s1, Set {\<omega>})"
 | RedIfFalse: "\<lbrakk> Pr \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool False \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single_set Pr conf (If e_b s1 s2) \<omega> (Inl s2, Set {\<omega>})"

(* datatype 'a stmt_config_2 = Failure2 | Normal "((stmt + unit) \<times> 'a full_total_state) set" *)

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a full_total_state"

datatype 'a single_result = FailureSingle | Normal "(stmt + unit) \<times> 'a full_total_state"

inductive red_stmt_total_single :: "program \<Rightarrow> conf \<Rightarrow> 'a single_result \<Rightarrow> 'a single_result \<Rightarrow> bool"
  where 
    NormalSingleStep: "\<lbrakk> red_stmt_total_single_set Pr conf s \<omega> (m', Set W'); \<omega>' \<in> W' \<rbrakk> \<Longrightarrow> 
       red_stmt_total_single Pr conf (Normal (Inl s, \<omega>)) (Normal (m', \<omega>'))"
  | FailureSingleStep: "\<lbrakk> red_stmt_total_single_set Pr conf s \<omega> (m', Failure) \<rbrakk> \<Longrightarrow>
       red_stmt_total_single Pr conf (Normal (Inl s, \<omega>)) FailureSingle"

definition red_stmt_total_multi :: "program \<Rightarrow> conf \<Rightarrow> 'a single_result \<Rightarrow> 'a single_result \<Rightarrow> bool"
  where "red_stmt_total_multi Pr conf = rtranclp (red_stmt_total_single Pr conf)"


definition is_empty_total :: "'a full_total_state \<Rightarrow> bool"
  where "is_empty_total \<omega> \<equiv> get_mask_total_full \<omega> = zero_mask"

(* todo: incorporate precondition *)
(* first argument is just there to fix 'a *)
definition stmt_verifies_total :: "'a full_total_state \<Rightarrow> program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow>  bool"
  where "stmt_verifies_total dummy Pr conf s \<equiv> 
         \<forall>(\<omega> :: 'a full_total_state) r. is_empty_total \<omega> \<longrightarrow> 
           red_stmt_total_multi Pr conf ((Normal (Inl s, \<omega>))) r \<longrightarrow> r \<noteq> FailureSingle"


subsection \<open>Havoc at exhale is sufficient\<close>

definition equal_on_mask :: "mask \<Rightarrow> 'a total_heap \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "equal_on_mask m h1 h2 \<equiv> \<forall> l. m(l) \<noteq> pnone \<longrightarrow> h1(l) = h2(l)"

lemma equal_on_mask_refl: "equal_on_mask m h h"
  by (simp add: equal_on_mask_def)

type_synonym 'a simulation_rel = "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"

lemma havoc_equiv:
  assumes "stmt_verifies_total dummy Pr \<lparr>havoc_inhale = false\<rparr> s"
  shows "stmt_verifies_total dummy Pr \<lparr>havoc_inhale = true\<rparr> s"
  oops

subsection \<open>Backwards simulation\<close>

(*definition lift_simulation_rel :: "'a simulation_rel \<Longrightarrow> *)

lemma backwards_simulation:
  assumes initial_rel: "\<And> \<omega> \<omega>2. is_empty_total \<omega> \<Longrightarrow> R \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2" and
          total_rel: "\<forall>\<omega>. \<exists> \<omega>'. R \<omega> \<omega>'" and
          step:"\<And> s \<omega> w. red_stmt_total_single Pr conf (Normal (Inl s, \<omega>)) w \<Longrightarrow>
                (w = FailureSingle \<longrightarrow> (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 conf2 (Normal (Inl s, \<omega>2)) FailureSingle)) \<and>
                (\<forall> s' \<omega>' \<omega>2'. (w = Normal (Inl s', \<omega>') \<longrightarrow> R \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr2 conf2 (Normal (Inl s, \<omega>2)) (Normal (Inl s', \<omega>2')))))"
        assumes "stmt_verifies_total dummy Pr2 conf2 s"
 shows "stmt_verifies_total dummy Pr conf s"
  sorry

definition havoc_rel :: "'a simulation_rel"
  where "havoc_rel \<omega> \<omega>' \<equiv> get_mask_total_full \<omega> = get_mask_total_full \<omega>' \<and> 
                          equal_on_mask (get_mask_total_full \<omega>) (get_heap_total_full \<omega>) (get_heap_total_full \<omega>')"

lemma init_havoc_rel: "is_empty_total \<omega> \<Longrightarrow> havoc_rel \<omega> \<omega>2 \<Longrightarrow> is_empty_total \<omega>2"
  by (simp add: havoc_rel_def is_empty_total_def)

lemma total_havoc_rel: "\<exists> \<omega>'. havoc_rel \<omega> \<omega>'"
  by (rule exI[where ?x=\<omega>]) (simp add: havoc_rel_def equal_on_mask_refl)

fun supported_subset :: "assertion \<Rightarrow> bool"
  where 
    "supported_subset (ForAll v va) = False"
  | "supported_subset (Atomic (AccPredicate va vb vc)) = False"
  | "supported_subset (Atomic (AccPredicateWildcard va vb)) = False"
  | "supported_subset (A --* B) = False"
  | "supported_subset _ = True"


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

lemma havoc_inhale_rel:
  assumes "handle_inhale Pr True inh_assume A \<omega> = Set W'" and "\<omega>' \<in> W'" and "havoc_rel \<omega>' \<omega>2'" (*and "supported_subset A"*)
  shows "\<exists>W2'. handle_inhale Pr False inh_assume A (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>)) = Set W2' \<and> \<omega>2' \<in> W2' \<and> havoc_rel \<omega> (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
  using assms
proof (induction Pr True inh_assume A \<omega> arbitrary:W' \<omega>' \<omega>2' rule: handle_inhale.induct)
  case (1 Pr inh_assume A B \<omega>)
  from handle_inhale_sep_aux[OF \<open>handle_inhale Pr True inh_assume (A && B) \<omega> = Set W'\<close> \<open>\<omega>' \<in> W'\<close>] obtain WA \<omega>a WB where
    InhA:"handle_inhale Pr True inh_assume A \<omega> = Set WA" and "\<omega>a \<in> WA" and InhB:"handle_inhale Pr True inh_assume B \<omega>a = Set WB" and "\<omega>' \<in> WB"
    by auto
  let ?\<omega>2'B="(update_mask_total_full \<omega>2' (get_mask_total_full \<omega>a))"
  from 1(1)[OF InhB \<open>\<omega>' \<in> WB\<close> \<open>havoc_rel \<omega>' \<omega>2'\<close>] obtain W2B where
    InhB2:"handle_inhale Pr False inh_assume B ?\<omega>2'B = Set W2B" and "\<omega>2' \<in> W2B" and 
    "havoc_rel \<omega>a ?\<omega>2'B"
    by auto
  let ?\<omega>2'A ="(update_mask_total_full ?\<omega>2'B (get_mask_total_full \<omega>))"
  from 1(2)[OF InhA \<open>\<omega>a \<in> WA\<close> \<open>havoc_rel \<omega>a ?\<omega>2'B\<close>]  obtain W2A where
    InhA2:"handle_inhale Pr False inh_assume A ?\<omega>2'A = Set W2A" and "?\<omega>2'B \<in> W2A" and "havoc_rel \<omega> ?\<omega>2'A"
    by auto
  have "?\<omega>2'A = (update_mask_total_full \<omega>2' (get_mask_total_full \<omega>))"
    apply (rule update_mask_total_full_multiple)
    by (rule get_mask_total_full_wf)
  from \<open>handle_inhale Pr True inh_assume (A && B) \<omega> = Set W'\<close> obtain W2' where
       "handle_inhale Pr False inh_assume (A && B) \<omega> = Set W2'"
    using handle_inhale_havoc_failure_preservation by blast
(*  with InhA2 InhB2 \<open>\<omega>2' \<in> W2B\<close> \<open>?\<omega>2'B \<in> W2A\<close> *)
  hence "\<omega>2' \<in> W2'"
    using handle_inhale_sep_aux_2[OF InhA2 \<open>?\<omega>2'B \<in> W2A\<close> InhB2 \<open>\<omega>2' \<in> W2B\<close>]
    
    
  then show ?case sorry
next
  case (2 Pr inh_assume e A \<omega>)
  then show ?case sorry
next
  case (3 Pr e_r f e_p \<omega>)
  then show ?case sorry
next
  case (4 Pr e_r f \<omega>)
  then show ?case sorry
next
  case (5 Pr e_r f e_p \<omega>)
  then show ?case sorry
next
  case (6 Pr e_r f \<omega>)
  then show ?case sorry
next
  case (7 Pr inh_assume A B \<omega>)
  then show ?case sorry
next
  case (8 Pr inh_assume e \<omega>)
  then show ?case sorry
next
  case (9 Pr inh_assume v va \<omega>)
  then show ?case sorry
next
  case (10 Pr inh_assume va vb vc \<omega>)
  then show ?case sorry
next
  case (11 Pr inh_assume va vb \<omega>)
  then show ?case sorry
next
  case (12 Pr inh_assume A B \<omega>)
  then show ?case sorry
qed



lemma step_havoc_rel:
  assumes "red_stmt_total_single Pr \<lparr>havoc_inhale=False\<rparr> (Normal (Inl s, \<omega>)) w"
  shows   "(w = FailureSingle \<longrightarrow> (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<lparr>havoc_inhale=False\<rparr> (Normal (Inl s, \<omega>2)) FailureSingle)) \<and>
                (\<forall> s' \<omega>' \<omega>2'. (w = Normal (Inl s', \<omega>') \<longrightarrow> R \<omega>' \<omega>2' \<longrightarrow>
                               (\<exists>\<omega>2. R \<omega> \<omega>2 \<and> red_stmt_total_single Pr \<lparr>havoc_inhale=False\<rparr> (Normal (Inl s, \<omega>2)) (Normal (Inl s', \<omega>2')))))"
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