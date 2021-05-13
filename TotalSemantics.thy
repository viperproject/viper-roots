theory TotalSemantics
imports Viper.ViperLang TotalExpressions
begin

datatype fail = WellDefFail | StandardFail
datatype 'a inh_exh_result = IEFailure fail | Set "'a full_total_state set"

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

fun update_heap_total_full :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_heap_total_full (\<sigma>, \<pi>, \<phi>) l v = (\<sigma>, \<pi>, update_heap_total \<phi> l v )"


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

fun get_address_opt :: "'a val \<Rightarrow> address option"
  where 
    "get_address_opt (VRef (Address a)) = Some a"
  | "get_address_opt _ = None"


fun handle_inhale :: "'a program \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
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


fun handle_exhale :: "'a program \<Rightarrow> heap_loc set \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
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

record conf =
  havoc_inhale :: bool

type_synonym 'a stmt_config = "(stmt+unit) \<times> ('a result)"

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {l |l. pgt (get_mask_total_full \<omega> l) pnone}"

inductive red_stmt_total_single :: "'a program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> 'a full_total_state  \<Rightarrow> 'a stmt_config \<Rightarrow> bool" where
   RedSkip: " red_stmt_total_single Pr conf Skip \<omega> (Inr (), Set {\<omega>})"
 | RedInhale: "red_stmt_total_single Pr conf (Inhale A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) False A \<omega>))"
 | RedAssume: "red_stmt_total_single Pr conf (Assume A) \<omega> (Inr (), (handle_inhale Pr (havoc_inhale conf) True A \<omega>))"
 | RedExhale: "red_stmt_total_single Pr conf (Exhale A) \<omega> (Inr (), (handle_exhale Pr (get_valid_locs \<omega>) A \<omega>))"
 | RedSeq1: "\<lbrakk> red_stmt_total_single Pr conf s1 \<omega> (Inl s'', r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single Pr conf (Seq s1 s2) \<omega> (Inl (Seq s'' s2), r'')"
 | RedSeq2: "\<lbrakk> red_stmt_total_single Pr conf s1 \<omega> (Inr (), r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_single Pr conf (Seq s1 s2) \<omega> (Inl s2, r'')"
 | RedLocalAssign: "\<lbrakk> wd_pure_exp_total Pr CInhale e \<omega>; Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t = v \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single Pr conf (LocalAssign x e) \<omega> (Inr (), (Set {update_store_total \<omega> x v}))"
 | RedLocalAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr CInhale e \<omega> \<rbrakk> \<Longrightarrow> red_stmt_total_single Pr conf (LocalAssign x e) \<omega> (Inr (), Failure)"
 | RedFieldAssign: "\<lbrakk> wd_pure_exp_total Pr CInhale e_r \<omega>; 
                      wd_pure_exp_total Pr CInhale e \<omega>; 
                      Pr \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t = VRef (Address addr);
                      Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t = v \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single Pr conf (FieldAssign e_r f e) \<omega> (Inr (), (Set {update_heap_total_full \<omega> (addr,f) v}))"
 | RedFieldAssignFailure: "\<lbrakk> \<not> wd_pure_exp_total Pr CInhale e_r \<omega> \<or> \<not> wd_pure_exp_total Pr CInhale e \<omega> \<or> (Pr \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t) = (VRef Null) \<rbrakk> \<Longrightarrow> 
               red_stmt_total_single Pr conf (FieldAssign e_r f e) \<omega> (Inr (), Failure)"
 | RedIfTrue: "\<lbrakk> Pr \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool True \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single Pr conf (If e_b s1 s2) \<omega> (Inl s1, Set {\<omega>})"
 | RedIfFalse: "\<lbrakk> Pr \<turnstile> \<langle>e_b; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool False \<rbrakk> \<Longrightarrow> 
                red_stmt_total_single Pr conf (If e_b s1 s2) \<omega> (Inl s2, Set {\<omega>})"


(*

type_synonym config2 = " (stmt + unit, state set)  + 'a result
fun red_stmt_total_single_2 :: "'a program \<Rightarrow> conf \<Rightarrow> ('a stmt_config) set \<Rightarrow> ('a stmt_config) set"
  where "red_stmt_total_single_2 Pr c W W' = 
*)

datatype 'a stmt_config_2 = Failure | Set "( (stmt + unit) \<times> 'a full_total_state) set"

(*
fun small_step_2 :: "'a program \<Rightarrow> conf \<Rightarrow> 'a stmt_config_2 \<Rightarrow> 'a stmt_config_2"
  where 
    "small_step_2 Pr c Failure = Failure"
  | "small_step_2 Pr c (Set W) =
*)

(*
inductive red_stmt_total_single_2 :: "'a program => conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where 
    RedFailureProp: "red_stmt_total_single_2 Pr c (m, Failure) (Inr (), Failure)"
  | RedFailure: "\<lbrakk> \<omega> \<in> W; red_stmt_total_single Pr c s1 \<omega> (m, Failure) \<rbrakk> \<Longrightarrow>
                 red_stmt_total_single_2 Pr c (Inl s1, Set W) (Inr (), Failure)"
  | RedNormal: " \<lbrakk> W' = (\<Union>\<omega>\<in>W. {W' | W'. red_stmt_total_single Pr c s1 \<omega>  (Set W')}) \<rbrakk> \<Longrightarrow>
                red_stmt_total_single_2 Pr c (Inl s1, Set W) (Inr (), Set W')"
*)
(*
inductive red_stmt_total_2 :: "'a program \<Rightarrow> conf \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool" where 
   RedSkip: " red_stmt_total_2 Pr conf ((Inl Skip), r) (Inr (), r)"
 | RedInhale: "red_stmt_total_2 Pr conf (Inl (Inhale A), (Set W)) (Inr (), \<Union>\<omega> \<in> W. (handle_inhale Pr (havoc_inhale conf) A \<omega>))"
 | RedSeq1: "\<lbrakk> red_stmt_total_2 Pr conf (Inl s1, (Set W)) (Inl s'', r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_2 Pr conf (Inl (Seq s1 s2), (Set W)) (Inl (Seq s'' s2), r'')"
 | RedSeq2: "\<lbrakk> red_stmt_total_2 Pr conf (Inl s1, (Set W)) (Inr (), r'') \<rbrakk> \<Longrightarrow>
               red_stmt_total_2 Pr conf (Inl (Seq s1 s2), (Set W)) (Inl s2, r'')"
 | RedFailure: "red_stmt_total_2 Pr conf ( (Inl s), Failure ) (Inr (), Failure)"
*)

  (* RedSeq: "red_stmt_total_2 Pr conf (Seq s1 s2) W (Set W')"*)


inductive red_stmt_total :: "'a program \<Rightarrow> conf \<Rightarrow> stmt \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result \<Rightarrow> bool" where
  RedSkip: "red_stmt_total Pr conf Skip \<omega> (Set {\<omega>})"
(*
| RedAssertTrue: "\<lbrakk> wft Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assert A) \<omega> (Set {\<omega>})"
| RedAssertFalse: "\<lbrakk> wd_assertion Pr RExhale A \<omega> ; \<not> Pr RExhale \<Turnstile> \<langle>A; \<omega>\<rangle> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assert A) \<omega> Failure"
*)
| RedInhale: "red_stmt_total Pr conf (Inhale A) \<omega> (handle_inhale Pr (havoc_inhale conf) A \<omega>)"
| RedExhale: "red_stmt_total Pr conf (Exhale A) \<omega> (handle_exhale Pr {} A \<omega>)"
| RedSeq: "\<lbrakk> red_stmt_total Pr conf s1 \<omega> (Set s) \<rbrakk> \<Longrightarrow> 
             red_stmt_total Pr conf (Seq s1 s2) \<omega> (Set r)"


(*
| RedExhaleTrueAngelic: "\<lbrakk> angelic_exhale conf ; wft Pr RExhale A \<omega> ; a \<in> SA.under (inh Pr RExhale A) \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Exhale A) \<omega> (Set {\<omega> \<ominus> a})"
| RedExhaleTrueDemonic: "\<lbrakk> \<not> angelic_exhale conf ; wft Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Exhale A) \<omega> (Set {(\<omega> \<ominus> a) |a. a \<in> SA.under (inh Pr RExhale A) \<omega> })"

| RedExhaleFalse: "\<lbrakk> wd_assertion Pr RExhale A \<omega> ; \<not> Pr RExhale \<Turnstile> \<langle>A; \<omega>\<rangle> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Exhale A) \<omega> Failure"
| RedAssertFailure: "\<lbrakk> \<not> wd_assertion Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assert A) \<omega> Failure"
| RedInhaleFailure: "\<lbrakk> \<not> wd_assertion Pr RInhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Inhale A) \<omega> Failure"
| RedExhaleFailure: "\<lbrakk> \<not> wd_assertion Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Exhale A) \<omega> Failure"
*)

(*
(* | RedAssumeTrue: "\<lbrakk> wft Pr A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assume A) \<omega> (Set {\<omega>})"
| RedAssumeFalse: "\<lbrakk> wd_assertion Pr RExhale A \<omega> ; \<not> Pr \<Turnstile> \<langle>A; \<omega>\<rangle> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assume A) \<omega> (Set {})"
| RedAssumeFailure: "\<lbrakk> \<not> wd_assertion Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assume A) \<omega> Failure" *)

| RedIfTrue: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] Val (VBool True) ; red_stmt conf Pr s1 \<omega> r \<rbrakk> \<Longrightarrow> red_stmt conf Pr (If b s1 s2) \<omega> r"
| RedIfFalse: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] Val (VBool False) ; red_stmt conf Pr s2 \<omega> r \<rbrakk> \<Longrightarrow> red_stmt conf Pr (If b s1 s2) \<omega> r"
| RedIfFailure: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (If b _ _) \<omega> Failure"

(* May be an overapproximation, but should not be an issue, except maybe for the store *)
| RedSeq: "\<lbrakk> red_stmt conf Pr s1 \<omega> (Set s) ; \<And>x. x \<in> s \<Longrightarrow> (\<exists>s'. red_stmt conf Pr s2 x (Set s') \<and> s' \<subseteq> r)  \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Seq s1 s2) \<omega> (Set r)"
| RedSeqFailure: "\<lbrakk> red_stmt conf Pr s1 \<omega> Failure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Seq s1 s2) \<omega> Failure"

(* No need to handle the case where the variable is not defined, since it is part of well-definedness of a program *)
| RedLocalAssign: "\<lbrakk> Pr \<turnstile> \<langle>e; (\<sigma>, \<gamma>)\<rangle> [\<Down>] (Val v) \<rbrakk> \<Longrightarrow> red_stmt conf Pr (LocalAssign x e) (\<sigma>, \<gamma>) (Set {(\<sigma>(x \<mapsto> v), \<gamma>)})"
| RedLocalAssignFailure: "\<lbrakk> Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (LocalAssign x e) \<omega> Failure"

| RedFieldAssign: "\<lbrakk> Pr \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] (Val (VRef (Address a))) ;  can_write (get_m \<omega>) (a, f) ; Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] (Val v) \<rbrakk>
  \<Longrightarrow> red_stmt conf Pr (FieldAssign r f e) \<omega> (Set {field_assign \<omega> (a, f) v})"

| RedFieldAssignFailureNull: "\<lbrakk> Pr \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] (Val (VRef Null)) \<rbrakk> \<Longrightarrow> red_stmt conf Pr (FieldAssign r f e) \<omega> Failure"
| RedFieldAssignFailurePerm: "\<lbrakk> Pr \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] (Val (VRef (Address a))) ; \<not> (can_write (get_m \<omega>) (a, f)) \<rbrakk> \<Longrightarrow> red_stmt conf Pr (FieldAssign r f e) \<omega> Failure"
| RedFieldAssignFailureRef: "\<lbrakk> Pr \<turnstile> \<langle>r; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (FieldAssign r f e) \<omega> Failure"
| RedFieldAssignFailureExp: "\<lbrakk> Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (FieldAssign r f e) \<omega> Failure"


(* Failure only when program not well-defined? *)
| RedLabel: "red_stmt conf Pr (Label l) (\<sigma>, \<tau>, \<phi>) (Set {(\<sigma>, \<tau>(l \<mapsto> \<phi>), \<phi>)})"

(* Overapproximation possible *)
| RedScope: "\<lbrakk> \<And>\<sigma>'. \<sigma>' \<in> declare_var_list l \<sigma> \<Longrightarrow> (\<exists>s'. red_stmt conf Pr s (\<sigma>', \<tau>, \<phi>) (Set s') \<and> s' \<subseteq> r) \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Scope l s) (\<sigma>, \<tau>, \<phi>) (Set (unshift_state (length l) ` r))"

| RedFoldSkip: "\<lbrakk> equi_predicate conf ; \<not> ghost_assert conf\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Fold _ _ _) \<omega> (Set {\<omega>})"
| RedFoldAssert: "\<lbrakk> equi_predicate conf ; ghost_assert conf ;  red_stmt conf Pr (Assert (AccPredicate p l f)) \<omega> r \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Fold p l f) \<omega> r"
| RedUnfoldSkip: "\<lbrakk> equi_predicate conf ; \<not> ghost_assert conf\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Unfold _ _ _) \<omega> (Set {\<omega>})"
| RedUnfoldAssert: "\<lbrakk> equi_predicate conf ; ghost_assert conf ; red_stmt conf Pr (Assert (AccPredicate p l f)) \<omega> r \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Unfold p l f) \<omega> r"

| RedApplySkip: "\<lbrakk> equi_wands conf ; \<not> ghost_assert conf\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Apply _ _) \<omega> (Set {\<omega>})"
| RedApplyAssert: "\<lbrakk> equi_wands conf ; ghost_assert conf ; red_stmt conf Pr (Assert (A --* B)) \<omega> r\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Apply A B) \<omega> (Set {\<omega>})"
| RedPackageSkip: "\<lbrakk> equi_wands conf ; \<not> ghost_assert conf\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Package _ _) \<omega> (Set {\<omega>})"
| RedPackageAssert: "\<lbrakk> equi_wands conf ; ghost_assert conf ; red_stmt conf Pr (Assert (A --* B)) \<omega> r\<rbrakk> \<Longrightarrow> red_stmt conf Pr (Package A B) \<omega> (Set {\<omega>})"

| RedWhileTrue: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] Val (VBool True) ; red_stmt conf Pr s \<omega> (Set r1) ; \<And>x. x \<in> r1 \<Longrightarrow> (\<exists>r2'. red_stmt conf Pr (While b I s) x (Set r2') \<and> r2' \<subseteq> r2)\<rbrakk>
  \<Longrightarrow> red_stmt conf Pr (While b I s) \<omega> (Set r2)"
| RedWhileFalse: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] Val (VBool False) \<rbrakk> \<Longrightarrow> red_stmt conf Pr (While b _ _) \<omega> (Set {\<omega>})"
| RedWhileFailure: "\<lbrakk> Pr \<turnstile> \<langle>b ; \<omega>\<rangle> [\<Down>] VFailure \<rbrakk> \<Longrightarrow> red_stmt conf Pr (While b _ _) \<omega> Failure"

(* Only rets and args defined when executing a method call, also empty trace *)
(* If method does not exist, or wrong number of args or rets: Not well-defined *)
(* Concrete method *)
| RedMethod: "\<lbrakk> methods Pr name = Some m ; body m = Some s; length vals = length x ; list_all2 (\<lambda>xx v. \<sigma> xx = Some v) x vals ;
  \<And>\<sigma>'. \<sigma>' \<in> declare_var_list (rets m) \<sigma> \<Longrightarrow> (\<exists>s'. red_stmt conf Pr s (shift_and_add_list \<sigma>' vals, \<phi>) (Set s') \<and> s' \<subseteq> r) \<rbrakk>
  \<Longrightarrow> red_stmt conf Pr (MethodCall y name x) \<omega> (Set (unshift_state (length (args m)) ` r))"

(* Abstract method *)
definition ver :: "configuration \<Rightarrow> 'a program \<Rightarrow> stmt \<Rightarrow> 'a state \<Rightarrow> bool" where
  "ver conf Pr s \<omega> \<longleftrightarrow> (\<exists>r. red_stmt conf Pr s \<omega> (Set r))"
*)

end