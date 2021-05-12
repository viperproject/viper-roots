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

(*
  Impure 'i
  | Imp 'p "('p, 'i) assert"
  | InhaleExhale "('p, 'i) assert" "('p, 'i) assert"
  | Star "('p, 'i) assert" "('p, 'i) assert" (infixl "&&" 60)
  | Wand "('p, 'i) assert" "('p, 'i) assert" (infixl "--*" 60)
  | ForAll vtyp "('p, 'i) assert"
*)

inductive red_stmt_total :: "'a program \<Rightarrow> stmt \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result \<Rightarrow> bool" where
  RedSkip: "red_stmt_total Pr Skip \<omega> (Set {\<omega>})"
| RedSeq: "\<lbrakk> red_stmt_total Pr s1 \<omega> (Set s) ; \<And>x. x \<in> s \<Longrightarrow> (\<exists>s'. red_stmt_total Pr s2 x (Set s') \<and> s' \<subseteq> r)  \<rbrakk> \<Longrightarrow> 
            red_stmt_total Pr (Seq s1 s2) \<omega> (Set r)"


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

fun handle_inhale :: "'a program \<Rightarrow> bool \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
  where 
(** connectives **)
    "handle_inhale Pr havoc_new (A && B) \<omega> = 
       map_result (handle_inhale Pr havoc_new B) (handle_inhale Pr havoc_new A \<omega>)"
  | "handle_inhale Pr havoc_new (Imp e A) \<omega> = 
        (if (red_pure_exp_total Pr e \<omega>) = VBool True then (handle_inhale Pr havoc_new A \<omega>) else Set {\<omega>})"
(** inhale specific **)
  | "handle_inhale Pr havoc_new (Atomic (Acc e_r f e_p)) \<omega> =
       (let r = the_address (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>))
        in 
            (if p \<ge> 0 then 
               Set (plus_total_set {\<omega>} 
                      ((singleton_total havoc_new (r,f) (Abs_prat p) (get_heap_total_full \<omega> (r,f)) (get_store_total \<omega>) (get_trace_total \<omega>))))
             else Failure))"
  | "handle_inhale Pr havoc_new (Atomic (AccWildcard e_r f)) \<omega> =
        (let r = the_address (red_pure_exp_total Pr e_r \<omega>) in
            Set (plus_total_set {\<omega>} 
                ((singleton_total_pred (r,f) (\<lambda>p v. (pgt p pnone) \<and> (\<not>havoc_new \<longrightarrow> v = get_heap_total_full \<omega> (r,f))) (get_store_total \<omega>) (get_trace_total \<omega>)))))"
  | "handle_inhale Pr havoc_new (InhaleExhale A B) \<omega> = handle_inhale Pr havoc_new A \<omega>"
  | "handle_inhale Pr havoc_new (Atomic (Pure e)) \<omega> =
        (if wd_pure_exp_total Pr CInhale e \<omega> then  
          (if (red_pure_exp_total Pr e \<omega>) = VBool True then Set {\<omega>} else Set {})
         else Failure)"
(* todo *)
  | "handle_inhale Pr havoc_new (ForAll v va) \<omega> = undefined"
  | "handle_inhale Pr havoc_new (Atomic (AccPredicate va vb vc)) \<omega> = undefined"
  | "handle_inhale Pr havoc_new (Atomic (AccPredicateWildcard va vb)) \<omega> = undefined"
  | "handle_inhale Pr havoc_new (A --* B) \<omega> = undefined"


fun handle_exhale :: "'a program \<Rightarrow> heap_loc set \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result"
  where
    "handle_exhale Pr def_locs (A && B) \<omega> = 
       map_result (handle_exhale Pr def_locs B) (handle_exhale Pr def_locs A \<omega>)"
  | "handle_exhale Pr def_locs (Imp e A) \<omega> = 
        (if (red_pure_exp_total Pr e \<omega>) = VBool True then (handle_exhale Pr def_locs A \<omega>) else Set {\<omega>})"
  | "handle_exhale Pr def_locs (Atomic (Acc e_r f e_p)) \<omega> = 
       (let r = the_address (red_pure_exp_total Pr e_r \<omega>);
            p = (un_VPerm (red_pure_exp_total Pr e_p \<omega>)) 
        in 
            if p \<ge> 0 \<and> pgte (get_mask_total_full \<omega> (r,f) ) (Abs_prat p) then
             Set {\<omega>'| \<omega>' \<omega>_r. \<omega>_r \<in> singleton_total_only_mask (r,f) (Abs_prat p) (get_store_total \<omega>) (get_trace_total \<omega>) \<and> \<omega>' |\<oplus>|\<^sub>t \<omega>_r = Some \<omega>}
            else 
             Failure
            )"
  | "handle_exhale Pr def_locs (Atomic (AccWildcard e_r f)) \<omega> =
       (let r = the_address (red_pure_exp_total Pr e_r \<omega>)
        in 
          if pgt (get_mask_total_full \<omega> (r,f) ) pnone then
           Set {\<omega>'| \<omega>' \<omega>_r. \<omega>_r \<in> (singleton_total_pred (r,f) (\<lambda>p v. pgt ((get_mask_total_full \<omega>) (r,f)) p) (get_store_total \<omega>) (get_trace_total \<omega>)) \<and>
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

(*
inductive red_stmt :: "'a program \<Rightarrow> stmt \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result \<Rightarrow> bool" where

  RedSkip: "red_stmt conf Pr Skip \<omega> (Set {\<omega>})"
(*
| RedAssertTrue: "\<lbrakk> wft Pr RExhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assert A) \<omega> (Set {\<omega>})"
| RedAssertFalse: "\<lbrakk> wd_assertion Pr RExhale A \<omega> ; \<not> Pr RExhale \<Turnstile> \<langle>A; \<omega>\<rangle> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Assert A) \<omega> Failure"
*)
| RedInhale: "\<lbrakk> wd_assertion Pr RInhale A \<omega> \<rbrakk> \<Longrightarrow> red_stmt conf Pr (Inhale A) \<omega> (Set ({\<omega>' |\<omega>'. \<omega>' \<in> {\<omega>} \<otimes> inh Pr RInhale A}))"

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
*)
end