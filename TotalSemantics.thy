theory TotalSemantics
imports Viper.ViperLang TotalExpressions "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" TotalUtil
begin

(*datatype 'a result = Failure | Set (select_set: "'a full_total_state set")*)
datatype 'a standard_result = RMagic | RFailure | RNormal "'a full_total_state"


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
      Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)); 
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
       red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f (PureExp e_p))) \<omega> (RNormal \<omega>')"
 | InhAssumeAccFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f (PureExp e_p))) \<omega> RMagic"
 | InhAssumeAccFail2: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
      (\<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega> \<or> p < 0)\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f (PureExp e_p))) \<omega> RFailure"
(** inhale/assume acc(e.f, wildcard) **)
(*  \<omega>' \<in> plus_total_full_set {\<omega>} 
        singleton_total_wildcard havoc_new (r,f) (get_heap_total_full \<omega> (r,f)) (get_store_total \<omega>) (get_trace_total \<omega>)) *)
 | InhAccWildcard: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       (wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>);
       \<omega>' \<in> inhale_perm_single havoc_new \<omega> (a,f) None \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f Wildcard)) \<omega> (RNormal \<omega>')"
  | InhAssumeAccWildcardFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> 
    red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f Wildcard)) \<omega> RMagic"
 | InhAssumeAccWildcardFail2: 
     "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)); 
        Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       \<not>wd_pure_exp_total Pr \<Delta> CInhale e_r \<omega>\<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> havoc_new (Atomic (Acc e_r f Wildcard)) \<omega> RFailure"
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
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) m (ExhaleNormal m')"
  | ExhAccFail1: 
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
      (r = Null \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega> \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_p \<omega> \<or> p < 0)\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) m ExhaleFailure"
  | ExhAccFail2:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       Pr, \<Delta> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_p \<omega>;
       p \<ge> 0; 
       \<not> (pgte (m(a,f)) (Abs_prat p)) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) m ExhaleFailure"

\<comment>\<open>exhale acc(e.f, wildcard)\<close>
 \<comment>\<open>Exhaling wildcard removes some non-zero permission this is less than the current permission held\<close>
  | ExhAccWildcard:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       p > 0; 
       pgt (m(a,f)) (Abs_prat p);
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       m' = m( (a,f) := Abs_prat ( (Rep_prat (m((a, f)))) - p) ) \<rbrakk> \<Longrightarrow>
       red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f Wildcard)) m (ExhaleNormal m')"
  | ExhAccWildcardFail1:
    "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
      (r = Null \<or> \<not>wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>)\<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f Wildcard)) m ExhaleFailure"
  | ExhAccWildcardFail2:
    "\<lbrakk> \<omega> = update_mask_total_full \<omega>0 m;
       Pr, \<Delta> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a));
       wd_pure_exp_total Pr \<Delta> (CExhale locs) e_r \<omega>;
       (m(a,f)) = pnone \<rbrakk> \<Longrightarrow>
      red_exhale Pr \<Delta> \<omega>0 (Atomic (Acc e_r f Wildcard)) m ExhaleFailure"
 
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