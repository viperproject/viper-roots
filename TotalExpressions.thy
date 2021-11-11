theory TotalExpressions
imports Viper.ViperLang Viper.ValueAndBasicState TotalViperState Viper.Binop Viper.DeBruijn Viper.PredicatesUtil TotalUtil
begin

(* duplicated: TODO share it *)
(*
fun the_address :: "'a val \<Rightarrow> address" where
  "the_address (VRef (Address a)) = a"
| "the_address _ = undefined"
*)

fun the_rat :: "'a val \<Rightarrow> rat" where
  "the_rat (VPerm r) = r"
| "the_rat _ = undefined"


fun wd_binop :: "binop \<Rightarrow> 'a val \<Rightarrow> 'a val \<Rightarrow> bool"
  where 
    "wd_binop IntDiv v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop PermDiv v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop Mod v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop _ _ _ = True"

datatype 'a standard_result = RMagic | RFailure | RNormal "'a full_total_state"

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {l |l. pgt (get_mh_total_full \<omega> l) pnone}"


definition inhale_perm_single :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> prat option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single \<omega> l p_opt =
      {\<omega>'| \<omega>' q. 
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mh_total_full \<omega> l) q) \<and>
               \<omega>' = update_mask_total_full \<omega> ((get_mh_total_full \<omega>)(l := (padd (get_mh_total_full \<omega> l) q)))
       }"

definition inhale_perm_single_pred :: "'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> prat option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single_pred \<omega> ploc p_opt = 
      {\<omega>'| \<omega>' q.   
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mp_total_full \<omega> ploc) q) \<and>
               \<omega>' = update_pmask_total_full \<omega> ((get_mp_total_full \<omega>)(ploc := (padd (get_mp_total_full \<omega> ploc) q)))
       }"

fun inh_if_if_total :: "bool \<Rightarrow> bool \<Rightarrow> 'a full_total_state \<Rightarrow> 'a standard_result"  where
  "inh_if_if_total False _ _ = RFailure"
| "inh_if_if_total True False _ = RMagic"
| "inh_if_if_total True True \<omega> = RNormal \<omega>"

(* potential duplicate *)
fun sub_expressions_exp_or_wildcard :: "pure_exp exp_or_wildcard \<Rightarrow> pure_exp set" where
  "sub_expressions_exp_or_wildcard (PureExp e) = {e}"
| "sub_expressions_exp_or_wildcard Wildcard = {}"

(* TODO: duplicate with ViperLang.SemanticsPerm, put in some common theory *)
fun sub_expressions_atomic :: "pure_exp atomic_assert \<Rightarrow> pure_exp set" where
  "sub_expressions_atomic (Pure e) = {e}"
| "sub_expressions_atomic (Acc x f p) = {x} \<union> sub_expressions_exp_or_wildcard p"
| "sub_expressions_atomic (AccPredicate P exps p) = set exps \<union> sub_expressions_exp_or_wildcard p"

text\<open>Pure expression evaluation, where the set of heap locations expresses the set of readable locations
(if no set is provided, then all locations can be read).
\<close>
inductive red_pure_exp_total :: "program \<Rightarrow> 'a interp \<Rightarrow> (heap_loc set) option \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a extended_val \<Rightarrow> bool"
  ("_, _, _ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t _)" [51,51,51,0,51,51] 81) and
   red_pure_exps_total :: "program \<Rightarrow> 'a interp \<Rightarrow> (heap_loc set) option \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> ('a extended_val) list \<Rightarrow> bool" and
   red_inhale :: "program \<Rightarrow>  'a interp \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a standard_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp"
  where
\<comment>\<open>Atomic inhale\<close>
  InhAcc: 
    "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
       Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       W' = inhale_perm_single \<omega> (the_address r,f) (Some (Abs_prat p)) \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (Acc e_r f (PureExp e_p))) \<omega> 
                (inh_if_if_total (p \<ge> 0) (W' \<noteq> {} \<and> r \<noteq> Null) (SOME \<omega>'. \<omega>' \<in> W' \<and> R \<omega>'))"
| InhAccPred:
    "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       red_pure_exps_total Pr \<Delta> (Some (get_valid_locs \<omega>)) e_args \<omega> (map Val v_args);
       W' = inhale_perm_single_pred \<omega> (pred_id, v_args) (Some (Abs_prat p)) \<rbrakk> \<Longrightarrow>       
       red_inhale Pr \<Delta> R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> 
                (inh_if_if_total (p \<ge> 0) (W' \<noteq> {} \<and> r \<noteq> Null) (SOME \<omega>'. \<omega>' \<in> W' \<and> R \<omega>'))"
| InhAccWildcard: 
    "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       W' = inhale_perm_single \<omega> (the_address r,f) None \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (Acc e_r f Wildcard)) \<omega> 
                   (inh_if_if_total True (W' \<noteq> {} \<and> r \<noteq> Null) (SOME \<omega>'. \<omega>' \<in> W' \<and> R \<omega>'))"
| InhAccPredWildcard: 
    "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       W' = inhale_perm_single_pred \<omega> (pred_id, v_args) None \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> 
                 (inh_if_if_total True (W' \<noteq> {} \<and> r \<noteq> Null) (SOME \<omega>'. \<omega>' \<in> W' \<and> R \<omega>'))"
| InhPureNormalMagic: 
    "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> R (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"
| SubFailure: 
    "\<lbrakk> e \<in> sub_expressions_atomic A; Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta>  R (Atomic A) \<omega> RFailure"

\<comment>\<open>Connectives inhale\<close>
| InhSepNormal: 
   "\<lbrakk> red_inhale Pr \<Delta> R A \<omega> (RNormal \<omega>''); 
      red_inhale Pr \<Delta> R B \<omega>'' res\<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> R (A && B) \<omega> res"
| InhSepFailureMagic:
   "\<lbrakk> red_inhale Pr \<Delta> R A \<omega> resA; 
      resA = RFailure \<or> resA = RMagic \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> R (A && B) \<omega> resA"
| InhImpTrue:
 "\<lbrakk> 
    Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)); 
    red_inhale Pr \<Delta> R A \<omega> res \<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> R (Imp e A) \<omega> res"
| InhImpFalse:
 "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
    red_inhale Pr \<Delta> R (Imp e A) \<omega> (RNormal \<omega>)"
| InhImpFailure:
 "\<lbrakk> Pr, \<Delta>, Some (get_valid_locs \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
   red_inhale Pr \<Delta> R (Imp e A) \<omega> RFailure"

\<comment>\<open>Pure expression evaluation\<close>


\<comment>\<open>Atomic expressions\<close>
| RedLit: "Pr, \<Delta>, HLOpt \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l)"
| RedVar: "\<lbrakk> \<sigma> n = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Var n; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"
| RedResult: "\<lbrakk> \<sigma> 0 = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Result; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"

\<comment>\<open>Binop and Unop\<close>
| RedBinopLazy: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinop: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop_lazy v1 bop = None; eval_binop v1 bop v2 = BinopNormal v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinopRightFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure;  eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopOpFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop v1 bop v2 = BinopOpFailure ; eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* Division by 0 *)
| RedBinopLeftFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

| RedUnop: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v; eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
| RedUnopFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Cond\<close>
| RedCondExpTrue: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) ; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFalse: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) ; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Old\<close>
| RedOld: "\<lbrakk> t l = Some \<phi> ; Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; (\<sigma>, t, \<phi>)\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Old l e; (\<sigma>, t, _)\<rangle> [\<Down>]\<^sub>t v"
| RedOldFailure: "\<lbrakk> t l = None \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Old l e ; (_, t, _)\<rangle> [\<Down>]\<^sub>t VFailure" 

\<comment>\<open>Heap lookup\<close>
| RedField: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) ; get_heap_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow> 
       Pr, \<Delta>, HLOpt \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t option_fold (\<lambda>l. if (a,f) \<in> l then Val v else VFailure) (Val v) HLOpt"
| RedFieldFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Permission introspection\<close>
| RedPermNull: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
| RedPerm: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_prat (get_mask_total_full \<omega> (a, f))))"
| RedPermFailure: "\<lbrakk> Pr, \<Delta>, HLOpt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, HLOpt \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)
(*
\<comment>\<open>Unfolding\<close>
| RedUnfolding: "\<lbrakk> 
         Pr, \<Delta>, HLOpt \<turnstile> \<langle>e_arg; \<omega>\<rangle> [\<Down>]\<^sub>t v_arg;
        ViperLang.predicates Pr p = Some pred;
        ViperLang.predicate_decl.body pred = Some pred_body;
        red_inhale Pr \<Delta> False pred_body \<omega> (RNormal \<omega>');
            
 \<rbrakk> \<Longrightarrow>
     Pr, \<Delta>, HLOpt \<turnstile> \<langle>Unfolding p [e_arg] p_body; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
*)

(*| RedPropagateFailure: "\<lbrakk> e \<in> sub_pure_exp e' ; Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>  Pr, \<Delta> \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"*)
(*| RedUnfoldingPermNegFailure: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v) ; v < 0 \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Unfolding p exps f e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"*)
(*
(* perm(P(...)) = 0 if equirecursive *)
| RedPermPred: "\<lbrakk> list_all2 (\<lambda>e v. Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vals \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_prat (get_pm \<omega> (p, vals))))"
*)
(*| RedLet: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta> \<turnstile> \<langle>e2; shift_and_add_state \<omega> v1\<rangle> [\<Down>]\<^sub>t r \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedExistsTrue: "\<lbrakk> v \<in> set_from_type \<Delta> ty ; Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool True) ;
  \<And>v'. \<exists>b. Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v'\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
| RedExistsFalse: "\<lbrakk> \<And>v. v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
| RedForallTrue: "\<lbrakk> \<And>v. v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
| RedForallFalse: "\<lbrakk> v \<in> set_from_type \<Delta> ty ; Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"*)
(*
| RedExistsFailure: "\<lbrakk> v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedForallFailure: "\<lbrakk> v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"*)



inductive unfold_rel :: "program \<Rightarrow> 'a interp \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> prat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where UnfoldRelStep: 
                    "\<lbrakk> ViperLang.predicates Pr pred_id = Some pred_decl;
                     ViperLang.predicate_decl.body pred_decl = Some pred_body;
                     m = get_pmask_total_full \<omega>;
                     pgte (m (pred_id,vs)) q;
                     m' = m( (pred_id,vs) := psub (m (pred_id, vs)) q);
                     \<omega>2 = (nth_option vs, get_trace_total \<omega>, update_pmask_total (get_mh_total_full \<omega>) m');
                     red_inhale Pr \<Delta> (\<lambda>_. True) (syntactic_mult (Rep_prat q) pred_body) \<omega>2 (RNormal \<omega>') \<rbrakk> \<Longrightarrow> 
                     unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>'"

definition unfold_rel_general
  where "unfold_rel_general Pr \<Delta> \<omega> \<omega>' \<equiv> \<exists> pred_id vs q. unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>'"

definition unfold_rel_multi
  where "unfold_rel_multi Pr \<Delta>  \<equiv> rtranclp (unfold_rel_general Pr \<Delta>)"

coinductive unfold_consistent :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where 
  unfold_step: "\<lbrakk> \<And> pred_id vs q. pgt (get_pmask_total_full \<omega> (pred_id,vs)) q \<Longrightarrow>
                     \<exists>\<omega>'. unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>' \<and> unfold_consistent Pr \<Delta> \<omega>' \<rbrakk> \<Longrightarrow>
                  unfold_consistent Pr \<Delta> \<omega>"

(*  this definition here is incorrect since it does not account for non-determinism
definition unfold_consistent where
 "unfold_consistent Pr \<Delta> \<omega> \<equiv> 
          \<forall> \<omega>' pred_id vs q. 
               (unfold_rel_multi Pr \<Delta> \<omega> \<omega>' \<and> pgt (get_pmask_total_full \<omega>' (pred_id,vs)) q) \<longrightarrow>
               (\<exists>\<omega>''. unfold_rel Pr \<Delta> pred_id vs q \<omega>' \<omega>'')"
*)

text \<open>Expression evaluation as a function. Using this function makes sense, when it is known that 
e is well-defined and is deterministic (for example, if e is the body of a predicate)\<close>
fun red_pure_exp_total_fun :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a val"
  where "red_pure_exp_total_fun Pr \<Delta> e \<omega> = (SOME v. Pr, \<Delta>, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"

fun red_pure_exps_total_fun :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> ('a val) list"
  where "red_pure_exps_total_fun Pr \<Delta> es \<omega> = (SOME vs. red_pure_exps_total Pr \<Delta> None es \<omega> (map Val vs))"

fun extract_address_from_val :: "'a val \<Rightarrow> address"
  where 
    "extract_address_from_val (VRef (Address a)) = a"
  | "extract_address_from_val _ = undefined"

fun extract_perm_from_val :: "'a val \<Rightarrow> rat"
  where 
    "extract_perm_from_val (VPerm r) = r"
  | "extract_perm_from_val _ = undefined"

fun is_positive_permission :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where 
    "is_positive_permission Pr \<Delta> Wildcard \<omega> = True"
  | "is_positive_permission Pr \<Delta> (PureExp e) \<omega> = (extract_perm_from_val (red_pure_exp_total_fun Pr \<Delta> e \<omega>) > 0)"


fun assertion_heap_snapshot :: "program \<Rightarrow> 'a interp \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> heap_loc set"
  where 
   "assertion_heap_snapshot Pr \<Delta> (Atomic (Pure e)) \<omega> = {}"
 | "assertion_heap_snapshot Pr \<Delta> (Atomic (Acc e f e_p)) \<omega> = 
             (if is_positive_permission Pr \<Delta> e_p \<omega> then 
                  {(extract_address_from_val (red_pure_exp_total_fun Pr \<Delta> e \<omega>), f)} 
              else {})"
 | "assertion_heap_snapshot Pr \<Delta> (Atomic (AccPredicate pred_id e_args e_p)) \<omega> = 
             (if is_positive_permission Pr \<Delta> e_p \<omega> then
                fst (get_pheap_total_full \<omega> (pred_id, red_pure_exps_total_fun Pr \<Delta> e_args \<omega>))
              else {})"
 | "assertion_heap_snapshot Pr \<Delta> (Imp e A) \<omega> =
             (if red_pure_exp_total_fun Pr \<Delta> e \<omega> = VBool True then 
                 assertion_heap_snapshot Pr \<Delta> A \<omega> 
              else {})"
 | "assertion_heap_snapshot Pr \<Delta> (A && B) \<omega> = assertion_heap_snapshot Pr \<Delta> A \<omega> \<union> assertion_heap_snapshot Pr \<Delta> B \<omega>"      
 | "assertion_heap_snapshot Pr \<Delta> _ \<omega> = undefined" (* wands and quantified permissions not supported *)

fun assertion_predicate_snapshot :: "program \<Rightarrow> 'a interp \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc set"
  where 
   "assertion_predicate_snapshot Pr \<Delta> (Atomic (Pure e)) \<omega> = {}"
 | "assertion_predicate_snapshot Pr \<Delta> (Atomic (Acc e f e_p)) \<omega> = {}"
 | "assertion_predicate_snapshot Pr \<Delta> (Atomic (AccPredicate pred_id e_args e_p)) \<omega> = 
             (if is_positive_permission Pr \<Delta> e_p \<omega> then
                {(pred_id, red_pure_exps_total_fun Pr \<Delta> e_args \<omega>)} \<union> 
                snd (get_pheap_total_full \<omega> (pred_id, red_pure_exps_total_fun Pr \<Delta> e_args \<omega>))
              else {})"
 | "assertion_predicate_snapshot Pr \<Delta> (Imp e A) \<omega> =
             (if red_pure_exp_total_fun Pr \<Delta> e \<omega> = VBool True then 
                 assertion_predicate_snapshot Pr \<Delta> A \<omega> 
              else {})"
 | "assertion_predicate_snapshot Pr \<Delta> (A && B) \<omega> = assertion_predicate_snapshot Pr \<Delta> A \<omega> \<union> assertion_predicate_snapshot Pr \<Delta> B \<omega>"      
 | "assertion_predicate_snapshot Pr \<Delta> _ \<omega> = undefined" (* wands and quantified permissions not supported *)


definition pheap_consistent :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
 "pheap_consistent Pr \<Delta> \<omega> \<equiv> 
          \<forall> \<omega>' pred_id vs pred_decl. 
               (unfold_rel_multi Pr \<Delta> \<omega> \<omega>' \<and> pgt (get_pmask_total_full \<omega>' (pred_id,vs)) pnone \<and>
                ViperLang.predicates Pr pred_id = Some pred_decl) \<longrightarrow>
                option_fold (\<lambda> pred_body. get_pheap_total_full \<omega> (pred_id, vs) = 
                              (assertion_heap_snapshot Pr \<Delta> pred_body \<omega>, assertion_predicate_snapshot Pr \<Delta> pred_body \<omega>) )
                            True
                            (ViperLang.predicate_decl.body pred_decl)"



datatype inh_exh_conf = CInhale | CExhale "heap_loc set"
(*
(* can't show this, since need to take typing into account *)
lemma wd_binop_total: 
  assumes "wd_binop bop v1 v2"
  shows "binop_eval v1 v2 \<noteq> None"
  oops

fun wd_pure_exp_total :: "program \<Rightarrow> 'a interp \<Rightarrow> inh_exh_conf \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
  "wd_pure_exp_total Pr \<Delta> c (ELit l) \<omega> \<longleftrightarrow> True"
| "wd_pure_exp_total Pr \<Delta> c (Var n) \<omega> \<longleftrightarrow> True"
| "wd_pure_exp_total Pr \<Delta> c (Unop unop e) \<omega> \<longleftrightarrow> (wd_pure_exp_total Pr \<Delta> c e \<omega>)"
| "wd_pure_exp_total Pr \<Delta> c (Binop e1 bop e2) \<omega> \<longleftrightarrow> 
     (wd_pure_exp_total Pr \<Delta> c e1 \<omega> \<and> ((\<forall>v1. Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 \<longrightarrow> eval_binop_lazy v1 bop = None \<longrightarrow> 
                  ((\<forall>v2. Pr, \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 \<longrightarrow> wd_binop bop v1 v2) \<and> (wd_pure_exp_total Pr \<Delta> c e2 \<omega>)))))"
| "wd_pure_exp_total Pr \<Delta> c (CondExp e1 e2 e3) \<omega> \<longleftrightarrow> 
     wd_pure_exp_total Pr \<Delta> c e1 \<omega> \<and> (if ((Pr,\<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True))) then wd_pure_exp_total Pr \<Delta> c e2 \<omega> else wd_pure_exp_total Pr \<Delta> c e3 \<omega>)" 
| "wd_pure_exp_total Pr \<Delta> CInhale (FieldAcc e f) \<omega> \<longleftrightarrow> 
    wd_pure_exp_total Pr \<Delta> CInhale e \<omega> \<and> (\<forall>l. (Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address l))) \<longrightarrow> (pgt (get_mask_total_full \<omega> (l,f)) pnone))"
| "wd_pure_exp_total Pr \<Delta> (CExhale locs) (FieldAcc e f) \<omega> \<longleftrightarrow> 
    wd_pure_exp_total Pr \<Delta> (CExhale locs) e \<omega> \<and>
    (\<forall>l. ( (Pr,\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address l))) \<longrightarrow> (l,f) \<in> locs))"
| "wd_pure_exp_total Pr \<Delta> c (Perm e f) \<omega> \<longleftrightarrow> 
     wd_pure_exp_total Pr \<Delta> c e \<omega> \<and> (\<forall>r. (Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)) \<longrightarrow> r \<noteq> Null)"
| "wd_pure_exp_total Pr \<Delta> c _ _  \<longleftrightarrow> False"

(* TODO *)
(*
| "wd_pure_exp_total conf Pr \<Delta> (PermPred p exps) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (FunApp f exps) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> Result \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Unfolding p exps f e) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Let e1 e2) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (PExists ty e) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (PForall ty e) \<omega> \<longleftrightarrow> False" 
*)
*)

end