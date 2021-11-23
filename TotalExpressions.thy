theory TotalExpressions
imports Viper.ViperLang Viper.ValueAndBasicState TotalViperState Viper.Binop Viper.DeBruijn Viper.PredicatesUtil TotalUtil
begin

section \<open>Pure expression evaluation and inhale\<close>

fun wd_binop :: "binop \<Rightarrow> 'a val \<Rightarrow> 'a val \<Rightarrow> bool"
  where 
    "wd_binop IntDiv v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop PermDiv v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop Mod v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop _ _ _ = True"

datatype 'a standard_result = RMagic | RFailure | RNormal "'a full_total_state"

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {lh |lh. pgt (get_mh_total_full \<omega> lh) pnone}"


definition inhale_perm_single :: "('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> prat option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single R \<omega> lh p_opt =
      {\<omega>'| \<omega>' q. R \<omega>' \<and>
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mh_total_full \<omega> lh) q) \<and>
               \<omega>' = update_mh_total_full \<omega> ((get_mh_total_full \<omega>)(lh := (padd (get_mh_total_full \<omega> lh) q)))
       }"

definition inhale_perm_single_pred :: "('a full_total_state \<Rightarrow> bool) \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> prat option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single_pred R \<omega> lp p_opt = 
      {\<omega>'| \<omega>' q. R \<omega>' \<and>  
               option_fold ((=) q) (q \<noteq> pnone) p_opt \<and>
               pgte pwrite (padd (get_mp_total_full \<omega> lp) q) \<and>
               \<omega>' = update_mp_total_full \<omega> ((get_mp_total_full \<omega>)(lp := (padd (get_mp_total_full \<omega> lp) q)))
       }"

inductive th_result_rel :: "bool \<Rightarrow> bool \<Rightarrow> ('a full_total_state) set \<Rightarrow> 'a standard_result \<Rightarrow> bool"  where
  THResultNormal: "\<lbrakk> \<omega> \<in> W \<rbrakk> \<Longrightarrow> th_result_rel True True W (RNormal \<omega>)"
| THResultMagic: "th_result_rel True False W RMagic"
| THResultFailure: "th_result_rel False b W RFailure"


inductive_cases THResultNormal_case: "th_result_rel True True W (RNormal \<omega>)"

lemma THResultNormal_alt: "\<lbrakk> \<omega> \<in> W; A; B\<rbrakk> \<Longrightarrow> th_result_rel A B W (RNormal \<omega>)"
  by (cases A; cases B) (auto intro: THResultNormal)



lemma th_result_rel_normal: 
  assumes "th_result_rel a b W (RNormal \<omega>)"
  shows "a \<and> b \<and> \<omega> \<in> W"
  using assms
  by (cases) auto

lemma th_result_rel_failure: 
  assumes "th_result_rel False  b W res"
  shows "res = RFailure"
  using assms
  by (cases) auto

lemma th_result_rel_magic: 
  assumes "th_result_rel True False W res"
  shows "res = RMagic"
  using assms
  by (cases) auto

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
inductive red_pure_exp_total :: "program \<Rightarrow> 'a interp \<Rightarrow> heap_loc set \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a extended_val \<Rightarrow> bool"
  ("_, _, _ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t _)" [51,51,51,0,51,51] 81) and
   red_pure_exps_total :: "program \<Rightarrow> 'a interp \<Rightarrow> heap_loc set \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> (('a val) list) option \<Rightarrow> bool" and
   red_inhale :: "program \<Rightarrow>  'a interp \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a standard_result \<Rightarrow> bool"
  for Pr :: program and \<Delta> :: "'a interp"
  where
\<comment>\<open>Atomic inhale\<close>
  InhAcc: 
    "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r); 
       Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p); 
       W' = inhale_perm_single R \<omega> (the_address r,f) (Some (Abs_prat p));
       th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
| InhAccPred:
    "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
       red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (Some v_args);
       W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) (Some (Abs_prat p));
       th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' res \<rbrakk> \<Longrightarrow>       
       red_inhale Pr \<Delta> R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res"
| InhAccWildcard: 
    "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
       W' = inhale_perm_single R \<omega> (the_address r,f) None;
       th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (Acc e_r f Wildcard)) \<omega> res"
| InhAccPredWildcard: 
    "\<lbrakk> red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (Some v_args);
       W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) None;
       th_result_rel True (W' \<noteq> {}) W' res \<rbrakk> \<Longrightarrow>
       red_inhale Pr \<Delta> R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res"
| InhPureNormalMagic: 
    "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
      red_inhale Pr \<Delta> R (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"
| InhSubFailure: 
    "\<lbrakk> e \<in> sub_expressions_atomic A; Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> 
      red_inhale Pr \<Delta> R (Atomic A) \<omega> RFailure"

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
    Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True)); 
    red_inhale Pr \<Delta> R A \<omega> res \<rbrakk> \<Longrightarrow>
    red_inhale Pr \<Delta> R (Imp e A) \<omega> res"
| InhImpFalse:
 "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow> 
    red_inhale Pr \<Delta> R (Imp e A) \<omega> (RNormal \<omega>)"
| InhImpFailure:
 "\<lbrakk> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>
   red_inhale Pr \<Delta> R (Imp e A) \<omega> RFailure"

\<comment>\<open>Pure expression evaluation\<close>

\<comment>\<open>List of expressions\<close>
| RedExpList: 
  "\<lbrakk> list_all2 (\<lambda>e v. red_pure_exp_total Pr \<Delta> LH e \<omega> (Val v)) es vs \<rbrakk> \<Longrightarrow>
     red_pure_exps_total Pr \<Delta> LH es \<omega> (Some vs)"
| RedExpListFailure: 
  "\<lbrakk> e \<in> set(es); red_pure_exp_total Pr \<Delta> LH e \<omega> VFailure \<rbrakk> \<Longrightarrow>
     red_pure_exps_total Pr \<Delta> LH es \<omega> None"

\<comment>\<open>Atomic expressions\<close>
| RedLit: "Pr, \<Delta>, LH \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l)"
| RedVar: "\<lbrakk> \<sigma> n = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Var n; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"
| RedResult: "\<lbrakk> \<sigma> 0 = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Result; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"

\<comment>\<open>Binop and Unop\<close>
| RedBinopLazy: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinop: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta>, LH \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop_lazy v1 bop = None; eval_binop v1 bop v2 = BinopNormal v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinopRightFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1; Pr, \<Delta>, LH \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure;  eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopOpFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta>, LH \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop v1 bop v2 = BinopOpFailure ; eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* Division by 0 *)
| RedBinopLeftFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

| RedUnop: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v; eval_unop unop v = BinopNormal v' \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
| RedUnopFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Cond\<close>
| RedCondExpTrue: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) ; Pr, \<Delta>, LH \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFalse: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) ; Pr, \<Delta>, LH \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Old\<close>
| RedOld: "\<lbrakk> t l = Some \<phi> ; Pr, \<Delta>, LH \<turnstile> \<langle>e; (\<sigma>, t, \<phi>)\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Old l e; (\<sigma>, t, _)\<rangle> [\<Down>]\<^sub>t v"
| RedOldFailure: "\<lbrakk> t l = None \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Old l e ; (_, t, _)\<rangle> [\<Down>]\<^sub>t VFailure" 

\<comment>\<open>Heap lookup (TODO: null case?)\<close>
| RedField: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) ; get_hh_total_full \<omega> (a, f) = v \<rbrakk> \<Longrightarrow> 
       Pr, \<Delta>, LH \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t (if (a,f) \<in> LH then Val v else VFailure)"
| RedFieldFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)

\<comment>\<open>Permission introspection\<close>
| RedPermNull: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
| RedPerm: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_prat (get_mh_total_full \<omega> (a, f))))"
| RedPermFailure: "\<lbrakk> Pr, \<Delta>, LH \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow> Pr, \<Delta>, LH \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* could be replaced *)
(*
\<comment>\<open>Unfolding\<close>
| RedUnfolding: "\<lbrakk> 
         Pr, \<Delta>, LH \<turnstile> \<langle>e_arg; \<omega>\<rangle> [\<Down>]\<^sub>t v_arg;
        ViperLang.predicates Pr p = Some pred;
        ViperLang.predicate_decl.body pred = Some pred_body;
        red_inhale Pr \<Delta> False pred_body \<omega> (RNormal \<omega>');
            
 \<rbrakk> \<Longrightarrow>
     Pr, \<Delta>, LH \<turnstile> \<langle>Unfolding p [e_arg] p_body; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
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


section \<open>Simplified induction principles\<close>
lemma conj2conj2: "A \<and> B \<and> C \<Longrightarrow> C"
  apply (rule conjunct2)
  apply (erule conjunct2)
  done

lemmas red_inhale_induct_aux = mp[OF conj2conj2[OF red_pure_exp_total_red_pure_exps_total_red_inhale.induct[where ?P1.0 = "\<lambda> a b c d. True" and ?P2.0 = "\<lambda> a b c d. True"]]]

lemma red_inhale_induct [consumes 1, case_names InhAcc InhAccPred InhAccWildcard InhAccPredWildcard 
InhPureNormalMagic InhSubFailure InhSepNormal InhSepFailureMagic InhImpTrue InhImpFalse InhImpFailure]:
  assumes "red_inhale Pr \<Delta> R A \<omega> res" and
    "(\<And>\<omega> e_r r e_p p W' R f res.
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<Longrightarrow>
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<Longrightarrow>
            W' = inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_prat p)) \<Longrightarrow>
            th_result_rel (0 \<le> p) (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<Longrightarrow> P R (Atomic (Acc e_r f (PureExp e_p))) \<omega> res)" and
    "(\<And>\<omega> e_p p e_args v_args W' R pred_id res.
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<Longrightarrow>
            red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (Some v_args) \<Longrightarrow>
            W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) (Some (Abs_prat p)) \<Longrightarrow>
            th_result_rel (0 \<le> p) (W' \<noteq> {}) W' res \<Longrightarrow> P R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res)" and
    "(\<And>\<omega> e_r r W' R f res.
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r) \<Longrightarrow>
            W' = inhale_perm_single R \<omega> (the_address r, f) None \<Longrightarrow>
            th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res \<Longrightarrow> P R (Atomic (Acc e_r f Wildcard)) \<omega> res)" and
    "(\<And>\<omega> e_args v_args W' R pred_id res.
            red_pure_exps_total Pr \<Delta> (get_valid_locs \<omega>) e_args \<omega> (Some v_args) \<Longrightarrow>
            W' = inhale_perm_single_pred R \<omega> (pred_id, v_args) None \<Longrightarrow>
            th_result_rel True (W' \<noteq> {}) W' res \<Longrightarrow> P R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res)"
    "(\<And>\<omega> e b R.
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<Longrightarrow>
            P R (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic))" and
    "(\<And>e A \<omega> R.
            e \<in> sub_expressions_atomic A \<Longrightarrow> Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> True \<Longrightarrow> P R (Atomic A) \<omega> RFailure)" and
    "(\<And>R A \<omega> \<omega>'' B res.
            red_inhale Pr \<Delta> R A \<omega> (RNormal \<omega>'') \<Longrightarrow>
            P R A \<omega> (RNormal \<omega>'') \<Longrightarrow> red_inhale Pr \<Delta> R B \<omega>'' res \<Longrightarrow> P R B \<omega>'' res \<Longrightarrow> P R (A && B) \<omega> res)" and
    "(\<And>R A \<omega> resA B. red_inhale Pr \<Delta> R A \<omega> resA \<Longrightarrow> P R A \<omega> resA \<Longrightarrow> resA = RFailure \<or> resA = RMagic \<Longrightarrow> P R (A && B) \<omega> resA)" and
    "(\<And>\<omega> e R A res.
            Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<Longrightarrow>
            red_inhale Pr \<Delta> R A \<omega> res \<Longrightarrow> P R A \<omega> res \<Longrightarrow> P R (Imp e A) \<omega> res)" and
    "(\<And>\<omega> e R A. Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<Longrightarrow> P R (Imp e A) \<omega> (RNormal \<omega>))" and
    "(\<And>\<omega> e R A. Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P R (Imp e A) \<omega> RFailure)" and
    "(\<And>\<omega> e R A. Pr, \<Delta>, get_valid_locs \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<Longrightarrow> P R (Imp e A) \<omega> RFailure)"
 shows "P R A \<omega> res"
  apply (rule red_inhale_induct_aux[where ?P3.0=P])
  by (tactic \<open>resolve_tac @{context} @{thms assms} 1\<close>, assumption+)+ (auto intro: assms(1))

section \<open>Total heap consistency\<close>

inductive unfold_rel :: "program \<Rightarrow> 'a interp \<Rightarrow> predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> prat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where 
   UnfoldRelStep: 
    "\<lbrakk> ViperLang.predicates Pr pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     m = get_mp_total_full \<omega>;
     pgte (m (pred_id,vs)) q;
     q \<noteq> pnone;
     m' = m( (pred_id,vs) := psub (m (pred_id, vs)) q);
     \<omega>2 = (nth_option vs, get_trace_total \<omega>, update_mp_total (get_total_full \<omega>) m');
     red_inhale Pr \<Delta> (\<lambda>_. True) (syntactic_mult (Rep_prat q) pred_body) \<omega>2 (RNormal \<omega>') \<rbrakk> \<Longrightarrow> 
     unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>'"

definition unfold_rel_general :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "unfold_rel_general Pr \<Delta> \<omega> \<omega>' \<equiv> \<exists> pred_id vs q. unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>'"

definition unfold_rel_multi :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where "unfold_rel_multi Pr \<Delta>  \<equiv> rtranclp (unfold_rel_general Pr \<Delta>)"

text \<open>Expression evaluation as a function. Using this function makes sense, when it is known that 
e is well-defined and is deterministic (for example, if e is the body of a predicate). \<^term>\<open>UNIV\<close>
is used to indicate that every heap location can be read (effectively omitting heap checks)\<close>

fun red_pure_exp_total_fun :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a val"
  where "red_pure_exp_total_fun Pr \<Delta> e \<omega> = (SOME v. Pr, \<Delta>, UNIV \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v)"

fun red_pure_exps_total_fun :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp list \<Rightarrow> 'a full_total_state \<Rightarrow> ('a val) list"
  where "red_pure_exps_total_fun Pr \<Delta> es \<omega> = (SOME vs. red_pure_exps_total Pr \<Delta> UNIV es \<omega> (Some vs))"

(* TODO: duplicate? *)
fun extract_address_from_val :: "'a val \<Rightarrow> address"
  where 
    "extract_address_from_val (VRef (Address a)) = a"
  | "extract_address_from_val _ = undefined"

(* TODO: duplicate? *)
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
                fst (get_hp_total_full \<omega> (pred_id, red_pure_exps_total_fun Pr \<Delta> e_args \<omega>))
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
                snd (get_hp_total_full \<omega> (pred_id, red_pure_exps_total_fun Pr \<Delta> e_args \<omega>))
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
         (pgt (get_mp_total_full \<omega>' (pred_id,vs)) pnone \<and> ViperLang.predicates Pr pred_id = Some pred_decl) \<longrightarrow>
          option_fold (\<lambda> pred_body. get_hp_total_full \<omega> (pred_id, vs) = 
                        (assertion_heap_snapshot Pr \<Delta> pred_body \<omega>, assertion_predicate_snapshot Pr \<Delta> pred_body \<omega>) )
                      True
                      (ViperLang.predicate_decl.body pred_decl)"

coinductive total_heap_consistent :: "program \<Rightarrow> 'a interp \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where 
  UnfoldStep: "\<lbrakk> \<And> pred_id vs q.                      
                     option_fold (\<lambda>decl. ViperLang.predicate_decl.body decl) None (ViperLang.predicates Pr pred_id) \<noteq> None \<Longrightarrow>
                     pgte (get_mp_total_full \<omega> (pred_id,vs)) q \<and> q \<noteq> pnone  \<Longrightarrow>
                     \<exists>\<omega>'. unfold_rel Pr \<Delta> pred_id vs q \<omega> \<omega>' \<and> total_heap_consistent Pr \<Delta> \<omega>';
                 pheap_consistent Pr \<Delta> \<omega> \<rbrakk> \<Longrightarrow>
                 total_heap_consistent Pr \<Delta> \<omega>"


abbreviation red_inhale_th_cons :: "program \<Rightarrow> 'a interp \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a standard_result \<Rightarrow> bool"
  where "red_inhale_th_cons Pr \<Delta> A \<omega> res \<equiv> red_inhale Pr \<Delta> (total_heap_consistent Pr \<Delta>) A \<omega> res"

text \<open>\<^const>\<open>red_inhale_th_cons\<close> only takes transitions to total heap consistent states whenever some 
permission is inhaled\<close>

end