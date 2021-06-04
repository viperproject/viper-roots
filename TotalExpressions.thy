theory TotalExpressions
imports Viper.ViperLang Viper.ValueAndBasicState TotalViperState Viper.Binop Viper.DeBruijn
begin

(* duplicated: TODO share it *)
fun the_address :: "'a val \<Rightarrow> address" where
  "the_address (VRef (Address a)) = a"
| "the_address _ = undefined"

fun the_rat :: "'a val \<Rightarrow> rat" where
  "the_rat (VPerm r) = r"
| "the_rat _ = undefined"

inductive red_pure_exp_total :: "program \<Rightarrow> 'a interp \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a extended_val \<Rightarrow> bool"
  ("_, _ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t _)" [51,51,0,51,51] 81)
  where
(* Independent of SA *)
  RedLit: "Pr, \<Delta> \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t Val (val_of_lit l)"
| RedVar: "\<lbrakk> \<sigma> n = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Var n; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"
| RedUnop: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v ; eval_unop unop v = Some v' \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'"
| RedBinopLazy: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; eval_binop_lazy v1 bop = Some v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedBinop: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop_lazy v1 bop = None; eval_binop v1 bop v2 = Some v \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
(*| RedOld: "\<lbrakk> t l = Some \<phi> ; Pr, \<Delta> \<turnstile> \<langle>e; (\<sigma>, t, \<phi>)\<rangle> [\<Down>]\<^sub>t v \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Old l e; (\<sigma>, t, _)\<rangle> [\<Down>]\<^sub>t v"*) (* Implicitly propagates failures *)
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
| RedCondExpTrue: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) ; Pr, \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedCondExpFalse: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) ; Pr, \<Delta> \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t r \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t r"
| RedPermNull: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef Null) \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
| RedResult: "\<lbrakk> \<sigma> 0 = Some v \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Result; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t Val v"
(*| RedUnfoldingPermNegFailure: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v) ; v < 0 \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Unfolding p exps f e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"*)

| RedBinopRightFailure: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure ;  eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedBinopFailure: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1 ; Pr, \<Delta> \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2 ; eval_binop v1 bop v2 = None ; eval_binop_lazy v1 bop = None \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" (* Division by 0 *)
| RedOldFailure: "\<lbrakk> t l = None \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Old l e ; (_, t, _)\<rangle> [\<Down>]\<^sub>t VFailure"
(*
| RedExistsFailure: "\<lbrakk> v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
| RedForallFailure: "\<lbrakk> v \<in> set_from_type \<Delta> ty \<longrightarrow> Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"*)
| RedPropagateFailure: "\<lbrakk> e \<in> sub_pure_exp e' ; Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure \<rbrakk> \<Longrightarrow>  Pr, \<Delta> \<turnstile> \<langle>e'; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"

(* Dependent on the SA *)
| RedField: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) ; get_heap_total_full \<phi> (a, f) = v \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
| RedPerm: "\<lbrakk> Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a)) \<rbrakk> \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_prat (get_mask_total_full \<omega> (a, f))))"
(*
(* perm(P(...)) = 0 if equirecursive *)
| RedPermPred: "\<lbrakk> list_all2 (\<lambda>e v. Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>] Val v) exps vals \<rbrakk>
  \<Longrightarrow> Pr, \<Delta> \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>] Val (VPerm (Rep_prat (get_pm \<omega> (p, vals))))"
*)

datatype inh_exh_conf = CInhale | CExhale "heap_loc set"

fun wd_binop :: "binop \<Rightarrow> 'a val \<Rightarrow> 'a val \<Rightarrow> bool"
  where 
    "wd_binop Div v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop Mod v1 v2 \<longleftrightarrow> v2 \<noteq> (VInt 0)"
  | "wd_binop _ _ _ = True"

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
    (\<forall>l. ( (Pr,\<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address l))) \<longrightarrow> (l,f) \<in> locs))"
| "wd_pure_exp_total Pr \<Delta> c (Perm e f) \<omega> \<longleftrightarrow> wd_pure_exp_total Pr \<Delta> c e \<omega> \<and> (\<forall>r. (Pr, \<Delta> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)) \<longrightarrow> r \<noteq> Null)"
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

end