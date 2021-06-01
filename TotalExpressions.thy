theory TotalExpressions
imports Viper.ViperLang Viper.ValueAndBasicState TotalViperState Viper.Binop
begin

(* duplicated: TODO share it *)
fun the_address :: "'a val \<Rightarrow> address" where
  "the_address (VRef (Address a)) = a"
| "the_address _ = undefined"

fun the_rat :: "'a val \<Rightarrow> rat" where
  "the_rat (VPerm r) = r"
| "the_rat _ = undefined"

(* not sure about this notation *)
fun red_pure_exp_total :: "program \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> 'a val"
  ("_ \<turnstile> ((\<langle>_;_\<rangle>) [\<Down>]\<^sub>t)" [51,0,0] 81)
  where 
  "Pr \<turnstile> \<langle>ELit l; _\<rangle> [\<Down>]\<^sub>t = (val_of_lit l)"
| "Pr \<turnstile> \<langle>Var n; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t = the (\<sigma> n)"
| "Pr \<turnstile> \<langle>Unop unop e; \<omega>\<rangle> [\<Down>]\<^sub>t = the (eval_unop unop (Pr \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t))"
| "Pr \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t = (let v1 = (Pr \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t) in let r = eval_binop_lazy v1 bop in
  if r \<noteq> None then the r else the (eval_binop v1 bop (Pr \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t)))"
| "Pr \<turnstile> \<langle>CondExp e1 e2 e3; \<omega>\<rangle> [\<Down>]\<^sub>t = (if (Pr \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool True) then (Pr \<turnstile> \<langle>e2; \<omega>\<rangle> [\<Down>]\<^sub>t) else (Pr \<turnstile> \<langle>e3; \<omega>\<rangle> [\<Down>]\<^sub>t))"
(* difference to virtual state: heap lookup *)
| "Pr \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t = get_heap_total_full \<omega> (the_address (Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t), f)"
| "Pr \<turnstile> \<langle>Old l e; (\<sigma>, \<tau>, \<phi>)\<rangle> [\<Down>]\<^sub>t = (Pr \<turnstile> \<langle>e; (\<sigma>, \<tau>, (the (\<tau> l)))\<rangle> [\<Down>]\<^sub>t)"
| "Pr \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t = VPerm (Rep_prat (get_mask_total_full \<omega> ((the_address (Pr \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t)), f)))"

(*| "Pr \<turnstile> \<langle>PermPred p exps; \<omega>\<rangle> [\<Down>]\<^sub>t = VPerm (get_pm \<omega> (p, List.map (\<lambda>e. conf, Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t) exps))" *)

(*
| "conf, Pr, \<Delta> \<turnstile> \<langle>FunApp f exps; \<omega>\<rangle> [\<Down>]\<^sub>t = the (the (funs \<Delta> f) (List.map (\<lambda>e. conf, Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t) exps) (get_v \<omega>))"
| "conf, Pr, \<Delta> \<turnstile> \<langle>Result; (\<sigma>, _, _)\<rangle> [\<Down>]\<^sub>t = the (\<sigma> 0)"

| "conf, Pr, \<Delta> \<turnstile> \<langle>Unfolding p exps f e; \<omega>\<rangle> [\<Down>]\<^sub>t = (if equi_predicate conf then (conf, Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t)
  else (conf, Pr, \<Delta> \<turnstile> \<langle>e; (SOME \<omega>'. \<omega>' \<in> unfold_states conf Pr \<Delta> p (List.map (\<lambda>e. conf, Pr, \<Delta> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t) exps) (the_rat (conf, Pr, \<Delta> \<turnstile> \<langle>f; \<omega>\<rangle> [\<Down>]\<^sub>t)) \<omega>)\<rangle> [\<Down>]\<^sub>t))"

| "conf, Pr, \<Delta> \<turnstile> \<langle>Let e1 e2; \<omega>\<rangle> [\<Down>]\<^sub>t = (conf, Pr, \<Delta> \<turnstile> \<langle>e2; shift_and_add_state \<omega> (conf, Pr, \<Delta> \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t)\<rangle> [\<Down>]\<^sub>t)"

| "conf, Pr, \<Delta> \<turnstile> \<langle>PExists ty e; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool (\<exists>v \<in> set_from_type \<Delta> ty. (conf, Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t = VBool True))"
| "conf, Pr, \<Delta> \<turnstile> \<langle>PForall ty e; \<omega>\<rangle> [\<Down>]\<^sub>t = VBool (\<forall>v \<in> set_from_type \<Delta> ty. (conf, Pr, \<Delta> \<turnstile> \<langle>e; shift_and_add_state \<omega> v\<rangle> [\<Down>]\<^sub>t = VBool True))"
*)

datatype inh_exh_conf = CInhale | CExhale "heap_loc set"


fun (sequential) wd_pure_exp_total :: "program \<Rightarrow> inh_exh_conf \<Rightarrow> pure_exp \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
(* TODO *)
  "wd_pure_exp_total Pr c (ELit l) \<omega> \<longleftrightarrow> True"
| "wd_pure_exp_total Pr c (Var n) \<omega> \<longleftrightarrow> True"

| "wd_pure_exp_total Pr c (Unop unop e) \<omega> \<longleftrightarrow> (wd_pure_exp_total Pr c e \<omega>)"
| "wd_pure_exp_total Pr c (Binop e1 bop e2) \<omega> \<longleftrightarrow> 
     (wd_pure_exp_total Pr c e1 \<omega> \<and> (let v1 = (Pr \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t)
          in eval_binop_lazy v1 bop = None \<longrightarrow> (wd_pure_exp_total Pr c e2 \<omega>)))"
| "wd_pure_exp_total Pr c (CondExp e1 e2 e3) \<omega> \<longleftrightarrow> 
     wd_pure_exp_total Pr c e1 \<omega> \<and> (if (un_VBool (Pr \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t)) then wd_pure_exp_total Pr c e2 \<omega> else wd_pure_exp_total Pr c e3 \<omega>)" 
| "wd_pure_exp_total Pr CInhale (FieldAcc e f) \<omega> \<longleftrightarrow> 
    (let l = the_address (Pr \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t) in (pgt (get_mask_total_full \<omega> (l,f)) pnone))"
| "wd_pure_exp_total Pr (CExhale locs) (FieldAcc e f) \<omega> \<longleftrightarrow> 
    (let l = the_address (Pr \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t) in (l,f) \<in> locs)"
(*
| "wd_pure_exp_total conf Pr \<Delta> (CondExp e1 e2 e3) \<omega> \<longleftrightarrow> wd_pure_exp_total conf Pr \<Delta> e1 \<and> (if  "
| "wd_pure_exp_total conf Pr \<Delta> (FieldAcc e f) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Old l e) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Perm e f) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (PermPred p exps) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (FunApp f exps) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> Result \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Unfolding p exps f e) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (Let e1 e2) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (PExists ty e) \<omega> \<longleftrightarrow> False"
| "wd_pure_exp_total conf Pr \<Delta> (PForall ty e) \<omega> \<longleftrightarrow> False" *)

end