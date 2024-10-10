theory MainResults
imports SimpleViperFrontEnd.SyntacticTranslation ViperAbstractRefinesTotal.AbstractRefinesTotal
begin

section \<open>Theorem VCG back-end to ViperCore operational semantics\<close>

fun scoped_var_list :: "vtyp list \<Rightarrow> stmt \<Rightarrow> stmt"
  where 
    "scoped_var_list [] C = C"
  | "scoped_var_list (t # ts) C = (stmt.Scope t (scoped_var_list ts C))"

term shift_and_add_state_total
term shift_and_add_list_state

fun shift_and_add_list_total :: "'a full_total_state \<Rightarrow> ('a val) list \<Rightarrow> 'a full_total_state"
  where 
    "shift_and_add_list_total \<omega> vs = update_store_total \<omega> (shift_and_add_list (get_store_total \<omega>) vs)"

lemma red_stmt_total_scoped_var_list:
  assumes "\<not> (red_stmt_total ctxt R \<Lambda> (scoped_var_list ts C) \<omega> RFailure)"
      and "ts = map (get_type (absval_interp_total ctxt)) (rev vs)"
    shows "\<not> (red_stmt_total ctxt R (shift_and_add_list \<Lambda> ts) C (shift_and_add_list_total \<omega> vs) RFailure)" 
  using assms
  sorry
(*
proof (induction ts)
  case Nil
  then show ?case     
    by simp
next
  case (Cons t ts)  
  show ?case
  proof (rule notI)
    assume "red_stmt_total ctxt R Map.empty (scoped_var_list (t # ts) C) \<omega> RFailure"
    hence "red_stmt_total ctxt R Map.empty (Scope t (scoped_var_list ts C)) \<omega> RFailure"
      by simp
    hence "red_stmt_total ctxt R (shift_and_add Map.empty t) (scoped_var_list ts C) (shift_and_add_state_total \<omega> v) res"    
qed
*)


definition triple_as_method_decl :: "vtyp list \<Rightarrow> ViperLang.assertion \<Rightarrow> stmt \<Rightarrow> ViperLang.assertion \<Rightarrow> method_decl"
  where "triple_as_method_decl ts P C Q \<equiv> \<lparr> method_decl.args = [], 
                                         rets = [], 
                                         pre = Atomic (Pure (ELit (LBool True))), 
                                         post = Atomic (Pure (ELit (LBool True))), 
                                         body = Some (scoped_var_list ts ((stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))))\<rparr>"

definition vpr_program_from_method_decl :: "method_decl \<Rightarrow> program"
  where "vpr_program_from_method_decl m = 
           \<lparr> methods = [''m'' \<mapsto> m], predicates = Map.empty, funs = Map.empty, declared_fields = [field_val \<mapsto> TInt], domains = 0 \<rparr>"

definition default_ctxt :: "('a \<Rightarrow> abs_type) \<Rightarrow> method_decl \<Rightarrow> 'a total_context"
  where "default_ctxt d m = \<lparr> program_total = vpr_program_from_method_decl m, fun_interp_total = Map.empty, absval_interp_total = d \<rparr>"

definition is_initial_vcg_state
  where "is_initial_vcg_state ctxt \<Lambda> \<omega> \<equiv> 
             total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>) \<and>
             is_empty_total_full \<omega> \<and>
             (\<forall>x v. get_store_total \<omega> x = Some v \<longrightarrow> \<Lambda> x = Some (get_type (absval_interp_total ctxt) v))"

lemma convert_vpr_method_correct_total:
  assumes MethodCorrect: "vpr_method_correct_total (ctxt :: 'a total_context) R (triple_as_method_decl ts P C Q)"
      and "\<Lambda> = nth_option ts"
    shows "red_stmt_total_set_ok ctxt R \<Lambda> ((stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))) {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
  unfolding (*vpr_method_correct_total_def vpr_method_correct_total_aux_def triple_as_method_decl_def
            vpr_method_body_correct_def*)
            red_stmt_total_set_ok_def \<open>\<Lambda> = _\<close>
(*proof (rule allI, rule impI, rule notI, simp)
  fix \<omega> :: "'a full_total_state"
  assume "is_initial_vcg_state ctxt (nth_option ts) \<omega>"*)
  sorry

definition aemp where
  "aemp = inhalify (Set.filter pure UNIV)"

(*
declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]
*)

definition initial_vcg_states_equi where 
      "initial_vcg_states_equi \<equiv> {\<omega> :: int equi_state. stable \<omega> \<and> typed tcfe \<omega> \<and> get_trace \<omega> = Map.empty 
                                   \<and> (\<forall>l. get_m \<omega> l = 0)}"

theorem VCG_to_verifies_set :                             
  assumes "vpr_method_correct_total ctxt (\<lambda>_ :: int full_total_state. True) (triple_as_method_decl ts P C Q)"
      and "stmt_typing (program_total ctxt) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
      and "valid_a2t_stmt C"
    shows "ConcreteSemantics.verifies_set (t2a_ctxt ctxt \<Lambda>) initial_vcg_states_equi
            (compile False (ctxt_to_interp ctxt) (\<Lambda>, declared_fields (program_total ctxt)) 
               (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)))"
  sorry

(*  \<and> (\<forall>auxRes \<in> snd Res. valid_a2t_stmt auxRes) *)

lemma valid_a2t_exp_translate_exp: "valid_a2t_exp (translate_exp e)"
  by (induction e) auto

lemma valid_a2t_stmt_translate_syn:
  assumes "res = translate_syn \<Delta> t C"
  shows "valid_a2t_stmt (fst res)"
  using assms
  (*apply (induction C)
           apply (simp_all add: valid_a2t_exp_translate_exp 
                                syntactic_translate_heap_loc_def
                                syntactic_translate_addr_def)*)
  oops 

theorem sound_syntactic_translation_VCG:
  assumes "wf_stmt \<Delta> tcfes C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_assertion tcfe P \<and> TypedEqui.wf_assertion tcfe Q"
      and "typed_stmt C" (* TODO: Unify the two notions of typing *)

      and "mdecl = (triple_as_method_decl ts Ps (fst (translate_syn \<Delta> tcfes C)) Qs)"
      and MethodCorrect: "vpr_method_correct_total (default_ctxt (domains \<Delta>) mdecl) (\<lambda>_ :: int full_total_state. True) mdecl"     
      and AuxiliaryMethodsCorrect:
        "\<And> stmtAux. stmtAux \<in> snd (translate_syn \<Delta> tcfes C) \<Longrightarrow> 
             let mdeclAux = triple_as_method_decl ts 
                              (Atomic (Pure (ELit (LBool True)))) 
                              (fst (translate_syn \<Delta> tcfes C)) 
                              (Atomic (Pure (ELit (LBool True)))) 
             in
             vpr_method_correct_total (default_ctxt (domains \<Delta>) mdeclAux) (\<lambda>_ :: int full_total_state. True) mdeclAux"
 
      and ViperTyped: 
            "stmt_typing (program_total (default_ctxt (domains \<Delta>) mdecl)) (nth_option ts)
                   (stmt.Seq (stmt.Seq (stmt.Inhale Ps) (fst (translate_syn \<Delta> tcfes C))) (stmt.Exhale Qs))"
      and "nth_option (map (set_from_type undefined) ts) = abs_type_context.variables tcfe"
      and "P = make_semantic_assertion_gen False \<Delta> tcfes Ps"
      and "Q = make_semantic_assertion_gen False \<Delta> tcfes Qs"
       (* TODO snd element verifies *)
    shows "tcfe \<turnstile>CSL [P \<otimes> UNIV] C [Q \<otimes> UNIV]"
proof (rule sound_syntactic_translation[OF assms(1-6)], simp)
  let ?Ctr_main = "(fst (translate_syn \<Delta> tcfes C))"
  let ?ctxt = "(default_ctxt (domains \<Delta>) mdecl) :: int total_context"
  let ?\<Lambda> = "nth_option ts"
  let ?Ctr_mainV = "(stmt.Seq (stmt.Seq (stmt.Inhale Ps) ?Ctr_main) (stmt.Exhale Qs))"

  show "ConcreteSemantics.verifies_set tcfe atrue (abs_stmt.Inhale P ;; compile False \<Delta> tcfes ?Ctr_main ;; abs_stmt.Exhale Q)"
  proof -
   
    have "red_stmt_total_set_ok ?ctxt (\<lambda>_ :: int full_total_state. True) (nth_option ts) 
                ?Ctr_mainV 
                {\<omega>. is_initial_vcg_state ?ctxt (nth_option ts) \<omega>}"
      apply (rule convert_vpr_method_correct_total)
      using MethodCorrect \<open>mdecl = _\<close>
       apply blast
      by simp

    have "tcfe = t2a_ctxt ?ctxt (nth_option ts)"
      sorry   

    have "tcfes = (nth_option ts, declared_fields (program_total (default_ctxt (domains \<Delta>) mdecl)))"
      sorry

    have "\<Delta> = (ctxt_to_interp ?ctxt)"
      sorry
    thm abstract_refines_total_verifies_set



    typ "int equi_state"

    have A1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) initial_vcg_states_equi
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) ?Ctr_mainV)"
      apply (rule VCG_to_verifies_set)
      using MethodCorrect
      unfolding \<open>mdecl = _\<close>
        apply blast
      using ViperTyped
      unfolding \<open>mdecl = _\<close>
       apply blast
      sorry
      
    have "ConcreteSemantics.verifies_set tcfe initial_vcg_states_equi (compile False \<Delta> tcfes ?Ctr_mainV)"
    proof -
      have "tcfe = t2a_ctxt ?ctxt (nth_option ts)"
        sorry   
  
      moreover have "tcfes = (nth_option ts, declared_fields (program_total (default_ctxt (domains \<Delta>) mdecl)))"
        sorry
  
      moreover have "\<Delta> = (ctxt_to_interp ?ctxt)"
        sorry
      ultimately show ?thesis
         using A1
         by metis
    qed

    hence "ConcreteSemantics.verifies_set tcfe initial_vcg_states_equi
              (abs_stmt.Inhale P ;; compile False \<Delta> tcfes ?Ctr_main ;; abs_stmt.Exhale Q)"
      using \<open>P = _\<close> \<open>Q = _\<close>
      by simp

    thus ?thesis
      sorry \<comment>\<open>Thibault: TODO\<close>     
  qed

  fix Cv
  assume "Cv \<in> compile False \<Delta> tcfes ` snd (translate_syn \<Delta> tcfes C)"
  show "ConcreteSemantics.verifies_set tcfe atrue Cv"
    sorry
qed

end