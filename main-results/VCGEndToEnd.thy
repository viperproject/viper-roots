theory VCGEndToEnd
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
  oops
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
                                         rets = ts, 
                                         pre = Atomic (Pure (ELit (LBool True))), 
                                         post = Atomic (Pure (ELit (LBool True))), 
                                         body = Some (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))\<rparr>"


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

(*
declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]
*)

definition initial_vcg_states_equi where 
      "initial_vcg_states_equi \<Delta> \<equiv> {\<omega> :: int equi_state. stable \<omega> \<and> 
                                    typed \<Delta> \<omega> \<and> 
                                    get_trace \<omega> = Map.empty \<and> (\<forall>l. get_m \<omega> l = 0)
                                  }"

corollary VCG_to_verifies_set :                             
  assumes MethodCorrect: "vpr_method_correct_total ctxt (\<lambda>_ :: int full_total_state. True) (triple_as_method_decl ts P C Q)"
      and "\<Lambda> = nth_option ts"
      and Typed: "stmt_typing (program_total ctxt) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
      and "valid_a2t_stmt C"
      and AbsTypeWf: "abs_type_wf (absval_interp_total ctxt)"
    shows "ConcreteSemantics.verifies_set (t2a_ctxt ctxt \<Lambda>) (initial_vcg_states_equi (t2a_ctxt ctxt \<Lambda>))
            (compile False (ctxt_to_interp ctxt) (\<Lambda>, declared_fields (program_total ctxt)) 
               (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)))"  
proof (rule abstract_refines_total_verifies_set[OF _ Typed])
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>"
  hence "stable \<omega>" and "typed (t2a_ctxt ctxt \<Lambda>) \<omega>" and "get_trace \<omega> = Map.empty" and 
        EmptyMask: "\<forall>l. get_m \<omega> l = 0"
    unfolding initial_vcg_states_equi_def
    by auto

  from MethodCorrect \<open>\<Lambda> = _\<close>
  have "red_stmt_total_set_ok ctxt (\<lambda>_. True) \<Lambda> 
          ((stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))) {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
    using convert_vpr_method_correct_total
    by blast

  moreover have "a2t_states ctxt \<omega> \<subseteq> {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"
  proof 
    fix \<omega>t
    assume "\<omega>t \<in> a2t_states ctxt \<omega>"

    show "\<omega>t \<in> {\<omega>. is_initial_vcg_state ctxt \<Lambda> \<omega>}"      
    proof 
      show "is_initial_vcg_state ctxt \<Lambda> \<omega>t"
        unfolding is_initial_vcg_state_def
      proof (intro conjI)
        from \<open>typed ?\<Delta> \<omega>\<close> have StoreTyped: "store_typed (variables ?\<Delta>) (get_store \<omega>)"
          unfolding TypedEqui.typed_def well_typed_def

        show "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>t)"
          sorry
      next
        show "is_empty_total_full \<omega>t"          
          unfolding is_empty_total_full_def is_empty_total_def zero_mask_def
          apply (rule conjI)
          using EmptyMask \<open>\<omega>t \<in>  _\<close> 
           apply fastforce
          using \<open>\<omega>t \<in>  _\<close> 
          sorry \<comment>\<open>Predicate Mask must be empty, ask Michael\<close>                    
      next
        from \<open>typed ?\<Delta> \<omega>\<close> have StoreTyped: "store_typed (variables ?\<Delta>) (get_store \<omega>)"
          unfolding TypedEqui.typed_def TypedEqui.typed_store_def
          by blast

        show "\<forall>x v. get_store_total \<omega>t x = Some v \<longrightarrow> \<Lambda> x = Some (get_type (absval_interp_total ctxt) v)"
        proof (rule allI | rule impI)+
          fix x v
          assume "get_store_total \<omega>t x = Some v"
          hence "get_store \<omega> x = Some v"
            using \<open>\<omega>t \<in> _\<close>
            by simp
          moreover from this obtain t where "\<Lambda> x = Some t"
            using StoreTyped[simplified store_typed_def]
            unfolding t2a_ctxt_def sem_store_def
            by fastforce
          ultimately show "\<Lambda> x = Some (get_type (absval_interp_total ctxt) v)"
            using StoreTyped[simplified store_typed_def]
            unfolding t2a_ctxt_def
            apply simp
            by (metis sem_vtyp_to_get_type)
        qed
      qed
    qed
  qed

  ultimately show
    "red_stmt_total_set_ok ctxt (\<lambda>_. True) \<Lambda> (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q)) (a2t_states ctxt \<omega>)"  
    using red_stmt_total_set_ok_mono 
    by blast
next 
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>" 
     and TypedState: "typed (t2a_ctxt ctxt \<Lambda>) \<omega>"

  show "abs_state_typing ctxt \<Lambda> \<omega>"
    unfolding abs_state_typing_def
  proof (intro conjI)
    from TypedState have "store_typed (variables (t2a_ctxt ctxt \<Lambda>)) (get_store \<omega>)"
      unfolding TypedEqui.typed_def TypedEqui.typed_store_def
      by blast

    thus "store_typing ctxt \<Lambda> (get_store \<omega>)"
      by (simp add: store_typing_def t2a_ctxt_def)
  next
    from TypedState have HeapTyped: "well_typed_heap (custom_context (t2a_ctxt ctxt \<Lambda>)) (snd (get_abs_state \<omega>))"
      unfolding TypedEqui.typed_def well_typed_def
      by blast
    thus "well_typed_heap (sem_fields (absval_interp_total ctxt) (declared_fields (program_total ctxt))) (get_state \<omega>)"
      by (simp add: snd_get_abs_state t2a_ctxt_def)
  next
    show "partial_trace_typing ctxt (get_trace \<omega>)"
      using \<open>\<omega> \<in> _\<close>
      by (simp add: partial_trace_typing_def initial_vcg_states_equi_def)
  qed
next
  let ?\<Delta> = "(t2a_ctxt ctxt \<Lambda>)"

  fix \<omega>
  assume "\<omega> \<in> initial_vcg_states_equi ?\<Delta>"

  thus "a2t_state_wf ctxt (get_trace \<omega>)"
    unfolding a2t_state_wf_def initial_vcg_states_equi_def
    by (simp add: AbsTypeWf)
next
  show "valid_a2t_stmt (stmt.Seq (stmt.Seq (stmt.Inhale P) C) (stmt.Exhale Q))"
    sorry
qed    

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

abbreviation true_syn_assertion 
  where "true_syn_assertion \<equiv> (Atomic (Pure (ELit (LBool True))))"

theorem sound_syntactic_translation_VCG:
  assumes "wf_stmt \<Delta> tcfes C"
      and "well_typed_cmd tcfe C"
      and "ConcreteSemantics.wf_abs_stmt tcfe (fst (translate \<Delta> C))"
      and "\<And>Cv. Cv \<in> snd (translate \<Delta> C) \<Longrightarrow> ConcreteSemantics.wf_abs_stmt tcfe Cv"
      and "TypedEqui.wf_assertion tcfe P \<and> TypedEqui.wf_assertion tcfe Q"
      and "typed_stmt C" (* TODO: Unify the two notions of typing *)
      and AbsTypeWf: "abs_type_wf (interp.domains \<Delta>)"

      and "mdecl = (triple_as_method_decl ts Ps (fst (translate_syn \<Delta> tcfes C)) Qs)"
      and MethodCorrect: "vpr_method_correct_total (default_ctxt (domains \<Delta>) mdecl) (\<lambda>_ :: int full_total_state. True) mdecl"     
      and AuxiliaryMethodsCorrect:
        "\<And> stmtAux. stmtAux \<in> snd (translate_syn \<Delta> tcfes C) \<Longrightarrow> 
             let mdeclAux = triple_as_method_decl ts 
                              true_syn_assertion stmtAux true_syn_assertion 
             in
             vpr_method_correct_total (default_ctxt (domains \<Delta>) mdeclAux) (\<lambda>_ :: int full_total_state. True) mdeclAux"
 
      and ViperTyped: 
            "stmt_typing (program_total (default_ctxt (domains \<Delta>) mdecl)) (nth_option ts)
                   (stmt.Seq (stmt.Seq (stmt.Inhale Ps) (fst (translate_syn \<Delta> tcfes C))) (stmt.Exhale Qs))"
      and "nth_option (map (set_from_type undefined) ts) = abs_type_context.variables tcfe"
      and "P = make_semantic_assertion_gen False \<Delta> tcfes Ps"
      and "Q = make_semantic_assertion_gen False \<Delta> tcfes Qs"     
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

    have A1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) ?Ctr_mainV)"
      apply (rule VCG_to_verifies_set)
      using MethodCorrect
      unfolding \<open>mdecl = _\<close>
          apply blast
         apply simp
      using ViperTyped
      unfolding \<open>mdecl = _\<close>
        apply blast
       defer
      apply (simp add: default_ctxt_def)
      sorry
      
    have "ConcreteSemantics.verifies_set tcfe (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)) (compile False \<Delta> tcfes ?Ctr_mainV)"
    proof -
      have "tcfe = t2a_ctxt ?ctxt (nth_option ts)"
        sorry      
      moreover have "tcfes = (nth_option ts, declared_fields (program_total ?ctxt))"
        sorry
      moreover have "\<Delta> = (ctxt_to_interp ?ctxt)"
        sorry
      ultimately show ?thesis
        using A1
        by metis
    qed

    hence "ConcreteSemantics.verifies_set tcfe (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
              (abs_stmt.Inhale P ;; compile False \<Delta> tcfes ?Ctr_main ;; abs_stmt.Exhale Q)"
      using \<open>P = _\<close> \<open>Q = _\<close>
      by simp

    thus ?thesis
      sorry \<comment>\<open>Thibault: TODO monotonicity etc...\<close>     
  qed


  fix Cv
  
  assume "Cv \<in> compile False \<Delta> tcfes ` snd (translate_syn \<Delta> tcfes C)"
  from this obtain Cv_syn where "Cv_syn \<in> snd (translate_syn \<Delta> tcfes C)" and "Cv = compile False \<Delta> tcfes Cv_syn"
    by blast
  let ?mdeclAux = "triple_as_method_decl ts 
                              true_syn_assertion Cv_syn true_syn_assertion"
  let ?ctxt = "(default_ctxt (domains \<Delta>) ?mdeclAux) :: int total_context"

  have TypingAux: "stmt_typing (program_total (default_ctxt (interp.domains \<Delta>) (triple_as_method_decl ts true_syn_assertion Cv_syn true_syn_assertion)))
     (nth_option ts) (stmt.Seq (stmt.Seq (stmt.Inhale true_syn_assertion) Cv_syn) (stmt.Exhale true_syn_assertion))"
    sorry

  show "ConcreteSemantics.verifies_set tcfe atrue Cv"
  proof -
    have "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) 
               (stmt.Seq (stmt.Seq (stmt.Inhale true_syn_assertion) Cv_syn) (stmt.Exhale true_syn_assertion)))"
      apply (rule VCG_to_verifies_set)
      using AuxiliaryMethodsCorrect[OF \<open>Cv_syn \<in> _\<close>]
      unfolding \<open>mdecl = _\<close> Let_def  
         apply blast
        apply simp
        apply (rule TypingAux)
       defer
       apply (simp add: default_ctxt_def AbsTypeWf)
      sorry

    hence A1: "ConcreteSemantics.verifies_set (t2a_ctxt ?ctxt ?\<Lambda>) (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>))
               (compile False (ctxt_to_interp ?ctxt) (?\<Lambda>, declared_fields (program_total ?ctxt)) Cv_syn)"
      sorry \<comment>\<open>TODO: Thibault --> remove inhale true exhale true\<close>

    hence "ConcreteSemantics.verifies_set tcfe (initial_vcg_states_equi (t2a_ctxt ?ctxt ?\<Lambda>)) (compile False \<Delta> tcfes Cv_syn)"
    proof -
      have "tcfe = t2a_ctxt ?ctxt (nth_option ts)"
        sorry      
      moreover have "tcfes = (nth_option ts, declared_fields (program_total ?ctxt))"
        sorry    
      moreover have "\<Delta> = (ctxt_to_interp ?ctxt)"
        sorry
      ultimately show ?thesis
        using A1
        by argo        
    qed

    thus ?thesis
      sorry \<comment>\<open>Thibault: TODO monotonicity etc...\<close>
  qed
qed

end