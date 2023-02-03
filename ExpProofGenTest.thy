theory ExpProofGenTest
imports ExpRel ExprWfRel TotalSemProperties TotalViper.ViperBoogieTranslationInterface
begin

text \<open>
The goal is to generate proofs of Viper programs containing a single \<open>x := e\<close> statement. I will
pursue this goal in three phases:

  \<^item> Phase 1: \<open>e\<close> contains no lazy operations and is trivially well-defined
  \<^item> Phase 2: \<open>e\<close> is trivially well-defined
  \<^item> Phase 3: No restrictions on \<open>e\<close> other than general subset restriction
\<close>

(*
definition assert_rel :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> ViperLang.program \<Rightarrow> 'a total_context \<Rightarrow>  'a astcontext_bpl \<Rightarrow>
       viper_expr \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont)  \<Rightarrow> bool"
  where
   "assert_rel R Pr ctxt_vpr ctxt e_vpr \<gamma> \<gamma>' \<equiv> 
    \<forall> \<omega> ns res. R \<omega> ns \<longrightarrow> 
           red_exhale Pr ctxt_vpr \<omega> (Atomic (Pure e_vpr)) (get_m_total_full \<omega>) res \<longrightarrow>

           (res \<noteq> ExhaleFailure \<longrightarrow> \<comment>\<open>for general exhales would have to take resulting mask into account\<close>
               (\<exists>\<gamma>' ns'. red_ast_bpl ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R \<omega> ns')) \<and>
           (res = ExhaleFailure \<longrightarrow> 
              (\<exists>c'.  snd c' = Failure \<and>
                    red_ast_bpl ctxt (\<gamma>, Normal ns) c'))"
*)

subsection \<open>Well formedness of type relation\<close>

definition type_interp_rel_wf :: "('a \<Rightarrow> abs_type) \<Rightarrow> ('a vbpl_absval) absval_ty_fun  \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> bool"
  where "type_interp_rel_wf A_vpr A_bpl Trep \<equiv> 
    \<forall>v ty_vpr ty_bpl. get_type A_vpr v = ty_vpr \<longrightarrow>
                      vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl \<longrightarrow>
                      type_of_val A_bpl (val_rel_vpr_bpl v) = ty_bpl"

lemma type_interp_rel_wf_vbpl: 
  assumes "A_vpr = domain_type Trep"
    shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain d where "domain_translation Trep (A_vpr a) = Some d" and "ty_bpl = TCon (fst d) (snd d)"
      by fastforce
    hence "vbpl_absval_ty Trep (ADomainVal a) = d" using \<open>A_vpr = domain_type Trep\<close>
      by simp
    hence "type_of_vbpl_val Trep (AbsV (ADomainVal a)) = ty_bpl" using \<open>ty_bpl = _\<close>
      by simp
    thus ?thesis using VAbs
      by simp     
  qed (insert * **, auto)
qed

lemma type_interp_rel_wf_vbpl_no_domains:
  assumes "\<And> d. domain_translation Trep d = None"
  shows "type_interp_rel_wf A_vpr (vbpl_absval_ty Trep) Trep"
  unfolding type_interp_rel_wf_def
proof (rule allI | rule impI)+
  fix v ty_vpr ty_bpl
  assume *:"get_type A_vpr v = ty_vpr" and
         **:"vpr_to_bpl_ty Trep ty_vpr = Some ty_bpl"
  show "type_of_vbpl_val Trep (val_rel_vpr_bpl v) = ty_bpl"
  proof (cases v)
    case (VAbs a)
    fix contra
    from VAbs * have "ty_vpr = TAbs (A_vpr a)" by simp
    with ** obtain d where "domain_translation Trep (A_vpr a) = Some d"
      by fastforce
    with assms show contra 
      by simp
  qed (insert * **, auto)
qed

subsection \<open>Statement relation - general statement\<close>

text\<open> Points to think about:
  \<^item> backward vs. forward simulation (also tracking single Boogie state vs sets of Boogie states)
\<close>

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a stmt_result_total"

definition red_stmt_total_smallstep :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> type_context \<Rightarrow> 'a stmt_config \<Rightarrow> 'a stmt_config \<Rightarrow> bool"
  where "red_stmt_total_smallstep ctxt R \<Lambda> config1 config2 \<equiv> True"

definition stmt_rel_small_step :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                                   'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow>
                                   type_context \<Rightarrow> ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
                                   ViperLang.stmt \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where "stmt_rel_small_step R ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'  \<equiv>
           \<comment>\<open>for all  Viper and Boogie states in the input relation\<close>
           \<forall> \<omega> ns. R \<omega> ns \<longrightarrow>               
               \<comment>\<open>If the Boogie program starting at program point \<^term>\<open>\<gamma>\<close> cannot fail\<close>
               (\<forall> \<gamma>' state_bpl. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', state_bpl)) \<longrightarrow> state_bpl \<noteq> Failure) \<longrightarrow>
               \<comment>\<open>Then the Viper statement \<^term>\<open>stmt_vpr\<close> cannot fail\<close>
               (\<forall> a b. red_stmt_total_smallstep ctxt_vpr StateCons \<Lambda> (Inl stmt_vpr, RNormal \<omega>) (a,b) \<longrightarrow>
                     b \<noteq> RFailure )"
(*\<and>
                     (a = Inr () \<longrightarrow> \<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns')) )
                  "*)
 
definition stmt_rel :: "('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow>
                               ('a full_total_state \<Rightarrow> ('a vbpl_absval) nstate \<Rightarrow> bool) \<Rightarrow> 
                                'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> 
                                type_context \<Rightarrow> ast \<Rightarrow> 'a econtext_bpl \<Rightarrow>
                                ViperLang.stmt \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> (Ast.bigblock \<times> cont) \<Rightarrow> bool"
  where 
    "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>' \<equiv>
      \<comment>\<open>for all  Viper and Boogie states in the input relation\<close>
      \<forall> \<omega> ns res. R \<omega> ns \<longrightarrow> 
             \<comment>\<open>If the Viper stmt reduces\<close>
             red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> res \<longrightarrow>
             (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                 \<comment>\<open>Normal Viper executions can be simulated by normal Boogie executions\<close>
                 (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                 \<comment>\<open>If the Viper execution fails, then there is a failing Boogie execution\<close>
                (\<exists>c'. snd c' = Failure \<and>
                      red_ast_bpl P ctxt (\<gamma>, Normal ns) c'))"
 
lemma stmt_rel_intro[case_names base step]:
  assumes 
  "\<And>\<omega> ns \<omega>'. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>') \<Longrightarrow>
          \<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')" and
  "\<And>\<omega> ns.
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure \<Longrightarrow>
          \<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'"
  using assms
  unfolding stmt_rel_def  
  by blast

definition stmt_rel_aux 
  where "stmt_rel_aux R' \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>' ns res \<equiv>             
          (\<forall>\<omega>'. res = RNormal \<omega>' \<longrightarrow>
                 (\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'))) \<and>
             (res = RFailure \<longrightarrow> 
                (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure))"

lemma stmt_rel_aux_intro:
  assumes "\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow>
            \<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')" and
          "res = RFailure \<Longrightarrow> 
            (\<exists>c'. red_ast_bpl P ctxt (\<gamma>, Normal ns) c' \<and> snd c' = Failure)"
  shows "stmt_rel_aux R' \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>' ns res"
  using assms
  unfolding stmt_rel_aux_def
  by blast

lemma stmt_rel_intro_2:
  assumes 
  "\<And>\<omega> ns res. 
          R \<omega> ns \<Longrightarrow> 
          red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> res \<Longrightarrow>
          stmt_rel_aux R' \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>' ns res"
shows "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'"
  using assms
  unfolding stmt_rel_def stmt_rel_aux_def
  by blast

lemma stmt_rel_normal_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> (RNormal \<omega>')"
    shows   "\<exists>ns'. (red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns')"
  using assms
  unfolding stmt_rel_def
  by blast

lemma stmt_rel_failure_elim:
  assumes "stmt_rel R R' ctxt_vpr StateCons \<Lambda> P ctxt stmt_vpr \<gamma> \<gamma>'" and
          "R \<omega> ns" and
          "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt_vpr \<omega> RFailure"
  shows "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  using assms
  unfolding stmt_rel_def
  by blast

lemma stmt_rel_propagate:
  assumes "\<And> \<omega> ns. R0 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'" and
          "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"  
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> (RNormal \<omega>')"

  from \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using stmt_rel_normal_elim[OF assms(2)] RedVpr
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> RFailure"

  from \<open>R0 \<omega> ns\<close> and assms(1) obtain ns1 where
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega> ns1"
    by blast

  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using stmt_rel_failure_elim[OF assms(2)] RedVpr
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
qed

lemma stmt_rel_propagate_same_rel:
  assumes "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns') \<and> R \<omega> ns'" and
          "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>1 \<gamma>2"
        shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using stmt_rel_propagate assms
  by blast

lemma stmt_rel_propagate_2:
  assumes "stmt_rel R0 R1 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega> ns. R1 \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega> ns'"
  shows "stmt_rel R0 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume "R0 \<omega> ns" and
         "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> (RNormal \<omega>')"  
  from this obtain ns1 where 
    "red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>1, Normal ns1)" and "R1 \<omega>' ns1"
    using assms(1) stmt_rel_normal_elim 
    by blast

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>0, Normal ns) (\<gamma>2, Normal ns') \<and> R2 \<omega>' ns'"
    using assms(2)
    by (metis (no_types, opaque_lifting) red_ast_bpl_transitive)
next
  fix \<omega> ns
  assume "R0 \<omega> ns" and
         "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr stmt_vpr \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>0, Normal ns) c'"
    using assms(1) stmt_rel_failure_elim 
    by blast
qed

lemma stmt_rel_propagate_2_same_rel:
  assumes "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>1" and
          "\<And> \<omega> ns. R \<omega> ns \<Longrightarrow> \<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>2, Normal ns') \<and> R \<omega> ns'"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt stmt_vpr \<gamma>0 \<gamma>2"
  using assms stmt_rel_propagate_2
  by blast

lemma stmt_rel_seq:
  assumes "stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt s1_vpr \<gamma>1 \<gamma>2" and
          "stmt_rel R2 R3 ctxt_vpr StateCons \<Lambda>_vpr P ctxt s2_vpr \<gamma>2 \<gamma>3"
  shows 
    "stmt_rel R1 R3 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Seq s1_vpr s2_vpr) \<gamma>1 \<gamma>3"
(* "stmt_rel R1 R3 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Seq s1_vpr s2_vpr) (Seq s1_bpl s2_bpl)" *)
proof (rule stmt_rel_intro)
  fix \<omega> ns \<omega>'
  assume R1:"R1 \<omega> ns" and RedStmt:"red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Seq s1_vpr s2_vpr) \<omega> (RNormal \<omega>')"
  from RedStmt obtain \<omega>'' where
    RedS1: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s1_vpr \<omega> (RNormal \<omega>'')" and
    RedS2: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s2_vpr \<omega>'' (RNormal \<omega>')"
    by (auto elim: RedSeqNormal_case)

  with stmt_rel_normal_elim[OF assms(1) R1 RedS1] stmt_rel_normal_elim[OF assms(2) _ RedS2]
  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) (\<gamma>3, Normal ns') \<and> R3 \<omega>' ns'"
    by (meson red_ast_bpl_transitive)
next
  fix \<omega> ns
  assume R1: "R1 \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (Seq s1_vpr s2_vpr) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) c'"
  proof (rule RedSeqFailure_case)
   \<comment>\<open>s1 normal, s2 fails\<close>
    fix \<omega>'
    assume RedS1: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s1_vpr \<omega> (RNormal \<omega>')" and
           RedS2: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s2_vpr \<omega>' RFailure"
    show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) c'"
      using stmt_rel_normal_elim[OF assms(1) R1 RedS1] stmt_rel_failure_elim[OF assms(2) _ RedS2]      
      by (meson red_ast_bpl_transitive)
  next
    assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s1_vpr \<omega> RFailure"
    thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>1, Normal ns) c'"
      using stmt_rel_failure_elim[OF assms(1) R1]
      by blast
  qed (simp)
qed

lemma stmt_rel_seq_same_rel:
  assumes "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s1_vpr \<gamma>1 \<gamma>2" and
          "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s2_vpr \<gamma>2 \<gamma>3"
  shows 
    "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (Seq s1_vpr s2_vpr) \<gamma>1 \<gamma>3"
  using assms stmt_rel_seq
  by blast

method stmt_rel_if_proof_tac uses InitElim RedBranch ResultEq RedAstToIf RedCondBpl RedParsedIfRule =
        (
         rule InitElim,
         (insert RedBranch ResultEq),
          simp,
         (rule exI, rule conjI),
         (rule red_ast_bpl_transitive),
         (rule RedAstToIf),
         (rule red_ast_bpl_transitive),
         (rule red_ast_bpl_one_step_empty_simple_cmd),
         (rule RedParsedIfRule),
         (fastforce intro: RedCondBpl),
         auto
        )
         
lemma stmt_rel_if:
  assumes \<comment>\<open>When invoking the wf_rel tactic, apply one of the wf_rel extension lemmas such that the 
            wf_rel tactic itself need not guarantee progress to the if block\<close>
     ExpWfRel:          
          "expr_wf_rel (\<lambda> _ \<omega>. R \<omega>) ctxt_vpr StateCons P ctxt cond 
           \<gamma>1
           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)" and
     ExpRel: "exp_rel_vpr_bpl (\<lambda> _ \<omega>. R \<omega>) ctxt_vpr ctxt cond cond_bpl" and
     ThnRel: "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s_thn (thn_hd, convert_list_to_cont thn_tl (KSeq next cont)) (next, cont)" and
     ElsRel: "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt s_els (els_hd, convert_list_to_cont els_tl (KSeq next cont)) (next, cont)"
   shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (If cond s_thn s_els) \<gamma>1 (next, cont)"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume R: "R \<omega> ns"
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (stmt.If cond s_thn s_els) \<omega> res"

  thus "stmt_rel_aux R \<Lambda>_vpr P ctxt (stmt.If cond s_thn s_els) \<gamma>1 (next, cont) ns res"
  proof (rule RedIf_case)
    \<comment>\<open>thn case\<close>
    assume RedCond: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and 
           RedThn: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_thn \<omega> res"

    from RedCond wf_rel_normal_elim[OF ExpWfRel R] obtain ns' where
     Rns': "R \<omega> ns'" and
     RedAstToIf: "red_ast_bpl P ctxt (\<gamma>1, Normal ns)
           ((if_bigblock name (Some cond_bpl) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont), Normal ns')"
      by blast

    have RedCondBpl: "red_expr_bpl ctxt cond_bpl ns' (BoolV True)"
     using ExpRel RedCond Rns'
     by (fastforce elim: exp_rel_vpr_bpl_elim)
    
    show "stmt_rel_aux R \<Lambda>_vpr P ctxt (stmt.If cond s_thn s_els) \<gamma>1 (next, cont) ns res"
      

    proof (rule stmt_rel_aux_intro)
      fix \<omega>'
      assume "res = RNormal \<omega>'"

      show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) ((next, cont), Normal ns') \<and> R \<omega>' ns'"
        by (stmt_rel_if_proof_tac 
                   InitElim: exE[OF stmt_rel_normal_elim[OF ThnRel Rns']] 
                   RedBranch: RedThn 
                   ResultEq: \<open>res = _\<close> 
                   RedAstToIf: RedAstToIf
                   RedCondBpl: RedCondBpl
                   RedParsedIfRule: RedParsedIfTrue)
     next
       assume "res = RFailure"
       show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure" 
        by (stmt_rel_if_proof_tac 
                   InitElim: exE[OF stmt_rel_failure_elim[OF ThnRel Rns']] 
                   RedBranch: RedThn 
                   ResultEq: \<open>res = _\<close> 
                   RedAstToIf: RedAstToIf
                   RedCondBpl: RedCondBpl
                   RedParsedIfRule: RedParsedIfTrue)
     qed
   next
    assume RedCond: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)" and 
           RedEls: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr s_els \<omega> res"

    from RedCond wf_rel_normal_elim[OF ExpWfRel R] obtain ns' where
     Rns': "R \<omega> ns'" and
     RedAstToIf: "red_ast_bpl P ctxt (\<gamma>1, Normal ns)
           ((if_bigblock name (Some cond_bpl) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont), Normal ns')"
      by blast

    have RedCondBpl: "red_expr_bpl ctxt cond_bpl ns' (BoolV False)"
     using ExpRel RedCond Rns'
     by (fastforce elim: exp_rel_vpr_bpl_elim)
    
    show "stmt_rel_aux R \<Lambda>_vpr P ctxt (stmt.If cond s_thn s_els) \<gamma>1 (next, cont) ns res"
      

    proof (rule stmt_rel_aux_intro)
      fix \<omega>'
      assume "res = RNormal \<omega>'"

      show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) ((next, cont), Normal ns') \<and> R \<omega>' ns'"        
        by (stmt_rel_if_proof_tac 
                   InitElim: exE[OF stmt_rel_normal_elim[OF ElsRel Rns']] 
                   RedBranch: RedEls 
                   ResultEq: \<open>res = _\<close> 
                   RedAstToIf: RedAstToIf
                   RedCondBpl: RedCondBpl
                   RedParsedIfRule: RedParsedIfFalse)
     next
       assume "res = RFailure"
       show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure"         
        by (stmt_rel_if_proof_tac 
                   InitElim: exE[OF stmt_rel_failure_elim[OF ElsRel Rns']] 
                   RedBranch: RedEls 
                   ResultEq: \<open>res = _\<close> 
                   RedAstToIf: RedAstToIf
                   RedCondBpl: RedCondBpl
                   RedParsedIfRule: RedParsedIfFalse)
     qed
   next
     fix e
     assume "res = RFailure" and "e \<in> sub_expressions (stmt.If cond s_thn s_els)" and 
            "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
     hence RedCond: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
       by simp
     
     show "stmt_rel_aux R \<Lambda>_vpr P ctxt (stmt.If cond s_thn s_els) \<gamma>1 (next, cont) ns res"
     proof (rule stmt_rel_aux_intro)
       assume "res = RFailure"
       show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure "
         using wf_rel_failure_elim[OF ExpWfRel R RedCond]
         by simp
     qed (simp add: \<open>res = _\<close>)
   qed
 qed

 text \<open>Skip relation\<close>

lemma stmt_rel_skip: "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.Skip) \<gamma> \<gamma>"
proof (rule stmt_rel_intro_2)
  fix \<omega> ns res
  assume "R2 \<omega> ns" and "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr Skip \<omega> res"
  hence "res = RNormal \<omega>"
    by (auto elim: RedSkip_case)

  thus "stmt_rel_aux R2 \<Lambda>_vpr P ctxt Skip \<gamma> \<gamma> ns res"
    unfolding stmt_rel_aux_def
    using \<open>R2 \<omega> ns\<close> red_ast_bpl_refl by blast
qed


subsection \<open>Local variable assignment relation\<close>

lemma assign_rel_simple:
  assumes R_def:  "R3 = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R2 \<omega> ns)" and
          VprTy: "\<Lambda>_vpr x_vpr = Some ty" and
          ExpWfRel: "expr_wf_rel R3 ctxt_vpr StateCons P ctxt e_vpr \<gamma> ((BigBlock name ((Lang.Assign x_bpl e_bpl)#cs) str tr), cont)" 
                    (is "expr_wf_rel R3 ctxt_vpr StateCons P ctxt e_vpr \<gamma> (?b, cont)") and
          BplTy: "lookup_var_ty (var_context ctxt) x_bpl = Some ty_bpl" and
          TyRel: "vpr_to_bpl_ty Trep ty = Some ty_bpl" and
                    \<comment>\<open>Key assignment property for R2\<close>
          RAssign:  "\<And> \<omega> ns v . R2 \<omega> ns \<Longrightarrow>
                           get_type (absval_interp_total ctxt_vpr) v = ty \<Longrightarrow>
                           type_of_val (type_interp ctxt) (val_rel_vpr_bpl v) = ty_bpl \<Longrightarrow>
                           R2 (update_var_total \<omega> x_vpr v) (update_var (var_context ctxt) ns x_bpl (val_rel_vpr_bpl v))" and
          TyRelWf: "type_interp_rel_wf (absval_interp_total ctxt_vpr) (type_interp ctxt) Trep" and
          ExpRel: "exp_rel_vpr_bpl R3 ctxt_vpr ctxt e_vpr e_bpl"
          
        shows "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) 
               \<gamma>
               (BigBlock name cs str tr, cont)" (is "stmt_rel R2 R2 ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.LocalAssign x_vpr e_vpr) \<gamma> ?\<gamma>'") 
proof (cases rule: stmt_rel_intro)
\<comment>\<open>normal case\<close>
  fix \<omega> ns \<omega>'
  assume R: "R2 \<omega> ns" and
         RedVpr: "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> (RNormal \<omega>')"

  show "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>', Normal ns') \<and> R2 \<omega>' ns'"
  proof -
    from RedVpr obtain v where RedEVpr: "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>e_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t (Val v)" and 
                                "\<omega>' = (update_var_total \<omega> x_vpr v)" and
                                vTyVpr: "get_type (absval_interp_total ctxt_vpr) v = ty"      
      apply (rule red_stmt_total.cases)
      using VprTy
      by auto

    from this obtain ns' where
        R':"R3 \<omega> \<omega> ns'" and
        RedBplWf:"red_ast_bpl P ctxt (\<gamma>, Normal ns) ((?b, cont), Normal ns')"
      using R R_def wf_rel_normal_elim[OF ExpWfRel]
      by blast

    let ?v_bpl = "val_rel_vpr_bpl v"
    have RedEBpl:"red_expr_bpl ctxt e_bpl ns' ?v_bpl"
      apply (rule exp_rel_vpr_bpl_elim_2[OF ExpRel])
      using R' RedEVpr R_def
      by fastforce

    have ValBplTy:"type_of_val (type_interp ctxt) ?v_bpl = instantiate [] ty_bpl"
      using vTyVpr TyRel TyRelWf
      unfolding type_interp_rel_wf_def
      by simp

    let ?ns'' = "update_var (var_context ctxt) ns' x_bpl ?v_bpl"

    have RedBpl: "red_ast_bpl P ctxt ((?b, cont), Normal ns') ((BigBlock name cs str tr, cont), Normal ?ns'')"
      unfolding red_ast_bpl_def
      apply (rule converse_rtranclp_into_rtranclp)
       apply rule
       apply rule
         apply (rule BplTy)
        apply (rule ValBplTy)
      using RedEBpl
      by auto

    moreover have "R3 \<omega>' \<omega>' ?ns''" 
      apply (subst \<open>\<omega>' = _\<close>)+
      using R_def RAssign R' vTyVpr ValBplTy 
      by auto

    ultimately show ?thesis 
      using RedBplWf R_def \<open>\<omega>' = _\<close> red_ast_bpl_def
      by (metis (mono_tags, lifting) rtranclp_trans)
  qed
next
  \<comment>\<open>Failure case\<close>
  fix \<omega> ns 
  assume "R2 \<omega> ns" and 
         RedVpr:"red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (LocalAssign x_vpr e_vpr) \<omega> RFailure"
  
  from RedVpr show "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
  case (RedSubExpressionFailure e)
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by simp

  then show ?thesis 
    using  R_def \<open>R2 \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
    by blast
  qed
qed

subsection \<open>Misc\<close>

lemma init_state:
  assumes "R0 \<omega> ns" and
          "is_empty_total \<omega>" 
  shows "\<exists>ns'. red_ast_bpl P ctxt ((BigBlock name cs str tr,cont), Normal ns) (\<gamma>1, Normal ns') \<and> R1 \<omega> ns'"
  oops

lemma red_ast_bpl_propagate_rel:
  assumes "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1)" and
          "R1 \<omega> ns1" and
          "R1 \<omega> ns1 \<Longrightarrow> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2) \<and> R2 \<omega> ns2"
        shows "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>2, Normal ns2) \<and> R2 \<omega> ns2"
  using assms
  unfolding red_ast_bpl_def
  by auto

lemma red_ast_bpl_propagate_same_rel:
    assumes "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>1, Normal ns1)" and
          "R \<omega> ns1" and
          "R \<omega> ns1 \<Longrightarrow> red_ast_bpl P ctxt (\<gamma>1, Normal ns1) (\<gamma>2, Normal ns2) \<and> R \<omega> ns2"
        shows "red_ast_bpl P ctxt (\<gamma>0, Normal ns0) (\<gamma>2, Normal ns2) \<and> R \<omega> ns2"
  using assms
  unfolding red_ast_bpl_def
  by auto

lemma lookup_zero_mask_bpl:
  assumes "state_rel Pr TyRep Tr ctxt mvar \<omega>_def \<omega> ns" and
          "const_repr Tr = const_repr_basic"
  shows "lookup_var (var_context ctxt) ns 2 = Some (AbsV (AMask zero_mask_bpl))"
  using boogie_const_rel_lookup[where ?const = CZeroMask] state_rel_boogie_const[OF assms(1)] assms
  by fastforce

lemma tr_def_field_translation:
  assumes "tr = tr_def" and
          "field_translation tr_def = F"
        shows "field_translation tr = F"
  using assms by simp

(*
method zero_mask_lookup_tac uses tr_def =
       (rule boogie_const_rel_lookup_2[where ?const = CZeroMask],
        rule state_rel_boogie_const,
         blast,
         simp add: tr_def,
         simp)
*)
(* (rule tr_def_field_translation[OF tr_def], fastforce)*)
(*
method red_assume_good_state uses CtxtWf tr_def =
     (rule RedAssumeOk,
      rule assume_state_normal[OF CtxtWf],
      (rule tr_def_field_translation[OF tr_def], fastforce),
      simp add: tr_def,
      simp add: tr_def,
      simp add: tr_def,
      simp add: tr_def)
*)


end