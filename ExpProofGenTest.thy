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

lemma vpr_to_bpl_val_type:
  assumes "get_type A v = ty_vpr" and
          "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl" and
          "domain_type TyRep = A"
  shows "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
proof (cases v)
  case (VAbs x5)
  then show ?thesis 
    using assms
    using type_interp_rel_wf_def type_interp_rel_wf_vbpl by blast
qed (insert assms, auto)

subsection \<open>Statement relation - general statement\<close>

text\<open> Points to think about:
  \<^item> backward vs. forward simulation (also tracking single Boogie state vs sets of Boogie states)
\<close>

type_synonym 'a stmt_config = "(stmt + unit) \<times> 'a stmt_result_total"
 
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
          "expr_wf_rel (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr StateCons P ctxt cond 
           \<gamma>1
           (if_bigblock name (Some (cond_bpl)) (thn_hd # thn_tl) (els_hd # els_tl), KSeq next cont)" and
     ExpRel: "exp_rel_vpr_bpl (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns) ctxt_vpr ctxt cond cond_bpl" and
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


    from RedCond wf_rel_normal_elim[OF ExpWfRel HOL.conjI[OF _ R]] obtain ns' where
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

    from RedCond wf_rel_normal_elim[OF ExpWfRel HOL.conjI[OF _ R]] obtain ns' where
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
     assume "res = RFailure" and "sub_expressions (stmt.If cond s_thn s_els) \<noteq> []" and 
            "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) (sub_expressions (stmt.If cond s_thn s_els)) \<omega> None"
     hence RedCond: "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>cond;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
       by (fastforce elim: red_pure_exps_total_singleton)
     
     show "stmt_rel_aux R \<Lambda>_vpr P ctxt (stmt.If cond s_thn s_els) \<gamma>1 (next, cont) ns res"
     proof (rule stmt_rel_aux_intro)
       assume "res = RFailure"
       show "\<exists>c'. red_ast_bpl P ctxt (\<gamma>1, Normal ns) c' \<and> snd c' = Failure "
         using wf_rel_failure_elim[OF ExpWfRel HOL.conjI[OF _ R]] RedCond
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
\<comment>\<open>Normal case\<close>
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
      apply (rule red_ast_bpl_one_simple_cmd)
       apply (rule Semantics.RedAssign)
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
  case (RedSubExpressionFailure)
  hence "ctxt_vpr, StateCons, Some \<omega> \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by (fastforce elim: red_pure_exps_total_singleton)

  then show ?thesis 
    using  R_def \<open>R2 \<omega> ns\<close> wf_rel_failure_elim[OF ExpWfRel]
    by blast
  qed
qed

subsection \<open>Field assignment relation\<close>

definition field_rel_single :: "program \<Rightarrow> 'a ty_repr_bpl \<Rightarrow> tr_vpr_bpl \<Rightarrow> char list \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  where "field_rel_single Pr TyRep Tr f_vpr e_f_bpl \<tau>_bpl  \<equiv> 
           has_Some (\<lambda>f_tr. e_f_bpl = Lang.Var f_tr) (field_translation Tr f_vpr) \<and>
           has_Some (\<lambda>\<tau>_vpr. vpr_to_bpl_ty TyRep \<tau>_vpr = Some \<tau>_bpl) (declared_fields Pr f_vpr)"


lemma field_assign_rel:
  assumes 
    HeapUpdWf: "heap_update_wf TyRep ctxt (heap_update Tr)" and
               "domain_type TyRep = absval_interp_total ctxt_vpr" and
               "type_interp ctxt = vbpl_absval_ty TyRep" and
    Rext: "Rext = (\<lambda> \<omega>def \<omega> ns. \<omega>def = \<omega> \<and> R \<omega> ns)"  and
    RcvWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rcv_vpr \<gamma> \<gamma>1" and
    RhsWfRel: "expr_wf_rel Rext ctxt_vpr StateCons P ctxt rhs_vpr \<gamma>1 \<gamma>2" and
    WriteableLocRel: "wf_rel_fieldacc get_writeable_locs Rext ctxt_vpr StateCons P ctxt rcv_vpr f_vpr 
                 \<gamma>2 
                 ((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)" and 
                   "h_bpl = heap_var Tr" and
                   HeapLookupTyBpl: "lookup_var_ty (var_context ctxt) h_bpl = Some (TConSingle (THeapId TyRep))" and
    HeapUpdateBpl: "h_upd_bpl = heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]" and    
    RcvRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rcv_vpr rcv_bpl" and
    FieldRelSingle: "field_rel_single (program_total ctxt_vpr) TyRep Tr f_vpr e_f_bpl \<tau>_bpl" and
    RhsRel: "exp_rel_vpr_bpl Rext ctxt_vpr ctxt rhs_vpr rhs_bpl" and

    \<comment>\<open>Key field assignment property for R\<close>
    RFieldAssign:  "\<And> \<omega> ns ty_vpr hb addr  f_bpl v . R \<omega> ns \<Longrightarrow>
                     declared_fields (program_total ctxt_vpr) f_vpr = Some ty_vpr \<Longrightarrow>
                     field_translation Tr f_vpr = Some f_bpl \<Longrightarrow>
                     vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl \<Longrightarrow>
                     type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl \<Longrightarrow>
                     (\<exists>hb f_bpl_val. 
                       lookup_var (var_context ctxt) ns (heap_var Tr) = Some (AbsV (AHeap hb)) \<and>
                       vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, []) \<and>
                       lookup_var (var_context ctxt) ns f_bpl = Some (AbsV (AField f_bpl_val)) \<and>
                       field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl]) \<and>
                       vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, []) \<and>
                       R (update_hh_loc_total_full \<omega> (addr,f_vpr) v) 
                         (update_var (var_context ctxt) ns (heap_var Tr) 
                               (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
                         ))"
  shows "stmt_rel R R ctxt_vpr StateCons \<Lambda>_vpr P ctxt (ViperLang.FieldAssign rcv_vpr f_vpr rhs_vpr) 
         \<gamma>
         (BigBlock name cs str tr, cont)" 
proof (rule stmt_rel_intro)
  let ?\<gamma>3="((BigBlock name ((Lang.Assign h_bpl h_upd_bpl)#cs) str tr), cont)"
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns"
  hence "Rext \<omega> \<omega> ns" using Rext by simp

  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> (RNormal \<omega>')"

  thus "\<exists>ns'. red_ast_bpl P ctxt (\<gamma>, Normal ns) ((BigBlock name cs str tr, cont), Normal ns') \<and> R \<omega>' ns'"
  proof cases
    case (RedFieldAssign addr v ty_vpr)
    from this  obtain ns1 where
      "Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
      by auto
    from this RedFieldAssign obtain ns2 where "Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast
    from this RedFieldAssign obtain ns3 where "Rext \<omega> \<omega> ns3" and RedNs3: "red_ast_bpl P ctxt (\<gamma>, Normal ns) (?\<gamma>3, Normal ns3)" 
      using wf_rel_normal_elim[OF WriteableLocRel] red_ast_bpl_transitive
      by blast
    hence "R \<omega> ns3"
      using Rext by simp

    obtain  f_bpl where
         "vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl" and
         "field_translation Tr f_vpr = Some f_bpl" and 
         "e_f_bpl = Lang.Var f_bpl"
      using FieldRelSingle \<open>declared_fields _ f_vpr = Some ty_vpr\<close>
      unfolding field_rel_single_def
      using has_SomeD by force      
 
   moreover have NewValTypeBpl: "type_of_vbpl_val TyRep (val_rel_vpr_bpl v) = \<tau>_bpl"
     using vpr_to_bpl_val_type[OF \<open>get_type _ v = ty_vpr\<close> \<open>vpr_to_bpl_ty TyRep ty_vpr = Some \<tau>_bpl\<close>]
           \<open>domain_type _ = _\<close>
     by simp

   ultimately obtain hb f_bpl_val
     where LookupHeapVarBpl: "lookup_var (var_context ctxt) ns3 (heap_var Tr) = Some (AbsV (AHeap hb))" and 
           HeapWellTyBpl:       "vbpl_absval_ty_opt TyRep (AHeap hb) = Some (THeapId TyRep, [])" and
           HeapUpdWellTyBpl: "vbpl_absval_ty_opt TyRep (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))) = Some (THeapId TyRep, [])" and
           LookupFieldVarBpl: "lookup_var (var_context ctxt) ns3 f_bpl = Some (AbsV (AField f_bpl_val))" and           
           FieldTyBpl: "field_ty_fun_opt TyRep f_bpl_val = Some ((TFieldId TyRep), [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])" and
           "R \<omega>'
                   (update_var (var_context ctxt) ns3 (heap_var Tr) 
                   (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))
             )" (is "R _ ?ns_upd")
     using RFieldAssign[OF \<open>R \<omega> ns3\<close> \<open>declared_fields _ f_vpr = Some ty_vpr\<close>] \<open>\<omega>' = _\<close>
     by blast

   from RcvRel have RedRcvBpl: "red_expr_bpl ctxt rcv_bpl ns3 (AbsV (ARef (Address addr)))"
     using \<open>Rext \<omega> \<omega> ns3\<close>  RedFieldAssign
     by (metis exp_rel_vpr_bpl_elim val_rel_vpr_bpl.simps(3))

   from RhsRel have RedRhsBpl: "red_expr_bpl ctxt rhs_bpl ns3 (val_rel_vpr_bpl v)" 
     using \<open>Rext \<omega> \<omega> ns3\<close>  RedFieldAssign
     by (meson  exp_rel_vpr_bpl_elim)

   from HeapUpdWf have 
      RedHeapUpdBpl:
     "red_expr_bpl ctxt (heap_update Tr (Lang.Var h_bpl) rcv_bpl e_f_bpl rhs_bpl [TConSingle (TNormalFieldId TyRep), \<tau>_bpl])
                             ns3 (AbsV (AHeap (hb( (Address addr,f_bpl_val) \<mapsto> (val_rel_vpr_bpl v) ))))"
     apply (rule heap_update_wf_apply)
     using  \<open>h_bpl = _\<close> Semantics.RedVar[OF LookupHeapVarBpl]
           apply simp
          apply (rule HeapWellTyBpl)
         apply (rule RedRcvBpl)
     using \<open>e_f_bpl = _\<close> Semantics.RedVar[OF LookupFieldVarBpl]
        apply simp
       apply (rule FieldTyBpl)
      apply (rule RedRhsBpl)
     apply (simp add: NewValTypeBpl)
     done

   have "red_ast_bpl P ctxt 
           ((BigBlock name (Assign h_bpl h_upd_bpl # cs) str tr, cont), Normal ns3) 
           ((BigBlock name cs str tr, cont), Normal ?ns_upd)"
     apply (rule red_ast_bpl_one_simple_cmd)
     apply (subst HOL.sym[OF \<open>h_bpl = _\<close>])
     apply (rule Semantics.RedAssign)
       apply (rule HeapLookupTyBpl)
     using HeapUpdWellTyBpl \<open>type_interp ctxt = _\<close>
      apply simp
     by (fastforce intro: RedHeapUpdBpl simp: \<open>h_upd_bpl = _\<close>)
    thus ?thesis
      using RedNs3 \<open>R \<omega>' ?ns_upd\<close>
      using red_ast_bpl_transitive by blast      
  qed
next
  fix \<omega> ns 
  assume "R \<omega> ns"
  hence "Rext \<omega> \<omega> ns" using Rext by simp
  assume "red_stmt_total ctxt_vpr StateCons \<Lambda>_vpr (FieldAssign rcv_vpr f_vpr rhs_vpr) \<omega> RFailure"
  thus "\<exists>c'. snd c' = Failure \<and> red_ast_bpl P ctxt (\<gamma>, Normal ns) c'"
  proof cases
    case (RedFieldAssignFailure r v)
    from this obtain ns1 where
      "Rext \<omega> \<omega> ns1" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>1, Normal ns1)"
      using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
      by auto      
    from this RedFieldAssignFailure obtain ns2 where "Rext \<omega> \<omega> ns2" and "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>2, Normal ns2)"
      using wf_rel_normal_elim[OF RhsWfRel] red_ast_bpl_transitive
      by blast

    with RedFieldAssignFailure obtain \<gamma>' where "red_ast_bpl P ctxt (\<gamma>, Normal ns) (\<gamma>', Failure)"
      using wf_rel_failure_elim[OF WriteableLocRel \<open>Rext \<omega> \<omega> ns2\<close>] red_ast_bpl_transitive
      by (metis (no_types, opaque_lifting) ref.exhaust ref.sel snd_conv surj_pair)
    thus ?thesis
      by (meson snd_conv)
  next
    case RedSubExpressionFailure
    hence RedSubExpFailureAux: "red_pure_exps_total ctxt_vpr StateCons (Some \<omega>) [rcv_vpr, rhs_vpr] \<omega> None"
      by simp
    show ?thesis
    proof (cases  "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure")
      case True
      then show ?thesis 
        using wf_rel_failure_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>]
        by blast
    next
      case False
      from this obtain v where "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rcv_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t Val v" and
                               "ctxt_vpr, StateCons, (Some \<omega>) \<turnstile> \<langle>rhs_vpr; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
        using RedSubExpFailureAux
        by (auto elim: red_pure_exp_total_elims)
      then show ?thesis 
        using wf_rel_normal_elim[OF RcvWfRel \<open>Rext \<omega> \<omega> ns\<close>] wf_rel_failure_elim[OF RhsWfRel] red_ast_bpl_transitive
        by blast
    qed
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

lemma tr_def_field_translation:
  assumes "tr = tr_def" and
          "field_translation tr_def = F"
        shows "field_translation tr = F"
  using assms by simp

lemma exp_rel_true_imp_1:
  assumes  "exp_rel_vpr_bpl R ctxt_vpr ctxt e_vpr e_bpl"
  shows "exp_rel_vpr_bpl R ctxt_vpr ctxt (Binop (ELit (ViperLang.LBool True)) BImp e_vpr) e_bpl"
proof (rule exp_rel_equiv_vpr[OF _ assms])
  fix v1 StateCons \<omega> \<omega>_def_opt
  assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>Binop (ELit (ViperLang.LBool True)) BImp e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  thus "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
  proof (rule RedBinop_case)
    fix v1a contra
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ELit (ViperLang.lit.LBool True);\<omega>\<rangle> [\<Down>]\<^sub>t Val v1a"
    hence "v1a = VBool True"
      by (metis TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(1))
    assume "eval_binop_lazy v1a BImp = Some v1"
    thus contra using \<open>v1a = _\<close>
      by simp
  next
    fix v1a v2
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>ELit (ViperLang.lit.LBool True);\<omega>\<rangle> [\<Down>]\<^sub>t Val v1a"
    hence "v1a = VBool True"
      by (metis TotalExpressions.RedLit_case extended_val.inject val_of_lit.simps(1))
    assume "eval_binop v1a BImp v2 = BinopNormal v1"
    hence "v2 = v1"
      unfolding \<open>v1a = _\<close>
      by (rule eval_binop.elims) auto
    assume "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
    thus "ctxt_vpr, StateCons, \<omega>_def_opt \<turnstile> \<langle>e_vpr;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      by (simp add: \<open>v2 = v1\<close>)
  qed
qed

    
end