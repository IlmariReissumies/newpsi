(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Bisim_Struct_Cong
  imports Weak_Bisim_Pres Bisim_Struct_Cong
begin

context env begin

lemma weakBisimParComm:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<approx> Q \<parallel> P"
by(metis bisim_par_comm strongBisimWeakBisim)

lemma weakBisimResComm:
  fixes x :: name
  and   \<Psi> :: 'b
  and   y :: name
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<approx> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(metis bisim_res_comm strongBisimWeakBisim)

lemma weakBisimResComm':
  fixes x    :: name
  and   \<Psi>   :: 'b
  and   xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<approx> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(metis bisim_res_comm' strongBisimWeakBisim)

lemma weakBisimScopeExt:
  fixes x :: name
  and   \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<approx> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
using assms
by(metis bisim_scope_ext strongBisimWeakBisim)

lemma weakBisimScopeExtChain:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<approx> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>Q)"
using assms
by(metis bisim_scope_ext_chain strongBisimWeakBisim)

lemma weakBisimParAssoc:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<approx> P \<parallel> (Q \<parallel> R)"
by(metis bisim_par_assoc strongBisimWeakBisim)

lemma weakBisimParNil:
  fixes P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> \<zero> \<approx> P"
by(metis bisim_par_nil strongBisimWeakBisim)

lemma weakBisimResNil:
  fixes x :: name
  and   \<Psi> :: 'b
  
  assumes "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<approx> \<zero>"
using assms
by(metis bisim_res_nil strongBisimWeakBisim)

lemma weakBisimOutputPushRes:
  fixes x :: name
  and   \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<approx> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis bisim_output_push_res strongBisimWeakBisim)

lemma weakBisimInputPushRes:
  fixes x    :: name
  and   \<Psi>    :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<approx> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis bisim_input_push_res strongBisimWeakBisim)

lemma weakBisimCasePushRes:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> (map fst Cs)"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<approx> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
using assms
by(metis bisim_case_push_res strongBisimWeakBisim)

lemma weak_bangExt:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  assumes "guarded P"

  shows "\<Psi> \<rhd> !P \<approx> P \<parallel> !P"
using assms
by(metis bang_ext strongBisimWeakBisim)

lemma weakBisimParSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<approx> R \<parallel> Q"
using assms
by(metis weakBisimParComm weakBisimParPres weakBisimTransitive)

lemma weakBisimScopeExtSym:
  fixes x :: name
  and   Q :: "('a, 'b, 'c) psi"
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<approx> (\<lparr>\<nu>x\<rparr>P) \<parallel> Q"
using assms
by(metis weakBisimScopeExt weakBisimTransitive weakBisimParComm weakBisimE weakBisimResPres)

lemma weakBisimScopeExtChainSym:
  fixes xvec :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<approx> (\<lparr>\<nu>*xvec\<rparr>P) \<parallel> Q"
using assms
by(induct xvec) (auto intro: weakBisimScopeExtSym weakBisimReflexive weakBisimTransitive weakBisimResPres)

lemma weakBisimParPresAuxSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<approx> Q"
  and     "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<approx> R \<parallel> Q"
using assms
by(metis weakBisimParComm weakBisimParPresAux weakBisimTransitive)

lemma weakBisimParPresSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<approx> R \<parallel> Q"
using assms
by(metis weakBisimParComm weakBisimParPres weakBisimTransitive)

lemma guarded_frame_stat_eq:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "extract_frame P \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrR: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
    by(rule fresh_frame)

  with `guarded P` have "\<Psi>\<^sub>P \<simeq> \<one>" and "((supp \<Psi>\<^sub>P)::name set) = {}"
    by(metis guarded_stat_eq)+
  from `supp \<Psi>\<^sub>P = {}` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>P" by(auto simp add: fresh_star_def fresh_def)
  hence "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>[], \<Psi>\<^sub>P\<rangle>" by(force intro: frame_res_fresh_chain)
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have  "\<langle>[], \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>[], \<one>\<rangle>"
    by(simp add: Frame_stat_eq_def Frame_stat_imp_def Assertion_stat_eq_def Assertion_stat_imp_def)
  ultimately show ?thesis using FrR by(rule_tac Frame_stat_eq_trans) auto
qed

lemma guardedInsertAssertion:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<Psi> :: 'b

  assumes "guarded P"

  shows "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrR: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
    by(rule fresh_frame)

  with `guarded P` have "\<Psi>\<^sub>P \<simeq> \<one>" and "((supp \<Psi>\<^sub>P)::name set) = {}"
    by(metis guarded_stat_eq)+
  from `supp \<Psi>\<^sub>P = {}` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>P" by(auto simp add: fresh_star_def fresh_def)
  hence "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>[], \<Psi> \<otimes> \<Psi>\<^sub>P\<rangle>" using `A\<^sub>P \<sharp>* \<Psi>` by(force intro: frame_res_fresh_chain)
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have  "\<langle>\<epsilon>, \<Psi> \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(force intro: composition_sym)
  moreover have "\<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>" by(force intro: Identity)
  ultimately show ?thesis using FrR `A\<^sub>P \<sharp>* \<Psi>`
    by(force intro: Frame_stat_eq_trans Assertion_stat_eq_trans)
qed

lemma insertDoubleAssertionStatEq':
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "insert_assertion(insert_assertion F \<Psi>) \<Psi>' \<simeq>\<^sub>F (insert_assertion F) (\<Psi>' \<otimes> \<Psi>)"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'" and "A\<^sub>F \<sharp>* (\<Psi>' \<otimes> \<Psi>)"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto
  thus ?thesis
    by auto (metis frame_int_associativity Frame_stat_eq_sym)
qed

lemma bangActE:
  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "guarded P"
  and     "\<alpha> \<noteq> \<tau>"
  and     "bn \<alpha> \<sharp>* P"

  obtains Q \<pi>' where "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q" and "P' \<sim> Q \<parallel> !P"
proof -
  assume "\<And>\<pi>' Q. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q; P' \<sim> Q \<parallel> !P\<rbrakk> \<Longrightarrow> thesis"
  moreover from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha> \<noteq> \<tau>` `bn \<alpha> \<sharp>* P`  have "\<exists>Q \<pi>'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
  proof(nominal_induct rule: bang_induct')
    case(c_alpha \<pi> \<alpha> P' p)
    then obtain \<pi>' Q where "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q" and "P' \<sim> Q \<parallel> (P \<parallel> !P)" by fastforce
    from `\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q` have "distinct(bn \<alpha>)" by(rule bound_output_distinct)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from `\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    have "bn(p \<bullet> \<alpha>) \<sharp>* Q" by(force dest: free_fresh_chain_derivative)
    with `\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` S `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> Q)"
      by(fastforce simp add: residual_alpha)
    moreover from `P' \<sim> Q \<parallel> (P \<parallel> !P)` have "(p \<bullet> \<one>) \<rhd> (p \<bullet> P') \<sim> (p \<bullet> (Q \<parallel> (P \<parallel> !P)))"
      by(rule bisim_closed)
    with `(bn \<alpha>) \<sharp>* P` `bn(p \<bullet> \<alpha>) \<sharp>* P` S have "(p \<bullet> P') \<sim> (p \<bullet> Q) \<parallel> (P \<parallel> !P)"
      by(simp add: eqvts)
    ultimately show ?case by blast
  next
    case(c_par1 \<pi> \<alpha> P')
    from `guarded P` have "P' \<parallel> !P \<sim> P' \<parallel> (P \<parallel> !P)" by(metis bang_ext bisim_par_pres_sym)
    with `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` show ?case by blast
  next
    case(c_par2 \<pi> \<alpha> P')
    then obtain Q \<pi>' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q" and "P' \<sim> Q \<parallel> !P" by blast
    from `P' \<sim> Q \<parallel> !P` have "P \<parallel> P' \<sim> Q \<parallel> (P \<parallel> !P)"
      by(metis bisim_par_pres_sym bisim_par_assoc bisim_transitive bisim_par_comm)
    with PTrans show ?case by blast
  next
    case c_comm1
    from `\<tau> \<noteq> \<tau>` have False by simp
    thus ?case by simp
  next
    case c_comm2
    from `\<tau> \<noteq> \<tau>` have False by simp
    thus ?case by simp
  next
    case(c_bang \<pi> \<alpha> P')
    then obtain Q \<pi>' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q" and "P' \<sim> Q \<parallel> (P \<parallel> !P)" by blast
    from `P' \<sim> Q \<parallel> (P \<parallel> !P)` `guarded P` have "P' \<sim> Q \<parallel> !P" by(metis bisim_transitive bisim_par_pres_sym bang_ext bisim_symmetric)
    with PTrans show ?case by blast
  qed
  ultimately show ?thesis by blast
qed

lemma bangTauE:
  assumes "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P'"
  and     "guarded P"

  obtains Q where "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> Q" and "P' \<sim> Q \<parallel> !P"
using assms
proof -
  assume "\<And>Q. \<lbrakk>\<Psi> \<rhd> P \<parallel> P\<longmapsto>None @ \<tau> \<prec> Q; P' \<sim> Q \<parallel> !P\<rbrakk> \<Longrightarrow> thesis"
  moreover from assms have "\<exists>Q. \<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
  proof(nominal_induct rule: bang_tau_induct)
    case(c_par1 P')
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P"
      by(rule_tac C="(\<Psi>, P)" in fresh_frame) auto
    from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(drule_tac guarded_stat_eq) auto
    with `\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'"
      thm stat_eq_transition
      by(rule_tac stat_eq_transition, auto) (metis Identity Assertion_stat_eq_sym composition_sym Assertion_stat_eq_trans)
    hence "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> P' \<parallel> P" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` by(rule_tac Par1[where \<pi>=None,simplified]) auto 
    moreover from `guarded P` have "P' \<parallel> !P \<sim> (P' \<parallel> P) \<parallel> (P \<parallel> !P)"
      by(metis bisim_par_pres_sym bisim_par_assoc bisim_transitive bisim_par_comm bang_ext)
    ultimately show ?case by blast
  next
    case(c_par2 P')
    then obtain n Q where PTrans: "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> Q" and "P' \<sim> Q \<parallel> !P" by blast
    from `P' \<sim> Q \<parallel> !P` have "P \<parallel> P' \<sim> Q \<parallel> (P \<parallel> !P)"
      by(metis bisim_par_pres_sym bisim_par_assoc bisim_transitive bisim_par_comm)
    with PTrans show ?case by blast
  next
    case(c_comm1 M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'')
    have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(drule_tac guarded_stat_eq) auto
    from `\<Psi> \<rhd> !P \<longmapsto>Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''` `guarded P` `xvec \<sharp>* P` `xvec \<sharp>* K`
    obtain Q \<pi> where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q" and "P'' \<sim> Q \<parallel> !P" 
      by(drule_tac bangActE) auto
    moreover from PTrans obtain A\<^sub>P' \<Psi>\<^sub>P' uvec M' where FrP': "extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
      and \<pi>: "\<pi> = Some(\<langle>A\<^sub>P'; uvec, M'\<rangle>)" and "distinct A\<^sub>P'" and "distinct uvec"
      and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* uvec" and M'eqK: "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> M' \<leftrightarrow> K"
      and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* M" and "A\<^sub>P' \<sharp>* K"
      and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* yvec" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* A\<^sub>P"
      and "uvec \<sharp>* Q" and "uvec \<sharp>* M" and "uvec \<sharp>* K"
      and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* P" and "uvec \<sharp>* A\<^sub>P"
      unfolding residual_inject
      by(drule_tac output_provenance[where C="(\<Psi>,Q, K, M, xvec, yvec, A\<^sub>P)"]) auto    
    from `guarded P` FrP' have "\<Psi>\<^sub>P' \<simeq> \<one>" by(drule_tac guarded_stat_eq) auto
    from `A\<^sub>P \<sharp>* P` `A\<^sub>P' \<sharp>* A\<^sub>P` FrP' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain)
    from `yvec \<sharp>* P` `A\<^sub>P' \<sharp>* yvec` FrP' have "yvec \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain)
    from `A\<^sub>P \<sharp>* P` PTrans have "A\<^sub>P \<sharp>* \<pi>" by(rule_tac trans_fresh_provenance)
    hence "A\<^sub>P \<sharp>* M'" using `uvec \<sharp>* A\<^sub>P` `A\<^sub>P' \<sharp>* A\<^sub>P` unfolding \<pi>
      by (simp add: frame_chain_fresh_chain'')
    from `yvec \<sharp>* P` PTrans have "yvec \<sharp>* \<pi>" by(rule_tac trans_fresh_provenance)
    hence "yvec \<sharp>* M'" using `uvec \<sharp>* yvec` `A\<^sub>P' \<sharp>* yvec` unfolding \<pi>
      by (simp add: frame_chain_fresh_chain'')
    from `uvec \<sharp>* P` `A\<^sub>P' \<sharp>* uvec` FrP' have "uvec \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain) 
    have M'eqK': "\<Psi> \<otimes> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>P \<turnstile> M' \<leftrightarrow> K" using `\<Psi>\<^sub>P \<simeq> \<one>`
      by (meson Assertion_stat_eq_def Associativity Identity M'eqK assertion.composition_sym assertion_axioms stat_imp_ent)
    from `\<Psi>\<^sub>P' \<simeq> \<one>` `\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'` have "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
      by(rule_tac stat_eq_transition, auto) (metis Identity Assertion_stat_eq_sym composition_sym Assertion_stat_eq_trans)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M'\<lparr>N\<rparr> \<prec> P'" using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` M'eqK'
      Frame_stat_imp_refl `distinct A\<^sub>P` `A\<^sub>P' \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M'`
       `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `distinct yvec` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* \<Psi>\<^sub>P'` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* M'`
       `yvec \<sharp>* P` `A\<^sub>P' \<sharp>* yvec`
      by(rule_tac comm2_aux[where A\<^sub>P="A\<^sub>P'"]) (assumption|simp)+
    moreover from PTrans `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q"
      by(rule_tac stat_eq_transition, auto) (metis Identity Assertion_stat_eq_sym composition_sym Assertion_stat_eq_trans)
    ultimately have "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q)" using FrP FrP' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `A\<^sub>P' \<sharp>* A\<^sub>P` `xvec \<sharp>* P`
      unfolding \<pi> using `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* P` `uvec \<sharp>* \<Psi>` `uvec \<sharp>* P` `uvec \<sharp>* \<Psi>\<^sub>P'`
      by(rule_tac Comm1) (assumption | simp)+
    moreover from `P'' \<sim> Q \<parallel> !P` `guarded P` have "P' \<parallel> P'' \<sim> (P' \<parallel> Q) \<parallel> (P \<parallel> !P)"
      by(metis bisim_transitive bang_ext bisim_par_pres_sym bisim_par_assoc bisim_symmetric)
    hence "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> (P \<parallel> !P))" by(rule_tac bisim_res_chain_pres) auto
    with `xvec \<sharp>* P` `xvec \<sharp>* \<Psi>` have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q)) \<parallel> (P \<parallel> !P)"
      by(force intro: bisim_transitive bisim_scope_ext_chain_sym)
    ultimately show ?case by blast
  next
    case(c_comm2 M xvec N P' K A\<^sub>P \<Psi>\<^sub>P yvec zvec P'')
    have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(drule_tac guarded_stat_eq) auto
    from `\<Psi> \<rhd> !P \<longmapsto>_ @ _ \<prec> P''` `guarded P` `xvec \<sharp>* P` `xvec \<sharp>* K`
    obtain Q \<pi> where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ K\<lparr>N\<rparr> \<prec> Q" and "P'' \<sim> Q \<parallel> !P" 
      by(drule_tac bangActE) auto
    moreover from PTrans obtain A\<^sub>P' \<Psi>\<^sub>P' uvec M' where FrP': "extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
      and \<pi>: "\<pi> = Some(\<langle>A\<^sub>P'; uvec, M'\<rangle>)" and "distinct A\<^sub>P'" and "distinct uvec"
      and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* uvec" and M'eqK: "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> K \<leftrightarrow> M'"
      and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* M" and "A\<^sub>P' \<sharp>* K"
      and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* yvec" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* A\<^sub>P"
      and "uvec \<sharp>* Q" and "uvec \<sharp>* M" and "uvec \<sharp>* K"
      and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* P" and "uvec \<sharp>* A\<^sub>P"
      by(drule_tac input_provenance[where C="(\<Psi>,Q, K, M, xvec, yvec, A\<^sub>P)"]) auto    
    from `guarded P` FrP' have "\<Psi>\<^sub>P' \<simeq> \<one>" by(drule_tac guarded_stat_eq) auto
    from `A\<^sub>P \<sharp>* P` `A\<^sub>P' \<sharp>* A\<^sub>P` FrP' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain)
    from `yvec \<sharp>* P` `A\<^sub>P' \<sharp>* yvec` FrP' have "yvec \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain)
    from `A\<^sub>P \<sharp>* P` PTrans have "A\<^sub>P \<sharp>* \<pi>" by(rule_tac trans_fresh_provenance)
    hence "A\<^sub>P \<sharp>* M'" using `uvec \<sharp>* A\<^sub>P` `A\<^sub>P' \<sharp>* A\<^sub>P` unfolding \<pi>
      by (simp add: frame_chain_fresh_chain'')
    from `yvec \<sharp>* P` PTrans have "yvec \<sharp>* \<pi>" by(rule_tac trans_fresh_provenance)
    hence "yvec \<sharp>* M'" using `uvec \<sharp>* yvec` `A\<^sub>P' \<sharp>* yvec` unfolding \<pi>
      by (simp add: frame_chain_fresh_chain'')
    from `uvec \<sharp>* P` `A\<^sub>P' \<sharp>* uvec` FrP' have "uvec \<sharp>* \<Psi>\<^sub>P'" by(auto dest: extract_frame_fresh_chain) 
    have M'eqK': "\<Psi> \<otimes> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M'" using M'eqK `\<Psi>\<^sub>P \<simeq> \<one>` `\<Psi>\<^sub>P' \<simeq> \<one>`
      by (metis Assertion_stat_eq_def Assertion_stat_eq_trans Assertion_stat_imp_def Composition' Identity)
    from `\<Psi>\<^sub>P' \<simeq> \<one>` `\<Psi> \<rhd> P \<longmapsto>_ @ _ \<prec> P'` have "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      by(rule_tac stat_eq_transition, auto) (metis Identity Assertion_stat_eq_sym composition_sym Assertion_stat_eq_trans)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` M'eqK'
      Frame_stat_imp_refl `distinct A\<^sub>P` `A\<^sub>P' \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M'`
       `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `distinct yvec` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* \<Psi>\<^sub>P'` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* M'`
       `yvec \<sharp>* P` `A\<^sub>P' \<sharp>* yvec`
      by(rule_tac comm1_aux[where A\<^sub>P="A\<^sub>P'"]) (assumption|simp)+
    moreover from PTrans `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>\<pi> @ K\<lparr>N\<rparr> \<prec> Q"
      by(rule_tac stat_eq_transition, auto) (metis Identity Assertion_stat_eq_sym composition_sym Assertion_stat_eq_trans)
    ultimately have "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q)" using FrP FrP' `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `A\<^sub>P' \<sharp>* A\<^sub>P` `xvec \<sharp>* P`
      unfolding \<pi> using `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* P` `uvec \<sharp>* \<Psi>` `uvec \<sharp>* P` `uvec \<sharp>* \<Psi>\<^sub>P'`
      by(rule_tac Comm2) (assumption | simp)+
    moreover from `P'' \<sim> Q \<parallel> !P` `guarded P` have "P' \<parallel> P'' \<sim> (P' \<parallel> Q) \<parallel> (P \<parallel> !P)"
      by(metis bisim_transitive bang_ext bisim_par_pres_sym bisim_par_assoc bisim_symmetric)
    hence "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> (P \<parallel> !P))" by(rule_tac bisim_res_chain_pres) auto
    with `xvec \<sharp>* P` `xvec \<sharp>* \<Psi>` have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q)) \<parallel> (P \<parallel> !P)"
      by(force intro: bisim_transitive bisim_scope_ext_chain_sym)
    ultimately show ?case by blast
  next
    case(c_bang P')
    then obtain Q where PTrans: "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> Q" and "P' \<sim> Q \<parallel> (P \<parallel> !P)" by blast
    from `P' \<sim> Q \<parallel> (P \<parallel> !P)` `guarded P` have "P' \<sim> Q \<parallel> !P" by(metis bisim_transitive bisim_par_pres_sym bang_ext bisim_symmetric)
    with PTrans show ?case by blast
  qed
  ultimately show ?thesis by blast
qed

lemma tauBangI:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> P'"
  and     "guarded P"

  obtains Q where "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> Q" and "Q \<sim> P' \<parallel> !P"
proof -
  assume "\<And>Q. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> Q; Q \<sim> P' \<parallel> !P\<rbrakk> \<Longrightarrow> thesis"
  moreover from `\<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> P'` have "\<exists>Q. \<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> Q \<and> Q \<sim> P' \<parallel> !P"
  proof(induct rule: parTauCases[where C="()"])
    case(c_par1 P' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'" 
      by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P' \<parallel> !P" by(rule_tac Par1[where \<pi>=None,simplified]) auto
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P' \<parallel> !P" using `guarded P` by(rule Bang[where \<pi>=None,simplified])
     hence "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P \<parallel> (P' \<parallel> !P)" using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
       by(rule_tac Par2[where \<pi>=None,simplified]) auto
     hence "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P \<parallel> (P' \<parallel> !P)" using `guarded P` by(rule Bang[where \<pi>=None,simplified])
     moreover have "P \<parallel> (P' \<parallel> !P) \<sim> P' \<parallel> P \<parallel> !P"
       by(metis bisim_par_assoc bisim_par_comm bisim_transitive bisim_symmetric bisim_par_pres)
     ultimately show ?case by blast
   next
    case(c_par2 P' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'" 
      by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P' \<parallel> !P" by(rule_tac Par1[where \<pi>=None, simplified]) auto
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P' \<parallel> !P" using `guarded P` by(rule Bang[where \<pi>=None, simplified])
     hence "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P \<parallel> (P' \<parallel> !P)" using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
       by(rule_tac Par2[where \<pi>=None, simplified]) auto
     hence "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P \<parallel> (P' \<parallel> !P)" using `guarded P` by(rule Bang[where \<pi>=None, simplified])
     moreover have "P \<parallel> (P' \<parallel> !P) \<sim> P \<parallel> P' \<parallel> !P"
       by(metis bisim_par_assoc bisim_symmetric)
     ultimately show ?case by blast
   next
     case(c_comm1 \<Psi>\<^sub>P' M N P' A\<^sub>P \<Psi>\<^sub>P K xvec P'' A\<^sub>P' yvec zvec)
     from `extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>` `guarded P` have "\<Psi>\<^sub>P' \<simeq> \<one>" by(blast dest: guarded_stat_eq)
     with `\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>_ @ M\<lparr>N\<rparr> \<prec> P'` have "\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
       by(rule_tac stat_eq_transition, auto) (metis composition_sym Assertion_stat_eq_sym)
     moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
     moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>_ @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P'; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
       by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<parallel> !P \<longmapsto>Some (\<langle>A\<^sub>P'; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P'' \<parallel> !P)" using `xvec \<sharp>* P`
       by(force intro: Par1[where A\<^sub>Q="[]" and Q="!P",simplified,unfolded map_option.id[unfolded id_def]])
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !P \<longmapsto>Some (\<langle>\<epsilon>, \<langle>(A\<^sub>P' @ zvec), M\<rangle>\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P'' \<parallel> !P)" using `guarded P`
       by(rule Bang[where \<pi>="Some (\<langle>A\<^sub>P'; zvec, M\<rangle>)",simplified])
     ultimately have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P))"
       using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>P'` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `xvec \<sharp>* P`
             `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P`
       by(force intro: Comm1[where Q="!P" and A\<^sub>Q="[]",simplified])
     hence "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P))" using `guarded P` by(rule Bang[where \<pi>=None,simplified])
     moreover have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P)) \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')) \<parallel> !P" 
     proof -
       have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> P'') \<parallel> !P)"
         by(force intro: bisim_res_chain_pres bisim_par_assoc[THEN bisim_symmetric])
       moreover have "\<lparr>\<nu>*xvec\<rparr>((P' \<parallel> P'') \<parallel> !P) \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')) \<parallel> !P" using `xvec \<sharp>* P`
         by(rule_tac bisim_scope_ext_chain_sym) auto
       ultimately show ?thesis by(rule bisim_transitive)
     qed
     ultimately show ?case by blast
   next
     case(c_comm2 \<Psi>\<^sub>P' M xvec N P' A\<^sub>P \<Psi>\<^sub>P K P'' A\<^sub>P' yvec zvec)
     from `extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>` `guarded P` have "\<Psi>\<^sub>P' \<simeq> \<one>" by(blast dest: guarded_stat_eq)
     with `\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> P \<longmapsto>_ @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<prec> P'` have "\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
       by(rule_tac stat_eq_transition, auto) (metis composition_sym Assertion_stat_eq_sym)
     moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
     moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<longmapsto>_ @ K\<lparr>N\<rparr> \<prec> P''` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P'; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> P''"
       by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> P \<parallel> !P \<longmapsto>Some (\<langle>A\<^sub>P'; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> (P'' \<parallel> !P)"
       by(force intro: Par1[where A\<^sub>Q="[]" and Q="!P",simplified,unfolded map_option.id[unfolded id_def]])
     hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !P \<longmapsto>Some (\<langle>\<epsilon>, \<langle>(A\<^sub>P' @ zvec), M\<rangle>\<rangle>) @ K\<lparr>N\<rparr> \<prec> (P'' \<parallel> !P)" using `guarded P`
       by(rule Bang[where \<pi>="Some (\<langle>A\<^sub>P'; zvec, M\<rangle>)",simplified])
     ultimately have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P))"
       using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>P'` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* P` `A\<^sub>P' \<sharp>* K` `xvec \<sharp>* P`
             `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P`
       by(force intro: Comm2[where Q="!P" and A\<^sub>Q="[]",simplified])
     hence "\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P))" using `guarded P` by(rule Bang[where \<pi>=None,simplified])
     moreover have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P)) \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')) \<parallel> !P" 
     proof -
       have "\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (P'' \<parallel> !P)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> P'') \<parallel> !P)"
         by(force intro: bisim_res_chain_pres bisim_par_assoc[THEN bisim_symmetric])
       moreover have "\<lparr>\<nu>*xvec\<rparr>((P' \<parallel> P'') \<parallel> !P) \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')) \<parallel> !P" using `xvec \<sharp>* P`
         by(rule_tac bisim_scope_ext_chain_sym) auto
       ultimately show ?thesis by(rule bisim_transitive)
     qed
     ultimately show ?case by blast
   qed
   ultimately show ?thesis by blast
qed

lemma tauChainBangI:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "guarded P"

  obtains Q where "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" and "\<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
proof -
  assume "\<And>Q. \<lbrakk>\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q; \<Psi> \<rhd> Q \<sim> P' \<parallel> !P\<rbrakk> \<Longrightarrow> thesis"
  moreover from `\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'` have "\<exists>Q. \<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q \<and> \<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
  proof(induct x1=="P \<parallel> P" P' rule: tau_chain_induct)
    case tau_base
    have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> !P" by simp
    moreover have "\<Psi> \<rhd> !P \<sim> (P \<parallel> P) \<parallel> !P" using `guarded P`
      by(metis bisim_par_assoc bisim_transitive bisim_par_pres_sym bang_ext bisim_par_comm)
    ultimately show ?case by blast
  next
    case(tau_step R' R'')
    then obtain Q where PChain: "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" and "\<Psi> \<rhd> Q \<sim> R' \<parallel> !P" by auto
    from `\<Psi> \<rhd> R' \<longmapsto>None @ \<tau> \<prec> R''` have "\<Psi> \<otimes> \<one> \<rhd> R' \<longmapsto>None @ \<tau> \<prec> R''" by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
    hence "\<Psi> \<rhd> R' \<parallel> !P \<longmapsto>None @ \<tau> \<prec> R'' \<parallel> !P" by(rule_tac Par1[where \<pi>=None,simplified]) auto
    with `\<Psi> \<rhd> Q \<sim> R' \<parallel> !P` obtain Q' \<pi> where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<tau> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> R'' \<parallel> !P"
      by(force dest: bisimE(2) simE) 
    from PChain tau_no_provenance'[OF QTrans] have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" by(auto dest: tau_act_tau_chain)
    thus ?case using `\<Psi> \<rhd> Q' \<sim> R'' \<parallel> !P` by blast
  qed
  ultimately show ?thesis by blast
qed

lemma weakBisimBangPresAux:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx> Q"
  and     "guarded P"
  and     "guarded Q"

  shows   "\<Psi> \<rhd> R \<parallel> !P \<approx> R \<parallel> !Q"
proof -
  let ?X = "{(\<Psi>, R \<parallel> !P, R \<parallel> !Q) | \<Psi> R P Q. guarded P \<and> guarded Q \<and> \<Psi> \<rhd> P \<approx> Q}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>R S. \<Psi> \<rhd> P \<approx> R \<and> (\<Psi>, R, S) \<in> ?X \<and> \<Psi> \<rhd> S \<sim> Q}"

  from assms have "(\<Psi>, R \<parallel> !P, R \<parallel> !Q) \<in> ?X" by auto
  moreover have "eqvt ?X"
    by(fastforce simp add: eqvt_def intro: weakBisimClosed)
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct2)
    case(cStatImp \<Psi> P Q)
    thus ?case by(force dest: weakBisimE(3) simp add: weak_stat_imp_def)
  next
    case(cSim \<Psi> P Q)
    moreover {
      fix \<Psi> P Q R
      assume "\<Psi> \<rhd> P \<approx> Q"
      moreover have "eqvt ?Y" 
        apply(auto simp add: eqvt_def)
        apply(rule_tac x="p \<bullet> (Ra \<parallel> !P)" in exI, auto)
        apply(fastforce dest: weakBisimClosed simp add: eqvts)
        apply(rule_tac x="(p \<bullet> Ra) \<parallel> !(p \<bullet> Q)" in exI, auto)
        apply(rule_tac x="p \<bullet> Ra" in exI)
        apply(rule_tac x="p \<bullet> P" in exI, auto)
        apply(rule_tac x="p \<bullet> Q" in exI, auto)
        apply(blast intro: weakBisimClosed)
        by(fastforce dest: bisim_closed simp add: eqvts)
      moreover assume "guarded P" and "guarded Q" 
      moreover note weakBisimClosed bisim_closed weakBisimE(3) bisimE(3) weakBisimE(2) weakBisimE(4) bisimE(4) statEqWeakBisim stat_eq_bisim weakBisimTransitive bisim_transitive weakBisimParAssoc[THEN weakBisimE(4)] bisim_par_assoc[THEN bisimE(4)] weakBisimParPres 
      moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<approx> Q \<Longrightarrow> \<Psi> \<rhd> P \<parallel> P \<approx> Q \<parallel> Q"
        by(metis weakBisimParPres weakBisimParComm weakBisimE(4) weakBisimTransitive)
      moreover note bisim_par_pres_sym
      moreover have "bisim \<subseteq> weakBisim" by(auto dest: strongBisimWeakBisim)
      moreover have "\<And>\<Psi> \<Psi>\<^sub>R P Q R A\<^sub>R. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<approx> Q; extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> R \<parallel> P \<approx> R \<parallel> Q"
        by(metis weakBisimParComm weakBisimTransitive weakBisimParPresAux)
      moreover note weakBisimResChainPres bisim_res_chain_pres weakBisimScopeExtChainSym bisim_scope_ext_chain_sym
      moreover have "\<And>\<Psi> P R S Q. \<lbrakk>\<Psi> \<rhd> P \<approx> R; (\<Psi>, R, S) \<in> ?Y; \<Psi> \<rhd> S \<sim> Q\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> ?Y"
        by(blast dest: weakBisimTransitive bisim_transitive)
      moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<approx> Q; guarded P; guarded Q\<rbrakk> \<Longrightarrow> (\<Psi>, R \<parallel> !P, R \<parallel> !Q) \<in> ?Y"
        by(blast intro: bisim_reflexive weakBisimReflexive)
      moreover from bangActE have "\<And>\<Psi> P \<alpha> \<pi> P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* P; guarded P; \<alpha> \<noteq> \<tau>; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow> \<exists>Q \<pi>'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
        by blast
      moreover from bangTauE have "\<And>\<Psi> P P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P'; guarded P\<rbrakk> \<Longrightarrow> \<exists>Q. \<Psi> \<rhd> P \<parallel> P \<longmapsto>None @ \<tau> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
        by blast
      moreover from tauChainBangI have "\<And>\<Psi> P P'. \<lbrakk>\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; guarded P\<rbrakk> \<Longrightarrow> \<exists>Q. \<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q \<and> \<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
        by blast
      ultimately have  "\<Psi> \<rhd> R \<parallel> !P \<leadsto><?Y> R \<parallel> !Q" 
        by(rule_tac weakSimBangPres)
        
    }
    ultimately show ?case by blast
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: weakBisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: weakBisimE)
  qed
qed


lemma weakBisimBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<approx> Q"
  and     "guarded P"
  and     "guarded Q"

  shows   "\<Psi> \<rhd> !P \<approx> !Q"
proof -
  from assms have "\<Psi> \<rhd> \<zero> \<parallel> !P \<approx> \<zero> \<parallel> !Q" by(rule weakBisimBangPresAux)
  thus ?thesis
    by(metis weakBisimParNil weakBisimParComm weakBisimTransitive weakBisimE(4))
qed

end

end

