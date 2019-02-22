(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Stat_Imp
  imports Tau_Chain
begin

context env begin

definition
  "weak_stat_imp" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                     ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                     ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<lessapprox><_> _" [80, 80, 80, 80] 80)
where "\<Psi> \<rhd> P \<lessapprox><Rel> Q \<equiv> \<forall>\<Psi>'. \<exists>Q' Q''. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> \<and> \<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'' \<and> (\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"

lemma weak_stat_impMonotonic:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<lessapprox><A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<lessapprox><B> Q"
using assms
by(auto simp add: weak_stat_imp_def) blast

lemma weak_stat_impI[case_names cStatImp]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<And>\<Psi>'. \<exists>Q' Q''. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> \<and> \<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'' \<and> (\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
using assms
by(auto simp add: weak_stat_imp_def)

lemma weak_stat_impE:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<lessapprox><Rel> Q"

  obtains Q' Q'' where "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> " and "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"

using assms
by(auto simp add: weak_stat_imp_def) blast

lemma weak_stat_impClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PStatImpQ: "\<Psi> \<rhd> P \<lessapprox><Rel> Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<lessapprox><Rel> (p \<bullet> Q)"
proof(induct rule: weak_stat_impI)
  case(cStatImp \<Psi>')
  from PStatImpQ obtain Q' Q'' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                                 and PimpQ': "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q') \<Psi>"
                                 and Q'Chain: "\<Psi> \<otimes> (rev(p::name prm) \<bullet> \<Psi>') \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> (rev p \<bullet> \<Psi>'), P,  Q'') \<in> Rel"
    by(rule weak_stat_impE)
  from QChain have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> Q')" by(rule tau_chain_eqvt)
  moreover from PimpQ' have "insert_assertion (extract_frame (p \<bullet> P)) (p \<bullet> \<Psi>) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(p \<bullet> Q')) (p \<bullet> \<Psi>)"
    by(drule_tac p=p in Frame_stat_imp_closed) (simp add: eqvts)
  moreover from Q'Chain have "(p \<bullet> \<Psi>) \<otimes> \<Psi>' \<rhd> (p \<bullet> Q') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> Q'')" by(drule_tac p=p in tau_chain_eqvt) (simp add: eqvts)
  moreover from `(\<Psi> \<otimes> (rev p \<bullet> \<Psi>'), P, Q'') \<in> Rel` EqvtRel have "((p \<bullet> \<Psi>) \<otimes> \<Psi>', (p \<bullet> P), (p \<bullet> Q'')) \<in> Rel"
    by(drule_tac p=p in eqvtI) (auto simp add: eqvts)
  ultimately show ?case
    by blast
qed

lemma weak_stat_impReflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel> P"
using assms
by(auto simp add: weak_stat_imp_def weak_transition_def dest: rtrancl_into_rtrancl) force+

lemma weak_stat_impTransitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PStatImpQ: "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     QRelR: "(\<Psi>, Q, R) \<in> Rel'"
  and     Set: "{(\<Psi>', S, U) | \<Psi>' S U. \<exists>T. (\<Psi>', S, T) \<in> Rel \<and> (\<Psi>', T, U) \<in> Rel'} \<subseteq> Rel''"
  and     C1: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> \<Psi>' \<rhd> S \<lessapprox><Rel'> T"
  and     C2: "\<And>\<Psi>' S T S'. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; \<Psi>' \<rhd> S \<Longrightarrow>\<^sup>^\<^sub>\<tau> S'\<rbrakk> \<Longrightarrow> \<exists>T'. \<Psi>' \<rhd> T \<Longrightarrow>\<^sup>^\<^sub>\<tau> T' \<and> (\<Psi>', S', T') \<in> Rel'"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel''> R"
proof(induct rule: weak_stat_impI)
  case(cStatImp \<Psi>')
  from `\<Psi> \<rhd> P \<lessapprox><Rel> Q` obtain Q' Q'' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                                         and PimpQ': "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q') \<Psi>"
                                         and Q'Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"
    by(rule weak_stat_impE)
  from QChain `(\<Psi>, Q, R) \<in> Rel'` obtain R' where RChain: "\<Psi> \<rhd> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> R'" and "(\<Psi>, Q', R') \<in> Rel'"
    by(metis C2)
  from `(\<Psi>, Q', R') \<in> Rel'` obtain R'' R''' where R'Chain: "\<Psi> \<rhd> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> R''"
                                              and Q'impR'': "insert_assertion (extract_frame Q') \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame R'') \<Psi>"
                                              and R''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> R'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> R'''" and "(\<Psi> \<otimes> \<Psi>', Q', R''') \<in> Rel'"
    by(blast dest: C1 weak_stat_impE)
  from RChain R'Chain have "\<Psi> \<rhd> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> R''" by auto
  moreover from PimpQ' Q'impR'' have "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame R'') \<Psi>"
    by(rule Frame_stat_imp_trans)
  moreover from Q'Chain `(\<Psi> \<otimes> \<Psi>', Q',  R''') \<in> Rel'` obtain R'''' where R'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> R''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> R''''" and "(\<Psi> \<otimes> \<Psi>', Q'', R'''') \<in> Rel'"
    by(metis C2)
  from R''Chain R'''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> R'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> R''''" by auto
  moreover from `(\<Psi> \<otimes> \<Psi>', P,  Q'') \<in> Rel` `(\<Psi> \<otimes> \<Psi>', Q'', R'''') \<in> Rel'` Set have "(\<Psi> \<otimes> \<Psi>', P, R'''') \<in> Rel''" by blast
  ultimately show ?case
    by blast
qed

lemma weak_stat_impStatEq:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<lessapprox><Rel'> Q"
proof(induct rule: weak_stat_impI)
  case(cStatImp \<Psi>'')
  from `\<Psi> \<rhd> P \<lessapprox><Rel> Q` obtain Q' Q'' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                                         and PimpQ: "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q') \<Psi>"
                                         and Q'Chain: "\<Psi> \<otimes> \<Psi>'' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> \<Psi>'', P, Q'') \<in> Rel"
    by(rule weak_stat_impE)
  from QChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" by(rule tau_chain_stat_eq)
  moreover from PimpQ `\<Psi> \<simeq> \<Psi>'` have "insert_assertion (extract_frame P) \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q') \<Psi>'"
    by(rule insert_assertionStatImp)
  moreover from Q'Chain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<otimes> \<Psi>'' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" by(metis tau_chain_stat_eq Composition)
  moreover from `(\<Psi> \<otimes> \<Psi>'', P, Q'') \<in> Rel` `\<Psi> \<simeq> \<Psi>'`  have "(\<Psi>' \<otimes> \<Psi>'', P, Q'') \<in> Rel'" by(blast intro: Composition C1)
  ultimately show ?case
    by blast
qed

lemma statImpWeakStatImp:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PImpQ: "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q) \<Psi>"
  and     C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
proof(induct rule: weak_stat_impI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" by simp
  moreover note PImpQ
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" by simp
  moreover have "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule C1)
  ultimately show ?case
    by blast
qed

end

end
