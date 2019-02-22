(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weaken_Stat_Imp
  imports Weaken_Transition
begin

context weak begin

definition
  "weakenStatImp" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                     ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                     ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<lessapprox>\<^sub>w<_> _" [80, 80, 80, 80] 80)
where "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q \<equiv> \<exists>Q'. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q' \<and> insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> \<and> (\<Psi>, P, Q') \<in> Rel"

lemma weakenStatImpMonotonic:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<B> Q"
using assms
by(auto simp add: weakenStatImp_def)

lemma weakenStatImpI:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi>"
  and     "(\<Psi>, P, Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q"
using assms
by(auto simp add: weakenStatImp_def)

lemma weakenStatImpE:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q"

  obtains Q' where "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> " and "(\<Psi>, P, Q') \<in> Rel"
using assms
by(auto simp add: weakenStatImp_def)

lemma weak_stat_impWeakenStatImp:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes cSim: "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     cStatEq: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q"
proof -
  from `\<Psi> \<rhd> P \<lessapprox><Rel> Q` 
  obtain Q' Q'' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                  and PImpQ': "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi>"
                  and Q'Chain: "\<Psi> \<otimes> \<one> \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and "(\<Psi> \<otimes> \<one>, P, Q'') \<in> Rel"
    by(rule weak_stat_impE)
  from Q'Chain Identity have Q'Chain: "\<Psi> \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" by(rule tau_chain_stat_eq)
  with QChain have "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" by auto
  moreover from Q'Chain have "insert_assertion(extract_frame Q') \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q'') \<Psi>"
    by(rule statImpTauChainDerivative)
  with PImpQ' have "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q'') \<Psi>"
    by(rule Frame_stat_imp_trans)
  moreover from `(\<Psi> \<otimes> \<one>, P, Q'') \<in> Rel` Identity have "(\<Psi>, P, Q'') \<in> Rel" by(rule cStatEq)
  ultimately show ?thesis by(rule weakenStatImpI)
qed

lemma weakenStatImpWeakStatImp:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q"
  and     cExt: "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
proof(induct rule: weak_stat_impI)
  case(cStatImp \<Psi>')
     
  from `\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q` 
  obtain Q' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
              and PImpQ': "insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi>"
              and "(\<Psi>, P, Q') \<in> Rel"
    by(rule weakenStatImpE)
  note QChain PImpQ'
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" by simp
  moreover from `(\<Psi>, P, Q') \<in> Rel` have "(\<Psi> \<otimes> \<Psi>', P, Q') \<in> Rel" by(rule cExt)
  ultimately show ?case by blast
qed

end

end
