(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weaken_Simulation
  imports Weaken_Stat_Imp
begin

context weak
begin

definition
  "weakenSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                         ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                         ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>\<^sub>w<_> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>\<^sub>w<Rel> Q \<equiv> \<forall>\<alpha> \<pi> Q'. \<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> (\<exists>P' \<pi>'. \<Psi> \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel)"

lemma weakenSimI[case_names c_act]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes rOutput: "\<And>\<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P\<rbrakk> \<Longrightarrow>
                             \<exists>P' \<pi>'. \<Psi> \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
                                             
  shows "\<Psi> \<rhd> P \<leadsto>\<^sub>w<Rel> Q"
using assms
by(auto simp add: weakenSimulation_def)

lemma weaken_transition_tau_no_provenance:
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<pi> @ \<tau> \<prec> P'"
  shows "\<Psi> \<rhd> P \<Longrightarrow>None @ \<tau> \<prec> P'"
  using assms
  by(auto simp add: weakenTransition_def dest: tau_no_provenance')

lemma weakenSimWeakSim:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     cStatImp: "\<And>\<Psi>' R S. (\<Psi>, R, S) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> R \<lessapprox>\<^sub>w<Rel> S"
  and     cSim: "\<And>\<Psi>' R S. (\<Psi>, R, S) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> R \<leadsto>\<^sub>w<Rel'> S"
  and     cExt: "\<And>\<Psi>' R S \<Psi>'. (\<Psi>, R, S) \<in> Rel' \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', R, S) \<in> Rel'"
  and     cSym: "\<And>\<Psi>' R S. (\<Psi>, R, S) \<in> Rel \<Longrightarrow> (\<Psi>, S, R) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel'> Q"
proof(induct rule: weakSimI2)
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  from `(\<Psi>, P, Q) \<in> Rel` obtain P''''
    where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" 
      and QImpP'''': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'''') \<Psi>"
      and "(\<Psi>, P'''', Q) \<in> Rel" using weakenStatImp_def
    by(metis cStatImp cSym)
    
  from `(\<Psi>, P'''', Q) \<in> Rel` have "\<Psi> \<rhd> P'''' \<leadsto>\<^sub>w<Rel'> Q" by(rule cSim)
  moreover from PChain `bn \<alpha> \<sharp>* P` have "bn \<alpha> \<sharp>* P''''" by(rule tau_chain_fresh_chain)
  ultimately obtain P' \<pi>' where P''''Trans: "\<Psi> \<rhd> P'''' \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'" and "(\<Psi>, P', Q') \<in> Rel'"
    using `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>`
    by(unfold weakenSimulation_def, force)

  from P''''Trans `\<alpha> \<noteq> \<tau>` obtain P''' P'' where P''''Chain: "\<Psi> \<rhd> P'''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" and P'''Trans: "\<Psi> \<rhd> P''' \<longmapsto>\<pi>' @ \<alpha> \<prec> P''" and P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" 
    by(force simp add: weakenTransition_def)
  from P''''Chain QImpP'''' have "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P''') \<Psi>"
    by(blast intro: statImpTauChainDerivative Frame_stat_imp_trans)
  with PChain P''''Chain have "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" using P'''Trans by(rule_tac weak_transitionI) auto
  moreover from P''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule weakenTauChain) 
  moreover from `(\<Psi>, P', Q') \<in> Rel'` have "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel'" by(rule cExt)
  ultimately show ?case by blast
next
  case(c_tau Q')
  from `(\<Psi>, P, Q) \<in> Rel` have "\<Psi> \<rhd> P \<leadsto>\<^sub>w<Rel'> Q" by(rule cSim)
  then obtain P' \<pi> where "\<Psi> \<rhd> P \<Longrightarrow>\<pi> @ \<tau> \<prec> P'" and "(\<Psi>, P', Q') \<in> Rel'" using `\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'`
    by(unfold weakenSimulation_def, fastforce)
  from weaken_transition_tau_no_provenance[OF `\<Psi> \<rhd> P \<Longrightarrow>\<pi> @ \<tau> \<prec> P'`] have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
    by(auto simp add: weakenTransition_def dest: tau_act_tau_chain)
  with `(\<Psi>, P', Q') \<in> Rel'` show ?case by blast
qed

lemma weakSimWeakenSim:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes cSim: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     cStatEq: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<^sub>w<Rel> Q"
proof(induct rule: weakenSimI)
  case(c_act \<alpha> \<pi> Q')
  show ?case
  proof(cases "\<alpha>=\<tau>")
    case True
    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha> = \<tau>` 
    obtain P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: weakSimE tau_no_provenance')
    from `\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'` have "\<Psi> \<rhd> P \<Longrightarrow>None @ \<tau> \<prec> P'"
      by(induct rule: tau_chain_induct) (auto simp add: weakenTransition_def)
    thus ?thesis using `(\<Psi>, P', Q') \<in> Rel` `\<alpha> = \<tau>` by blast
  next
    case False
    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
    obtain P'' P' \<pi>' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<one> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi> \<otimes> \<one>, P', Q') \<in> Rel"
      by(blast dest: weakSimE)
    from PTrans have "\<Psi> \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" by(auto simp add: weak_transition_def weakenTransition_def)
    moreover from P''Chain have "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(metis tau_chain_stat_eq Identity)
    moreover from `(\<Psi> \<otimes> \<one>, P', Q') \<in> Rel` have "(\<Psi>, P', Q') \<in> Rel" by(metis cStatEq Identity)
    ultimately show ?thesis
    proof(induct rule: weakenTransitionCases)
      case cBase 
      from `\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'` have "\<Psi> \<rhd> P \<Longrightarrow>None @ \<tau> \<prec> P'"
        by(induct rule: tau_chain_induct) (auto simp add: weakenTransition_def)
      with `(\<Psi>, P', Q') \<in> Rel` show ?case by blast
    next
      case(cStep P'''' P''')
      thus ?case 
        apply(unfold weakenTransition_def)
        by(rule_tac x=P' in exI) fastforce
    qed
  qed
qed

lemma weakenSimE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>\<^sub>w<Rel> Q"

  shows "\<And>\<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P\<rbrakk> \<Longrightarrow> 
                   \<exists>P' \<pi>'. \<Psi> \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: weakenSimulation_def)

lemma weakenSimMonotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto>\<^sub>w<A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto>\<^sub>w<B> Q"
using assms
by(simp (no_asm) add: weakenSimulation_def) (blast dest: weakenSimE)

end

end
