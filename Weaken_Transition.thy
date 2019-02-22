(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weaken_Transition
  imports Weakening
begin

context weak
begin

definition weakenTransition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>_ @ _ \<prec> _" [80, 80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P' \<equiv> (\<exists>P''' P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''' \<and> \<Psi> \<rhd> P''' \<longmapsto>\<pi> @ \<alpha> \<prec> P'' \<and> \<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P') \<or> (P = P' \<and> \<alpha> = \<tau>)"

lemma weakenTransitionCases[consumes 1, case_names cBase cStep]:
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and "Prop (\<tau>) \<pi> P"
  and "\<And>P''' P''. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''; \<Psi> \<rhd> P''' \<longmapsto>\<pi> @ \<alpha> \<prec> P''; \<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> Prop \<alpha> \<pi> P'"

  shows "Prop \<alpha> \<pi> P'"
using assms
by(auto simp add: weakenTransition_def)

lemma statImpTauChainDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  shows "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P') \<Psi>"
using assms
by(induct rule: tau_chain_induct) (auto intro: statImpTauDerivative dest: Frame_stat_imp_trans)

lemma weakenTauChain:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  shows "\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms
proof(induct rule: tau_chain_induct)
  case(tau_base P)
  thus ?case by simp
next
  case(tau_step P P' P'')
  note `\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'`
  moreover from `\<Psi> \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''` have "\<Psi> \<otimes> \<Psi>' \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''" by(rule weakenTransition)
  ultimately show ?case by(auto dest: tau_act_tau_chain)
qed

end

end
