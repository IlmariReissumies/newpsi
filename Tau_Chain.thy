(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Chain
  imports Semantics
begin

context env begin

abbreviation tau_chain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sup>^\<^sub>\<tau> _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}^*"

abbreviation tau_step_chain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sub>\<tau> _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}^+"

abbreviation tau_context_chain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sup>^\<^sub>\<tau> _" [80, 80] 80)
where "P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
abbreviation tau_context_step_chain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>\<tau> _" [80, 80] 80)
where "P \<Longrightarrow>\<^sub>\<tau> P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"

lemmas tau_chain_induct[consumes 1, case_names tau_base tau_step] = rtrancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}", simplified] for \<Psi>
lemmas tau_step_chain_induct[consumes 1, case_names tau_base tau_step] = trancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}", simplified] for \<Psi>


lemma tau_act_tau_step_chain:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
using assms by auto

lemma tau_act_tau_chain:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms by(auto simp add: rtrancl_eq_or_trancl)

lemma tau_step_chainEqvt[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')"
using assms
proof(induct rule: tau_step_chain_induct)  
  case(tau_base P P')
  hence "\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'" by simp
  thus ?case by(force dest: semantics.eqvt simp add: eqvts)
next
  case(tau_step P P' P'')
  hence "\<Psi> \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''" by simp  
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P') \<longmapsto>None @ \<tau> \<prec> (p \<bullet> P'')" by(force dest: semantics.eqvt simp add: eqvts)
  with `(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')` show ?case
    by(subst trancl.trancl_into_trancl) auto
qed

lemma tau_chain_eqvt[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')"
using assms
by(auto simp add: rtrancl_eq_or_trancl eqvts)

lemma tau_step_chainEqvt'[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P')) = (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')"
apply(auto simp add: eqvts perm_set_def pt_bij[OF pt_name_inst, OF at_name_inst])
by(drule_tac p="rev p" in tau_step_chainEqvt) auto

lemma tau_chain_eqvt'[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P')) = (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')"
apply(auto simp add: eqvts perm_set_def pt_bij[OF pt_name_inst, OF at_name_inst] rtrancl_eq_or_trancl)
by(drule_tac p="rev p" in tau_step_chainEqvt) auto

lemma tau_step_chainFresh:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
using assms
by(induct rule: trancl.induct) (auto dest: tau_fresh_derivative)

lemma tau_chainFresh:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tau_step_chainFresh)

lemma tau_step_chain_fresh_chain:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tau_step_chainFresh)

lemma tau_chain_fresh_chain:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tau_chainFresh)

lemma tau_step_chain_case:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   \<phi>  :: 'c
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "(\<phi>, P) mem Cs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"

  shows "\<Psi> \<rhd> (Cases Cs) \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct rule: trancl.induct; force dest: Case intro: trancl_into_trancl)

lemma tau_step_chain_res_pres:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name  

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
by(induct rule: trancl.induct)
  (auto dest: Scope[where \<pi>=None,simplified] trancl_into_trancl)

lemma tau_chain_res_pres:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name  

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tau_step_chain_res_pres)

lemma tau_step_chainResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>P'"
using assms
by(induct xvec) (auto intro: tau_step_chain_res_pres)

lemma tau_chain_res_chain_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>P'"
using assms
by(induct xvec) (auto intro: tau_chain_res_pres)

lemma tau_step_chain_par1:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>Q :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q"
using assms
by(induct rule: trancl.induct) (auto dest: Par1[where \<pi>=None,simplified] tau_step_chain_fresh_chain trancl_into_trancl)


lemma tau_chain_par1:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>Q :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> Q"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tau_step_chain_par1)

lemma tau_step_chain_par2:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>P :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'"
using assms
by(induct rule: trancl.induct) (auto dest: Par2[where \<pi>=None,simplified] trancl_into_trancl tau_step_chain_fresh_chain)

lemma tau_chain_par2:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>P :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<parallel> Q'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tau_step_chain_par2)

lemma tau_step_chain_bang:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "guarded P"

  shows "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct x1=="P \<parallel> !P" P' rule: trancl.induct) (auto intro: Bang[where \<pi>=None,simplified] dest: trancl_into_trancl)

lemma tau_step_chain_stat_eq:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct rule: trancl.induct) (auto dest: stat_eq_transition trancl_into_trancl)

lemma tau_chain_stat_eq:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tau_step_chain_stat_eq)

definition weak_transition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>  ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ : _ \<rhd> _ \<Longrightarrow>_ @ _ \<prec> _" [80, 80, 80, 80, 80, 80] 80)
where
  "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P' \<equiv> \<exists>P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<and> (insert_assertion (extract_frame Q) \<Psi>) \<hookrightarrow>\<^sub>F (insert_assertion (extract_frame P'') \<Psi>) \<and>
                                          \<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"

lemma weak_transitionI:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   P''  :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
  and     "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
  and     "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
using assms
by(auto simp add: weak_transition_def)

lemma weak_transitionE:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"

  obtains P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                 and "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
using assms
by(auto simp add: weak_transition_def)

lemma weak_transitionClosed[eqvt]:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"

  shows "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> \<pi>) @ (p \<bullet> \<alpha>)\<prec> (p \<bullet> P')"
proof -
  from assms obtain P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)

  from `\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P'')"
    by(rule tau_chain_eqvt)
  moreover from `insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>` 
  have "(p \<bullet> (insert_assertion (extract_frame Q) \<Psi>)) \<hookrightarrow>\<^sub>F (p \<bullet> (insert_assertion (extract_frame P'') \<Psi>))"
    by(rule Frame_stat_imp_closed)
  hence "insert_assertion (extract_frame(p \<bullet> Q)) (p \<bullet> \<Psi>) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(p \<bullet> P'')) (p \<bullet> \<Psi>)" by(simp add: eqvts)
  moreover from `\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> \<pi>) @ (p \<bullet> (\<alpha> \<prec> P'))"
    by(rule semantics.eqvt)
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> \<pi>) @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> P')" by(simp add: eqvts)
  ultimately show ?thesis by(rule weak_transitionI)
qed
(*
lemma weak_transitionAlpha:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "xvec \<sharp>* (p \<bullet> xvec)"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and     "(p \<bullet> xvec) \<sharp>* N"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  note PChain qeq_p''
  moreover from PChain `(p \<bullet> xvec) \<sharp>* P` have "(p \<bullet> xvec) \<sharp>* P''" by(rule tau_chain_fresh_chain)
  with P''Trans `xvec \<sharp>* (p \<bullet> xvec)` `(p \<bullet> xvec) \<sharp>* N` have "(p \<bullet> xvec) \<sharp>* P'"
    by(force intro: output_fresh_chain_derivative)
  with P''Trans S `(p \<bullet> xvec) \<sharp>* N` have "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
    by(simp add: bound_output_chain_alpha'')
  ultimately show ?thesis by(rule weak_transitionI)
qed
*)
lemma weak_output_alpha:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "distinct_perm p"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* (p \<bullet> xvec)"
  and     "(p \<bullet> xvec) \<sharp>* M"
  and     "distinct xvec"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
    by(rule weak_transitionE)


  note PChain qeq_p''
  moreover from PChain `xvec \<sharp>* P` have "xvec \<sharp>* P''" by(rule tau_chain_fresh_chain)
  with P''Trans `xvec \<sharp>* (p \<bullet> xvec)` `distinct xvec` `(p \<bullet> xvec) \<sharp>* M` have "xvec \<sharp>* (p \<bullet> N)" and "xvec \<sharp>* P'"
    by(force intro: output_fresh_chain_derivative)+
  hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> N)" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])+
  with `distinct_perm p` have "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')" by simp+
  with P''Trans S `distinct_perm p` have "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
    apply(simp add: residual_inject)
    by(subst bound_output_chain_alpha) auto
    
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_fresh_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> \<alpha>"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"

  shows "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `x \<sharp> P` have "x \<sharp> P''" by(rule tau_chainFresh)
  with P''Trans show "x \<sharp> P'" using `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    by(force intro: free_fresh_derivative)
qed

lemma weak_fresh_chain_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* \<alpha>"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"

  shows "yvec \<sharp>* P'"
using assms
by(induct yvec) (auto intro: weak_fresh_derivative)

lemma weak_input_fresh_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> N"

  shows "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `x \<sharp> P` have "x \<sharp> P''" by(rule tau_chainFresh)
  with P''Trans show "x \<sharp> P'" using `x \<sharp> N` 
    by(force intro: input_fresh_derivative)
qed

lemma weak_input_fresh_chain_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* N"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: weak_input_fresh_derivative)

lemma weak_output_fresh_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> xvec"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"

  shows "x \<sharp> N"
  and   "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `x \<sharp> P` have "x \<sharp> P''" by(rule tau_chainFresh)
  with P''Trans show "x \<sharp> N" and "x \<sharp> P'" using `x \<sharp> xvec` `xvec \<sharp>* M` `distinct xvec`
    by(force intro: output_fresh_derivative)+
qed

lemma weak_output_fresh_chain_derivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "yvec \<sharp>* P"
  and     "xvec \<sharp>* yvec"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"

  shows "yvec \<sharp>* N"
  and   "yvec \<sharp>* P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `yvec \<sharp>* P` have "yvec \<sharp>* P''" by(rule tau_chain_fresh_chain)
  with P''Trans show "yvec \<sharp>* N" and "yvec \<sharp>* P'" using `xvec \<sharp>* yvec` `xvec \<sharp>* M` `distinct xvec`
    by(force intro: output_fresh_chain_derivative)+
qed

lemma weak_output_perm_subject:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `yvec \<sharp>* P` `zvec \<sharp>* P` have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tau_chain_fresh_chain)+

  note PChain qeq_p''
  moreover from P''Trans S `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* P''` `zvec \<sharp>* P''` have "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac output_perm_subject) (assumption | auto)
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_input_perm_subject:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `yvec \<sharp>* P` `zvec \<sharp>* P` have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tau_chain_fresh_chain)+

  note PChain qeq_p''
  moreover from P''Trans S `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* P''` `zvec \<sharp>* P''` have "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule_tac input_perm_subject) auto
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_input:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<turnstile> K \<leftrightarrow> M"
  and     "distinct xvec" 
  and     "set xvec \<subseteq> supp N"
  and     "length xvec = length Tvec"
  and     Qeq\<Psi>: "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
proof -
  have "\<Psi> \<rhd>  M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<lparr>\<lambda>*xvec N\<rparr>.P" by simp
  moreover from Qeq\<Psi> have "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(M\<lparr>\<lambda>*xvec N\<rparr>.P)) \<Psi>"
    by auto
  moreover from assms have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
    by(rule_tac Input)
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_output:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     Qeq\<Psi>: "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<langle>N\<rangle>.P \<Longrightarrow>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<langle>N\<rangle> \<prec> P"
proof -
  have "\<Psi> \<rhd>  M\<langle>N\<rangle>.P \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<langle>N\<rangle>.P" by simp
  moreover from Qeq\<Psi> have "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(M\<langle>N\<rangle>.P)) \<Psi>"
    by auto
  moreover have "insert_assertion (extract_frame(M\<langle>N\<rangle>.P)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(M\<langle>N\<rangle>.P)) \<Psi>" by simp
  moreover from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<langle>N\<rangle> \<prec> P"
    by(rule Output)
  ultimately show ?thesis by(rule_tac weak_transitionI) auto
qed

lemma insert_guarded_assertion:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "insert_assertion(extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule fresh_frame)
  from `guarded P` fr_p have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
    by(blast dest: guarded_stat_eq)+
  
  from fr_p `A\<^sub>P \<sharp>* \<Psi>` `\<Psi>\<^sub>P \<simeq> \<one>` have "insert_assertion(extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
    by simp (metis frame_int_composition_sym)
  moreover from `A\<^sub>P \<sharp>* \<Psi>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
    by(rule_tac frame_res_fresh_chain) auto
  ultimately show ?thesis by(rule Frame_stat_eq_trans)
qed
  
lemma weak_case:
  fixes \<Psi>   :: 'b 
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "(\<phi>, P) mem cs_p"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"
  and     r_imp_q: "insert_assertion (extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     imp_r: "insert_assertion (extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"

  shows "\<Psi> : R \<rhd> Cases cs_p \<Longrightarrow>\<pi> @ \<alpha> \<prec> P' \<or> \<Psi> : R \<rhd> Cases cs_p \<Longrightarrow>map_option (F_assert o push_prov) \<pi> @ \<alpha> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)
  show ?thesis
  proof(case_tac "P = P''")
    assume "P = P''"
    have "\<Psi> \<rhd> Cases cs_p \<Longrightarrow>\<^sup>^\<^sub>\<tau> Cases cs_p" by simp
    moreover from imp_r Assertion_stat_eq_def have "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame(Cases cs_p)) \<Psi>"
      by(rule_tac Frame_stat_imp_trans) (auto intro: Identity)+

    moreover from P''Trans `(\<phi>, P) mem cs_p` `\<Psi> \<turnstile> \<phi>` `guarded P` `P = P''` have "\<Psi> \<rhd> Cases cs_p \<longmapsto>map_option (F_assert o push_prov) \<pi> @ \<alpha> \<prec> P'"
      by(blast intro: Case)
    ultimately show ?thesis
      by(metis weak_transitionI)
  next
    assume "P \<noteq> P''"
    with PChain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(simp add: rtrancl_eq_or_trancl)
    hence "\<Psi> \<rhd> Cases cs_p \<Longrightarrow>\<^sub>\<tau> P''" using `(\<phi>, P) mem cs_p` `\<Psi> \<turnstile> \<phi>` `guarded P` 
      by(rule tau_step_chain_case)
    hence "\<Psi> \<rhd> Cases cs_p \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    moreover from r_imp_q qeq_p'' have "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P'') \<Psi>"
      by(rule Frame_stat_imp_trans)
    ultimately show ?thesis using P''Trans by(metis weak_transitionI)
  qed
qed

lemma weak_open:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<in> supp N"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tau_chain_res_pres)
  moreover from qeq_p'' `x \<sharp> \<Psi>` have "insert_assertion (extract_frame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frame_imp_res_pres)
  moreover from P''Trans `x \<in> supp N` `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule Open)
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_scope:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>map_option (F_res x) \<pi> @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tau_chain_res_pres)
  moreover from qeq_p'' `x \<sharp> \<Psi>` have "insert_assertion (extract_frame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frame_imp_res_pres)
  moreover from P''Trans `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>map_option (F_res x) \<pi> @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
    by(rule Scope)
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_par1:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     fr_q: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "bn \<alpha> \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* \<alpha>"
  and     "A\<^sub>Q \<sharp>* R"

  shows "\<Psi> : R \<parallel> Q \<rhd> P \<parallel> Q \<Longrightarrow>append_at_end_prov_option \<pi> A\<^sub>Q @ \<alpha> \<prec> P' \<parallel> Q"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and req_p'': "insert_assertion (extract_frame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* P''" by(rule tau_chain_fresh_chain)
  from PChain fr_q `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tau_chain_par1)
  moreover have "insert_assertion (extract_frame(R \<parallel> Q)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(P'' \<parallel> Q)) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where fr_r: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in fresh_frame) auto
    obtain A\<^sub>P'' \<Psi>\<^sub>P'' where fr_p'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in fresh_frame) auto

    from fr_r fr_p'' `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* P''` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''"
      by(force dest: extract_frame_fresh_chain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frame_nil_stat_eq frame_res_chain_pres Associativity Commutativity Composition Assertion_stat_eq_trans)
    moreover from req_p'' fr_r fr_p'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using fresh_comp_chain by auto
    moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis frame_nil_stat_eq frame_res_chain_pres Associativity Commutativity Composition Assertion_stat_eq_trans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(force dest: Frame_stat_imp_trans simp add: Frame_stat_eq_def)

    hence "\<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P''@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      apply(simp add: frame_chain_append)
      apply(drule_tac xvec=A\<^sub>Q in frame_imp_res_chain_pres)
      by(metis frame_imp_chain_comm Frame_stat_imp_trans)
    with fr_r fr_q fr_p'' `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P'' \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` req_p''
    show ?thesis by simp
  qed
  moreover from P''Trans fr_q `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P''` `A\<^sub>Q \<sharp>* \<alpha>` have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>append_at_end_prov_option \<pi> A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)"
    by(rule Par1)  
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_par2:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Q'   :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b

  assumes QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P : R \<rhd> Q \<Longrightarrow>\<pi> @ \<alpha> \<prec> Q'"
  and     fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "bn \<alpha> \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* R"

  shows "\<Psi> : P \<parallel> R \<rhd> P \<parallel> Q \<Longrightarrow>append_at_front_prov_option \<pi> A\<^sub>P @ \<alpha> \<prec> P \<parallel> Q'"
proof -
  from QTrans obtain Q'' where QChain: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''"
                           and req_q'': "insert_assertion (extract_frame R) (\<Psi> \<otimes> \<Psi>\<^sub>P) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q'') (\<Psi> \<otimes> \<Psi>\<^sub>P)"
                           and Q''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q'' \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
    by(rule weak_transitionE)

  from QChain `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* Q''" by(rule tau_chain_fresh_chain)

  from QChain fr_p `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<parallel> Q''" by(rule tau_chain_par2)
  moreover have "insert_assertion (extract_frame(P \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(P \<parallel> Q'')) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where fr_r: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in fresh_frame) auto
    obtain A\<^sub>Q'' \<Psi>\<^sub>Q'' where fr_q'': "extract_frame Q'' = \<langle>A\<^sub>Q'', \<Psi>\<^sub>Q''\<rangle>" and "A\<^sub>Q'' \<sharp>* A\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in fresh_frame) auto

    from fr_r fr_q'' `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q''` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''"
      by(force dest: extract_frame_fresh_chain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frame_nil_stat_eq frame_res_chain_pres Associativity Commutativity Composition Assertion_stat_eq_trans)

    moreover from req_q'' fr_r fr_q'' `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P`
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle>" using fresh_comp_chain by simp
    moreover have "\<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(metis frame_nil_stat_eq frame_res_chain_pres Associativity Commutativity Composition Assertion_stat_eq_trans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(force dest: Frame_stat_imp_trans simp add: Frame_stat_eq_def)
    hence "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P@A\<^sub>Q''), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      apply(simp add: frame_chain_append)
      apply(drule_tac xvec=A\<^sub>P in frame_imp_res_chain_pres)
      by(metis frame_imp_chain_comm Frame_stat_imp_trans)
    with fr_r fr_p fr_q'' `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q'' \<sharp>* A\<^sub>P` `A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q'' \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` req_q''
    show ?thesis by simp
  qed
  moreover from Q''Trans fr_p `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q''` `A\<^sub>P \<sharp>* \<alpha>` have "\<Psi> \<rhd> P \<parallel> Q'' \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')"
    by(rule_tac Par2) auto
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma weak_comm1:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     fr_r: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     fr_q: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* M"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* K"
  and     "A\<^sub>Q \<sharp>* zvec"
  and     "distinct A\<^sub>Q"
  and     "distinct zvec"
  and     "xvec \<sharp>* P"
  and     "zvec \<sharp>* \<Psi>"  
  and     "zvec \<sharp>* Q"
  and     "zvec \<sharp>* P"
  and     "zvec \<sharp>* A\<^sub>R"
  and     "zvec \<sharp>* \<Psi>\<^sub>Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and rimp_p'': "insert_assertion (extract_frame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* P''" by(rule tau_chain_fresh_chain)
  obtain A\<^sub>P'' \<Psi>\<^sub>P'' where fr_p'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* (\<Psi>, A\<^sub>Q, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, Q, P'', xvec, zvec)" and "distinct A\<^sub>P''"
    by(rule fresh_frame)
  hence "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* Q"
    and "A\<^sub>P'' \<sharp>* N" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P'' \<sharp>* zvec"
    by simp+
  from fr_r `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* R` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
  from fr_q `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* Q` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extract_frame_fresh_chain) auto
  from PChain `xvec \<sharp>* P` have "xvec \<sharp>* P''" by(force intro: tau_chain_fresh_chain)+

  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" 
    by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
  moreover with rimp_p'' fr_p'' fr_r `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using fresh_comp_chain
    by(simp add: fresh_chain_simps)
  moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
  ultimately have r_imp_p'': "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  from P''Trans `A\<^sub>P'' \<sharp>* P''` have "A\<^sub>P'' \<sharp>* \<pi>"
    by(rule trans_fresh_provenance)
    from P''Trans `extract_frame P'' = \<langle>A\<^sub>P'',\<Psi>\<^sub>P''\<rangle>` `distinct A\<^sub>P''`
         `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* A\<^sub>Q` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P'' \<sharp>* M` `A\<^sub>P'' \<sharp>* R` `A\<^sub>P'' \<sharp>* Q`
         `A\<^sub>P'' \<sharp>* N` `A\<^sub>P'' \<sharp>* K` `A\<^sub>P'' \<sharp>* A\<^sub>R` `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* xvec` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P'' \<sharp>* \<pi>` `A\<^sub>P'' \<sharp>* zvec`
    obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>A\<^sub>P''; tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* A\<^sub>P''"
                            "tvec \<sharp>* \<Psi>" "tvec \<sharp>* A\<^sub>Q" "tvec \<sharp>* \<Psi>\<^sub>Q" "tvec \<sharp>* M" "tvec \<sharp>* R" "tvec \<sharp>* Q"
                            "tvec \<sharp>* N" "tvec \<sharp>* K" "tvec \<sharp>* A\<^sub>R" "tvec \<sharp>* P''" "tvec \<sharp>* xvec" "tvec \<sharp>* \<Psi>\<^sub>R" "tvec \<sharp>* zvec"
                   and MeqK: "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P'' \<turnstile> M \<leftrightarrow> K'"
      by(frule_tac input_provenance'[where C="(\<Psi>,A\<^sub>Q,\<Psi>\<^sub>Q,M,R,Q,N,K,A\<^sub>R,P'',xvec,\<Psi>\<^sub>R,A\<^sub>P'',zvec)"]) auto
  from P''Trans have P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto> Some(\<langle>A\<^sub>P''; tvec, K'\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
    unfolding \<pi>.
  from MeqK have MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'"
    by(metis stat_eq_ent Associativity associativity_sym)

  from `A\<^sub>P'' \<sharp>* A\<^sub>Q` `extract_frame P'' = \<langle>A\<^sub>P'',\<Psi>\<^sub>P''\<rangle>` `A\<^sub>Q \<sharp>* P''`
  have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''"
    by(force dest: extract_frame_fresh_chain)
  from `A\<^sub>R \<sharp>* A\<^sub>Q` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `A\<^sub>Q \<sharp>* R`
  have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
    by(force dest: extract_frame_fresh_chain)
  from `tvec \<sharp>* A\<^sub>P''` `extract_frame P'' = \<langle>A\<^sub>P'',\<Psi>\<^sub>P''\<rangle>` `tvec \<sharp>* P''`
  have "tvec \<sharp>* \<Psi>\<^sub>P''"
    by(force dest: extract_frame_fresh_chain)

  have "zvec \<sharp>* P''" using `zvec \<sharp>* P` PChain
    by(rule_tac tau_chain_fresh_chain)
  from `A\<^sub>P'' \<sharp>* zvec` `extract_frame P'' = \<langle>A\<^sub>P'',\<Psi>\<^sub>P''\<rangle>` `zvec \<sharp>* P''`
  have "zvec \<sharp>* \<Psi>\<^sub>P''"
    by(force dest: extract_frame_fresh_chain)

  have "A\<^sub>Q \<sharp>* K'" using P''Trans
      `A\<^sub>Q\<sharp>* P''` `A\<^sub>P'' \<sharp>* A\<^sub>Q` `tvec \<sharp>* A\<^sub>Q`
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "zvec \<sharp>* K'" using P''Trans
      `zvec \<sharp>* P''` `A\<^sub>P'' \<sharp>* zvec` `tvec \<sharp>* zvec`
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')

  have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    using QTrans `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` QTrans MeqK' 
          r_imp_p'' iffD1[OF fresh_chain_sym, OF `A\<^sub>P'' \<sharp>* A\<^sub>Q`] 
          iffD1[OF fresh_chain_sym, OF `A\<^sub>R \<sharp>* A\<^sub>Q`] `A\<^sub>Q \<sharp>* \<Psi>`
          `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K'` `A\<^sub>P'' \<sharp>* \<Psi>`
          `A\<^sub>P'' \<sharp>* Q` `A\<^sub>P'' \<sharp>* M` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* M` `distinct zvec`
          `A\<^sub>Q \<sharp>* zvec` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>P''` `zvec \<sharp>* K'` `zvec \<sharp>* Q`
          iffD1[OF fresh_chain_sym, OF `A\<^sub>P'' \<sharp>* zvec`]
          `zvec \<sharp>* A\<^sub>R`
    by(rule_tac comm1_aux)

  from PChain fr_q `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tau_chain_par1)
  moreover from P''Trans QTrans fr_p'' have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    using fr_q `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P''` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* Q` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>P''` `tvec \<sharp>* Q` `zvec \<sharp>* \<Psi>` ` zvec \<sharp>* P''` `zvec \<sharp>* \<Psi>\<^sub>Q`
          `xvec \<sharp>* P''`
   by(rule_tac Comm1)
  ultimately show ?thesis
    by(drule_tac tau_act_tau_step_chain) auto
qed
(*
lemma weak_comm2:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     fr_r: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
  and     fr_q: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     meq_k: "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* M"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* K"
  and     "xvec \<sharp>* Q"
  and     "xvec \<sharp>* M"
  and     "xvec \<sharp>* A\<^sub>Q"
  and     "xvec \<sharp>* A\<^sub>R"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
proof -
  from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>Q` `xvec \<sharp>* A\<^sub>Q`
  obtain A\<^sub>Q' where fr_q': "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" 
               and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K" and "A\<^sub>R \<sharp>* A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* xvec"
    by(rule_tac C="(\<Psi>, P, Q, R, K, A\<^sub>R, xvec)" in distinct_frame) auto

  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and rimp_p'': "insert_assertion (extract_frame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `A\<^sub>Q' \<sharp>* P` have "A\<^sub>Q' \<sharp>* P''" by(rule tau_chain_fresh_chain)
  obtain A\<^sub>P'' \<Psi>\<^sub>P'' where fr_p'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* (\<Psi>, A\<^sub>Q', \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, Q, P'', xvec)" and "distinct A\<^sub>P''"
    by(rule fresh_frame)
  hence "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q'" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* Q"
    and "A\<^sub>P'' \<sharp>* N" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R"
    by simp+
  from fr_r `A\<^sub>R \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* R` have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
  from fr_q' `A\<^sub>R \<sharp>* A\<^sub>Q'` `A\<^sub>R \<sharp>* Q` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extract_frame_fresh_chain) auto

  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" 
    by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
  moreover with rimp_p'' fr_p'' fr_r `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using fresh_comp_chain
    by(simp add: fresh_chain_simps)
  moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
  ultimately have r_imp_p'': "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
      
  from PChain fr_q' `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tau_chain_par1)
  moreover from QTrans fr_r P''Trans meq_k r_imp_p'' fr_p'' fr_q' `distinct A\<^sub>P''` `distinct A\<^sub>Q'` `A\<^sub>P'' \<sharp>* A\<^sub>Q'` `A\<^sub>R \<sharp>* A\<^sub>Q'`
        `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P''` `A\<^sub>Q' \<sharp>* Q` `A\<^sub>Q' \<sharp>* R` `A\<^sub>Q' \<sharp>* K` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `A\<^sub>P'' \<sharp>* Q`
        `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* M` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* M` `xvec \<sharp>* A\<^sub>R` `xvec \<sharp>* M` `A\<^sub>Q' \<sharp>* xvec`
  obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>Q' \<sharp>* K'"
    by(rule_tac comm2_aux) (assumption | simp)+
  with P''Trans fr_p'' have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')" using fr_q' `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P''` `A\<^sub>Q' \<sharp>* Q`
    `xvec \<sharp>* Q` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* Q` `A\<^sub>P'' \<sharp>* M`  `A\<^sub>P'' \<sharp>* A\<^sub>Q'`
    by(rule_tac Comm2)
  ultimately show ?thesis
    by(drule_tac tau_act_tau_step_chain) auto
qed
*)
lemma frame_imp_int_composition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
proof -
  from assms have "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>" by(rule frame_int_composition)
  thus ?thesis by(simp add: Frame_stat_eq_def)
qed

lemma insert_assertionStatImp:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes feq_g: "insert_assertion F \<Psi> \<hookrightarrow>\<^sub>F insert_assertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insert_assertion F \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where fr_f: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where fr_g: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto

  from `\<Psi> \<simeq> \<Psi>'` have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle>" by (metis frame_int_composition Frame_stat_eq_sym)
  moreover from `\<Psi> \<simeq> \<Psi>'` have "\<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>G\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" by(rule frame_int_composition)
  ultimately have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" using feq_g fr_f fr_g `A\<^sub>F \<sharp>* \<Psi>` `A\<^sub>G \<sharp>* \<Psi>` `\<Psi> \<simeq> \<Psi>'`
    by(force simp add: Frame_stat_eq_def dest: Frame_stat_imp_trans)
  with fr_f fr_g `A\<^sub>F \<sharp>* \<Psi>'` `A\<^sub>G \<sharp>* \<Psi>'` show ?thesis by simp
qed

lemma insert_assertionStatEq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes feq_g: "insert_assertion F \<Psi> \<simeq>\<^sub>F insert_assertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insert_assertion F \<Psi>' \<simeq>\<^sub>F insert_assertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where fr_f: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where fr_g: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto

  from feq_g fr_f fr_g `A\<^sub>F \<sharp>* \<Psi>` `A\<^sub>G \<sharp>* \<Psi>` `\<Psi> \<simeq> \<Psi>'`
  have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>"
    by simp (metis frame_int_composition Frame_stat_eq_trans Frame_stat_eq_sym)
  with fr_f fr_g `A\<^sub>F \<sharp>* \<Psi>'` `A\<^sub>G \<sharp>* \<Psi>'` show ?thesis by simp
qed

lemma weak_transition_stat_eq:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and qeq_p'': "insert_assertion (extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)

  from PChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(rule tau_chain_stat_eq)
  moreover from qeq_p'' `\<Psi> \<simeq> \<Psi>'` have "insert_assertion (extract_frame Q) \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') \<Psi>'"
    by(rule insert_assertionStatImp)
  moreover from P''Trans `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule stat_eq_transition)
  ultimately show ?thesis by(rule weak_transitionI)
qed

lemma transition_weak_transition:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "insert_assertion(extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P) \<Psi>"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
using assms
by(fastforce intro: weak_transitionI)

lemma weak_bang:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : R \<rhd> P \<parallel> !P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and     "guarded P"

  obtains \<pi>' where "\<Psi> : R \<rhd> !P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'"
proof -
  assume ob: "(\<And>\<pi>'. \<Psi> : R \<rhd> !P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P' \<Longrightarrow> thesis)"
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and r_imp_p'': "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(rule weak_transitionE)
  moreover obtain A\<^sub>P \<Psi>\<^sub>P where fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule fresh_frame)
  moreover from `guarded P` fr_p have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guarded_stat_eq)
  ultimately show ?thesis
  proof(auto simp add: rtrancl_eq_or_trancl)
    have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> !P" by simp
    moreover assume rimp_p: "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    have "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame(!P)) \<Psi>"
    proof -
      from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
        by(metis frame_int_composition_sym frame_int_associativity frame_int_commutativity frame_int_identity Frame_stat_eq_trans Frame_stat_eq_sym)
      moreover from `A\<^sub>P \<sharp>* \<Psi>` have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
        by(force intro: frame_res_fresh_chain)
      ultimately show ?thesis using rimp_p by(auto simp add: Frame_stat_eq_def dest: Frame_stat_imp_trans)
    qed
    moreover assume "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    hence "\<Psi> \<rhd> !P \<longmapsto> map_option (F_assert \<circ> push_prov) \<pi> @ \<alpha> \<prec> P'" using `guarded P` by(rule Bang)
   ultimately show ?thesis by(metis ob weak_transitionI)
  next
    fix P'''
    assume "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau>  P''"
    hence "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P''" using `guarded P` by(rule tau_step_chain_bang)
    hence "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    moreover assume "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P'') \<Psi>"
                and "\<Psi> \<rhd> P'' \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    ultimately show ?thesis by(metis ob weak_transitionI)
  qed
qed

lemma weak_transition_frame_imp:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and             "insert_assertion(extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q) \<Psi>"

  shows "\<Psi> : R \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
using assms
by(auto simp add: weak_transition_def intro: Frame_stat_imp_trans)

lemma guarded_frame_stat_eq:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "extract_frame P \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(rule fresh_frame)
  from `guarded P` fr_p have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guarded_stat_eq)
  hence "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<one>\<rangle>" by(rule_tac frame_res_chain_pres) auto
  moreover have "\<langle>A\<^sub>P, \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>" by(rule_tac frame_res_fresh_chain) auto
  ultimately show ?thesis using fr_p by(force intro: Frame_stat_eq_trans)
qed

lemma weak_guarded_transition:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
  and    "guarded Q"

  shows "\<Psi> : \<zero> \<rhd> P \<Longrightarrow>\<pi> @ \<alpha> \<prec> P'"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where fr_q: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" by(rule fresh_frame)
  moreover from `guarded Q` fr_q have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guarded_stat_eq)
  hence "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle>" by(metis frame_int_composition_sym)
  moreover from `A\<^sub>Q \<sharp>* \<Psi>` have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule_tac frame_res_fresh_chain) auto
  ultimately have "insert_assertion(extract_frame Q) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame (\<zero>)) \<Psi>"
    using fr_q `A\<^sub>Q \<sharp>* \<Psi>` by simp (blast intro: Frame_stat_eq_trans)
  with PTrans show ?thesis by(rule_tac weak_transition_frame_imp) (auto simp add: Frame_stat_eq_def) 
qed

lemma expand_tau_chain_frame:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   C   :: "'d::fs_name"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"

  obtains \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
using PChain fr_p `A\<^sub>P \<sharp>* P`
proof(induct arbitrary: thesis rule: tau_chain_induct)
  case(tau_base P)
  have "\<Psi>\<^sub>P \<otimes> \<one> \<simeq> \<Psi>\<^sub>P" by(rule Identity)
  with `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` show ?case using `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* C` `distinct A\<^sub>P` by(rule tau_base)
next
  case(tau_step P P' P'')
  from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* P`
  obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                       and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
    by(rule_tac tau_step)
  from `\<Psi> \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''` fr_p' `distinct A\<^sub>P'` `A\<^sub>P' \<sharp>* P'` `A\<^sub>P' \<sharp>* C`
  obtain \<Psi>'' A\<^sub>P'' \<Psi>\<^sub>P'' where fr_p'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "\<Psi>\<^sub>P' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''"
                          and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* C" and "distinct A\<^sub>P''"
    by(rule expand_tau_frame)
  from `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'` have "(\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>''" by(rule Composition)
  with `\<Psi>\<^sub>P' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''` have "\<Psi>\<^sub>P \<otimes> \<Psi>' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''"
    by(metis Assertion_stat_eq_trans Associativity Commutativity)
  with fr_p'' show ?case using `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* C` `distinct A\<^sub>P''`
    by(rule tau_step)
qed

lemma frame_int_imp_composition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms frame_int_composition
by(simp add: Frame_stat_eq_def)

lemma tau_chain_induct2[consumes 1, case_names tau_base tau_step]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     cBase: "\<And>P. Prop P P"
  and     cStep: "\<And>P P' P''. \<lbrakk>\<Psi> \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''; \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; Prop P P'\<rbrakk> \<Longrightarrow> Prop P P''"

  shows "Prop P P'"
using assms
by(rule tau_chain_induct)

lemma tau_step_chain_induct2[consumes 1, case_names tau_base tau_step]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     cBase: "\<And>P P'. \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P' \<Longrightarrow> Prop P P'"
  and     cStep: "\<And>P P' P''. \<lbrakk>\<Psi> \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''; \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'; Prop P P'\<rbrakk> \<Longrightarrow> Prop P P''"

  shows "Prop P P'"
using assms
by(rule tau_step_chain_induct)

lemma weak_transfer_tau_chain_frame:
  fixes \<Psi>\<^sub>F :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   A\<^sub>F :: "name list"
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b

  assumes PChain: "\<Psi>\<^sub>F \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     feq_g: "\<And>\<Psi>. insert_assertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>"
  and     "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* \<Psi>"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>P \<sharp>* P"

  shows "\<Psi>\<^sub>G \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using PChain fr_p `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` `A\<^sub>P \<sharp>* P` 
proof(induct rule: tau_chain_induct2)
  case tau_base
  thus ?case by simp
next
  case(tau_step P P' P'')
  have fr_p: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  then have PChain: "\<Psi>\<^sub>G \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" using `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` `A\<^sub>P \<sharp>* P` by(rule tau_step)
  then obtain A\<^sub>P' \<Psi>\<^sub>P' \<Psi>' where fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                            and "A\<^sub>P' \<sharp>* A\<^sub>F" and "A\<^sub>P' \<sharp>* A\<^sub>G" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>F" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>G"
                            and "distinct A\<^sub>P'"
                
    using fr_p `distinct A\<^sub>P` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G`
    by(rule_tac C="(A\<^sub>F, A\<^sub>G, \<Psi>\<^sub>F, \<Psi>\<^sub>G)" in expand_tau_chain_frame) auto

  from PChain `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` have "A\<^sub>F \<sharp>* P'" and "A\<^sub>G \<sharp>* P'" by(blast dest: tau_chain_fresh_chain)+

  with `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G``A\<^sub>P' \<sharp>* A\<^sub>F` `A\<^sub>P' \<sharp>* A\<^sub>G` fr_p fr_p'
  have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>P'" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>P'"
    by(auto dest: extract_frame_fresh_chain)

  from feq_g have feq_g: "insert_assertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>'"
    by blast
  obtain p::"name prm" where "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F" and  "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'"
                         and Sp: "(set p) \<subseteq> set A\<^sub>F \<times> set(p \<bullet> A\<^sub>F)" and "distinct_perm p"
      by(rule_tac xvec=A\<^sub>F and c="(\<Psi>\<^sub>F, \<Psi>\<^sub>P, \<Psi>', \<Psi>\<^sub>P')" in name_list_avoiding) auto
  obtain q::"name prm" where "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G" and  "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P'" and "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>'"
                         and Sq: "(set q) \<subseteq> set A\<^sub>G \<times> set(q \<bullet> A\<^sub>G)" and "distinct_perm q"
    by(rule_tac xvec=A\<^sub>G and c="(\<Psi>\<^sub>G, \<Psi>\<^sub>P, \<Psi>', \<Psi>\<^sub>P')" in name_list_avoiding) auto
  from `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'` have "\<langle>(p \<bullet> A\<^sub>F), ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P')\<rangle> \<simeq>\<^sub>F \<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>')\<rangle>"
    by(rule frame_int_composition_sym[OF Assertion_stat_eq_sym])
  hence "\<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle>"
    by(metis frame_int_associativity Frame_stat_eq_trans frame_int_commutativity Frame_stat_eq_sym)
  moreover from feq_g `A\<^sub>F \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'` Sp
  have "\<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F insert_assertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>'"
    apply(erule_tac rev_mp) by(subst frame_chain_alpha) (auto simp add: eqvts)
  hence "\<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F  (\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P\<rangle>)"
    using `A\<^sub>G \<sharp>* \<Psi>\<^sub>P` `(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P` `(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G` `(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>'` Sq
    apply(erule_tac rev_mp) by(subst frame_chain_alpha) (auto simp add: eqvts)
  moreover have "\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> ((q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P)\<rangle> \<simeq>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>')\<rangle>"
    by(metis frame_int_associativity Frame_stat_eq_trans frame_int_commutativity Frame_stat_eq_sym)
  hence "\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> ((q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P)\<rangle> \<simeq>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>" using `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'`
    by(blast intro: Frame_stat_eq_trans frame_int_composition_sym)
  ultimately have "\<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  with `A\<^sub>F \<sharp>* \<Psi>\<^sub>P'` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P'` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F` Sp have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(subst frame_chain_alpha) (auto simp add: eqvts)
  with `A\<^sub>G \<sharp>* \<Psi>\<^sub>P'` `(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P'` `(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G` Sq have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(subst frame_chain_alpha) (auto simp add: eqvts)
  
  with `\<Psi>\<^sub>F \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''` fr_p' `distinct A\<^sub>P'`
       `A\<^sub>F \<sharp>* P'` `A\<^sub>G \<sharp>* P'` `A\<^sub>F \<sharp>* \<Psi>\<^sub>G` `A\<^sub>G \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P' \<sharp>* A\<^sub>F` `A\<^sub>P' \<sharp>* A\<^sub>G` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>G`
  have "\<Psi>\<^sub>G \<rhd> P' \<longmapsto>None @ \<tau> \<prec> P''" by(rule_tac transfer_tau_frame)
  with PChain show ?case by(simp add: r_into_rtrancl rtrancl_into_rtrancl)
qed

coinductive quiet :: "('a, 'b, 'c) psi \<Rightarrow> bool"
  where "\<lbrakk>\<forall>\<Psi>. (insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle> \<and> 
              (\<forall>Rs \<pi>. \<Psi> \<rhd> P \<longmapsto>\<pi> @  Rs \<longrightarrow> (\<exists>P'. Rs = \<tau> \<prec> P' \<and> \<pi> = None \<and> quiet P')))\<rbrakk> \<Longrightarrow> quiet P"

lemma quiet_frame:
  fixes \<Psi> :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "quiet P"

  shows "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
using assms
by(erule_tac quiet.cases) force
  
lemma quiet_transition:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"

  assumes "quiet P"
  and     "\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"

  obtains P' where "Rs = \<tau> \<prec> P'" and "quiet P'" and "\<pi> = None"
using assms
by(erule_tac quiet.cases) force

lemma quiet_eqvt:
  fixes P :: "('a, 'b, 'c) psi"
  and   p :: "name prm"

  assumes "quiet P"

  shows "quiet(p \<bullet> P)"
proof -
  let ?X = "\<lambda>P. \<exists>p::name prm. quiet(p \<bullet> P)"
  from assms have "?X (p \<bullet> P)" by(rule_tac x="rev p" in exI) auto
  thus ?thesis
    apply coinduct
    apply(clarify)
    apply(rule_tac x=x in exI)
    apply auto
    apply(drule_tac \<Psi>="p \<bullet> \<Psi>" in quiet_frame)
    apply(drule_tac p="rev p" in Frame_stat_eq_closed)
    apply(simp add: eqvts)
    apply(drule_tac pi=p in semantics.eqvt)
    apply(erule_tac quiet_transition)
    apply assumption
    apply(rule_tac x="rev p \<bullet> P'" in exI)
    apply auto
    apply(drule_tac pi="rev p" in pt_bij3)
    apply(simp add: eqvts)
    apply(drule_tac pi="rev p" in pt_bij3)
    apply(drule_tac pi="rev p" in pt_bij3)
    apply(simp add: eqvts)
    apply(drule_tac pi="rev p" in pt_bij3)
    apply(simp add: eqvts)
    apply(rule_tac x=p in exI)
    by simp
qed
  

lemma quiet_output:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "quiet P"

  shows False
using assms
apply(erule_tac quiet.cases)
thm residual_inject
by(force simp add: residual_inject)

lemma quiet_input:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "quiet P"

  shows False
using assms
by(erule_tac quiet.cases) (force simp add: residual_inject)

lemma quiet_tau:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'"
  and     "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
  and     "quiet P"

  shows "quiet P'"
using assms
by(erule_tac quiet.cases) (force simp add: residual_inject)

lemma tau_chain_cases[consumes 1, case_names tau_base tau_step]:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "P = P' \<Longrightarrow> Prop"
  and     "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> Prop"

  shows Prop
using assms
by(blast elim: rtranclE dest: rtrancl_into_trancl1)

end

end
