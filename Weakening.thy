(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weakening
  imports Weak_Bisimulation
begin

locale weak = env + 
  assumes weaken: "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
begin

lemma entWeaken:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  assumes "\<Psi> \<turnstile> \<phi>"

  shows "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>"
using assms weaken
by(auto simp add: Assertion_stat_imp_def)

lemma assertWeaken:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
by(auto simp add: Assertion_stat_imp_def entWeaken)

lemma frameWeaken:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F \<otimes>\<^sub>F G"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* F" and  "A\<^sub>F \<sharp>* G"
    by(rule_tac F=F and C="(F, G)" in fresh_frame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* F" and  "A\<^sub>G \<sharp>* G" and "A\<^sub>G \<sharp>* A\<^sub>F" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
    by(rule_tac F=G and C="(F, G, A\<^sub>F, \<Psi>\<^sub>F)" in fresh_frame) auto
  from FrG `A\<^sub>F \<sharp>* G` `A\<^sub>G \<sharp>* A\<^sub>F` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" by auto
  have "\<Psi>\<^sub>F \<hookrightarrow> \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" by(rule weaken)
  hence "\<langle>A\<^sub>G, \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>" by(rule_tac frame_imp_res_chain_pres) auto
  with `A\<^sub>G \<sharp>* \<Psi>\<^sub>F` have "\<langle>\<epsilon>, \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>" using frame_res_fresh_chain
    by(rule_tac Frame_stat_imp_trans) (auto simp add: Frame_stat_eq_def)
  with FrF FrG `A\<^sub>G \<sharp>* A\<^sub>F` `A\<^sub>G \<sharp>* \<Psi>\<^sub>F` `A\<^sub>F \<sharp>* \<Psi>\<^sub>G` show ?thesis
    by(force simp add: frame_chain_append intro: frame_imp_res_chain_pres)
qed

lemma unitAssertWeaken:
  fixes \<Psi> :: 'b

  shows "\<one> \<hookrightarrow> \<Psi>"
proof -
  have "\<one> \<hookrightarrow> \<one> \<otimes> \<Psi>" by(rule assertWeaken)
  moreover have "\<one> \<otimes> \<Psi> \<hookrightarrow> \<Psi>" by(metis Identity Assertion_stat_eq_def Commutativity Assertion_stat_eq_trans)
  ultimately show ?thesis by(rule Assertion_stat_imp_trans)
qed

lemma unitFrameWeaken:
  fixes F :: "'b frame"

  shows "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F F"
proof -
  have "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F ((\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F)" by(rule frameWeaken)
  moreover obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
    by(rule_tac F=F and C="()" in fresh_frame) auto
  hence "(\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F \<simeq>\<^sub>F F" 
    by simp (metis frame_int_identity frame_int_commutativity Frame_stat_eq_trans Frame_stat_eq_sym)
  ultimately show ?thesis by(metis Frame_stat_imp_trans Frame_stat_eq_def)
qed

lemma insert_assertionWeaken:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F insert_assertion F \<Psi>"
proof -
  have "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F (\<langle>\<epsilon>, \<Psi>\<rangle>) \<otimes>\<^sub>F F" by(rule frameWeaken)
  thus ?thesis by simp
qed

lemma frameImpStatEq:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<phi>  :: 'c

  assumes "(\<langle>A\<^sub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "(\<langle>A\<^sub>F, \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>"
proof -
  obtain p::"name prm" where "(p \<bullet> A\<^sub>F) \<sharp>* \<phi>" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'"
                         and "distinct_perm p" and S: "set p \<subseteq> set A\<^sub>F \<times> set(p \<bullet> A\<^sub>F)"
    by(rule_tac c="(\<phi>, \<Psi>, \<Psi>')" in name_list_avoiding) auto
  from `(\<langle>A\<^sub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>` `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>` S have "(\<langle>(p \<bullet> A\<^sub>F), p \<bullet> \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(simp add: frame_chain_alpha)
  hence "(p \<bullet> \<Psi>) \<turnstile> \<phi>" using `(p \<bullet> A\<^sub>F) \<sharp>* \<phi>` by(rule frame_impE)
  moreover from `\<Psi> \<simeq> \<Psi>'` have "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')" by(rule Assertion_stat_eq_closed)
  ultimately have "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(simp add: Assertion_stat_eq_def Assertion_stat_imp_def)
  hence "(\<langle>(p \<bullet> A\<^sub>F), p \<bullet> \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>" using `(p \<bullet> A\<^sub>F) \<sharp>* \<phi>` 
    by(rule_tac frame_impI) auto
  with `(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'` S show ?thesis by(simp add: frame_chain_alpha)
qed

lemma statImpTauDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'"

  shows "insert_assertion (extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P') \<Psi>"
proof(auto simp add: Frame_stat_imp_def)
  fix \<phi> :: 'c
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>P \<sharp>* \<Psi>" and "distinct A\<^sub>P" 
    by(rule_tac C="(P, \<phi>, \<Psi>)" in fresh_frame) auto
  with `\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'` obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" 
                                              and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<phi>"  and "A\<^sub>P' \<sharp>* \<Psi>" 
    by(rule_tac C="(\<Psi>, \<phi>)" in expand_tau_frame) auto
  assume "insert_assertion (extract_frame P) \<Psi> \<turnstile>\<^sub>F \<phi>"
  with FrP `A\<^sub>P \<sharp>* \<phi>` `A\<^sub>P \<sharp>* \<Psi>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(auto dest: frame_impE)
  hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  hence "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> \<phi>" using `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'`
    by(rule_tac stat_eq_ent, auto) (metis Associativity composition_sym Assertion_stat_eq_trans Assertion_stat_eq_sym Commutativity)
  with `A\<^sub>P' \<sharp>* \<phi>` `A\<^sub>P' \<sharp>* \<Psi>` FrP' show "insert_assertion (extract_frame P') \<Psi> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frame_impI)
qed

lemma weakenTransition:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"

  shows "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> \<pi> @ Rs"
using assms
proof(nominal_induct avoiding: \<Psi>' rule: semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P \<Psi>')
  from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case using `distinct xvec` `set xvec \<subseteq> (supp N)` `length xvec = length Tvec` 
    by(rule Input)
next
  case(Output \<Psi> M K N P \<Psi>')
  from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case by(rule semantics.Output)
next
  case(Case \<Psi> P \<pi> Rs \<phi> Cs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> \<pi> @ Rs" by(rule Case)
  moreover note `(\<phi>, P) mem Cs`
  moreover from `\<Psi> \<turnstile> \<phi>` have "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  ultimately show ?case using `guarded P`
    by(rule semantics.Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'" by(rule c_par1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  thus ?case using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>'` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
    by(rule_tac Par1) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" by(rule c_par2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  thus ?case using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>'` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
    by(rule_tac Par2) auto
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec xvec Q' \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" by(rule c_comm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
  moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by(rule c_comm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
  ultimately show ?case using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>'` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q`
                              `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>'` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* P`
                              `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* \<Psi>'` `yvec \<sharp>* Q`
                              `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* \<Psi>'` `zvec \<sharp>* P`
    by(rule_tac Comm1) (assumption | auto)+
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec Q' \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule c_comm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
  moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'" by(rule c_comm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'"
    by(metis stat_eq_transition Composition Associativity Commutativity Assertion_stat_eq_trans)
  moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
  ultimately show ?case using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>'` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q`
                              `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>'` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* Q`
                              `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* \<Psi>'` `yvec \<sharp>* Q`
                              `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* \<Psi>'` `zvec \<sharp>* P`
    by(rule_tac Comm2) (assumption | auto)+
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule c_open)
  thus ?case using `x \<in> supp N` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec`
    by(rule_tac Open) auto
next  
  case(c_scope \<Psi> P \<pi> \<alpha> P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'" by(rule c_scope)
  thus ?case using `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` `x \<sharp> \<alpha>` by(rule_tac Scope) auto
next
  case(Bang \<Psi> P \<pi> Rs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<parallel> !P\<longmapsto>\<pi> @ Rs" by(rule Bang)
  thus ?case using `guarded P` by(rule semantics.Bang)
qed

end

end
