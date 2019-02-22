theory Bisimulation
  imports Simulation
begin

context env begin

lemma mono_coinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto>[{(xc, xb, xa). x xc xb xa}] P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto>[{(xb, xa, xc). y xb xa xc}] P)"
apply auto
apply(rule monotonic)
by(auto dest: le_funE)

coinductive_set bisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  step: "\<lbrakk>(insert_assertion (extract_frame P)) \<Psi> \<simeq>\<^sub>F (insert_assertion (extract_frame Q) \<Psi>);
          \<Psi> \<rhd> P \<leadsto>[bisim] Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> bisim; (\<Psi>, Q, P) \<in> bisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> bisim"
monos mono_coinduct

abbreviation
  bisim_judge ("_ \<rhd> _ \<sim> _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<sim> Q \<equiv> (\<Psi>, P, Q) \<in> bisim"
abbreviation
  bisim_nil_judge ("_ \<sim> _" [70, 70] 65) where "P \<sim> Q \<equiv> S_bottom' \<rhd> P \<sim> Q"

lemma bisim_coinduct_aux[consumes 1]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi> \<and>
                                    (\<Psi> \<rhd> P \<leadsto>[(X \<union> bisim)] Q) \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim) \<and>
                                    ((\<Psi>, Q, P) \<in> X \<or> (\<Psi>, Q, P) \<in> bisim)"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisim_coinduct[consumes 1, case_names c_stat_eq c_sim c_ext c_sym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> insert_assertion (extract_frame R) \<Psi>' \<simeq>\<^sub>F insert_assertion (extract_frame S) \<Psi>'"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[(X \<union> bisim)] S"
  and     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> bisim"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> (\<Psi>', S, R) \<in> bisim"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisim_weak_coinduct_aux[consumes 1]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi> \<and>
                                     \<Psi> \<rhd> P \<leadsto>[X] Q \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X) \<and> (\<Psi>, Q, P) \<in> X" 

  shows "(\<Psi>, P, Q) \<in> bisim"
using assms
by(coinduct rule: bisim_coinduct_aux) (blast intro: monotonic)

lemma bisim_weak_coinduct[consumes 1, case_names c_stat_eq c_sim c_ext c_sym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[X] Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
  by(coinduct rule: bisim_coinduct) (blast intro: monotonic)+
qed

(*lemma bisim_weak_coinduct[consumes 1, case_names c_stat_eq c_sim c_ext c_sym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[X] Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
  by(coinduct rule: bisim_coinduct) (blast intro: monotonic)+
qed*)

lemma bisimE:
  fixes P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "(\<Psi>, P, Q) \<in> bisim"

  shows "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and   "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
  and   "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
  and   "(\<Psi>, Q, P) \<in> bisim"
using assms
by(auto simp add: intro: bisim.cases)

lemma bisimI:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<Psi> :: 'b

  assumes "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
  and     "\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
  and     "(\<Psi>, Q, P) \<in> bisim"

  shows "(\<Psi>, P, Q) \<in> bisim"
using assms
by(auto intro: bisim.step)

lemma bisim_reflexive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"


  shows "\<Psi> \<rhd> P \<sim> P"
proof -
  let ?X = "{(\<Psi>, P, P) | \<Psi> P. True}"
  have "(\<Psi>, P, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisim_weak_coinduct, auto intro: reflexive)
qed

lemma bisim_closed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"
  
  assumes P_bisimQ: "\<Psi> \<rhd> P \<sim> Q"

  shows "(p \<bullet> \<Psi>) \<rhd>  (p \<bullet> P) \<sim> (p \<bullet> Q)"
proof -
  let ?X = "{(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) | (p::name prm) \<Psi>  P Q. \<Psi> \<rhd> P \<sim> Q}"
  from P_bisimQ have "(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> P Q)
    have "\<And>\<Psi> P Q (p::name prm). insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi> \<Longrightarrow>
          insert_assertion (extract_frame(p \<bullet> P)) (p \<bullet> \<Psi>) \<simeq>\<^sub>F insert_assertion (extract_frame(p \<bullet> Q))  (p \<bullet> \<Psi>)"
      by(drule_tac p = p in Frame_stat_eq_closed) (simp add: eqvts)
      
    with `(\<Psi>, P, Q) \<in> ?X` show ?case by(blast dest: bisimE)
  next
    case(c_sim \<Psi> P Q)
    {
      fix p :: "name prm"
      fix \<Psi> P Q
      have "eqvt ?X"
	apply(auto simp add: eqvt_def)
	apply(rule_tac x="pa@p" in exI)
	by(auto simp add: pt2[OF pt_name_inst])
      moreover assume "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
      hence "\<Psi> \<rhd> P \<leadsto>[?X] Q"
	apply(rule_tac A=bisim in monotonic, auto)
	by(rule_tac x="[]::name prm" in exI) auto
      ultimately have "((p::name prm) \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[?X] (p \<bullet> Q)"
	by(rule_tac sim_closed)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    {
      fix p :: "name prm"
      fix \<Psi> P Q \<Psi>'
      assume "\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
      hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P, p \<bullet> Q) \<in> ?X"  
	apply(auto, rule_tac x=p in exI)
	apply(rule_tac x="\<Psi> \<otimes> (rev p \<bullet> \<Psi>')" in exI)
	by(auto simp add: eqvts)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_sym \<Psi> P Q)
    thus ?case
      by(blast dest: bisimE)
  qed
qed

lemma bisim_eqvt[simp]:
  shows "eqvt bisim"
by(auto simp add: eqvt_def bisim_closed)

lemma stat_eq_bisim:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b
  
  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>', P, Q) | \<Psi> P Q \<Psi>'. \<Psi> \<rhd> P \<sim> Q \<and> \<Psi> \<simeq> \<Psi>'}"
  from `\<Psi> \<rhd> P \<sim> Q` `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>', P, Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisim_coinduct)
    case(c_stat_eq \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<sim> Q` have PeqQ: "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
      by(rule bisimE)

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* \<Psi>'"
      by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>'"
      by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto

    from PeqQ FrP FrQ `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `\<Psi> \<simeq> \<Psi>'`
    have "\<langle>A\<^sub>P, \<Psi>' \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by simp (metis frame_int_composition Frame_stat_eq_trans Frame_stat_eq_sym)
    with FrP FrQ `A\<^sub>P \<sharp>* \<Psi>'` `A\<^sub>Q \<sharp>* \<Psi>'` show ?case by simp
  next
    case(c_sim \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<rhd> P \<leadsto>[bisim] Q" by(blast dest: bisimE)
    moreover have "eqvt ?X"
      by(auto simp add: eqvt_def) (metis bisim_closed Assertion_stat_eq_closed)
    hence "eqvt(?X \<union> bisim)" by auto
    moreover note `\<Psi> \<simeq> \<Psi>'`
    moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> bisim"
      by auto
    ultimately show ?case
      by(rule stat_eq_sim)
  next
    case(c_ext \<Psi>' P Q \<Psi>'')
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<otimes> \<Psi>'' \<rhd> P \<sim> Q" by(rule bisimE)
    moreover from `\<Psi> \<simeq> \<Psi>'` have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
    ultimately show ?case by blast
  next
    case(c_sym \<Psi>' P Q)
    from `(\<Psi>', P, Q) \<in> ?X` obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<rhd> Q \<sim> P" by(rule bisimE)
    thus ?case using `\<Psi> \<simeq> \<Psi>'` by auto
  qed
qed

lemma bisim_transitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes PQ: "\<Psi> \<rhd> P \<sim> Q"
  and     QR: "\<Psi> \<rhd> Q \<sim> R"

  shows "\<Psi> \<rhd> P \<sim> R"
proof -
  let ?X = "{(\<Psi>, P, R) | \<Psi> P Q R. \<Psi> \<rhd> P \<sim> Q \<and> \<Psi> \<rhd> Q \<sim> R}" 
  from PQ QR have "(\<Psi>, P, R) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisim_coinduct)
    case(c_stat_eq \<Psi> P R)
    thus ?case by(blast dest: bisimE Frame_stat_eq_trans)
  next
    case(c_sim \<Psi> P R)
    {
      fix \<Psi> P Q R
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] Q" and "\<Psi> \<rhd> Q \<leadsto>[bisim] R"
      moreover have "eqvt ?X"
	by(force simp add: eqvt_def dest: bisim_closed)
      with bisim_eqvt have "eqvt (?X \<union> bisim)" by blast
      moreover have "?X \<subseteq> ?X \<union> bisim" by auto
      ultimately have "\<Psi> \<rhd> P \<leadsto>[(?X \<union> bisim)] R"
	by(force intro: transitive)
    }
    with `(\<Psi>, P, R) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_ext \<Psi> P R \<Psi>')
    thus ?case by(blast dest: bisimE)
  next
    case(c_sym \<Psi> P R)
    thus ?case by(blast dest: bisimE)
  qed
qed

lemma weak_transitive_coinduct[case_names c_stat_eq c_sim c_ext c_sym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and r_stat_eq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and r_sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and r_ext: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and r_sym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisim_reflexive)
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> P Q)
    thus ?case
      by(blast dest: r_stat_eq bisimE Frame_stat_eq_trans)
  next
    case(c_sim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'_rel_q': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule r_sim)
      moreover from `eqvt X` P'_rel_q' have "eqvt ?X"
	apply(auto simp add: eqvt_def)
	apply(drule_tac p=p in bisim_closed)
	apply(drule_tac p=p in bisim_closed)
	apply(rule_tac x="p \<bullet> P'a" in exI, simp)
	by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
	by(force intro: transitive dest: bisim_transitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using `eqvt ?X`
	by(force intro: transitive dest: bisim_transitive)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE intro: r_ext)
  next
    case(c_sym \<Psi> P Q)
    thus ?case by(blast dest: bisimE intro: r_sym)
  qed
qed

lemma weak_transitive_coinduct'[case_names c_stat_eq c_sim c_ext c_sym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and r_stat_eq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and r_sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and r_ext: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and r_sym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow>
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisim_reflexive)
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> P Q)
    thus ?case
      by(blast dest: r_stat_eq bisimE Frame_stat_eq_trans)
  next
    case(c_sim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'_rel_q': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule r_sim)
      moreover from `eqvt X` P'_rel_q' have "eqvt ?X"
	apply(auto simp add: eqvt_def)
	apply(drule_tac p=p in bisim_closed)
	apply(drule_tac p=p in bisim_closed)
	apply(rule_tac x="p \<bullet> P'a" in exI, simp)
	by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
	by(force intro: transitive dest: bisim_transitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using `eqvt ?X`
	by(force intro: transitive dest: bisim_transitive)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE intro: r_ext)
  next
    case(c_sym \<Psi> P Q)
    thus ?case
      apply auto
      apply(drule r_sym)
      apply auto
      by(metis bisim_transitive bisimE(4))
  qed
qed

lemma weak_transitive_coinduct''[case_names c_stat_eq c_sim c_ext c_sym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and r_stat_eq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and r_sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and r_ext: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q} \<Longrightarrow> 
                         (\<Psi> \<otimes> \<Psi>', P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  and r_sym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q} \<Longrightarrow> 
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisim_reflexive)
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> P Q)
    thus ?case
      by(blast dest: r_stat_eq bisimE Frame_stat_eq_trans)
  next
    case(c_sim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'_rel_q': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule r_sim)
      moreover from `eqvt X` P'_rel_q' have "eqvt ?X"
	apply(auto simp add: eqvt_def)
	apply(drule_tac p=p in bisim_closed)
	apply(drule_tac p=p in bisim_closed)
	apply(rule_tac x="p \<bullet> P'a" in exI, simp)
	by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
	by(force intro: transitive dest: bisim_transitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using `eqvt ?X`
	by(force intro: transitive dest: bisim_transitive)
    }
    with `(\<Psi>, P, Q) \<in> ?X` show ?case
      by(blast dest: bisimE)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    thus ?case by(rule_tac r_ext)
  next
    case(c_sym \<Psi> P Q)
    thus ?case by(rule_tac r_sym)
  qed
qed

lemma transitive_coinduct[case_names c_stat_eq c_sim c_ext c_sym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and r_stat_eq: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> insert_assertion (extract_frame R) \<Psi>' \<simeq>\<^sub>F insert_assertion (extract_frame S) \<Psi>'"
  and r_sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[({(\<Psi>', R, S) | \<Psi>' R R' S' S. \<Psi>' \<rhd> R \<sim> R' \<and>
                                                                        ((\<Psi>', R', S') \<in> X \<or> \<Psi>' \<rhd> R' \<sim> S') \<and>
                                                                        \<Psi>' \<rhd> S' \<sim> S})] S"
  and r_ext: "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> \<Psi>' \<otimes> \<Psi>'' \<rhd> R \<sim> S"
  and r_sym: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> \<Psi>' \<rhd> S \<sim> R"


  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> (X \<union> bisim)"
    by blast
  moreover from `eqvt X` bisim_eqvt have "eqvt (X \<union> bisim)"
    by auto
  ultimately show ?thesis
  proof(coinduct rule: weak_transitive_coinduct')
    case(c_stat_eq \<Psi> P Q)
    thus ?case
      by(blast intro: r_stat_eq dest: bisimE)
  next
    case(c_sim \<Psi> P Q)
    thus ?case
      apply auto
      apply(blast intro: r_sim)
      apply(drule bisimE(2))
      apply(rule_tac A=bisim in monotonic, simp)
      by(force intro: bisim_reflexive)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    thus ?case
      by(blast dest: bisimE r_ext)
  next
    case(c_sym \<Psi> P Q)
    thus ?case by(blast dest: bisimE r_sym intro: bisim_reflexive)
  qed
qed

lemma transitive_coinduct'[case_names c_stat_eq c_sim c_ext c_sym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and r_stat_eq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and r_sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> (X \<union> bisim) \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and r_ext: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> \<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> Q"
  and r_sym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow>
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> (X \<union> bisim)) \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> (X \<union> bisim)"
    by blast
  moreover from `eqvt X` bisim_eqvt have "eqvt (X \<union> bisim)"
    by auto
  ultimately show ?thesis
  proof(coinduct rule: weak_transitive_coinduct')
    case(c_stat_eq \<Psi> P Q)
    thus ?case
      by(blast intro: r_stat_eq dest: bisimE)
  next
    case(c_sim \<Psi> P Q)
    thus ?case
      apply -
      apply(case_tac "(\<Psi>, P, Q) \<in> X")
      apply(rule_tac r_sim)
      apply simp
      apply(clarify)
      apply(drule bisimE(2))
      apply(rule_tac A=bisim in monotonic, simp)
      by(force intro: bisim_reflexive)
  next
    case(c_ext \<Psi> P Q \<Psi>')
    thus ?case
      by(blast dest: bisimE r_ext)
  next
    case(c_sym \<Psi> P Q)
    thus ?case
      apply auto
      apply(drule r_sym)
      apply auto
      apply(rule_tac x=Q in exI)
      apply(auto intro: bisim_reflexive)
      apply(rule_tac x=P in exI)
      by(auto intro: bisim_reflexive dest: bisimE(4))
  qed
qed

lemma bisim_symmetric:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"
  
  shows "\<Psi> \<rhd> Q \<sim> P"
using assms
by(rule bisimE)

lemma eqvt_trans[intro]:
  assumes "eqvt X"

  shows "eqvt {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> X \<or> \<Psi> \<rhd> P' \<sim> Q') \<and> \<Psi> \<rhd> Q' \<sim> Q}"
using assms
apply(auto simp add: eqvt_def eqvts)
apply(erule_tac x="(a, P', Q')" in ballE, auto)
by(blast dest: bisim_closed)+

lemma eqvt_weak_trans[intro]:
  assumes "eqvt X"

  shows "eqvt {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
using assms
apply(auto simp add: eqvt_def eqvts)
apply(erule_tac x="(a, P', Q')" in ballE, auto)
by(blast dest: bisim_closed)+

end

end


