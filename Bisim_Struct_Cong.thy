theory Bisim_Struct_Cong
  imports Bisim_Pres Sim_Struct_Cong Structural_Congruence
begin

context env begin

lemma bisim_par_comm:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<sim> Q \<parallel> P"
proof -
  let ?X = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)) | xvec \<Psi> P Q. xvec \<sharp>* \<Psi>}"
  
  have "eqvt ?X"
    by(force simp add: eqvt_def pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)

  have "(\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
    apply auto by(rule_tac x="[]" in exI) auto
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> PQ QP)
    from `(\<Psi>, PQ, QP) \<in> ?X`
    obtain xvec P Q where P_frQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and Q_frP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)" and "xvec \<sharp>* \<Psi>"
      by auto

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q"
      by(rule_tac C="(\<Psi>, Q)" in fresh_frame) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P)" in fresh_frame) auto
    from FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" by(force dest: extract_frame_fresh_chain)
    have "\<langle>(xvec@A\<^sub>P@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>(xvec@A\<^sub>Q@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(simp add: frame_chain_append)
        (metis frame_res_chain_pres frame_res_chain_comm frame_nil_stat_eq composition_sym Associativity Commutativity Frame_stat_eq_trans)
    with FrP FrQ P_frQ Q_frP `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>P` `xvec \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>`
    show ?case by(auto simp add: frame_chain_append)
  next
    case(c_sim \<Psi> PQ QP)
    from `(\<Psi>, PQ, QP) \<in> ?X`    
    obtain xvec P Q where P_frQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and Q_frP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
                      and "xvec \<sharp>* \<Psi>"
      by auto
    moreover have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<leadsto>[?X] \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
    proof -
      have "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[?X] Q \<parallel> P"
      proof -
	note `eqvt ?X`
	moreover have "\<And>\<Psi> P Q. (\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
	  apply auto by(rule_tac x="[]" in exI) auto
	moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X"
	  apply(induct xvec, auto)
	  by(rule_tac x="xvec@xveca" in exI) (auto simp add: res_chain_append)
	ultimately show ?thesis by(rule sim_par_comm) 
      qed
      moreover note `eqvt ?X` `xvec \<sharp>* \<Psi>`
      moreover have "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
	apply auto
	by(rule_tac x="x#xvec" in exI) auto
      ultimately show ?thesis by(rule res_chain_pres) 
    qed
    ultimately show ?case by simp
  next
    case(c_ext \<Psi> PQ QP \<Psi>')
    from `(\<Psi>, PQ, QP) \<in> ?X`
    obtain xvec P Q where P_frQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and Q_frP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
                      and "xvec \<sharp>* \<Psi>"
      by auto
    
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>"
               and "(p \<bullet> xvec) \<sharp>* P"
               and "(p \<bullet> xvec) \<sharp>* Q"
               and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinct_perm p"
      by(rule_tac c="(\<Psi>, P, Q, \<Psi>')" in name_list_avoiding) auto

    from `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` S have "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (P \<parallel> Q))"
      by(subst res_chain_alpha) auto
    hence P_q_alpha: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q))"
      by(simp add: eqvts)

    from `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` S have "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (Q \<parallel> P))"
      by(subst res_chain_alpha) auto
    hence Q_p_alpha: "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))"
      by(simp add: eqvts)

    from `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))) \<in> ?X"
      by auto
    with P_frQ Q_frP P_q_alpha Q_p_alpha show ?case by simp
  next
    case(c_sym \<Psi> PR QR)
    thus ?case by blast
  qed
qed

lemma bisim_res_comm:
  fixes x :: name
  and   \<Psi> :: 'b
  and   y :: name
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(cases "x=y")
  case True
  thus ?thesis by(blast intro: bisim_reflexive)
next
  case False
  {
    fix x::name and y::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>"
    let ?X = "{((\<Psi>::'b), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(P::('a, 'b, 'c) psi)), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) | \<Psi> x y P. x \<sharp> \<Psi> \<and> y \<sharp> \<Psi>}"
    from `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
    proof(coinduct rule: bisim_coinduct)
      case(c_stat_eq \<Psi> xyP yxP)
      from `(\<Psi>, xyP, yxP) \<in> ?X` obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "y \<sharp> A\<^sub>P"
	by(rule_tac C="(x, y, \<Psi>)" in fresh_frame) auto
      ultimately show ?case by(force intro: frame_res_comm Frame_stat_eq_trans)
    next
      case(c_sim \<Psi> xyP yxP)
      from `(\<Psi>, xyP, yxP) \<in> ?X` obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      note `x \<sharp> \<Psi>` `y \<sharp> \<Psi>`
      moreover have "eqvt ?X" by(force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      hence "eqvt(?X \<union> bisim)" by auto
      moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?X \<union> bisim" by(blast intro: bisim_reflexive)
      moreover have "\<And>\<Psi> x y P. \<lbrakk>x \<sharp> \<Psi>; y \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?X \<union> bisim" by auto
      ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(rule res_comm)
      with `xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)` `yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)` show ?case
	by simp
    next
      case(c_ext \<Psi> xyP yxP \<Psi>')
      from `(\<Psi>, xyP, yxP) \<in> ?X` obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and xy_peq: "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and yx_peq: "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      show ?case
      proof(case_tac "x=y")
	assume "x = y"
	with xy_peq yx_peq show ?case
	  by(blast intro: bisim_reflexive)
      next
	assume "x \<noteq> y"
	obtain x' where "x' \<sharp> \<Psi>" and "x' \<sharp> \<Psi>'" and "x' \<noteq> x" and "x' \<noteq> y" and "x' \<sharp> P" by(generate_fresh "name") (auto simp add: fresh_prod)
	obtain y' where "y' \<sharp> \<Psi>" and "y' \<sharp> \<Psi>'" and "y' \<noteq> x" and "x' \<noteq> y'" and "y' \<noteq> y" and "y' \<sharp> P" by(generate_fresh "name") (auto simp add: fresh_prod)
	with xy_peq `y' \<sharp> P` `x' \<sharp> P` `x \<noteq> y` `x' \<noteq> y` `y' \<noteq> x` have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))"
	  apply(subst alpha_res[of x']) apply(simp add: abs_fresh) by(subst alpha_res[of y' _ y]) (auto simp add: eqvts calc_atm)
	moreover with yx_peq `y' \<sharp> P` `x' \<sharp> P` `x \<noteq> y` `x' \<noteq> y` `y' \<noteq> x` `x' \<noteq> y'` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y')] \<bullet> [(x, x')] \<bullet> P))"
	  apply(subst alpha_res[of y']) apply(simp add: abs_fresh) by(subst alpha_res[of x' _ x]) (auto simp add: eqvts calc_atm)
	with `x \<noteq> y` `x' \<noteq> y` `y' \<noteq> y` `x' \<noteq> x` `y' \<noteq> x` `x' \<noteq> y'` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))"
	  by(subst perm_compose) (simp add: calc_atm)
	moreover from `x' \<sharp> \<Psi>` `x' \<sharp> \<Psi>'` `y' \<sharp> \<Psi>` `y' \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)), \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))) \<in> ?X"
	  by auto
	ultimately show ?case using xy_peq yx_peq by simp
      qed
    next
      case(c_sym \<Psi> xyP yxP)
      thus ?case by auto
    qed
  }
  moreover obtain x'::name where "x' \<sharp> \<Psi>" and "x' \<sharp> P" and "x' \<noteq> x" and "x' \<noteq> y"
    by(generate_fresh "name") auto
  moreover obtain y'::name where "y' \<sharp> \<Psi>" and "y' \<sharp> P" and "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y'), (x, x')] \<bullet> P)) \<sim> \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y'), (x, x')] \<bullet> P))" by auto
  thus ?thesis using `x' \<sharp> P` `x' \<noteq> x` `x' \<noteq> y` `y' \<sharp> P` `y' \<noteq> x` `y' \<noteq> y` `y' \<noteq> x'` `x \<noteq> y`
    apply(subst alpha_res[where x=x and y=x' and P=P], auto)
    apply(subst alpha_res[where x=y and y=y' and P=P], auto)
    apply(subst alpha_res[where x=x and y=x' and P="\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    apply(subst alpha_res[where x=y and y=y' and P="\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    by(subst perm_compose) (simp add: eqvts calc_atm)
qed

lemma bisim_res_comm':
  fixes x    :: name
  and   \<Psi>   :: 'b
  and   xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<sim> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(induct xvec) (auto intro: bisim_res_comm bisim_reflexive bisim_res_pres bisim_transitive)

lemma bisim_scope_ext:
  fixes x :: name
  and   \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  {
    fix x::name and Q :: "('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> P"
    let ?X1 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) | \<Psi> xvec x P Q. x \<sharp> \<Psi> \<and> x \<sharp> P \<and> xvec \<sharp>* \<Psi>}"
    let ?X2 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) | \<Psi> xvec x P Q. x \<sharp> \<Psi> \<and> x \<sharp> P \<and> xvec \<sharp>* \<Psi>}"
    let ?X = "?X1 \<union> ?X2"

    from `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
      by(auto, rule_tac x="[]" in exI) (auto simp add: fresh_list_nil)
    moreover have "eqvt ?X"
      by(rule eqvt_union)
    (force simp add: eqvt_def eqvts pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] pt_fresh_bij[OF pt_name_inst, OF at_name_inst])+
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
    proof(coinduct rule: transitive_coinduct)
      case(c_stat_eq \<Psi> R T)
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
	assume "(\<Psi>, R, T) \<in> ?X1"
	then obtain xvec x P Q where "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
	  by(rule_tac C="(\<Psi>, x, Q)" in fresh_frame) auto
	moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
	  by(rule_tac C="(\<Psi>, x, A\<^sub>P, \<Psi>\<^sub>P)" in fresh_frame) auto
	moreover from FrQ `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	  by(drule_tac extract_frame_fresh_chain) auto
	moreover from `x \<sharp> P` `x \<sharp> A\<^sub>P` FrP have "x \<sharp> \<Psi>\<^sub>P" by(drule_tac extract_frame_fresh) auto
	ultimately show ?case
	  by(force simp add: frame_chain_append intro: frame_res_comm' Frame_stat_eq_trans frame_res_chain_pres)
      next
	assume "(\<Psi>, R, T) \<notin> ?X1"
	with `(\<Psi>, R, T) \<in> ?X` have "(\<Psi>, R, T) \<in> ?X2" by blast
	then obtain xvec x P Q where "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
	  by(rule_tac C="(\<Psi>, x, Q)" in fresh_frame) auto
	moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
	  by(rule_tac C="(\<Psi>, x, A\<^sub>P, \<Psi>\<^sub>P)" in fresh_frame) auto
	moreover from FrQ `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	  by(drule_tac extract_frame_fresh_chain) auto
	moreover from `x \<sharp> P` `x \<sharp> A\<^sub>P` FrP have "x \<sharp> \<Psi>\<^sub>P" by(drule_tac extract_frame_fresh) auto
	ultimately show ?case
	  apply auto
	  by(force simp add: frame_chain_append intro: frame_res_comm' Frame_stat_eq_trans frame_res_chain_pres Frame_stat_eq_sym)
      qed
    next
      case(c_sim \<Psi> R T)
      let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> ?X \<or> \<Psi> \<rhd> P' \<sim> Q') \<and> \<Psi> \<rhd> Q' \<sim> Q}"
      from `eqvt ?X` have "eqvt ?Y" by blast
      have C1: "\<And>\<Psi> R T y. \<lbrakk>(\<Psi>, R, T) \<in> ?Y; (y::name) \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
      proof -
	fix \<Psi> R T y
	assume "(\<Psi>, R, T) \<in> ?Y"
	then obtain R' T' where "\<Psi> \<rhd> R \<sim> R'" and "(\<Psi>, R', T') \<in> (?X \<union> bisim)" and "\<Psi> \<rhd> T' \<sim> T" by force
	assume "(y::name) \<sharp> \<Psi>" 
	show "(\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
	proof(case_tac "(\<Psi>, R', T') \<in> ?X")
	  assume "(\<Psi>, R', T') \<in> ?X"
	  show ?thesis
	  proof(case_tac "(\<Psi>, R', T') \<in> ?X1")
	    assume "(\<Psi>, R', T') \<in> ?X1"
	    then obtain xvec x P Q where R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)"
                                     and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	      by auto
	    from `\<Psi> \<rhd> R \<sim> R'` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisim_res_pres)
	    moreover from `xvec \<sharp>* \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>\<lparr>\<nu>x\<rparr>(P \<parallel> Q), \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?X1"
	      by(force simp del: res_chain.simps)
	    with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
	    moreover from `\<Psi> \<rhd> T' \<sim> T` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisim_res_pres)
	    ultimately show ?thesis by blast
	  next
	    assume "(\<Psi>, R', T') \<notin> ?X1"
	    with `(\<Psi>, R', T') \<in> ?X` have "(\<Psi>, R', T') \<in> ?X2" by blast
	    then obtain xvec x P Q where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	      by auto
	    from `\<Psi> \<rhd> R \<sim> R'` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisim_res_pres)
	    moreover from `xvec \<sharp>* \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*(y#xvec)\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) \<in> ?X2"
	      by(force simp del: res_chain.simps)
	    with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
	    moreover from `\<Psi> \<rhd> T' \<sim> T` `y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisim_res_pres)
	    ultimately show ?thesis by blast
	  qed
	next
	  assume "(\<Psi>, R', T') \<notin> ?X"
	  with `(\<Psi>, R', T') \<in> ?X \<union> bisim` have "\<Psi> \<rhd> R' \<sim> T'" by blast
	  with `\<Psi> \<rhd> R \<sim> R'` `\<Psi> \<rhd> T' \<sim> T` `y \<sharp> \<Psi>` show ?thesis
	    by(blast dest: bisim_res_pres)
	qed
      qed
      
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
	assume "(\<Psi>, R, T) \<in> ?X1"
	then obtain xvec x P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)"
	proof -
	  have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[?Y] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
	  proof -
	    note `x \<sharp> P` `x \<sharp> \<Psi>` `eqvt ?Y`
	    moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Y" by(blast intro: bisim_reflexive)
	    moreover have "\<And>x \<Psi> P Q xvec. \<lbrakk>x \<sharp> \<Psi>; x \<sharp> P; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?Y"
	    proof -
	      fix x \<Psi> P Q xvec
	      assume "(x::name) \<sharp> (\<Psi>::'b)" and "x \<sharp> (P::('a, 'b, 'c) psi)" and "(xvec::name list) \<sharp>* \<Psi>"
	      from `x \<sharp> \<Psi>` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))"
		by(rule bisim_res_comm')
	      moreover from `xvec \<sharp>* \<Psi>` `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?X \<union> bisim"
		by blast
	      ultimately show "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?Y" 
		by(blast intro: bisim_reflexive)
	    qed
	    moreover have "\<And>\<Psi> xvec P x. \<lbrakk>x \<sharp> \<Psi>; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?Y"
	      by(blast intro: bisim_res_comm' bisim_reflexive)
	    ultimately show ?thesis by(rule scope_ext_left)
	  qed
	  thus ?thesis using `eqvt ?Y` `xvec \<sharp>* \<Psi>` C1 
	    by(rule res_chain_pres)
	qed
	with Req Teq show ?case by simp
      next
	assume "(\<Psi>, R, T) \<notin> ?X1"
	with `(\<Psi>, R, T) \<in> ?X` have "(\<Psi>, R, T) \<in> ?X2" by blast
	then obtain xvec x P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))"
	proof -
	  have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[?Y] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
	  proof -
	    note `x \<sharp> P` `x \<sharp> \<Psi>` `eqvt ?Y`
	    moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Y" by(blast intro: bisim_reflexive)
	    moreover have "\<And>x \<Psi> P Q xvec. \<lbrakk>x \<sharp> \<Psi>; x \<sharp> P; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))) \<in> ?Y"
	    proof -
	      fix x \<Psi> P Q xvec
	      assume "(x::name) \<sharp> (\<Psi>::'b)" and "x \<sharp> (P::('a, 'b, 'c) psi)" and "(xvec::name list) \<sharp>* \<Psi>"
	      from `xvec \<sharp>* \<Psi>` `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) \<in> ?X \<union> bisim"
		by blast
	      moreover from `x \<sharp> \<Psi>` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))"
		by(blast intro: bisim_res_comm' bisimE)
	      ultimately show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))) \<in> ?Y" 
		by(blast intro: bisim_reflexive)
	    qed
	    ultimately show ?thesis by(rule scope_ext_right)
	  qed
	  thus ?thesis using `eqvt ?Y` `xvec \<sharp>* \<Psi>` C1 
	    by(rule res_chain_pres)
	qed
	with Req Teq show ?case by simp
      qed
    next
      case(c_ext \<Psi> R T \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
	assume "(\<Psi>, R, T) \<in> ?X1"
	then obtain xvec x P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'"
	  by(generate_fresh "name", auto simp add: fresh_prod)

	obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
                  and "x \<sharp> (p \<bullet> xvec)" and "y \<sharp> (p \<bullet> xvec)"
                   and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinct_perm p"
	  by(rule_tac c="(\<Psi>, P, Q, x, y, \<Psi>')" in name_list_avoiding) auto
	
	
	from `y \<sharp> P` have "(p \<bullet> y) \<sharp> (p \<bullet> P)" by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
	with S `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` have "y \<sharp> (p \<bullet> P)" by simp
	with `(p \<bullet> xvec) \<sharp>* \<Psi>` `y \<sharp> \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` `y \<sharp> \<Psi>'`
	have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q))), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (\<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q)))) \<in> ?X"
	  by auto
	moreover from Req `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` `x \<sharp> (p \<bullet> xvec)` `y \<sharp> P` `y \<sharp> Q` `x \<sharp> P` S
	have "R = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))"
	  apply(erule_tac rev_mp)
	  apply(subst alpha_res[of y])
	  apply(clarsimp simp add: eqvts)
	  apply(subst res_chain_alpha[of p])
	  by(auto simp add: eqvts)
	moreover from Teq `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` `x \<sharp> (p \<bullet> xvec)` `y \<sharp> P` `y \<sharp> Q` `x \<sharp> P` S
	have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q))"
	  apply(erule_tac rev_mp)
	  apply(subst alpha_res[of y])
	  apply(clarsimp simp add: eqvts)
	  apply(subst res_chain_alpha[of p])
	  by(auto simp add: eqvts)
	ultimately show ?case
	  by blast
      next
	assume "(\<Psi>, R, T) \<notin> ?X1"
	with `(\<Psi>, R, T) \<in> ?X` have "(\<Psi>, R, T) \<in> ?X2" by blast
	then obtain xvec x P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
	  by auto
	obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'"
	  by(generate_fresh "name", auto simp add: fresh_prod)

	obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
                   and "x \<sharp> (p \<bullet> xvec)" and "y \<sharp> (p \<bullet> xvec)"
                   and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinct_perm p"
	  by(rule_tac c="(\<Psi>, P, Q, x, y, \<Psi>')" in name_list_avoiding) auto
	
	from `y \<sharp> P` have "(p \<bullet> y) \<sharp> (p \<bullet> P)" by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
	with S `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` have "y \<sharp> (p \<bullet> P)" by simp
	with `(p \<bullet> xvec) \<sharp>* \<Psi>` `y \<sharp> \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` `y \<sharp> \<Psi>'`
	have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))) \<in> ?X2"
	  by auto
	moreover from Teq `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` `x \<sharp> (p \<bullet> xvec)` `y \<sharp> P` `y \<sharp> Q` `x \<sharp> P` S
	have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))"
	  apply(erule_tac rev_mp)
	  apply(subst alpha_res[of y])
	  apply(clarsimp simp add: eqvts)
	  apply(subst res_chain_alpha[of p])
	  by(auto simp add: eqvts)
	moreover from Req `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `y \<sharp> xvec` `y \<sharp> (p \<bullet> xvec)` `x \<sharp> (p \<bullet> xvec)` `y \<sharp> P` `y \<sharp> Q` `x \<sharp> P` S
	have "R = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q))"
	  apply(erule_tac rev_mp)
	  apply(subst alpha_res[of y])
	  apply(clarsimp simp add: eqvts)
	  apply(subst res_chain_alpha[of p])
	  by(auto simp add: eqvts)
	ultimately show ?case
	  by blast
      qed
    next
      case(c_sym \<Psi> P Q)
      thus ?case
	by(blast dest: bisimE)
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" "y \<sharp> Q"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<sim> P \<parallel> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by auto
  thus ?thesis using assms `y \<sharp> P` `y \<sharp> Q`
    apply(subst alpha_res[where x=x and y=y and P=Q], auto)
    by(subst alpha_res[where x=x and y=y and P="P \<parallel> Q"]) auto
qed

lemma bisim_scope_ext_chain:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>Q)"
using assms
by(induct xvec) (auto intro: bisim_scope_ext bisim_reflexive bisim_transitive bisim_res_pres) 

(* only used for bisim up-to
lemma par_assoc_right:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   R   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' S T U. (\<Psi>, S \<parallel> (T \<parallel> U),(S \<parallel> T) \<parallel> U) \<in> Rel"
  and     C2: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* S\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> (\<lparr>\<nu>*xvec\<rparr>(T \<parallel> U)), \<lparr>\<nu>*xvec\<rparr>((S \<parallel> T) \<parallel> U)) \<in> Rel"
  and     C3: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* U\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> (T \<parallel> U)), (\<lparr>\<nu>*xvec\<rparr>(S \<parallel> T)) \<parallel> U) \<in> Rel"
  and     C4: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<leadsto>[Rel] (P \<parallel> Q) \<parallel> R"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<alpha> PQR) 
  from `bn \<alpha> \<sharp>* (P \<parallel> Q \<parallel> R)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  hence "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
  from `\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> PQR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* (P \<parallel> Q)` `bn \<alpha> \<sharp>* R`
  show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`    
  proof(induct rule: par_cases[where C = "(\<Psi>, P, Q, R, \<alpha>)"])
    case(c_par2 R' A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q)
    from `A\<^sub>P\<^sub>Q \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>P\<^sub>Q \<sharp>* Q" and  "A\<^sub>P\<^sub>Q \<sharp>* R" "A\<^sub>P\<^sub>Q \<sharp>* P"
      by simp+
    with `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` `distinct A\<^sub>P\<^sub>Q`
    obtain A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>P \<Psi>\<^sub>P where "A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q" and "\<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q" and FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and  FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
                           and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac merge_frameE) (auto dest: extract_frame_fresh_chain)
    from `A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q` `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* R` `A\<^sub>P\<^sub>Q \<sharp>* \<alpha>`
    have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>P \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* R" and "A\<^sub>Q \<sharp>* R"
      by simp+
    from `\<Psi> \<otimes> \<Psi>\<^sub>P\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'` `\<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
      by(metis stat_eq_transition Associativity Commutativity Composition)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> (Q \<parallel> R')" using FrQ `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* \<alpha>`
      by(rule_tac Par2) auto
    hence "\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> P \<parallel> (Q \<parallel> R')" using FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
      by(rule_tac Par2) auto
    moreover have "(\<Psi>, P \<parallel> (Q \<parallel> R'),(P \<parallel> Q) \<parallel> R') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par1 PQ A\<^sub>R \<Psi>\<^sub>R)
    from `A\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* \<alpha>"
      by simp+
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    with `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
    with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>R)" by force
    with `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ`
    show ?case using `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q`
    proof(induct rule: par_cases_subject[where C = "(A\<^sub>R, \<Psi>\<^sub>R, P, Q, R, \<Psi>)"])
      case(c_par1 P' A\<^sub>Q \<Psi>\<^sub>Q)
      from `A\<^sub>Q \<sharp>* (A\<^sub>R, \<Psi>\<^sub>R, P, Q, R, \<Psi>)` have "A\<^sub>Q \<sharp>* A\<^sub>R" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>"
	by simp+
      from `A\<^sub>R \<sharp>* Q` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'` have "\<Psi> \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R) \<rhd> P \<longmapsto>\<alpha> \<prec> P'" 
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> P' \<parallel> (Q \<parallel> R)"
        using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
        by(rule_tac Par1[where A\<^sub>Q="A\<^sub>Q@A\<^sub>R"]) auto
      moreover have "(\<Psi>, P' \<parallel> (Q \<parallel> R),(P' \<parallel> Q) \<parallel> R) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(c_par2 Q' A\<^sub>P \<Psi>\<^sub>P)
      from `A\<^sub>P \<sharp>* (A\<^sub>R, \<Psi>\<^sub>R, P, Q, R, \<Psi>)` have "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* R" and "A\<^sub>P \<sharp>* P"  and "A\<^sub>P \<sharp>* Q"  and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>"
	by simp+
      have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      from `A\<^sub>R \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'`
      have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
        by(rule stat_eq_transition) (rule associativity_sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> Q' \<parallel> R"
        using `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
	by(rule_tac Par1) auto
      hence "\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> P \<parallel> (Q' \<parallel> R)"
        using `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* \<alpha>`
        by(rule_tac Par2) auto
      moreover have "(\<Psi>, P \<parallel> (Q' \<parallel> R),(P \<parallel> Q') \<parallel> R) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(c_comm1 \<Psi>\<^sub>Q M N Q' A\<^sub>P \<Psi>\<^sub>P K xvec R' A\<^sub>Q) 
      from `A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` `A\<^sub>P \<sharp>* R` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* K` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
	by(rule_tac output_fresh_chain_derivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N`
	by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by simp
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
	by(metis stat_eq_transition Associativity)
      moreover note `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
              `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* P` `xvec \<sharp>* Q`
	by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
	by(rule C2)
      ultimately show ?case by blast
    next
      case(c_comm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R) 
      from `A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(drule_tac extract_frame_fresh_chain) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^sub>P \<sharp>* Q` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* M` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
	by(rule_tac output_fresh_chain_derivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `xvec \<sharp>* P` `xvec \<sharp>* A\<^sub>P`
	by(rule_tac Par2) auto
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by simp+
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
	by(metis stat_eq_transition Associativity)
      moreover note `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M` have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
              `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* R`
	by(rule_tac Comm2) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
	by(rule C2)
      ultimately show ?case by blast
    qed
  next
    case(c_comm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P K xvec QR' A\<^sub>Q\<^sub>R)
    from `xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'`  
    moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>P` have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note `xvec \<sharp>* Q``xvec \<sharp>* R` `xvec \<sharp>* K`
         `extract_frame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: par_cases_output_frame)
      case(c_par1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(auto dest:  extract_frame_fresh_chain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* P`
	by(rule_tac Comm1) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>R \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
	by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
	by(rule C3)
      ultimately show ?case by blast
    next
      case(c_par2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" by simp+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" by simp
      from `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>Q \<sharp>* P" by simp
      from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by(auto dest: extract_frame_fresh_chain)
      from `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
      have R_trans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where Keq_k': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `distinct A\<^sub>R` `xvec \<sharp>* K` `distinct xvec`
	by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtain_output_prefix) (assumption | force)+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover then obtain M' where Meq_m': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "A\<^sub>Q \<sharp>* M'" and "A\<^sub>R \<sharp>* M'"
        using `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>`
        by(rule_tac B="A\<^sub>Q@A\<^sub>R" in obtain_input_prefix) (assumption | force)+
      note `((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'`
      moreover hence "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> M'"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      moreover with MeqK Keq_k' \<Psi>eq have Meq_k': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M'"
	by(metis stat_eq_ent Associativity Commutativity Composition chan_eq_trans)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using FrP `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K'` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'`
	by(rule_tac input_rename_subject) auto
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* K'` `A\<^sub>Q \<sharp>* \<Psi>`
	by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      proof -
        from R_trans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity stat_eq_transition)
        moreover from MeqK have "(\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K" using \<Psi>eq
	  by(metis stat_eq_ent Associativity Commutativity Composition)
        moreover from Meq_m' have "(\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> M'" using \<Psi>eq
	  by(metis stat_eq_ent Associativity Commutativity Composition)
        moreover note `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* M'`
        ultimately show ?thesis
          by(rule_tac output_rename_subject) auto
      qed
      moreover note FrR
      moreover from Meq_k' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M'"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* K'` `A\<^sub>Q \<sharp>* K'` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
              `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M'` `xvec \<sharp>* P` `xvec \<sharp>* Q`
	by(rule_tac Comm1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
	by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(c_comm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P K QR' A\<^sub>Q\<^sub>R)
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` `xvec \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> K \<leftrightarrow> M" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>N\<rparr> \<prec> QR'` `extract_frame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: par_cases_input_frame)
      case(c_par1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
	by(metis stat_eq_ent Associativity Commutativity Composition)
      moreover from `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>`  `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* Q`
	by(rule_tac Comm2) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
	by(rule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
	by(rule C3)
      ultimately show ?case by blast
    next
      case(c_par2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq 
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have R_trans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where Keq_k': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `distinct A\<^sub>R`
	by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtain_input_prefix) (assumption | force)+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover from MeqK Keq_k' \<Psi>eq have Meq_k': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> K'" and Meq_k: "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
	by(metis stat_eq_ent Associativity Commutativity Composition)+
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` FrR `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(auto dest: extract_frame_fresh_chain)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using FrP `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K'`
	by(rule_tac output_rename_subject) auto
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` `A\<^sub>Q\<^sub>R \<sharp>* xvec` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* K'` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>`
	by(rule_tac Par1) (assumption | force)+
      moreover from FrP `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from R_trans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity stat_eq_transition)
      moreover note FrR
      moreover from Keq_k' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'"
	by(metis stat_eq_ent Associativity Commutativity Composition chan_eq_trans)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* K'` `A\<^sub>Q \<sharp>* K'` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
              `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `xvec \<sharp>* R`
	by(rule_tac Comm2) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
	by(metis C1 C4)
      ultimately show ?case by blast
    qed
  qed
qed
*)
lemma bisim_par_assoc:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) | \<Psi> xvec P Q R. xvec \<sharp>* \<Psi>}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  have "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
    by(auto, rule_tac x="[]" in exI) auto
  moreover have "eqvt ?X" by(force simp add: eqvt_def simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)
  ultimately show ?thesis
  proof(coinduct rule: weak_transitive_coinduct')
    case(c_stat_eq \<Psi> PQR PQR')
    from `(\<Psi>, PQR, PQR') \<in> ?X` obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and "PQR = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and "PQR' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R"
      by(rule_tac C="(\<Psi>, Q, R)" in fresh_frame) auto
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* R"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, R)" in fresh_frame) auto
    moreover obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>Q)" in fresh_frame) auto
    moreover from FrQ `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
      by(drule_tac extract_frame_fresh_chain) auto
    moreover from FrR `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extract_frame_fresh_chain) auto
    moreover from FrR `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extract_frame_fresh_chain) auto
    ultimately show ?case using fresh_comp_chain
      by auto (metis frame_chain_append composition_sym Associativity frame_nil_stat_eq frame_res_chain_pres)
  next
    case(c_sim \<Psi> T S)
    from `(\<Psi>, T, S) \<in> ?X` obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and T_eq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and S_eq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    from `eqvt ?X`have "eqvt ?Y" by blast
    have C1: "\<And>\<Psi> T S yvec. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; yvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y"
    proof -
      fix \<Psi> T S yvec
      assume "(\<Psi>, T, S) \<in> ?Y"
      then obtain T' S' where "\<Psi> \<rhd> T \<sim> T'" and "(\<Psi>, T', S') \<in> ?X" and "\<Psi> \<rhd> S' \<sim> S" by force
      assume "(yvec::name list) \<sharp>* \<Psi>" 
      from `(\<Psi>, T', S') \<in> ?X` obtain xvec P Q R where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and S'eq: "S' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
                                                  and "xvec \<sharp>* \<Psi>"
	by auto
      from `\<Psi> \<rhd> T \<sim> T'` `yvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>T \<sim> \<lparr>\<nu>*yvec\<rparr>T'" by(rule bisim_res_chain_pres)
      moreover from `xvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*(yvec@xvec)\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*(yvec@xvec)\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X"
	by force
      with T'eq S'eq have "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T', \<lparr>\<nu>*yvec\<rparr>S') \<in> ?X" by(simp add: res_chain_append)
      moreover from `\<Psi> \<rhd> S' \<sim> S` `yvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>S' \<sim> \<lparr>\<nu>*yvec\<rparr>S" by(rule bisim_res_chain_pres)
      ultimately show "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y" by blast
    qed
    have C2: "\<And>\<Psi> T S y. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; y \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>T, \<lparr>\<nu>y\<rparr>S) \<in> ?Y"
      by(drule_tac yvec="[y]" in C1) auto

    have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
    proof -
      have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[?Y] P \<parallel> (Q \<parallel> R)" 
      proof -
	note `eqvt ?Y`
	moreover have "\<And>\<Psi> P Q R. (\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
	proof -
	  fix \<Psi> P Q R
	  have "(\<Psi>::'b, ((P::('a, 'b, 'c) psi) \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
	    by(auto, rule_tac x="[]" in exI) auto
	  thus "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
	    by(blast intro: bisim_reflexive)
	qed
	moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
	proof -
	  fix xvec \<Psi> P Q R
	  assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (P::('a, 'b, 'c) psi)"
	  from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
	  moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))"
	    by(rule bisim_scope_ext_chain)
	  ultimately show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
	    by(blast intro: bisim_reflexive)
	qed
	moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* R\<rbrakk> \<Longrightarrow> (\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"
	proof -
	  fix xvec \<Psi> P Q R
	  assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (R::('a, 'b, 'c) psi)"
	  have "\<Psi> \<rhd> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisim_par_comm)
	  moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisim_scope_ext_chain)
	  hence "\<Psi> \<rhd> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q))" by(rule bisimE)
	  moreover from `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
	    by(metis bisim_res_chain_pres bisim_par_comm)
	  moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
	  ultimately show "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"  by(blast dest: bisim_transitive intro: bisim_reflexive)
	qed
	ultimately show ?thesis using C1
	  by(rule par_assoc_left)
      qed
      thus ?thesis using `eqvt ?Y` `xvec \<sharp>* \<Psi>` C2
	by(rule res_chain_pres)
    qed
    with T_eq S_eq show ?case by simp
  next
    case(c_ext \<Psi> T S \<Psi>')
    from `(\<Psi>, T, S) \<in> ?X` obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and T_eq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and S_eq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* R" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinct_perm p"
      by(rule_tac c="(\<Psi>, P, Q, R, \<Psi>')" in name_list_avoiding) auto

    from `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))) \<in> ?X"
      by auto
    moreover from T_eq `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* R` S have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R))"
      apply auto by(subst res_chain_alpha[of p]) auto
    moreover from S_eq `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* R` S have "S = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))"
      apply auto by(subst res_chain_alpha[of p]) auto
    ultimately show ?case by simp
  next
    case(c_sym \<Psi> T S)
    from `(\<Psi>, T, S) \<in> ?X` obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and T_eq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and S_eq: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) = S"
      by auto
    
    from `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P)"
      by(metis bisim_par_comm bisim_par_pres bisim_transitive bisim_res_chain_pres)
    moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P), \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P))) \<in> ?X" by blast
    moreover from `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      by(metis bisim_par_comm bisim_par_pres bisim_transitive bisim_res_chain_pres)
    ultimately show ?case using T_eq S_eq by(blast dest: bisim_transitive)
  qed
qed    

lemma bisim_par_nil:
  fixes P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> \<zero> \<sim> P"
proof -
  let ?X1 = "{(\<Psi>, P \<parallel> \<zero>, P) | \<Psi> P. True}"
  let ?X2 = "{(\<Psi>, P, P \<parallel> \<zero>) | \<Psi> P. True}"
  let ?X = "?X1 \<union> ?X2"
  have "eqvt ?X" by(auto simp add: eqvt_def)
  have "(\<Psi>, P \<parallel> \<zero>, P) \<in> ?X" by simp
  thus ?thesis
  proof(coinduct rule: bisim_weak_coinduct)
    case(c_stat_eq \<Psi> Q R)
    show ?case
    proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
      assume "(\<Psi>, Q, R) \<in> ?X1"
      then obtain P where "Q = P \<parallel> \<zero>" and "R = P" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
	by(rule fresh_frame)
      ultimately show ?case
	apply auto by(metis frame_res_chain_pres frame_nil_stat_eq Identity Associativity Assertion_stat_eq_trans Commutativity)
    next
      assume "(\<Psi>, Q, R) \<notin> ?X1"
      with `(\<Psi>, Q, R) \<in> ?X` have "(\<Psi>, Q, R) \<in> ?X2" by blast
      then obtain P where "Q = P" and "R = P \<parallel> \<zero>" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
	by(rule fresh_frame)
      ultimately show ?case
	apply auto by(metis frame_res_chain_pres frame_nil_stat_eq Identity Associativity Assertion_stat_eq_trans Assertion_stat_eq_sym Commutativity)
    qed
  next
    case(c_sim \<Psi> Q R)
    thus ?case using `eqvt ?X`
      by(auto intro: par_nil_left par_nil_right)
  next
    case(c_ext \<Psi> Q R \<Psi>')
    thus ?case by auto
  next
    case(c_sym \<Psi> Q R)
    thus ?case by auto
  qed
qed

lemma bisim_res_nil:
  fixes x :: name
  and   \<Psi> :: 'b
  
  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
proof -
  {
    fix x::name
    assume "x \<sharp> \<Psi>"
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
    proof -
      let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X2 = "{(\<Psi>, \<zero>, \<lparr>\<nu>x\<rparr>\<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X = "?X1 \<union> ?X2"

      from `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) \<in> ?X" by auto
      thus ?thesis
      proof(coinduct rule: bisim_weak_coinduct)
	case(c_stat_eq \<Psi> P Q)
	thus ?case using fresh_comp by(force intro: frame_res_fresh Frame_stat_eq_sym)
      next
	case(c_sim \<Psi> P Q)
	thus ?case
	  by(force intro: res_nil_left res_nil_right)
      next
	case(c_ext \<Psi> P Q \<Psi>')
	obtain y where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<noteq> x"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	show ?case
	proof(case_tac "(\<Psi>, P, Q) \<in> ?X1")
	  assume "(\<Psi>, P, Q) \<in> ?X1"
	  then obtain x where "P = \<lparr>\<nu>x\<rparr>\<zero>" and "Q = \<zero>" by auto
	  moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alpha_res) auto
	  ultimately show ?case using `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` by auto
	next
	  assume "(\<Psi>, P, Q) \<notin> ?X1"
	  with `(\<Psi>, P, Q) \<in> ?X` have "(\<Psi>, P, Q) \<in> ?X2" by auto
	  then obtain x where "Q = \<lparr>\<nu>x\<rparr>\<zero>" and "P = \<zero>" by auto
	  moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alpha_res) auto
	  ultimately show ?case using `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` by auto
	qed
      next
	case(c_sym \<Psi> P Q)
	thus ?case by auto
      qed
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>\<zero> \<sim> \<zero>" by auto
  thus ?thesis by(subst alpha_res[where x=x and y=y]) auto
qed

lemma bisim_output_push_res:
  fixes x :: name
  and   \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> M"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" by(rule_tac eqvt_union) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+
    from `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> N`  have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisim_coinduct)
      case(c_stat_eq \<Psi> Q R)
      thus ?case using fresh_comp by(force intro: frame_res_fresh Frame_stat_eq_sym)
    next
      case(c_sim \<Psi> Q R)
      thus ?case using `eqvt ?X`
	by(force intro: output_push_res_left output_push_res_right bisim_reflexive)
    next
      case(c_ext \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
	assume "(\<Psi>, Q, R) \<in> ?X1"
	then obtain x M N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Req: "R = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	
	moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
	moreover from Qeq `x \<sharp> M` `y \<sharp> M` `x \<sharp> N` `y \<sharp> N` `y \<sharp> P` have "Q = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	moreover from Req `y \<sharp> P` have "R = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	ultimately show ?case by blast
      next
	assume "(\<Psi>, Q, R) \<notin> ?X1"
	with `(\<Psi>, Q, R) \<in> ?X` have "(\<Psi>, Q, R) \<in> ?X2" by blast
	then obtain x M N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Qeq: "Q = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	
	moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
	moreover from Req `x \<sharp> M` `y \<sharp> M` `x \<sharp> N` `y \<sharp> N` `y \<sharp> P` have "R = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	moreover from Qeq `y \<sharp> P` have "Q = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	ultimately show ?case by blast
      qed
    next
      case(c_sym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" "y \<sharp> P"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  thus ?thesis using assms `y \<sharp> P` `y \<sharp> M` `y \<sharp> N`
    apply(subst alpha_res[where x=x and y=y and P=P], auto)
    by(subst alpha_res[where x=x and y=y and P="M\<langle>N\<rangle>.P"]) auto
qed

lemma bisim_input_push_res:
  fixes x    :: name
  and   \<Psi>    :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" and "x \<sharp> xvec"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" by(rule_tac eqvt_union) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+

    from `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> N` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) \<in> ?X" by blast
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisim_coinduct)
      case(c_stat_eq \<Psi> Q R)
      thus ?case using fresh_comp by(force intro: frame_res_fresh Frame_stat_eq_sym)
    next
      case(c_sim \<Psi> Q R)
      thus ?case using `eqvt ?X`
        by(auto intro!: input_push_res_left input_push_res_right intro: bisim_reflexive)
    next
      case(c_ext \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
	assume "(\<Psi>, Q, R) \<in> ?X1"
	then obtain x M xvec N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Req: "R = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
                                   and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	
	moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by force
	moreover from Qeq `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec` `y \<sharp> xvec` `x \<sharp> N` `y \<sharp> N` `y \<sharp> P` have "Q = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts input_chain_fresh)
	moreover from Req `y \<sharp> P` have "R = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	ultimately show ?case by blast
      next
	assume "(\<Psi>, Q, R) \<notin> ?X1"
	with `(\<Psi>, Q, R) \<in> ?X` have "(\<Psi>, Q, R) \<in> ?X2" by blast
	then obtain x M xvec N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Qeq: "Q = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
                                   and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
	  by(generate_fresh "name") (auto simp add: fresh_prod)

	moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by force
	moreover from Req `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec` `y \<sharp> xvec` `x \<sharp> N` `y \<sharp> N` `y \<sharp> P` have "R = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts input_chain_fresh)
	moreover from Qeq `y \<sharp> P` have "Q = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	ultimately show ?case by blast
      qed
    next
      case(c_sym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  thus ?thesis using assms `y \<sharp> P` `y \<sharp> M` `y \<sharp> N` `y \<sharp> xvec`
    apply(subst alpha_res[where x=x and y=y and P=P], auto)
    by(subst alpha_res[where x=x and y=y and P="M\<lparr>\<lambda>*xvec N\<rparr>.P"]) (auto simp add: input_chain_fresh eqvts)
qed

lemma bisim_case_push_res:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "x \<sharp> (map fst Cs)"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  {
    fix x::name and Cs::"('c \<times> ('a, 'b, 'c) psi) list"
    assume "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X2 = "{(\<Psi>, Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs), \<lparr>\<nu>x\<rparr>(Cases Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" apply(rule_tac eqvt_union) 
      apply(auto simp add: eqvt_def eqvts)
      apply(rule_tac x="p \<bullet> x" in exI)
      apply(rule_tac x="p \<bullet> Cs" in exI)
      apply(perm_extend_simp)
      apply(auto simp add: eqvts)
      apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(simp add: eqvts)
      apply(perm_extend_simp)
      apply(simp add: eqvts)
      apply(rule_tac x="p \<bullet> x" in exI)
      apply(rule_tac x="p \<bullet> Cs" in exI)
      apply auto
      apply(perm_extend_simp)
      apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(simp add: eqvts)
      apply(perm_extend_simp)
      by(simp add: eqvts)    
    
    from `x \<sharp> \<Psi>` `x \<sharp> map fst Cs` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    proof(coinduct rule: bisim_coinduct)
      case(c_stat_eq \<Psi> Q R)
      thus ?case using fresh_comp by(force intro: frame_res_fresh Frame_stat_eq_sym)
    next
      case(c_sim \<Psi> Q R)
      thus ?case using `eqvt ?X`
	by(force intro: case_push_res_left case_push_res_right bisim_reflexive)
    next
      case(c_ext \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
	assume "(\<Psi>, Q, R) \<in> ?X1"
	then obtain x Cs where Qeq: "Q = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Req: "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
                           and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	from `y \<sharp> Cs` `x \<sharp> (map fst Cs)` have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)

	moreover with `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
	  by auto
	moreover from Qeq `y \<sharp> Cs` have "Q = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	moreover from Req `y \<sharp> Cs` `x \<sharp> (map fst Cs)` have "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))" 
	  by(induct Cs arbitrary: R) (auto simp add: fresh_list_cons fresh_prod alpha_res)
	ultimately show ?case by blast
      next
	assume "(\<Psi>, Q, R) \<notin> ?X1"
	with `(\<Psi>, Q, R) \<in> ?X` have "(\<Psi>, Q, R) \<in> ?X2" by blast
	then obtain x Cs where Req: "R = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Qeq: "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
                           and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
	obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
	  by(generate_fresh "name") (auto simp add: fresh_prod)
	from `y \<sharp> Cs` `x \<sharp> (map fst Cs)` have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)
	
	moreover with `y \<sharp> \<Psi>` `y \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
	  by auto
	moreover from Req `y \<sharp> Cs` have "R = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
	  apply auto by(subst alpha_res[of y]) (auto simp add: eqvts)
	moreover from Qeq `y \<sharp> Cs` `x \<sharp> (map fst Cs)` have "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))" 
	  by(induct Cs arbitrary: Q) (auto simp add: fresh_list_cons fresh_prod alpha_res)
	ultimately show ?case by blast
      qed
    next
      case(c_sym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> Cs" by(generate_fresh "name") auto
  moreover from `x \<sharp> map fst Cs` have "y \<sharp> map fst([(x, y)] \<bullet> Cs)" 
    by(induct Cs) (auto simp add: fresh_left calc_atm)
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))"
    by auto
  moreover from `y \<sharp> Cs` have "\<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) =  \<lparr>\<nu>x\<rparr>(Cases Cs)"
    by(simp add: alpha_res eqvts)
  moreover from `x \<sharp> map fst Cs` `y \<sharp> Cs` have "Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs)) = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: alpha_res)
  ultimately show ?thesis by auto
qed

lemma bang_ext:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  assumes "guarded P"

  shows "\<Psi> \<rhd> !P \<sim> P \<parallel> !P"
proof -
  let ?X = "{(\<Psi>, !P, P \<parallel> !P) | \<Psi> P. guarded P} \<union> {(\<Psi>, P \<parallel> !P, !P) | \<Psi> P. guarded P}"
  from `guarded P` have "(\<Psi>, !P, P \<parallel> !P) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisim_coinduct)
    case(c_stat_eq \<Psi> Q R)
    from `(\<Psi>, Q, R) \<in> ?X` obtain P where Eq: "(Q = !P \<and> R = P \<parallel> !P) \<or> (Q = P \<parallel> !P \<and> R = !P)" and "guarded P"
      by auto
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule fresh_frame)
    from FrP `guarded P` have "\<Psi>\<^sub>P \<simeq> S_bottom'" by(blast dest: guarded_stat_eq)
    from `\<Psi>\<^sub>P \<simeq> S_bottom'` have "\<Psi> \<otimes> S_bottom' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> S_bottom'" by(metis Identity Composition Assertion_stat_eq_trans Commutativity Assertion_stat_eq_sym)
    hence "\<langle>A\<^sub>P, \<Psi> \<otimes> S_bottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> S_bottom'\<rangle>"
      by(force intro: frame_res_chain_pres)
    moreover from `A\<^sub>P \<sharp>* \<Psi>` have "\<langle>\<epsilon>, \<Psi> \<otimes> S_bottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> S_bottom'\<rangle>"
      by(rule_tac Frame_stat_eq_sym) (force intro: frame_res_fresh_chain)
    ultimately show ?case using Eq `A\<^sub>P \<sharp>* \<Psi>` FrP
      by auto (blast dest: Frame_stat_eq_trans Frame_stat_eq_sym)+
  next
    case(c_sim \<Psi> Q R)
    thus ?case by(auto intro: bang_ext_left bang_ext_right bisim_reflexive)
  next
    case(c_ext \<Psi> Q R)
    thus ?case by auto
  next
    case(c_sym \<Psi> Q R)
    thus ?case by auto
  qed
qed
  
lemma bisim_par_pres_sym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
using assms
by(metis bisim_par_comm bisim_par_pres bisim_transitive)

lemma bisim_scope_ext_sym:
  fixes x :: name
  and   Q :: "('a, 'b, 'c) psi"
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>x\<rparr>P) \<parallel> Q"
using assms
by(metis bisim_scope_ext bisim_transitive bisim_par_comm bisim_symmetric bisim_res_pres)

lemma bisim_scope_ext_chain_sym:
  fixes xvec :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>*xvec\<rparr>P) \<parallel> Q"
using assms
by(induct xvec) (auto intro: bisim_scope_ext_sym bisim_reflexive bisim_transitive bisim_res_pres)

lemma bisim_par_pres_aux_sym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
  and     "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
using assms
by(metis bisim_par_comm bisim_par_pres_aux bisim_transitive)

lemma bang_nontau_derivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "\<Psi> \<rhd> P \<sim> Q"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "guarded Q"
  and     "\<alpha> \<noteq> \<tau>"

  obtains \<pi>' Q' R T where "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                   and "((supp R)::name set) \<subseteq> supp P'" and "((supp T)::name set) \<subseteq> supp Q'"
proof -
  from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "guarded P" apply - by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'") (auto simp add: psi.inject)
  assume "\<And>\<pi>' Q' R T. \<lbrakk>\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'; \<Psi> \<rhd> P' \<sim> R \<parallel> !P; \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q; \<Psi> \<rhd> R \<sim> T; ((supp R)::name set) \<subseteq> supp P';
                    ((supp T)::name set) \<subseteq> supp Q'\<rbrakk> \<Longrightarrow> thesis"
  moreover from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `\<Psi> \<rhd> P \<sim> Q` `guarded Q`  `\<alpha> \<noteq> \<tau>`
  have "\<exists>Q' \<pi>' T R . \<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha>  \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and> \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and> \<Psi> \<rhd> R \<sim> T \<and>
                  ((supp R)::name set) \<subseteq> supp P' \<and> ((supp T)::name set) \<subseteq> supp Q'"
  proof(nominal_induct avoiding: Q rule: bang_induct')
    case(c_alpha \<pi> \<alpha> P' p Q)
    moreover have "\<alpha> \<noteq> \<tau>" using `(p\<bullet>\<alpha>) \<noteq> \<tau>`
      by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
    ultimately obtain Q' \<pi>' T R where Q_trans: "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from Q_trans have "distinct(bn \<alpha>)" by(rule bound_output_distinct)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from Q_trans `bn(p \<bullet> \<alpha>) \<sharp>* Q` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "bn(p \<bullet> \<alpha>) \<sharp>* Q'"
      by(drule_tac free_fresh_chain_derivative) simp+
    with Q_trans `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` S `bn \<alpha> \<sharp>* subject \<alpha>` have "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> Q')"
      by(force simp add: residual_alpha)
    moreover from `\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P') \<sim> (p \<bullet> (R \<parallel> (P \<parallel> !P)))"
      by(rule bisim_closed)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* P` S have "\<Psi> \<rhd> (p \<bullet> P') \<sim> (p \<bullet> R) \<parallel> (P \<parallel> !P)"
      by(simp add: eqvts)
    moreover from `\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> (T \<parallel> !Q))"
      by(rule bisim_closed)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* Q` S have "\<Psi> \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> T) \<parallel> !Q"
      by(simp add: eqvts)
    moreover from `\<Psi> \<rhd> R \<sim> T` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(rule bisim_closed)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` S have "\<Psi> \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(simp add: eqvts)
    moreover from suppR have "((supp(p \<bullet> R))::name set) \<subseteq> supp(p \<bullet> P')"
      apply(erule_tac rev_mp)
      by(subst subset_closed[of p, symmetric]) (simp add: eqvts)
    moreover from suppT have "((supp(p \<bullet> T))::name set) \<subseteq> supp(p \<bullet> Q')"
      apply(erule_tac rev_mp)
      by(subst subset_closed[of p, symmetric]) (simp add: eqvts)
    ultimately show ?case by blast
  next
    case(c_par1 \<pi> \<alpha> P' Q)
    from `\<Psi> \<rhd> P \<sim> Q` `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` 
    obtain \<pi>' Q' where Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(blast dest: bisimE simE)
    from Q_trans have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
    hence "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> (Q' \<parallel> !Q)" using `bn \<alpha> \<sharp>* Q`
      by(drule_tac Par1[where Q="!Q"]) (assumption|simp add: option.map_ident)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>map_option (F_assert o push_prov) \<pi>' @ \<alpha> \<prec> (Q' \<parallel> !Q)" using `guarded Q` by(rule Bang)
    moreover from `guarded P` have "\<Psi> \<rhd> P' \<parallel> !P \<sim> P' \<parallel> (P \<parallel> !P)" by(metis bang_ext bisim_par_pres_sym)
    moreover have "\<Psi> \<rhd> Q' \<parallel> !Q \<sim> Q' \<parallel> !Q" by(rule bisim_reflexive)
    ultimately show ?case using `\<Psi> \<rhd> P' \<sim> Q'` by(force simp add: psi.supp)
  next
    case(c_par2 \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P Q)
    then obtain Q' \<pi>' T R where Q_trans: "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    note Q_trans
    from `\<Psi> \<rhd> P' \<sim> R \<parallel> !P` have "\<Psi> \<rhd> P \<parallel> P' \<sim> R \<parallel> (P \<parallel> !P)"
      by(metis bisim_par_pres_sym bisim_par_comm bisim_transitive bisim_par_assoc)
    with Q_trans show ?case using `\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q` `\<Psi> \<rhd> R \<sim> T` suppR suppT
      by(force simp add: psi.supp)
  next
    case(c_comm1 M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' Q)
    thus ?case by blast
  next
    case(c_comm2 M xvec N P' K P'' Q)
    thus ?case by blast
  next
    case(c_bang \<pi> \<alpha> P' Q)
    then obtain Q' \<pi>' T R where Q_trans: "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from `\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)` `guarded P` have "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" by(metis bang_ext bisim_par_pres_sym bisim_transitive bisim_symmetric)
    with Q_trans show ?case using `\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q` `\<Psi> \<rhd> R \<sim> T` suppR suppT
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma bang_tau_derivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     "\<Psi> \<rhd> P \<sim> Q"
  and     "guarded Q"

  obtains Q' R T where "\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                   and "((supp R)::name set) \<subseteq> supp P'" and "((supp T)::name set) \<subseteq> supp Q'"
proof -
  from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<tau> \<prec> P'` have "guarded P" apply - by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<tau> \<prec> P'") (auto simp add: psi.inject)
  assume "\<And>Q' R T. \<lbrakk>\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> Q'; \<Psi> \<rhd> P' \<sim> R \<parallel> !P; \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q; \<Psi> \<rhd> R \<sim> T; ((supp R)::name set) \<subseteq> supp P';
                    ((supp T)::name set) \<subseteq> supp Q'\<rbrakk> \<Longrightarrow> thesis"
  moreover from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<tau> \<prec> P'` `\<Psi> \<rhd> P \<sim> Q` `guarded Q` 
  have "\<exists>Q' T R . \<Psi> \<rhd> !Q \<longmapsto>None @ \<tau>  \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and> \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and> \<Psi> \<rhd> R \<sim> T \<and>
                  ((supp R)::name set) \<subseteq> supp P' \<and> ((supp T)::name set) \<subseteq> supp Q'"
  proof(nominal_induct avoiding: Q rule: bang_tau_induct)
    case(c_par1 \<pi> P' Q)
    have "bn(\<tau>) \<sharp>* \<Psi>" and "bn(\<tau>) \<sharp>* Q" by simp_all
    with `\<Psi> \<rhd> P \<sim> Q` `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'`
    obtain \<pi>' Q' where Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<tau> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(blast dest: bisimE simE)
    from Q_trans have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi>' @ \<tau> \<prec> Q'" by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
    hence "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<pi>' @ \<tau> \<prec> (Q' \<parallel> !Q)"
      by(drule_tac Par1[where Q="!Q"]) (assumption|simp add: option.map_ident)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>map_option (F_assert o push_prov) \<pi>' @ \<tau> \<prec> (Q' \<parallel> !Q)" using `guarded Q` by(rule Bang)
    hence "\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> (Q' \<parallel> !Q)"
      by(metis tau_no_provenance')
    moreover from `guarded P` have "\<Psi> \<rhd> P' \<parallel> !P \<sim> P' \<parallel> (P \<parallel> !P)" by(metis bang_ext bisim_par_pres_sym)
    moreover have "\<Psi> \<rhd> Q' \<parallel> !Q \<sim> Q' \<parallel> !Q" by(rule bisim_reflexive)
    ultimately show ?case using `\<Psi> \<rhd> P' \<sim> Q'` by(force simp add: psi.supp)
  next
    case(c_par2 \<pi> P' A\<^sub>P \<Psi>\<^sub>P Q)
    then obtain Q' \<pi>' T R where Q_trans: "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<tau> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    note Q_trans
    from `\<Psi> \<rhd> P' \<sim> R \<parallel> !P` have "\<Psi> \<rhd> P \<parallel> P' \<sim> R \<parallel> (P \<parallel> !P)"
      by(metis bisim_par_pres_sym bisim_par_comm bisim_transitive bisim_par_assoc)
    with tau_no_provenance'[OF Q_trans] show ?case using `\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q` `\<Psi> \<rhd> R \<sim> T` suppR suppT
      by(force simp add: psi.supp)
  next
    case(c_comm1 M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' Q)
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<rhd> Q \<leadsto>[bisim] P" by(metis bisimE)
    with `\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'` obtain \<pi> Q' where Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      by(force dest: simE)
    from Q_trans have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'" by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
    from Q_trans obtain A\<^sub>Q \<Psi>\<^sub>Q tvec K' where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* yvec" and "A\<^sub>Q \<sharp>* zvec" and "A\<^sub>Q \<sharp>* tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* Q" and "tvec \<sharp>* P" and "tvec \<sharp>* M" and "tvec \<sharp>* N" and "tvec \<sharp>* xvec" and "tvec \<sharp>* yvec" and "tvec \<sharp>* zvec" and "distinct tvec" and "distinct A\<^sub>Q" and \<pi>: "\<pi> = Some(\<langle>A\<^sub>Q; tvec, K'\<rangle>)" and "\<Psi> \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'"
      by(drule_tac C="(\<Psi>, Q, M, P, xvec, yvec, zvec)" in input_provenance) auto
    have "tvec \<sharp>* \<Psi>\<^sub>Q" using `tvec \<sharp>* Q` `A\<^sub>Q \<sharp>* tvec` FrQ
      by(auto dest: extract_frame_fresh_chain)
    have "zvec \<sharp>* \<Psi>\<^sub>Q" using `zvec \<sharp>* Q` `A\<^sub>Q \<sharp>* zvec` FrQ
      by(auto dest: extract_frame_fresh_chain)
    have "zvec \<sharp>* K'" using `zvec \<sharp>* Q` Q_trans `A\<^sub>Q \<sharp>* zvec` `tvec \<sharp>* zvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    have "xvec \<sharp>* K'" using `xvec \<sharp>* Q` Q_trans `A\<^sub>Q \<sharp>* xvec` `tvec \<sharp>* xvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    note FrQ
    moreover from FrQ `guarded Q` have "\<Psi>\<^sub>Q \<simeq> S_bottom'" by(blast dest: guarded_stat_eq)
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'" using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'`
      by (metis Assertion_stat_eq_def Associativity Identity stat_eq_ent)
    from `\<Psi> \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''` `\<Psi>\<^sub>Q \<simeq> S_bottom'`
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)      
    hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
      using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'` `zvec \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* M`
      `distinct zvec` `zvec \<sharp>* P` `A\<^sub>Q \<sharp>* zvec` `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* K'`
      apply(subst frame_res_chainbase[symmetric])
      by(rule_tac comm1_aux[where A\<^sub>P=A\<^sub>Q]) (auto intro!: Frame_stat_imp_refl)
    hence "\<Psi> \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''" using `\<Psi>\<^sub>Q \<simeq> S_bottom'`
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)
    with `xvec \<sharp>* K'` `\<Psi> \<rhd> P \<sim> Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* Q` `guarded Q`
    obtain Q'' \<pi>' T R where Q_trans': "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''"
      by(rule_tac bang_nontau_derivative) auto
    from Q_trans' `\<Psi>\<^sub>Q \<simeq> S_bottom'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''"
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)
    then obtain uvec M' where "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* Q" and "uvec \<sharp>* P" and "uvec \<sharp>* M" and "uvec \<sharp>* N" and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* zvec" and "uvec \<sharp>* tvec" and "distinct uvec" and \<pi>': "\<pi>' = Some(\<langle>([]); uvec, M'\<rangle>)" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K'" and "uvec \<sharp>* A\<^sub>Q"
      unfolding residual_inject
      by(drule_tac C="(\<Psi>, \<Psi>\<^sub>Q,Q, M, P, xvec, yvec, zvec,tvec,A\<^sub>Q)" in output_provenance) auto
    hence "\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'"
      by(metis Associativity associativity_sym stat_eq_ent)
    have "A\<^sub>Q \<sharp>* M'" using `A\<^sub>Q \<sharp>* Q` Q_trans' `uvec \<sharp>* A\<^sub>Q`
      unfolding \<pi>'
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)    
    have "tvec \<sharp>* M'" using `tvec \<sharp>* Q` Q_trans' `uvec \<sharp>* tvec`
      unfolding \<pi>'
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)
    with `\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'` FrQ `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `distinct tvec` `A\<^sub>Q \<sharp>* tvec` `tvec \<sharp>* \<Psi>` `\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'` `A\<^sub>Q \<sharp>* M'` `tvec \<sharp>* Q`
    have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M'\<lparr>N\<rparr> \<prec> Q'"
      unfolding \<pi>
      by(rule_tac comm2_aux[where A\<^sub>Q="[]" and A\<^sub>P="[]"]) (assumption|auto)+
    moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K'` `\<Psi>\<^sub>Q \<simeq> S_bottom'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K'" by(metis stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* M` `xvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>Q` `tvec \<sharp>* Q`
       `uvec \<sharp>* \<Psi>` `uvec \<sharp>* Q`
      unfolding \<pi> \<pi>'
      by(rule_tac Comm1) (assumption | simp)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using `guarded Q` by(drule_tac Bang) auto
    moreover from `\<Psi> \<rhd> P'' \<sim> R \<parallel> !P` `guarded P` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisim_par_pres_sym bang_ext bisim_transitive bisim_par_assoc bisim_symmetric bisim_res_chain_pres)
    with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisim_scope_ext_chain_sym bisim_transitive psi_fresh_vec)
    moreover from `\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisim_par_pres_sym bisim_transitive bisim_par_assoc bisim_symmetric bisim_res_chain_pres bisim_scope_ext_chain_sym psi_fresh_vec)
    moreover from `\<Psi> \<rhd> R \<sim> T` `\<Psi> \<rhd> Q' \<sim> P'` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisim_par_pres_sym bisim_transitive bisim_res_chain_pres bisim_par_comm bisimE(4))
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp res_chain_supp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp res_chain_supp)
    ultimately show ?case by blast
  next
    case(c_comm2 M xvec N P' K A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' Q)
    from `\<Psi> \<rhd> P \<sim> Q` have "\<Psi> \<rhd> Q \<leadsto>[bisim] P" by(metis bisimE)
    with `\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q`
    obtain \<pi> Q' where Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      by(force dest: simE)
    from Q_trans have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
    from Q_trans obtain A\<^sub>Q \<Psi>\<^sub>Q tvec K' where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* yvec" and "A\<^sub>Q \<sharp>* zvec" and "A\<^sub>Q \<sharp>* tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* Q" and "tvec \<sharp>* P" and "tvec \<sharp>* M" and "tvec \<sharp>* N" and "tvec \<sharp>* xvec" and "tvec \<sharp>* yvec" and "tvec \<sharp>* zvec" and "distinct tvec" and "distinct A\<^sub>Q" and \<pi>: "\<pi> = Some(\<langle>A\<^sub>Q; tvec, K'\<rangle>)" and "\<Psi> \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M"
      unfolding residual_inject
      by(drule_tac C="(\<Psi>, Q, M, P, xvec, yvec, zvec)" in output_provenance) auto
    have "tvec \<sharp>* \<Psi>\<^sub>Q" using `tvec \<sharp>* Q` `A\<^sub>Q \<sharp>* tvec` FrQ
      by(auto dest: extract_frame_fresh_chain)
    have "zvec \<sharp>* \<Psi>\<^sub>Q" using `zvec \<sharp>* Q` `A\<^sub>Q \<sharp>* zvec` FrQ
      by(auto dest: extract_frame_fresh_chain)
    have "zvec \<sharp>* K'" using `zvec \<sharp>* Q` Q_trans `A\<^sub>Q \<sharp>* zvec` `tvec \<sharp>* zvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    have "xvec \<sharp>* K'" using `xvec \<sharp>* Q` Q_trans `A\<^sub>Q \<sharp>* xvec` `tvec \<sharp>* xvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    note FrQ
    moreover from FrQ `guarded Q` have "\<Psi>\<^sub>Q \<simeq> S_bottom'" by(blast dest: guarded_stat_eq)
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M" using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M`
      by (metis Assertion_stat_eq_def Associativity Identity stat_eq_ent)
    from `\<Psi> \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K\<lparr>N\<rparr> \<prec> P''` `\<Psi>\<^sub>Q \<simeq> S_bottom'`
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K\<lparr>N\<rparr> \<prec> P''"
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)      
    hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K'\<lparr>N\<rparr> \<prec> P''"
      using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M` `zvec \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* M`
      `distinct zvec` `zvec \<sharp>* P` `A\<^sub>Q \<sharp>* zvec` `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* K'`
      apply(subst frame_res_chainbase[symmetric])
      by(rule_tac comm2_aux[where A\<^sub>P=A\<^sub>Q]) (auto intro!: Frame_stat_imp_refl)
    hence "\<Psi> \<rhd> !P \<longmapsto> Some (\<langle>\<epsilon>, \<langle>zvec, M\<rangle>\<rangle>) @ K'\<lparr>N\<rparr> \<prec> P''" using `\<Psi>\<^sub>Q \<simeq> S_bottom'`
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)
    with `xvec \<sharp>* K'` `\<Psi> \<rhd> P \<sim> Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* Q` `guarded Q`
    obtain Q'' \<pi>' T R where Q_trans': "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>N\<rparr> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''"
      by(rule_tac bang_nontau_derivative) auto
    from Q_trans' `\<Psi>\<^sub>Q \<simeq> S_bottom'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>N\<rparr> \<prec> Q''"
      by(metis stat_eq_transition Identity composition_sym Assertion_stat_eq_sym)
    then obtain uvec M' where "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* Q" and "uvec \<sharp>* P" and "uvec \<sharp>* M" and "uvec \<sharp>* N" and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* zvec" and "uvec \<sharp>* tvec" and "distinct uvec" and \<pi>': "\<pi>' = Some(\<langle>([]); uvec, M'\<rangle>)" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M'" and "uvec \<sharp>* A\<^sub>Q"
      by(drule_tac C="(\<Psi>, \<Psi>\<^sub>Q,Q, M, P, xvec, yvec, zvec,tvec,A\<^sub>Q)" in input_provenance) auto
    hence "\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
      by(metis Associativity associativity_sym stat_eq_ent)
    have "A\<^sub>Q \<sharp>* M'" using `A\<^sub>Q \<sharp>* Q` Q_trans' `uvec \<sharp>* A\<^sub>Q`
      unfolding \<pi>'
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)    
    have "tvec \<sharp>* M'" using `tvec \<sharp>* Q` Q_trans' `uvec \<sharp>* tvec`
      unfolding \<pi>'
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)
    with `\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` FrQ `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `distinct tvec` `A\<^sub>Q \<sharp>* tvec` `tvec \<sharp>* \<Psi>` `\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'` `A\<^sub>Q \<sharp>* M'` `tvec \<sharp>* Q`
    have "\<Psi> \<otimes> S_bottom' \<rhd> Q \<longmapsto>\<pi> @ M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      unfolding \<pi>
      by(rule_tac comm1_aux[where A\<^sub>Q="[]" and A\<^sub>P="[]"]) (assumption|auto)+
    moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M'` `\<Psi>\<^sub>Q \<simeq> S_bottom'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M'" by(metis stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* M` `xvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<pi>' @ K'\<lparr>N\<rparr> \<prec> Q''` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>Q` `tvec \<sharp>* Q`
       `uvec \<sharp>* \<Psi>` `uvec \<sharp>* Q`
      unfolding \<pi> \<pi>'
      by(rule_tac Comm2) (assumption | simp)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using `guarded Q` by(drule_tac Bang) auto
    moreover from `\<Psi> \<rhd> P'' \<sim> R \<parallel> !P` `guarded P` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisim_par_pres_sym bang_ext bisim_transitive bisim_par_assoc bisim_symmetric bisim_res_chain_pres)
    with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisim_scope_ext_chain_sym bisim_transitive psi_fresh_vec)
    moreover from `\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisim_par_pres_sym bisim_transitive bisim_par_assoc bisim_symmetric bisim_res_chain_pres bisim_scope_ext_chain_sym psi_fresh_vec)
    moreover from `\<Psi> \<rhd> R \<sim> T` `\<Psi> \<rhd> Q' \<sim> P'` `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisim_par_pres_sym bisim_transitive bisim_res_chain_pres bisim_par_comm bisimE(4))
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp res_chain_supp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp res_chain_supp)
    ultimately show ?case by blast
  next
    case(c_bang \<pi> P' Q)
    then obtain Q' T R where Q_trans: "\<Psi> \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from `\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)` `guarded P` have "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" by(metis bang_ext bisim_par_pres_sym bisim_transitive bisim_symmetric)
    with Q_trans show ?case using `\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q` `\<Psi> \<rhd> R \<sim> T` suppR suppT
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma bang_derivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "\<Psi> \<rhd> P \<sim> Q"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "guarded Q"

  obtains \<pi>' Q' R T where "\<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                   and "((supp R)::name set) \<subseteq> supp P'" and "((supp T)::name set) \<subseteq> supp Q'"
  using assms
  by(cases "\<alpha> = \<tau>") (auto intro: bang_nontau_derivative bang_tau_derivative)

lemma struct_cong_bisim:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim> Q"
using assms
by(induct rule: struct_cong.induct)
  (auto intro: bisim_reflexive bisim_symmetric bisim_transitive bisim_par_comm bisim_par_assoc bisim_par_nil bisim_res_nil bisim_res_comm bisim_scope_ext bisim_case_push_res bisim_input_push_res bisim_output_push_res bang_ext)

lemma bisim_bang_pres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "guarded P"
  and     "guarded Q"

  shows "\<Psi> \<rhd> !P \<sim> !Q"
proof -
  let ?X = "{(\<Psi>, R \<parallel> !P, R \<parallel> !Q) | \<Psi> P Q R. \<Psi> \<rhd> P \<sim> Q \<and> guarded P \<and> guarded Q}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from assms have "(\<Psi>, \<zero> \<parallel> !P, \<zero> \<parallel> !Q) \<in> ?X" by(blast intro: bisim_reflexive)

  moreover have "eqvt ?X" 
    apply(auto simp add: eqvt_def)
    apply(drule_tac p=p in bisim_closed)
    by force
  ultimately have "\<Psi> \<rhd> \<zero> \<parallel> !P \<sim> \<zero> \<parallel> !Q"
  proof(coinduct rule: weak_transitive_coinduct)
    case(c_stat_eq \<Psi> P Q)
    thus ?case by auto
  next
    case(c_sim \<Psi> RP RQ)
    from `(\<Psi>, RP, RQ) \<in> ?X` obtain P Q R where "\<Psi> \<rhd> P \<sim> Q" and "guarded P" and "guarded Q"
                                           and "RP = R \<parallel> !P" and "RQ = R \<parallel> !Q"
      by auto
    note `\<Psi> \<rhd> P \<sim> Q` 
    moreover from `eqvt ?X` have "eqvt ?Y" by blast
    moreover note `guarded P` `guarded Q` bisimE(2) bisimE(3) bisimE(4) stat_eq_bisim bisim_closed bisim_par_assoc[THEN bisim_symmetric] 
                  bisim_par_pres bisim_par_pres_aux_sym bisim_res_chain_pres bisim_scope_ext_chain_sym bisim_transitive
    moreover have "\<And>\<Psi> P Q R T. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Y; \<Psi> \<rhd> R \<sim> T\<rbrakk> \<Longrightarrow> (\<Psi>, P, T) \<in> ?Y"
      by auto (metis bisim_transitive)
    moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; guarded P; guarded Q\<rbrakk> \<Longrightarrow> (\<Psi>, R \<parallel> !P, R \<parallel> !Q) \<in> ?Y" by(blast intro: bisim_reflexive)
    moreover have "\<And>\<Psi> P \<pi> \<alpha> P' Q. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; \<Psi> \<rhd> P \<sim> Q; bn \<alpha> \<sharp>* \<Psi>;  bn \<alpha> \<sharp>* P;  bn \<alpha> \<sharp>* Q; guarded Q; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                         \<exists>\<pi>' Q' R T.  \<Psi> \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and>  \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and>
                                                   \<Psi> \<rhd> R \<sim> T \<and> ((supp R)::name set) \<subseteq> supp P' \<and> 
                                                   ((supp T)::name set) \<subseteq> supp Q'"
      by(blast elim: bang_derivative)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[?Y] R \<parallel> !Q"
      by(rule bang_pres)
    with `RP = R \<parallel> !P` `RQ = R \<parallel> !Q` show ?case
      by blast
  next
    case(c_ext \<Psi> RP RQ \<Psi>')
    thus ?case by(blast dest: bisimE)
  next
    case(c_sym \<Psi> RP RQ)
    thus ?case by(blast dest: bisimE)
  qed
  thus ?thesis
    by(metis bisim_transitive bisim_par_nil bisim_symmetric bisim_par_comm)
qed

end

end

