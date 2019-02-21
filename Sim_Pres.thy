theory Sim_Pres
  imports Simulation
begin

context env begin

lemma input_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes P_relQ: "\<And>Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> \<pi> Q'
  assume "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
  thus "\<exists>\<pi> P'. \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: input_cases) (auto intro: Input P_relQ)
qed

lemma output_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a

  assumes P_relQ: "(\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<leadsto>[Rel] M\<langle>N\<rangle>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> \<pi> Q'
  assume "\<Psi> \<rhd> M\<langle>N\<rangle>.Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
  thus "\<exists>\<pi> P'. \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: output_cases) (auto intro: Output P_relQ)
qed

lemma case_pres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes P_relQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and          "Rel \<subseteq> Rel'"

  shows "\<Psi> \<rhd> Cases CsP \<leadsto>[Rel'] Cases CsQ"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> \<pi> Q'
  assume "\<Psi> \<rhd> Cases CsQ \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* CsP" and "bn \<alpha> \<sharp>* \<Psi>"
  thus "\<exists>\<pi> P'. \<Psi> \<rhd> Cases CsP \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel'"
  proof(induct rule: case_cases)
    case(c_case \<phi> Q \<pi>')
    from `(\<phi>, Q) mem CsQ` obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "(\<Psi>, P, Q) \<in> Rel"
      by(metis P_relQ)
    from `(\<Psi>, P, Q) \<in> Rel` have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
    moreover from `bn \<alpha> \<sharp>* CsP` `(\<phi>, P) mem CsP` have "bn \<alpha> \<sharp>* P"
      by(drule_tac mem_fresh_chain) auto
    moreover note `\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>`
    ultimately obtain \<pi>'' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'" and P'_rel_q': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: simE)
    from P_trans `(\<phi>, P) mem CsP` `\<Psi> \<turnstile> \<phi>` `guarded P` have "\<Psi> \<rhd> Cases CsP \<longmapsto>map_option (F_assert o push_prov) \<pi>'' @ \<alpha> \<prec> P'"
      by(rule Case)
    moreover from P'_rel_q' `Rel \<subseteq> Rel'` have "(\<Psi>, P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed

lemma res_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes P_simQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel'"
  and     "x \<sharp> \<Psi>"
  and     "Rel \<subseteq> Rel'"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto>[Rel'] \<lparr>\<nu>x\<rparr>Q"
proof -
  note `eqvt Rel'` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)+
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[where C="()"])
    case(c_sim \<pi> \<alpha> Q') 
    from `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P` `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" by simp+
    from `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> Q'`  `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` 
         `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>`
    show ?case
    proof(induct rule: res_cases)
      case(c_open M \<pi>' xvec1 xvec2 y N Q')
      from `bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` have "xvec1 \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" and "xvec2 \<sharp>* \<Psi>" by simp+
      from `bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "xvec1 \<sharp>* P" and "y \<sharp> P" and "xvec2 \<sharp>* P" by simp+
      from `x \<sharp> (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from P_simQ `\<Psi> \<rhd> Q \<longmapsto>Some \<pi>' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')` 
           `xvec1 \<sharp>* \<Psi>` `xvec2 \<sharp>* \<Psi>` `xvec1 \<sharp>* P` `xvec2 \<sharp>* P`
      obtain \<pi>'' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'" and P'_rel_q': "(\<Psi>, P', ([(x, y)] \<bullet> Q')) \<in> Rel"
	by(force dest: simE)
      from `\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'`
      obtain \<pi>''' where \<pi>'': "\<pi>'' = Some \<pi>'''"
        unfolding residual_inject        
        by(auto dest: output_provenance)
      from `y \<in> supp N` `x \<noteq> y` have "x \<in> supp([(x, y)] \<bullet> N)" 
	by(drule_tac pt_set_bij2[OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"]) (simp add: eqvts calc_atm)
      with P_trans `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>''') @ M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'"
        unfolding \<pi>''
	by(rule_tac Open)
      hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>([(x, y)] \<bullet> Some(\<lparr>\<nu>x\<rparr>\<pi>''')) @ ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'))"
	by(rule eqvts)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `y \<sharp> P` `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec1` `y \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec2` `x \<noteq> y`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>([(x, y)] \<bullet> Some(\<lparr>\<nu>x\<rparr>\<pi>''')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(simp add: eqvts calc_atm alpha_res)
      moreover from P'_rel_q' `Rel \<subseteq> Rel'` `eqvt Rel'` have "([(y, x)] \<bullet> \<Psi>, [(y, x)] \<bullet> P', [(y, x)] \<bullet> [(x, y)] \<bullet> Q') \<in> Rel'"
	by(force simp add: eqvt_def)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "(\<Psi>, [(x, y)] \<bullet> P', Q') \<in> Rel'" by(simp add: name_swap)
      ultimately show ?case by blast
    next
      case(c_res \<pi>' Q')
      from P_simQ `\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
      obtain \<pi>'' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'" and P'_rel_q': "(\<Psi>, P', Q') \<in> Rel"
	by(blast dest: simE)
      from P_trans `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi>'' @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
	by(rule Scope)
      moreover from P'_rel_q' `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma res_chain_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes P_simQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q"
using `xvec \<sharp>* \<Psi>`
proof(induct xvec)
  case Nil
  from P_simQ show ?case by simp
next
  case(Cons x xvec)
  from `(x#xvec) \<sharp>* \<Psi>` have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by simp+
  from `xvec \<sharp>* \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q" by(rule Cons)
  moreover note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "Rel \<subseteq> Rel" by simp
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)" using C1
    by(rule res_pres)
  thus ?case by simp
qed


lemma par_pres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes P_relQ: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> (\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" 
  and     Eqvt: "eqvt Rel"
  and     Eqvt': "eqvt Rel'"

  and     Stat_imp: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> insert_assertion (extract_frame T) \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion (extract_frame S) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     Ext: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"


  and     C1: "\<And>\<Psi>' S T A\<^sub>U \<Psi>\<^sub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extract_frame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
using Eqvt'
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> QR)
  from `bn \<alpha> \<sharp>* (P \<parallel> R)` `bn \<alpha> \<sharp>* (Q \<parallel> R)`
  have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R"
    by simp+
  from `\<Psi> \<rhd> Q \<parallel> R \<longmapsto>\<pi> @ \<alpha> \<prec> QR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>`
  show ?case
  proof(induct rule: par_cases[where C = "(P, R)"])
    case(c_par1 Q' \<pi>' A\<^sub>R \<Psi>\<^sub>R)
    from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P" by simp
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` FrR
    have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
    from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto>[Rel] Q"
      by(blast intro: Sim P_relQ)
    moreover have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" by fact
    ultimately obtain P' \<pi>'' where P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'"
                           and P'_rel_q': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
    using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>R` `bn \<alpha> \<sharp>* P`
      by(force dest: simE)
    from P_trans Q_trans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
      by(blast dest: free_fresh_chain_derivative)+
    from P_trans `bn \<alpha> \<sharp>* R` FrR  `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* \<alpha>` have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>append_at_end_prov_option \<pi>'' A\<^sub>R @ \<alpha> \<prec> (P' \<parallel> R)"
      by(rule_tac Par1) 
    moreover from P'_rel_q' FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* Q'` have "(\<Psi>, P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 R' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
    from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, \<alpha>, R)"
      by(rule fresh_frame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* R"
      by simp+
    have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from `A\<^sub>Q \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(drule_tac extract_frame_fresh_chain) auto

    from FrP FrQ `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>`
    have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha> \<sharp>* \<Psi>\<^sub>Q"
      by(force dest: extract_frame_fresh_chain)+
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi>, P, Q, A\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, \<alpha>, R)" and "distinct A\<^sub>R"
      by(rule fresh_frame)
    then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* A\<^sub>Q" and  "A\<^sub>R \<sharp>* A\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* R"
      by simp+

    from `A\<^sub>Q \<sharp>* R`  FrR `A\<^sub>R \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extract_frame_fresh_chain) auto
    from `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` FrR  have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extract_frame_fresh_chain) auto

    have R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi>' @ \<alpha> \<prec> R'" by fact
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym Frame_stat_eq_sym)
      moreover from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q`
      have "(insert_assertion (extract_frame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F (insert_assertion (extract_frame P) (\<Psi> \<otimes> \<Psi>\<^sub>R))"
	by(blast intro: P_relQ Stat_imp)
      with FrP FrQ `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>" using fresh_comp_chain by auto
      moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
	by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym frame_int_associativity[THEN Frame_stat_eq_sym])
      ultimately show ?thesis
	by(rule Frame_stat_eq_imp_compose)
     qed
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>\<pi>' @ \<alpha> \<prec> R'"
      using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>`
            `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>` FrR `distinct A\<^sub>R`
      by(force intro: transfer_frame)
    with `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>`  `A\<^sub>P \<sharp>* R`  `A\<^sub>P \<sharp>* \<alpha>` FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>append_at_front_prov_option \<pi>' A\<^sub>P @ \<alpha> \<prec> (P \<parallel> R')"
      by(rule_tac Par2) auto
    moreover obtain A\<^sub>R' \<Psi>\<^sub>R' where "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac fresh_frame[where C="(\<Psi>, P, Q)"]) auto

    moreover from R_trans FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha>  \<sharp>* P` `bn \<alpha>  \<sharp>* Q` `bn \<alpha>  \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and Fr_r': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                           and "bn(p \<bullet> \<alpha>) \<sharp>* R" and "bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(p \<bullet> \<alpha>) \<sharp>* P" and "bn(p \<bullet> \<alpha>) \<sharp>* Q" and "bn(p \<bullet> \<alpha>) \<sharp>* R"
                           and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, Q, R)" and C'="(\<Psi>, P, Q, R)" in expand_frame) (assumption | simp)+

    from `A\<^sub>R \<sharp>* \<Psi>` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
    from `A\<^sub>R \<sharp>* P` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* P` `bn(p \<bullet> \<alpha>) \<sharp>* P` S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
    from `A\<^sub>R \<sharp>* Q` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `bn \<alpha> \<sharp>* Q` `bn(p \<bullet> \<alpha>) \<sharp>* Q` S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp

    from FrR have "(p \<bullet> extract_frame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
    with `bn \<alpha> \<sharp>* R` `bn(p \<bullet> \<alpha>) \<sharp>* R` S have "extract_frame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(simp add: eqvts)

    with `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q` have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), P, Q) \<in> Rel" by(rule_tac P_relQ)

    hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule Ext)
    with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P, Q) \<in> Rel" by(blast intro: C3 Associativity composition_sym)
    with Fr_r' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* Q` have "(\<Psi>, P \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) 
    ultimately show ?case by blast
  next
    case(c_comm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R yvec zvec)
    have  FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+
    from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    
    from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
  
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, M, N, K, R, P, xvec,yvec,zvec)" and "distinct A\<^sub>P"
      by(rule fresh_frame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* R"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* K" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* xvec"
      and "A\<^sub>P \<sharp>* yvec" and "A\<^sub>P \<sharp>* zvec"
      by simp+
    have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> Q'" and R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      by fact+
    from FrP FrR `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* xvec` `xvec \<sharp>* P`
    have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P"
      by(force dest!: extract_frame_fresh_chain)+
  
    from R_trans FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* xvec` `xvec \<sharp>* R` `xvec \<sharp>* Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* Q`
      `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `xvec \<sharp>* K` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* R` `xvec \<sharp>* R` `A\<^sub>R \<sharp>* P` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* xvec` `zvec \<sharp>* xvec` `zvec \<sharp>* A\<^sub>R`
      `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `xvec \<sharp>* \<Psi>\<^sub>P` `distinct xvec` `xvec \<sharp>* M`
    obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and Fr_r': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
      and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
      and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* K" and "(p \<bullet> xvec) \<sharp>* R"
      and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P"
      and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* N" and dp: "distinct_perm p" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* xvec" and "(p \<bullet> xvec) \<sharp>* zvec"
      by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P)" and C'="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P,zvec)" in expand_frame) 
        (assumption | simp)+
    from `A\<^sub>R \<sharp>* \<Psi>` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
    from `A\<^sub>R \<sharp>* P` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
    from `A\<^sub>R \<sharp>* Q` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp
    from `A\<^sub>R \<sharp>* R` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> R)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `xvec \<sharp>* R` `(p \<bullet> xvec) \<sharp>* R` S have "(p \<bullet> A\<^sub>R) \<sharp>* R" by simp
    from `A\<^sub>R \<sharp>* K` have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> K)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `xvec \<sharp>* K` `(p \<bullet> xvec) \<sharp>* K` S have "(p \<bullet> A\<^sub>R) \<sharp>* K" by simp
    
    from `A\<^sub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* M` S have "A\<^sub>P \<sharp>* (p \<bullet> M)" by(simp add: fresh_chain_simps)
    from `A\<^sub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* M` S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by(simp add: fresh_chain_simps)
    from `A\<^sub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>R` S have "(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P" by(simp add: fresh_chain_simps)
    from `A\<^sub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` S have "(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q" by(simp add: fresh_chain_simps)
    have "A\<^sub>P \<sharp>* (p\<bullet>\<Psi>\<^sub>R)" using S `A\<^sub>P \<sharp>* xvec` `(p\<bullet>xvec) \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R`
      by(simp add: fresh_chain_simps)
    from Q_trans S `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
      by(rule_tac input_perm_frame_subject) (simp add: fresh_star_def)+
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have Q_trans: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
      by(simp add: eqvts)

    from FrR have "(p \<bullet> extract_frame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
    with `xvec \<sharp>* R` `(p \<bullet> xvec) \<sharp>* R` S have FrR: "extract_frame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(simp add: eqvts)
    from R_trans have "(p \<bullet> xvec) \<sharp>* R'" using `(p\<bullet>xvec) \<sharp>* R` `(p\<bullet>xvec) \<sharp>* N` `distinct xvec` `(p\<bullet>xvec) \<sharp>* xvec` `xvec \<sharp>* K`
      by(auto dest!: output_fresh_chain_derivative)
    from R_trans have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto> Some (\<langle>(p\<bullet>A\<^sub>R); zvec, (p\<bullet>M)\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      using S `xvec \<sharp>* \<Psi>` `(p\<bullet>xvec) \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>Q` `(p\<bullet>xvec) \<sharp>* \<Psi>\<^sub>Q` `xvec \<sharp>* K` `(p\<bullet>xvec) \<sharp>* K`
            dp `xvec \<sharp>* R` `(p\<bullet>xvec) \<sharp>* R` `(p\<bullet>xvec) \<sharp>* N` `(p\<bullet>xvec) \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* R'` `(p \<bullet> xvec) \<sharp>* zvec` `zvec \<sharp>* xvec`
      by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts residual_inject bound_output_chain_alpha''[symmetric])
    moreover note FrR
    moreover from FrR `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q` have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<leadsto>[Rel] Q"
      by(metis Sim P_relQ)
    with Q_trans obtain \<pi> P' where P_trans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" and P'_rel_q': "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), P', Q') \<in> Rel"
      by(force dest: simE)
    from P_trans `A\<^sub>P \<sharp>* P` have "A\<^sub>P \<sharp>* \<pi>" by(rule trans_fresh_provenance)    
    from P_trans Q_trans `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* Q` `A\<^sub>R' \<sharp>* N` have "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
      by(blast dest: input_fresh_chain_derivative)+
    from P_trans `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<pi>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* (p\<bullet>\<Psi>\<^sub>R)` `A\<^sub>P \<sharp>* (p \<bullet> M)`
    obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* (p\<bullet>M)" and "tvec \<sharp>* P" and "tvec \<sharp>* N" and "tvec \<sharp>* P'" and "tvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)" and "tvec \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* tvec" and MeqK: "(\<Psi> \<otimes> (p\<bullet>\<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P \<turnstile> (p\<bullet>M) \<leftrightarrow> K'" and "tvec \<sharp>* A\<^sub>R" and "tvec \<sharp>* zvec" and "tvec \<sharp>* \<Psi>\<^sub>P" and "tvec \<sharp>* R" and "tvec \<sharp>* xvec" and "tvec \<sharp>* (p\<bullet>A\<^sub>R)"
      by(frule_tac input_provenance'[where C="(\<Psi>,\<Psi>\<^sub>R,p\<bullet>\<Psi>\<^sub>R,A\<^sub>R,p\<bullet>A\<^sub>R,R,zvec,\<Psi>\<^sub>P,xvec)"]) auto

    from P_trans have P_trans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; tvec, K'\<rangle>) @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
      unfolding \<pi> .
    have "zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)" using `zvec \<sharp>* xvec` `zvec \<sharp>* \<Psi>\<^sub>R` `(p\<bullet>xvec) \<sharp>* zvec` S
      by(simp add: fresh_chain_simps)
    have  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact    
    from MeqK have "(\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R))  \<turnstile> (p \<bullet> M) \<leftrightarrow> K'"
      by(metis stat_eq_ent Associativity associativity_sym)
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
    proof -
      have "\<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
        by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      moreover from FrR `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q`
      have "(insert_assertion (extract_frame Q) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<hookrightarrow>\<^sub>F (insert_assertion (extract_frame P) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)))"
        by(metis P_relQ Stat_imp)
      with FrP FrQ `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q` S
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle>" using fresh_comp_chain
        by(simp add: fresh_chain_simps)
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
        by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      ultimately show ?thesis by(rule_tac Frame_stat_eq_imp_compose)
    qed
    moreover note `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P`  `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q` `(p \<bullet> A\<^sub>R) \<sharp>* R` `(p \<bullet> A\<^sub>R) \<sharp>* K`
      `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* (p \<bullet> M)` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* (p \<bullet> M)` `A\<^sub>P \<sharp>* xvec` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* R`
    moreover have "(p\<bullet>A\<^sub>R) \<sharp>* \<Psi>\<^sub>P" using `(p\<bullet>A\<^sub>R) \<sharp>* A\<^sub>P` `(p\<bullet>A\<^sub>R) \<sharp>* P` FrP
      by(auto dest: extract_frame_fresh_chain)
    moreover have "(p\<bullet>A\<^sub>R) \<sharp>* \<Psi>\<^sub>Q" using `(p\<bullet>A\<^sub>R) \<sharp>* A\<^sub>Q` `(p\<bullet>A\<^sub>R) \<sharp>* Q` FrQ
      by(auto dest: extract_frame_fresh_chain)
    moreover have "(p\<bullet>A\<^sub>R) \<sharp>* K'" using P_trans
      `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P` `tvec \<sharp>* (p \<bullet> A\<^sub>R)`
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    moreover from `distinct A\<^sub>R` have "distinct(p \<bullet> A\<^sub>R)" by simp
    moreover note `distinct zvec`
    moreover from `zvec \<sharp>* A\<^sub>R` have "(p\<bullet>A\<^sub>R) \<sharp>* zvec"
      using S `zvec \<sharp>* xvec` `(p\<bullet>xvec) \<sharp>* zvec`
      by(subst (asm) perm_bool[where pi=p,symmetric]) (simp add: eqvts)
    moreover note `zvec \<sharp>* \<Psi>` `zvec \<sharp>* R`
    moreover have "zvec \<sharp>* \<Psi>\<^sub>P" using `zvec \<sharp>* (P,R)` `A\<^sub>P \<sharp>* zvec` FrP
      by(auto dest: extract_frame_fresh_chain)
    moreover have "zvec \<sharp>* K'" using `zvec \<sharp>* (P,R)` P_trans
      `A\<^sub>P \<sharp>* zvec` `tvec \<sharp>* zvec`
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    moreover from `A\<^sub>P \<sharp>* zvec` have "zvec \<sharp>* A\<^sub>P" by simp
    moreover note `zvec \<sharp>* A\<^sub>Q`
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some (\<langle>(p\<bullet>A\<^sub>R); zvec, (p\<bullet>M)\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      by(rule_tac comm1_aux) assumption+    
    with P_trans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* R`
      `xvec \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* (p \<bullet> M)` `(p \<bullet> A\<^sub>R) \<sharp>* K'` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P`
      `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>P` `tvec \<sharp>* R` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)` `zvec \<sharp>* (P,R)`
      by(rule_tac Comm1) (assumption | simp)+    
    moreover from P'_rel_q' have  "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
    with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel" by(metis C3 Associativity composition_sym)
    with Fr_r' `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
    with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
    ultimately show ?case by blast
  next
    case(c_comm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R yvec zvec)
    have  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+

    have  FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+

    from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, M, N, K, R, P, xvec, yvec, zvec)" and "distinct A\<^sub>P"
      by(rule fresh_frame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* R"
      and "A\<^sub>P \<sharp>* N" "A\<^sub>P \<sharp>* K" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* P"  and "A\<^sub>P \<sharp>* xvec" and "A\<^sub>P \<sharp>* yvec"
      and "A\<^sub>P \<sharp>* zvec" 
      by simp+

    from FrP FrR `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* xvec` `xvec \<sharp>* P`
    have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P"
      by(force dest!: extract_frame_fresh_chain)+

    have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
    note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'` FrR
    moreover from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto>[Rel] Q" by(metis P_relQ Sim)
    with Q_trans obtain P' \<pi> where P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and P'_rel_q': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
      using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>R` `xvec \<sharp>* P`
      by(force dest: simE)
    from P_trans Q_trans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* xvec` `xvec \<sharp>* M` `distinct xvec` have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
      by(blast dest: output_fresh_chain_derivative)+
    from P_trans `A\<^sub>P \<sharp>* P` have "A\<^sub>P \<sharp>* \<pi>" by(rule trans_fresh_provenance)
    from P_trans `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* P` `distinct A\<^sub>P`
      `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* \<pi>`
    obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* M" and "tvec \<sharp>* P" and "tvec \<sharp>* N" and "tvec \<sharp>* P'" and "tvec \<sharp>* A\<^sub>R" and "tvec \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* tvec" and "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M" and "tvec \<sharp>* zvec" and "tvec \<sharp>* \<Psi>\<^sub>P" and "tvec \<sharp>* R"
      unfolding residual_inject
      by(frule_tac output_provenance'[where C="(\<Psi>,A\<^sub>R,\<Psi>\<^sub>R,\<Psi>\<^sub>P,N,P,P',zvec,R)"]) auto
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"
      by(metis Associativity associativity_sym stat_eq_ent)
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
	by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      moreover from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q`
      have "(insert_assertion (extract_frame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F (insert_assertion (extract_frame P) (\<Psi> \<otimes> \<Psi>\<^sub>R))"
	by(metis P_relQ Stat_imp)
      with FrP FrQ `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>" using fresh_comp_chain by simp
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
	by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      ultimately show ?thesis by(rule_tac Frame_stat_eq_imp_compose)
    qed
    moreover note `distinct A\<^sub>R`
    moreover from `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* A\<^sub>Q" by simp+
    moreover have "A\<^sub>R \<sharp>* K'"
      using P_trans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* A\<^sub>P` `tvec \<sharp>* A\<^sub>R`
      unfolding \<pi> by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
    moreover have "zvec \<sharp>* P" and "zvec \<sharp>* R" using `zvec \<sharp>* (P,R)` by auto
    moreover have "zvec \<sharp>* K'"
      using P_trans `zvec \<sharp>* P` `A\<^sub>P \<sharp>* zvec` `tvec \<sharp>* zvec`
      unfolding \<pi> by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')    
    moreover note `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K`  `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
      `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* xvec` `xvec \<sharp>* M` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
      `A\<^sub>R \<sharp>* K'` `distinct zvec` `zvec \<sharp>* \<Psi>`
    moreover have "A\<^sub>R \<sharp>* zvec" using `zvec \<sharp>* A\<^sub>R` by simp
    moreover have "zvec \<sharp>* \<Psi>\<^sub>P" using `zvec \<sharp>* P` `A\<^sub>P \<sharp>* zvec` FrP
      by(auto dest: extract_frame_fresh_chain)
    moreover from `A\<^sub>P \<sharp>* zvec` have "zvec \<sharp>* A\<^sub>P" by simp
    moreover note `zvec \<sharp>* A\<^sub>Q`
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      by(rule_tac comm2_aux) assumption+

    with P_trans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* R`
      `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* R` and `xvec \<sharp>* R` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>P \<sharp>* M` `A\<^sub>R \<sharp>* K'` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>P` `tvec \<sharp>* R` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>R` `zvec \<sharp>* P`
      unfolding \<pi>
      by(rule_tac Comm2) (assumption|auto)+
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* Q'` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* K'`
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where  Req_r': "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and Fr_r': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" 
                         and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
      by(rule_tac C="(\<Psi>, P', Q')" and C'="\<Psi>" in expand_frame) auto

    from P'_rel_q' have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
    with Req_r' have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel" by(metis C3 Associativity composition_sym)
    with Fr_r' `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'"
      by(rule_tac C1)
    with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
    ultimately show ?case by blast
  qed
qed

lemma bang_pres:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     "eqvt Rel'"
  and     "guarded P"
  and     "guarded Q"
  and     c_sim: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     c_ext: "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     c_sym: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     Stat_eq: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"
  and     Closed: "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel"
  and     Assoc: "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"
  and     Par_pres: "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel"
  and     Frame_par_pres: "\<And>\<Psi>' \<Psi>\<^sub>U S T U A\<^sub>U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extract_frame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow>
                                            (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel"
  and     Res_pres: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"
  and     Scope_ext: "\<And>xvec \<Psi>' S T. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel"
  and     Trans: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel"
  and     Compose: "\<And>\<Psi>' S T U W. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel'; (\<Psi>', U, W) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, W) \<in> Rel'"
  and     C1: "\<And>\<Psi> S T U. \<lbrakk>(\<Psi>, S, T) \<in> Rel; guarded S; guarded T\<rbrakk> \<Longrightarrow> (\<Psi>, U \<parallel> !S, U \<parallel> !T) \<in> Rel'"
  and     Der: "\<And>\<Psi>' S \<pi> \<alpha> S' T. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<pi> @ \<alpha> \<prec> S'; (\<Psi>', S, T) \<in> Rel; bn \<alpha> \<sharp>* \<Psi>'; bn \<alpha> \<sharp>* S; bn \<alpha> \<sharp>* T; guarded T; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                      \<exists>\<pi>' T' U W.  \<Psi>' \<rhd> !T \<longmapsto>\<pi>' @ \<alpha> \<prec> T' \<and> (\<Psi>', S', U \<parallel> !S) \<in> Rel \<and> (\<Psi>', T', W \<parallel> !T) \<in> Rel \<and>
                                                (\<Psi>', U, W) \<in> Rel \<and> ((supp U)::name set) \<subseteq> supp S' \<and> 
                                                 ((supp W)::name set) \<subseteq> supp T'"

  shows "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[Rel'] R \<parallel> !Q"
using `eqvt Rel'`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> RQ')
  from `bn \<alpha> \<sharp>* (R \<parallel> !P)` `bn \<alpha> \<sharp>* (R \<parallel> !Q)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* (!Q)" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  from `\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>\<pi> @ \<alpha> \<prec> RQ'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* !Q` `bn \<alpha> \<sharp>* subject \<alpha>` show ?case
  proof(induct rule: par_cases[where C=P])
    case(c_par1 R' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
    from `extract_frame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = S_bottom'" by simp+
    with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi>' @ \<alpha> \<prec> R'` `bn \<alpha> \<sharp>* P` have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>append_at_end_prov_option \<pi>' A\<^sub>Q @ \<alpha> \<prec> (R' \<parallel> !P)"
      by(rule_tac Par1) (assumption | simp)+
    moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel'"
      by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 Q' \<pi>' A\<^sub>R \<Psi>\<^sub>R)
    have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    with `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(force dest: extract_frame_fresh_chain)
    with Q_trans `(\<Psi>, P, Q) \<in> Rel` `bn \<alpha> \<sharp>* \<Psi>``bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `guarded P` `bn \<alpha> \<sharp>* subject \<alpha>`
    obtain P' \<pi>'' S T where P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
      and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      by(drule_tac c_sym) (auto dest: Der c_ext)
    from P_trans FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>append_at_front_prov_option \<pi>'' A\<^sub>R @ \<alpha> \<prec> (R \<parallel> P')"
      by(rule_tac Par2) auto
    moreover 
    { 
      from `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* (!Q)` `A\<^sub>R \<sharp>* \<alpha>` P_trans Q_trans `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
	by(force dest: free_fresh_chain_derivative)+
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel` FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* P` suppT have "(\<Psi>, R \<parallel> P', R \<parallel> (T \<parallel> !P)) \<in> Rel"
	by(rule_tac Frame_par_pres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> P', (R \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', T \<parallel> !Q) \<in> Rel"
	by(blast intro: Par_pres Trans)
      with FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* Q'` `A\<^sub>R \<sharp>* (!Q)` suppT suppS have "(\<Psi>, R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel"
	by(rule_tac Frame_par_pres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      ultimately have "(\<Psi>, R \<parallel> P', R \<parallel> Q') \<in> Rel'" by(blast intro: c_sym Compose)
    }
    ultimately show ?case by blast
  next
    case(c_comm1 \<Psi>\<^sub>Q M N R' A\<^sub>R \<Psi>\<^sub>R K xvec Q' A\<^sub>Q yvec zvec)
    from `extract_frame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = S_bottom'" by simp+
    have R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> R'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
    from FrR `xvec \<sharp>* R` `A\<^sub>R \<sharp>* xvec` have "xvec \<sharp>* \<Psi>\<^sub>R" by(force dest: extract_frame_fresh_chain)
    with Q_trans `(\<Psi>, P, Q) \<in> Rel` `xvec \<sharp>* \<Psi>``xvec \<sharp>* P` `xvec \<sharp>* (!Q)` `guarded P` `xvec \<sharp>* K`
    obtain P' \<pi> S T where P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      apply(drule_tac c_sym)
      apply(drule_tac Der)
      apply(rule c_ext)
      by auto
    from P_trans
    obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>([]); tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* K" and "tvec \<sharp>* P" and "tvec \<sharp>* N" and "tvec \<sharp>* P'" and "tvec \<sharp>* \<Psi>\<^sub>R" and MeqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<turnstile> K' \<leftrightarrow> K" and "tvec \<sharp>* A\<^sub>R" and "tvec \<sharp>* zvec" and "tvec \<sharp>* R" and "tvec \<sharp>* xvec" and "tvec \<sharp>* yvec" and "tvec \<sharp>* A\<^sub>R"
      unfolding residual_inject
      by(frule_tac output_provenance'[where C="(\<Psi>,\<Psi>\<^sub>R,A\<^sub>R,R,zvec,\<Psi>\<^sub>P,xvec,yvec)"]) (auto simp add: frame.inject)
    have "A\<^sub>R \<sharp>* K'" using `A\<^sub>R \<sharp>* P` P_trans `tvec \<sharp>* A\<^sub>R`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)
    have "yvec \<sharp>* K'" using `yvec \<sharp>* P` P_trans `tvec \<sharp>* yvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)    
    from MeqK have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> K' \<leftrightarrow> K"
      by (metis Associativity stat_eq_ent)
    hence "\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
      by (metis Commutativity composition_sym stat_eq_ent)
    note `\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> K' \<leftrightarrow> K`
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      using R_trans `\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K'`
       `distinct yvec` `yvec \<sharp>* A\<^sub>R` `yvec \<sharp>* A\<^sub>R` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* K'` `yvec \<sharp>* R`
      unfolding `\<Psi>\<^sub>Q = S_bottom'`
      by(rule_tac comm2_aux[where A\<^sub>P="[]" and  A\<^sub>Q="[]"]) (assumption|auto intro!: Frame_stat_imp_refl)+      
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P')" 
      using P_trans `\<Psi>\<^sub>Q = S_bottom'` `xvec \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M` `A\<^sub>R \<sharp>* P` FrR
       `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* R`
      unfolding \<pi>
      by(rule_tac Comm1[where A\<^sub>Q="[]"]) (assumption | simp)+
    moreover from `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* (!Q)` `A\<^sub>R \<sharp>* xvec` P_trans Q_trans `xvec \<sharp>* K` `distinct xvec` 
    have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'" by(force dest: output_fresh_chain_derivative)+
    moreover with R_trans FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* (!Q)` `A\<^sub>R \<sharp>* M`
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where Fr_r': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* \<Psi>"
                         and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, P', Q, Q')" and C'=\<Psi> in expand_frame) auto

    moreover 
    { 
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel` have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', T \<parallel> !P) \<in> Rel" by(rule c_ext)
      with `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', T \<parallel> !P) \<in> Rel"
	by(metis Associativity Stat_eq composition_sym) 
      with Fr_r' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* P` suppT have "(\<Psi>, R' \<parallel> P', R' \<parallel> (T \<parallel> !P)) \<in> Rel"
	by(rule_tac Frame_par_pres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> P', (R' \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P) \<in> Rel"
	by(metis Res_pres psi_fresh_vec Scope_ext Trans)
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', T \<parallel> !Q) \<in> Rel"
	by(blast intro: Par_pres Trans)
      hence "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', Q', T \<parallel> !Q) \<in> Rel" by(rule c_ext)
      with `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', Q', T \<parallel> !Q) \<in> Rel"
	by(metis Associativity Stat_eq composition_sym) 
      with Fr_r' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* Q` suppT suppS have "(\<Psi>, R' \<parallel> Q', R' \<parallel> (T \<parallel> !Q)) \<in> Rel"
	by(rule_tac Frame_par_pres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel"
	by(metis Res_pres psi_fresh_vec Scope_ext Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: c_sym Compose)
    }
    ultimately show ?case by blast
  next
    case(c_comm2 \<Psi>\<^sub>Q M xvec N R' A\<^sub>R \<Psi>\<^sub>R K Q' A\<^sub>Q yvec zvec)
    from `extract_frame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = S_bottom'" by simp+
    have R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    then obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                and Fr_r': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* \<Psi>"
                                and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* R'" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                                and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "xvec \<sharp>* A\<^sub>R'" and "(p \<bullet> xvec) \<sharp>* A\<^sub>R'"
                                and "distinct_perm p" and "(p \<bullet> xvec) \<sharp>* R'" and "(p \<bullet> xvec) \<sharp>* N" 
      using `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* (!Q)`
            `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* (!Q)` `xvec \<sharp>* R` `xvec \<sharp>* M` `distinct xvec`
     by(rule_tac C="(\<Psi>, P, Q)" and C'="(\<Psi>, P, Q)" in expand_frame) (assumption | simp)+
    have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'" by fact
    with Q_trans S `(p \<bullet> xvec) \<sharp>* N` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" using `distinct_perm p` `xvec \<sharp>* (!Q)` `(p \<bullet> xvec) \<sharp>* Q`
      by(rule_tac input_alpha) auto
    with `(\<Psi>, P, Q) \<in> Rel` `guarded P`
    obtain P' \<pi> S T where P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>\<pi> @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp(p \<bullet> Q')"
      by(drule_tac c_sym) (auto dest: Der c_ext)
    from P_trans
    obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>([]); tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* \<Psi>" and "tvec \<sharp>* K" and "tvec \<sharp>* P" and "tvec \<sharp>* (p\<bullet>N)" and "tvec \<sharp>* N" and "tvec \<sharp>* P'" and "tvec \<sharp>* \<Psi>\<^sub>R" and MeqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<turnstile> K \<leftrightarrow> K'" and "tvec \<sharp>* A\<^sub>R" and "tvec \<sharp>* zvec" and "tvec \<sharp>* R" and "tvec \<sharp>* xvec" and "tvec \<sharp>* yvec" and "tvec \<sharp>* A\<^sub>R"
      by(frule_tac input_provenance'[where C="(\<Psi>,\<Psi>\<^sub>R,A\<^sub>R,R,p\<bullet>N,N,zvec,\<Psi>\<^sub>P,xvec,yvec)"]) (auto simp add: frame.inject)
    have "A\<^sub>R \<sharp>* K'" using `A\<^sub>R \<sharp>* P` P_trans `tvec \<sharp>* A\<^sub>R`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)
    have "yvec \<sharp>* K'" using `yvec \<sharp>* P` P_trans `tvec \<sharp>* yvec`
      unfolding \<pi>
      by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'' frame_chain_fresh_chain)        
    from MeqK have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> K \<leftrightarrow> K'"
      by (metis Associativity stat_eq_ent)
    hence "\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'"
      by (metis Commutativity composition_sym stat_eq_ent)
    note `\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> K \<leftrightarrow> K'`
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      using R_trans `\<Psi> \<otimes> \<one> \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K'`
       `distinct yvec` `yvec \<sharp>* A\<^sub>R` `yvec \<sharp>* A\<^sub>R` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* K'` `yvec \<sharp>* R`
      unfolding `\<Psi>\<^sub>Q = S_bottom'`
      by(rule_tac comm1_aux[where A\<^sub>P="[]" and  A\<^sub>Q="[]"]) (assumption|auto intro!: Frame_stat_imp_refl)+
    with S `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* R'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ K'\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
      apply(simp add: residual_inject)
      by(subst bound_output_chain_alpha''[symmetric]) auto
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P')" 
      using P_trans FrR `\<Psi>\<^sub>Q = S_bottom'` `(p \<bullet> xvec) \<sharp>* P` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M` `A\<^sub>R \<sharp>* P`
      `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P` `tvec \<sharp>* \<Psi>` `tvec \<sharp>* R`
      unfolding \<pi>
      by(rule_tac Comm2) (assumption | simp)+

    moreover from `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* Q` `A\<^sub>R' \<sharp>* N` S `xvec \<sharp>* A\<^sub>R'` `(p \<bullet> xvec) \<sharp>* A\<^sub>R'` P_trans Q_trans `distinct_perm p` have "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
      apply -
      apply(drule_tac input_fresh_chain_derivative, auto)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(force dest: input_fresh_chain_derivative)+
    from `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* N` P_trans `distinct_perm p` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
      apply(drule_tac input_fresh_chain_derivative, simp)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)

    { 
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R), (p \<bullet> P'), p \<bullet> (T \<parallel> !P)) \<in> Rel"
	by(rule Closed)
      with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel"
	by(simp add: eqvts)     
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel" by(rule c_ext)
      with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', (p \<bullet> P'), (p \<bullet> T) \<parallel> !P) \<in> Rel"
	by(metis Associativity Stat_eq composition_sym) 
      with Fr_r' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* P` `xvec \<sharp>* A\<^sub>R'` `(p \<bullet> xvec) \<sharp>* A\<^sub>R'` S `distinct_perm p` suppT
      have "(\<Psi>, R' \<parallel> (p \<bullet> P'), R' \<parallel> ((p \<bullet> T) \<parallel> !P)) \<in> Rel"
	apply(rule_tac Frame_par_pres)
	apply(assumption | simp add: fresh_chain_simps)+
	by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> (p \<bullet> P'), (R' \<parallel> (p \<bullet> T)) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> P')), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
	by(metis Res_pres psi_fresh_vec Scope_ext Trans)
      hence "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
      using `(p \<bullet> xvec) \<sharp>* R'` `(p \<bullet> xvec) \<sharp>* (p \<bullet> P')` S `distinct_perm p`
      apply(erule_tac rev_mp) by(subst res_chain_alpha[of p]) auto
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel'"
	by(rule C1)
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel` `(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), T \<parallel> !Q) \<in> Rel"
	by(blast intro: Par_pres Trans)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R), p \<bullet> p \<bullet> Q', p \<bullet> (T \<parallel> !Q)) \<in> Rel" by(rule Closed)
      with S `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` `(p \<bullet> xvec) \<sharp>* Q` `distinct_perm p`
      have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(simp add: eqvts)
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(rule c_ext)
      with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel"
	by(metis Associativity Stat_eq composition_sym) 
      with Fr_r' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* Q` suppT suppS `xvec \<sharp>* A\<^sub>R'` `(p \<bullet> xvec) \<sharp>* A\<^sub>R'` S `distinct_perm p` 
      have "(\<Psi>, R' \<parallel> Q', R' \<parallel> ((p \<bullet> T) \<parallel> !Q)) \<in> Rel"
	apply(rule_tac Frame_par_pres)
	apply(assumption | simp)+
	apply(simp add: fresh_chain_simps)
	by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> (p \<bullet> T)) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with `xvec \<sharp>* \<Psi>` `xvec \<sharp>* (!Q)` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel"
	by(metis Res_pres psi_fresh_vec Scope_ext Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: c_sym Compose)
    }
    ultimately show ?case by blast
  qed
qed

end

end
