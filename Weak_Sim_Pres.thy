(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Sim_Pres
  imports Sim_Pres Weak_Simulation Weak_Stat_Imp
begin

context env begin

lemma weak_inputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes PRelQ: "\<And>Tvec \<Psi>'. length xvec = length Tvec \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<leadsto><Rel> M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(induct rule: weakSimI2)
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` show ?case
  proof(induct rule: input_cases)
    case(c_input K Tvec)
    from `\<Psi> \<turnstile> K \<leftrightarrow> M` `set xvec \<subseteq> supp N` `length xvec = length Tvec` `distinct xvec`
    have "\<Psi> : (M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (P[xvec::=Tvec])"
      by(rule_tac weak_input) auto
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P[xvec::=Tvec] \<Longrightarrow>\<^sup>^\<^sub>\<tau>  P[xvec::=Tvec]" by simp
    moreover from `length xvec = length Tvec` have "(\<Psi> \<otimes> \<Psi>',  P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"
      by(rule PRelQ)
    ultimately show ?case by blast
  qed
next
  case(c_tau Q')
  from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.Q \<longmapsto>None @ \<tau> \<prec> Q'` have False by auto
  thus ?case by simp
qed

lemma weak_outputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<leadsto><Rel> M\<langle>N\<rangle>.Q"
proof(induct rule: weakSimI2)
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  from `\<Psi> \<rhd> M\<langle>N\<rangle>.Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` show ?case
  proof(induct rule: output_cases)
    case(c_output K)
    from `\<Psi> \<turnstile> M \<leftrightarrow> K` 
    have "\<Psi> : (M\<langle>N\<rangle>.Q) \<rhd> M\<langle>N\<rangle>.P \<Longrightarrow>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<langle>N\<rangle> \<prec> P" by(rule weak_output) auto
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>  P" by simp
    moreover have "(\<Psi> \<otimes> \<Psi>',  P, Q) \<in> Rel" by(rule PRelQ)
    ultimately show ?case by blast
  qed
next
  case(c_tau Q')
  from  `\<Psi> \<rhd> M\<langle>N\<rangle>.Q \<longmapsto>None @ \<tau> \<prec> Q'` have False by auto
  thus ?case by simp
qed

lemma res_tau_cases[consumes 3, case_names c_res]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>None @ \<tau> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> P'"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop P'"
proof -
  note Trans `x \<sharp> \<Psi>`
  moreover have "x \<sharp> (\<tau>)" by simp
  moreover note `x \<sharp> P'`
  moreover have "bn(\<tau>) \<sharp>* \<Psi>" and "bn(\<tau>) \<sharp>* P" and "bn(\<tau>) \<sharp>* subject(\<tau>)" and "bn(\<tau>) = []" by simp+
  ultimately show ?thesis
    by(induct rule: res_cases) (auto intro: rScope dest: tau_no_provenance')
qed

thm output_provenance

lemma weak_output_provenance_Some:
  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
  shows "\<exists>\<pi>'. \<pi> = Some \<pi>'"
  using assms
  by(auto elim!: weak_transitionE dest!: output_provenance
          simp add: residual_inject)

lemma weakResPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel'"
  and     "x \<sharp> \<Psi>"
  and     "Rel \<subseteq> Rel'"
  and     C1: "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto><Rel'> \<lparr>\<nu>x\<rparr>Q"
proof -
  note `eqvt Rel'` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)+ 
  ultimately show ?thesis
  proof(induct rule: weakSimIFresh[of _ _ _ _ _ "()"])
    case(c_act \<alpha> \<pi> Q' \<Psi>')
    from `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P` `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" by simp+
    from `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>`
    show ?case
    proof(induct rule: res_cases)
      case(c_open M \<pi> xvec1 xvec2 y N Q')
      from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "xvec1 \<sharp>* P" and "xvec2 \<sharp>* P" and "y \<sharp> P" by simp+
      from `x \<sharp> (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from PSimQ `\<Psi> \<rhd> Q \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')` `xvec1 \<sharp>* \<Psi>` `xvec2 \<sharp>* \<Psi>` `xvec1 \<sharp>* P` `xvec2 \<sharp>* P` `\<alpha> \<noteq> \<tau>`
      obtain P'' P' \<pi>' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P''"
                      and P''Chain: "\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>'), P', ([(x, y)] \<bullet> Q')) \<in> Rel"
        by (fastforce dest: weakSimE)
      from PTrans obtain \<pi>'' where \<pi>': "\<pi>' = Some \<pi>''"
        by(blast dest: weak_output_provenance_Some)
      from PTrans have "([(x, y)] \<bullet> \<Psi>) : ([(x, y)] \<bullet> Q) \<rhd> ([(x, y)] \<bullet> P) \<Longrightarrow>([(x, y)] \<bullet> \<pi>') @ ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>)) \<prec> ([(x, y)] \<bullet> P'')"
        by(rule eqvts)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec1` `y \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec2`
      have "\<Psi> : ([(x, y)] \<bullet> Q) \<rhd> ([(x, y)] \<bullet> P) \<Longrightarrow>Some([(x, y)] \<bullet> \<pi>'') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P'')"
        by(simp add: eqvts \<pi>')
      hence "\<Psi> : \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q) \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P) \<Longrightarrow>Some(\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P'')"
        using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
        by(rule weak_open)
      with `y \<sharp> P` `y \<sharp> Q` have "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>Some(\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P'')"
        by(simp add: alpha_res)
      moreover from P''Chain have "([(x, y)] \<bullet> (\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>'))) \<rhd> ([(x, y)] \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> ([(x, y)] \<bullet> P')"
        by(rule eqvts)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi> \<otimes> \<Psi>' \<rhd> ([(x, y)] \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> ([(x, y)] \<bullet> P')" by(simp add: eqvts)
      moreover from P'RelQ' `Rel \<subseteq> Rel'` have "(\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>'), P', ([(x, y)] \<bullet> Q')) \<in> Rel'" by auto
      with `eqvt Rel'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>'), P', ([(x, y)] \<bullet> Q'))) \<in> Rel'" by(rule eqvtI)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have " (\<Psi> \<otimes> \<Psi>', [(x, y)] \<bullet> P', Q') \<in> Rel'" by(simp add: eqvts)
      ultimately show ?case by blast
    next
      case(c_res \<pi> Q')
      from PSimQ `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
      obtain P'' P' \<pi>' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''"
                      and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
        by(blast dest: weakSimE)
      from PTrans `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`  have "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>map_option (F_res x) \<pi>' @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P''"
        by(rule_tac weak_scope)
      moreover from P''Chain  `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` have "\<Psi> \<otimes> \<Psi>' \<rhd> \<lparr>\<nu>x\<rparr>P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
        by(rule_tac tau_chain_res_pres) auto
      moreover from P'RelQ' `x \<sharp> \<Psi>` `x \<sharp> \<Psi>'` have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" 
        apply(rule_tac C1) by(auto simp add: fresh_left calc_atm)
      ultimately show ?case by blast
    qed
  next
    case(c_tau Q')
    from `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>None @ \<tau> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> Q'`
    show ?case
    proof(induct rule: res_tau_cases)
      case(c_res Q')
      from PSimQ `\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'` obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel" 
        by(blast dest: weakSimE)
      from PChain `x \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'" by(rule tau_chain_res_pres)
      moreover from P'RelQ' `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma weakResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     C1:    "\<And>\<Psi>' R S yvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; yvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*yvec\<rparr>R, \<lparr>\<nu>*yvec\<rparr>S) \<in> Rel"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto><Rel> \<lparr>\<nu>*xvec\<rparr>Q"
using `xvec \<sharp>* \<Psi>`
proof(induct xvec)
  case Nil
  from PSimQ show ?case by simp
next
  case(Cons x xvec)
  from `(x#xvec) \<sharp>* \<Psi>` have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by simp+
  from `xvec \<sharp>* \<Psi> \<Longrightarrow> \<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto><Rel> \<lparr>\<nu>*xvec\<rparr>Q` `xvec \<sharp>* \<Psi>`
  have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto><Rel> \<lparr>\<nu>*xvec\<rparr>Q" by simp
  moreover note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "Rel \<subseteq> Rel" by simp
  moreover have "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*[x]\<rparr>P, \<lparr>\<nu>*[x]\<rparr>Q) \<in> Rel"
    by(rule_tac yvec="[x]" in C1) auto
  hence "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> Rel"
    by simp
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto><Rel> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)"
    by(rule weakResPres)
  thus ?case by simp
qed

lemma parTauCases[consumes 1, case_names c_par1 c_par2 c_comm1 c_comm2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> R"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>None @ \<tau> \<prec> P';  extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  and     rComm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            distinct xvec; distinct yvec; distinct zvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K; xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
            yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
            yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
            zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
            zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
            Prop (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rComm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q yvec zvec.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            distinct xvec; distinct yvec; distinct zvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K;  xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
            yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
            yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
            zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
            zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
            Prop (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"

  shows "Prop R"
proof -
  from Trans obtain \<alpha> where "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<alpha> \<prec> R" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* subject \<alpha>" and "\<alpha> = \<tau>" by auto
  thus ?thesis using rPar1 rPar2 rComm1 rComm2
    by(induct rule: par_cases[where C=C]) (auto simp add: residual_inject dest: tau_no_provenance'')
qed

lemma weakParPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes PRelQ: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> (\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" 
  and     Eqvt:  "eqvt Rel"
  and     Eqvt': "eqvt Rel'"

  and     Sim:    "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto><Rel> T"
  and     Sym:    "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     Ext:    "\<And>\<Psi>' S T \<Psi>'. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     StatImp: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<lessapprox><Rel> T"
  and     C1: "\<And>\<Psi>' S T A\<^sub>U \<Psi>\<^sub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extract_frame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> R \<leadsto><Rel'> Q \<parallel> R"
proof -
  from Eqvt' show ?thesis
  proof(induct rule: weakSimI[where C="()"])
    case(c_act \<Psi>' \<alpha> \<pi> QR)
    from `bn \<alpha> \<sharp>* (P \<parallel> R)` `bn \<alpha> \<sharp>* (Q \<parallel> R)`
    have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R"
      by simp+
    from `\<Psi> \<rhd> Q \<parallel> R \<longmapsto>\<pi> @ \<alpha> \<prec> QR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q`  `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha> \<noteq> \<tau>` show ?case
    proof(induct rule: par_cases[where C="(P, R, \<Psi>')"])
      case(c_par1 Q' \<pi> A\<^sub>R \<Psi>\<^sub>R)
      from `A\<^sub>R \<sharp>* (P, R, \<Psi>')` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* \<Psi>'" by simp+
      have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      from `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* R` FrR
      have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" by fact
      from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto><Rel> Q"
        by(blast intro: PRelQ Sim)
      then obtain P'' P' \<pi>' where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''"
                           and P''Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', Q') \<in> Rel"
        using QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>R` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` `\<alpha> \<noteq> \<tau>`
        by(drule_tac \<Psi>'=\<Psi>' in weakSimE(1)) auto

      from PTrans QTrans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` 
      have "A\<^sub>R \<sharp>* P''" and "A\<^sub>R \<sharp>* Q'"
        by(fastforce dest: weak_fresh_chain_derivative free_fresh_chain_derivative)+
      with P''Chain have "A\<^sub>R \<sharp>* P'" by(force dest: tau_chain_fresh_chain)
      
      from PTrans FrR `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* \<alpha>` `A\<^sub>R \<sharp>* Q` 
      have "\<Psi> : Q \<parallel> R \<rhd> P \<parallel> R \<Longrightarrow>append_at_end_prov_option \<pi>' A\<^sub>R @ \<alpha> \<prec> (P'' \<parallel> R)"
        by(rule_tac weak_par1)
      moreover from P''Chain have "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" 
        by(metis tau_chain_stat_eq Associativity Commutativity Composition)
      with FrR have "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R" using `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* P''`
        by(rule_tac tau_chain_par1) auto
      
      moreover from P'RelQ' have "((\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel" 
        by(metis C3 composition_sym Associativity Commutativity)
      hence "(\<Psi> \<otimes> \<Psi>', P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* Q'`
        by(rule_tac C1) auto
      ultimately show ?case by blast
    next
      case(c_par2 R' \<pi> A\<^sub>Q \<Psi>\<^sub>Q)
      from `A\<^sub>Q \<sharp>* (P, R, \<Psi>')` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* \<Psi>'" by simp+
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
      
      obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi>, P, Q, A\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, \<alpha>, R, \<Psi>')" 
                      and "distinct A\<^sub>R"
        by(rule fresh_frame)
      then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* A\<^sub>Q" and  "A\<^sub>R \<sharp>* A\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
            and "A\<^sub>R \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* \<Psi>'"
        by simp+

      from `A\<^sub>Q \<sharp>* R`  FrR `A\<^sub>R \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
      from `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` FrR  have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto

      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` `A\<^sub>R \<sharp>* \<Psi>'`
                 `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
      obtain p \<Psi>'' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>R'"
                              and FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                              and "bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(p \<bullet> \<alpha>) \<sharp>* P" and "bn(p \<bullet> \<alpha>) \<sharp>* Q"
                              and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>'" and "distinct_perm p"
        by(rule_tac C="(\<Psi>, \<Psi>', P, Q)" and C'="(\<Psi>, P, Q)" in expand_frame) (assumption | simp)+

      from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q`
      have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule PRelQ)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q, P) \<in> Rel" by(rule Sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<lessapprox><Rel> P" by(rule StatImp)
      then obtain P' P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                           and QimpP': "insert_assertion(extract_frame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                          and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> ((p \<bullet> \<Psi>'') \<otimes> (p \<bullet> \<Psi>')) \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                          and P'RelQ: "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> ((p \<bullet> \<Psi>'') \<otimes> (p \<bullet> \<Psi>')), Q, P'') \<in> Rel"
        by(rule weak_stat_impE)
      obtain A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q"
                        and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* R" and "A\<^sub>P' \<sharp>* A\<^sub>R" and "A\<^sub>P' \<sharp>* \<alpha>"
        by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, \<Psi>\<^sub>Q, A\<^sub>Q, R, A\<^sub>R, \<alpha>)" in fresh_frame) auto

      from PChain `A\<^sub>R \<sharp>* P` `A\<^sub>Q \<sharp>* P` `bn \<alpha> \<sharp>* P` have "A\<^sub>Q \<sharp>* P'" and "A\<^sub>R \<sharp>* P'" and "bn \<alpha> \<sharp>* P'"
        by(force intro: tau_chain_fresh_chain)+
      from `A\<^sub>R \<sharp>* P'` `A\<^sub>P' \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P' \<sharp>* A\<^sub>Q` FrP' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P'"
        by(force dest: extract_frame_fresh_chain)+

      from PChain FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R" by(rule tau_chain_par1)
      moreover have "insert_assertion (extract_frame(Q \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame(P' \<parallel> R)) \<Psi>"
      proof -
        have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
          by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
        moreover from QimpP' FrQ FrP' `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` 
        have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle>" using fresh_comp_chain by simp
        moreover have "\<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P', \<Psi> \<otimes> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
        ultimately have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', \<Psi> \<otimes> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(rule Frame_stat_eq_imp_compose)
        hence "\<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>R@A\<^sub>P'), \<Psi> \<otimes> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(force intro: frame_imp_res_chain_pres simp add: frame_chain_append)
        with FrQ FrR FrP' `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>P' \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>R` 
                          `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` 
        show ?thesis
          by(simp add: frame_chain_append) (metis frame_imp_chain_comm Frame_stat_imp_trans)
      qed
      moreover have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'"
      proof -
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'" by fact
        moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
            by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym Frame_stat_eq_sym)
          moreover with FrP' FrQ QimpP' `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`
          have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle>" using fresh_comp_chain
            by simp
          moreover have "\<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym frame_int_associativity[THEN Frame_stat_eq_sym])
          ultimately show ?thesis
            by(rule Frame_stat_eq_imp_compose)
        qed
        ultimately show ?thesis
          using `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>P' \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P' \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>`
                `A\<^sub>P' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'` FrR `distinct A\<^sub>R`
          by(force intro: transfer_frame)
      qed
      hence "\<Psi> \<rhd> P' \<parallel> R \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P' @ \<alpha> \<prec> (P' \<parallel> R')" using FrP' `bn \<alpha> \<sharp>* P'` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* R` `A\<^sub>P' \<sharp>* \<alpha>` `A\<^sub>P' \<sharp>* \<alpha>`
        by(rule_tac Par2)
      ultimately have "\<Psi> : (Q \<parallel> R) \<rhd> P \<parallel> R \<Longrightarrow>append_at_front_prov_option \<pi> A\<^sub>P' @ \<alpha> \<prec> (P' \<parallel> R')"
        by(rule_tac weak_transitionI)
      moreover from PChain P'Chain `bn \<alpha> \<sharp>* P'` `bn(p \<bullet> \<alpha>) \<sharp>* P` `A\<^sub>R' \<sharp>* P` 
      have "bn \<alpha> \<sharp>* P''" and "bn(p \<bullet> \<alpha>) \<sharp>* P'" and "bn(p \<bullet> \<alpha>) \<sharp>* P''" and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* P''" 
        by(metis tau_chain_fresh_chain)+
      from P'Chain have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'') \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P'')"
        by(rule eqvts)
      with `bn \<alpha> \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P'` `bn(p \<bullet> \<alpha>) \<sharp>* P'` `bn \<alpha> \<sharp>* P''` `bn(p \<bullet> \<alpha>) \<sharp>* P''`
            S `distinct_perm p`
      have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>'' \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
        by(simp add: eqvts)
      hence "(\<Psi> \<otimes> \<Psi>') \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>'' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" 
        by(rule tau_chain_stat_eq) (metis Associativity Commutativity Composition Assertion_stat_eq_trans)
      with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(metis tau_chain_stat_eq composition_sym)
      hence "\<Psi> \<otimes> \<Psi>' \<rhd> P' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> R'" using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* \<Psi>'` `A\<^sub>R' \<sharp>* P'` by(rule_tac tau_chain_par1) auto
      moreover from P'RelQ have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'') \<otimes> (p \<bullet> \<Psi>'), P'', Q) \<in> Rel" by(rule Sym)
      with `eqvt Rel` have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'') \<otimes> (p \<bullet> \<Psi>'), P'', Q)) \<in> Rel" by(rule eqvtI)
      with `bn \<alpha> \<sharp>* \<Psi>` `bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P''` `bn(p \<bullet> \<alpha>) \<sharp>* P''` `bn \<alpha> \<sharp>* Q` `bn(p \<bullet> \<alpha>) \<sharp>* Q` S `distinct_perm p`
      have "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>'' \<otimes> \<Psi>', P'', Q) \<in> Rel" by(simp add: eqvts)
      with `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>R'` have "((\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R', P'', Q) \<in> Rel" 
        by(rule_tac C3, auto) (metis Associativity Commutativity Composition Assertion_stat_eq_trans)
      with FrR' `A\<^sub>R' \<sharp>* \<Psi>`  `A\<^sub>R' \<sharp>* \<Psi>'` `A\<^sub>R' \<sharp>* P''` `A\<^sub>R' \<sharp>* Q` 
      have "(\<Psi> \<otimes> \<Psi>', P'' \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) auto
      ultimately show ?case by blast
    next
      case c_comm1
      from `\<tau> \<noteq> \<tau>` have False by simp
      thus ?case by simp
    next
      case c_comm2
      from `\<tau> \<noteq> \<tau>` have False by simp
      thus ?case by simp
    qed
  next
    case(c_tau QR)
    from `\<Psi> \<rhd> Q \<parallel> R \<longmapsto>None @ \<tau> \<prec> QR` show ?case
    proof(induct rule: parTauCases[where C="(P, R)"])
      case(c_par1 Q' A\<^sub>R \<Psi>\<^sub>R)
      from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P"
        by simp+
      have FrR: " extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto><Rel> Q"
        by(blast intro: PRelQ Sim)
      moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'" by fact
      ultimately obtain P' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
        by(force dest: weakSimE)
      from PChain QTrans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
        by(force dest: free_fresh_chain_derivative tau_chain_fresh_chain)+
      from PChain FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> (P' \<parallel> R)"
        by(rule tau_chain_par1)
      moreover from P'RelQ' FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'` `A\<^sub>R \<sharp>* Q'` have "(\<Psi>, P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    next
      case(c_par2 R' A\<^sub>Q \<Psi>\<^sub>Q)
      from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
      obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, R)"
        by(rule fresh_frame)
      hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* R"
        by simp+
      
      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `A\<^sub>Q \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
        by(drule_tac extract_frame_fresh_chain) auto
      
      obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi>, P, Q, A\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, R)" and "distinct A\<^sub>R"
        by(rule fresh_frame)
      then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* A\<^sub>Q" and  "A\<^sub>R \<sharp>* A\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
            and "A\<^sub>R \<sharp>* R"
        by simp+

      from `A\<^sub>Q \<sharp>* R`  FrR `A\<^sub>R \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto
      from `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` FrR  have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(drule_tac extract_frame_fresh_chain) auto

      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R`
      obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                           and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
        by(rule_tac C="(\<Psi>, P, Q, R)" in expand_tau_frame) (assumption | simp)+

      from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q`
      obtain P' P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                      and QimpP': "insert_assertion(extract_frame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                      and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                      and P'RelQ: "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', Q, P'') \<in> Rel"
        by(metis StatImp PRelQ Sym weak_stat_impE)
      obtain A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q"
                        and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* R" and "A\<^sub>P' \<sharp>* A\<^sub>R"
        by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, \<Psi>\<^sub>Q, A\<^sub>Q, R, A\<^sub>R)" in fresh_frame) auto

      from PChain P'Chain `A\<^sub>R \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R' \<sharp>* P` have "A\<^sub>Q \<sharp>* P'" and "A\<^sub>R \<sharp>* P'" and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* P''"
        by(force intro: tau_chain_fresh_chain)+
      from `A\<^sub>R \<sharp>* P'` `A\<^sub>P' \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P' \<sharp>* A\<^sub>Q` FrP' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P'"
        by(force dest: extract_frame_fresh_chain)+
      
      from PChain FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R" by(rule tau_chain_par1)
      moreover have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'"
      proof -
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'" by fact
        moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
            by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym Frame_stat_eq_sym)
          moreover with FrP' FrQ QimpP' `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`
          have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle>" using fresh_comp_chain
            by simp
          moreover have "\<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(metis frame_int_associativity Commutativity Frame_stat_eq_trans frame_int_composition_sym frame_int_associativity[THEN Frame_stat_eq_sym])
          ultimately show ?thesis
            by(rule Frame_stat_eq_imp_compose)
        qed
        ultimately show ?thesis
          using `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>P' \<sharp>* R` `A\<^sub>Q \<sharp>* R` 
                `A\<^sub>P' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'` FrR `distinct A\<^sub>R`
          by(force intro: transfer_tau_frame)
      qed
      hence "\<Psi> \<rhd> P' \<parallel> R \<longmapsto>None @ \<tau> \<prec> (P' \<parallel> R')" using FrP' `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* R`
        by(rule_tac Par2[where \<pi>=None,simplified]) auto
      moreover from P'Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" 
        by(rule tau_chain_stat_eq) (metis Associativity)
      with `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(metis tau_chain_stat_eq composition_sym)
      hence "\<Psi> \<rhd> P' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> R'" using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P'` by(rule_tac tau_chain_par1)
      ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> (P'' \<parallel> R')"
        by(fastforce dest: rtrancl_into_rtrancl)

      moreover from P'RelQ `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P'', Q) \<in> Rel" by(blast intro: C3 Associativity composition_sym Sym)
      with FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P''` `A\<^sub>R' \<sharp>* Q` have "(\<Psi>, P'' \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) 
      ultimately show ?case by blast
    next
      case(c_comm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R yvec zvec)
      have  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+

      have  FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+
      from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+

      from `zvec \<sharp>* (P, R)` have "zvec \<sharp>* P" and "zvec \<sharp>* R" by simp+

      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by fact+
      from RTrans FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R \<sharp>* N` `xvec \<sharp>* R` `xvec \<sharp>* Q` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* Q`
                      `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `xvec \<sharp>* K` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* R` `xvec \<sharp>* R` `A\<^sub>R \<sharp>* P` `xvec \<sharp>* P` `yvec \<sharp>* xvec`
                       `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* xvec` `xvec \<sharp>* K` `distinct xvec` `A\<^sub>R \<sharp>* N`  `zvec \<sharp>* xvec` `zvec \<sharp>* A\<^sub>R` `yvec \<sharp>* A\<^sub>R`
      obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                             and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                             and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* K" and "(p \<bullet> xvec) \<sharp>* R" and "(p \<bullet> xvec) \<sharp>* zvec" and "(p \<bullet> xvec) \<sharp>* yvec" and "(p \<bullet> xvec) \<sharp>* N"
                             and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* xvec"
                             and "distinct_perm p"
        by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>Q)" and C'="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>Q,zvec,yvec)" in expand_frame) (assumption | simp)+
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

      from `A\<^sub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* M` S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by(simp add: fresh_chain_simps)
      from `A\<^sub>Q \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` S have "A\<^sub>Q \<sharp>* (p \<bullet> A\<^sub>R)" by(simp add: fresh_chain_simps)

      from QTrans S `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
        by(rule_tac input_perm_frame_subject) (assumption | auto simp add: fresh_star_def)+
      with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S have QTrans: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
        by(simp add: eqvts)
      from FrR have "(p \<bullet> extract_frame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
      with `xvec \<sharp>* R` `(p \<bullet> xvec) \<sharp>* R` S have FrR: "extract_frame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
        by(simp add: eqvts)

      from FrR `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q`
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<leadsto><Rel> Q" by(force intro: Sim PRelQ)

      with QTrans obtain \<pi> P' P'' where PTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) : Q \<rhd> P \<Longrightarrow>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P''"
                                  and P''Chain: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                                  and P'RelQ': "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P', Q') \<in> Rel"
        by(drule_tac weakSimE) auto
      from PTrans QTrans `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* Q` `A\<^sub>R' \<sharp>* N` have "A\<^sub>R' \<sharp>* P''" and "A\<^sub>R' \<sharp>* Q'"
        by(auto dest: weak_input_fresh_chain_derivative input_fresh_chain_derivative)

      from RTrans have "(p \<bullet> xvec) \<sharp>* R'" using `(p\<bullet>xvec) \<sharp>* R` `(p\<bullet>xvec) \<sharp>* N` `distinct xvec` `(p\<bullet>xvec) \<sharp>* xvec` `xvec \<sharp>* K`
        by(auto dest!: output_fresh_chain_derivative)

      from RTrans have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto> Some (\<langle>(p\<bullet>A\<^sub>R); zvec, (p\<bullet>M)\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        using S `xvec \<sharp>* \<Psi>` `(p\<bullet>xvec) \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>Q` `(p\<bullet>xvec) \<sharp>* \<Psi>\<^sub>Q` `xvec \<sharp>* K` `(p\<bullet>xvec) \<sharp>* K`
              `distinct_perm p` `xvec \<sharp>* R` `(p\<bullet>xvec) \<sharp>* R` `(p\<bullet>xvec) \<sharp>* N` `(p\<bullet>xvec) \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* R'` `(p \<bullet> xvec) \<sharp>* zvec` `zvec \<sharp>* xvec`
        by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts residual_inject bound_output_chain_alpha''[symmetric])

      from `zvec \<sharp>* A\<^sub>R` have "(p\<bullet>A\<^sub>R) \<sharp>* zvec"
        using S `zvec \<sharp>* xvec` `(p\<bullet>xvec) \<sharp>* zvec`
        by(subst (asm) perm_bool[where pi=p,symmetric]) (simp add: eqvts)

      have "zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)" using `zvec \<sharp>* xvec` `zvec \<sharp>* \<Psi>\<^sub>R` `(p\<bullet>xvec) \<sharp>* zvec` S
        by(simp add: fresh_chain_simps)
      from PTrans FrQ RTrans FrR `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* (p \<bullet> M)` `A\<^sub>Q \<sharp>* (p \<bullet> A\<^sub>R)`
           `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* P` `(p \<bullet> A\<^sub>R) \<sharp>* Q` `(p \<bullet> A\<^sub>R) \<sharp>* R` `(p \<bullet> A\<^sub>R) \<sharp>* K` `xvec \<sharp>* P` `distinct A\<^sub>R`
           `(p \<bullet> A\<^sub>R) \<sharp>* zvec` `distinct zvec` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* R` `zvec \<sharp>* P` `A\<^sub>Q \<sharp>* xvec` `zvec \<sharp>* A\<^sub>Q`
           `zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)`
      have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R')" by(rule_tac weak_comm1) (assumption|simp)+

      moreover from P''Chain `A\<^sub>R' \<sharp>* P''` have "A\<^sub>R' \<sharp>* P'" by(rule tau_chain_fresh_chain)
      from `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>R'"
        by(metis Associativity Assertion_stat_eq_trans Assertion_stat_eq_sym composition_sym)
      with P''Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tau_chain_stat_eq)
      hence "\<Psi> \<rhd> P'' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R'" using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P''` by(rule tau_chain_par1)
      hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R') \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using `xvec \<sharp>* \<Psi>` by(rule tau_chain_res_chain_pres)
      ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')"
        by auto
      moreover from P'RelQ' `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel"  by(metis C3 Associativity composition_sym)
      with FrR' `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
      with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'"
        by(rule_tac C2)
      ultimately show ?case by blast
    next
      case(c_comm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R yvec zvec)
      have  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `A\<^sub>Q \<sharp>* (P, R)` have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+

      have  FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      from `A\<^sub>R \<sharp>* (P, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+
      from `xvec \<sharp>* (P, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
      from `yvec \<sharp>* (P, R)` have "yvec \<sharp>* P" and "yvec \<sharp>* R" by simp+
      from `zvec \<sharp>* (P, R)` have "zvec \<sharp>* P" and "zvec \<sharp>* R" by simp+

      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'"
        by fact+

      from RTrans FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* Q'` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R \<sharp>* K` `yvec \<sharp>* A\<^sub>R` `zvec \<sharp>* A\<^sub>R`
      obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where  ReqR': "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" 
                           and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q'" and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* yvec" and "A\<^sub>R' \<sharp>* zvec"
        by(rule_tac C="(\<Psi>, P, Q', N, xvec, yvec, zvec)" and C'="(\<Psi>, P, Q', N, xvec)" in expand_frame) (assumption | simp)+

      from FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto><Rel> Q" by(force intro: Sim PRelQ)

      with QTrans `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>R` `xvec \<sharp>* P`
      obtain P'' P' \<pi> where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
                      and P''Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                      and P'RelQ': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', Q') \<in> Rel"
        by(fastforce dest: weakSimE)
      from PTrans obtain P''' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''"
                                and QimpP''': "insert_assertion (extract_frame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P''') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                                and P'''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P''' \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
        by(rule weak_transitionE)
      
      from PChain `A\<^sub>R \<sharp>* P` have "A\<^sub>R \<sharp>* P'''" by(rule tau_chain_fresh_chain)

      obtain A\<^sub>P''' \<Psi>\<^sub>P''' where FrP''': "extract_frame P''' = \<langle>A\<^sub>P''', \<Psi>\<^sub>P'''\<rangle>" and "A\<^sub>P''' \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, P''', Q, xvec,yvec,zvec,\<pi>)" and "distinct A\<^sub>P'''"
        by(rule fresh_frame)
      hence "A\<^sub>P''' \<sharp>* \<Psi>" and "A\<^sub>P''' \<sharp>* A\<^sub>Q" and "A\<^sub>P''' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P''' \<sharp>* M" and "A\<^sub>P''' \<sharp>* R"
        and "A\<^sub>P''' \<sharp>* N" and "A\<^sub>P''' \<sharp>* K" and "A\<^sub>P''' \<sharp>* A\<^sub>R" and "A\<^sub>P''' \<sharp>* P'''" and "A\<^sub>P''' \<sharp>* xvec" and "A\<^sub>P''' \<sharp>* \<Psi>\<^sub>R"
        and "A\<^sub>P''' \<sharp>* yvec" and "A\<^sub>P''' \<sharp>* zvec" and "A\<^sub>P''' \<sharp>* \<pi>" and "A\<^sub>P''' \<sharp>* Q"
        by simp+
      from P'''Trans `extract_frame P''' = \<langle>A\<^sub>P''',\<Psi>\<^sub>P'''\<rangle>` `distinct A\<^sub>P'''`
           `A\<^sub>P''' \<sharp>* \<Psi>` `A\<^sub>P''' \<sharp>* A\<^sub>Q` `A\<^sub>P''' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P''' \<sharp>* M` `A\<^sub>P''' \<sharp>* R` `A\<^sub>P''' \<sharp>* Q`
           `A\<^sub>P''' \<sharp>* N` `A\<^sub>P''' \<sharp>* K` `A\<^sub>P''' \<sharp>* A\<^sub>R` `A\<^sub>P''' \<sharp>* P'''` `A\<^sub>P''' \<sharp>* xvec` `A\<^sub>P''' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P''' \<sharp>* \<pi>` `A\<^sub>P''' \<sharp>* zvec`
      obtain tvec K' where \<pi>: "\<pi> = Some(\<langle>A\<^sub>P'''; tvec, K'\<rangle>)" and "distinct tvec" and "tvec \<sharp>* A\<^sub>P'''"
                              "tvec \<sharp>* \<Psi>" "tvec \<sharp>* A\<^sub>Q" "tvec \<sharp>* \<Psi>\<^sub>Q" "tvec \<sharp>* M" "tvec \<sharp>* R" "tvec \<sharp>* Q"
                              "tvec \<sharp>* N" "tvec \<sharp>* K" "tvec \<sharp>* A\<^sub>R" "tvec \<sharp>* P'''" "tvec \<sharp>* xvec" "tvec \<sharp>* \<Psi>\<^sub>R" "tvec \<sharp>* zvec"
                     and MeqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''' \<turnstile> K' \<leftrightarrow> M"
        unfolding residual_inject
        by(frule_tac output_provenance'[where C="(\<Psi>,A\<^sub>Q,\<Psi>\<^sub>Q,M,R,Q,N,K,A\<^sub>R,P''',xvec,\<Psi>\<^sub>R,A\<^sub>P''',zvec)"]) auto
      from P'''Trans have P'''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P''' \<longmapsto> Some(\<langle>A\<^sub>P'''; tvec, K'\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
        unfolding \<pi>.
      from MeqK have MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"
        by(metis stat_eq_ent Associativity associativity_sym)

      from `A\<^sub>R \<sharp>* P'''` `A\<^sub>P''' \<sharp>* A\<^sub>R` `extract_frame P''' = \<langle>A\<^sub>P''',\<Psi>\<^sub>P'''\<rangle>` 
      have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P'''"
        by(auto dest: extract_frame_fresh_chain)

      have "zvec \<sharp>* P'''" using `zvec \<sharp>* P` PChain
        by(rule_tac tau_chain_fresh_chain)

      from `zvec \<sharp>* P'''` `A\<^sub>P''' \<sharp>* zvec` `extract_frame P''' = \<langle>A\<^sub>P''',\<Psi>\<^sub>P'''\<rangle>` 
      have "zvec \<sharp>* \<Psi>\<^sub>P'''"
        by(auto dest: extract_frame_fresh_chain)

      have "A\<^sub>R \<sharp>* K'" using P'''Trans
          `A\<^sub>R \<sharp>* P'''` `A\<^sub>P''' \<sharp>* A\<^sub>R` `tvec \<sharp>* A\<^sub>R`
        by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
      have "zvec \<sharp>* K'" using P'''Trans
          `zvec \<sharp>* P'''` `A\<^sub>P''' \<sharp>* zvec` `tvec \<sharp>* zvec`
        by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
     from `tvec \<sharp>* A\<^sub>P'''` `extract_frame P''' = \<langle>A\<^sub>P''',\<Psi>\<^sub>P'''\<rangle>` `tvec \<sharp>* P'''`
      have "tvec \<sharp>* \<Psi>\<^sub>P'''"
        by(force dest: extract_frame_fresh_chain)

      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
        by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      moreover with QimpP''' FrP''' FrQ `A\<^sub>P''' \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P''' \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'''\<rangle>" using fresh_comp_chain
        by simp
      moreover have "\<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(metis frame_res_chain_pres frame_nil_stat_eq Commutativity Assertion_stat_eq_trans Composition Associativity)
      ultimately have QImpP''': "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(rule Frame_stat_eq_imp_compose)
      from PChain FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''' \<parallel> R" by(rule tau_chain_par1)
      moreover from RTrans FrR P'''Trans MeqK' QImpP''' FrP''' FrQ `distinct A\<^sub>P'''` `distinct A\<^sub>R` `A\<^sub>P''' \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
        `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'''` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `A\<^sub>P''' \<sharp>* \<Psi>` `A\<^sub>P''' \<sharp>* R`
        `A\<^sub>P''' \<sharp>* P'''` `A\<^sub>P''' \<sharp>* M` `A\<^sub>Q \<sharp>* R`  `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* xvec` `xvec \<sharp>* M` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P'''`
        `A\<^sub>R \<sharp>* K'` `distinct zvec` `zvec \<sharp>* A\<^sub>R` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>P'''` `zvec \<sharp>* K'` `zvec \<sharp>* R`
         `A\<^sub>P''' \<sharp>* zvec` `zvec \<sharp>* A\<^sub>Q`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
        by(rule_tac comm2_aux) (assumption | simp)+
      with P'''Trans FrP''' have "\<Psi> \<rhd> P''' \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R')" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P'''` `A\<^sub>R \<sharp>* R`
          `xvec \<sharp>* R` `A\<^sub>P''' \<sharp>* \<Psi>` `A\<^sub>P''' \<sharp>* P'''` `A\<^sub>P''' \<sharp>* R` `A\<^sub>P''' \<sharp>* M` `A\<^sub>R \<sharp>* K'` `A\<^sub>P''' \<sharp>* A\<^sub>R`
          `tvec \<sharp>* \<Psi>` `tvec \<sharp>* \<Psi>\<^sub>P'''` `tvec \<sharp>* R` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P'''` `zvec \<sharp>* \<Psi>\<^sub>R`
        by(rule_tac Comm2) assumption+
      moreover from P'''Trans `A\<^sub>R \<sharp>* P'''` `A\<^sub>R \<sharp>* xvec` `xvec \<sharp>* M` `distinct xvec` have "A\<^sub>R \<sharp>* P''"
        by(rule_tac output_fresh_chain_derivative) auto

      from PChain `A\<^sub>R' \<sharp>* P` have "A\<^sub>R' \<sharp>* P'''" by(rule tau_chain_fresh_chain)
      with P'''Trans have "A\<^sub>R' \<sharp>* P''" using `A\<^sub>R' \<sharp>* xvec` `xvec \<sharp>* M` `distinct xvec`
        by(rule_tac output_fresh_chain_derivative) auto

      with P''Chain have "A\<^sub>R' \<sharp>* P'" by(rule tau_chain_fresh_chain)
      from `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>R'"
        by(metis Associativity Assertion_stat_eq_trans Assertion_stat_eq_sym composition_sym)
      with P''Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tau_chain_stat_eq)
      hence "\<Psi> \<rhd> P'' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R'" using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P''` 
        by(rule tau_chain_par1)
      hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R') \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" 
        using `xvec \<sharp>* \<Psi>` by(rule tau_chain_res_chain_pres)
      ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" by(drule_tac tau_act_tau_chain) auto
      moreover from P'RelQ' `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel"  by(metis C3 Associativity composition_sym)
      with FrR' `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* Q'` `A\<^sub>R' \<sharp>* \<Psi>` have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
      with `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'"
        by(rule_tac C2)
      ultimately show ?case by blast
    qed
  qed
qed
no_notation relcomp (infixr "O" 75)
lemma weakSimBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     "eqvt Rel''"
  and     "guarded P"
  and     "guarded Q"
  and     Rel'Rel: "Rel' \<subseteq> Rel"

  and     FrameParPres: "\<And>\<Psi>' \<Psi>\<^sub>U S T U A\<^sub>U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extract_frame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow>
                                            (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel"
  and     C1: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; guarded S; guarded T\<rbrakk> \<Longrightarrow> (\<Psi>', U \<parallel> !S, U \<parallel> !T) \<in> Rel''"
  and     ResPres: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"
  and     ResPres': "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"

  and     Closed: "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel"
  and     Closed': "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel'"
  and     StatEq: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"
  and     StatEq': "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel'"
  and     Trans: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel"
  and     Trans': "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; (\<Psi>', T, U) \<in> Rel'\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel'"

  and     cSim: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto><Rel> T"
  and     cExt: "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     cExt': "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel'"
  and     cSym: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     cSym': "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>', T, S) \<in> Rel'"

  and     ParPres: "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel"
  and     ParPres2: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> S, T \<parallel> T) \<in> Rel"
  and     ParPres': "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel'"

  and     Assoc: "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"
  and     Assoc': "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel'"
  and     ScopeExt: "\<And>xvec \<Psi>' T S. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel"
  and     ScopeExt': "\<And>xvec \<Psi>' T S. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel'"

  and     Compose: "\<And>\<Psi>' S T U O. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel''; (\<Psi>', U, O) \<in> Rel'\<rbrakk> \<Longrightarrow> (\<Psi>', S, O) \<in> Rel''"

  and     rBangActE: "\<And>\<Psi>' S \<alpha> \<pi> S'. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<pi> @ \<alpha> \<prec> S'; guarded S; bn \<alpha> \<sharp>* S; \<alpha> \<noteq> \<tau>; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow> \<exists>T \<pi>'. \<Psi>' \<rhd> S \<longmapsto>\<pi>' @ \<alpha> \<prec> T \<and> (\<one>, S', T \<parallel> !S) \<in> Rel'"
  and     rBangTauE: "\<And>\<Psi>' S S'. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>None @ \<tau> \<prec> S'; guarded S\<rbrakk> \<Longrightarrow> \<exists>T. \<Psi>' \<rhd> S \<parallel> S \<longmapsto> None @ \<tau> \<prec> T \<and> (\<one>, S', T \<parallel> !S) \<in> Rel'"
  and     rBangTauI: "\<And>\<Psi>' S S'. \<lbrakk>\<Psi>' \<rhd> S \<parallel> S \<Longrightarrow>\<^sup>^\<^sub>\<tau> S'; guarded S\<rbrakk> \<Longrightarrow> \<exists>T. \<Psi>' \<rhd> !S \<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<and> (\<Psi>', T, S' \<parallel> !S) \<in> Rel'"
  shows "\<Psi> \<rhd> R \<parallel> !P \<leadsto><Rel''> R \<parallel> !Q"
using `eqvt Rel''`
proof(induct rule: weakSimI[where C="()"])
  case(c_act \<Psi>' \<alpha> \<pi> RQ')
  from `bn \<alpha> \<sharp>* (R \<parallel> !P)` `bn \<alpha> \<sharp>* (R \<parallel> !Q)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* (!Q)" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R"
    by simp+
  from `\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>\<pi> @ \<alpha> \<prec> RQ'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* !Q` `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha> \<noteq> \<tau>` show ?case
  proof(induct rule: par_cases[where C="(\<Psi>', P, Q, R)"])
    case(c_par1 R' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
    from `extract_frame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = \<one>" by simp+
    with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi>' @ \<alpha> \<prec> R'` `\<Psi>\<^sub>Q = \<one>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
    have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<pi>' @ \<alpha> \<prec> (R' \<parallel> !P)"
     by(drule_tac Par1[where Q="!P" and A\<^sub>Q="[]",simplified, unfolded map_option.id[unfolded id_def]])
       auto
    hence "\<Psi> : R \<parallel> !Q \<rhd> R \<parallel> !P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> R' \<parallel> !P" by(rule_tac transition_weak_transition) auto
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> R' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> !P" by auto
    moreover from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule cExt)
    hence "(\<Psi> \<otimes> \<Psi>', R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel''" using `guarded P` `guarded Q` 
      by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 Q' \<pi>' A\<^sub>R \<Psi>\<^sub>R)
    from `A\<^sub>R \<sharp>* (\<Psi>', P, Q, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* \<Psi>'" and "A\<^sub>R \<sharp>* R" by simp+
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    with `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
    
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* A\<^sub>R"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R)" in fresh_frame) auto
    from FrQ `guarded Q` have "\<Psi>\<^sub>Q \<simeq> \<one>" and "supp \<Psi>\<^sub>Q = ({}::name set)" by(blast dest: guarded_stat_eq)+
    hence "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>Q" by(auto simp add: fresh_star_def fresh_def)

    from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'` `guarded Q` `bn \<alpha> \<sharp>* Q` `\<alpha> \<noteq> \<tau>` `bn \<alpha> \<sharp>* subject \<alpha>`
    obtain T \<pi>'' where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi>'' @ \<alpha> \<prec> T" and "(\<one>, Q', T \<parallel> !Q) \<in> Rel'" 
      by(blast dest: rBangActE)
    
    from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    with QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>R` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
    obtain P'' \<pi>''' S where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>\<pi>''' @ \<alpha> \<prec> P''" 
                   and P''Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S"
                   and SRelT: "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', S, T) \<in> Rel"
      by(blast dest: cSim weakSimE)
    from PTrans have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> : Q \<rhd> P \<Longrightarrow>\<pi>''' @ \<alpha> \<prec> P''"
      by(metis weak_transition_stat_eq Identity Assertion_stat_eq_sym)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<parallel> !P \<rhd> P \<parallel> !P \<Longrightarrow>\<pi>''' @ \<alpha> \<prec> P'' \<parallel> !P" using `bn \<alpha> \<sharp>* P` 
      by(force intro: weak_par1[where A\<^sub>Q="[]",simplified,unfolded map_option.id[unfolded id_def]])
    then obtain \<pi>'''' where "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<parallel> !P \<rhd> !P \<Longrightarrow>\<pi>'''' @ \<alpha> \<prec> P'' \<parallel> !P" using `guarded P`
      by(rule weak_bang)
    hence "\<Psi> : R \<parallel> (Q \<parallel> !P) \<rhd> R \<parallel> !P \<Longrightarrow>append_at_front_prov_option \<pi>'''' A\<^sub>R @ \<alpha> \<prec> R \<parallel> (P'' \<parallel> !P)" 
      using FrR `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* Q``A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* \<alpha>` `A\<^sub>R \<sharp>* \<alpha>`
      by(rule_tac weak_par2) auto
    moreover have "insert_assertion (extract_frame(R \<parallel> !Q)) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame(R \<parallel> (Q \<parallel> !P))) \<Psi>"
    proof -
      have "insert_assertion (extract_frame(R \<parallel> !P)) \<Psi> = \<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>" using FrR `A\<^sub>R \<sharp>* \<Psi>`
        by auto
      moreover from `\<Psi>\<^sub>Q \<simeq> \<one>` have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle>"
        by(rule_tac frame_res_chain_pres, auto) (metis Identity composition_sym Assertion_stat_eq_trans Assertion_stat_eq_sym)
      moreover have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<lparr>\<nu>*A\<^sub>Q\<rparr>(\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle>)" using `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R` fresh_comp_chain
        by(subst frame_res_fresh_chain[where xvec=A\<^sub>Q, THEN Frame_stat_eq_sym]) auto
      moreover have "\<lparr>\<nu>*A\<^sub>Q\<rparr>(\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle>) \<simeq>\<^sub>F \<lparr>\<nu>*A\<^sub>R\<rparr>(\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle>)"
        by(rule frame_res_chain_comm)
      moreover have "insert_assertion (extract_frame(R \<parallel> (Q \<parallel> !P))) \<Psi> = \<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<otimes> \<one>\<rangle>" 
        using FrR FrQ `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R`  `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`  fresh_comp_chain
        by auto
      ultimately have "insert_assertion (extract_frame(R \<parallel> !P)) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame(R \<parallel> (Q \<parallel> !P))) \<Psi>"
        by(auto simp add: frame_chain_append) (blast dest: Frame_stat_eq_trans)
      thus ?thesis by(simp add: Frame_stat_eq_def)
    qed
    ultimately have "\<Psi> : R \<parallel> !Q \<rhd> R \<parallel> !P \<Longrightarrow>append_at_front_prov_option \<pi>'''' A\<^sub>R @ \<alpha> \<prec> R \<parallel> (P'' \<parallel> !P)" 
      by(rule weak_transition_frame_imp)

    moreover from PTrans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    have "A\<^sub>R \<sharp>* P''" by(force dest: weak_fresh_chain_derivative)
    with P''Chain have "A\<^sub>R \<sharp>* S" by(force dest: tau_chain_fresh_chain)
    from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>_ @ \<alpha> \<prec> T` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "A\<^sub>R \<sharp>* T"
      by(force dest: free_fresh_chain_derivative)

    from P''Chain have "((\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> S" 
      by(rule tau_chain_stat_eq) (metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym Identity)
    hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> S \<parallel> !P"
      by(rule_tac tau_chain_par1) auto
    hence "\<Psi> \<otimes> \<Psi>' \<rhd> R \<parallel> (P'' \<parallel> !P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> R \<parallel> (S \<parallel> !P)" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* P''` `A\<^sub>R \<sharp>* P`
      by(rule_tac tau_chain_par2) auto
    moreover have "(\<Psi> \<otimes> \<Psi>', R \<parallel> (S \<parallel> !P), R \<parallel> Q') \<in> Rel''"
    proof -
      from `((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', S, T) \<in> Rel` have "((\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
        by(rule StatEq) (metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym)
      with FrR `A\<^sub>R \<sharp>* \<Psi>`  `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* S` `A\<^sub>R \<sharp>* T` have "(\<Psi> \<otimes> \<Psi>', R \<parallel> S, R \<parallel> T) \<in> Rel"
        by(rule_tac FrameParPres) auto
      hence "(\<Psi> \<otimes> \<Psi>', R \<parallel> T, R \<parallel> S) \<in> Rel" by(rule cSym)
      hence "(\<Psi> \<otimes> \<Psi>', (R \<parallel> T) \<parallel> !P, (R \<parallel> S) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi> \<otimes> \<Psi>', (R \<parallel> S) \<parallel> !P, (R \<parallel> T) \<parallel> !P) \<in> Rel" by(rule cSym)
      hence "(\<Psi> \<otimes> \<Psi>', R \<parallel> (S \<parallel> !P), (R \<parallel> T) \<parallel> !P) \<in> Rel" by(metis Trans Assoc)
      moreover from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule cExt)
      hence "(\<Psi> \<otimes> \<Psi>', (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel''" using `guarded P` `guarded Q` by(rule C1)
      moreover from `(\<one>, Q', T \<parallel> !Q) \<in> Rel'` have "(\<one> \<otimes> \<Psi> \<otimes> \<Psi>', Q', T \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi> \<otimes> \<Psi>', Q', T \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity Assertion_stat_eq_sym Commutativity Assertion_stat_eq_trans)
      hence "(\<Psi> \<otimes> \<Psi>', R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi> \<otimes> \<Psi>', R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi> \<otimes> \<Psi>', (R \<parallel> T) \<parallel> !Q, R \<parallel> Q') \<in> Rel'" by(rule cSym')
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  next
    case c_comm1
    from `\<tau> \<noteq> \<tau>` have False by simp
    thus ?case by simp
  next
    case c_comm2
    from `\<tau> \<noteq> \<tau>` have False by simp
    thus ?case by simp
  qed
next
  case(c_tau RQ')
  from `\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>None @ \<tau> \<prec> RQ'` show ?case
  proof(induct rule: parTauCases[where C="(P, Q, R)"])
    case(c_par1 R' A\<^sub>Q \<Psi>\<^sub>Q)
    from `extract_frame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = \<one>" by simp+
    with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'` `\<Psi>\<^sub>Q = \<one>`
    have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>None @ \<tau> \<prec> (R' \<parallel> !P)" by(rule_tac Par1[where \<pi>=None,simplified]) (assumption | simp)+
    hence "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> !P" by auto
    moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel''"
      by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 Q' A\<^sub>R \<Psi>\<^sub>R)
    from `A\<^sub>R \<sharp>* (P, Q, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* A\<^sub>R"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R)" in fresh_frame) auto
    from FrQ `guarded Q` have "\<Psi>\<^sub>Q \<simeq> \<one>" and "supp \<Psi>\<^sub>Q = ({}::name set)" by(blast dest: guarded_stat_eq)+
    hence "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>Q" by(auto simp add: fresh_star_def fresh_def)

    from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>None @ \<tau> \<prec> Q'` `guarded Q` 
    obtain T where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<parallel> Q \<longmapsto>None @ \<tau> \<prec> T" and "(\<one>, Q', T \<parallel> !Q) \<in> Rel'" 
      by(blast dest: rBangTauE)
    
    from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>R, P \<parallel> P, Q \<parallel> Q) \<in> Rel" by(rule ParPres2)
    with QTrans 
    obtain S where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> S" and SRelT: "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
      by(blast dest: cSim weakSimE)
    from PTrans `guarded P` obtain U where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> U" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel'"
      by(blast dest: rBangTauI)
    from PChain `A\<^sub>R \<sharp>* P` have "A\<^sub>R \<sharp>* U" by(force dest: tau_chain_fresh_chain)
    from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> U` FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> R \<parallel> U"
      by(rule_tac tau_chain_par2) auto
    moreover from PTrans `A\<^sub>R \<sharp>* P` have "A\<^sub>R \<sharp>* S" by(force dest: tau_chain_fresh_chain)
    from QTrans `A\<^sub>R \<sharp>* Q` have "A\<^sub>R \<sharp>* T" by(force dest: tau_fresh_chain_derivative)
    have "(\<Psi>, R \<parallel> U, R \<parallel> Q') \<in> Rel''"
    proof -
      from `(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel'` Rel'Rel have "(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel"
        by auto
      hence "(\<Psi>, R \<parallel> U, R \<parallel> (S \<parallel> !P)) \<in> Rel" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* U` `A\<^sub>R \<sharp>* S` `A\<^sub>R \<sharp>* P`
        by(rule_tac FrameParPres) auto

      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel` FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* S` `A\<^sub>R \<sharp>* T` have "(\<Psi>, R \<parallel> S, R \<parallel> T) \<in> Rel"
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, R \<parallel> T, R \<parallel> S) \<in> Rel" by(rule cSym)
      hence "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> S) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, (R \<parallel> S) \<parallel> !P, (R \<parallel> T) \<parallel> !P) \<in> Rel" by(rule cSym)
      hence "(\<Psi>, R \<parallel> (S \<parallel> !P), (R \<parallel> T) \<parallel> !P) \<in> Rel" by(metis Trans Assoc)
      ultimately have "(\<Psi>, R \<parallel> U, (R \<parallel> T) \<parallel> !P) \<in> Rel" by(rule Trans)
      moreover from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel''" using `guarded P` `guarded Q` by(rule C1)
      moreover from `(\<one>, Q', T \<parallel> !Q) \<in> Rel'` have "(\<one> \<otimes> \<Psi>, Q', T \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', T \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity Assertion_stat_eq_sym Commutativity Assertion_stat_eq_trans)
      hence "(\<Psi>, R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R \<parallel> T) \<parallel> !Q, R \<parallel> Q') \<in> Rel'" by(rule cSym')
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  next
    case(c_comm1 \<Psi>\<^sub>Q M N R' A\<^sub>R \<Psi>\<^sub>R K xvec Q' A\<^sub>Q yvec zvec)
    from `A\<^sub>R \<sharp>* (P, Q, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    from `xvec \<sharp>* (P, Q, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `yvec \<sharp>* (P, Q, R)` have "yvec \<sharp>* P" and "yvec \<sharp>* Q" and "yvec \<sharp>* R" by simp+
    have FrQ: "extract_frame(!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> R'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* M`
    obtain A\<^sub>R' \<Psi>\<^sub>R' \<Psi>' where FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>"
      by(rule_tac C="(\<Psi>, xvec, P, Q)" and C'="(\<Psi>, xvec, P, Q)" in expand_frame) auto
    from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `guarded Q` `xvec \<sharp>* Q` `xvec \<sharp>* K`
    obtain S \<pi> where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> S" and "(\<one>, Q', S \<parallel> !Q) \<in> Rel'"
      by(fastforce dest: rBangActE)

    ultimately obtain P' \<pi>' T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T" and "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', T, S) \<in> Rel"
      using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>R` `xvec \<sharp>* P`
      by(drule_tac cSim) (fastforce dest!: weakSimE(1))

    from PTrans `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* xvec` `xvec \<sharp>* K` `distinct xvec`
    have "A\<^sub>R \<sharp>* P'" and  "A\<^sub>R' \<sharp>* P'"
      by(force dest: weak_output_fresh_chain_derivative)+
    with P'Chain have "A\<^sub>R' \<sharp>* T" by(force dest: tau_chain_fresh_chain)+
    from QTrans `A\<^sub>R' \<sharp>* Q` `A\<^sub>R' \<sharp>* xvec` `xvec \<sharp>* K` `distinct xvec` 
    have "A\<^sub>R' \<sharp>* S" by(force dest: output_fresh_chain_derivative)

    from QTrans obtain A\<^sub>Q' \<Psi>\<^sub>Q' tvec M'' where FrQ': "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>"
      and \<pi>: "\<pi> = Some(\<langle>A\<^sub>Q'; tvec, M''\<rangle>)" and "distinct A\<^sub>Q'" and "distinct tvec"
      and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* tvec" and M'eqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q' \<turnstile> M'' \<leftrightarrow> K"
      and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q' \<sharp>* A\<^sub>R" and "A\<^sub>Q' \<sharp>* M" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K"
      and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* yvec"
      unfolding residual_inject
      by(drule_tac output_provenance[where C="(\<Psi>,Q,\<Psi>\<^sub>R, A\<^sub>R, K, M, R, xvec, yvec)"]) auto

    from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                             and NilImpP'': "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                             and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      using FrQ' `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R` fresh_comp_chain
      by(drule_tac weak_transitionE) auto

    from FrQ' `guarded Q` have "\<Psi>\<^sub>Q' \<simeq> \<one>" and "supp \<Psi>\<^sub>Q' = ({}::name set)" by(blast dest: guarded_stat_eq)+
    hence "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>Q'" by(auto simp add: fresh_star_def fresh_def)

    from P''Trans obtain A\<^sub>P'' \<Psi>\<^sub>P'' uvec M' where FrP'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>"
      and \<pi>': "\<pi>' = Some(\<langle>A\<^sub>P''; uvec, M'\<rangle>)" and "distinct A\<^sub>P''" and "distinct uvec"
      and "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* uvec" and M'eqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'' \<turnstile> M' \<leftrightarrow> K"
      and "A\<^sub>P'' \<sharp>* Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* K"
      and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* yvec" and "A\<^sub>P'' \<sharp>* P" and "A\<^sub>P'' \<sharp>* P''"
      and "uvec \<sharp>* Q" and "uvec \<sharp>* \<Psi>\<^sub>R" and "uvec \<sharp>* A\<^sub>R" and "uvec \<sharp>* M" and "uvec \<sharp>* R" and "uvec \<sharp>* K"
      and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* P" and "uvec \<sharp>* P''"
      unfolding residual_inject
      by(drule_tac output_provenance[where C="(\<Psi>,Q,\<Psi>\<^sub>R, A\<^sub>R, K, M, R, xvec, yvec,P)"]) auto

    from FrP'' `uvec \<sharp>* P''` `A\<^sub>P'' \<sharp>* uvec` have "uvec \<sharp>* \<Psi>\<^sub>P''" by(force dest: extract_frame_fresh_chain)

    from M'eqK have M'eqK': "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>R \<turnstile> M' \<leftrightarrow> K"
      by (meson Assertion_stat_eq_def Assertion_stat_imp_def Associativity associativity_sym)

    from `A\<^sub>R \<sharp>* P` PChain have "A\<^sub>R \<sharp>* P''" by(rule_tac tau_chain_fresh_chain)
    from `yvec \<sharp>* P` PChain have "yvec \<sharp>* P''" by(rule_tac tau_chain_fresh_chain)

    from FrP'' `A\<^sub>R \<sharp>* P''` `A\<^sub>P'' \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P''" by(auto dest: extract_frame_fresh_chain)

    from FrP'' `yvec \<sharp>* P''` `A\<^sub>P'' \<sharp>* yvec` have "yvec \<sharp>* \<Psi>\<^sub>P''" by(auto dest: extract_frame_fresh_chain)
    
    from `A\<^sub>R \<sharp>* P''` P''Trans have "A\<^sub>R \<sharp>* \<pi>'" by(rule_tac trans_fresh_provenance)
    hence "A\<^sub>R \<sharp>* M'" unfolding \<pi>'
      using `A\<^sub>P'' \<sharp>* A\<^sub>R` using `uvec \<sharp>* A\<^sub>R`
      by (simp add: frame_chain_fresh_chain'')
    from `yvec \<sharp>* P''` P''Trans have "yvec \<sharp>* \<pi>'" by(rule_tac trans_fresh_provenance)
    hence "yvec \<sharp>* M'" unfolding \<pi>'
      using `A\<^sub>P'' \<sharp>* yvec` using `uvec \<sharp>* yvec`
      by (simp add: frame_chain_fresh_chain'')

    from FrQ' `A\<^sub>R \<sharp>* Q` `A\<^sub>Q' \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'" by(auto dest: extract_frame_fresh_chain)

    from PChain have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))"
    proof(induct rule: tau_chain_cases)
      case tau_base
      from FrP'' `guarded P` `P = P''` have "\<Psi>\<^sub>P'' \<simeq> \<one>" and "supp \<Psi>\<^sub>P'' = ({}::name set)" by(blast dest: guarded_stat_eq)+

      with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>_ @ M\<lparr>N\<rparr> \<prec> R'` FrQ
      have "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> R'"
        using Assertion_stat_eq_sym composition_sym
        by(force elim: stat_eq_transition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>N\<rparr> \<prec> R'"
        using `extract_frame R = _` `\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>R \<turnstile> M' \<leftrightarrow> K`
              Frame_stat_imp_refl `distinct A\<^sub>R` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>`
              `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M'`
              `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* K`
              `distinct  yvec` iffD1[OF fresh_chain_sym, OF `yvec \<sharp>* A\<^sub>R`]
              `A\<^sub>R \<sharp>* M'` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P''` `yvec \<sharp>* M'`
              `yvec \<sharp>* R` `yvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* A\<^sub>Q`
        by(rule comm2_aux)
      hence "\<Psi> \<otimes> \<one> \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>N\<rparr> \<prec> R'"
        using Assertion_stat_eq_sym composition_sym `\<Psi>\<^sub>P'' \<simeq> \<one>`
        by(force elim: stat_eq_transition)
      moreover note FrR
      moreover from P''Trans `P = P''` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>R` `xvec \<sharp>* P`
        by(rule_tac Par1[where Q="!P" and A\<^sub>Q="[]",simplified,unfolded map_option.id[unfolded id_def]]) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>Some(\<langle>\<epsilon>, \<langle>(A\<^sub>P'' @ uvec), M'\<rangle>\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using `guarded P`
       unfolding \<pi>'
       by(rule Bang[where \<pi>=\<pi>', unfolded \<pi>',simplified])
      ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))" using `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* M` `xvec \<sharp>* R`
        `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P` `A\<^sub>P'' \<sharp>* \<Psi>` `uvec \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `uvec \<sharp>* R`
        by(force intro: Comm1[where A\<^sub>Q="[]" and zvec = "A\<^sub>P'' @ uvec",simplified])
      thus ?case by(rule tau_act_tau_chain)
    next
      case tau_step
      from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tau_step_chain_stat_eq) (metis Identity Assertion_stat_eq_sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" by(rule_tac tau_step_chain_par1) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" using `guarded P` by(rule tau_step_chain_bang)
      hence  "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R \<parallel> (P'' \<parallel> !P)" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P`
        by(rule_tac tau_step_chain_par2) auto
      moreover have "\<Psi> \<rhd> R \<parallel> (P'' \<parallel> !P) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))"
      proof -
        from FrQ `\<Psi>\<^sub>Q' \<simeq> \<one>` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>_ @ M\<lparr>N\<rparr> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> R'"
          by simp (metis stat_eq_transition Assertion_stat_eq_sym composition_sym)
        moreover from P''Trans have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P'' \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
        hence P''PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<parallel> !P \<longmapsto>\<pi>' @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using `xvec \<sharp>* P`
          by(rule_tac Par1[where A\<^sub>Q="[]" and Q="!P",simplified,unfolded map_option.id[unfolded id_def]]) auto
        moreover from FrP'' have FrP''P: "extract_frame(P'' \<parallel> !P) = \<langle>A\<^sub>P'', \<Psi>\<^sub>P'' \<otimes> \<one>\<rangle>"
          by auto
        moreover from `_ \<otimes> _ \<otimes> _ \<turnstile> M' \<leftrightarrow> K` have "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> M' \<leftrightarrow> K"
          using Assertion_stat_eq_sym Composition Identity composition_sym stat_eq_ent by blast
        moreover have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>)) \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle>"
            by(rule_tac frame_res_chain_pres, simp)
              (metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym)
          moreover from NilImpP'' FrQ FrP'' `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R` fresh_comp_chain have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle>"
            by auto
          moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(rule frame_res_chain_pres, simp) 
              (metis Identity Assertion_stat_eq_sym Associativity Commutativity Composition Assertion_stat_eq_trans)
          ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
        qed
        ultimately have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>N\<rparr> \<prec> R'"
          using FrR FrQ' `distinct A\<^sub>R` `distinct A\<^sub>P''` `A\<^sub>P'' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P''` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R`  `A\<^sub>R \<sharp>* M` `A\<^sub>Q' \<sharp>* R` `A\<^sub>Q' \<sharp>* K` `A\<^sub>Q' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* P` `A\<^sub>P'' \<sharp>* P` `A\<^sub>R \<sharp>* xvec`
                     `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R`  `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* K` `xvec \<sharp>* K` `distinct xvec` FrR
                     `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'` `A\<^sub>R \<sharp>* M'` `distinct yvec` `yvec \<sharp>* A\<^sub>R`
                     `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P''` `yvec \<sharp>* M'` `yvec \<sharp>* R` `A\<^sub>P'' \<sharp>* yvec` `A\<^sub>Q' \<sharp>* yvec`
          by(rule_tac A\<^sub>Q="A\<^sub>Q'" in comm2_aux) (assumption | simp | force)+
        note RTrans FrR P''PTrans FrP''P
        thus ?thesis using `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* P''` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* M'` `A\<^sub>P'' \<sharp>* A\<^sub>R` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* P` `A\<^sub>P'' \<sharp>* K` `xvec \<sharp>* R` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P''` `yvec \<sharp>* P` `uvec \<sharp>* \<Psi>` `uvec \<sharp>* R` `uvec \<sharp>* \<Psi>\<^sub>P''`
          unfolding \<pi>'
          by(rule_tac Comm1) (assumption | simp | force)+
      qed
      ultimately show ?thesis
        by(drule_tac tau_act_tau_chain) auto
    qed

    moreover from P'Chain have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>') \<otimes> \<one> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T"
      by(rule tau_chain_stat_eq) (metis Identity Assertion_stat_eq_sym)
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P"
      by(rule_tac tau_chain_par1) auto
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>' \<rhd> P' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P"
      by(rule tau_chain_stat_eq) (metis Associativity)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P' \<parallel> !P\<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P" using `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'`
      by(rule_tac tau_chain_stat_eq) (auto intro: composition_sym)
    hence "\<Psi> \<rhd> R' \<parallel> (P' \<parallel> !P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> (T \<parallel> !P)" using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* P'`
      by(rule_tac tau_chain_par2) auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P))" using `xvec \<sharp>* \<Psi>`
      by(rule tau_chain_res_chain_pres)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P))"
      by auto
    moreover have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P)), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel''"
    proof -
      from `((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', T, S) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>', T, S) \<in> Rel"
        by(rule StatEq) (metis Associativity)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R', T, S) \<in> Rel" using `\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'`
        by(rule_tac StatEq) (auto dest: composition_sym)

      with FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* S` `A\<^sub>R' \<sharp>* T` have "(\<Psi>, R' \<parallel> T, R' \<parallel> S) \<in> Rel"
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, (R' \<parallel> T) \<parallel> !P, (R' \<parallel> S) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> T) \<parallel> !P), \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> S) \<parallel> !P)) \<in> Rel" using `xvec \<sharp>* \<Psi>`
        by(rule ResPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P) \<in> Rel" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P`
        by(force intro: Trans ScopeExt)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P)), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P) \<in> Rel" using `xvec \<sharp>* \<Psi>`
        by(force intro: Trans ResPres Assoc)

      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !Q) \<in> Rel''"
        by(rule C1)
      moreover from `(\<one>, Q', S \<parallel> !Q) \<in> Rel'` have "(\<one> \<otimes> \<Psi>, Q', S \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', S \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity Assertion_stat_eq_sym Commutativity Assertion_stat_eq_trans)
      hence "(\<Psi>, R' \<parallel> Q', R' \<parallel> (S \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> S) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R' \<parallel> S) \<parallel> !Q, R' \<parallel> Q') \<in> Rel'" by(rule cSym')
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> S) \<parallel> !Q), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using `xvec \<sharp>* \<Psi>`
        by(rule ResPres')
      hence "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !Q, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q`
        by(force intro: Trans' ScopeExt'[THEN cSym'])
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  next
    case(c_comm2 \<Psi>\<^sub>Q M xvec N R' A\<^sub>R \<Psi>\<^sub>R K Q' A\<^sub>Q yvec zvec)
    from `A\<^sub>R \<sharp>* (P, Q, R)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    from `xvec \<sharp>* (P, Q, R)` have "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `yvec \<sharp>* (P, Q, R)` have "yvec \<sharp>* P" and "yvec \<sharp>* Q" and "yvec \<sharp>* R" by simp+
    from `zvec \<sharp>* (P, Q, R)` have "zvec \<sharp>* P" and "zvec \<sharp>* Q" and "zvec \<sharp>* R" by simp+
    have FrQ: "extract_frame(!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>_ @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` FrR `distinct A\<^sub>R` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* N` `A\<^sub>R \<sharp>* xvec` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<Psi>` `xvec \<sharp>* R` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* Q` `xvec \<sharp>* M` `distinct xvec` `A\<^sub>R \<sharp>* M`
    obtain p A\<^sub>R' \<Psi>\<^sub>R' \<Psi>' where FrR': "extract_frame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinct_perm p" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* R'" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* (p \<bullet> xvec)"
      by(rule_tac C="(\<Psi>, P, Q)"  and C'="(\<Psi>, P, Q)" in expand_frame) (assumption | simp)+

    from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>_ @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` S `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* R'`
    have  RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
      by(simp add: bound_output_chain_alpha'' residual_inject)
    from `(\<Psi>, P, Q) \<in> Rel` have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>_ @ K\<lparr>N\<rparr> \<prec> Q'` S `(p \<bullet> xvec) \<sharp>* Q`  `xvec \<sharp>* Q` `distinct_perm p`
    have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" 
      by(rule_tac input_alpha) auto
    then obtain \<pi> S where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> S" and "(\<one>, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel'" 
      using `guarded Q`
      by(fastforce dest: rBangActE)
    ultimately obtain P' \<pi>' T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" 
                             and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>') \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T" 
                             and "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'), T, S) \<in> Rel"
      by(fastforce dest: cSim dest!: weakSimE(1))

    from `A\<^sub>R' \<sharp>* N` `A\<^sub>R' \<sharp>* xvec` `A\<^sub>R' \<sharp>* (p \<bullet> xvec)` S have "A\<^sub>R' \<sharp>* (p \<bullet> N)"
      by(simp add: fresh_chain_simps)
    with PTrans `A\<^sub>R' \<sharp>* P` have "A\<^sub>R' \<sharp>* P'" by(force dest: weak_input_fresh_chain_derivative)
    with P'Chain have "A\<^sub>R' \<sharp>* T" by(force dest: tau_chain_fresh_chain)+
    from QTrans `A\<^sub>R' \<sharp>* Q` `A\<^sub>R' \<sharp>* (p \<bullet> N)` have "A\<^sub>R' \<sharp>* S" by(force dest: input_fresh_chain_derivative)

    obtain A\<^sub>Q' \<Psi>\<^sub>Q' where FrQ': "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q' \<sharp>* A\<^sub>R" and "A\<^sub>Q' \<sharp>* M" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* yvec" and "A\<^sub>Q' \<sharp>* K"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R, K, M, R, xvec, yvec)" in fresh_frame) auto
    from FrQ' `guarded Q` have "\<Psi>\<^sub>Q' \<simeq> \<one>" and "supp \<Psi>\<^sub>Q' = ({}::name set)" by(blast dest: guarded_stat_eq)+
    hence "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>Q'" by(auto simp add: fresh_star_def fresh_def)

    from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                             and NilImpP'': "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                             and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'"
      using FrQ' `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R` fresh_comp_chain
      by(drule_tac weak_transitionE) auto

    from `(p \<bullet> xvec) \<sharp>* P` `xvec \<sharp>* P` PChain have "(p \<bullet> xvec) \<sharp>* P''" and "xvec \<sharp>* P''" 
      by(force dest: tau_chain_fresh_chain)+
    from `(p \<bullet> xvec) \<sharp>* N` `distinct_perm p` have "xvec \<sharp>* (p \<bullet> N)"
      by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, where pi=p, symmetric]) simp
    with P''Trans `xvec \<sharp>* P''` have "xvec \<sharp>* P'" by(force dest: input_fresh_chain_derivative)
    hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])

    from P''Trans obtain A\<^sub>P'' \<Psi>\<^sub>P'' uvec M' where FrP'': "extract_frame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>"
      and \<pi>': "\<pi>' = Some(\<langle>A\<^sub>P''; uvec, M'\<rangle>)" and "distinct A\<^sub>P''" and "distinct uvec"
      and "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* uvec" and M'eqK: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'' \<turnstile> K \<leftrightarrow> M'"
      and "A\<^sub>P'' \<sharp>* Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* K"
      and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* yvec" and "A\<^sub>P'' \<sharp>* P" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* p"
      and "uvec \<sharp>* Q" and "uvec \<sharp>* \<Psi>\<^sub>R" and "uvec \<sharp>* A\<^sub>R" and "uvec \<sharp>* M" and "uvec \<sharp>* R" and "uvec \<sharp>* K"
      and "uvec \<sharp>* xvec" and "uvec \<sharp>* yvec" and "uvec \<sharp>* \<Psi>" and "uvec \<sharp>* P" and "uvec \<sharp>* P''" and "uvec \<sharp>* p"
      by(drule_tac input_provenance[where C="(\<Psi>,Q,\<Psi>\<^sub>R, A\<^sub>R, K, M, R, xvec, yvec,P,p)"]) auto

    from FrP'' `uvec \<sharp>* P''` `A\<^sub>P'' \<sharp>* uvec` have "uvec \<sharp>* \<Psi>\<^sub>P''" by(force dest: extract_frame_fresh_chain)

    from M'eqK have M'eqK': "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'"
      by (meson Assertion_stat_eq_def Assertion_stat_imp_def Associativity associativity_sym)

    from `A\<^sub>R \<sharp>* P` PChain have "A\<^sub>R \<sharp>* P''" by(rule_tac tau_chain_fresh_chain)
    from `yvec \<sharp>* P` PChain have "yvec \<sharp>* P''" by(rule_tac tau_chain_fresh_chain)

    from FrP'' `A\<^sub>R \<sharp>* P''` `A\<^sub>P'' \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P''" by(auto dest: extract_frame_fresh_chain)

    from FrP'' `yvec \<sharp>* P''` `A\<^sub>P'' \<sharp>* yvec` have "yvec \<sharp>* \<Psi>\<^sub>P''" by(auto dest: extract_frame_fresh_chain)

    from `A\<^sub>R \<sharp>* P''` P''Trans have "A\<^sub>R \<sharp>* \<pi>'" by(rule_tac trans_fresh_provenance)
    hence "A\<^sub>R \<sharp>* M'" unfolding \<pi>'
      using `A\<^sub>P'' \<sharp>* A\<^sub>R` using `uvec \<sharp>* A\<^sub>R`
      by (simp add: frame_chain_fresh_chain'')
    from `yvec \<sharp>* P''` P''Trans have "yvec \<sharp>* \<pi>'" by(rule_tac trans_fresh_provenance)
    hence "yvec \<sharp>* M'" unfolding \<pi>'
      using `A\<^sub>P'' \<sharp>* yvec` using `uvec \<sharp>* yvec`
      by (simp add: frame_chain_fresh_chain'')

    from FrQ' `A\<^sub>R \<sharp>* Q` `A\<^sub>Q' \<sharp>* A\<^sub>R` have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'" by(auto dest: extract_frame_fresh_chain)

    from PChain have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))"
    proof(induct rule: tau_chain_cases)
      case tau_base
      from FrP'' `guarded P` `P = P''` have "\<Psi>\<^sub>P'' \<simeq> \<one>" and "supp \<Psi>\<^sub>P'' = ({}::name set)" by(blast dest: guarded_stat_eq)+
      with RTrans FrQ have "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
        using Assertion_stat_eq_sym composition_sym
        by(force elim: stat_eq_transition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
        using `extract_frame R = _` `\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'`
              Frame_stat_imp_refl `distinct A\<^sub>R` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>`
              `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* M'`
              `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* R` `A\<^sub>Q \<sharp>* K`
              `distinct  yvec` iffD1[OF fresh_chain_sym, OF `yvec \<sharp>* A\<^sub>R`]
              `A\<^sub>R \<sharp>* M'` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P''` `yvec \<sharp>* M'`
              `yvec \<sharp>* R` `yvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* A\<^sub>Q`
        by(rule comm1_aux)
      hence "\<Psi> \<otimes> \<one> \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
        using Assertion_stat_eq_sym composition_sym `\<Psi>\<^sub>P'' \<simeq> \<one>`
        by(force elim: stat_eq_transition)
      moreover note FrR
      moreover from P''Trans `P = P''` have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr>\<prec> P'" by simp
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" 
        by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)"
        by(rule_tac Par1[where Q="!P" and A\<^sub>Q="[]",simplified,unfolded map_option.id[unfolded id_def]]) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>Some(\<langle>\<epsilon>, \<langle>(A\<^sub>P'' @ uvec), M'\<rangle>\<rangle>) @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)" using `guarded P`
       unfolding \<pi>'
       by(rule Bang[where \<pi>=\<pi>', unfolded \<pi>',simplified])
      ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))" using `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* M` `(p \<bullet> xvec) \<sharp>* P`
        `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P` `A\<^sub>P'' \<sharp>* \<Psi>` `uvec \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `uvec \<sharp>* R`
        by(force intro: Comm2[where A\<^sub>Q="[]" and zvec = "A\<^sub>P'' @ uvec",simplified])
      thus ?case by(rule tau_act_tau_chain)
    next
      case tau_step
      from `\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tau_step_chain_stat_eq) (metis Identity Assertion_stat_eq_sym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" by(rule_tac tau_step_chain_par1) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" using `guarded P` by(rule tau_step_chain_bang)
      hence  "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R \<parallel> (P'' \<parallel> !P)" using FrR `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P`
        by(rule_tac tau_step_chain_par2) auto
      moreover have "\<Psi> \<rhd> R \<parallel> (P'' \<parallel> !P) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))"
      proof -
        from FrQ `\<Psi>\<^sub>Q' \<simeq> \<one>` RTrans have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
          by simp (metis stat_eq_transition Assertion_stat_eq_sym composition_sym)
        moreover from P''Trans have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P'' \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'"
          by(rule stat_eq_transition) (metis Identity Assertion_stat_eq_sym)
        hence P''PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<parallel> !P \<longmapsto>\<pi>' @ K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)"
          by(rule_tac Par1[where Q="!P" and A\<^sub>Q="[]",simplified,unfolded map_option.id[unfolded id_def]]) auto
        moreover from FrP'' have FrP''P: "extract_frame(P'' \<parallel> !P) = \<langle>A\<^sub>P'', \<Psi>\<^sub>P'' \<otimes> \<one>\<rangle>"
          by auto
        moreover from `_ \<otimes> _ \<otimes> _ \<turnstile> K \<leftrightarrow> M'` have "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'"
          using Assertion_stat_eq_sym Composition Identity composition_sym stat_eq_ent by blast
        moreover have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>)) \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle>"
            by(rule_tac frame_res_chain_pres, simp)
              (metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym)
          moreover from NilImpP'' FrQ FrP'' `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R` fresh_comp_chain have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle>"
            by auto
          moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(rule frame_res_chain_pres, simp) 
              (metis Identity Assertion_stat_eq_sym Associativity Commutativity Composition Assertion_stat_eq_trans)
          ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
        qed
        ultimately have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; yvec, K\<rangle>) @ M'\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
          using FrR FrQ' `distinct A\<^sub>R` `distinct A\<^sub>P''` `A\<^sub>P'' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P''` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R`  `A\<^sub>R \<sharp>* M` `A\<^sub>Q' \<sharp>* R` `A\<^sub>Q' \<sharp>* K` `A\<^sub>Q' \<sharp>* A\<^sub>R` `A\<^sub>R \<sharp>* P` `A\<^sub>P'' \<sharp>* P`
                     `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R`  `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* K` FrR `A\<^sub>R \<sharp>* \<Psi>\<^sub>P''` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q'` `A\<^sub>R \<sharp>* M'` `distinct yvec` `yvec \<sharp>* A\<^sub>R`
                     `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P''` `yvec \<sharp>* M'` `yvec \<sharp>* R` `A\<^sub>P'' \<sharp>* yvec` `A\<^sub>Q' \<sharp>* yvec`
          by(rule_tac A\<^sub>Q="A\<^sub>Q'" in comm1_aux) (assumption | simp | force)+
        note RTrans FrR P''PTrans FrP''P
        thus ?thesis using `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* P''` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* M'` `A\<^sub>P'' \<sharp>* A\<^sub>R` `A\<^sub>P'' \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `A\<^sub>P'' \<sharp>* P''` `A\<^sub>P'' \<sharp>* P` `A\<^sub>P'' \<sharp>* K` `(p \<bullet> xvec) \<sharp>* P''` `(p \<bullet> xvec) \<sharp>* P`
                           `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>R` `yvec \<sharp>* P` `A\<^sub>P'' \<sharp>* \<Psi>` `uvec \<sharp>* \<Psi>` `A\<^sub>P'' \<sharp>* R` `uvec \<sharp>* R`  `yvec \<sharp>* P''` `uvec \<sharp>* \<Psi>\<^sub>P''`
          unfolding \<pi>'
          by(rule_tac Comm2) (assumption | simp | force)+
      qed
      ultimately show ?thesis
        by(drule_tac tau_act_tau_chain) auto
    qed
    hence "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> P') \<parallel> !P))" 
      using `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* (p \<bullet> P')` `(p \<bullet> xvec) \<sharp>* R'` S `distinct_perm p`
      by(subst res_chain_alpha[where p=p]) auto
    moreover from P'Chain have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)"
      by(rule tau_chain_eqvt)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinct_perm p`
    have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)" by(simp add: eqvts)
    hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>') \<otimes> \<one> \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)"
      by(rule tau_chain_stat_eq) (metis Identity Assertion_stat_eq_sym)
    hence "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P"
      by(rule_tac tau_chain_par1) auto
    hence "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P"
      by(rule tau_chain_stat_eq) (metis Associativity)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P" using `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq>  \<Psi>\<^sub>R'`
      by(rule_tac tau_chain_stat_eq) (auto intro: composition_sym)
    hence "\<Psi> \<rhd> R' \<parallel> ((p \<bullet> P') \<parallel> !P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> ((p \<bullet> T) \<parallel> !P)" 
      using FrR' `A\<^sub>R' \<sharp>* \<Psi>` `A\<^sub>R' \<sharp>* P` `A\<^sub>R' \<sharp>* P'` `A\<^sub>R' \<sharp>* xvec` `A\<^sub>R' \<sharp>* (p \<bullet> xvec)` S
      by(rule_tac tau_chain_par2) (auto simp add: fresh_chain_simps)
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> P') \<parallel> !P)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P))" using `xvec \<sharp>* \<Psi>`
      by(rule tau_chain_res_chain_pres)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P))"
      by auto
    moreover have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P)), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel''"
    proof -
      from `((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'), T, S) \<in> Rel` 
      have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>')), (p \<bullet> T), (p \<bullet> S)) \<in> Rel"
        by(rule Closed)
      with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `distinct_perm p` S
      have "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', p \<bullet> T, p \<bullet> S) \<in> Rel"
        by(simp add: eqvts)
      hence "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>', p \<bullet> T, p \<bullet> S) \<in> Rel"
        by(rule StatEq) (metis Associativity)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R', p \<bullet> T, p \<bullet> S) \<in> Rel" using `(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'`
        by(rule_tac StatEq) (auto dest: composition_sym)
      moreover from `A\<^sub>R' \<sharp>* S` `A\<^sub>R' \<sharp>* T` `A\<^sub>R' \<sharp>* xvec` `A\<^sub>R' \<sharp>* (p \<bullet> xvec)` S
      have "A\<^sub>R' \<sharp>* (p \<bullet> S)" and "A\<^sub>R' \<sharp>* (p \<bullet> T)"
        by(simp add: fresh_chain_simps)+
      ultimately have "(\<Psi>, R' \<parallel> (p \<bullet> T), R' \<parallel> (p \<bullet> S)) \<in> Rel" using FrR' `A\<^sub>R' \<sharp>* \<Psi>`
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, (R' \<parallel> (p \<bullet> T)) \<parallel> !P, (R' \<parallel> (p \<bullet> S)) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> T)) \<parallel> !P), \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> S)) \<parallel> !P)) \<in> Rel" 
        using `xvec \<sharp>* \<Psi>`
        by(rule ResPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P) \<in> Rel" 
        using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P`
        by(force intro: Trans ScopeExt)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P)), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P) \<in> Rel"
        using `xvec \<sharp>* \<Psi>`
        by(force intro: Trans ResPres Assoc)
      moreover from `(\<Psi>, P, Q) \<in> Rel` `guarded P` `guarded Q` 
      have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !Q) \<in> Rel''"
        by(rule C1)
      moreover from `(\<one>, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel'` 
      have "(p \<bullet> \<one>, p \<bullet> p \<bullet> Q', p \<bullet> (S \<parallel> !Q)) \<in> Rel'" by(rule Closed')
      with `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` S `distinct_perm p` 
        have "(\<one>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" by(simp add: eqvts)
      hence "(\<one> \<otimes> \<Psi>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity Assertion_stat_eq_sym Commutativity Assertion_stat_eq_trans)
      hence "(\<Psi>, R' \<parallel> Q', R' \<parallel> ((p \<bullet> S) \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> (p \<bullet> S)) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R' \<parallel> (p \<bullet> S)) \<parallel> !Q, R' \<parallel> Q') \<in> Rel'" by(rule cSym')
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> S)) \<parallel> !Q), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using `xvec \<sharp>* \<Psi>`
        by(rule ResPres')
      hence "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !Q, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q`
        by(force intro: Trans' ScopeExt'[THEN cSym'])
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  qed
qed
notation relcomp (infixr "O" 75)
end

end
