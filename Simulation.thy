theory Simulation
  imports Semantics
begin

context env begin

definition
  "simulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                   ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                   ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>[_] _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>[Rel] Q \<equiv> \<forall>\<alpha> \<pi> Q'. \<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> (\<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel)"

abbreviation
  simulation_nil_judge ("_ \<leadsto>[_] _" [80, 80, 80] 80) where "P \<leadsto>[Rel] Q \<equiv> S_bottom' \<rhd> P \<leadsto>[Rel] Q"

lemma simI[consumes 1, case_names c_sim]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     Sim: "\<And>\<pi> \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<pi>; bn \<alpha>  \<sharp>* \<Psi>; distinct(bn \<alpha>);
                         bn \<alpha> \<sharp>* (subject \<alpha>); bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow> \<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
proof(auto simp add: simulation_def)
  fix \<pi> \<alpha> Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P"
  thus "\<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
  proof(nominal_induct \<alpha> rule: action.strong_induct)
    case(In M N)
    thus ?case by(rule_tac Sim) auto
  next
    case(Out M xvec N)
    moreover {
      fix M xvec N Q'
      assume "(xvec::name list) \<sharp>* \<Psi>" and "xvec \<sharp>* P"
      obtain p where xvec_fresh_psi: "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* \<Psi>"
                 and xvec_freshM: "(p \<bullet> xvec) \<sharp>* (M::'a)"
                 and xvec_freshN: "(p \<bullet> xvec) \<sharp>* (N::'a)"
                 and xvec_freshP: "(p \<bullet> xvec) \<sharp>* P"
                 and xvec_freshQ: "(p \<bullet> xvec) \<sharp>* Q"
                 and xvec_fresh_pi: "(p \<bullet> xvec) \<sharp>* \<pi>"
                 and xvec_freshQ': "(p \<bullet> xvec) \<sharp>* (Q'::('a, 'b, 'c) psi)"
                 and xvec_freshC: "(p \<bullet> xvec) \<sharp>* C"
                 and xvec_freshxvec: "(p \<bullet> xvec) \<sharp>* xvec"
                 and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
                 and dpr: "distinct_perm p"
	by(rule_tac xvec=xvec and c="(\<Psi>, M, Q, N, P, Q', \<pi>, xvec, C)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)

      from `(p \<bullet> xvec) \<sharp>* M` `distinct_perm p` have "xvec \<sharp>* (p \<bullet> M)"
	by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, where pi=p, symmetric]) simp

      assume Trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      with xvec_freshN xvec_freshQ' S
      have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
	by(simp add: bound_output_chain_alpha'' residual_inject)
      moreover hence "distinct(p \<bullet> xvec)"  by(auto dest: bound_output_distinct)
      
      moreover note xvec_fresh_psi xvec_freshP xvec_freshQ xvec_freshM xvec_freshC xvec_fresh_pi
      ultimately obtain \<pi>' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
                            and P'_rel_q': "(\<Psi>, P', p \<bullet> Q') \<in> Rel"
	by(drule_tac Sim) auto
      hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p\<bullet>\<pi>') @ (p \<bullet> (M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'))"
	by(rule_tac semantics.eqvt)
      moreover from xvec_freshP `xvec \<sharp>* P` P_trans
      have "xvec \<sharp>* \<pi>'"  "(p\<bullet>xvec) \<sharp>* \<pi>'"
        by(auto intro: trans_fresh_provenance)
      moreover note `xvec \<sharp>* \<Psi>` xvec_fresh_psi `xvec \<sharp>* P` xvec_freshP S dpr
      ultimately have "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
	by(simp add: eqvts name_set_fresh_fresh)
      with `xvec \<sharp>* \<Psi>` xvec_fresh_psi `xvec \<sharp>* P` xvec_freshP S `xvec \<sharp>* (p \<bullet> M)`
      have "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ (p \<bullet> p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
       by(rule_tac output_perm_subject)
         (simp add: fresh_star_def | assumption)+

      with dpr have "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
	by simp

      moreover from P'_rel_q' Eqvt have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
	apply(simp add: eqvt_def eqvts)
	apply(erule_tac x="(\<Psi>, P', p \<bullet> Q')" in ballE)
	apply(erule_tac x="p" in allE)
	by(auto simp add: eqvts)
      with `xvec \<sharp>* \<Psi>` xvec_fresh_psi S dpr have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
      ultimately have "\<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto> \<pi>' @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
	by blast
    }
    ultimately show ?case by force
  next
    case Tau
    thus ?case by(rule_tac Sim) auto
  qed
qed

lemma simI2[case_names c_sim]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Sim: "\<And>\<pi> \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha>  \<sharp>* \<Psi>; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> \<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using assms
by(force simp add: simulation_def dest: bound_output_distinct)

lemma sim_i_chain_fresh[consumes 4, case_names c_sim]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* Q"
  and     Sim: "\<And>\<pi> \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<pi>;
                         bn \<alpha> \<sharp>* subject \<alpha>; distinct(bn \<alpha>); bn \<alpha> \<sharp>* C; xvec \<sharp>* \<alpha>; xvec \<sharp>* \<pi>; xvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
                         \<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using `eqvt Rel`
proof(induct rule: simI[where C="(xvec, C)"])
  case(c_sim \<pi> \<alpha> Q')
  from `xvec \<sharp>* Q` `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` have "xvec \<sharp>* \<pi>"
      by(auto intro: trans_fresh_provenance)
  from `bn \<alpha> \<sharp>* (xvec, C)` have "bn \<alpha> \<sharp>* xvec" and "bn \<alpha> \<sharp>* C" by(simp add: fresh_chain_sym)+ 
  obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and  "(p \<bullet> xvec) \<sharp>* P" and  "(p \<bullet> xvec) \<sharp>* Q" and  "(p \<bullet> xvec) \<sharp>* \<pi>"
                         and  "(p \<bullet> xvec) \<sharp>* \<alpha>" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                         and "distinct_perm p"
    by(rule_tac c="(\<Psi>, P, Q, \<pi>, \<alpha>)" and xvec=xvec in name_list_avoiding) auto
  show ?case
  proof(cases rule: action_cases[where \<alpha>=\<alpha>])
    case(c_input M N)
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha>=M\<lparr>N\<rparr>` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q) \<longmapsto>(p\<bullet>\<pi>) @ (p \<bullet> (M\<lparr>N\<rparr> \<prec> Q'))"
      by(force intro: semantics.eqvt)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` S `(p\<bullet>xvec) \<sharp>* \<pi>` `xvec \<sharp>* \<pi>`
    have Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')"
      by(simp add: eqvts)
    moreover from `(p \<bullet> xvec) \<sharp>* \<alpha>` have "(p \<bullet> (p \<bullet> xvec)) \<sharp>* (p \<bullet> \<alpha>)"
      by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])  
    with `distinct_perm p` `\<alpha>=M\<lparr>N\<rparr>` have "xvec \<sharp>* (p \<bullet> M)" and "xvec \<sharp>* (p \<bullet> N)" by simp+
    moreover with Q_trans `xvec \<sharp>* Q` have "xvec \<sharp>* (p \<bullet> Q')" by(rule_tac input_fresh_chain_derivative)
    ultimately have "\<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto> \<pi>' @ (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P' \<and> (\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      using `xvec \<sharp>* \<pi>`
      by(rule_tac Sim) (assumption | simp)+
    then obtain \<pi>' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto> \<pi>' @ (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" and P'_rel_q': "(\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      by blast
    from P_trans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto> (p\<bullet>\<pi>') @ (p \<bullet> ((p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P'))"
      by(rule semantics.eqvt)
    moreover from P_trans `xvec \<sharp>* P` `(p\<bullet>xvec) \<sharp>* P` have "xvec \<sharp>* \<pi>'" "(p\<bullet>xvec) \<sharp>* \<pi>'"
      by(auto intro: trans_fresh_provenance)
    moreover note `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S `distinct_perm p`
    ultimately have "\<Psi> \<rhd> P \<longmapsto> \<pi>' @ M\<lparr>N\<rparr> \<prec> (p \<bullet> P')"
      by(simp add: eqvts)
    moreover from P'_rel_q' `eqvt Rel` have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      by(auto simp add: eqvt_def)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinct_perm p`
    have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
    ultimately show ?thesis using `\<alpha>=M\<lparr>N\<rparr>` by blast
  next
    case(c_output M yvec N)
    from `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` have "distinct yvec" and "yvec \<sharp>* M" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q) \<longmapsto>(p \<bullet> \<pi>) @ (p \<bullet> (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> Q'))"
      by(force intro: semantics.eqvt)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* Q` S `xvec \<sharp>* \<pi>` `(p\<bullet>xvec) \<sharp>* \<pi>`
    have Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by(simp add: eqvts)
    with S `bn \<alpha> \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* \<alpha>` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by simp
    moreover from `(p \<bullet> xvec) \<sharp>* \<alpha>` have "(p \<bullet> (p \<bullet> xvec)) \<sharp>* (p \<bullet> \<alpha>)"
      by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])  
    with `distinct_perm p` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` have "xvec \<sharp>* (p \<bullet> M)" and "xvec \<sharp>* (p \<bullet> N)" and "xvec \<sharp>* (p \<bullet> yvec)" by simp+
    moreover with Q_trans `xvec \<sharp>* Q` `distinct yvec` `yvec \<sharp>* M` have "xvec \<sharp>* (p \<bullet> Q')"
      by(drule_tac output_fresh_chain_derivative(2)) (auto simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    moreover from `yvec \<sharp>* M` S `bn \<alpha> \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* \<alpha>` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` `distinct_perm p`
    have "yvec \<sharp>* (p \<bullet> M)" by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi=p]) simp
    ultimately have "\<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ (p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P' \<and> (\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q``bn \<alpha> \<sharp>* xvec` `bn \<alpha> \<sharp>* C` `yvec \<sharp>* M` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` `distinct yvec` `bn \<alpha> \<sharp>* \<pi>` `xvec \<sharp>* \<pi>`
      by(rule_tac Sim) auto
    then obtain \<pi>' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto> \<pi>' @ (p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'" and P'_rel_q': "(\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      by blast
    from P_trans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto> (p\<bullet>\<pi>') @ (p \<bullet> ((p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'))"
      by(rule semantics.eqvt)
    moreover from P_trans `xvec \<sharp>* P` `(p\<bullet>xvec) \<sharp>* P` have "xvec \<sharp>* \<pi>'" "(p\<bullet>xvec) \<sharp>* \<pi>'"
      by(auto intro: trans_fresh_provenance)    
    moreover note `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` S `distinct_perm p` `bn \<alpha> \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* \<alpha>` `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>`
    ultimately have "\<Psi> \<rhd> P \<longmapsto> \<pi>' @ M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'_rel_q' `eqvt Rel` have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      by(auto simp add: eqvt_def)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinct_perm p`
    have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
    ultimately show ?thesis using `\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>` by blast
  next
    case c_tau
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha> = \<tau>` `xvec \<sharp>* Q` have "xvec \<sharp>* Q'"
      by(blast dest: tau_fresh_chain_derivative)
    with `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha> = \<tau>` `xvec \<sharp>* \<pi>`
    show ?thesis by(drule_tac Sim) auto
  qed
qed

lemma sim_i_fresh[consumes 4, case_names c_sim]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   x   :: name
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> P"
  and     "x \<sharp> Q"
  and     "\<And>\<pi> \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<pi>;
                    bn \<alpha> \<sharp>* subject \<alpha>; distinct(bn \<alpha>); bn \<alpha> \<sharp>* C; x \<sharp> \<alpha>; x \<sharp> Q'; x \<sharp> \<pi>\<rbrakk> \<Longrightarrow>
                    \<exists>\<pi>' P'. \<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using assms
by(rule_tac xvec="[x]" and C=C in sim_i_chain_fresh) auto

lemma simE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>[Rel] Q"

  shows "\<And>\<pi> \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P\<rbrakk> \<Longrightarrow> \<exists>\<pi> P'. \<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: simulation_def)

lemma sim_closed_aux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes Eqvt_rel: "eqvt Rel"
  and     P_simQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
using Eqvt_rel
proof(induct rule: simI[of _ _ _ _ "(\<Psi>, P, p)"])
  case(c_sim \<pi> \<alpha> Q')
  from `p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> \<pi>) @ (rev p \<bullet> (\<alpha> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>(rev p \<bullet> \<pi>) @ (rev p \<bullet> \<alpha>) \<prec> (rev p \<bullet> Q')"
    by(simp add: eqvts)
  moreover with `bn \<alpha> \<sharp>* (\<Psi>, P, p)` have "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* p" by simp+
  ultimately obtain \<pi>' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ (rev p \<bullet> \<alpha>) \<prec> P'"
                         and P'_rel_q': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    using P_simQ
    by(force dest!: simE fresh_chain_perm_simp simp add: eqvts)
  from P_trans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p\<bullet> \<pi>') @ (p \<bullet> ((rev p \<bullet> \<alpha>) \<prec> P'))"
    by(rule semantics.eqvt)
  with `bn \<alpha> \<sharp>* p` have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p\<bullet>\<pi>') @ \<alpha> \<prec> (p \<bullet> P')"
    by(simp add: eqvts fresh_chain_perm_simp)
  moreover from P'_rel_q' Eqvt_rel have "(p \<bullet> (\<Psi>, P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
  ultimately show ?case by blast
qed

lemma sim_closed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes Eqvt_rel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
  and   "P \<leadsto>[Rel] Q \<Longrightarrow> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
using Eqvt_rel
by(force dest: sim_closed_aux simp add: perm_bottom)+

lemma reflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] P"
using assms
by(force simp add: simulation_def)
(*
lemma sim_res[consumes 11, case_names c_open c_res]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Q'   :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times>  ('a, 'b, 'c) psi) set"
  and   C    :: "'d::fs_name"
  and   \<Psi>'   :: 'b

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     "x \<sharp> xvec"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> \<Psi>'"
  and     "x \<sharp> P"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* \<Psi>'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* C"
  and     r_open: "\<And>xvec1 xvec2 y N Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'; x \<in> supp N; x \<sharp> xvec1; x \<sharp> xvec2; xvec1 \<sharp>* \<Psi>; xvec1 \<sharp>* \<Psi>'; xvec1 \<sharp>* P; xvec1 \<sharp>* C;
                                         xvec2 \<sharp>* \<Psi>; xvec2 \<sharp>* \<Psi>'; xvec2 \<sharp>* P; xvec2 \<sharp>* C; x \<noteq> y; y \<sharp> xvec1; y \<sharp> xvec2; y \<sharp> \<Psi>; y \<sharp> P; y \<sharp> C\<rbrakk> \<Longrightarrow> 
                                         \<exists>P'. \<Psi>' \<rhd> P \<longmapsto>(([(x, y)] \<bullet> G) (xvec1@x#xvec2) N P') \<and> (\<Psi>', P', ([(x, y)] \<bullet> F) Q') \<in> Rel"
  and     r_scope: "\<And>N Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto> M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; x \<sharp> N\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi>' \<rhd> P \<longmapsto>(G xvec N P') \<and> (\<Psi>', P', F (\<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
  
  shows "\<exists>P'. \<Psi>' \<rhd> P \<longmapsto>(G xvec N P') \<and> (\<Psi>', P', F Q') \<in> Rel"
using Trans `x \<sharp> xvec` `x \<sharp> \<Psi>` `x \<sharp> M`
proof(induct rule: res_casesB)
  case(c_open xvec1 xvec2 y N Q')
  note `\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')`
  moreover from `y \<in> supp N` have "([(x, y)] \<bullet> y) \<in> [(x, y)] \<bullet> (supp N)"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with `x \<noteq> y` have "x \<in> supp([(x, y)] \<bullet> N)" by(simp add: calc_atm eqvts)
  moreover from `xvec = xvec1@y#xvec2` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>'` `xvec \<sharp>* P` `xvec \<sharp>* C` `x \<sharp> xvec`
  have "xvec1 \<sharp>* \<Psi>" and "xvec1 \<sharp>* \<Psi>'" and  "xvec1 \<sharp>* P" and  "xvec1 \<sharp>* C"
   and "xvec2 \<sharp>* \<Psi>" and "xvec2 \<sharp>* \<Psi>'"  and "xvec2 \<sharp>* P" and "xvec2 \<sharp>* C"
   and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> P" and "x \<sharp> xvec1" and "x \<sharp> xvec2" and "y \<sharp> C"
    by(simp add: fresh_list_cons fresh_list_append)+ 
  ultimately obtain P' where P_trans: "\<Psi>' \<rhd> P \<longmapsto>(([(x, y)] \<bullet> G) (xvec1@x#xvec2) ([(x, y)] \<bullet> N) P')"
                         and P'_rel_q': "(\<Psi>', P', ([(x, y)] \<bullet> F) ([(x, y)] \<bullet> Q')) \<in> Rel"
    using `y \<sharp> xvec1` `y \<sharp> xvec2` `x \<noteq> y`
    by(blast dest: r_open)
  
  from P_trans have "([(x, y)] \<bullet> \<Psi>') \<rhd> ([(x, y)] \<bullet> P) \<longmapsto> [(x, y)] \<bullet> (([(x, y)] \<bullet> G) (xvec1@x#xvec2) ([(x, y)] \<bullet> N) P')"
    by(rule semantics.eqvt)
  with `x \<sharp> \<Psi>'` `y \<sharp> \<Psi>'` `x \<sharp> P` `y \<sharp> P` `x \<sharp> xvec1` `y \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec2` `x \<noteq> y` `xvec = xvec1@y#xvec2`
  have "\<Psi>' \<rhd> P \<longmapsto>(G xvec N ([(x, y)] \<bullet> P'))"
    by(simp add: pt_fun_app_eq perm_fun_def eqvts calc_atm)
  moreover from P'_rel_q' `eqvt Rel` have "([(x, y)] \<bullet> \<Psi>', [(x, y)] \<bullet> P', ([(x, y)] \<bullet> (([(x, y)] \<bullet> F) ([(x, y)] \<bullet> Q')))) \<in> Rel"
    by(simp only: eqvt_def) auto
  with `x \<sharp> \<Psi>'` `y \<sharp> \<Psi>'` `x \<noteq> y`have "(\<Psi>', [(x, y)] \<bullet> P', F Q') \<in> Rel"
    by(simp add: eqvts pt_fun_app_eq[OF pt_name_inst, OF at_name_inst, of _ "([(x, y)] \<bullet> F)"])
  ultimately show ?case by blast
next
  case(c_res N Q')
  thus ?case by(blast intro: r_scope)
qed
*)
lemma transitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes P_simQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     Q_simR: "\<Psi> \<rhd> Q \<leadsto>[Rel'] R"
  and     Eqvt: "eqvt Rel''"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel''] R"
using `eqvt Rel''`
proof(induct rule: simI[where C=Q])
  case(c_sim \<pi> \<alpha> R')
  from Q_simR `\<Psi> \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'` `(bn \<alpha>) \<sharp>* \<Psi>` `(bn \<alpha>) \<sharp>* Q`
  obtain \<pi>' Q' where Q_trans: "\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and Q'_rel'_r': "(\<Psi>, Q', R') \<in> Rel'"
    by(blast dest: simE)
  from P_simQ Q_trans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  obtain \<pi>'' P' where P_trans: "\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'" and P'_rel_q': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  with P_trans Q'_rel'_r' P'_rel_q' Set
  show ?case by blast
qed

lemma stat_eq_sim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes P_simQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel'"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>'' R S \<Psi>'''. \<lbrakk>(\<Psi>'', R, S) \<in> Rel; \<Psi>'' \<simeq> \<Psi>'''\<rbrakk> \<Longrightarrow> (\<Psi>''', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto>[Rel'] Q"
using `eqvt Rel'`
proof(induct rule: simI[of _ _ _ _ \<Psi>])
  case(c_sim \<pi> \<alpha> Q')
  from `\<Psi>' \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<Psi> \<simeq> \<Psi>'`
  have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" by(metis stat_eq_transition Assertion_stat_eq_sym)
  with P_simQ `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  obtain \<pi>' P' where "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'" and "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from `\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'"
    by(rule stat_eq_transition)
  moreover from `(\<Psi>, P', Q') \<in> Rel` `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma monotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto>[A] Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto>[B] Q"
using assms
by(simp (no_asm) add: simulation_def) (force dest: simE)

end

end

