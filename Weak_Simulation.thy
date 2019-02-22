(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Simulation
  imports Simulation Tau_Chain
begin

context env begin

definition
  "weakSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto><_> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto><Rel> Q \<equiv> (\<forall>\<Psi>' \<alpha> \<pi> Q'. \<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> \<alpha> \<noteq> \<tau> \<longrightarrow>
                      (\<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel))) \<and> 
                      (\<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel))"

abbreviation
  weakSimulationNilJudge ("_ \<leadsto><_> _" [80, 80, 80] 80) where "P \<leadsto><Rel> Q \<equiv> \<one> \<rhd> P \<leadsto><Rel> Q"

lemma weakSimI[consumes 1, case_names c_act c_tau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     rAct: "\<And>\<Psi>' \<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q;
                               bn \<alpha> \<sharp>* \<pi>;
                              bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                         
                              \<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(auto simp add: weakSimulation_def)
  fix \<Psi>' \<alpha> \<pi> Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "\<alpha> \<noteq> \<tau>"
  thus "\<exists>P''. (\<exists>\<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'') \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  proof(nominal_induct \<alpha> rule: action.strong_induct)
    case(In M N)
    thus ?case
      by(drule_tac rAct) auto
  next
    case(Out M xvec N)
    from `bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` `bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "distinct xvec" by(force dest: bound_output_distinct)
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* xvec"
               and"(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* xvec" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* \<pi>"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinct_perm p"
      by(rule_tac xvec=xvec and c="(\<Psi>, M, Q, N, P, Q', xvec, C, \<Psi>',\<pi>)" in name_list_avoiding)
        (auto simp add: eqvts fresh_star_prod)
    from `distinct xvec` have "distinct(p \<bullet> xvec)" by simp
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q'` S 
    have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')" by(simp add: bound_output_chain_alpha'' residual_inject)

    then obtain P'' P' \<pi> where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P''" 
                         and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                         and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q') \<in> Rel"
      using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* M` `(p \<bullet> xvec) \<sharp>* C` `(p \<bullet> xvec) \<sharp>* \<pi>` `distinct(p \<bullet> xvec)`
      by(drule_tac \<Psi>'="p \<bullet> \<Psi>'" in rAct) auto
    from PTrans S `distinct_perm p` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* M` `distinct xvec` 
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')" 
      by(rule_tac weak_output_alpha) auto
    moreover from P''Chain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>'` S `distinct_perm p`
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt S `distinct_perm p` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with `xvec \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* \<Psi>` S `distinct_perm p`
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?case by blast
  next
    case Tau
    thus ?case by simp
  qed
next
  fix Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(rule rTau)
qed

lemma weakSimI2[case_names c_act c_tau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes rOutput: "\<And>\<Psi>' \<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                \<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms by(simp add: weakSimulation_def)

lemma weakSimIChainFresh[consumes 4, case_names c_output c_input]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* Q"
  and     rAct: "\<And>\<Psi>' \<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; \<alpha> \<noteq> \<tau>;
                             bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; yvec \<sharp>* \<alpha>; yvec \<sharp>* Q'; yvec \<sharp>* \<Psi>'; yvec \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
                             \<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau: "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'; yvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using `eqvt Rel`
proof(induct rule: weakSimI[of _ _ _ _ "(yvec, C)"])
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  obtain p::"name prm" where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P" and  "(p \<bullet> yvec) \<sharp>* Q"
                         and  "(p \<bullet> yvec) \<sharp>* \<alpha>" and "(p \<bullet> yvec) \<sharp>* \<Psi>'" and "(p \<bullet> yvec) \<sharp>* \<pi>"
                         and "(p \<bullet> yvec) \<sharp>* Q'" and S: "(set p) \<subseteq> set yvec \<times> set(p \<bullet> yvec)"
                         and "distinct_perm p"
    by(rule_tac c="(\<Psi>, P, Q, \<alpha>, Q', \<Psi>', \<pi>)" and xvec=yvec in name_list_avoiding) auto
  from `bn \<alpha> \<sharp>* (yvec, C)` have "bn \<alpha> \<sharp>* yvec" and "bn \<alpha> \<sharp>* C" by(simp add: fresh_chain_sym)+ 
  show ?case
  proof(cases rule: action_cases[where \<alpha> = \<alpha>])
    case(c_input M N)
    from `(p \<bullet> yvec) \<sharp>* \<alpha>` `\<alpha> = M\<lparr>N\<rparr>` have "(p \<bullet> yvec) \<sharp>* M" and  "(p \<bullet> yvec) \<sharp>* N" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `yvec \<sharp>* Q` have "yvec \<sharp>* \<pi>"
     by(rule trans_fresh_provenance)
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<alpha> = M\<lparr>N\<rparr>` `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` S
         `yvec \<sharp>* \<pi>` `(p \<bullet> yvec) \<sharp>* \<pi>`
    have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" 
      by(drule_tac pi=p in semantics.eqvt) (simp add: eqvts)
    moreover from `(p \<bullet> yvec) \<sharp>* M` have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* N` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> N)" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> N)" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* Q'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> Q')" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> Q')" by simp
    moreover from `(p \<bullet> yvec) \<sharp>* \<Psi>'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    moreover note `yvec \<sharp>* \<pi>`
    ultimately obtain P' \<pi>' P'' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P''" and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', (p \<bullet> Q')) \<in> Rel"
      by(auto dest: rAct)
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p\<bullet>\<pi>') @ p \<bullet> ((p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr>) \<prec> (p \<bullet> P'')"
      by(rule weak_transitionClosed)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` `yvec \<sharp>* P` `(p \<bullet> yvec) \<sharp>* P` `distinct_perm p`
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>(p\<bullet>\<pi>') @ M\<lparr>N\<rparr> \<prec> (p \<bullet> P'')" by(simp add: eqvts)
    moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` S `distinct_perm p` 
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` S `distinct_perm p` have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using `\<alpha>=M\<lparr>N\<rparr>` by blast
  next
    case(c_output M xvec N)
    from `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q`  `bn \<alpha> \<sharp>* subject \<alpha>` `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `bn \<alpha> \<sharp>* yvec`
         `(p \<bullet> yvec) \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
    have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* M" and "yvec \<sharp>* xvec"
     and "(p \<bullet> yvec) \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* xvec" and "xvec \<sharp>* C" and "xvec \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* N" 
     and "distinct xvec" by simp+
    from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` S `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
    have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      by(rule_tac output_perm_subject) (assumption | simp add: fresh_star_def)+
    moreover note `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` 
    moreover note `xvec \<sharp>* Q`
    moreover from `xvec \<sharp>* M` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `yvec \<sharp>* xvec` `(p \<bullet> yvec) \<sharp>* xvec` S have "xvec \<sharp>* (p \<bullet> M)"
      by simp
    moreover note `xvec \<sharp>* C`
    moreover from `(p \<bullet> yvec) \<sharp>* M` have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover note `yvec \<sharp>* xvec`
    moreover from `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `yvec \<sharp>* Q` `yvec \<sharp>* xvec` `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `xvec \<sharp>* M` `distinct xvec`
    have "yvec \<sharp>* N" and "yvec \<sharp>* Q'" and "yvec \<sharp>* \<pi>"  by(force dest: output_fresh_chain_derivative trans_fresh_provenance)+
    moreover from `(p \<bullet> yvec) \<sharp>* \<Psi>'` have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    ultimately obtain P'' \<pi>' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
                               and PChain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(drule_tac rAct) auto
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> \<pi>') @ (p \<bullet> ((p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)) \<prec> (p \<bullet> P'')" 
      by(rule eqvts)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `yvec \<sharp>* P` `(p \<bullet> yvec) \<sharp>* P` `yvec \<sharp>* Q` `(p \<bullet> yvec) \<sharp>* Q` `yvec \<sharp>* xvec` `(p \<bullet> yvec) \<sharp>* xvec` 
      `yvec \<sharp>* N` `(p \<bullet> yvec) \<sharp>* N` `distinct_perm p` have "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> \<pi>') @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')"
      by(simp add: eqvts)
    moreover from PChain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with S `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>` `distinct_perm p` have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' `eqvt Rel` have "p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(simp add: eqvt_def) auto
    with `yvec \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* \<Psi>``yvec \<sharp>* Q'` `(p \<bullet> yvec) \<sharp>* Q'` S `distinct_perm p` 
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` by blast
  next
    case c_tau
    with `\<alpha> \<noteq> \<tau>` have "False" by simp
    thus ?thesis by simp
  qed
next
  case(c_tau Q')
  from `\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'` `yvec \<sharp>* Q` have "yvec \<sharp>* Q'"
    by(force dest: tau_fresh_chain_derivative)
  with `\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'` show ?case
    by(rule rTau)
qed

lemma weakSimIFresh[consumes 4, case_names c_act c_tau]:
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
  and     "\<And>\<alpha> \<pi> Q' \<Psi>'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<pi>; \<alpha> \<noteq> \<tau>;
                       bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; x \<sharp> \<alpha>; x \<sharp> Q'; x \<sharp> \<Psi>'; x \<sharp> \<pi>\<rbrakk> \<Longrightarrow>
                       \<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'; x \<sharp> Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms
by(rule_tac yvec="[x]" and C=C in weakSimIChainFresh) (auto simp add: trans_fresh_provenance)

lemma weakSimE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "\<And>\<Psi>' \<alpha> \<pi> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow> 
                            \<exists>P'' \<pi>'. \<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and   "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: weakSimulation_def)

lemma weakSimClosedAux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
proof(induct rule: weakSimI[of _ _ _ _ "(\<Psi>, P, p)"])
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  from `p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p\<bullet>\<pi>) @ (rev p \<bullet> (\<alpha> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>(rev p\<bullet>\<pi>) @ (rev p \<bullet> \<alpha>) \<prec> (rev p \<bullet> Q')"
    by(simp add: eqvts)
  moreover with `bn \<alpha> \<sharp>* (\<Psi>, P, p)` have "bn \<alpha>  \<sharp>* \<Psi>" and "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* p" by simp+
  moreover from `\<alpha> \<noteq> \<tau>` have "(rev p \<bullet> \<alpha>) \<noteq> \<tau>"
    by(cases rule: action_cases[where \<alpha>=\<alpha>]) auto
  ultimately obtain P'' \<pi>' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ (rev p \<bullet> \<alpha>) \<prec> P''"
                          and P''Chain: "\<Psi> \<otimes> (rev p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> (rev p \<bullet> \<Psi>'), P', rev p \<bullet> Q') \<in> Rel"
    using `\<alpha> \<noteq> \<tau>` PSimQ
    by(drule_tac \<Psi>'="rev p \<bullet> \<Psi>'" in weakSimE(1)) (auto simp add: fresh_chain_perm_simp bn_eqvt[symmetric])

  from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p\<bullet> \<pi>') @ (p \<bullet> (rev p \<bullet> \<alpha>)) \<prec> (p \<bullet> P'')"
    by(rule eqvts)
  hence "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p\<bullet>\<pi>') @ \<alpha> \<prec> (p \<bullet> P'')" by(simp add: eqvts fresh_chain_perm_simp)
  moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (rev p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
  hence "(p \<bullet> \<Psi>) \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> ((\<Psi> \<otimes> (rev p \<bullet> \<Psi>')), P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case by blast
next
  case(c_tau Q')
  from `p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>None @ \<tau> \<prec> Q'` 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>None @ (rev p \<bullet> (\<tau> \<prec> Q'))"
    by(auto dest: semantics.eqvt[where pi="rev p"])
  hence "\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> (rev p \<bullet> Q')" by(simp add: eqvts)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    by(blast dest: weakSimE)
  from PChain have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule tau_chain_eqvt)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> (\<Psi>,  P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case
    by blast
qed

lemma weakSimClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
  and   "P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
by(force dest: weakSimClosedAux simp add: perm_bottom)+

lemma weakSimReflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> P"
using assms
by(auto simp add: weakSimulation_def weak_transition_def dest: rtrancl_into_rtrancl) force+

lemma weakSimTauChain:
  fixes \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  
  obtains P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi>, P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from `\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'` `(\<Psi>, P, Q) \<in> Rel` A show ?thesis
  proof(induct arbitrary: P thesis rule: tau_chain_induct)
    case(tau_base Q P)
    moreover have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
    ultimately show ?case by blast
  next
    case(tau_step Q Q' Q'' P)
    from `(\<Psi>, P, Q) \<in> Rel` obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
      by(rule tau_step)
    from `(\<Psi>, P', Q') \<in> Rel` have "\<Psi> \<rhd> P' \<leadsto><Rel> Q'" by(rule Sim)
    then obtain P'' where P'Chain: "\<Psi> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "(\<Psi>, P'', Q'') \<in> Rel"
      using `\<Psi> \<rhd> Q' \<longmapsto>None @ \<tau> \<prec> Q''` by(blast dest: weakSimE)
    from PChain P'Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    thus ?case using `(\<Psi>, P'', Q'') \<in> Rel` by(rule tau_step)
  qed
qed

lemma weakSimE2:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
  and   Q   :: "('a, 'b, 'c) psi"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  and     QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<pi> @ \<alpha> \<prec> Q'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "\<alpha> \<noteq> \<tau>"

  obtains P'' P' \<pi>' where "\<Psi> : R \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" and "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
proof -
  assume A: "\<And>\<pi>' P'' P'. \<lbrakk>\<Psi> : R \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''; \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from QTrans obtain Q'' 
    where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" 
      and ReqQ'': "insert_assertion (extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q'') \<Psi>"
      and Q''Trans: "\<Psi> \<rhd> Q'' \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
    by(rule weak_transitionE)

  from QChain PRelQ Sim
  obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi>, P'', Q'') \<in> Rel" by(rule weakSimTauChain)

  from PChain `bn \<alpha> \<sharp>* P` have "bn \<alpha> \<sharp>* P''" by(rule tau_chain_fresh_chain)
  from P''RelQ'' have "\<Psi> \<rhd> P'' \<leadsto><Rel> Q''" by(rule Sim)
  with Q''Trans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P''` `\<alpha> \<noteq> \<tau>`
  obtain P''' P' \<pi>' where P''Trans: "\<Psi> : Q'' \<rhd> P'' \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'''" and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                   and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from P''Trans obtain P'''' where P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''"
                               and Q''eqP'''': "insert_assertion (extract_frame Q'') \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'''') \<Psi>"
                               and P''''Trans: "\<Psi> \<rhd> P'''' \<longmapsto>\<pi>' @ \<alpha> \<prec> P'''"
    by(rule weak_transitionE)
  from PChain P''Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" by simp
  moreover from ReqQ'' Q''eqP'''' have "insert_assertion (extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame P'''') \<Psi>"
    by(rule Frame_stat_imp_trans)
  ultimately have "\<Psi> : R \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'''" using P''''Trans by(rule weak_transitionI)
  with P'''Chain P'RelQ' A show ?thesis by blast
qed

lemma weakSimTransitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   T     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto><Rel'> R"
  and     Eqvt: "eqvt Rel''"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
using `eqvt Rel''`
proof(induct rule: weakSimI[of _ _ _ _ Q])
  case(c_act \<Psi>' \<alpha> \<pi> R')
  from QSimR `\<Psi> \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q` `\<alpha> \<noteq> \<tau>`
  obtain Q'' Q' \<pi>' where QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<pi>' @ \<alpha> \<prec> Q''" and Q''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                  and Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'"
    by(blast dest: weakSimE)
  with PRelQ Sim QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
  obtain P''' P'' \<pi>'' where PTrans: "\<Psi> : R \<rhd> P \<Longrightarrow>\<pi>'' @ \<alpha> \<prec> P'''" 
                and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi> \<otimes> \<Psi>', P'', Q'') \<in> Rel"
    by(drule_tac weakSimE2) auto
  note PTrans
  moreover from Q''Chain P''RelQ'' Sim obtain P' where P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  from P'''Chain P''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by simp
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
next
  case(c_tau R')
  from QSimR `\<Psi> \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'` obtain Q' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'" 
    by(blast dest: weakSimE)
  from QChain PRelQ Sim obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  note PChain
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
qed

lemma weakSimStatEq:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel'"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto><Rel'> Q"
using `eqvt Rel'`
proof(induct rule: weakSimI[of _ _ _ _ \<Psi>])
  case(c_act \<Psi>'' \<alpha> \<pi> Q')
  from `\<Psi>' \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `\<Psi> \<simeq> \<Psi>'`
  have "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" by(metis stat_eq_transition Assertion_stat_eq_sym)
  with PSimQ `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>`
  obtain P'' P' \<pi>' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" 
                  and P'RelQ': "(\<Psi> \<otimes> \<Psi>'', P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PTrans `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P''" by(rule weak_transition_stat_eq)
  moreover from P''Chain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(metis tau_chain_stat_eq Composition)
  moreover from P'RelQ' `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>' \<otimes> \<Psi>'', P', Q') \<in> Rel'"
    by(metis C1 Composition)
  ultimately show ?case
    by blast
next
  case(c_tau Q')
  from `\<Psi>' \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'` `\<Psi> \<simeq> \<Psi>'`
  have "\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'" by(metis stat_eq_transition Assertion_stat_eq_sym)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from PChain `\<Psi> \<simeq> \<Psi>'` have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tau_chain_stat_eq)
  moreover from `(\<Psi>, P', Q') \<in> Rel` `\<Psi> \<simeq> \<Psi>'` have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma weakSimMonotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto><A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto><B> Q"
using assms
by(simp (no_asm) add: weakSimulation_def) (blast dest: weakSimE)+

lemma strongSimWeakSim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     StatImp: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> insert_assertion(extract_frame S) \<Psi>' \<hookrightarrow>\<^sub>F insert_assertion(extract_frame R) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and     Ext:     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(induct rule: weakSimI2)
  case(c_act \<Psi>' \<alpha> \<pi> Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with `\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  obtain P' \<pi>' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from PRelQ have "insert_assertion(extract_frame Q) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame P) \<Psi>" by(rule StatImp)
  with PTrans have "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>' @ \<alpha> \<prec> P'" by(rule transition_weak_transition)
  moreover from P'RelQ' have "\<forall>\<Psi>'. \<exists>P''. \<Psi> \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<and> (\<Psi> \<otimes> \<Psi>', P'', Q') \<in> Rel"
    by(force intro: Ext)
  ultimately show ?case by blast
next
  case(c_tau Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with `\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'` obtain P' \<pi> where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(force dest: simE)
  from PTrans have "\<pi> = None" by(rule tau_no_provenance)
  with PTrans have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by auto
  thus ?case using P'RelQ' by blast
qed

lemma strongAppend:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Q     :: "('a, 'b, 'c) psi"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto>[Rel'] R"
  and     Eqvt'': "eqvt Rel''"
  and     RimpQ: "insert_assertion (extract_frame R) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     C1: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> Rel' \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel'"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: weakSimI[of _ _ _ _ Q])
    case(c_act \<Psi>' \<alpha> \<pi> R')
    from `\<Psi> \<rhd> Q \<leadsto>[Rel'] R` `\<Psi> \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> R'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* Q`
    obtain Q' \<pi>' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'" and "(\<Psi>, Q', R') \<in> Rel'"
      by(blast dest: simE)

    from `(\<Psi>, Q', R') \<in> Rel'` have Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'" by(rule C1)

    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` QTrans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `\<alpha> \<noteq> \<tau>` 
    obtain P'' P' \<pi>'' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<pi>'' @ \<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                    and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    from PTrans RimpQ have "\<Psi> : R \<rhd> P \<Longrightarrow>\<pi>'' @ \<alpha> \<prec> P''" by(rule weak_transition_frame_imp)
    moreover note P''Chain
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(c_tau R')
    from `\<Psi> \<rhd> Q \<leadsto>[Rel'] R` `\<Psi> \<rhd> R \<longmapsto>None @ \<tau> \<prec> R'`
    obtain Q' \<pi> where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<tau> \<prec> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'"
      by(force dest: simE)
    from QTrans have QTrans: "\<Psi> \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'"
      by(rule tau_no_provenance')
    from `\<Psi> \<rhd> P \<leadsto><Rel> Q` QTrans
    obtain P' where PTrans: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    note PTrans
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  qed
qed

lemma quietSim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "quiet P"
  and     "eqvt Rel"
  and     cQuiet: "\<And>P. quiet P \<Longrightarrow> (\<Psi>, \<zero>, P) \<in> Rel"

  shows "\<Psi> \<rhd> \<zero> \<leadsto><Rel> P"
using `eqvt Rel`
proof(induct rule: weakSimI[of _ _ _ _ "()"])
  case(c_act \<Psi>' \<alpha> \<pi> P')
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `\<alpha> \<noteq> \<tau>` have False using `quiet P` 
    by(cases rule: action_cases[where \<alpha>=\<alpha>]) (auto intro: quiet_output quiet_input)
  thus ?case by simp
next
  case(c_tau P')
  from `\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'` `quiet P` have "quiet P'"
    by(erule_tac quiet.cases) (force simp add: residual_inject)
  have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
  moreover from `quiet P'` have "(\<Psi>, \<zero>, P') \<in> Rel" by(rule cQuiet)
  ultimately show ?case by blast
qed


end

end


