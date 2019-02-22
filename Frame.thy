theory Frame
  imports Agent
begin

lemma perm_length[simp]:
  fixes p    :: "name prm"
  and   xvec :: "'a::pt_name list"

  shows "length(p \<bullet> xvec) = length xvec"
by(induct xvec) auto

nominal_datatype 'assertion frame =
    F_assert "'assertion::fs_name"
  | F_res "\<guillemotleft>name\<guillemotright> ('assertion frame)" ("\<lparr>\<nu>_\<rparr>_" [80, 80] 80)

fun frame_res_chain :: "name list \<Rightarrow> ('a::fs_name) frame \<Rightarrow> 'a frame"
where
  frame_res_chainbase: "frame_res_chain [] F = F"
| frame_res_chainstep: "frame_res_chain (x#xs) F = \<lparr>\<nu>x\<rparr>(frame_res_chain xs F)"

notation frame_res_chain ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80)
notation F_assert  ("\<langle>\<epsilon>, _\<rangle>" [80] 80)
abbreviation F_assert_judge ("\<langle>_, _\<rangle>" [80, 80] 80) where "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<equiv> frame_res_chain A\<^sub>F (F_assert \<Psi>\<^sub>F)"

lemma frame_res_chain_eqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>F) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> F)"
by(induct_tac xvec, auto)

lemma frame_res_chain_fresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "x \<sharp> \<lparr>\<nu>*xvec\<rparr>F = (x \<in> set xvec \<or> x \<sharp> F)"
by (induct xvec) (simp_all add: abs_fresh)

lemma frame_res_chain_fresh_set: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> F)"
by (simp add: fresh_star_def frame_res_chain_fresh)

lemma frame_chain_alpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  assumes xvec_freshF: "(p \<bullet> xvec) \<sharp>* F"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>F = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> F)"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frame_res_chain_fresh_set)
  moreover from xvec_freshF have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frame_res_chain_fresh_set) (simp add: fresh_star_def)
  ultimately have "\<lparr>\<nu>*xvec\<rparr>F = p \<bullet> (\<lparr>\<nu>*xvec\<rparr>F)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma frame_chain_alpha':
  fixes p    :: "name prm"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: "'a::fs_name"

  assumes "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P"
  and     S: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)"

  shows "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
using assms
by(subst frame_chain_alpha) (auto simp add: fresh_star_def)

lemma alpha_frame_res:
  fixes x :: name
  and   F :: "'a::fs_name frame"
  and   y :: name

  assumes "y \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F)"
proof(cases "x = y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with `y \<sharp> F` show ?thesis
    by(perm_simp add: frame.inject alpha calc_atm fresh_left)
qed

lemma frame_chain_append:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>F = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F)"
by(induct xvec) auto

lemma frame_chain_eq_length:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
	by(simp add: alpha frame.inject)
      with IH `length xvec' = n` have "length xvec' = length yvec'"
	by blast
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
	by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
	by(simp add: eqvts)
      with IH `length xvec' = n` have "length xvec' = length ([(x, y)] \<bullet> yvec')"
	by blast
      hence "length xvec' = length yvec'"
	by simp
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    qed
  qed
qed

lemma frame_eq_fresh:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<sharp> F"
  
  shows "y \<sharp> G"
using assms
by(auto simp add: frame.inject alpha fresh_left calc_atm)  

lemma frame_eq_supp:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<in> supp F"
  
  shows "y \<in> supp G"
using assms
apply(auto simp add: frame.inject alpha fresh_left calc_atm)
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts calc_atm)

lemma frame_chain_eq_supp_empty[dest]:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "supp \<Psi> = ({}::name set)"

  shows "\<Psi> = \<Psi>'"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case  using `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>`
      by(simp add: frame.inject) 
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; supp \<Psi> = ({}::name set); n = length xvec\<rbrakk> \<Longrightarrow> \<Psi> = \<Psi>'"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
	by(simp add: alpha frame.inject)
      with IH `length xvec' = n` `supp \<Psi> = {}` show ?case
	by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
	by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
	by(simp add: eqvts)
      with IH `length xvec' = n` `supp \<Psi> = {}` have "\<Psi> = [(x, y)] \<bullet> \<Psi>'"
	by(simp add: eqvts)
      moreover with `supp \<Psi> = {}` have "supp([(x, y)] \<bullet> \<Psi>') = ({}::name set)"
	by simp
      hence "x \<sharp> ([(x, y)] \<bullet> \<Psi>')" and "y \<sharp> ([(x, y)] \<bullet> \<Psi>')"
	by(simp add: fresh_def)+
      with `x \<noteq> y` have "x \<sharp> \<Psi>'" and "y \<sharp> \<Psi>'"
	by(simp add: fresh_left calc_atm)+
      ultimately show ?case by simp
    qed
  qed
qed

lemma frame_chain_eq:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "distinct_perm p" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; distinct_perm p; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
      by fact

    from EQ `x \<noteq> y` have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                     and x_fresh\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by(simp add: frame.inject alpha)+

    show ?case
    proof(case_tac "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
      assume "x \<sharp> \<langle>xvec', \<Psi>\<rangle>"
      with EQ have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
	by(rule frame_eq_fresh)
      with x_fresh\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
	by(simp)
      with `xvec' \<sharp>* yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p"  and "\<Psi>' = p \<bullet> \<Psi>"
	by blast
      from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      with `xvec = x#xvec'` `yvec=y#yvec'` `distinct_perm p` `\<Psi>' = p \<bullet> \<Psi>`
      show ?case by blast
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>))"
      hence x_supp\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
	by(simp add: fresh_def)
      with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
	by(rule frame_eq_supp)
      hence "y \<sharp> yvec'"
	by(induct yvec') (auto simp add: frame.supp abs_supp)      
      with `x \<sharp> yvec'` EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
	by(simp add: eqvts)
      with  `xvec' \<sharp>* yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
	by blast

      from x_supp\<Psi> have "x \<sharp> xvec'"
	by(induct xvec') (auto simp add: frame.supp abs_supp)      
      with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
	apply(induct p)
	by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
      from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
	by force
      moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinct_perm p`
      have "distinct_perm((x,y)#p)" by simp
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
	by(simp add: eqvts calc_atm fresh_chain_simps)
      moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
      have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
	by(simp add: pt_bij)
      hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
      ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
	by blast
    qed
  qed
  ultimately show ?thesis by blast
qed
(*
lemma frame_chain_eq'':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    show ?case
    proof(cases "x=y")
      case True
      from EQ `x = y` have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" by(simp add: alpha frame.inject)
      then obtain p where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "\<Psi>' = p \<bullet> \<Psi>" using `length xvec' = n` IH
	by blast
      from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set (y#yvec')" by auto
      moreover from `x = y` `\<Psi>' = p \<bullet> \<Psi>` have "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by auto
      ultimately show ?thesis using `xvec = x#xvec'` `yvec = y#yvec'` by blast
    next
      case False
thm 
      from EQ `x \<noteq> y` have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                       and x_fresh\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
	by(simp add: frame.inject alpha)+
    
      show ?thesis
      proof(cases "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
	case True
	from EQ `x \<sharp> \<langle>xvec', \<Psi>\<rangle>` have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
	  by(rule frame_eq_fresh)
	with x_fresh\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
	  by(simp)
	with `length xvec' = n` IH
	obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "\<Psi>' = p \<bullet> \<Psi>"
	  by blast
	from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
	with `xvec = x#xvec'` `yvec=y#yvec'` `\<Psi>' = p \<bullet> \<Psi>`
	show ?thesis by blast
      next
	case False
	from `\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>))` have x_supp\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
	  by(simp add: fresh_def)
	with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
	  by(rule frame_eq_supp)
	hence "y \<sharp> yvec'"
	  by(induct yvec') (auto simp add: frame.supp abs_supp)

	with `x \<sharp> yvec'` EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
	  by(simp add: eqvts)
	with  `xvec' \<sharp>* yvec'` `length xvec' = n` IH
	obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
	  by blast
	
	from x_supp\<Psi> have "x \<sharp> xvec'"
	  by(induct xvec') (auto simp add: frame.supp abs_supp)      
	with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
	  apply(induct p)
	  by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
	from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
	  by force
	moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinct_perm p`
	have "distinct_perm((x,y)#p)" by simp
	moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
	  by(simp add: eqvts calc_atm fresh_chain_simps)
	moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
	have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
	  by(simp add: pt_bij)
	hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
	ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
	  by blast
      qed
    qed
    ultimately show ?thesis by blast
qed
*)
lemma frame_chain_eq':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinct_perm p" and "yvec = p \<bullet> xvec" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinct_perm p; yvec = p \<bullet> xvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(F_assert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(F_assert \<Psi>')"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    from EQ `x \<noteq> y`  `x \<sharp> yvec'` `y \<sharp> yvec'` have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'` `length xvec' = n` IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "yvec' = p \<bullet> xvec'" and "[(x, y)] \<bullet> \<Psi>' = p \<bullet> \<Psi>"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from `x \<sharp> xvec'` `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: name_list_supp) (auto simp add: fresh_def) 

    with S `distinct_perm p` `x \<noteq> y` have "distinct_perm((x, y)#p)" by auto
    moreover from `yvec' = p \<bullet> xvec'` `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: fresh_chain_simps calc_atm)
    moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
      by(simp add: pt_bij)
    hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>"
      by simp
    ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma frame_eq[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>  :: "'a::fs_name"
  and   \<Psi>'  :: 'a

  shows "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
  and   "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^sub>F, \<Psi>\<rangle>  = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
proof -
  {
    assume "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle>"
    hence A: "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>[], \<Psi>'\<rangle>" by simp
    hence "length A\<^sub>F = length ([]::name list)"
      by(rule frame_chain_eq_length)
    with A have "A\<^sub>F = []" and "\<Psi> = \<Psi>'" by(auto simp add: frame.inject)
  }
  thus "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
  and  "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^sub>F, \<Psi>\<rangle>  = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
    by auto
qed

lemma distinct_frame:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: "'a::fs_name"
  and   C  :: "'b::fs_name"
  
  assumes "A\<^sub>F \<sharp>* C"

  obtains A\<^sub>F' where  "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C"
proof -
  assume "\<And>A\<^sub>F'. \<lbrakk>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>; distinct A\<^sub>F'; A\<^sub>F' \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover from assms have "\<exists>A\<^sub>F'. \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle> \<and> distinct A\<^sub>F' \<and> A\<^sub>F' \<sharp>* C"
  proof(induct A\<^sub>F)
    case Nil
    thus ?case by simp
  next
    case(Cons a A\<^sub>F)
    then obtain A\<^sub>F' where Eq: "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C" by force
    from `(a#A\<^sub>F) \<sharp>* C` have "a \<sharp> C" and "A\<^sub>F \<sharp>* C" by simp+
    show ?case
    proof(case_tac "a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>")
      assume "a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>"
      obtain b::name where "b \<sharp> A\<^sub>F'" and "b \<sharp> \<Psi>\<^sub>F" and "b \<sharp> C" by(generate_fresh "name", auto)
      have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(b#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>"
      proof -
	from Eq have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(a#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
	moreover from `b \<sharp> \<Psi>\<^sub>F` have "\<dots> = \<lparr>\<nu>b\<rparr>([(a, b)] \<bullet> \<lparr>\<nu>*A\<^sub>F'\<rparr>(F_assert \<Psi>\<^sub>F))"
	  by(force intro: alpha_frame_res simp add: frame_res_chain_fresh)
	ultimately show ?thesis using `a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>` `b \<sharp> \<Psi>\<^sub>F`
	  by(simp add: frame_res_chain_fresh)
      qed
      moreover from `distinct A\<^sub>F'` `b \<sharp> A\<^sub>F'` have "distinct(b#A\<^sub>F')" by simp
      moreover from `A\<^sub>F' \<sharp>* C` `b \<sharp> C` have "(b#A\<^sub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    next
      from Eq have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(a#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
      moreover assume "\<not>(a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>)"
      hence "a \<sharp> A\<^sub>F'" apply(simp add: fresh_def)
	by(induct A\<^sub>F') (auto simp add: supp_list_nil supp_list_cons supp_atm frame.supp abs_supp)
      with `distinct A\<^sub>F'` have "distinct(a#A\<^sub>F')" by simp
      moreover from `A\<^sub>F' \<sharp>* C` `a \<sharp> C` have "(a#A\<^sub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    qed
  qed
  ultimately show ?thesis using `A\<^sub>F \<sharp>* C`
    by blast
qed

lemma fresh_frame:
  fixes F  :: "('a::fs_name) frame"
  and   C  :: "'b ::fs_name"

  obtains A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F" and "A\<^sub>F \<sharp>* C"
proof -
  assume "\<And>A\<^sub>F \<Psi>\<^sub>F. \<lbrakk>F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; distinct A\<^sub>F; A\<^sub>F \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover have "\<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* C"
  proof(nominal_induct F avoiding: C rule: frame.strong_induct)
    case(F_assert \<Psi>\<^sub>F)
    have "F_assert \<Psi>\<^sub>F = \<langle>[], \<Psi>\<^sub>F\<rangle>" by simp
    moreover have "([]::name list) \<sharp>* C" by simp
    ultimately show ?case by force
  next
    case(F_res a F)
    from `\<And>C. \<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* C`
    obtain A\<^sub>F \<Psi>\<^sub>F  where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* C"
      by blast
    with `a \<sharp> C` have "\<lparr>\<nu>a\<rparr>F = \<lparr>\<nu>*(a#A\<^sub>F)\<rparr>(F_assert \<Psi>\<^sub>F)" and "(a#A\<^sub>F) \<sharp>* C"
      by simp+
    thus ?case by blast
  qed
  ultimately show ?thesis
    by(auto, rule_tac distinct_frame) auto
qed

locale assertion_aux = 
  fixes S_compose :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"   (infixr "\<otimes>" 80)
  and   S_imp     :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool" ("_ \<turnstile> _" [70, 70] 70)
  and   S_bottom  :: 'b                         ("\<bottom>" 90) 
  and   S_chan_eq  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"   ("_ \<leftrightarrow> _" [80, 80] 80)

  assumes stat_eqvt[eqvt]:   "\<And>p::name prm. p \<bullet> (\<Psi> \<turnstile> \<Phi>) = (p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<Phi>)"
  and     stat_eqvt'[eqvt]:  "\<And>p::name prm. p \<bullet> (\<Psi> \<otimes> \<Psi>') = (p \<bullet> \<Psi>) \<otimes> (p \<bullet> \<Psi>')" 
  and     stat_eqvt''[eqvt]: "\<And>p::name prm. p \<bullet> (M \<leftrightarrow> N) = (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
  and     perm_bottom[eqvt]: "\<And>p::name prm. (p \<bullet> S_bottom) = S_bottom"

begin

lemma stat_closed:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c
  and   p :: "name prm"
  
  assumes "\<Psi> \<turnstile> \<phi>"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<phi>)"
using assms stat_eqvt
by(simp add: perm_bool)

lemma comp_supp:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(supp(\<Psi> \<otimes> \<Psi>')::name set) \<subseteq> ((supp \<Psi>) \<union> (supp \<Psi>'))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> \<Psi>) \<otimes> [(x, y)] \<bullet> \<Psi>' \<noteq> \<Psi> \<otimes> \<Psi>'"
  let ?Q = "\<lambda>y \<Psi>. ([(x, y)] \<bullet> \<Psi>) \<noteq> \<Psi>"
  assume "finite {y. ?Q y \<Psi>'}"
  moreover assume "finite {y. ?Q y \<Psi>}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y \<Psi>})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y \<Psi>}) - {y. ?Q y \<Psi>'})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma chan_eq_supp:
  fixes M :: 'a
  and   N :: 'a

  shows "(supp(M \<leftrightarrow> N)::name set) \<subseteq> ((supp M) \<union> (supp N))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M) \<leftrightarrow> [(x, y)] \<bullet> N \<noteq> M \<leftrightarrow> N"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> M"
  assume "finite {y. ?Q y N}"
  moreover assume "finite {y. ?Q y M}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y M}) - {y. ?Q y N})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma fresh_comp[intro]:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> \<Psi>'"

  shows "x \<sharp> \<Psi> \<otimes> \<Psi>'"
using assms comp_supp
by(auto simp add: fresh_def)

lemma fresh_comp_chain[intro]:
  fixes xvec  :: "name list"
  and   Xs    :: "name set"
  and   \<Psi>     :: 'b
  and   \<Psi>'    :: 'b

  shows "\<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> xvec \<sharp>* (\<Psi> \<otimes> \<Psi>')"
  and   "\<lbrakk>Xs \<sharp>* \<Psi>; Xs \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> Xs \<sharp>* (\<Psi> \<otimes> \<Psi>')"
by(auto simp add: fresh_star_def)

lemma fresh_chan_eq[intro]:
  fixes x :: name
  and   M :: 'a
  and   N :: 'a

  assumes "x \<sharp> M"
  and     "x \<sharp> N"

  shows "x \<sharp> M \<leftrightarrow> N"
using assms chan_eq_supp
by(auto simp add: fresh_def)

lemma fresh_chan_eq_chain[intro]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   M    :: 'a
  and   N    :: 'a

  shows "\<lbrakk>xvec \<sharp>* M; xvec \<sharp>* N\<rbrakk> \<Longrightarrow> xvec \<sharp>* (M \<leftrightarrow> N)"
  and   "\<lbrakk>Xs \<sharp>* M; Xs \<sharp>* N\<rbrakk> \<Longrightarrow> Xs \<sharp>* (M \<leftrightarrow> N)"
by(auto simp add: fresh_star_def)

lemma supp_bottom[simp]:
  shows "((supp S_bottom)::name set) = {}"
by(auto simp add: supp_def perm_bottom)

lemma fresh_bottom[simp]:
  fixes x :: name
  
  shows "x \<sharp> \<bottom>"
by(simp add: fresh_def)

lemma fresh_botto_chain[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>)"
  and   "Xs   \<sharp>* (\<bottom>)"
by(auto simp add: fresh_star_def)

lemma chan_eq_closed:
  fixes \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   p :: "name prm"
 
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> N"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
proof -
  from `\<Psi> \<turnstile> M \<leftrightarrow> N` have "(p \<bullet> \<Psi>) \<turnstile> p \<bullet> (M \<leftrightarrow> N)"
    by(rule stat_closed)
  thus ?thesis by(simp add: eqvts)
qed

definition
  Assertion_stat_imp :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<hookrightarrow>" 70)
  where "(\<Psi> \<hookrightarrow> \<Psi>') \<equiv> (\<forall>\<Phi>. \<Psi> \<turnstile> \<Phi> \<longrightarrow> \<Psi>' \<turnstile> \<Phi>)"

definition
  Assertion_stat_eq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<simeq>" 70)
  where "(\<Psi> \<simeq> \<Psi>') \<equiv> \<Psi> \<hookrightarrow> \<Psi>' \<and> \<Psi>' \<hookrightarrow> \<Psi>"

lemma stat_imp_ent:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(simp add: Assertion_stat_imp_def)

lemma stat_eq_ent:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(auto simp add: Assertion_stat_eq_def intro: stat_imp_ent)

lemma Assertion_stat_imp_closed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>')"
proof(auto simp add: Assertion_stat_imp_def)
  fix \<phi>
  assume "(p \<bullet> \<Psi>) \<turnstile> \<phi>"
  hence "\<Psi> \<turnstile> rev p \<bullet> \<phi>" by(drule_tac p="rev p" in stat_closed) auto
  with `\<Psi> \<hookrightarrow> \<Psi>'` have "\<Psi>' \<turnstile> rev p \<bullet> \<phi>" by(simp add: Assertion_stat_imp_def)
  thus "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(drule_tac p=p in stat_closed) auto
qed

lemma Assertion_stat_eq_closed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')"
using assms
by(auto simp add: Assertion_stat_eq_def intro: Assertion_stat_imp_closed)

lemma Assertion_stat_imp_eqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<hookrightarrow> \<Psi>')) = ((p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>'))"
by(simp add: Assertion_stat_imp_def eqvts)

lemma Assertion_stat_eq_eqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<simeq> \<Psi>')) = ((p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>'))"
by(simp add: Assertion_stat_eq_def eqvts)

lemma Assertion_stat_imp_refl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi>"
by(simp add: Assertion_stat_imp_def)

lemma Assertion_stat_eq_refl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<simeq> \<Psi>"
by(simp add: Assertion_stat_eq_def)

lemma Assertion_stat_eq_sym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<simeq> \<Psi>"
using assms
by(auto simp add: Assertion_stat_eq_def)

lemma Assertion_stat_imp_trans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi>' \<hookrightarrow> \<Psi>''"

  shows "\<Psi> \<hookrightarrow> \<Psi>''"
using assms
by(simp add: Assertion_stat_imp_def)

lemma Assertion_stat_eq_trans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>' \<simeq> \<Psi>''"

  shows "\<Psi> \<simeq> \<Psi>''"
using assms
by(auto simp add: Assertion_stat_eq_def intro: Assertion_stat_imp_trans)

definition 
  Frame_imp :: "'b::fs_name frame \<Rightarrow> 'c \<Rightarrow> bool"   (infixl "\<turnstile>\<^sub>F" 70)
  where "(F \<turnstile>\<^sub>F \<Phi>) = (\<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* \<Phi> \<and> (\<Psi>\<^sub>F \<turnstile> \<Phi>))"

lemma frame_impI:
  fixes F  :: "'b frame"
  and   \<phi>  :: 'c
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
  and     "A\<^sub>F \<sharp>* \<phi>"
  and     "\<Psi>\<^sub>F \<turnstile> \<phi>"

  shows "F \<turnstile>\<^sub>F \<phi>"
using assms
by(force simp add: Frame_imp_def)

lemma frame_imp_alpha_ent:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>\<^sub>F  :: 'b
  and   A\<^sub>F' :: "name list"
  and   \<Psi>\<^sub>F' :: 'b
  and   \<phi>   :: 'c

  assumes "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>" 
  and     "A\<^sub>F \<sharp>* \<phi>"
  and     "A\<^sub>F' \<sharp>* \<phi>"
  and     "\<Psi>\<^sub>F' \<turnstile> \<phi>"

  shows "\<Psi>\<^sub>F \<turnstile> \<phi>"
proof -
  from `\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>`
  obtain n where "n = length A\<^sub>F" by blast
  moreover from `\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>`
  have "length A\<^sub>F = length A\<^sub>F'"
    by(rule frame_chain_eq_length)
  ultimately show ?thesis using assms
  proof(induct n arbitrary: A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F' rule: nat.induct)
    case(zero A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F')
    thus ?case by(auto simp add: frame.inject)
  next
    case(Suc n A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F')
    from `Suc n = length A\<^sub>F`
    obtain x xs where "A\<^sub>F = x#xs" and "n = length xs"
      by(case_tac A\<^sub>F) auto
    from `\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>` `A\<^sub>F = x # xs`
    obtain y ys where "\<langle>(x#xs), \<Psi>\<^sub>F\<rangle> = \<langle>(y#ys), \<Psi>\<^sub>F'\<rangle>" and "A\<^sub>F' = y#ys"
      by(case_tac A\<^sub>F') auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xs\<rparr>(F_assert \<Psi>\<^sub>F) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*ys\<rparr>(F_assert \<Psi>\<^sub>F')"
      by simp
    from `A\<^sub>F = x # xs` `A\<^sub>F' = y # ys` `length A\<^sub>F = length A\<^sub>F'` `A\<^sub>F \<sharp>* \<phi>` `A\<^sub>F' \<sharp>* \<phi>`
    have "length xs = length ys" and "xs \<sharp>* \<phi>" and "ys \<sharp>* \<phi>" and "x \<sharp> \<phi>" and "y \<sharp> \<phi>" 
      by auto
    
    have IH: "\<And>xs ys \<Psi>\<^sub>F'. \<lbrakk>n = length xs; length xs = length ys; \<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>ys, (\<Psi>\<^sub>F'::'b)\<rangle>; xs \<sharp>* \<phi>; ys \<sharp>* \<phi>; \<Psi>\<^sub>F' \<turnstile> \<phi>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>F \<turnstile> \<phi>"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>ys, \<Psi>\<^sub>F'\<rangle>" by(simp add: alpha frame.inject)
      with IH `n = length xs` `length xs = length ys` `xs \<sharp>* \<phi>`  `ys \<sharp>* \<phi>` `\<Psi>\<^sub>F' \<turnstile> \<phi>`
      show ?case by blast
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xs, \<Psi>\<^sub>F\<rangle> = [(x, y)] \<bullet> \<langle>ys, \<Psi>\<^sub>F'\<rangle>" by(simp add: alpha frame.inject)
      hence "\<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>([(x, y)] \<bullet> ys), ([(x, y)] \<bullet> \<Psi>\<^sub>F')\<rangle>" by(simp add: eqvts)
      moreover from `length xs = length ys` have "length xs = length([(x, y)] \<bullet> ys)"
	by auto
      moreover from `ys \<sharp>* \<phi>` have "([(x, y)] \<bullet> ys) \<sharp>* ([(x, y)] \<bullet> \<phi>)"
	by(simp add: fresh_star_bij)
      with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> ys) \<sharp>* \<phi>"
	by simp
      moreover with `\<Psi>\<^sub>F' \<turnstile> \<phi>` have "([(x, y)] \<bullet> \<Psi>\<^sub>F') \<turnstile> ([(x, y)] \<bullet> \<phi>)"
	by(simp add: stat_closed)
      with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> \<Psi>\<^sub>F') \<turnstile> \<phi>"
	by simp
      ultimately show ?case using IH `n = length xs` `xs \<sharp>* \<phi>`
	by blast
    qed
  qed
qed

lemma frame_imp_e_aux:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "F \<turnstile>\<^sub>F \<Phi>"
  and      "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
  and      "A\<^sub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^sub>F \<turnstile> \<Phi>"
using assms
by(auto simp add: Frame_imp_def dest: frame_imp_alpha_ent)

lemma frame_impE:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<Phi>"
  and      "A\<^sub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^sub>F \<turnstile> \<Phi>"
using assms
by(auto elim: frame_imp_e_aux)

lemma frame_imp_closed:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  assumes "F \<turnstile>\<^sub>F \<Phi>"

  shows "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
using assms
by(force simp add: Frame_imp_def eqvts pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst]
         intro: stat_closed)

lemma frame_imp_eqvt[eqvt]:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  shows "(p \<bullet> (F \<turnstile>\<^sub>F \<Phi>)) = (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
proof -
  have "F \<turnstile>\<^sub>F \<Phi> \<Longrightarrow> (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
    by(rule frame_imp_closed)
  moreover have "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>) \<Longrightarrow> F \<turnstile>\<^sub>F \<Phi>"
    by(drule_tac p = "rev p" in frame_imp_closed) simp
  ultimately show ?thesis
    by(auto simp add: perm_bool)
qed

lemma frame_imp_empty[simp]:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<turnstile>\<^sub>F \<phi> = \<Psi> \<turnstile> \<phi>" 
by(auto simp add: Frame_imp_def)

definition
  Frame_stat_imp :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<hookrightarrow>\<^sub>F" 70)
  where "(F \<hookrightarrow>\<^sub>F G) \<equiv> (\<forall>\<phi>. F \<turnstile>\<^sub>F \<phi> \<longrightarrow> G \<turnstile>\<^sub>F \<phi>)"

definition
  Frame_stat_eq :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<simeq>\<^sub>F" 70)
  where "(F \<simeq>\<^sub>F G) \<equiv> F \<hookrightarrow>\<^sub>F G \<and> G \<hookrightarrow>\<^sub>F F"

lemma Frame_stat_imp_closed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "(p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G)"
proof(auto simp add: Frame_stat_imp_def)
  fix \<phi>
  assume "(p \<bullet> F) \<turnstile>\<^sub>F \<phi>"
  hence "F \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(drule_tac p="rev p" in frame_imp_closed) auto
  with `F \<hookrightarrow>\<^sub>F G` have "G \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(simp add: Frame_stat_imp_def)
  thus "(p \<bullet> G) \<turnstile>\<^sub>F \<phi>" by(drule_tac p=p in frame_imp_closed) auto
qed

lemma Frame_stat_eq_closed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<simeq>\<^sub>F G"

  shows "(p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G)"
using assms
by(auto simp add: Frame_stat_eq_def intro: Frame_stat_imp_closed)

lemma Frame_stat_imp_eqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<hookrightarrow>\<^sub>F G)) = ((p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G))"
by(simp add: Frame_stat_imp_def eqvts)

lemma Frame_stat_eq_eqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<simeq>\<^sub>F G)) = ((p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G))"
by(simp add: Frame_stat_eq_def eqvts)

lemma Frame_stat_imp_refl[simp]:
  fixes F :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F"
by(simp add: Frame_stat_imp_def)

lemma Frame_stat_eq_refl[simp]:
  fixes F :: "'b frame"

  shows "F \<simeq>\<^sub>F F"
by(simp add: Frame_stat_eq_def)

lemma Frame_stat_eq_sym:
  fixes F  :: "'b frame"
  and   G  :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"

  shows "G \<simeq>\<^sub>F F"
using assms
by(auto simp add: Frame_stat_eq_def)

lemma Frame_stat_imp_trans:
  fixes F :: "'b frame"
  and   G :: "'b frame" 
  and   H :: "'b frame"

  assumes "F \<hookrightarrow>\<^sub>F G"
  and     "G \<hookrightarrow>\<^sub>F H"

  shows "F \<hookrightarrow>\<^sub>F H"
using assms
by(simp add: Frame_stat_imp_def)

lemma Frame_stat_eq_trans:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   H :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"
  and     "G \<simeq>\<^sub>F H"

  shows "F \<simeq>\<^sub>F H"
using assms
by(auto simp add: Frame_stat_eq_def intro: Frame_stat_imp_trans)

lemma fs_compose[simp]: "finite((supp S_compose)::name set)"
by(simp add: supp_def perm_fun_def eqvts)

nominal_primrec 
   insert_assertion :: "'b frame \<Rightarrow> 'b \<Rightarrow> 'b frame"
where
  "insert_assertion (F_assert \<Psi>) \<Psi>' = F_assert (\<Psi>' \<otimes> \<Psi>)"
| "x \<sharp> \<Psi>' \<Longrightarrow> insert_assertion (\<lparr>\<nu>x\<rparr>F) \<Psi>' = \<lparr>\<nu>x\<rparr>(insert_assertion F \<Psi>')"
apply(finite_guess add: fs_compose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(rule supports_fresh[of "supp \<Psi>'"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

lemma insert_assertion_eqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   \<Psi> :: 'b

  shows "p \<bullet> (insert_assertion F \<Psi>) = insert_assertion (p \<bullet> F) (p \<bullet> \<Psi>)"
by(nominal_induct F avoiding: p \<Psi> rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)


nominal_primrec 
   merge_frame :: "'b frame \<Rightarrow> 'b frame \<Rightarrow> 'b frame"
where
  "merge_frame (F_assert \<Psi>) G = insert_assertion G \<Psi>"
| "x \<sharp> G \<Longrightarrow> merge_frame (\<lparr>\<nu>x\<rparr>F) G = \<lparr>\<nu>x\<rparr>(merge_frame F G)"
apply(finite_guess add: fs_compose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(simp add: fs_name1)
apply(rule supports_fresh[of "supp G"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

notation merge_frame (infixr "\<otimes>\<^sub>F" 80)

abbreviation
  frame_bottom_judge ("\<bottom>\<^sub>F") where "\<bottom>\<^sub>F \<equiv> (F_assert S_bottom)"

lemma merge_frame_eqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   G :: "'b frame"

  shows "p \<bullet> (merge_frame F G) = merge_frame (p \<bullet> F) (p \<bullet> G)"
by(nominal_induct F avoiding: p G rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)

nominal_primrec
    extract_frame   :: "('a, 'b, 'c) psi \<Rightarrow> 'b frame"
and extract_frame'  :: "('a, 'b, 'c) input \<Rightarrow> 'b frame"
and extract_frame'' :: "('a, 'b, 'c) psi_case \<Rightarrow> 'b frame"

where
  "extract_frame (\<zero>) =  \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extract_frame (M\<lparr>I) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extract_frame (M\<langle>N\<rangle>.P) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extract_frame (Case C) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extract_frame (P \<parallel> Q) = (extract_frame P) \<otimes>\<^sub>F (extract_frame Q)"
| "extract_frame ((\<lbrace>\<Psi>\<rbrace>::('a, 'b, 'c) psi)) = \<langle>\<epsilon>, \<Psi>\<rangle>" 

| "extract_frame (\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>x\<rparr>(extract_frame P)"
| "extract_frame (!P) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extract_frame' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extract_frame' (Bind x I) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extract_frame'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extract_frame'' (\<box>\<Phi> \<Rightarrow> P C) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
apply(finite_guess add: fs_compose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: fresh_bottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: fresh_bottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: fresh_bottom)+
done

lemmas extract_frame_simps = extract_frame_extract_frame'_extract_frame''.simps

lemma extract_frame_eqvt[eqvt]:
  fixes p :: "name prm"
  and   P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psi_case"

  shows "p \<bullet> (extract_frame P) = extract_frame (p \<bullet> P)"
  and   "p \<bullet> (extract_frame' I) = extract_frame' (p \<bullet> I)"
  and   "p \<bullet> (extract_frame'' C) = extract_frame'' (p \<bullet> C)"
by(nominal_induct P and I and C avoiding: p rule: psi_input_psi_case.strong_inducts)
   (auto simp add: at_prm_fresh[OF at_name_inst] eqvts perm_bottom
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst])

lemma insert_assertion_fresh[intro]:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b
  and   x :: name

  assumes "x \<sharp> F"
  and     "x \<sharp> \<Psi>"

  shows "x \<sharp> (insert_assertion F \<Psi>)"
using assms
by(nominal_induct F avoiding: x \<Psi> rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma insert_assertion_fresh_chain[intro]:
  fixes F    :: "'b frame"
  and   \<Psi>    :: 'b
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> xvec \<sharp>* (insert_assertion F \<Psi>)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> Xs \<sharp>* (insert_assertion F \<Psi>)"
by(auto simp add: fresh_star_def)

lemma merge_frame_fresh[intro]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name

  shows "\<lbrakk>x \<sharp> F; x \<sharp> G\<rbrakk> \<Longrightarrow> x \<sharp> (merge_frame F G)"
by(nominal_induct F avoiding: x G rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma merge_frame_fresh_chain[intro]:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* G\<rbrakk> \<Longrightarrow> xvec \<sharp>* (merge_frame F G)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* G\<rbrakk> \<Longrightarrow> Xs \<sharp>* (merge_frame F G)"
by(auto simp add: fresh_star_def)

lemma extract_frame_fresh:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psi_case"
  and   x :: name

  shows "x \<sharp> P \<Longrightarrow> x \<sharp> extract_frame P"
  and   "x \<sharp> I \<Longrightarrow> x \<sharp> extract_frame' I"
  and   "x \<sharp> C \<Longrightarrow> x \<sharp> extract_frame'' C"
by(nominal_induct P and I and C avoiding: x rule: psi_input_psi_case.strong_inducts)
  (auto simp add: abs_fresh)

lemma extract_frame_fresh_chain:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* P \<Longrightarrow> xvec \<sharp>* extract_frame P"
  and   "xvec \<sharp>* I \<Longrightarrow> xvec \<sharp>* extract_frame' I"
  and   "xvec \<sharp>* C \<Longrightarrow> xvec \<sharp>* extract_frame'' C"
  and   "Xs \<sharp>* P \<Longrightarrow> Xs \<sharp>* extract_frame P"
  and   "Xs \<sharp>* I \<Longrightarrow> Xs \<sharp>* extract_frame' I"
  and   "Xs \<sharp>* C \<Longrightarrow> Xs \<sharp>* extract_frame'' C"
by(auto simp add: fresh_star_def intro: extract_frame_fresh)


lemma guarded_frame_supp[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psi_case"
  and   x :: name 

  shows "guarded P \<Longrightarrow> x \<sharp> (extract_frame P)"
  and   "guarded' I \<Longrightarrow> x \<sharp> (extract_frame' I)"
  and   "guarded'' C \<Longrightarrow> x \<sharp> (extract_frame'' C)"
by(nominal_induct P and I and C arbitrary: x rule: psi_input_psi_case.strong_inducts)
  (auto simp add: frame_res_chain_fresh abs_fresh)

lemma frame_res_chain_fresh': 
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "(xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F)) = (\<forall>x \<in> set xvec. x \<in> set yvec \<or> x \<sharp> F)"
by(simp add: frame_res_chain_fresh fresh_star_def)

lemma frame_chain_fresh[simp]:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (F_assert \<Psi>) = xvec \<sharp>* \<Psi>"
  and   "Xs \<sharp>* (F_assert \<Psi>) = Xs \<sharp>* \<Psi>"
by(simp add: fresh_star_def)+

lemma frame_res_chain_fresh''[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "xvec \<sharp>* yvec"

  shows "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F) = xvec \<sharp>* F"

using assms
by(simp_all add: frame_res_chain_fresh')
  (auto simp add: fresh_star_def fresh_def name_list_supp)

lemma frame_res_chain_fresh'''[simp]:
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "x \<sharp> xvec"

  shows "x \<sharp> (\<lparr>\<nu>*xvec\<rparr>F) = x \<sharp> F"
using assms
by(induct xvec) (auto simp add: abs_fresh)

lemma F_fresh_bottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>\<^sub>F)"
  and   "Xs \<sharp>* (\<bottom>\<^sub>F)"
by(auto simp add: fresh_star_def)

lemma S_fresh_bottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (S_bottom)"
  and   "Xs \<sharp>* (S_bottom)"
by(auto simp add: fresh_star_def)
(*
lemma fresh_chain_comp[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   \<Psi>    :: 'b
  and   \<Psi>'   :: 'b

  shows "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((xvec \<sharp>* \<Psi>) \<and> xvec \<sharp>* \<Psi>')"
  and   "Xs \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((Xs \<sharp>* \<Psi>) \<and> Xs \<sharp>* \<Psi>')"
by(auto simp add: fresh_star_def)
*)
lemma fresh_frame_dest[dest]:
  fixes A\<^sub>F    :: "name list"
  and   \<Psi>\<^sub>F   :: 'b
  and   xvec  :: "name list"

  assumes "xvec \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"

  shows "xvec \<sharp>* A\<^sub>F \<Longrightarrow> xvec \<sharp>* \<Psi>\<^sub>F"
  and   "A\<^sub>F \<sharp>* xvec \<Longrightarrow> xvec \<sharp>* \<Psi>\<^sub>F"
proof -
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "xvec \<sharp>* A\<^sub>F"
  ultimately show "xvec \<sharp>* \<Psi>\<^sub>F"
    by(simp add: frame_res_chain_fresh_set) (force simp add: fresh_def name_list_supp fresh_star_def)
next
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "A\<^sub>F \<sharp>* xvec"
  ultimately show "xvec \<sharp>* \<Psi>\<^sub>F"
    by(simp add: frame_res_chain_fresh_set) (force simp add: fresh_def name_list_supp fresh_star_def)
qed

lemma insert_assertion_simps[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   \<Psi>  :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>"

  shows "insert_assertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<Psi> = \<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms
by(induct A\<^sub>F arbitrary: F) auto

lemma merge_frame_simps[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   \<Psi>  :: 'b

  assumes "A\<^sub>F \<sharp>* \<Psi>"

  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle> = \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<rangle>"
using assms
by(induct A\<^sub>F arbitrary: F) auto

lemma merge_frames[simp]:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   A\<^sub>G  :: "name list"
  and   \<Psi>\<^sub>G :: 'b

  assumes "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"

  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>) = (\<langle>(A\<^sub>F@A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
by(induct A\<^sub>F) auto

lemma frame_imp_res_fresh_left:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F F"
proof(auto simp add: Frame_stat_imp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule fresh_frame)
  from `A\<^sub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alpha_frame_res)
  with `x \<sharp> F` `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>F \<turnstile>\<^sub>F \<phi>" by simp
  with Feq have "\<langle>(y#A\<^sub>F), \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by simp
  with Feq `A\<^sub>F \<sharp>* \<phi>` `y \<sharp> \<phi>` show "F \<turnstile>\<^sub>F \<phi>"
    by(force intro: frame_impI dest: frame_impE simp del: frame_res_chain.simps)
qed

lemma frame_imp_res_fresh_right:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>F"
proof(auto simp add: Frame_stat_imp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule fresh_frame)
  from `A\<^sub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "F \<turnstile>\<^sub>F \<phi>"
  with Feq `A\<^sub>F \<sharp>* \<phi>` `y \<sharp> \<phi>` have "\<langle>(y#A\<^sub>F), \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frame_impI dest: frame_impE simp del: frame_res_chain.simps)
  moreover with `y \<sharp> F` `x \<sharp> F` Feq show "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
    by(subst alpha_frame_res) auto
qed

lemma frame_res_fresh:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F F"
using assms
by(auto simp add: Frame_stat_eq_def intro: frame_imp_res_fresh_left frame_imp_res_fresh_right)

lemma frame_imp_res_pres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>G"
proof(auto simp add: Frame_stat_imp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule fresh_frame)
  from `A\<^sub>F \<sharp>* (x, \<phi>)` have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> A\<^sub>F" and "y \<sharp> F" and "y \<sharp> G"
             and "x \<noteq> y" and "y \<sharp> \<phi>"
    by(generate_fresh "name", auto)
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with `y \<sharp> F` have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alpha_frame_res)
  with Feq `x \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F` have "\<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with `y \<sharp> \<phi>` `A\<^sub>F \<sharp>* \<phi>` have "\<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frame_impI dest: frame_impE simp del: frame_res_chain.simps)
  hence "([(x, y)] \<bullet> \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>) \<turnstile>\<^sub>F ([(x, y)] \<bullet> \<phi>)"
    by(rule frame_imp_closed)
  with `x \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F` Feq have "F \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>"
    by(simp add: eqvts)
  with `F \<hookrightarrow>\<^sub>F G` have "G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>" by(simp add: Frame_stat_imp_def)
  
  obtain A\<^sub>G \<Psi>\<^sub>G where Geq: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* (x, y, \<phi>)"
    by(rule fresh_frame)
  from `A\<^sub>G \<sharp>* (x, y, \<phi>)` have "x \<sharp> A\<^sub>G" and "y \<sharp> A\<^sub>G" and "A\<^sub>G \<sharp>* \<phi>" by simp+
  from `G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>` have "([(x, y)] \<bullet> G) \<turnstile>\<^sub>F [(x, y)] \<bullet> [(x, y)] \<bullet> \<phi>"
    by(rule frame_imp_closed)
  with Geq `x \<sharp> A\<^sub>G` `y \<sharp> A\<^sub>G` have "\<langle>A\<^sub>G, [(x, y)] \<bullet> \<Psi>\<^sub>G\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with `y \<sharp> \<phi>` `A\<^sub>G \<sharp>* \<phi>` have "\<langle>(y#A\<^sub>G), [(x, y)] \<bullet> \<Psi>\<^sub>G\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frame_impI dest: frame_impE simp del: frame_res_chain.simps)
  with `y \<sharp> G` `x \<sharp> A\<^sub>G` `y \<sharp> A\<^sub>G` Geq show "\<lparr>\<nu>x\<rparr>G \<turnstile>\<^sub>F \<phi>"
    by(subst alpha_frame_res) (assumption | force simp add: eqvts)+
qed

lemma frame_res_pres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>G"
using assms
by(auto simp add: Frame_stat_eq_def intro: frame_imp_res_pres)

lemma frame_imp_res_comm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
proof(case_tac "x = y")
  assume "x = y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  show ?thesis
  proof(auto simp add: Frame_stat_imp_def)
    fix \<phi>::'c
    obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, y, \<phi>)"
      by(rule fresh_frame)
    then have "x \<sharp> A\<^sub>F" and "y \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+

    obtain x'::name where "x' \<noteq> x" and "x' \<noteq> y" and "x' \<sharp> F" and "x' \<sharp> \<phi>" and "x' \<sharp> A\<^sub>F"
      by(generate_fresh "name") auto
    obtain y'::name where "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'" and "y' \<sharp> F" and "y' \<sharp> \<phi>" and "y' \<sharp> A\<^sub>F"
      by(generate_fresh "name") auto
  
    from `y' \<sharp> F` have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F))"
      by(simp add: alpha_frame_res)
    moreover from `x' \<sharp> F` `x' \<noteq> y` `y' \<noteq> x'` have "\<dots> = \<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> (\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F)))"
      by(rule_tac alpha_frame_res) (simp add: abs_fresh fresh_left)
    moreover with  `y' \<noteq> x'` `y' \<noteq> x` have "\<dots> = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    ultimately have A: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)= \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*A\<^sub>F\<rparr>(F_assert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F))))"
      using  Feq `x \<sharp> A\<^sub>F` `x' \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F` `y' \<sharp> A\<^sub>F`
      by(simp add: eqvts)

    from `x' \<sharp> F` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F))"
      by(simp add: alpha_frame_res)
    moreover from `y' \<sharp> F` `y' \<noteq> x` `y' \<noteq> x'` have "\<dots> = \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> (\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F)))"
      by(rule_tac alpha_frame_res) (simp add: abs_fresh fresh_left)
    moreover with  `y' \<noteq> x'` `x' \<noteq> y` have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y')] \<bullet> [(x, x')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    moreover with `x' \<noteq> x` `x' \<noteq> y` `y' \<noteq> x` `y' \<noteq> y` `y' \<noteq> x'` `x \<noteq> y`
      have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      apply(simp add: eqvts)
      by(subst perm_compose) (simp add: calc_atm)
    ultimately have B: "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)= \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*A\<^sub>F\<rparr>(F_assert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F))))"
      using  Feq `x \<sharp> A\<^sub>F` `x' \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F` `y' \<sharp> A\<^sub>F`
      by(simp add: eqvts)

    from `x' \<sharp> \<phi>` `y' \<sharp> \<phi>` `A\<^sub>F \<sharp>* \<phi>`
    have "\<langle>(x'#y'#A\<^sub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi> = \<langle>(y'#x'#A\<^sub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
      by(force dest: frame_impE intro: frame_impI simp del: frame_res_chain.simps)
    with A B have "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi> = (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
      by simp
    moreover assume "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
    ultimately show "(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>" by simp
  qed
qed

lemma frame_res_comm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(auto simp add: Frame_stat_eq_def intro: frame_imp_res_comm)

lemma frame_imp_res_comm_left':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frame_imp_res_comm Frame_stat_imp_trans frame_imp_res_pres)

lemma frame_imp_res_comm_right':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frame_imp_res_comm Frame_stat_imp_trans frame_imp_res_pres)

lemma frame_res_comm':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frame_res_comm Frame_stat_eq_trans frame_res_pres)

lemma frame_imp_chain_comm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frame_imp_res_comm_left' Frame_stat_imp_trans frame_imp_res_pres)

lemma frame_res_chain_comm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frame_res_comm' Frame_stat_eq_trans frame_res_pres)

lemma frame_imp_nil_stat_eq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<hookrightarrow> \<Psi>')"
by(simp add: Frame_stat_imp_def Assertion_stat_imp_def Frame_imp_def)


lemma frame_nil_stat_eq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<simeq> \<Psi>')"
by(simp add: Frame_stat_eq_def Assertion_stat_eq_def Frame_imp_def)

lemma extract_frame_chain_stat_imp:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extract_frame(\<lparr>\<nu>*xvec\<rparr>P) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extract_frame P)"
by(induct xvec) (auto intro: frame_imp_res_pres)

lemma extract_frame_chain_stat_eq:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extract_frame(\<lparr>\<nu>*xvec\<rparr>P) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extract_frame P)"
by(induct xvec) (auto intro: frame_res_pres)

lemma insert_assertion_extract_frame_fresh_imp:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insert_assertion(extract_frame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insert_assertion (extract_frame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frame_imp_res_pres)

lemma insert_assertion_extract_frame_fresh:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insert_assertion(extract_frame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insert_assertion (extract_frame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frame_res_pres)

lemma frame_imp_res_chain_pres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frame_imp_res_pres)

lemma frame_res_chain_pres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frame_res_pres)

lemma insert_assertionE:
  fixes F  :: "('b::fs_name) frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"

  assumes "insert_assertion F \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>"
  and     "A\<^sub>F \<sharp>* F"
  and     "A\<^sub>F \<sharp>* \<Psi>"
  and     "distinct A\<^sub>F"

  obtains \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "\<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F"
proof -
  assume A: "\<And>\<Psi>\<^sub>F. \<lbrakk>F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>\<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F"
  proof(nominal_induct F avoiding: \<Psi> A\<^sub>F \<Psi>' rule: frame.strong_induct)
    case(F_assert \<Psi> A\<^sub>F \<Psi>')
    thus ?case by auto
  next
    case(F_res x F \<Psi> A\<^sub>F \<Psi>')
    from `insert_assertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>` `x \<sharp> \<Psi>`
    moreover obtain y A\<^sub>F' where "A\<^sub>F = y#A\<^sub>F'" by(induct A\<^sub>F) auto
    with `insert_assertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>` `x \<sharp> \<Psi>` `x \<sharp> A\<^sub>F`
    have A: "insert_assertion F \<Psi> = \<langle>([(x, y)] \<bullet> A\<^sub>F'), [(x, y)] \<bullet> \<Psi>'\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    from `A\<^sub>F = y#A\<^sub>F'` `A\<^sub>F \<sharp>* \<Psi>` have "y \<sharp> \<Psi>" and "A\<^sub>F' \<sharp>* \<Psi>" by simp+
    from `distinct A\<^sub>F` `A\<^sub>F = y#A\<^sub>F'` have "y \<sharp> A\<^sub>F'" and "distinct A\<^sub>F'" by auto
    from `A\<^sub>F \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^sub>F` `A\<^sub>F = y#A\<^sub>F'` have "y \<sharp> F" and "A\<^sub>F' \<sharp>* F" and "x \<sharp> A\<^sub>F'"
      apply -
      apply(auto simp add: abs_fresh)
      apply(subst fresh_star_def)
      apply(subst (asm) fresh_star_def)
      apply(simp add: abs_fresh)
      by(auto simp add: fresh_def name_list_supp)
    with `x \<sharp> A\<^sub>F'` `y \<sharp> A\<^sub>F'` have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* F" by simp
    from `A\<^sub>F' \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* \<Psi>" by simp
    with `\<And>\<Psi> A\<^sub>F \<Psi>'. \<lbrakk>insert_assertion F \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>; A\<^sub>F \<sharp>* F; A\<^sub>F \<sharp>* \<Psi>; distinct A\<^sub>F\<rbrakk> \<Longrightarrow> \<exists>\<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F` A 
         `([(x, y)] \<bullet> A\<^sub>F') \<sharp>* F` `distinct A\<^sub>F'` `x \<sharp> A\<^sub>F'` `y \<sharp> A\<^sub>F'`
    obtain \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and \<Psi>eq: "([(x, y)] \<bullet> \<Psi>') = \<Psi> \<otimes> \<Psi>\<^sub>F"
      by force
    
    from Feq have "\<lparr>\<nu>x\<rparr>F =  \<langle>(x#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
    hence "([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>F) = [(x, y)] \<bullet> \<langle>(x#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by simp
    hence "\<lparr>\<nu>x\<rparr>F = \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" using `y \<sharp> F` `A\<^sub>F = y#A\<^sub>F'` `x \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F'`
      by(simp add: eqvts calc_atm alpha_frame_res)

    moreover from \<Psi>eq have "[(x, y)] \<bullet> ([(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>F)"
      by simp
    with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "\<Psi>' = \<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by(simp add: eqvts)
    ultimately show ?case
      by blast
  qed
  with A show ?thesis
    by blast
qed

lemma merge_frameE:
  fixes F   :: "'b frame"
  and   G   :: "'b frame"
  and   A\<^sub>F\<^sub>G :: "name list"
  and   \<Psi>\<^sub>F\<^sub>G :: 'b

  assumes "merge_frame F G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>"
  and     "distinct A\<^sub>F\<^sub>G"
  and     "A\<^sub>F\<^sub>G \<sharp>* F"
  and     "A\<^sub>F\<^sub>G \<sharp>* G"

  obtains A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G where "A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G" and "\<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" and "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
proof -
  assume A: "\<And>A\<^sub>F A\<^sub>G \<Psi>\<^sub>F \<Psi>\<^sub>G. \<lbrakk>A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G; \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G; F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>; A\<^sub>F \<sharp>* \<Psi>\<^sub>G; A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G. A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G \<and> \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G \<and> F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle> \<and> A\<^sub>F \<sharp>* \<Psi>\<^sub>G \<and> A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  proof(nominal_induct F avoiding: G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G rule: frame.strong_induct)
    case(F_assert \<Psi> G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G)
    thus ?case
      apply auto
      apply(rule_tac x="[]" in exI) 
      by(drule_tac insert_assertionE) auto
  next
    case(F_res x F G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G)
    from `merge_frame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>` `x \<sharp> G`
    obtain y A\<^sub>F\<^sub>G' where "A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'" by(induct A\<^sub>F\<^sub>G) auto
    with `A\<^sub>F\<^sub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^sub>F\<^sub>G` have "A\<^sub>F\<^sub>G' \<sharp>* F" and "x \<sharp> A\<^sub>F\<^sub>G'"
      by(auto simp add: supp_list_cons fresh_star_def fresh_def name_list_supp abs_supp frame.supp)
    from `A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'` `A\<^sub>F\<^sub>G \<sharp>* G` have "y \<sharp> G" and "A\<^sub>F\<^sub>G' \<sharp>* G" by simp+
    from `A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'` `A\<^sub>F\<^sub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)` `x \<sharp> A\<^sub>F\<^sub>G` have "y \<sharp> F" and "A\<^sub>F\<^sub>G' \<sharp>* F"
      apply(auto simp add: abs_fresh frame_res_chain_fresh_set)
      apply(induct A\<^sub>F\<^sub>G')
      apply(auto simp add: abs_fresh)
      by (metis `A\<^sub>F\<^sub>G = y # A\<^sub>F\<^sub>G'` `A\<^sub>F\<^sub>G' \<sharp>* F` fresh_sets(5))
    from `distinct A\<^sub>F\<^sub>G` `A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'` have "y \<sharp> A\<^sub>F\<^sub>G'" and "distinct A\<^sub>F\<^sub>G'" by auto
    
    with `A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'` `merge_frame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>` `x \<sharp> G` `x \<sharp> A\<^sub>F\<^sub>G` `y \<sharp> A\<^sub>F\<^sub>G'`
    have "merge_frame F G = \<langle>A\<^sub>F\<^sub>G', [(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with `distinct A\<^sub>F\<^sub>G'` `A\<^sub>F\<^sub>G' \<sharp>* F` `A\<^sub>F\<^sub>G' \<sharp>* G`
         `\<And>G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G. \<lbrakk>merge_frame F G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>; distinct A\<^sub>F\<^sub>G; A\<^sub>F\<^sub>G \<sharp>* F; A\<^sub>F\<^sub>G \<sharp>* G\<rbrakk> \<Longrightarrow> \<exists>A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G. A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G \<and> \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G \<and> F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle> \<and> A\<^sub>F \<sharp>* \<Psi>\<^sub>G \<and> A\<^sub>G \<sharp>* \<Psi>\<^sub>F`
    obtain A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G where "A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G" and "([(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" and FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
      by metis

    from `A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G` `A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'` have  "A\<^sub>F\<^sub>G = (y#A\<^sub>F)@A\<^sub>G" by simp
    moreover from `A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G` `y \<sharp> A\<^sub>F\<^sub>G'` `x \<sharp> A\<^sub>F\<^sub>G'` have "x \<sharp> A\<^sub>F" and "y \<sharp> A\<^sub>F" and "x \<sharp> A\<^sub>G" and "y \<sharp> A\<^sub>G" by simp+
    with `y \<sharp> G` `x \<sharp> G` `x \<sharp> A\<^sub>F\<^sub>G` FrG have "y \<sharp> \<Psi>\<^sub>G" and "x \<sharp> \<Psi>\<^sub>G" 
      by auto
    from `([(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G` have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = [(x, y)] \<bullet> (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G)"
      by simp
    with `x \<sharp> \<Psi>\<^sub>G` `y \<sharp> \<Psi>\<^sub>G` have "\<Psi>\<^sub>F\<^sub>G = ([(x, y)] \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>G" by(simp add: eqvts)
    moreover from FrF have "([(x, y)] \<bullet> F) = [(x, y)] \<bullet> \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" by simp
    with `x \<sharp> A\<^sub>F` `y \<sharp> A\<^sub>F` have "([(x, y)] \<bullet> F) = \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: eqvts)
    hence "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) = \<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
    with `y \<sharp> F` have "\<lparr>\<nu>x\<rparr>F = \<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: alpha_frame_res)
    moreover with `A\<^sub>G \<sharp>* \<Psi>\<^sub>F` have "([(x, y)] \<bullet> A\<^sub>G) \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with `x \<sharp> A\<^sub>G` `y \<sharp> A\<^sub>G` have "A\<^sub>G \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by simp
    moreover from `A\<^sub>F \<sharp>* \<Psi>\<^sub>G` `y \<sharp> \<Psi>\<^sub>G` have "(y#A\<^sub>F) \<sharp>* \<Psi>\<^sub>G" by simp
    ultimately show ?case using FrG 
      by blast
  qed
  with A show ?thesis by blast
qed

lemma merge_frame_res1[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   x   :: name
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<Psi>\<^sub>F"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  
  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>)) = (\<langle>(A\<^sub>F@x#A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
apply(fold frame_res_chain.simps)
by(rule merge_frames) auto

lemma merge_frame_res2[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   x   :: name
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* A\<^sub>F"
  and     "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<Psi>\<^sub>F"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  
  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>)) = (\<langle>(A\<^sub>F@x#A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
apply(fold frame_res_chain.simps)
by(rule merge_frames) auto

lemma insert_assertion_res_chain[simp]:
  fixes xvec :: "name list"
  and   F    :: "'b frame"
  and   \<Psi>   :: 'b

  assumes "xvec \<sharp>* \<Psi>"

  shows "insert_assertion (\<lparr>\<nu>*xvec\<rparr>F) \<Psi> = \<lparr>\<nu>*xvec\<rparr>(insert_assertion F \<Psi>)"
using assms
by(induct xvec) auto

lemma extract_frame_res_chain[simp]:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extract_frame(\<lparr>\<nu>*xvec\<rparr>P) = \<lparr>\<nu>*xvec\<rparr>(extract_frame P)"
by(induct xvec) auto

lemma frame_res_fresh_chain:
  fixes xvec :: "name list"
  and   F    :: "'b frame"

  assumes "xvec \<sharp>* F"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F F"
using assms
proof(induct xvec)
  case Nil
  thus ?case by simp
next
  case(Cons x xvec)
  thus ?case
    by auto (metis frame_res_pres frame_res_fresh Frame_stat_eq_trans)
qed

end

locale assertion = assertion_aux S_compose S_imp S_bottom S_chan_eq
  for S_compose  :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"
  and S_imp      :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool"
  and S_bottom   :: 'b
  and S_chan_eq   :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c" +

  assumes Composition:   "assertion_aux.Assertion_stat_eq S_imp \<Psi> \<Psi>' \<Longrightarrow> assertion_aux.Assertion_stat_eq S_imp (S_compose \<Psi> \<Psi>'') (S_compose \<Psi>' \<Psi>'')"
  and     Identity:      "assertion_aux.Assertion_stat_eq S_imp (S_compose \<Psi> S_bottom) \<Psi>"
  and     Associativity: "assertion_aux.Assertion_stat_eq S_imp (S_compose (S_compose \<Psi> \<Psi>') \<Psi>'') (S_compose \<Psi> (S_compose \<Psi>' \<Psi>''))"
  and     Commutativity: "assertion_aux.Assertion_stat_eq S_imp (S_compose \<Psi> \<Psi>') (S_compose \<Psi>' \<Psi>)"

begin

notation S_compose (infixr "\<otimes>" 90)
notation S_imp ("_ \<turnstile> _" [85, 85] 85)
notation S_chan_eq ("_ \<leftrightarrow> _" [90, 90] 90)
notation S_bottom ("\<bottom>" 90)

lemma composition_sym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi>'' \<otimes> \<Psi>'"
proof -
  have "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi> \<otimes> \<Psi>''" by(rule Commutativity)
  moreover from assms have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
  moreover have "\<Psi>' \<otimes> \<Psi>'' \<simeq> \<Psi>'' \<otimes> \<Psi>'" by(rule Commutativity)
  ultimately show ?thesis by(blast intro: Assertion_stat_eq_trans)
qed

lemma Composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>'' \<simeq> \<Psi>'''"
  
  shows "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>'''"
using assms
by(metis Composition Commutativity Assertion_stat_eq_trans)
  

lemma composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
proof -
  have "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Associativity)
  moreover from assms have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> \<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Composition)
  moreover have "\<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
    by(rule Associativity[THEN Assertion_stat_eq_sym])
  ultimately show ?thesis by(blast dest: Assertion_stat_eq_trans)
qed

lemma associativity_sym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b
  
  shows "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
proof -
  have "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')"
    by(rule Associativity)
  moreover have "\<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>')"
    by(rule composition_sym[OF Commutativity])
  moreover have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>') \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
    by(rule Assertion_stat_eq_sym[OF Associativity])
  ultimately show ?thesis
    by(blast dest: Assertion_stat_eq_trans)
qed

lemma frame_int_associativity:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  shows "\<langle>A\<^sub>F, (\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')\<rangle>"
by(induct A\<^sub>F) (auto intro: Associativity frame_res_pres)

lemma frame_int_commutativity:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<rangle>"
by(induct A\<^sub>F) (auto intro: Commutativity frame_res_pres)

lemma frame_int_identity:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b 

  shows "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> S_bottom\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
by(induct A\<^sub>F) (auto intro: Identity frame_res_pres)

lemma frame_int_composition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms
by(induct A\<^sub>F) (auto intro: Composition frame_res_pres)

lemma frame_int_composition_sym:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>'\<rangle>"
using assms
by(induct A\<^sub>F) (auto intro: composition_sym frame_res_pres)

lemma frame_commutativity:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<otimes>\<^sub>F G \<simeq>\<^sub>F G \<otimes>\<^sub>F F"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* G"
    by(rule fresh_frame)
  moreover obtain A\<^sub>G \<Psi>\<^sub>G where "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F" and "A\<^sub>G \<sharp>* A\<^sub>F"
    by(rule_tac C="(A\<^sub>F, \<Psi>\<^sub>F)" in fresh_frame) auto
  moreover from `A\<^sub>F \<sharp>* G` `G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>` `A\<^sub>G \<sharp>* A\<^sub>F` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
    by auto
  ultimately show ?thesis
    by auto (metis Frame_stat_eq_trans frame_chain_append frame_res_chain_comm frame_int_commutativity)
qed
  
lemma frame_scope_ext:
  fixes x :: name
  and   F :: "'b frame"
  and   G :: "'b frame"

  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
proof -
  have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>(G \<otimes>\<^sub>F F)"
    by(metis frame_res_pres frame_commutativity)
  with `x \<sharp> F` have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F (\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F"
    by simp
  moreover have "(\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
    by(rule frame_commutativity)
  ultimately show ?thesis by(rule Frame_stat_eq_trans)
qed

lemma insert_double_assertion_stat_eq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "insert_assertion(insert_assertion F \<Psi>) \<Psi>' \<simeq>\<^sub>F (insert_assertion F) (\<Psi> \<otimes> \<Psi>')"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'" and "A\<^sub>F \<sharp>* (\<Psi> \<otimes> \<Psi>')"
    by(rule_tac C="(\<Psi>, \<Psi>')" in fresh_frame) auto
  thus ?thesis
    by auto (metis frame_int_composition Commutativity frame_int_associativity Frame_stat_eq_trans Frame_stat_eq_sym)
qed

lemma guarded_stat_eq:
  fixes P  :: "('a, 'b, 'c) psi"
  and   I  :: "('a, 'b, 'c) input"
  and   C  :: "('a, 'b, 'c) psi_case"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b

  shows "\<lbrakk>guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
  and   "\<lbrakk>guarded' I; extract_frame' I = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
  and   "\<lbrakk>guarded'' C; extract_frame'' C = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
proof(nominal_induct P and I and C arbitrary: A\<^sub>P \<Psi>\<^sub>P rule: psi_input_psi_case.strong_inducts)
  case(Psi_nil A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Output M N P A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Input M In  A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Case psi_case A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Par P Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q)
  from `guarded(P \<parallel> Q)` have "guarded P" and "guarded Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* Q" by(rule fresh_frame)
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" 
    by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P)" in fresh_frame) auto
  
  from `\<And>A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>P = ({}::name set))` `guarded P` FrP
  have "\<Psi>\<^sub>P \<simeq> \<bottom>" and "supp \<Psi>\<^sub>P = ({}::name set)" by simp+
  from `\<And>A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>guarded Q; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>Q \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>Q = ({}::name set))` `guarded Q` FrQ
  have "\<Psi>\<^sub>Q \<simeq> \<bottom>" and "supp \<Psi>\<^sub>Q = ({}::name set)" by simp+
  
  from `A\<^sub>P \<sharp>* Q` FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extract_frame_fresh_chain) auto
  with `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` FrP FrQ `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by auto
  with `supp \<Psi>\<^sub>P = {}` `supp \<Psi>\<^sub>Q = {}` comp_supp have "\<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q"
    by blast
  moreover from `\<Psi>\<^sub>P \<simeq> \<bottom>` `\<Psi>\<^sub>Q \<simeq> \<bottom>` have "\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<simeq> \<bottom>"
    by(metis Composition Identity Associativity Commutativity Assertion_stat_eq_trans)
  ultimately show ?case using `supp \<Psi>\<^sub>P = {}` `supp \<Psi>\<^sub>Q = {}` comp_supp
    by blast
next
  case(Res x P A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P)
  from `guarded(\<lparr>\<nu>x\<rparr>P)` have "guarded P" by simp
  moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(rule fresh_frame)
  moreover note `\<And>A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>P = ({}::name set))`
  ultimately have "\<Psi>\<^sub>P \<simeq> \<bottom>" and "supp \<Psi>\<^sub>P = ({}::name set)" by auto
  from FrP `extract_frame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>` have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>" by simp
  with `supp \<Psi>\<^sub>P = {}` have "\<Psi>\<^sub>P = \<Psi>\<^sub>x\<^sub>P" by(auto simp del: frame_res_chain.simps)
  with `\<Psi>\<^sub>P \<simeq> \<bottom>` `supp \<Psi>\<^sub>P = {}` show ?case
    by simp
next
  case(Assert \<Psi> A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Bang P A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Trm M P)
  thus ?case by simp
next
  case(Bind x I)
  thus ?case by simp
next
  case Empty_case
  thus ?case by simp
next
  case(Cond \<phi> P psi_case)
  thus ?case by simp
qed

end

end
