theory Agent
  imports Subst_Term
begin

nominal_datatype ('term, 'assertion, 'condition) psi = 
  Psi_nil ("\<zero>" 190)


| Output "'term::fs_name" 'term "('term, 'assertion::fs_name, 'condition::fs_name) psi"    ("_\<langle>_\<rangle>._" [120, 120, 110] 110)
| Input 'term "('term, 'assertion, 'condition) input"                                      ("_\<lparr>_" [120, 120] 110)
| Case "(('term, 'assertion, 'condition) psi_case)"                                         ("Case _" [120] 120)
| Par "('term, 'assertion, 'condition) psi" "('term, 'assertion, 'condition) psi"          (infixl "\<parallel>" 90)
| Res "\<guillemotleft>name\<guillemotright>(('term, 'assertion, 'condition) psi)"                                        ("\<lparr>\<nu>_\<rparr>_" [120, 120] 110)
| Assert 'assertion                                                                        ("\<lbrace>_\<rbrace>" [120] 120)
| Bang "('term, 'assertion, 'condition) psi"                                               ("!_" [110] 110)

and ('term, 'assertion, 'condition) input = 
  Trm 'term "(('term, 'assertion, 'condition) psi)"                                        ("\<rparr>_._" [130, 130] 130)
| Bind "\<guillemotleft>name\<guillemotright>(('term, 'assertion, 'condition) input)"                                     ("\<nu>__" [120, 120] 120)

and ('term, 'assertion, 'condition) psi_case = 
  Empty_case                                                                                ("\<bottom>\<^sub>c" 120)
| Cond 'condition "(('term, 'assertion, 'condition) psi)"
                  "(('term, 'assertion, 'condition) psi_case)"                              ("\<box> _ \<Rightarrow> _ _ " [120, 120, 120] 120)

lemma psi_fresh_set[simp]:
  fixes X :: "name set"
  and   M :: "'a::fs_name"
  and   N :: 'a
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psi_case"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name
  and   \<Psi> :: 'b
  and   \<Phi> :: 'c

  shows "X \<sharp>* (M\<langle>N\<rangle>.P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* M\<lparr>I = (X \<sharp>* M \<and> X \<sharp>* I)"
  and   "X \<sharp>* Case C = X \<sharp>* C"
  and   "X \<sharp>* (P \<parallel> Q) = (X \<sharp>* P \<and> X \<sharp>* Q)"
  and   "X \<sharp>* \<lparr>\<nu>x\<rparr>P = (X \<sharp>* [x].P)"
  and   "X \<sharp>* \<lbrace>\<Psi>\<rbrace> = X \<sharp>* \<Psi>"
  and   "X \<sharp>* !P = X \<sharp>* P"
  and   "X \<sharp>* \<zero>"
  and   "X \<sharp>* Trm N P = (X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* Bind x I = X \<sharp>* ([x].I)"

  and   "X \<sharp>* \<bottom>\<^sub>c"
  and   "X \<sharp>* \<box> \<Phi> \<Rightarrow> P C = (X \<sharp>* \<Phi> \<and> X \<sharp>* P \<and> X \<sharp>* C)"
by(auto simp add: fresh_star_def psi.fresh)+

lemma psi_fresh_vec[simp]:
  fixes xvec :: "name list"

  shows "xvec \<sharp>* (M\<langle>N\<rangle>.P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* M\<lparr>I = (xvec \<sharp>* M \<and> xvec \<sharp>* I)"
  and   "xvec \<sharp>* Case C = xvec \<sharp>* C"
  and   "xvec \<sharp>* (P \<parallel> Q) = (xvec \<sharp>* P \<and> xvec \<sharp>* Q)"
  and   "xvec \<sharp>* \<lparr>\<nu>x\<rparr>P = (xvec \<sharp>* [x].P)"
  and   "xvec \<sharp>* \<lbrace>\<Psi>\<rbrace> = xvec \<sharp>* \<Psi>"
  and   "xvec \<sharp>* !P = xvec \<sharp>* P"
  and   "xvec \<sharp>* \<zero>"

  and   "xvec \<sharp>* Trm N P = (xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* Bind x I = xvec \<sharp>* ([x].I)"

  and   "xvec \<sharp>* \<bottom>\<^sub>c"
  and   "xvec \<sharp>* \<box> \<Phi> \<Rightarrow> P C = (xvec \<sharp>* \<Phi> \<and> xvec \<sharp>* P \<and> xvec \<sharp>* C)"
by(auto simp add: fresh_star_def)

fun psi_cases :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list \<Rightarrow> ('a, 'b, 'c) psi_case"
where 
  base: "psi_cases [] = \<bottom>\<^sub>c"
| step: "psi_cases ((\<Phi>, P)#xs) = Cond \<Phi> P (psi_cases xs)"

lemma psi_cases_eqvt[eqvt]:
  fixes p  :: "name prm"
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"

  shows "(p \<bullet> (psi_cases Cs)) = psi_cases(p \<bullet> Cs)"
by(induct Cs) auto

lemma psi_cases_fresh[simp]:
  fixes x  :: name
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  
  shows "x \<sharp> psi_cases Cs = x \<sharp> Cs"
using assms
by(induct Cs)
  (auto simp add: fresh_list_nil fresh_list_cons)

lemma psi_cases_fresh_chain[simp]:
  fixes xvec :: "name list"
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   Xs   :: "name set"
  
  shows "(xvec \<sharp>* psi_cases Cs) = xvec \<sharp>* Cs"
  and   "(Xs \<sharp>* psi_cases Cs) = Xs \<sharp>* Cs"
by(auto simp add: fresh_star_def)

abbreviation
  psi_cases_judge ("Cases _" [80] 80) where "Cases Cs \<equiv> Case(psi_cases Cs)"

fun res_chain :: "name list \<Rightarrow> ('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) psi"
where
  res_chainbase: "res_chain [] P = P"
| res_chainstep: "res_chain (x#xs) P = \<lparr>\<nu>x\<rparr>(res_chain xs P)"

notation res_chain ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80)

lemma res_chain_eqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>P) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> P)"
by(induct_tac xvec, auto)

lemma res_chain_supp:
  fixes xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "supp(\<lparr>\<nu>*xvec\<rparr>P) = (supp P) - set xvec"
by(induct xvec) (auto simp add: psi.supp abs_supp)

lemma res_chain_fresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "x \<sharp> \<lparr>\<nu>*xvec\<rparr>P = (x \<in> set xvec \<or> x \<sharp> P)"
by (induct xvec) (simp_all add: abs_fresh)

lemma res_chain_fresh_set: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> P)"
  and   "yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (\<forall>x\<in>(set yvec). x \<in> set xvec \<or> x \<sharp> P)"
by (simp add: fresh_star_def res_chain_fresh)+

lemma res_chain_fresh_simps[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"

  shows "Xs \<sharp>* xvec \<Longrightarrow> Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (Xs \<sharp>* P)"
  and   "yvec \<sharp>* xvec \<Longrightarrow> yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (yvec \<sharp>* P)"
  and   "xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
apply(simp add: res_chain_fresh_set) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: res_chain_fresh_set) apply(force simp add: fresh_star_def name_list_supp fresh_def)
by(simp add: res_chain_fresh_set)
  
lemma res_chain_alpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes xvec_freshP: "(p \<bullet> xvec) \<sharp>* P"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>P = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> P)"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
    by (simp add: res_chain_fresh_set)
  moreover from xvec_freshP have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
    by (simp add: res_chain_fresh_set) (simp add: fresh_star_def)
  ultimately have "\<lparr>\<nu>*xvec\<rparr>P = p \<bullet> (\<lparr>\<nu>*xvec\<rparr>P)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma res_chain_append:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  
  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>P = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>P)"
by(induct xvec) auto

lemma res_chain_simps[dest]:
  fixes xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q'   :: "('a, 'b, 'c) psi"

  shows "((\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) = P' \<parallel> Q') \<Longrightarrow> (P = P' \<and> Q = Q')"
  and   "(P \<parallel> Q = \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<Longrightarrow> (P = P' \<and> Q = Q')"
by(case_tac xvec, simp_all add: psi.inject)+

fun input_chain :: "name list \<Rightarrow> 'a::fs_name \<Rightarrow> ('a, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) input"
where
  input_chainbase: "input_chain [] N P = \<rparr>(N).P"
| input_chainstep: "input_chain (x#xs) N P = \<nu> x (input_chain xs N P)"

abbreviation
  input_chain_judge ("_\<lparr>\<lambda>*_ _\<rparr>._" [80, 80, 80, 80] 80) where "M\<lparr>\<lambda>*xvec N\<rparr>.P \<equiv> M\<lparr>(input_chain xvec N P)"

lemma input_chain_eqvt[eqvt]:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  shows "p \<bullet> (input_chain xvec N P) = input_chain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P)"
by(induct_tac xvec) auto

lemma input_chain_fresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "x \<sharp> (input_chain xvec N P) = (x \<in> set xvec \<or> (x \<sharp> N \<and> x \<sharp> P))"
by (induct xvec) (simp_all add: abs_fresh)

lemma induct_chain_simps[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (input_chain xvec N P)"
by(induct xvec) (auto simp add: abs_fresh abs_fresh_star fresh_star_def)

lemma input_chain_fresh_set: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "Xs \<sharp>* (input_chain xvec N P) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> (x \<sharp> N \<and> x \<sharp> P))"
by (simp add: fresh_star_def input_chain_fresh)

lemma input_chain_alpha:
  fixes p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes Xs_freshP: "Xs \<sharp>* (input_chain xvec N P)"
  and     Ys_freshN: "Ys \<sharp>* N"
  and     Ys_freshP: "Ys \<sharp>* P"
  and     S: "set p \<subseteq> Xs \<times> Ys"

  shows "(input_chain xvec N P) = (input_chain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P))"
proof -
  note pt_name_inst at_name_inst Xs_freshP S
  moreover from Ys_freshN Ys_freshP have "Ys \<sharp>* (input_chain xvec N P)"
    by (simp add: input_chain_fresh_set) (simp add: fresh_star_def)
  ultimately have "(input_chain xvec N P) = p \<bullet> (input_chain xvec N P)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma input_chain_alpha':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes xvec_freshP: "(p \<bullet> xvec) \<sharp>* P"
  and     xvec_freshN: "(p \<bullet> xvec) \<sharp>* N"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "(input_chain xvec N P) = (input_chain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P))"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (input_chain xvec N P)"
    by (simp add: input_chain_fresh_set)
  ultimately show ?thesis using xvec_freshN xvec_freshP 
    by(rule_tac input_chain_alpha) (simp add: fresh_star_def)+
qed

lemma alpha_res:
  fixes M :: "'a::fs_name"
  and   x :: name
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   y :: name

  assumes y_freshP: "y \<sharp> P"

  shows "\<lparr>\<nu>x\<rparr>P = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
proof(cases "x = y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with y_freshP show ?thesis
    by(perm_simp add: psi.inject alpha calc_atm fresh_left)
qed

lemma alpha_input:
  fixes x :: name
  and   I :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input"
  and   c :: name

  assumes A1: "c \<sharp> I"

  shows "\<nu> x I = \<nu> c([(x, c)] \<bullet> I)"
proof(cases "x = c")
  assume "x=c"
  thus ?thesis by simp
next
  assume "x \<noteq> c"
  with A1 show ?thesis
    by(perm_simp add: input.inject alpha calc_atm fresh_left)
qed

lemma input_chain_length_eq:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "length xvec = length yvec"
  and     "xvec \<sharp>* yvec"
  and     "distinct yvec"
  and     "yvec \<sharp>* M"
  and     "yvec \<sharp>* P"

  obtains N Q where "input_chain xvec M P = input_chain yvec N Q"
proof -
  assume "\<And>N Q. input_chain xvec M P = input_chain yvec N Q \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>N Q. input_chain xvec M P = input_chain yvec N Q"
  proof(induct n arbitrary: xvec yvec M P)
    case 0
    thus ?case by auto
  next
    case(Suc n xvec yvec M P)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    with `length xvec = length yvec`
    obtain y yvec' where "yvec = y#yvec'" by(case_tac yvec) auto
    from `yvec = y#yvec'` `xvec=x#xvec'` `xvec \<sharp>* yvec` `distinct yvec` `length xvec = length yvec` `yvec \<sharp>* M` `yvec \<sharp>* P`
    have "length xvec' = length yvec'" and "xvec' \<sharp>* yvec'" and "distinct yvec'" and "yvec' \<sharp>* M" and "yvec' \<sharp>* P"
      by simp+
    then obtain N Q where Eq: "input_chain xvec' M P = input_chain yvec' N Q" using `length xvec' = n`
      by(drule_tac Suc) auto
    moreover from `distinct yvec` `yvec = y#yvec'` have "y \<sharp> yvec'" by auto
    moreover from `xvec \<sharp>* yvec` `xvec = x#xvec'` `yvec=y#yvec'` have "x \<noteq> y" and "x \<sharp> yvec'"
      by auto
    moreover from `yvec \<sharp>* M` `yvec \<sharp>* P` `yvec = y#yvec'` have "y \<sharp> M" and "y \<sharp> P" by auto
    hence "y \<sharp> input_chain xvec' M P" by(simp add: input_chain_fresh)
    with Eq have "y \<sharp> input_chain yvec' N Q" by(simp add: input_chain_fresh)
    ultimately have "\<nu> x (input_chain xvec' M P) = \<nu> y (input_chain yvec' ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q))"
      by(simp add: input.inject alpha' eqvts name_swap)
    thus ?case using `xvec = x#xvec'` `yvec=y#yvec'` by force
  qed
  ultimately show ?thesis
    by blast
qed

lemma input_chain_eq:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "input_chain xvec M P = input_chain yvec N Q"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinct_perm p" and "yvec = p \<bullet> xvec" and "N = p \<bullet> M" and "Q = p \<bullet> P"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinct_perm p; yvec = p \<bullet> xvec; N = p \<bullet> M; Q = p \<bullet> P\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P"
  proof(induct n arbitrary: xvec yvec M N P Q)
    case(0 xvec yvec M N P Q)
    have Eq: "input_chain xvec M P = input_chain yvec N Q" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: input.inject)
  next
    case(Suc n xvec yvec M N P Q)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `input_chain xvec M P = input_chain yvec N Q` `xvec = x # xvec'`
    obtain y yvec' where "input_chain (x#xvec') M P = input_chain (y#yvec') N Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<nu> x (input_chain xvec' M P) = \<nu> y (input_chain yvec' N Q)"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec M N P Q. \<lbrakk>input_chain xvec (M::'a) (P::('a, 'b, 'c) psi) = input_chain yvec (N::'a) (Q::('a, 'b, 'c) psi); xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P"
      by fact
    from EQ `x \<noteq> y`  `x \<sharp> yvec'` `y \<sharp> yvec'` have "input_chain xvec' M P = input_chain yvec' ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
      by(simp add: input.inject alpha eqvts)
    with `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'` `length xvec' = n` IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "yvec' = p \<bullet> xvec'" and "([(x, y)] \<bullet> N) = p \<bullet> M" and "([(x, y)] \<bullet> Q) = p \<bullet> P"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from `x \<sharp> xvec'` `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_list_nil fresh_list_cons fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S `distinct_perm p` `x \<noteq> y` have "distinct_perm((x, y)#p)" by auto
    moreover from `yvec' = p \<bullet> xvec'` `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: calc_atm fresh_chain_simps)
    moreover from `([(x, y)] \<bullet> N) = p \<bullet> M` have "([(x, y)] \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> M"
      by(simp add: pt_bij)
    hence "N = ((x, y)#p) \<bullet> M" by simp
    moreover from `([(x, y)] \<bullet> Q) = p \<bullet> P` have "([(x, y)] \<bullet> [(x, y)] \<bullet> Q) = [(x, y)] \<bullet> p \<bullet> P"
      by(simp add: pt_bij)
    hence "Q = ((x, y)#p) \<bullet> P" by simp
    ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma input_chain_eq_length:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "input_chain xvec M P = input_chain yvec N Q"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `input_chain xvec M P = input_chain yvec N Q` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec M P N Q)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `input_chain xvec M P = input_chain yvec N Q` `xvec = x # xvec'`
    obtain y yvec' where "input_chain (x#xvec') M P = input_chain (y#yvec') N Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<nu> x (input_chain xvec' M P) = \<nu> y (input_chain yvec' N Q)"
      by simp
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>input_chain xvec (M::'a) (P::('a, 'b, 'c) psi) = input_chain yvec N Q; n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "input_chain xvec' M P = input_chain yvec' N Q"
	by(simp add: alpha input.inject)
      with IH `length xvec' = n` have "length xvec' = length yvec'"
	by blast
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "input_chain xvec' M P = input_chain ([(x, y)] \<bullet> yvec') ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
	by(simp add: alpha input.inject eqvts)
      with IH `length xvec' = n` have "length xvec' = length ([(x, y)] \<bullet> yvec')"
	by blast
      hence "length xvec' = length yvec'"
	by simp
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    qed
  qed
qed

lemma alpha_input_chain:
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* M"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "input_chain xvec M P = input_chain yvec ([xvec yvec] \<bullet>\<^sub>v M) ([xvec yvec] \<bullet>\<^sub>v P)"
using assms
proof(induct rule: compose_perm_induct)
  case c_base
  show ?case by simp
next
  case(c_step x xvec y yvec)
  thus ?case 
    apply auto
    by(subst alpha_input[of y]) (auto simp add: input_chain_fresh eqvts)
qed

lemma input_chain_inject[simp]:

  shows "(input_chain xvec M P = input_chain xvec N Q) = ((M = N) \<and> (P = Q))"
by(induct xvec) (auto simp add: input.inject alpha)

lemma alpha_input_distinct:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Eq: "input_chain xvec M P = input_chain yvec N Q"
  and     xvec_dist: "distinct xvec"
  and     Mem: "\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp M"
  and     xvec_freshyvec: "xvec \<sharp>* yvec"
  and     xvec_freshN: "xvec \<sharp>* N"
  and     xvec_freshQ: "xvec \<sharp>* Q"

  shows "distinct yvec"
proof -
  from Eq have "length xvec = length yvec"
    by(rule input_chain_eq_length)
  with assms show ?thesis
  proof(induct n=="length xvec" arbitrary: xvec yvec N Q rule: nat.induct)
    case(zero xvec yvec N Q)
    thus ?case by simp
  next
    case(Suc n xvec yvec N Q)
    have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
    then obtain x xvec' y yvec' where x_eq: "xvec = x#xvec'" and y_eq: "yvec = y#yvec'"
                                  and L': "length xvec' = length yvec'"
      by(cases xvec, auto, cases yvec, auto)
    have xvec_freshyvec: "xvec \<sharp>* yvec" and xvec_dist: "distinct xvec" by fact+
    with x_eq y_eq have xineqy: "x \<noteq> y" and xvec'_freshyvec': "xvec' \<sharp>* yvec'"
                  and xvec'_dist: "distinct xvec'" and x_freshxvec': "x \<sharp> xvec'"
                  and x_freshyvec': "x \<sharp> yvec'" and y_freshxvec': "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    have Eq: "input_chain xvec M P = input_chain yvec N Q" by fact
    with x_eq y_eq xineqy have Eq': "input_chain xvec' M P = input_chain ([(x, y)] \<bullet> yvec') ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
      by(simp add: input.inject alpha eqvts) 
    moreover have Mem:"\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp M" by fact
    with x_eq have "\<And>x. x \<in> set xvec' \<Longrightarrow> x \<in> supp M" by simp
    moreover have xvec_freshN: "xvec \<sharp>* N" by fact
    with x_eq x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> N)" by simp
    moreover have xvec_freshQ: "xvec \<sharp>* Q" by fact
    with x_eq x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
    moreover have "Suc n = length xvec" by fact
    with x_eq have "n = length xvec'" by simp
    moreover from xvec'_freshyvec' x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> yvec')"
      by simp
    moreover from L' have "length xvec' = length([(x, y)] \<bullet> yvec')" by simp
    moreover have "\<And>xvec yvec N Q.
                   \<lbrakk>n = length xvec; input_chain xvec (M::'a) (P::('a, 'b, 'c) psi) = input_chain yvec N Q; distinct xvec; \<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp M; xvec \<sharp>* yvec;
                    xvec \<sharp>* N; xvec \<sharp>* Q; length xvec = length yvec\<rbrakk>
                    \<Longrightarrow> distinct yvec" by fact
    ultimately have "distinct([(x, y)] \<bullet> yvec')" using xvec'_dist
      by blast
    hence "distinct yvec'" by simp
    from Mem x_eq have x_suppM: "x \<in> supp M" by simp
    from L xvec_freshyvec xvec_dist xvec_freshN xvec_freshQ
    have "input_chain yvec N Q = input_chain xvec ([yvec xvec] \<bullet>\<^sub>v N) ([yvec xvec] \<bullet>\<^sub>v Q)"
      by(simp add: alpha_input_chain)
    with Eq have "M = [yvec xvec] \<bullet>\<^sub>v N"  by auto
    with x_eq y_eq have "M = [(y, x)] \<bullet> [yvec' xvec'] \<bullet>\<^sub>v N"
      by simp
    with x_suppM have y_suppN: "y \<in> supp([yvec' xvec'] \<bullet>\<^sub>v N)"
      by(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
        (simp add: calc_atm eqvts name_swap)
    have "y \<sharp> yvec'"
    proof(simp add: fresh_def, rule notI)
      assume "y \<in> supp yvec'"
      hence "y mem yvec'"
	by(induct yvec') (auto simp add: supp_list_nil supp_list_cons supp_atm)
      moreover from xvec_freshN x_eq x_freshxvec' have "xvec' \<sharp>* N" by simp
      ultimately have "y \<sharp> [yvec' xvec'] \<bullet>\<^sub>v  N" using L' xvec'_freshyvec' xvec'_dist
	by(force intro: fresh_chain_perm simp add: fresh_chain_sym)
      with y_suppN show "False" by(simp add: fresh_def)
    qed
    with `distinct yvec'`  y_eq show ?case by simp
  qed
qed

lemma psi_cases_inject[simp]:
  fixes CsP  :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"

  shows "(psi_cases CsP = psi_cases CsQ) = (CsP = CsQ)"
proof(induct CsP arbitrary: CsQ)
  case(Nil CsQ)
  thus ?case by(case_tac CsQ) (auto)
next
  case(Cons a CsP CsQ)
  thus ?case
    by(case_tac a, case_tac CsQ) (clarsimp simp add: psi_case.inject)+
qed

lemma cases_inject[simp]:
  fixes CsP :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

  shows "(Cases CsP = Cases CsQ) = (CsP = CsQ)"
apply(induct CsP)
apply(auto simp add: psi_case.inject)
apply(case_tac CsQ)
apply(simp add: psi_case.inject psi.inject)
apply(force simp add: psi_case.inject psi.inject)
apply(case_tac CsQ)
apply(force simp add: psi_case.inject psi.inject)
apply(auto simp add: psi_case.inject psi.inject)
apply(simp only: psi_cases.simps[symmetric])
apply(simp only: psi_cases_inject)
apply simp
apply(case_tac CsQ)
by(auto simp add: psi_case.inject psi.inject)

nominal_primrec
  guarded :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> bool"
  and guarded'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> bool"
  and guarded'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case \<Rightarrow> bool"

where
  "guarded (\<zero>) = True"
| "guarded (M\<langle>N\<rangle>.P) = True"
| "guarded (M\<lparr>I) = True"
| "guarded (Case C) = guarded'' C"
| "guarded (P \<parallel> Q) = ((guarded P) \<and> (guarded Q))"
| "guarded (\<lparr>\<nu>x\<rparr>P) = (guarded P)"
| "guarded (\<lbrace>\<Psi>\<rbrace>) = False"
| "guarded (!P) = guarded P"

| "guarded' (Trm M P) = False"
| "guarded' (\<nu> y I) = False"

| "guarded'' (\<bottom>\<^sub>c) = True"
| "guarded'' (\<box>\<phi> \<Rightarrow> P C) = (guarded P \<and> guarded'' C)"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_bool)+

lemma guarded_eqvt[eqvt]:
  fixes p    :: "name prm"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  shows "(p \<bullet> (guarded P)) = guarded (p \<bullet> P)"
  and   "(p \<bullet> (guarded' I)) = guarded' (p \<bullet> I)"
  and   "(p \<bullet> (guarded'' C)) = guarded'' (p \<bullet> C)"
by(nominal_induct P and I and C rule: psi_input_psi_case.strong_inducts)
  (simp add: eqvts)+

lemma guarded_closed[simp]:
  fixes P :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   p :: "name prm"

  assumes "guarded P"

  shows "guarded(p \<bullet> P)"
proof -
  from `guarded P` have "p \<bullet> (guarded P)"
    by(simp add: perm_bool)
  thus ?thesis by(simp add: eqvts)
qed

locale subst_psi =
  subst_term: strong_subst_type subst_term +
  subst_assert: subst_type subst_assert +
  subst_cond: subst_type subst_cond

  for subst_term :: "('a::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'a"
  and subst_assert :: "('b::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'b"
  and subst_cond :: "('c::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'c"
begin

nominal_primrec 
    subs   :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b, 'c) psi"
and subs'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b, 'c) input"
and subs'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case \<Rightarrow> name list \<Rightarrow> 'a list  \<Rightarrow> ('a, 'b, 'c) psi_case"

where
  "subs (\<zero>) xvec Tvec = \<zero>"
| "(subs (M\<langle>N\<rangle>.P) xvec Tvec) = (subst_term M xvec Tvec)\<langle>(subst_term N xvec Tvec)\<rangle>.(subs P xvec Tvec)"
| "(subs (M\<lparr>I) xvec Tvec) = (subst_term M xvec Tvec)\<lparr>(subs' I xvec Tvec)"

| "(subs (Case C) xvec Tvec) = (Case (subs'' C xvec Tvec))"
| "(subs (P \<parallel> Q) xvec Tvec) = (subs P xvec Tvec) \<parallel> (subs Q xvec Tvec)"
| "\<lbrakk>y \<sharp> xvec; y \<sharp> Tvec\<rbrakk> \<Longrightarrow> (subs (\<lparr>\<nu>y\<rparr>P) xvec Tvec) = \<lparr>\<nu>y\<rparr>(subs P xvec Tvec)"
| "(subs (\<lbrace>\<Psi>\<rbrace>) xvec Tvec) = \<lbrace>(subst_assert \<Psi> xvec Tvec)\<rbrace>"
| "(subs (!P) xvec Tvec) = !(subs P xvec Tvec)"

| "(subs' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) xvec Tvec) = (\<rparr>(subst_term M xvec Tvec).(subs P xvec Tvec))"
| "\<lbrakk>y \<sharp> xvec; y \<sharp> Tvec\<rbrakk> \<Longrightarrow> (subs' (\<nu> y I) xvec Tvec) = (\<nu> y (subs' I xvec Tvec))"

| "(subs'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case) xvec Tvec) = \<bottom>\<^sub>c"
| "(subs'' (\<box>\<Phi> \<Rightarrow> P C) xvec Tvec) = (\<box>(subst_cond \<Phi> xvec Tvec) \<Rightarrow> (subs P xvec Tvec) (subs'' C xvec Tvec))"
apply(finite_guess add: subst_term.fs subst_assert.fs subst_cond.fs)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(simp add: abs_fresh)
apply(simp add: abs_fresh)
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
done

lemma subst_eqvt[eqvt]:
  fixes p    :: "name prm"
  and   P    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   Tvec :: "'a list"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  shows "(p \<bullet> (subs P xvec Tvec)) = subs (p \<bullet> P) (p \<bullet> xvec) (p \<bullet> Tvec)"
  and   "(p \<bullet> (subs' I xvec Tvec)) = subs' (p \<bullet> I) (p \<bullet> xvec) (p \<bullet> Tvec)"
  and   "(p \<bullet> (subs'' C xvec Tvec)) = subs'' (p \<bullet> C) (p \<bullet> xvec) (p \<bullet> Tvec)"
apply(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts)
apply(auto simp add: eqvts)
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply simp
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
by simp
(*
lemma subst1:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "x \<sharp> xvec"

  shows "x \<sharp> (subs P xvec Tvec) \<Longrightarrow> x \<sharp> P"
  and   "x \<sharp> (subs' I xvec Tvec) \<Longrightarrow> x \<sharp> I"
  and   "x \<sharp> (subs'' C xvec Tvec) \<Longrightarrow> x \<sharp> C"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.subst1 subst_cond.subst1 subst_assert.subst1 simp add: abs_fresh)

lemma subst1_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   Xs   :: "name set"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "Xs \<sharp>* xvec"

  shows "Xs \<sharp>* (subs P xvec Tvec) \<Longrightarrow> Xs \<sharp>* P"
  and   "Xs \<sharp>* (subs' I xvec Tvec) \<Longrightarrow> Xs \<sharp>* I"
  and   "Xs \<sharp>* (subs'' C xvec Tvec) \<Longrightarrow> Xs \<sharp>* C"
using assms
by(auto intro: subst1 simp add: fresh_star_def)
*)
lemma subst2[intro]:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "x \<sharp> Tvec"
  and     "x \<sharp> xvec"

  shows "x \<sharp> P \<Longrightarrow> x \<sharp> (subs P xvec Tvec)"
  and   "x \<sharp> I \<Longrightarrow> x \<sharp> (subs' I xvec Tvec)"
  and   "x \<sharp> C \<Longrightarrow> x \<sharp> (subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.subst2 subst_cond.subst2 subst_assert.subst2 simp add: abs_fresh)

lemma subst2_chain[intro]:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   Xs   :: "name set"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "Xs \<sharp>* xvec"
  and     "Xs \<sharp>* Tvec"

  shows "Xs \<sharp>* P \<Longrightarrow> Xs \<sharp>* (subs P xvec Tvec)"
  and   "Xs \<sharp>* I \<Longrightarrow> Xs \<sharp>* (subs' I xvec Tvec)"
  and   "Xs \<sharp>* C \<Longrightarrow> Xs \<sharp>* (subs'' C xvec Tvec)"
using assms
by(auto intro: subst2 simp add: fresh_star_def)
(*
lemma subst4:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a ,'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"

  shows "\<lbrakk>xvec \<sharp>* P\<rbrakk> \<Longrightarrow> (subs P xvec Tvec) = P"
  and   "\<lbrakk>xvec \<sharp>* I\<rbrakk> \<Longrightarrow> (subs' I xvec Tvec) = I"
  and   "\<lbrakk>xvec \<sharp>* C\<rbrakk> \<Longrightarrow> (subs'' C xvec Tvec) = C"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.subst4 subst_cond.subst4 subst_assert.subst4 simp add: psi.inject input.inject psi_case.inject)

lemma subst5:
  fixes xvec  :: "name list"
  and   Tvec  :: "'a list"
  and   yvec  :: "name list"
  and   Tvec' :: "'a list"
  and   P     :: "('a, 'b, 'c) psi"
  and   I     :: "('a ,'b, 'c) input"
  and   C     :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "length yvec = length Tvec'"
  and     "distinct yvec"
  and     "yvec \<sharp>* xvec"
  and     "yvec \<sharp>* Tvec"

  shows "(subs P (xvec@yvec) (Tvec@Tvec')) = subs (subs P xvec Tvec) yvec Tvec'"
  and   "(subs' I (xvec@yvec) (Tvec@Tvec')) = subs' (subs' I xvec Tvec) yvec Tvec'"
  and   "(subs'' C (xvec@yvec) (Tvec@Tvec')) = subs'' (subs'' C xvec Tvec) yvec Tvec'"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec yvec Tvec' rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.subst5 subst_cond.subst5 subst_assert.subst5 simp add: psi.inject input.inject psi_case.inject fresh_list_append)
*)
lemma renaming:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   p    :: "name prm"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a ,'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "distinct_perm p"

  shows "\<lbrakk>(p \<bullet> xvec) \<sharp>* P\<rbrakk> \<Longrightarrow> (subs P xvec Tvec) = subs (p \<bullet> P) (p \<bullet> xvec) Tvec"
  and   "\<lbrakk>(p \<bullet> xvec) \<sharp>* I\<rbrakk> \<Longrightarrow> (subs' I xvec Tvec) = subs' (p \<bullet> I) (p \<bullet> xvec) Tvec"
  and   "\<lbrakk>(p \<bullet> xvec) \<sharp>* C\<rbrakk> \<Longrightarrow> (subs'' C xvec Tvec) = subs'' (p \<bullet> C) (p \<bullet> xvec) Tvec"
using assms
by(nominal_induct P and I and C avoiding: xvec p Tvec rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.renaming subst_cond.renaming subst_assert.renaming simp add: fresh_chain_simps psi.inject input.inject psi_case.inject)

lemma subst4_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "xvec \<sharp>* Tvec"

  shows "xvec \<sharp>* (subs P xvec Tvec)"
  and   "xvec \<sharp>* (subs' I xvec Tvec)"
  and   "xvec \<sharp>* (subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts)
  (auto intro: subst_term.subst4_chain subst_cond.subst4_chain subst_assert.subst4_chain simp add: abs_fresh)
(*
lemma subst_empty[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"

  shows "(subs P [] []) = P"
  and   "(subs' I [] []) = I"
  and   "(subs'' C [] []) = C"
using assms
by(nominal_induct P and I and C rule: psi_input_psi_case.strong_inducts) auto
*)
lemma guarded_subst[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psi_case"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"

  shows "guarded P \<Longrightarrow> guarded(subs P xvec Tvec)"
  and   "guarded' I \<Longrightarrow> guarded'(subs' I xvec Tvec)"
  and   "guarded'' C \<Longrightarrow> guarded''(subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psi_case.strong_inducts) auto

definition seq_subs :: "('a, 'b, 'c) psi \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) psi" ("_[<_>]" [80, 80] 130)
  where "P[<\<sigma>>] \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs Q xvec Tvec) P \<sigma>"

definition seq_subs' :: "('a, 'b, 'c) input \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) input" 
  where "seq_subs' I \<sigma> \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs' Q xvec Tvec) I \<sigma>"

definition seq_subs'' :: "('a, 'b, 'c) psi_case \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) psi_case"
  where "seq_subs'' C \<sigma> \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs'' Q xvec Tvec) C \<sigma>"

lemma subst_input_chain[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a"
  and   P    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   Tvec :: "'a list"

  assumes "xvec \<sharp>* yvec"
  and     "xvec \<sharp>* Tvec"

  shows "subs' (input_chain xvec N P) yvec Tvec = input_chain xvec (subst_term N yvec Tvec) (subs P yvec Tvec)"
using assms
by(induct xvec) (auto simp add: psi.inject)

fun case_list_subst :: "('c \<times> ('a, 'b, 'c) psi) list \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('c \<times> ('a, 'b, 'c) psi) list"
where
  "case_list_subst [] _ _ = []"
| "case_list_subst ((\<phi>, P)#Cs) xvec Tvec = (subst_cond \<phi> xvec Tvec, (subs P xvec Tvec))#(case_list_subst Cs xvec Tvec)"

lemma subst_cases[simp]:
  fixes Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  shows "subs (Cases Cs) xvec Tvec = Cases(case_list_subst Cs xvec Tvec)"
by(induct Cs) (auto simp add: psi.inject)

lemma subst_cases'[simp]:
  fixes Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  shows "(subs'' (psi_cases Cs) xvec Tvec) = psi_cases(case_list_subst Cs xvec Tvec)"
by(induct Cs) auto

lemma seq_subst_simps[simp]:
  shows "seq_subs (\<zero>) \<sigma> = \<zero>"
  and   "(seq_subs (M\<langle>N\<rangle>.P) \<sigma>) = (subst_term.seq_subst M \<sigma>)\<langle>(subst_term.seq_subst N \<sigma>)\<rangle>.(seq_subs P \<sigma>)"
  and   "(seq_subs (M\<lparr>I) \<sigma>) = (subst_term.seq_subst M \<sigma>)\<lparr>(seq_subs' I \<sigma>)"

  and   "(seq_subs (Case C) \<sigma>) = (Case (seq_subs'' C \<sigma>))"
  and   "(seq_subs (P \<parallel> Q) \<sigma>) = (seq_subs P \<sigma>) \<parallel> (seq_subs Q \<sigma>)"
  and   "\<lbrakk>y \<sharp> \<sigma>\<rbrakk> \<Longrightarrow> (seq_subs (\<lparr>\<nu>y\<rparr>P) \<sigma>) = \<lparr>\<nu>y\<rparr>(seq_subs P \<sigma>)"
  and   "(seq_subs (\<lbrace>\<Psi>\<rbrace>) \<sigma>) = \<lbrace>(subst_assert.seq_subst \<Psi> \<sigma>)\<rbrace>"
  and   "(seq_subs (!P) \<sigma>) = !(seq_subs P \<sigma>)"
  
  and   "(seq_subs' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) \<sigma>) = (\<rparr>(subst_term.seq_subst M \<sigma>).(seq_subs P \<sigma>))"
  and   "\<lbrakk>y \<sharp> \<sigma>\<rbrakk> \<Longrightarrow> (seq_subs' (\<nu> y I) \<sigma>) = (\<nu> y (seq_subs' I \<sigma>))"
  
  and   "(seq_subs'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case) \<sigma>) = \<bottom>\<^sub>c"
  and   "(seq_subs'' (\<box>\<Phi> \<Rightarrow> P C) \<sigma>) = (\<box>(subst_cond.seq_subst \<Phi> \<sigma>) \<Rightarrow> (seq_subs P \<sigma>) (seq_subs'' C \<sigma>))"
by(induct \<sigma> arbitrary: M N P I C Q \<Psi> \<Phi>, auto simp add: seq_subs_def seq_subs'_def seq_subs''_def)

lemma seq_subs_nil[simp]:
  "seq_subs P [] = P"
by(simp add: seq_subs_def)

lemma seq_subs_cons[simp]:
  shows "seq_subs P ((xvec, Tvec)#\<sigma>) = seq_subs(subs P xvec Tvec) \<sigma>"
  by(simp add: seq_subs_def)

lemma seq_subs_term_append[simp]:
  shows "seq_subs P (\<sigma>@\<sigma>') = seq_subs (seq_subs P \<sigma>) \<sigma>'"
by(induct \<sigma>) (auto simp add: seq_subs_def)

fun case_list_seq_subst :: "('c \<times> ('a, 'b, 'c) psi) list \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('c \<times> ('a, 'b, 'c) psi) list"
where
  "case_list_seq_subst [] _ = []"
| "case_list_seq_subst ((\<phi>, P)#Cs) \<sigma> = (subst_cond.seq_subst \<phi> \<sigma>, (seq_subs P \<sigma>))#(case_list_seq_subst Cs \<sigma>)"

lemma seq_subst_cases[simp]:
  fixes Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<sigma>  :: "(name list \<times> 'a list) list"

  shows "seq_subs (Cases Cs) \<sigma> = Cases(case_list_seq_subst Cs \<sigma>)"
by(induct Cs) (auto simp add: psi.inject)

lemma seq_subst_cases'[simp]:
  fixes Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<sigma>  :: "(name list \<times> 'a list) list"

  shows "(seq_subs'' (psi_cases Cs) \<sigma>) = psi_cases(case_list_seq_subst Cs \<sigma>)"
by(induct Cs) auto

lemma seq_subst_eqvt[eqvt]:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"
  and   p :: "name prm"

  shows "(p \<bullet> (P[<\<sigma>>])) = (p \<bullet> P)[<(p \<bullet> \<sigma>)>]"
by(induct \<sigma> arbitrary: P) (auto simp add: eqvts seq_subs_def)

lemma guarded_seq_subst:
  assumes "guarded P"
  and     "well_formed_subst \<sigma>"

  shows "guarded(seq_subs P \<sigma>)"
using assms
by(induct \<sigma> arbitrary: P) (auto dest: guarded_subst)

end

lemma inter_eqvt:
  shows "(pi::name prm) \<bullet> ((X::name set) \<inter> Y) = (pi \<bullet> X) \<inter> (pi \<bullet> Y)"
by(auto simp add: perm_set_def perm_bij)

lemma delete_eqvt:
  fixes p :: "name prm"
  and   X :: "name set"
  and   Y :: "name set"

  shows "p \<bullet> (X - Y) = (p \<bullet> X) - (p \<bullet> Y)"
by(auto simp add: perm_set_def perm_bij)

lemma perm_singleton[simp]:
  shows "(p::name prm) \<bullet> {(x::name)} = {p \<bullet> x}"
by(auto simp add: perm_set_def)

end