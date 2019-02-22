theory Semantics
   imports Frame
begin

abbreviation provenance_judge ("\<langle>_; _, _\<rangle>" [80,80,80] 80)
  where "\<langle>xvec; yvec, \<pi>\<rangle> \<equiv> \<langle>xvec,\<langle>yvec,\<pi>\<rangle>\<rangle>"

abbreviation empty_provenance_judge ("\<langle>\<epsilon>; \<epsilon>, _\<rangle>" [80] 80)
where "\<langle>\<epsilon>; \<epsilon>, \<pi>\<rangle> \<equiv> F_assert(F_assert \<pi>)"

lemma tup_frame_eq_split:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: "'a::fs_name"
  and   C  :: "'b::fs_name"
  and   \<pi>  :: "('c::fs_name) frame"
  
  assumes "\<langle>A\<^sub>F, (\<Psi>\<^sub>F, \<pi>)\<rangle> = \<langle>A\<^sub>F', (\<Psi>\<^sub>F', \<pi>')\<rangle>"
  shows "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>"
  and "\<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>'\<rangle>"
proof -
  from assms  have "length A\<^sub>F = length A\<^sub>F'"
    by(rule frame_chain_eq_length)
  hence "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle> \<and> \<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>'\<rangle>" using assms
  proof(induct arbitrary: A\<^sub>F' \<Psi>\<^sub>F \<pi> \<Psi>\<^sub>F' \<pi>' rule: length_induct)
    case(1 A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F \<pi> \<Psi>\<^sub>F' \<pi>')
    have ind_hyp: "\<And> ys x (xa::'a) (xb::'c frame) (xc::'a) (xd::'c frame). \<lbrakk>length ys < length A\<^sub>F; length ys = length x; \<langle>ys, (xa, xb)\<rangle> = \<langle>x, (xc, xd)\<rangle>\<rbrakk> \<Longrightarrow> \<langle>ys, xa\<rangle> = \<langle>x, xc\<rangle> \<and> \<langle>ys,xb\<rangle> = \<langle>x,xd\<rangle>"
      using 1 by blast
    show ?case
    proof(cases A\<^sub>F)
      case Nil
      thus ?thesis using 1
        by(cases A\<^sub>F') (simp_all add: frame.inject)
    next
      case (Cons a as)
      then obtain b bs where b: "A\<^sub>F' = b # bs" using 1
        by (metis length_0_conv list.exhaust)
      have l: "length as < length A\<^sub>F" using Cons by simp
      have l': "length as = length([(a,b)]\<bullet>bs)"
        using `length A\<^sub>F = length A\<^sub>F'` unfolding Cons b by simp
      show ?thesis using `length A\<^sub>F = length A\<^sub>F'` `\<langle>A\<^sub>F, (\<Psi>\<^sub>F, \<pi>)\<rangle> = \<langle>A\<^sub>F', (\<Psi>\<^sub>F', \<pi>')\<rangle>`
        unfolding Cons b
        by(auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst] eqvts frame_res_chain_fresh dest: ind_hyp[OF l] ind_hyp[OF l, OF l'])
    qed
  qed
  thus "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>" and "\<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>'\<rangle>"
    by auto
qed

lemma distinct_frames_eq:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: "'a::fs_name"
  and   C  :: "'b::fs_name"
  and   \<pi>  :: "('c::fs_name) frame"
  
  assumes "A\<^sub>F \<sharp>* C"

  obtains A\<^sub>F' where  "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C" and "\<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>\<rangle>"
proof -
  assume a: "(\<And>A\<^sub>F'. \<lbrakk>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>; distinct A\<^sub>F'; A\<^sub>F' \<sharp>* C; \<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>\<rangle>\<rbrakk> \<Longrightarrow> thesis)"
  moreover from assms obtain A\<^sub>F' where F_eq: "\<langle>A\<^sub>F, (\<Psi>\<^sub>F,\<pi>)\<rangle> = \<langle>A\<^sub>F', (\<Psi>\<^sub>F,\<pi>)\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C"
    by(erule_tac distinct_frame)
  moreover hence "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle> \<and> \<langle>A\<^sub>F,\<pi>\<rangle> = \<langle>A\<^sub>F',\<pi>\<rangle>"
    by(metis tup_frame_eq_split)
  ultimately show thesis
    by blast
qed

nominal_datatype ('a, 'b, 'c) bound_output = 
  B_out "'a::fs_name" "('a, 'b::fs_name, 'c::fs_name) psi" ("_ \<prec>' _" [110, 110] 110)
| B_step "\<guillemotleft>name\<guillemotright> ('a, 'b, 'c) bound_output"                ("\<lparr>\<nu>_\<rparr>_" [110, 110] 110)

fun BO_res_chain :: "name list \<Rightarrow> ('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output \<Rightarrow> 
                      ('a, 'b, 'c) bound_output"
where
  BO_res_chain_base: "BO_res_chain [] B = B"
| BO_res_chain_step: "BO_res_chain (x#xs) B = \<lparr>\<nu>x\<rparr>(BO_res_chain xs B)"

abbreviation
  BO_res_chain_judge ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80) where "\<lparr>\<nu>*xvec\<rparr>B \<equiv> BO_res_chain xvec B"

lemma BO_res_chain_eqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>B) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> B)"
by(induct_tac xvec, auto)

lemma BO_res_chain_simps[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   N'   :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   B    :: "('a, 'b, 'c) bound_output"
  and   B'    :: "('a, 'b, 'c) bound_output"

  shows "(\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = N' \<prec>' P') = (xvec = [] \<and> N = N' \<and> P = P')"
  and   "(N' \<prec>' P' = \<lparr>\<nu>*xvec\<rparr>N \<prec>' P) = (xvec = [] \<and> N = N' \<and> P = P')"
  and   "(N' \<prec>' P' = N \<prec>' P) = (N = N' \<and> P = P')"
  and   "(\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*xvec\<rparr>B') = (B = B')"
by(induct xvec) (auto simp add: bound_output.inject alpha)

lemma output_fresh[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(Xs \<sharp>* (N \<prec>' P)) = ((Xs \<sharp>* N) \<and> (Xs \<sharp>* P))"
  and   "(xvec \<sharp>* (N \<prec>' P)) = ((xvec \<sharp>* N) \<and> (xvec \<sharp>* P))"
by(auto simp add: fresh_star_def)

lemma bound_output_fresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   B   :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"

  shows "(x \<sharp> (\<lparr>\<nu>*xvec\<rparr>B)) = (x \<in> set xvec \<or> x \<sharp> B)"
by (induct xvec) (simp_all add: abs_fresh)

lemma bound_output_fresh_set: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"
  and   x    :: name

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> B)"
  and   "yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = (\<forall>x\<in>(set yvec). x \<in> set xvec \<or> x \<sharp> B)"
  and   "Xs \<sharp>* (\<lparr>\<nu>x\<rparr>B) = Xs \<sharp>* [x].B"
  and   "xvec \<sharp>* (\<lparr>\<nu>x\<rparr>B) = xvec \<sharp>* [x].B"
by(simp add: fresh_star_def bound_output_fresh)+

lemma BO_res_chain_supp:
  fixes xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"

  shows "(supp(\<lparr>\<nu>*xvec\<rparr>B)::name set) = (supp B) - (supp xvec)" 
by(induct xvec)
  (auto simp add: bound_output.supp supp_list_nil supp_list_cons abs_supp supp_atm)

lemma bound_output_fresh_simps[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"
  and   x    :: name

  shows "Xs \<sharp>* xvec \<Longrightarrow> (Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B)) = (Xs \<sharp>* B)"
  and   "yvec \<sharp>* xvec \<Longrightarrow> yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = yvec \<sharp>* B"
  and   "xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B)"
  and   "x \<sharp> xvec \<Longrightarrow> x \<sharp> \<lparr>\<nu>*xvec\<rparr>B = x \<sharp> B"
apply(simp add: bound_output_fresh_set) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: bound_output_fresh_set) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: bound_output_fresh_set)  
by(simp add: BO_res_chain_supp fresh_def)

lemma bound_output_chain_alpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"

  assumes xvec_freshB: "(p \<bullet> xvec) \<sharp>* B"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "(set xvec) \<subseteq> (set yvec)"

  shows "(\<lparr>\<nu>*yvec\<rparr>B) = (\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(p \<bullet> B))"
proof -
  note pt_name_inst at_name_inst S
  moreover from `(set xvec) \<subseteq> (set yvec)` have "set xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>B)"
    by(force simp add: bound_output_fresh_set)
  moreover from xvec_freshB `(set xvec) \<subseteq> (set yvec)` have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*yvec\<rparr>B)"
    by (simp add: bound_output_fresh_set) (simp add: fresh_star_def)
  ultimately have "(\<lparr>\<nu>*yvec\<rparr>B) = p \<bullet> (\<lparr>\<nu>*yvec\<rparr>B)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma bound_output_chain_alpha':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes xvec_freshB: "xvec \<sharp>* B"
  and     S: "set p \<subseteq> set xvec \<times> set yvec"
  and     "yvec \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)"

  shows "(\<lparr>\<nu>*zvec\<rparr>B) = (\<lparr>\<nu>*(p \<bullet> zvec)\<rparr>(p \<bullet> B))"
proof -
  note pt_name_inst at_name_inst S `yvec \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)`
  moreover from xvec_freshB have "set (xvec) \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)"
    by (simp add: bound_output_fresh_set) (simp add: fresh_star_def)
  ultimately have "(\<lparr>\<nu>*zvec\<rparr>B) = p \<bullet> (\<lparr>\<nu>*zvec\<rparr>B)"
    by (rule_tac pt_freshs_freshs [symmetric]) auto
  then show ?thesis by(simp add: eqvts)
qed

lemma bound_output_chain_alpha'':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"

  assumes "(p \<bullet> xvec) \<sharp>* M"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and      "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "(set xvec) \<subseteq> (set yvec)"

  shows "(\<lparr>\<nu>*yvec\<rparr>M \<prec>' P) = (\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(p \<bullet> M) \<prec>' (p \<bullet> P))"
using assms
by(subst bound_output_chain_alpha) auto

lemma bound_output_chain_swap:
  fixes x    :: name
  and   y    :: name
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec :: "name list"

  assumes "y \<sharp> N"
  and     "y \<sharp> P"
  and     "x \<in> (set xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> xvec)\<rparr>([(x ,y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> P)"
proof(case_tac "x=y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with assms show ?thesis
    by(rule_tac xvec="[x]" in bound_output_chain_alpha'') (auto simp add: calc_atm)
qed

lemma alpha_bound_output:
  fixes x  :: name
  and   y  :: name
  and   B  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"

  assumes "y \<sharp> B"

  shows "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> B)"
using assms
by(auto simp add: bound_output.inject alpha fresh_left calc_atm)

lemma bound_output_eq_fresh:
  fixes B :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   C :: "('a, 'b, 'c) bound_output"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>C"
  and     "x \<sharp> B"
  
  shows "y \<sharp> C"
using assms
by(auto simp add: bound_output.inject alpha fresh_left calc_atm)  

lemma bound_output_eq_supp:
  fixes B :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   C :: "('a, 'b, 'c) bound_output"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>C"
  and     "x \<in> supp B"
  
  shows "y \<in> supp C"
using assms
apply(auto simp add: bound_output.inject alpha fresh_left calc_atm)
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts calc_atm)

lemma bound_output_chain_eq:
  fixes xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"
  and   B'   :: "('a, 'b, 'c) bound_output"

  assumes "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'"
  and     "xvec \<sharp>* yvec"
  and     "length xvec = length yvec"

  shows "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  B = p \<bullet> B' \<and> (set (map fst p)) \<subseteq> (supp B) \<and> xvec \<sharp>* B' \<and> yvec \<sharp>* B"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec B B')
    case(0 xvec yvec B B')
    have Eq: "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `length xvec = length yvec` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec B B')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'` `xvec = x # xvec'` `length xvec = length yvec`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>B = \<lparr>\<nu>*(y#yvec')\<rparr>B'"
      and "yvec = y#yvec'" and "length xvec' = length yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>B) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>B')"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    have IH: "\<And>xvec yvec B B'. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>(B::('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output) = \<lparr>\<nu>*yvec\<rparr>B'; xvec \<sharp>* yvec; length xvec = length yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  B = p \<bullet> B' \<and> set(map fst p) \<subseteq> supp B \<and> xvec \<sharp>* B' \<and> yvec \<sharp>* B"
      by fact
    from EQ `x \<noteq> y` have EQ': "\<lparr>\<nu>*xvec'\<rparr>B = ([(x, y)] \<bullet> (\<lparr>\<nu>*yvec'\<rparr>B'))" 
                     and x_fresh_B': "x \<sharp> (\<lparr>\<nu>*yvec'\<rparr>B')"
                     and y_freshB: "y \<sharp> (\<lparr>\<nu>*xvec'\<rparr>B)"
      by(metis bound_output.inject alpha)+
    from x_fresh_B' `x \<sharp> yvec'` have "x \<sharp> B'"
      by(auto simp add: bound_output_fresh) (simp add: fresh_def name_list_supp)+
    from y_freshB `y \<sharp> xvec'` have "y \<sharp> B"
      by(auto simp add: bound_output_fresh) (simp add: fresh_def name_list_supp)+
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B")
      assume x_freshB: "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B"
      with EQ have y_freshB': "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>B'"
	by(rule bound_output_eq_fresh)
      with x_fresh_B' EQ' have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>B'" 
	by(simp)
      with `xvec' \<sharp>* yvec'` `length xvec' = length yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "B = p \<bullet> B'"
                 and "set(map fst p) \<subseteq> supp B" and "xvec' \<sharp>* B'"  and "yvec' \<sharp>* B"
	by blast
      from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover note `xvec = x#xvec'` `yvec=y#yvec'` `distinct_perm p` `B = p \<bullet> B'`
                    `xvec' \<sharp>* B'` `x \<sharp> B'` `x \<sharp> B'` `yvec' \<sharp>* B` `y \<sharp> B` `set(map fst p) \<subseteq> supp B`

      ultimately show ?case by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B)"
      hence x_suppB: "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>B)"
	by(simp add: fresh_def)
      with EQ have y_supp_b': "y \<in> supp (\<lparr>\<nu>*yvec'\<rparr>B')"
	by(rule bound_output_eq_supp)
      hence "y \<sharp> yvec'"
	by(induct yvec') (auto simp add: bound_output.supp abs_supp)      
      with `x \<sharp> yvec'` EQ' have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')"
	by(simp add: eqvts)
      with  `xvec' \<sharp>* yvec'` `length xvec' = length yvec'` `length xvec' = n` IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "B = p \<bullet> [(x, y)] \<bullet> B'"
                 and "set(map fst p) \<subseteq> supp B" and "xvec' \<sharp>* ([(x, y)] \<bullet> B')" and "yvec' \<sharp>* B" 
	by blast

      from x_suppB have "x \<sharp> xvec'"
	by(induct xvec') (auto simp add: bound_output.supp abs_supp)      
      with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
	apply(induct p)
	by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
      from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
	by force
      moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinct_perm p`
      have "distinct_perm((x,y)#p)" by simp
      moreover from `B = p \<bullet> [(x, y)] \<bullet> B'` `x \<sharp> p` `y \<sharp> p` have "B = [(x, y)] \<bullet> p \<bullet> B'"
	by(subst perm_compose) simp
      hence "B = ((x, y)#p) \<bullet> B'" by simp
      moreover from `xvec' \<sharp>* ([(x, y)] \<bullet> B')` have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> B')"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> xvec'` `y \<sharp> xvec'` `x \<sharp> B'` have "(x#xvec') \<sharp>* B'" by simp
      moreover from `y \<sharp> B` `yvec' \<sharp>* B` have "(y#yvec') \<sharp>* B" by simp
      moreover from `set(map fst p) \<subseteq> supp B` x_suppB `x \<sharp> xvec'`
      have "set(map fst ((x, y)#p)) \<subseteq> supp B"
	by(simp add: BO_res_chain_supp)
      ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
	by metis
    qed
  qed
qed

lemma bound_output_chain_eq_length:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: "'a::fs_name"
  and   Q    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    from `0 = length xvec` have "xvec = []" by auto
    moreover with `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q` have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec M P N Q)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
      by simp
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q::('a, 'b, 'c) psi); n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P  = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(simp add: alpha bound_output.inject)
      with IH `length xvec' = n` have "length xvec' = length yvec'"
	by blast
      with `xvec = x#xvec'` `yvec=y#yvec'`
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(simp add: alpha bound_output.inject)
      hence "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
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

lemma bound_output_chain_eq':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "xvec \<sharp>* yvec"

  shows "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  M = p \<bullet> N \<and>  P = p \<bullet> Q \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> yvec \<sharp>* M \<and> yvec \<sharp>* P"
using assms
apply(frule_tac bound_output_chain_eq_length)
apply(drule_tac bound_output_chain_eq)
by(auto simp add: bound_output.inject)

lemma bound_output_chain_eq'':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinct_perm p" and "yvec = p \<bullet> xvec" and "N = p \<bullet> M" and "Q = p \<bullet> P" and "xvec \<sharp>* N" and "xvec \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* P"
proof -

  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinct_perm p; yvec = p \<bullet> xvec; N = p \<bullet> M; Q = p \<bullet> P; xvec \<sharp>* N; xvec \<sharp>* Q; (p \<bullet> xvec) \<sharp>* M; (p \<bullet> xvec) \<sharp>* P\<rbrakk> \<Longrightarrow> thesis"

  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> (p \<bullet> xvec) \<sharp>* M \<and> (p \<bullet> xvec) \<sharp>* P"
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M P N Q)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>(M::'a) \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> (p \<bullet> xvec) \<sharp>* M \<and> (p \<bullet> xvec) \<sharp>* P"
      by fact 
    from EQ `x \<noteq> y`  `x \<sharp> yvec'` `y \<sharp> yvec'` `y \<sharp> xvec'` `x \<sharp> xvec'` have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)" and "x \<sharp> N" and "x \<sharp> Q" and "y \<sharp> M" and "y \<sharp> P"
      apply -
      apply(simp add: bound_output.inject alpha eqvts)
      apply(simp add: bound_output.inject alpha eqvts)
      apply(simp add: bound_output.inject alpha eqvts)
      by(simp add: bound_output.inject alpha' eqvts)+
    with `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'` `length xvec' = n` IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "yvec' = p \<bullet> xvec'" and "([(x, y)] \<bullet> N) = p \<bullet> M" and "([(x, y)] \<bullet> Q) = p \<bullet> P" and "xvec' \<sharp>* ([(x, y)] \<bullet> N)" and "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" and "yvec' \<sharp>* M" and "yvec' \<sharp>* P"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from `x \<sharp> xvec'` `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S `distinct_perm p` `x \<noteq> y` have "distinct_perm((x, y)#p)" by auto
    moreover from `yvec' = p \<bullet> xvec'` `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: eqvts calc_atm perm_compose fresh_chain_simps)
    moreover from `([(x, y)] \<bullet> N) = p \<bullet> M`
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> M"
      by(simp add: pt_bij)
    hence "N = ((x, y)#p) \<bullet> M" by simp
    moreover from `([(x, y)] \<bullet> Q) = p \<bullet> P`
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> Q) = [(x, y)] \<bullet> p \<bullet> P"
      by(simp add: pt_bij)
    hence "Q = ((x, y)#p) \<bullet> P" by simp
    moreover from `xvec' \<sharp>* ([(x, y)] \<bullet> N)` have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> N)"
      by(subst fresh_star_bij)
    with `x \<sharp> xvec'` `y \<sharp> xvec'` have "xvec' \<sharp>* N" by simp
    with `x \<sharp> N` have "(x#xvec') \<sharp>* N" by simp
    moreover from `xvec' \<sharp>* ([(x, y)] \<bullet> Q)` have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> Q)"
      by(subst fresh_star_bij)
    with `x \<sharp> xvec'` `y \<sharp> xvec'` have "xvec' \<sharp>* Q" by simp
    with `x \<sharp> Q` have "(x#xvec') \<sharp>* Q" by simp
    moreover from `y \<sharp> M` `yvec' \<sharp>* M` have "(y#yvec') \<sharp>* M" by simp
    moreover from `y \<sharp> P` `yvec' \<sharp>* P` have "(y#yvec') \<sharp>* P" by simp
    ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
      by metis
  qed
  ultimately show ?thesis by blast
qed

lemma bound_output_eq_supp':
  fixes x    :: name
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   y    :: name
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>N \<prec>' Q)"
  and     "x \<noteq> y"
  and     "x \<sharp> yvec"
  and     "x \<sharp> xvec"
  and     "y \<sharp> xvec"
  and     "y \<sharp> yvec"
  and     "xvec \<sharp>* yvec"
  and     "x \<in> supp M"
  
  shows "y \<in> supp N"
proof -
  from Eq `x \<noteq> y` `x \<sharp> yvec` `y \<sharp> yvec` have "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(simp add: bound_output.inject alpha eqvts)
  then obtain p where S: "set p \<subseteq> set xvec \<times> set yvec" and "M = p \<bullet> [(x, y)] \<bullet> N" and "distinct_perm p" using `xvec \<sharp>* yvec`
    by(blast dest: bound_output_chain_eq')
  with `x \<in> supp M` have "x \<in> supp(p \<bullet> [(x, y)] \<bullet> N)" by simp
  hence "(p \<bullet> x) \<in> p \<bullet> supp(p \<bullet> [(x, y)] \<bullet> N)"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with `x \<sharp> xvec` `x \<sharp> yvec` S `distinct_perm p` have "x \<in> supp([(x, y)] \<bullet> N)"
    by(simp add: eqvts)
  hence "([(x, y)] \<bullet> x) \<in> ([(x, y)] \<bullet> (supp([(x, y)] \<bullet> N)))"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with `x \<noteq> y` show ?thesis by(simp add: calc_atm eqvts)
qed

lemma bound_output_chain_open_ih:
  fixes xvec :: "name list"
  and   x    :: name
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"
  and   yvec :: "name list"
  and   y    :: name
  and   B'   :: "('a, 'b, 'c) bound_output"

  assumes Eq: "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>B) = \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>B')"
  and     L: "length xvec = length yvec"
  and     x_fresh_B': "x \<sharp> B'"
  and     x_freshxvec: "x \<sharp> xvec"
  and     x_freshyvec: "x \<sharp> yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>([(x, y)] \<bullet> B')"
using assms
proof(induct n=="length xvec" arbitrary: xvec yvec y B' rule: nat.induct)
  case(zero xvec yvec y B')
  have "0 = length xvec" and "length xvec = length yvec" by fact+
  moreover have "\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec\<rparr>\<lparr>\<nu>y\<rparr>B'" by fact
  ultimately show ?case by(auto simp add: bound_output.inject alpha)
next
  case(Suc n xvec yvec y B')
  have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
  then obtain x' xvec' y' yvec' where x_eq: "xvec = x'#xvec'" and y_eq: "yvec = y'#yvec'"
                                  and L': "length xvec' = length yvec'"
    by(cases xvec, auto, cases yvec, auto)
  have x_fresh_B': "x \<sharp> B'" by fact
  have "x \<sharp> xvec" and "x \<sharp> yvec" by fact+
  with x_eq y_eq have xineqx': "x \<noteq> x'" and x_freshxvec': "x \<sharp> xvec'"
                and xineqy': "x \<noteq> y'" and x_freshyvec': "x \<sharp> yvec'"
    by simp+
  have "\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec\<rparr>\<lparr>\<nu>y\<rparr>B'" by fact
  with x_eq y_eq have Eq: "\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B')" by simp
  have IH: "\<And>xvec yvec y B'.
            \<lbrakk>n = length xvec; \<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec\<rparr>\<lparr>\<nu>y\<rparr>B'; length xvec = length yvec; x \<sharp> B'; x \<sharp> xvec; x \<sharp> yvec\<rbrakk>
            \<Longrightarrow> \<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>([(x, y)] \<bullet> B')" by fact
  have "Suc n = length xvec" by fact
  with x_eq have L'': "n = length xvec'" by simp
  have "\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*xvec'\<rparr>B) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B'))"
  proof(case_tac "x'=y'")
    assume x'eqy': "x' = y'"
    with Eq have "\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B'" by(simp add: bound_output.inject alpha)
    hence "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')" using L' x_fresh_B' x_freshxvec' x_freshyvec' L'' by(rule_tac IH)
    with x'eqy' show ?thesis by(simp add: bound_output.inject alpha)
  next
    assume x'ineqy': "x' \<noteq> y'"
    with Eq have Eq': "\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*([(x', y')] \<bullet> yvec')\<rparr>\<lparr>\<nu>([(x', y')] \<bullet> y)\<rparr>([(x', y')] \<bullet> B')"
             and x'_fresh_b': "x' \<sharp> \<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B'"
      by(simp add: bound_output.inject alpha eqvts)+
    from L' have "length xvec' = length ([(x', y')] \<bullet> yvec')" by simp
    moreover from xineqx' xineqy' x_fresh_B' have "x \<sharp> [(x', y')] \<bullet> B'" by(simp add: fresh_left calc_atm)
    moreover from xineqx' xineqy' x_freshyvec' have "x \<sharp> [(x', y')] \<bullet> yvec'" by(simp add: fresh_left calc_atm)
    ultimately have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*([(x', y')] \<bullet> yvec')\<rparr>([(x, ([(x', y')] \<bullet> y))] \<bullet> [(x', y')] \<bullet> B')" using Eq' x_freshxvec' L''
      by(rule_tac IH)
    moreover from x'_fresh_b' have "x' \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')"
    proof(case_tac "x' \<sharp> yvec'")
      assume "x' \<sharp> yvec'"
      with x'_fresh_b' have x'_fresh_b': "x' \<sharp> \<lparr>\<nu>y\<rparr>B'"
	by(simp add: fresh_def BO_res_chain_supp)
      show ?thesis
      proof(case_tac "x'=y")
	assume x'eqy: "x' = y"
	show ?thesis
	proof(case_tac "x=y")
	  assume "x=y"
	  with x_fresh_B' x'eqy show ?thesis by(simp add: BO_res_chain_supp fresh_def)
	next
	  assume "x \<noteq> y"
	  with `x \<sharp> B'` have "y \<sharp> [(x, y)] \<bullet> B'" by(simp add: fresh_left calc_atm)
	  with x'eqy show ?thesis by(simp add: BO_res_chain_supp fresh_def)
	qed
      next
	assume x'ineqy: "x' \<noteq> y"
	with x'_fresh_b' have "x' \<sharp> B'" by(simp add: abs_fresh)
	with xineqx' x'ineqy have "x' \<sharp> ([(x, y)] \<bullet> B')" by(simp add: fresh_left calc_atm)
	thus ?thesis by(simp add: BO_res_chain_supp fresh_def)
      qed
    next
      assume "\<not>x' \<sharp> yvec'"
      thus ?thesis by(simp add: BO_res_chain_supp fresh_def)
    qed
    ultimately show ?thesis using x'ineqy' xineqx' xineqy'
      apply(simp add: bound_output.inject alpha eqvts)
      apply(subst perm_compose[of "[(x', y')]"])
      by(simp add: calc_atm)
  qed
  with x_eq y_eq show ?case by simp
qed

lemma bound_output_par1_dest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* R"
  and     "yvec \<sharp>* R"

  obtains T where "P = T \<parallel> R" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>T. \<lbrakk>P = T \<parallel> R; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>T. P = T \<parallel> R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from `xvec \<sharp>* R` `yvec \<sharp>* R` `xvec = x#xvec'` `yvec = y#yvec'`
    have "x \<sharp> R" and "xvec' \<sharp>* R" and "y \<sharp> R" and "yvec' \<sharp>* R" by auto
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R); xvec \<sharp>* R; yvec \<sharp>* R; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>T. P = T \<parallel> R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(simp add: bound_output.inject alpha)
      with `xvec' \<sharp>* R` `yvec' \<sharp>* R` `length xvec' = n`
      obtain T where "P = T \<parallel> R" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(drule_tac IH) auto
      with `xvec=x#xvec'` `yvec=y#yvec'` `x=y` show ?case
	by(force simp add: bound_output.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ `x \<sharp> R` `y \<sharp> R`
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> R)"
       and x_fresh_QR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(simp add: bound_output.inject alpha eqvts)+
      moreover from `yvec' \<sharp>* R` have "([(x, y)] \<bullet> yvec') \<sharp>* ([(x, y)] \<bullet> R)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> R` `y \<sharp> R` have "([(x, y)] \<bullet> yvec') \<sharp>* R" by simp
      moreover note `xvec' \<sharp>* R` `length xvec' = n`
      ultimately obtain T where "P = T \<parallel> R" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
	by(drule_tac IH) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q))"
	by(simp add: bound_output.inject alpha)
      moreover from x_fresh_QR have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(force simp add: bound_output_fresh)
      ultimately show ?thesis using `P = T \<parallel> R` `xvec=x#xvec'` `yvec=y#yvec'` x_fresh_QR
	by(force simp add: alpha_bound_output name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma bound_output_par1_dest':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* yvec"

  obtains T p where "set p \<subseteq> set xvec \<times> set yvec" and "P = T \<parallel> (p \<bullet> R)" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>p T. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; P = T \<parallel> (p \<bullet> R); \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = T \<parallel> (p \<bullet> R) \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec` have "x \<noteq> y" and "x \<sharp> yvec'" and "y \<sharp> xvec'" and "xvec' \<sharp>* yvec'"
      by auto
    from Eq `x \<noteq> y` have Eq': "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
                     and x_fresh_QR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
      by(simp add: bound_output.inject alpha)+
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R);  xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = T \<parallel> (p \<bullet> R) \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
      by fact
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P")
      assume "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P"
      with Eq have y_fresh_qR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(rule bound_output_eq_fresh)
      with Eq' x_fresh_QR have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by simp
      with `xvec' \<sharp>* yvec'` `length xvec' = n`
      obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = T \<parallel> (p \<bullet> R)" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(drule_tac IH) auto
      from y_fresh_qR x_fresh_QR have y_freshQ: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" and x_freshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" 
	by(force simp add: BO_res_chain_supp fresh_def bound_output.supp psi.supp)+
      hence "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by (subst alpha_bound_output) simp+
      with A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by simp
      with `xvec=x#xvec'` `yvec=y#yvec'` S `P = T \<parallel> (p \<bullet> R)` show ?case
	by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)"
      hence "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)" by(simp add: fresh_def)
      with Eq have "y \<in> supp(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
	by(rule bound_output_eq_supp)
      hence "y \<sharp> yvec'" by(simp add: BO_res_chain_supp fresh_def)
      with Eq' `x \<sharp> yvec'` have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> ([(x, y)] \<bullet> R))"
	by(simp add: eqvts)
      moreover note `xvec' \<sharp>* yvec'` `length xvec' = n`
      ultimately obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = T \<parallel> (p \<bullet> [(x, y)] \<bullet> R)" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
	by(drule_tac IH) auto

      from S have "set(p@[(x, y)]) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover from `P = T \<parallel> (p \<bullet> [(x, y)] \<bullet> R)`  have "P = T \<parallel> ((p @ [(x, y)]) \<bullet> R)"
	by(simp add: pt2[OF pt_name_inst])
      moreover from x_fresh_QR have x_freshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" 
	by(force simp add: BO_res_chain_supp fresh_def bound_output.supp psi.supp)+
      with `x \<sharp> yvec'` `y \<sharp> yvec'` `x \<noteq> y` have "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
	by(simp add: fresh_left calc_atm)
      with `x \<sharp> yvec'` `y \<sharp> yvec'` have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
	by(subst alpha_bound_output) (assumption | simp add: eqvts)+
      with  A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by simp
      ultimately show ?thesis using `xvec=x#xvec'` `yvec=y#yvec'`
	by(rule_tac x="p@[(x, y)]" in exI) force
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma bound_output_par2_dest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* Q"
  and     "yvec \<sharp>* Q"

  obtains T where "P = Q \<parallel> T" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
proof -
  assume "\<And>T. \<lbrakk>P = Q \<parallel> T; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>T. P = Q \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from `xvec \<sharp>* Q` `yvec \<sharp>* Q` `xvec = x#xvec'` `yvec = y#yvec'`
    have "x \<sharp> Q" and "xvec' \<sharp>* Q" and "y \<sharp> Q" and "yvec' \<sharp>* Q" by auto
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R); xvec \<sharp>* Q; yvec \<sharp>* Q; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>T. P = Q \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(simp add: bound_output.inject alpha)
      with `xvec' \<sharp>* Q` `yvec' \<sharp>* Q` `length xvec' = n`
      obtain T where "P = Q \<parallel> T" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
	by(drule_tac IH) auto
      with `xvec=x#xvec'` `yvec=y#yvec'` `x=y` show ?case
	by(force simp add: bound_output.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ `x \<sharp> Q` `y \<sharp> Q`
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' (Q \<parallel> ([(x, y)] \<bullet> R))"
       and x_fresh_QR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(simp add: bound_output.inject alpha eqvts)+
      moreover from `yvec' \<sharp>* Q` have "([(x, y)] \<bullet> yvec') \<sharp>* ([(x, y)] \<bullet> Q)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> Q` `y \<sharp> Q` have "([(x, y)] \<bullet> yvec') \<sharp>* Q" by simp
      moreover note `xvec' \<sharp>* Q` `length xvec' = n`
      ultimately obtain T where "P = Q \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
	by(drule_tac IH) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R))"
	by(simp add: bound_output.inject alpha)
      moreover from x_fresh_QR have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
	by(force simp add: bound_output_fresh)
      ultimately show ?thesis using `P = Q \<parallel> T` `xvec=x#xvec'` `yvec=y#yvec'` x_fresh_QR
	by(force simp add: alpha_bound_output name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma bound_output_par2_dest':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* yvec"

  obtains T p where "set p \<subseteq> set xvec \<times> set yvec" and "P = (p \<bullet> Q) \<parallel> T" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
proof -
  assume "\<And>p T. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; P = (p \<bullet> Q) \<parallel> T; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = (p \<bullet> Q) \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec` have "x \<noteq> y" and "x \<sharp> yvec'" and "y \<sharp> xvec'" and "xvec' \<sharp>* yvec'"
      by auto
    from Eq `x \<noteq> y` have Eq': "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
                     and x_fresh_QR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
      by(simp add: bound_output.inject alpha)+
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R);  xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = (p \<bullet> Q) \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
      by fact
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P")
      assume "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P"
      with Eq have y_fresh_qR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by(rule bound_output_eq_fresh)
      with Eq' x_fresh_QR have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
	by simp
      with `xvec' \<sharp>* yvec'` `length xvec' = n`
      obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = (p \<bullet> Q) \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
	by(drule_tac IH) auto
      from y_fresh_qR x_fresh_QR have y_freshR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" and x_freshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" 
	by(force simp add: BO_res_chain_supp fresh_def bound_output.supp psi.supp)+
      hence "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by (subst alpha_bound_output) simp+
      with A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by simp
      with `xvec=x#xvec'` `yvec=y#yvec'` S `P = (p \<bullet> Q) \<parallel> T` show ?case
	by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)"
      hence "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)" by(simp add: fresh_def)
      with Eq have "y \<in> supp(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
	by(rule bound_output_eq_supp)
      hence "y \<sharp> yvec'" by(simp add: BO_res_chain_supp fresh_def)
      with Eq' `x \<sharp> yvec'` have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> ([(x, y)] \<bullet> R))"
	by(simp add: eqvts)
      moreover note `xvec' \<sharp>* yvec'` `length xvec' = n`
      ultimately obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = (p \<bullet> [(x, y)] \<bullet> Q) \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
	by(drule_tac IH) auto

      from S have "set(p@[(x, y)]) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover from `P = (p \<bullet> [(x, y)] \<bullet> Q) \<parallel> T`  have "P = ((p @ [(x, y)]) \<bullet> Q) \<parallel> T"
	by(simp add: pt2[OF pt_name_inst])
      moreover from x_fresh_QR have x_freshR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" 
	by(force simp add: BO_res_chain_supp fresh_def bound_output.supp psi.supp)+
      with `x \<sharp> yvec'` `y \<sharp> yvec'` `x \<noteq> y` have "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
	by(simp add: fresh_left calc_atm)
      with `x \<sharp> yvec'` `y \<sharp> yvec'` have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)"
	by(subst alpha_bound_output) (assumption | simp add: eqvts)+
      with  A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by simp
      ultimately show ?thesis using `xvec=x#xvec'` `yvec=y#yvec'`
	by(rule_tac x="p@[(x, y)]" in exI) force
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma bound_output_app:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) bound_output"

  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>B = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>B)"
by(induct xvec) auto
  
lemma open_inject_aux_aux_aux:
  fixes x    :: name
  and   xvec :: "name list"

  shows "\<exists>y yvec. x # xvec = yvec @ [y] \<and> length xvec = length yvec"
apply(induct xvec arbitrary: x)
apply auto
apply(subgoal_tac "\<exists>y yvec. a # xvec = yvec @ [y] \<and> length xvec = length yvec")
apply(clarify)
apply(rule_tac x=y in exI)
by auto

lemma open_inject_aux_aux:
  fixes xvec1 :: "name list"
  and   xvec2 :: "name list"
  and   yvec  :: "name list"

  assumes "length(xvec1@xvec2) = length yvec"

  shows "\<exists>yvec1 yvec2. yvec = yvec1@yvec2 \<and> length xvec1 = length yvec1 \<and> length xvec2 = length yvec2"
using assms
apply(induct yvec arbitrary: xvec1)
apply simp
apply simp
apply(case_tac xvec1)
apply simp
apply simp
apply(subgoal_tac "\<exists>yvec1 yvec2.
                   yvec = yvec1 @ yvec2 \<and> length list = length yvec1 \<and> length xvec2 = length yvec2")
apply(clarify)
apply(rule_tac x="a#yvec1" in exI)
apply(rule_tac x=yvec2 in exI)
by auto

lemma open_inject_aux:
  fixes xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   yvec  :: "name list"

  assumes "length(xvec1@x#xvec2) = length yvec"

  shows "\<exists>yvec1 y yvec2. yvec = yvec1@y#yvec2 \<and> length xvec1 = length yvec1 \<and> length xvec2 = length yvec2"
using assms
proof(induct xvec1 arbitrary: yvec)
  case Nil thus ?case
    by(cases yvec) auto
next
  case(Cons x xvec yvec)
  note Conso = this
  thus ?case
  proof(cases yvec)
    case Nil thus ?thesis using Cons 
      by simp
  next
    case(Cons y yvec')
    then obtain yvec1 y' yvec2 where "yvec' = yvec1 @ y' # yvec2"
      and "length xvec = length yvec1" and "length xvec2 = length yvec2"
      using Conso by force
    thus ?thesis
      by(rule_tac exI[where x="y#yvec1"]) (auto simp add: Cons)
  qed
qed

lemma bound_output_open_dest:
  fixes yvec  :: "name list"
  and   M     :: "'a::fs_name"
  and   P     :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   N     :: 'a
  and   Q     :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "x \<sharp> xvec1"
  and     "x \<sharp> yvec"
  and     "x \<sharp> N"
  and     "x \<sharp> Q"
  and     "distinct yvec"
  

  obtains yvec1 y yvec2 where "yvec=yvec1@y#yvec2" and "length xvec1 = length yvec1" and "length xvec2 = length yvec2" 
                          and "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
proof -
  assume Ass: "\<And>yvec1 y yvec2.
        \<lbrakk>yvec = yvec1 @ y # yvec2; length xvec1 = length yvec1; length xvec2 = length yvec2;
         \<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)\<rbrakk>
        \<Longrightarrow> thesis"
  from Eq have "length(xvec1@x#xvec2) = length yvec" by(rule bound_output_chain_eq_length)
  then obtain yvec1 y yvec2 where A: "yvec = yvec1@y#yvec2" and "length xvec1 = length yvec1"
          and "length xvec2 = length yvec2"
    by(metis open_inject_aux sym)

  from `distinct yvec` A have "y \<sharp> yvec2" by simp
  from A `x \<sharp> yvec` have "x \<sharp> yvec2" and "x \<sharp> yvec1"  by simp+
  with Eq `length xvec1 = length yvec1` `x \<sharp> N` `x \<sharp> Q` `y \<sharp> yvec2` `x \<sharp> xvec1` A
  have "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(force dest: bound_output_chain_open_ih simp add: bound_output_app BO_res_chain_supp fresh_def bound_output.supp eqvts)
  with `length xvec1 = length yvec1` `length xvec2 = length yvec2` A Ass show ?thesis
    by blast
qed

lemma bound_output_open_dest':
  fixes yvec  :: "name list"
  and   M     :: "'a::fs_name"
  and   P     :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   N     :: 'a
  and   Q     :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "x \<sharp> xvec1"
  and     "x \<sharp> yvec"
  and     "x \<sharp> N"
  and     "x \<sharp> Q"
  

  obtains yvec1 y yvec2 where "yvec=yvec1@y#yvec2" and "length xvec1 = length yvec1" and "length xvec2 = length yvec2" 
                          and "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@[(x, y)] \<bullet> yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
proof -
  assume Ass: "\<And>yvec1 y yvec2.
        \<lbrakk>yvec = yvec1 @ y # yvec2; length xvec1 = length yvec1; length xvec2 = length yvec2;
         \<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1 @ ([(x, y)] \<bullet> yvec2))\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)\<rbrakk>
        \<Longrightarrow> thesis"
  from Eq have "length(xvec1@x#xvec2) = length yvec" by(rule bound_output_chain_eq_length)
  then obtain yvec1 y yvec2 where A: "yvec = yvec1@y#yvec2" and "length xvec1 = length yvec1"
          and "length xvec2 = length yvec2"
    by(metis open_inject_aux sym)

  from A `x \<sharp> yvec` have "x \<sharp> yvec2" and "x \<sharp> yvec1"  by simp+
  with Eq `length xvec1 = length yvec1` `x \<sharp> N` `x \<sharp> Q` `x \<sharp> xvec1` A
  have "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@([(x, y)] \<bullet> yvec2))\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(force dest: bound_output_chain_open_ih simp add: bound_output_app BO_res_chain_supp fresh_def bound_output.supp eqvts)
  with `length xvec1 = length yvec1` `length xvec2 = length yvec2` A Ass show ?thesis
    by blast
qed

lemma bound_output_scope_dest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   x    :: name
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
  and     "z \<sharp> xvec"
  and     "z \<sharp> yvec"

  obtains R where "P = \<lparr>\<nu>z\<rparr>R" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>R. \<lbrakk>P = \<lparr>\<nu>z\<rparr>R; \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>R. P = \<lparr>\<nu>z\<rparr>R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q z)
    case(0 xvec yvec M N P Q z)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: bound_output.inject)
  next
    case(Suc n xvec yvec M N P Q z)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (\<lparr>\<nu>z\<rparr>Q)` `xvec = x # xvec'`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q)"
      by simp
    from `z \<sharp> xvec` `z \<sharp> yvec` `xvec = x#xvec'` `yvec = y#yvec'`
    have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> xvec'" and "z \<sharp> yvec'"
      by simp+
    have IH: "\<And>xvec yvec M N P Q z. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q; z \<sharp> xvec; z \<sharp> yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>R. P = \<lparr>\<nu>z\<rparr>R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
	by(simp add: bound_output.inject alpha)
      with `z \<sharp> xvec'` `z \<sharp> yvec'` `length xvec' = n`
      obtain R where "P = \<lparr>\<nu>z\<rparr>R" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(drule_tac IH) auto
      with `xvec=x#xvec'` `yvec=y#yvec'` `x=y` show ?case
	by(force simp add: bound_output.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ `z \<noteq> x` `z \<noteq> y`
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' \<lparr>\<nu>z\<rparr>([(x, y)] \<bullet> Q)"
       and x_freshzQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
	by(simp add: bound_output.inject alpha eqvts)+
      moreover from `z \<noteq> x` `z \<noteq> y` `z \<sharp> yvec'` `x \<noteq> y` have "z \<sharp> ([(x, y)] \<bullet> yvec')"
	by(simp add: fresh_left calc_atm)
      moreover note `z \<sharp> xvec'` `length xvec' = n`
      ultimately obtain R where "P = \<lparr>\<nu>z\<rparr>R" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
	by(drule_tac IH) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q))"
	by(simp add: bound_output.inject alpha)
      moreover from x_freshzQ `z \<noteq> x` have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
	by(simp add: bound_output_fresh abs_fresh)
      ultimately show ?thesis using `P = \<lparr>\<nu>z\<rparr>R` `xvec=x#xvec'` `yvec=y#yvec'` x_freshzQ
	by(force simp add: alpha_bound_output name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

nominal_datatype ('a, 'b, 'c) residual = 
  R_in "'a::fs_name" 'a "('a, 'b::fs_name, 'c::fs_name) psi" 
| R_out 'a "('a, 'b, 'c) bound_output"
| R_tau "('a, 'b, 'c) psi"

nominal_datatype 'a action = In "'a::fs_name" 'a      ("_\<lparr>_\<rparr>" [90, 90] 90)
                   | Out "'a::fs_name" "name list" 'a ("_\<lparr>\<nu>*_\<rparr>\<langle>_\<rangle>" [90, 90, 90] 90)
                   | Tau                              ("\<tau>" 90)

nominal_primrec bn :: "('a::fs_name) action \<Rightarrow> name list"
  where
  "bn (M\<lparr>N\<rparr>) = []"
| "bn (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec"
| "bn (\<tau>) = []"
by(rule TrueI)+

lemma bn_eqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> bn \<alpha>) = bn(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

nominal_primrec create_residual :: "('a::fs_name) action \<Rightarrow> ('a, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) residual" ("_ \<prec> _" [80, 80] 80)
where 
  "(M\<lparr>N\<rparr>) \<prec> P = R_in M N P"
| "M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P = R_out M (\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
| "\<tau> \<prec> P = (R_tau P)"
by(rule TrueI)+

nominal_primrec subject :: "('a::fs_name) action \<Rightarrow> 'a option" 
  where 
  "subject (M\<lparr>N\<rparr>) = Some M"
| "subject (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M"
| "subject (\<tau>) = None"
by(rule TrueI)+

nominal_primrec object :: "('a::fs_name) action \<Rightarrow> 'a option" 
  where 
  "object (M\<lparr>N\<rparr>) = Some N"
| "object (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N"
| "object (\<tau>) = None"
by(rule TrueI)+

lemma option_fresh_chain[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"

  shows "xvec \<sharp>* (Some x) = xvec \<sharp>* x"
  and   "X \<sharp>* (Some x) = X \<sharp>* x"
  and   "xvec \<sharp>* None"
  and   "X \<sharp>* None"
by(auto simp add: fresh_star_def fresh_some fresh_none)

lemmas [simp] = fresh_some fresh_none
  
lemma action_fresh[simp]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"

  shows "(x \<sharp> \<alpha>)  = (x \<sharp> (subject \<alpha>) \<and> x \<sharp> (bn \<alpha>) \<and> x \<sharp> (object \<alpha>))"
by(nominal_induct \<alpha> rule: action.strong_induct) auto
  
lemma action_fresh_chain[simp]:
  fixes X    :: "name set"
  and   \<alpha>    :: "('a::fs_name) action"
  and   xvec :: "name list"

  shows "(X \<sharp>* \<alpha>) = (X \<sharp>* (subject \<alpha>) \<and> X \<sharp>* (bn \<alpha>) \<and> X \<sharp>* (object \<alpha>))"
  and   "(xvec \<sharp>* \<alpha>) = (xvec \<sharp>* (subject \<alpha>) \<and> xvec \<sharp>* (bn \<alpha>) \<and> xvec \<sharp>* (object \<alpha>))"
by(auto simp add: fresh_star_def)

lemma subject_eqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> subject \<alpha>) = subject(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma okject_eqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> object \<alpha>) = object(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma create_residual_eqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(p \<bullet> (\<alpha> \<prec> P)) = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P)"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: eqvts)

lemma residual_fresh:
  fixes x :: name
  and   \<alpha> :: "'a::fs_name action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(x \<sharp> (\<alpha> \<prec> P)) = (x \<sharp> (subject \<alpha>) \<and> (x \<in> (set(bn(\<alpha>))) \<or> (x \<sharp> object(\<alpha>) \<and> x \<sharp> P)))"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: fresh_some fresh_none bound_output_fresh)

lemma residual_fresh2[simp]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "x \<sharp> \<alpha>"
  and     "x \<sharp> P"

  shows "x \<sharp> \<alpha> \<prec> P"
using assms
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma outres_eq:
  fixes M
  and   Bo
  and   C::"'d::fs_name"
  obtains xvec T P' where "R_out M Bo = M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle> \<prec> P'" and "xvec \<sharp>* M" and "xvec \<sharp>* C"
proof -
  assume R: "(\<And>xvec T P'. \<lbrakk>R_out M Bo = M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle> \<prec> P'; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> thesis)"
  have "\<exists> xvec T P'. R_out M Bo = M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle> \<prec> P' \<and> xvec \<sharp>* M \<and> xvec \<sharp>* C"
  proof(nominal_induct avoiding: M C rule: bound_output.strong_inducts)
    case(B_out T P')
    thus ?case
      apply(rule exI[where x="[]"])
      apply(rule exI[where x="T"])
      apply(rule exI[where x="P'"])
      by(simp add: bound_output.inject create_residual.simps)
  next
    case(B_step x Bo)
    then obtain xvec T P' where "R_out M Bo = M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle> \<prec> P'" and "xvec \<sharp>* M" and "xvec \<sharp>* C" by blast
    thus ?case using `x \<sharp> M` `x \<sharp> C`
      apply(rule_tac exI[where x="x#xvec"])
      apply(rule_tac exI[where x="T"])
      apply(rule_tac exI[where x="P'"])
      by(simp add: create_residual.simps Semantics.residual.inject bound_output.inject)
  qed
  thus thesis using R
    by blast
qed

lemma res_eq:
  fixes R
  and   C::"'d::fs_name"
  obtains \<alpha> P' where "R = \<alpha> \<prec> P'" and "bn \<alpha> \<sharp>* subject \<alpha>" and "bn \<alpha> \<sharp>* C"
proof -
  assume "(\<And>\<alpha> P'. \<lbrakk>R = \<alpha> \<prec> P'; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow> thesis)"
  moreover have "\<exists> \<alpha> P'. R = \<alpha> \<prec> P' \<and> bn \<alpha> \<sharp>* subject \<alpha> \<and> bn \<alpha> \<sharp>* C"
  proof(nominal_induct R rule: residual.strong_inducts)
    case(R_in M N P)
    thus ?case
      apply(rule_tac exI[where x="M\<lparr>N\<rparr>"])
      apply(rule_tac exI[where x="P"])
      by simp
  next
    case(R_out M Bo)
    obtain xvec T P' where "R_out M Bo = M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle> \<prec> P'" and "xvec \<sharp>* M" and "xvec \<sharp>* C"
      by(rule outres_eq)
    thus ?case
      apply(rule_tac exI[where x="M\<lparr>\<nu>*xvec\<rparr>\<langle>T\<rangle>"])
      apply(rule_tac exI[where x="P'"])
      by simp
  next
    case(R_tau P)
    thus ?case
      apply(rule_tac exI[where x="\<tau>"])
      apply(rule_tac exI[where x="P"])
      by simp
  qed
  ultimately show thesis
    by blast
qed

lemma residual_fresh_chain2[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "\<lbrakk>xvec \<sharp>* \<alpha>; xvec \<sharp>* P\<rbrakk> \<Longrightarrow> xvec \<sharp>* (\<alpha> \<prec> P)"
  and   "\<lbrakk>X \<sharp>* \<alpha>; X \<sharp>* P\<rbrakk> \<Longrightarrow> X \<sharp>* (\<alpha> \<prec> P)"
by(auto simp add: fresh_star_def)

lemma residual_fresh_simp[simp]:
  fixes x :: name
  and   M :: "'a::fs_name"
  and   N :: 'a
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  

  shows "x \<sharp> (M\<lparr>N\<rparr> \<prec> P) = (x \<sharp> M \<and> x \<sharp> N \<and> x \<sharp> P)"
  and   "x \<sharp> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P) = (x \<sharp> M \<and> x \<sharp> (\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P)))"
  and   "x \<sharp> (\<tau> \<prec> P) = (x \<sharp> P)"
by(auto simp add: residual_fresh)

lemma residual_inject':

  shows "(\<alpha> \<prec> P = R_in M N Q) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
  and   "(\<alpha> \<prec> P = R_out M B) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
  and   "(\<alpha> \<prec> P = R_tau Q) = (\<alpha> = \<tau> \<and> P = Q)"
  and   "(R_in M N Q = \<alpha> \<prec> P) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
  and   "(R_out M B = \<alpha> \<prec> P) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
  and   "(R_tau Q = \<alpha> \<prec> P) = (\<alpha> = \<tau> \<and> P = Q)"
proof -
  show "(\<alpha> \<prec> P = R_in M N Q) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(\<alpha> \<prec> P = R_out M B) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show  "(\<alpha> \<prec> P = R_tau Q) = (\<alpha> = \<tau> \<and> P = Q)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(R_in M N Q = \<alpha> \<prec> P) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(R_out M B = \<alpha> \<prec> P) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show  "(R_tau Q = \<alpha> \<prec> P) = (\<alpha> = \<tau> \<and> P = Q)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
qed

lemma residual_fresh_chain_simp[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   M    :: "'a::fs_name"
  and   N    :: 'a
  and   yvec :: "name list"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (M\<lparr>N\<rparr> \<prec> P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P) = (xvec \<sharp>* M \<and> xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>(N \<prec>' P)))"
  and   "xvec \<sharp>* (\<tau> \<prec> P) = (xvec \<sharp>* P)"
  and   "X \<sharp>* (M\<lparr>N\<rparr> \<prec> P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P) = (X \<sharp>* M \<and> X \<sharp>* (\<lparr>\<nu>*yvec\<rparr>(N \<prec>' P)))"
  and   "X \<sharp>* (\<tau> \<prec> P) = (X \<sharp>* P)"
by(auto simp add: fresh_star_def)

lemma residual_fresh_chain_simp2[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   M    :: "'a::fs_name"
  and   N    :: 'a
  and   yvec :: "name list"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (R_in M N P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* (R_out M B) = (xvec \<sharp>* M \<and> xvec \<sharp>* B)"
  and   "xvec \<sharp>* (R_tau P) = (xvec \<sharp>* P)"
  and   "X \<sharp>* (R_in M N P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* (R_out M B) = (X \<sharp>* M \<and> X \<sharp>* B)"
  and   "X \<sharp>* (R_tau P) = (X \<sharp>* P)"
by(auto simp add: fresh_star_def)

lemma fresh_residual3[dest]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "x \<sharp> bn \<alpha>"
  and     "x \<sharp> \<alpha> \<prec> P"

  shows "x \<sharp> \<alpha>" and "x \<sharp> P"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma fresh_residual_chain3[dest]:
  fixes xvec :: "name list"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "xvec \<sharp>* (\<alpha> \<prec> P)"
  and     "xvec \<sharp>* bn \<alpha>"

  shows "xvec \<sharp>* \<alpha>" and "xvec \<sharp>* P"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma fresh_residual4[dest]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "x \<sharp> \<alpha> \<prec> P"

  shows "x \<sharp> subject \<alpha>"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma fresh_residual_chain4[dest]:
  fixes xvec :: "name list"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "xvec \<sharp>* (\<alpha> \<prec> P)"

  shows "xvec \<sharp>* subject \<alpha>"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma alpha_output_residual:
  fixes M    :: "'a::fs_name"
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   p    :: "name prm"

  assumes "(p \<bullet> xvec) \<sharp>* N"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and     "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "set xvec \<subseteq> set yvec"

  shows "M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P = M\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P)"
using assms
by(simp add: bound_output_chain_alpha'')

lemmas[simp del] =  create_residual.simps

lemma residual_inject'':

  assumes "bn \<alpha> = bn \<beta>"

  shows "(\<alpha> \<prec> P = \<beta> \<prec> Q) = (\<alpha> = \<beta> \<and> P = Q)"
using assms
apply(nominal_induct \<alpha> rule: action.strong_induct)
apply(auto simp add: residual.inject create_residual.simps residual_inject' action.inject bound_output.inject)
by(rule_tac x="bn \<beta>" in exI) auto

lemmas residual_inject = residual.inject create_residual.simps residual_inject' residual_inject''

lemma bn_fresh_residual[simp]:
  fixes \<alpha> :: "('a::fs_name) action"

  shows "(bn \<alpha>) \<sharp>* (\<alpha> \<prec> P) = bn \<alpha> \<sharp>* (subject \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: residual_fresh fresh_some fresh_star_def)

lemma action_cases[case_names c_input c_output c_tau]:
  fixes \<alpha> :: "('a::fs_name) action"

  assumes "\<And>M N. \<alpha> = M\<lparr>N\<rparr> \<Longrightarrow> Prop"
  and     "\<And>M xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<Longrightarrow> Prop"
  and     "\<alpha> = \<tau> \<Longrightarrow> Prop"

  shows Prop
using assms
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma action_par1_dest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"

  obtains T p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn \<beta>)" and "P = T \<parallel> (p \<bullet> R)" and "\<alpha> \<prec> T = \<beta> \<prec> Q"
using assms
apply(cases rule: action_cases[where \<alpha>=\<alpha>])
apply(auto simp add: residual_inject)
by(drule_tac bound_output_par1_dest') auto

lemma action_par2_dest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"

  obtains T p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn \<beta>)" and "P = (p \<bullet> Q) \<parallel> T" and "\<alpha> \<prec> T = \<beta> \<prec> R"
using assms
apply(cases rule: action_cases[where \<alpha>=\<alpha>])
apply(auto simp add: residual_inject)
by(drule_tac bound_output_par2_dest') auto

lemma action_scope_dest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  fixes \<beta> :: "('a::fs_name) action"
  and   x :: name
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> \<lparr>\<nu>x\<rparr>Q"
  and     "x \<sharp> bn \<alpha>"
  and     "x \<sharp> bn \<beta>"

  obtains R where "P = \<lparr>\<nu>x\<rparr>R" and "\<alpha> \<prec> R = \<beta> \<prec> Q"
using assms
apply(cases rule: action_cases[where \<alpha>=\<alpha>])
apply(auto simp add: residual_inject)
by(drule_tac bound_output_scope_dest) auto

abbreviation
  output_judge ("_\<langle>_\<rangle>" [110, 110] 110) where "M\<langle>N\<rangle> \<equiv> M\<lparr>\<nu>*([])\<rparr>\<langle>N\<rangle>"

declare [[unify_trace_bound=100]]

locale env = subst_psi subst_term subst_assert subst_cond + 
             assertion S_compose' S_imp' S_bottom' S_chan_eq'
  for subst_term :: "('a::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'a"
  and subst_assert :: "('b::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'b"
  and subst_cond :: "('c::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'c"
  and S_compose'  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and S_imp'      :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  and S_bottom'   :: 'b
  and S_chan_eq'   :: "'a \<Rightarrow> 'a \<Rightarrow> 'c"
begin
notation S_compose' (infixr "\<otimes>" 90)
notation S_imp' ("_ \<turnstile> _" [85, 85] 85)
notation Frame_imp ("_ \<turnstile>\<^sub>F _" [85, 85] 85) 
abbreviation
  F_bottom_judge ("\<bottom>\<^sub>F" 90) where "\<bottom>\<^sub>F \<equiv> (F_assert S_bottom')"
notation S_chan_eq' ("_ \<leftrightarrow> _" [90, 90] 90)
notation subst_term ("_[_::=_]" [100, 100, 100] 100)
notation subs ("_[_::=_]" [100, 100, 100] 100)
notation Assertion_stat_eq ("_ \<simeq> _" [80, 80] 80)
notation Frame_stat_eq ("_ \<simeq>\<^sub>F _" [80, 80] 80)
notation S_bottom' ("\<one>" 190)
abbreviation insert_assertion' ("insert_assertion") where "insert_assertion' \<equiv> assertion_aux.insert_assertion (\<otimes>)"

nominal_primrec push_prov :: "'a frame frame \<Rightarrow> 'a frame"
  where
  "push_prov(F_assert ip) = ip"
| "push_prov(\<lparr>\<nu>x\<rparr>\<pi>) = \<lparr>\<nu>x\<rparr>(push_prov \<pi>)"
apply(finite_guess)+
apply(auto simp add: abs_fresh)
by(fresh_guess)+

lemma push_prov_eqvt[eqvt]:
  fixes \<pi> :: "'a frame frame"
  and p :: "name prm"
  shows "p\<bullet>(push_prov \<pi>) = push_prov(p\<bullet>\<pi>)"
by(nominal_induct \<pi> avoiding: p rule: frame.strong_inducts) auto

nominal_primrec append_at_end_prov :: "'a frame frame \<Rightarrow> name list \<Rightarrow> 'a frame frame"
  where
  "append_at_end_prov(F_assert ip) xvec  = \<lparr>\<nu>*xvec\<rparr>(F_assert ip)"
| "x \<sharp> xvec \<Longrightarrow> append_at_end_prov(\<lparr>\<nu>x\<rparr>\<pi>) xvec = \<lparr>\<nu>x\<rparr>(append_at_end_prov \<pi> xvec)"
apply(finite_guess)+
apply(auto simp add: abs_fresh)
by(fresh_guess)+

lemma append_at_end_prov_eqvt[eqvt]:
  fixes \<pi> :: "'a frame frame"
  and p :: "name prm"
  shows "p\<bullet>(append_at_end_prov \<pi> xvec ) = append_at_end_prov(p\<bullet>\<pi>) (p\<bullet>xvec)"
  by(nominal_induct \<pi> avoiding: p xvec rule: frame.strong_inducts) (auto simp add: eqvts pt_fresh_bij[OF pt_name_inst, OF at_name_inst])

lemma append_at_end_prov_res_chain':
  fixes \<pi> :: "'a frame frame"
  and p :: "name prm"
  assumes "yvec \<sharp>* xvec"
  shows "append_at_end_prov(\<lparr>\<nu>*xvec\<rparr>\<pi>) yvec = \<lparr>\<nu>*xvec\<rparr>(append_at_end_prov \<pi> yvec)"
  using assms
  by(induct xvec) simp_all

lemma append_at_end_prov_fresh:
  fixes \<pi> :: "'a frame frame"
  and x :: "name"
  shows "(x \<sharp> append_at_end_prov \<pi> xvec) = (x \<in> set xvec \<or> x \<sharp> \<pi>)"
proof(induct xvec)
  case Nil thus ?case
    by(nominal_induct \<pi> avoiding: x rule: frame.strong_inducts) (simp_all add: abs_fresh)
next
  case (Cons y xvec) thus ?case
    by(nominal_induct \<pi> avoiding: x y xvec rule: frame.strong_inducts) (simp_all add: abs_fresh)
qed

lemma append_at_end_prov_chain:
  fixes \<pi> :: "'a frame frame"
  and xvec :: "name list"
  shows "xvec \<sharp>* append_at_end_prov \<pi> xvec"
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* append_at_end_prov \<pi> yvec"
  by(auto simp add: append_at_end_prov_fresh fresh_star_def)

fun append_at_end_prov_option :: "'a frame frame option \<Rightarrow> name list \<Rightarrow> 'a frame frame option"
where
  "append_at_end_prov_option \<pi> xvec = map_option (\<lambda> \<pi>. append_at_end_prov \<pi> xvec) \<pi>"

lemma append_at_end_prov_option_eqvt[eqvt]:
  fixes \<pi> :: "'a frame frame option"
  and p :: "name prm"
  shows "p\<bullet>(append_at_end_prov_option \<pi> xvec ) = append_at_end_prov_option(p\<bullet>\<pi>) (p\<bullet>xvec)"
  by(induct \<pi>) (simp_all add: eqvts)

lemma frame_fresh_chain: 
  fixes xvec :: "name list"
  and   F    :: "'dd::fs_name frame"
  and   x    :: name

  shows "xvec \<sharp>* (\<lparr>\<nu>x\<rparr>F) = (\<forall>y\<in>set xvec. y = x \<or> y \<sharp> F)"
  by(simp add: fresh_star_def frame_res_chain_fresh abs_fun_fresh abs_fresh)

lemma frame_fresh_chain':
  fixes xvec :: "name list"
  and   F    :: "'dd::fs_name frame"
  and   x    :: name

  assumes "x \<sharp> xvec"

  shows "xvec \<sharp>* (\<lparr>\<nu>x\<rparr>F) = xvec \<sharp>* F"
  using assms
  by(auto simp add: fresh_star_def frame_res_chain_fresh abs_fun_fresh abs_fresh) (metis set_fresh)

lemma append_at_end_prov_option_perm:
  fixes p::"name prm"
  and xvec ::"name list"
  assumes "(p\<bullet>xvec) \<sharp>* \<pi>"
  and "xvec \<sharp>* \<pi>"
  and "xvec \<sharp>* (p\<bullet>xvec)"
  and "set p \<subseteq> set xvec \<times> set(p\<bullet>xvec)"
  shows  "append_at_end_prov_option (p\<bullet>\<pi>) (p\<bullet>xvec) = append_at_end_prov_option \<pi> xvec"
  using assms
proof(induct \<pi>)
  case None thus ?case by simp
next
  case (Some \<pi>)
  thus ?case
  proof(nominal_induct avoiding: p xvec rule: frame.strong_inducts)
    case(F_assert \<pi> p xvec)
    thus ?case
      by(auto simp add: frame_chain_alpha[where xvec=xvec and p=p])
  next
    case(F_res x \<pi> p xvec)
    moreover hence "(p\<bullet>xvec) \<sharp>* x"
      by(simp add: fresh_chain_simps)
    ultimately show ?case
      by(auto simp add: frame_fresh_chain')
  qed
qed

fun append_at_front_prov_option :: "'a frame frame option \<Rightarrow> name list \<Rightarrow> 'a frame frame option"
where
  "append_at_front_prov_option \<pi> xvec = map_option (\<lambda> \<pi>. \<lparr>\<nu>*xvec\<rparr>\<pi>) \<pi>"

lemma append_at_front_prov_option_eqvt[eqvt]:
  fixes \<pi> :: "'a frame frame option"
  and p :: "name prm"
  shows "p\<bullet>(append_at_front_prov_option \<pi> xvec ) = append_at_front_prov_option(p\<bullet>\<pi>) (p\<bullet>xvec)"
  by(induct \<pi>) (simp_all add: eqvts)

lemma append_at_front_prov_option_perm:
  fixes p::"name prm"
  and xvec ::"name list"
  assumes "(p\<bullet>xvec) \<sharp>* \<pi>"
  and "xvec \<sharp>* \<pi>"
  and "xvec \<sharp>* (p\<bullet>xvec)"
  and "set p \<subseteq> set xvec \<times> set(p\<bullet>xvec)"
  shows  "append_at_front_prov_option (p\<bullet>\<pi>) (p\<bullet>xvec) = append_at_front_prov_option \<pi> xvec"
  using assms
proof(induct \<pi>)
  case None thus ?case by simp
next
  case (Some \<pi>)
  thus ?case
    by(auto simp add: frame_chain_alpha[where xvec=xvec and p=p])
qed

lemma map_prov_step_option_eqvt[eqvt]:
  fixes p :: "name prm"
  shows "(p\<bullet>(map_option (F_res x) opt)) = map_option (F_res (p\<bullet>x)) (p\<bullet>opt)"
  by(induct opt) (auto simp add: perm_fun_def eqvts)

lemma map_prov_IP_push_prov_option_eqvt[eqvt]:
  fixes p :: "name prm"
  shows "(p\<bullet>(map_option (F_assert o push_prov) opt)) = map_option (F_assert o push_prov) (p\<bullet>opt)"
  by(induct opt) (auto simp add: perm_fun_def eqvts)
  
inductive semantics :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> ('a, 'b, 'c) residual \<Rightarrow> bool"
                       ("_ \<rhd> _ \<longmapsto> _ @ _" [50, 50, 50, 50] 50)
where
  c_input:  "\<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N; xvec \<sharp>* Tvec;
            length xvec = length Tvec;
            xvec \<sharp>* \<Psi>; xvec \<sharp>* M; xvec \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto> Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
| Output: "\<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto> Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<langle>N\<rangle> \<prec> P"
| Case:   "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> Cases Cs \<longmapsto> map_option (F_assert o push_prov) \<pi> @ Rs"
| c_par1:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto> \<pi> @ \<alpha> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<pi>; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); bn \<alpha> \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> append_at_end_prov_option \<pi> A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)"
| c_par2:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* \<pi>; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* (subject \<alpha>); bn \<alpha> \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> append_at_front_prov_option \<pi> A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')"
| c_comm1:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
             yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
             zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| c_comm2:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
             yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
             zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| c_open:    "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; x \<sharp> xvec; x \<sharp> yvec; x \<sharp> M; x \<sharp> \<Psi>;
              distinct xvec; distinct yvec;
              xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; xvec \<sharp>* \<pi>; yvec \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
              \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
| c_scope:  "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); distinct(bn \<alpha>); bn \<alpha> \<sharp>* \<pi>\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi> @ \<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')"
| Bang:    "\<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> !P \<longmapsto> map_option (F_assert o push_prov) \<pi> @ Rs"

(*abbreviation
  semantics_bottom_judge ("_ \<longmapsto> _ @ _" [50, 50, 50] 50) where "P \<longmapsto> \<pi> @ Rs \<equiv> \<one> \<rhd> P \<longmapsto> \<pi> @ Rs"*)

equivariance env.semantics

lemma push_prov_fresh[simp]:
  fixes \<pi> :: "'a frame frame"
  and x :: "name"
  shows "(x \<sharp> push_prov \<pi>) = x \<sharp> \<pi>"
  by(nominal_induct \<pi> avoiding: x rule: frame.strong_inducts) (simp_all add: abs_fresh)

lemma push_prov_chain:
  fixes \<pi> :: "'a frame frame"
  and xvec :: "name list"
  shows "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* push_prov \<pi>"
  by(auto simp add: fresh_star_def)

lemma frame_chain_fresh_chain:
  fixes xvec :: "name list"
  and   F    :: "'dd::fs_name"
  and   G    :: "'ee::fs_name frame"

  shows "xvec \<sharp>* (\<langle>xvec, F\<rangle>)"
  and "xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>G)"
  and "xvec \<sharp>* (\<langle>\<epsilon>, F\<rangle>) = xvec \<sharp>* F"
  by(auto simp add: fresh_star_def frame_res_chain_fresh abs_fun_fresh abs_fresh)  

lemma frame_chain_fresh_chain':
  fixes xvec :: "name list"
  and   F    :: "'dd::fs_name"
  and   G    :: "'dd::fs_name frame"  
  and   x    :: name

  shows "xvec \<sharp>* F \<Longrightarrow> xvec \<sharp>* (\<langle>yvec, F\<rangle>)"
  and "xvec \<sharp>* G \<Longrightarrow> xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>G)"
  and   "xvec \<sharp>* G \<Longrightarrow> xvec \<sharp>* (\<lparr>\<nu>x\<rparr>G)"
  by(auto simp add: fresh_star_def frame_res_chain_fresh abs_fun_fresh abs_fresh)

lemma frame_chain_fresh_chain'':
  fixes xvec :: "name list"
  and   F    :: "'dd::fs_name"
  and   x    :: name

    assumes "xvec \<sharp>* yvec"
  
  shows "xvec \<sharp>* (\<langle>yvec, F\<rangle>) = xvec \<sharp>* F"
  using assms
  by(auto simp add: fresh_star_def frame_res_chain_fresh abs_fun_fresh abs_fresh) (metis set_fresh)

lemma map_option_append_fresh:
  shows "xvec \<sharp>* map_option (\<lambda>\<pi>. append_at_end_prov \<pi> xvec) \<pi>"
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* map_option (\<lambda>\<pi>. append_at_end_prov \<pi> yvec) \<pi>"
  and "xvec \<sharp>* map_option (frame_res_chain xvec) \<pi>"  
  and "xvec \<sharp>* map_option (F_assert_judge xvec) \<pi>"
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* map_option (frame_res_chain yvec) \<pi>"  
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* map_option (F_assert_judge yvec) \<pi>"
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* map_option (F_res x) \<pi>"
  and "xvec \<sharp>* \<pi> \<Longrightarrow> xvec \<sharp>* map_option (F_assert \<circ> push_prov) \<pi>"
  and "x \<sharp> map_option (F_res x) \<pi>"
  by(induct \<pi>) (auto intro: append_at_end_prov_chain push_prov_chain simp add: abs_fresh frame_chain_fresh_chain frame_chain_fresh_chain')

lemma res_chain_fresh_vec: 
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows   "yvec \<sharp>* P \<Longrightarrow> yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
by (simp add: fresh_star_def res_chain_fresh)

nominal_inductive2 env.semantics
  avoids c_input: "set xvec"
       | c_par1: "set A\<^sub>Q \<union> set(bn \<alpha>)"
       | c_par2: "set A\<^sub>P \<union> set(bn \<alpha>)"
       | c_comm1: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec \<union> set yvec \<union> set zvec"
       | c_comm2: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec \<union> set yvec \<union> set zvec"
       | c_open:  "{x} \<union> set xvec \<union> set yvec"
       | c_scope: "{x} \<union> set(bn \<alpha>)"
  apply(auto intro: subst_term.subst4_chain subst4_chain simp add: abs_fresh residual_fresh map_option_append_fresh res_chain_fresh_vec frame_chain_fresh_chain'  frame_chain_fresh_chain'' frame_chain_fresh_chain)
  apply(force simp add: fresh_star_def abs_fresh)
  apply(simp add: bound_output_fresh)
  apply(simp add: bound_output_fresh_set)
  apply(simp add: bound_output_fresh_set)
  by(force simp add: fresh_star_def abs_fresh)

lemma nil_trans[dest]:
  fixes \<Psi>   :: 'b
  and   Rs   :: "('a, 'b, 'c) residual"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   yvec :: "name list"
  and   N'   :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   CsP  :: "('c \<times>  ('a, 'b, 'c) psi) list"
  and   \<Psi>'   :: 'b

  shows "\<Psi> \<rhd> \<zero> \<longmapsto> \<pi> @ Rs \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ K\<lparr>\<nu>*yvec\<rparr>\<langle>N'\<rangle> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi> @ K\<lparr>N'\<rparr> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi> @ \<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> \<lbrace>\<Psi>'\<rbrace> \<longmapsto>\<pi> @ Rs \<Longrightarrow> False"
apply(cases rule: semantics.cases) apply auto
apply(cases rule: semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: semantics.cases) apply(auto simp add: residual_inject)
by(cases rule: semantics.cases) (auto simp add: residual_inject)
 
lemma residual_eq:
  fixes \<alpha> :: "'a action"
  and   P :: "('a, 'b, 'c) psi"
  and   \<beta> :: "'a action"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> Q"
  and     "bn \<alpha> \<sharp>* (bn \<beta>)"
  and     "distinct(bn \<alpha>)"
  and     "distinct(bn \<beta>)"
  and     "bn \<alpha> \<sharp>* (\<alpha> \<prec> P)"
  and     "bn \<beta> \<sharp>* (\<beta> \<prec> Q)"

  obtains p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "\<beta> = p \<bullet> \<alpha>" and "Q = p \<bullet> P" and "bn \<alpha> \<sharp>* \<beta>" and "bn \<alpha> \<sharp>* Q" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* P"
using assms
proof(nominal_induct \<alpha> rule: action.strong_induct)
  case(In M N)
  thus ?case by(simp add: residual_inject)
next
  case(Out M xvec N)
  thus ?case 
    by(auto simp add: residual_inject)
      (drule_tac bound_output_chain_eq'', auto) 
next
  case Tau
  thus ?case by(simp add: residual_inject)
qed


lemma semantics_induct[consumes 3, case_names c_alpha c_input c_output c_case c_par1 c_par2 c_comm1 c_comm2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                'a frame frame option \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* (subject \<alpha>)"
  and     "distinct(bn \<alpha>)"
  and     r_alpha: "\<And>\<Psi> P \<pi> \<alpha> P' p C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* (subject \<alpha>); 
                                    bn \<alpha> \<sharp>* C; bn \<alpha> \<sharp>* (bn(p \<bullet> \<alpha>)); 
                                    set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinct_perm p;
                                    (bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; Prop C \<Psi> P \<pi> \<alpha> P'\<rbrakk> \<Longrightarrow>
                                     Prop C \<Psi> P \<pi> (p \<bullet> \<alpha>) (p \<bullet> P')"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>))
                              (K\<lparr>(N[xvec::=Tvec])\<rparr>) (P[xvec::=Tvec])"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) (K\<langle>N\<rangle>) P"
  and     r_case: "\<And>\<Psi> P \<pi> \<alpha> P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> \<alpha> P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                      Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) \<alpha> P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> \<alpha> P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) \<alpha> (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> \<alpha> Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) (M\<lparr>N\<rparr>) P'; 
                    extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q'; 
                    extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P'; 
                    extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>N\<rparr>) Q'; 
                    extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_open:  "\<And>\<Psi> P \<pi> M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;  distinct xvec; distinct yvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; xvec \<sharp>* \<pi>; yvec \<sharp>* \<pi>; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     r_scope: "\<And>\<Psi> P \<pi> \<alpha> P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> \<alpha> P';
                    x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>;
                    bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); x \<sharp> C; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P \<pi> \<alpha> P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) \<alpha> P'"
  shows "Prop C \<Psi> P \<pi> \<alpha> P'"
using `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* (subject \<alpha>)` `distinct(bn \<alpha>)`
proof(nominal_induct x3=="\<alpha> \<prec> P'" avoiding: \<alpha> C arbitrary: P' rule: semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P \<alpha> C P')
  thus ?case by(force intro: r_input simp add: residual_inject)
next
  case(Output \<Psi> M K N P \<alpha> C P')
  thus ?case by(force intro: r_output simp add: residual_inject)
next
  case(Case \<Psi> P \<pi> \<phi> Cs \<alpha> C P')
  thus ?case by(auto intro: r_case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q \<alpha>' C P'')
  note `\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> Q)" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (P' \<parallel> Q)" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P' \<parallel> Q)"
    by(rule residual_eq)
     
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> \<alpha> P'" by(rule_tac c_par1) auto
  moreover note `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `A\<^sub>Q \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<pi>`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) \<alpha> (P' \<parallel> Q)"
    by(rule_tac r_par1)

  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* bn \<alpha>'` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> Q)` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<pi>`
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> Q))"
    by(rule_tac r_alpha) (auto intro: map_option_append_fresh)
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P \<alpha>' C Q'')
  note `\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> Q''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> Q')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> Q'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and Q'eq: "Q'' = p \<bullet> (P \<parallel> Q')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P \<parallel> Q')"
    by(rule residual_eq)
    
  note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> \<alpha> Q'" by(rule_tac c_par2) auto

  moreover note `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<pi>`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> Q')"
    by(rule_tac r_par2)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> Q')` `bn \<alpha> \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<pi>`
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> Q'))"
    by(rule_tac r_alpha) (auto intro: map_option_append_fresh)
  with \<alpha>Eq Q'eq `distinct_perm p` show ?case by simp
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M N P' \<Psi>\<^sub>P Q KA\<^sub>Q zvec xvec Q' \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac r_comm1) (assumption | simp)+
  thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''`
    by(simp add: residual_inject)
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec Q' \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac r_comm2) (assumption | simp)+
  thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''`
    by(simp add: residual_inject)
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x \<alpha> C P'')
  note `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
  moreover from `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>` have "(xvec@x#yvec) \<sharp>* (bn \<alpha>)"
    by auto
  moreover from `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `distinct xvec` `distinct yvec`
  have "distinct(xvec@x#yvec)"
    by(auto simp add: fresh_star_def) (simp add: fresh_def name_list_supp)
  moreover note `distinct(bn \<alpha>)`
  moreover from `xvec \<sharp>* M` `x \<sharp> M` `yvec \<sharp>* M` have "(xvec@x#yvec) \<sharp>* M" by auto
  hence "(xvec@x#yvec) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by auto
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P'')" by simp
  ultimately obtain p where S: "(set p) \<subseteq> (set(xvec@x#yvec)) \<times> (set(p \<bullet> (xvec@x#yvec)))" and "distinct_perm p"
             and \<alpha>eq: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>" and P'eq: "P'' = (p \<bullet> P')"
             and A: "(xvec@x#yvec) \<sharp>* ((p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>)"
             and B: "(p \<bullet> (xvec@x#yvec)) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)"
             and C: "(p \<bullet> (xvec@x#yvec)) \<sharp>* P'"
    by(rule_tac residual_eq) (assumption | simp)+
    
  note `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<in> (supp N)`

  moreover {
    fix C
    from `xvec \<sharp>* M` `yvec \<sharp>* M` have "(xvec@yvec) \<sharp>* M" by simp
    moreover from `distinct xvec` `distinct yvec` `xvec \<sharp>* yvec` have "distinct(xvec@yvec)"
      by auto (simp add: fresh_star_def name_list_supp fresh_def)
    ultimately have "Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P'"
      by(rule_tac c_open) auto
  }

  moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* M`
                 `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* C` `x \<sharp> C` `xvec \<sharp>* C` `distinct xvec` `distinct yvec` `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<pi>`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
    by(rule_tac r_open) 

  with `xvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `yvec \<sharp>* P` `xvec \<sharp>* M` `yvec \<sharp>* M` 
       `yvec \<sharp>* C`  S `distinct_perm p` `x \<sharp> C` `xvec \<sharp>* C`
       `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` A B C `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<pi>`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (p \<bullet> (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)) (p \<bullet> P')"
    by(rule_tac \<alpha>="M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>" in r_alpha) (auto simp add: fresh_star_def abs_fresh)
  with \<alpha>eq P'eq show ?case by simp
next
  case(c_scope \<Psi> P \<pi> \<alpha> P' x \<alpha>' C P'')
  note `\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P') = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (\<lparr>\<nu>x\<rparr>P')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (\<lparr>\<nu>x\<rparr>P')"
    by(rule residual_eq)
    
  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C \<Psi> P \<pi> \<alpha> P'" by(rule_tac c_scope) auto

  moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>`
                `x \<sharp> C` `bn \<alpha> \<sharp>* C` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<pi>`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
    by(rule_tac r_scope)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (\<lparr>\<nu>x\<rparr>P')` `bn \<alpha> \<sharp>* \<pi>`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) (p \<bullet> \<alpha>) (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))"
    by(rule_tac r_alpha) (auto intro: map_option_append_fresh)
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(Bang \<Psi> P \<pi> \<alpha> C P')
  thus ?case
    by(rule_tac r_bang) auto
qed

lemma tau_no_provenance[simp]:
  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ \<tau> \<prec> P'"
  shows "\<pi> = None"
  using assms
  by(nominal_induct x3=="\<tau> \<prec> P'" arbitrary: P' rule: semantics.strong_induct) (auto simp add: residual_inject)

lemma tau_no_provenance':
  shows "\<Psi> \<rhd> P \<longmapsto> \<pi> @ \<tau> \<prec> P' \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto> None @ \<tau> \<prec> P'"
  by(auto dest: tau_no_provenance)
  
lemma output_induct[consumes 1, case_names c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) bound_output \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ R_out M B"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) K (N \<prec>' P)"
  and     r_case: "\<And>\<Psi> P \<pi> M B \<phi> Cs C.  
                  \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ (R_out M B); \<And>C. Prop C \<Psi> P \<pi> M B; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                   Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) M B"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C; A\<^sub>Q \<sharp>* \<pi>; xvec \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q))"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q');
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* P;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* C; A\<^sub>P \<sharp>* \<pi>; xvec \<sharp>* \<pi>\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q'))"
  and     r_open:  "\<And>\<Psi> P \<pi> M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P (Some \<pi>) M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; xvec \<sharp>* \<pi>; yvec \<sharp>* \<pi>; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P')"
  and     r_scope: "\<And>\<Psi> P \<pi> M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<pi>;
                    x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' \<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P \<pi> M B C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ (R_out M B); guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> M B\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) M B"
  shows "Prop C \<Psi> P \<pi> M B"
using `\<Psi> \<rhd> P \<longmapsto>\<pi> @ (R_out M B)`
proof(nominal_induct \<Psi> P \<pi> Rs=="(R_out M B)" avoiding: C arbitrary: B rule: semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P C)
  thus ?case by(simp add: residual_inject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(force simp add: residual_inject intro: r_output)
next
  case(Case \<Psi> P \<phi> Cs C B)
  thus ?case by(force intro: r_case) 
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q C)
  thus ?case by(force dest: r_par1 simp add: residual_inject)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P C)
  thus ?case by(force dest: r_par2 simp add: residual_inject)
next
  case c_comm1
  thus ?case by(simp add: residual_inject)
next
  case c_comm2
  thus ?case by(simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec yvec N P' x C B)
  thus ?case by(force intro: r_open simp add: residual_inject)
next
  case(c_scope \<Psi> P M \<alpha> P' x C)
  thus ?case by(force intro: r_scope simp add: residual_inject)
next
  case(Bang  \<Psi> P C)
  thus ?case by(force intro: r_bang)
qed

lemma bound_output_bind_object:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "y \<in> set(bn \<alpha>)"

  shows "y \<in> supp(object \<alpha>)"
using assms
proof(nominal_induct avoiding: P' arbitrary: y rule: semantics_induct)
  case(c_alpha \<Psi> P \<pi> \<alpha> P' p P'' y)
  from `y \<in> set(bn(p \<bullet> \<alpha>))` have "(p \<bullet> y) \<in> (p \<bullet> set(bn(p \<bullet> \<alpha>)))"
    by(rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  hence "(p \<bullet> y) \<in> set(bn \<alpha>)" using `distinct_perm p`
    by(simp add: eqvts)
  hence "(p \<bullet> y) \<in> supp(object \<alpha>)" by(rule c_alpha)
  hence "(p \<bullet> p \<bullet> y) \<in> (p \<bullet> supp(object \<alpha>))"
    by(rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  thus ?case using `distinct_perm p`
    by(simp add: eqvts)
next
  case c_input 
  thus ?case by(simp add: supp_list_nil)
next
  case c_output
  thus ?case by(simp add: supp_list_nil)
next
  case c_case
  thus ?case by simp
next
  case c_par1
  thus ?case by simp
next
  case c_par2
  thus ?case by simp
next
  case c_comm1
  thus ?case by(simp add: supp_list_nil)
next
  case c_comm2
  thus ?case by(simp add: supp_list_nil)
next
  case c_open
  thus ?case by(auto simp add: supp_list_cons supp_list_append supp_atm supp_some)
next
  case c_scope
  thus ?case by simp
next
  case c_bang
  thus ?case by simp
qed

lemma alpha_bound_output_chain':
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   B    :: "('a, 'b, 'c) bound_output"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* B"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>([xvec yvec] \<bullet>\<^sub>v B)"
using assms
proof(induct rule: compose_perm_induct)
  case c_base
  show ?case by simp
next
  case(c_step x xvec y yvec)
  thus ?case
    apply auto
    by(subst alpha_bound_output[of y]) (auto simp add: eqvts)
qed

lemma alpha_bound_output_chain'':
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* N"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P) = \<lparr>\<nu>*yvec\<rparr>(([xvec yvec] \<bullet>\<^sub>v N) \<prec>' ([xvec yvec] \<bullet>\<^sub>v P))"
proof -
  from assms have "\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P) = \<lparr>\<nu>*yvec\<rparr>([xvec yvec] \<bullet>\<^sub>v (N \<prec>' P))"
    by(simp add: alpha_bound_output_chain')
  thus ?thesis by simp
qed

lemma alpha_distinct:
  fixes xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   M    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> Q"
  and     "distinct(bn \<alpha>)"
  and     "\<And>x. x \<in> set(bn \<alpha>) \<Longrightarrow> x \<in> supp(object \<alpha>)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"
  and     "bn \<alpha> \<sharp>* (object \<beta>)"
  and     "bn \<alpha> \<sharp>* Q"

  shows "distinct(bn \<beta>)"
using assms
proof(rule_tac action_cases[where \<alpha>=\<alpha>], auto simp add: residual_inject supp_some)
  fix xvec M yvec N
  assume Eq: "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*yvec\<rparr>M \<prec>' Q" 
  assume "distinct xvec" and "xvec \<sharp>* M" and "xvec \<sharp>* yvec" and "xvec \<sharp>* Q" 
  assume Mem: "\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> (supp N)"
  show "distinct yvec"
proof -
  from Eq have "length xvec = length yvec"
    by(rule bound_output_chain_eq_length)
  with Eq `distinct xvec` `xvec \<sharp>* yvec` `xvec \<sharp>* M` `xvec \<sharp>* Q` Mem show ?thesis
  proof(induct n=="length xvec" arbitrary: xvec yvec M Q rule: nat.induct)
    case(zero xvec yvec M Q)
    thus ?case by simp
  next
    case(Suc n xvec yvec M Q)
    have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
    then obtain x xvec' y yvec' where x_eq: "xvec = x#xvec'" and y_eq: "yvec = y#yvec'"
                                  and L': "length xvec' = length yvec'"
      by(cases xvec, auto, cases yvec, auto)
    have xvec_freshyvec: "xvec \<sharp>* yvec" and xvec_dist: "distinct xvec" by fact+
    with x_eq y_eq have xineqy: "x \<noteq> y" and xvec'_freshyvec': "xvec' \<sharp>* yvec'"
                  and xvec'_dist: "distinct xvec'" and x_freshxvec': "x \<sharp> xvec'"
                  and x_freshyvec': "x \<sharp> yvec'" and y_freshxvec': "y \<sharp> xvec'"
      by auto
    have Eq: "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*yvec\<rparr>M \<prec>' Q" by fact
    with x_eq y_eq xineqy have Eq': "\<lparr>\<nu>*xvec'\<rparr>N \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> M) \<prec>' ([(x, y)] \<bullet> Q)"
      by(simp add: bound_output.inject alpha eqvts) 
    moreover have Mem:"\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp N" by fact
    with x_eq have "\<And>x. x \<in> set xvec' \<Longrightarrow> x \<in> supp N" by simp
    moreover have "xvec \<sharp>* M" by fact
    with x_eq x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> M)" by simp
    moreover have xvec_freshQ: "xvec \<sharp>* Q" by fact
    with x_eq x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
    moreover have "Suc n = length xvec" by fact
    with x_eq have "n = length xvec'" by simp
    moreover from xvec'_freshyvec' x_freshxvec' y_freshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> yvec')"
      by simp
    moreover from L' have "length xvec' = length([(x, y)] \<bullet> yvec')" by simp
    ultimately have "distinct([(x, y)] \<bullet> yvec')" using xvec'_dist
      by(rule_tac Suc) (assumption | simp)+
    hence "distinct yvec'" by simp
    from Mem x_eq have x_suppN: "x \<in> supp N" by simp
    from L `distinct xvec` `xvec \<sharp>* yvec` `xvec \<sharp>* M` `xvec \<sharp>* Q` 
    have "\<lparr>\<nu>*yvec\<rparr>M \<prec>' Q = \<lparr>\<nu>*xvec\<rparr>([yvec xvec] \<bullet>\<^sub>v M) \<prec>' ([yvec xvec] \<bullet>\<^sub>v Q)"
      by(simp add: alpha_bound_output_chain'')
    with Eq have "N = [yvec xvec] \<bullet>\<^sub>v M" by simp
    with x_eq y_eq have "N = [(y, x)] \<bullet> [yvec' xvec'] \<bullet>\<^sub>v M"
      by simp
    with x_suppN have y_suppM: "y \<in> supp([yvec' xvec'] \<bullet>\<^sub>v M)"
      by(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
        (simp add: calc_atm eqvts name_swap)
    have "y \<sharp> yvec'"
    proof(simp add: fresh_def, rule notI)
      assume "y \<in> supp yvec'"
      hence "y mem yvec'"
	by(induct yvec') (auto simp add: supp_list_nil supp_list_cons supp_atm)
      moreover from `xvec \<sharp>* M` x_eq x_freshxvec' have "xvec' \<sharp>* M" by simp
      ultimately have "y \<sharp> [yvec' xvec'] \<bullet>\<^sub>v  M" using L' xvec'_freshyvec' xvec'_dist
	by(force intro: fresh_chain_perm)
      with y_suppM show "False" by(simp add: fresh_def)
    qed
    with `distinct yvec'`  y_eq show ?case by simp
  qed
qed
qed

lemma bound_output_distinct:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"

  shows "distinct(bn \<alpha>)"
using assms
proof(nominal_induct \<Psi> P \<pi> x3=="\<alpha> \<prec> P'" avoiding: \<alpha> P' rule: semantics.strong_induct)
  case c_input
  thus ?case by(simp add: residual_inject)
next
  case Output
  thus ?case by(simp add: residual_inject)
next
  case Case
  thus ?case by(simp add: residual_inject)
next
  case c_par1
  thus ?case by(force intro: alpha_distinct bound_output_bind_object)
next
  case c_par2
  thus ?case by(force intro: alpha_distinct bound_output_bind_object)
next 
  case c_comm1
  thus ?case by(simp add: residual_inject)
next
  case c_comm2
  thus ?case by(simp add: residual_inject)
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x \<alpha> P'')
  note `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
  moreover from `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `distinct xvec` `distinct yvec`
  have "distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
    by auto (simp add: fresh_star_def fresh_def name_list_supp)
  moreover {
    fix y
    from `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<in> supp N` `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> M` `x \<sharp> \<Psi>` `distinct xvec` `distinct yvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* M` `xvec \<sharp>* yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<pi>`
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some (\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule_tac semantics.c_open)
    moreover from `xvec \<sharp>* M` `x \<sharp> M` `yvec \<sharp>* M` 
    have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* (subject(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by simp
    moreover note `distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))`
    moreover assume "y \<in> set(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"

    ultimately have "y \<in> supp(object(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by(rule_tac bound_output_bind_object)
  }
  moreover from `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>`
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* bn \<alpha>" and "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* object \<alpha>" by simp+
  moreover from `xvec \<sharp>* P''` `x \<sharp> P''` `yvec \<sharp>* P''`
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* P''" by simp
  ultimately show ?case by(rule alpha_distinct)
next
  case c_scope
  thus ?case
    by(rule_tac alpha_distinct, auto) (rule_tac bound_output_bind_object, auto)
next
  case Bang
  thus ?case by simp
qed

lemma input_distinct:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"

  assumes "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto> \<pi> @ Rs"

  shows "distinct xvec"
using assms
by(nominal_induct \<Psi> P=="M\<lparr>\<lambda>*xvec N\<rparr>.P" \<pi> Rs avoiding: xvec N P rule: semantics.strong_induct)
(auto simp add: psi.inject intro: alpha_input_distinct)


lemma push_prov_res_chain[simp]:
  "(push_prov (\<lparr>\<nu>*A\<^sub>P\<rparr>F_assert (\<lparr>\<nu>*xvec\<rparr>F_assert K))) = (\<lparr>\<nu>*(A\<^sub>P @ xvec)\<rparr>F_assert K)"
  by(induct A\<^sub>P) simp_all

lemma append_at_end_prov_res_chain[simp]:
  assumes "A\<^sub>Q \<sharp>* A\<^sub>P"
  shows "append_at_end_prov (\<lparr>\<nu>*A\<^sub>P\<rparr>F_assert IP) A\<^sub>Q = (\<lparr>\<nu>*(A\<^sub>P@A\<^sub>Q)\<rparr>F_assert IP)"
  using assms
  by(induct A\<^sub>P) simp_all

lemma output_provenance:
  fixes C::"'ty :: fs_name"
  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ R_out M B"
  shows "\<exists> A\<^sub>P \<Psi>\<^sub>P xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and> distinct xvec \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* M \<and> A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* B \<and> A\<^sub>P \<sharp>* C \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* B \<and> xvec \<sharp>* C \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M)"
proof -
  {
    fix C::"'typ::fs_name"
    and   D::"('a,'b,'c) psi"
    and   E::"name list"
    note assms
    hence "\<exists> A\<^sub>P \<Psi>\<^sub>P xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and> distinct xvec \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* M \<and> A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* B \<and> A\<^sub>P \<sharp>* C \<and> A\<^sub>P \<sharp>* D \<and> A\<^sub>P \<sharp>* E \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* B \<and> xvec \<sharp>* C \<and> xvec \<sharp>* D \<and> xvec \<sharp>* E \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M)"
  proof(nominal_induct avoiding: C D E rule: output_induct)
    case c_output
    thus ?case
      by(auto intro!: exI[where x="[]"] dest: stat_eq_ent[OF Assertion_stat_eq_sym, OF Identity])
  next
    case(c_case \<Psi> P \<pi> M B \<phi> Cs C D)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* B" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> (Cases Cs))" and "A\<^sub>P \<sharp>* E" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* B" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> (Cases Cs))" and "xvec \<sharp>* E" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover have "distinct(A\<^sub>P @ xvec)"
      using `distinct A\<^sub>P` `distinct xvec` `A\<^sub>P \<sharp>* xvec`
      by(auto simp add: fresh_star_def fresh_def name_list_supp)
    moreover have "\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> M"
    proof -
      from `guarded P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "\<Psi>\<^sub>P \<simeq> \<one>"
        by(blast dest: guarded_stat_eq)
      thus ?thesis
        using `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M`
        by (metis composition_sym stat_eq_ent)
    qed
    ultimately show ?case
      apply(rule_tac exI[where x="[]"])
      apply(rule_tac exI[where x="\<one>"])
      apply(rule_tac exI[where x="A\<^sub>P @ xvec"])
      apply(rule_tac exI[where x="K"])
      by auto
  next
    case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M yvec N P' A\<^sub>Q Q C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)" and  "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "xvec \<sharp>* (E@yvec@A\<^sub>Q)" and "A\<^sub>P \<sharp>* xvec" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover note `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>`  `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q`
      `A\<^sub>Q \<sharp>* yvec` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* D` `A\<^sub>Q \<sharp>* E`
    moreover have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      using `A\<^sub>Q \<sharp>* P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)`
      by(auto dest: extract_frame_fresh_chain)
    moreover have "distinct(A\<^sub>P@A\<^sub>Q)"
      using `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)`
      by(auto simp add: fresh_star_def fresh_def name_list_supp supp_list_append)
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      using `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M`
      by(metis Associativity associativity_sym stat_eq_ent)
    ultimately show ?case
      apply(rule_tac exI[where x="A\<^sub>P @ A\<^sub>Q"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto intro: merge_frames)
  next
    case(c_par2 \<Psi> \<Psi>\<^sub>Q P \<pi> M yvec N P' A\<^sub>Q Q C D)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)" and  "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "xvec \<sharp>* (E@yvec@A\<^sub>Q)" and "A\<^sub>P \<sharp>* xvec" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover note `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>`  `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q`
      `A\<^sub>Q \<sharp>* yvec` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* D` `A\<^sub>Q \<sharp>* E`
    moreover have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      using `A\<^sub>Q \<sharp>* P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)`
      by(auto dest: extract_frame_fresh_chain)
    moreover have "distinct(A\<^sub>Q@A\<^sub>P)"
      using `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* (E@yvec@A\<^sub>Q)`
      by(auto simp add: fresh_star_def fresh_def name_list_supp supp_list_append)
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      using `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M`
      by(metis Associativity stat_eq_ent)
    moreover have "\<And> \<pi>::'a frame frame. \<lparr>\<nu>*A\<^sub>Q\<rparr>(\<lparr>\<nu>*A\<^sub>P\<rparr>\<pi>) = \<lparr>\<nu>*(A\<^sub>Q@A\<^sub>P)\<rparr>\<pi>"
      by(induct A\<^sub>Q) auto
    ultimately show ?case
      apply(rule_tac exI[where x="A\<^sub>Q @ A\<^sub>P"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto intro: merge_frames)
  next
    case (c_open \<Psi> P \<pi> M yvec zvec N P' x C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* (\<lparr>\<nu>*(yvec @ zvec)\<rparr>N \<prec>' P')" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> P)" and "A\<^sub>P \<sharp>* (x#(E@yvec@zvec))" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* (\<lparr>\<nu>*(yvec @ zvec)\<rparr>N \<prec>' P')" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> P)" and "xvec \<sharp>* (x#(E@yvec@zvec))" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> C` `x \<sharp> D` `x \<sharp> E`
    ultimately show ?case
      apply(rule_tac exI[where x="x#A\<^sub>P"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>P"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto simp add: abs_fresh bound_output_fresh)
  next
    case(c_scope \<Psi> P \<pi> M yvec N P' x C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> P)" and "A\<^sub>P \<sharp>* (x#(E@yvec))" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>N \<prec>' P')" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> P)" and "xvec \<sharp>* (x#(E@yvec))" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> C` `x \<sharp> D` `x \<sharp> E` `x \<sharp> N`
    ultimately show ?case    
      apply(rule_tac exI[where x="x#A\<^sub>P"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>P"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto simp add: abs_fresh bound_output_fresh)
  next
    case(c_bang \<Psi> P \<pi> M B C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame(P\<parallel>!P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* (P\<parallel>!P)"
      and "A\<^sub>P \<sharp>* B" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> P)" and "A\<^sub>P \<sharp>* E" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* (P\<parallel>!P)"
      and "xvec \<sharp>* B" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> P)" and "xvec \<sharp>* E" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by blast
    moreover have "distinct(A\<^sub>P @ xvec)"
      using `distinct A\<^sub>P` `distinct xvec` `A\<^sub>P \<sharp>* xvec`
      by(auto simp add: fresh_star_def fresh_def name_list_supp)
    moreover have "\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> M"
    proof -
      from `guarded P` have "guarded(P \<parallel> !P)"
        by simp
      with `extract_frame(P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "\<Psi>\<^sub>P \<simeq> \<one>"
        by(blast dest: guarded_stat_eq)
      thus ?thesis
        using `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M`
        by (metis composition_sym stat_eq_ent)
    qed
    ultimately show ?case
      apply(rule_tac exI[where x="[]"])
      apply(rule_tac exI[where x="\<one>"])
      apply(rule_tac exI[where x="A\<^sub>P @ xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto simp add: abs_fresh bound_output_fresh)
  qed
}
thus ?thesis by blast
qed

lemma output_induct'[consumes 2, case_names c_alpha c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 'a \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     r_alpha: "\<And>\<Psi> P \<pi> M xvec N P' p C. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* \<pi>;  xvec \<sharp>* M;  xvec \<sharp>* C; xvec \<sharp>* (p \<bullet> xvec); 
                                           set p \<subseteq> set xvec \<times> set(p \<bullet> xvec); distinct_perm p;
                                           (p \<bullet> xvec) \<sharp>* N; (p \<bullet> xvec) \<sharp>* P'; Prop C \<Psi> P \<pi> M xvec N P'\<rbrakk> \<Longrightarrow>
                                           Prop C \<Psi> P \<pi> M (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P')"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) K ([]) N P"
  and     r_case: "\<And>\<Psi> P \<pi> M xvec N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> M xvec N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                             Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) M xvec N P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> M xvec N P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* \<pi>; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) M xvec N (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> M xvec N Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P; xvec \<sharp>* \<pi>; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) M xvec N (P \<parallel> Q')"
  and     r_open:  "\<And>\<Psi> P \<pi> M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P (Some \<pi>) M (xvec@yvec) N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* \<pi>; xvec \<sharp>* M; 
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* \<pi>; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) M (xvec@x#yvec) N P'"
  and     r_scope: "\<And>\<Psi> P \<pi> M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> M xvec N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* P; xvec \<sharp>* \<pi>; xvec \<sharp>* M; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) M xvec N (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P \<pi> M xvec N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> M xvec N P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) M xvec N P'"
  shows "Prop C \<Psi> P \<pi> M xvec N P'"
proof -
  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  moreover from `xvec \<sharp>* M` have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))"
    by(rule bound_output_distinct)
  ultimately show ?thesis
  proof(nominal_induct \<Psi> P \<pi> \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: C arbitrary: M xvec N rule: semantics_induct)
    case(c_alpha \<Psi> P \<pi> \<alpha> P' p C M xvec N)
    from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)"
      by(simp add: fresh_bij)
    with `distinct_perm p` have A: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>"
      by(simp add: eqvts)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* \<pi>` `bn \<alpha> \<sharp>* subject \<alpha> ` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* bn(p \<bullet> \<alpha>)` `distinct_perm p`
    have "(p \<bullet> xvec) \<sharp>* \<Psi>" and  "(p \<bullet> xvec) \<sharp>* P" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" and  "(p \<bullet> xvec) \<sharp>* C" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> xvec)" "(p \<bullet> xvec) \<sharp>* \<pi>"
      by auto
    moreover from A `set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))` `distinct_perm p`
    have S: "set p \<subseteq> set(p \<bullet> xvec) \<times> set(p \<bullet> p \<bullet> xvec)" by simp
    moreover note `distinct_perm p`
    moreover from A `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* P'`
    have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> N)" and "(p \<bullet> p \<bullet> xvec) \<sharp>* P'" by simp+
    moreover from A have "Prop C \<Psi> P \<pi> (p \<bullet> M) (p \<bullet> xvec) (p \<bullet> N) P'"
      by(rule c_alpha)
    ultimately have "Prop C \<Psi> P \<pi> (p \<bullet> M) (p \<bullet> p \<bullet> xvec) (p \<bullet> p \<bullet> N) (p \<bullet> P')"
      by(rule_tac r_alpha)
    moreover from A `bn \<alpha> \<sharp>* subject \<alpha>` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" by simp
    hence "xvec \<sharp>* M" by(simp add: fresh_star_bij)
    from A `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `distinct_perm p` have "xvec \<sharp>* (p \<bullet> M)" by simp
    hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> M)" by(simp add: fresh_star_bij)
    with `distinct_perm p` have "(p \<bullet> xvec) \<sharp>* M" by simp
    with `xvec \<sharp>* M` S `distinct_perm p` have  "(p \<bullet> M) = M" by simp
    ultimately show ?case using S `distinct_perm p` by simp 
  next
    case c_input
    thus ?case by(simp add: residual_inject)
  next
    case c_output
    thus ?case by(force dest: r_output simp add: action.inject)
  next
    case c_case
    thus ?case by(force intro: r_case)
  next
    case c_par1
    thus ?case by(force dest: r_par1)
  next
    case c_par2
    thus ?case by(force dest: r_par2)
  next
    case c_comm1
    thus ?case by(simp add: action.inject)
  next
    case c_comm2
    thus ?case by(simp add: action.inject)
  next
    case c_open
    thus ?case by(auto intro: r_open simp add: action.inject)
  next
    case c_scope
    thus ?case by(auto intro: r_scope)
  next
    case c_bang
    thus ?case
      by(force intro: r_bang)
  qed
qed

lemma input_induct[consumes 1, case_names c_input c_case c_par1 c_par2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>))
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec])"
  and     r_case: "\<And>\<Psi> P \<pi> M N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> M N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                        Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) M N P'" 
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> M N P'; distinct A\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) M N (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> M N Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> M N Q'; distinct A\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) M N (P \<parallel> Q')"
  and     r_scope: "\<And>\<Psi> P \<pi> M N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P \<pi> M N P'; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) M N (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P \<pi> M N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> M N P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) M N P'"
  shows "Prop C \<Psi> P \<pi> M N P'"
using Trans
proof(nominal_induct \<Psi> P \<pi> Rs=="M\<lparr>N\<rparr> \<prec> P'" avoiding: C arbitrary: P' rule: semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P C)
  thus ?case
    by(force intro: r_input simp add: residual_inject action.inject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(simp add: residual_inject)
next
  case(Case \<Psi> P \<phi> CS C P')
  thus ?case by(force intro: r_case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q C P'')
  thus ?case using r_par1
    by(auto simp add: residual_inject)
next
  case(c_par2 \<Psi> \<Psi>P Q \<alpha> Q' xvec P C Q'')
  thus ?case using r_par2
    by(force simp add: residual_inject)
next
  case(c_comm1 \<Psi> \<Psi>Q P M N P' xvec \<Psi>P Q K zvec Q' yvec C PQ)
  thus ?case by(simp add: residual_inject)
next
  case(c_comm2 \<Psi> \<Psi>Q P M zvec N P' xvec \<Psi>P Q K yvec Q' C PQ)
  thus ?case by(simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec N P' x yvec C P'') 
  thus ?case by(simp add: residual_inject)
next
  case(c_scope \<Psi> P \<alpha> P' x C P'')
  thus ?case by(force intro: r_scope simp add: residual_inject)
next
  case(Bang \<Psi> P C P')
  thus ?case
    by(force intro: r_bang)
qed

lemma input_provenance:
  fixes C::"'ty :: fs_name"
  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  shows "\<exists> A\<^sub>P \<Psi>\<^sub>P xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and> distinct xvec \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* M \<and> A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* N \<and> A\<^sub>P \<sharp>* P' \<and> A\<^sub>P \<sharp>* C \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P' \<and> xvec \<sharp>* C \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K)"
proof -
  {
    fix C::"'typ::fs_name"
    and   D::"('a,'b,'c) psi"
    and   E::"name list"
    note assms
    hence "\<exists> A\<^sub>P \<Psi>\<^sub>P xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and> distinct xvec \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* M \<and> A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* N \<and> A\<^sub>P \<sharp>* P' \<and> A\<^sub>P \<sharp>* C \<and> A\<^sub>P \<sharp>* D \<and> A\<^sub>P \<sharp>* E \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P' \<and> xvec \<sharp>* C \<and> xvec \<sharp>* D \<and> xvec \<sharp>* E \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K)"
  proof(nominal_induct avoiding: C D E rule: input_induct)
    case c_input
    thus ?case
      by(auto intro!: exI[where x="[]"] dest: stat_eq_ent[OF Assertion_stat_eq_sym, OF Identity])
  next
    case(c_case \<Psi> P \<pi> M N P' \<phi> Cs C D)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> (Cases Cs))" and "A\<^sub>P \<sharp>* E" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> (Cases Cs))" and "xvec \<sharp>* E" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      by blast
    moreover have "distinct(A\<^sub>P @ xvec)"
      using `distinct A\<^sub>P` `distinct xvec` `A\<^sub>P \<sharp>* xvec`
      by(auto simp add: fresh_star_def fresh_def name_list_supp)
    moreover have "\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    proof -
      from `guarded P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "\<Psi>\<^sub>P \<simeq> \<one>"
        by(blast dest: guarded_stat_eq)
      thus ?thesis
        using `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
        by (metis composition_sym stat_eq_ent)
    qed
    ultimately show ?case
      apply(rule_tac exI[where x="[]"])
      apply(rule_tac exI[where x="\<one>"])
      apply(rule_tac exI[where x="A\<^sub>P @ xvec"])
      apply(rule_tac exI[where x="K"])
      by auto
  next
    case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "A\<^sub>P \<sharp>* (E@A\<^sub>Q)" and  "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "xvec \<sharp>* (E@A\<^sub>Q)" and "A\<^sub>P \<sharp>* xvec" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      by blast
    moreover note `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>`  `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q`
      `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* D` `A\<^sub>Q \<sharp>* E`
    moreover have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      using `A\<^sub>Q \<sharp>* P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* (E@A\<^sub>Q)`
      by(auto dest: extract_frame_fresh_chain)
    moreover have "distinct(A\<^sub>P@A\<^sub>Q)"
      using `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* (E@A\<^sub>Q)`
      by(auto simp add: fresh_star_def fresh_def name_list_supp supp_list_append)
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
      using `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
      by(metis Associativity associativity_sym stat_eq_ent)
    ultimately show ?case
      apply(rule_tac exI[where x="A\<^sub>P @ A\<^sub>Q"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto intro: merge_frames)
  next
    case(c_par2 \<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q C D)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "A\<^sub>P \<sharp>* (E@A\<^sub>Q)" and  "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> Q \<parallel> \<lbrace>\<Psi>\<^sub>Q\<rbrace> \<parallel> \<lbrace>\<Psi>\<rbrace>)" and "xvec \<sharp>* (E@A\<^sub>Q)" and "A\<^sub>P \<sharp>* xvec" and "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      by blast
    moreover note `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>`  `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q`
      `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* D` `A\<^sub>Q \<sharp>* E`
    moreover have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      using `A\<^sub>Q \<sharp>* P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* (E@A\<^sub>Q)`
      by(auto dest: extract_frame_fresh_chain)
    moreover have "distinct(A\<^sub>Q@A\<^sub>P)"
      using `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* (E@A\<^sub>Q)`
      by(auto simp add: fresh_star_def fresh_def name_list_supp supp_list_append)
    moreover have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      using `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
      by(metis Associativity stat_eq_ent)
    moreover have "\<And> \<pi>::'a frame frame. \<lparr>\<nu>*A\<^sub>Q\<rparr>(\<lparr>\<nu>*A\<^sub>P\<rparr>\<pi>) = \<lparr>\<nu>*(A\<^sub>Q@A\<^sub>P)\<rparr>\<pi>"
      by(induct A\<^sub>Q) auto
    ultimately show ?case
      apply(rule_tac exI[where x="A\<^sub>Q @ A\<^sub>P"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto intro: merge_frames)
  next
    case(c_scope \<Psi> P \<pi> M N P' x C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* P"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> P)" and "A\<^sub>P \<sharp>* (x#E)" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P"
      and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> P)" and "xvec \<sharp>* (x#E)" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      by blast
    moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> C` `x \<sharp> D` `x \<sharp> E` `x \<sharp> N`
    ultimately show ?case    
      apply(rule_tac exI[where x="x#A\<^sub>P"])
      apply(rule_tac exI[where x="\<Psi>\<^sub>P"])
      apply(rule_tac exI[where x="xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto simp add: abs_fresh bound_output_fresh)
  next
    case(c_bang \<Psi> P \<pi> M N P' C D E)
    then obtain A\<^sub>P \<Psi>\<^sub>P xvec K where
      "\<pi> = Some (\<langle>A\<^sub>P; xvec, K\<rangle>)" and "extract_frame(P\<parallel>!P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and "distinct A\<^sub>P" and "distinct xvec" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* (P\<parallel>!P)"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* (D \<parallel> P)" and "A\<^sub>P \<sharp>* E" "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* (P\<parallel>!P)"
      and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C"and "xvec \<sharp>* (D \<parallel> P)" and "xvec \<sharp>* E" and "A\<^sub>P \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
      by blast
    moreover have "distinct(A\<^sub>P @ xvec)"
      using `distinct A\<^sub>P` `distinct xvec` `A\<^sub>P \<sharp>* xvec`
      by(auto simp add: fresh_star_def fresh_def name_list_supp)
    moreover have "\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    proof -
      from `guarded P` have "guarded(P \<parallel> !P)"
        by simp
      with `extract_frame(P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "\<Psi>\<^sub>P \<simeq> \<one>"
        by(blast dest: guarded_stat_eq)
      thus ?thesis
        using `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K`
        by (metis composition_sym stat_eq_ent)
    qed
    ultimately show ?case
      apply(rule_tac exI[where x="[]"])
      apply(rule_tac exI[where x="\<one>"])
      apply(rule_tac exI[where x="A\<^sub>P @ xvec"])
      apply(rule_tac exI[where x="K"])
      by(auto simp add: abs_fresh bound_output_fresh)
  qed
}
thus ?thesis by blast
qed

lemma tau_no_provenance'':
  shows "\<Psi> \<rhd> P \<longmapsto> \<pi> @ R_tau Rs \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto> None @ R_tau Rs"
  using tau_no_provenance'
  by(auto simp add: residual_inject)

lemma tau_induct[consumes 1, case_names c_case c_par1 c_par2 c_comm1 c_comm2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     r_case: "\<And>\<Psi> P P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                                    Prop C \<Psi> (Cases Cs) P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P P';
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q Q';
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';  extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_scope: "\<And>\<Psi> P P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; x \<sharp> \<Psi>; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P'"
  shows "Prop C \<Psi> P P'"
using Trans
proof(nominal_induct \<Psi> P \<pi> Rs=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: semantics.strong_induct)
  case(c_input M K xvec N Tvec P C)
  thus ?case by(simp add: residual_inject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(simp add: residual_inject)
next
  case(Case \<Psi> P \<phi> Cs C P')
  thus ?case
    by(drule_tac tau_no_provenance') (force intro!: r_case simp add: residual_inject)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q C P'')
  thus ?case  
    by(auto simp add: residual_inject intro!: r_par1 dest: tau_no_provenance'')
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P C Q'')
  thus ?case
    by(auto simp add: residual_inject intro!: r_par2 dest: tau_no_provenance'')
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C PQ)
  thus ?case by(force intro!: r_comm1 simp add: residual_inject)
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec Q' C P')
  thus ?case
    by(force intro!: r_comm2 simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec N P' x yvec C P'')
  thus ?case by(simp add: residual_inject)
next
  case(c_scope \<Psi> P \<alpha> P' x C P'')
  thus ?case
    by(force simp add: residual_inject intro!: r_scope dest: tau_no_provenance'')
next
  case(Bang \<Psi> P C P')
  thus ?case
    by(force simp add: residual_inject intro!: r_bang dest: tau_no_provenance'')
qed

lemma semantics_frame_induct[consumes 3, case_names c_alpha c_input c_output c_case c_par1 c_par2 c_comm1 c_comm2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 ('a, 'b, 'c) residual \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> 'e::fs_name \<Rightarrow> bool"
  and   C    :: "'d::fs_name"
  and   D    :: "'e::fs_name"  

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     r_alpha: "\<And>\<Psi> P A\<^sub>P \<Psi>\<^sub>P \<pi> p Rs C D. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C;
                                         set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p;
                                          Prop C \<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> Rs (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P) (p\<bullet>D)"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C D.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>))
                              (K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (P[xvec::=Tvec])) ([]) (\<one>) D"
  and     r_output: "\<And>\<Psi> M K N P C D. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) (K\<langle>N\<rangle> \<prec> P) ([]) (\<one>) D"
  and     r_case: "\<And>\<Psi> P \<pi> Rs \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C D. Prop C \<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) Rs ([]) (\<one>) D"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D; distinct(bn \<alpha>);
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) (\<alpha> \<prec> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q D; distinct(bn \<alpha>);
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) ((M\<lparr>N\<rparr>) \<prec> P') A\<^sub>P \<Psi>\<^sub>P D;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q D; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K;  distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>N\<rparr> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q D;
                    distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_open: "\<And>\<Psi> P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C D.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>(Some \<pi>) @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C D. Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec; xvec \<sharp>* yvec; distinct xvec; distinct yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<pi>; yvec \<sharp>* \<Psi>\<^sub>P;
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* \<pi>; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (x#A\<^sub>P) \<Psi>\<^sub>P D"
  and     r_scope: "\<And>\<Psi> P \<pi> \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C D.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C D. Prop C \<Psi> P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D;
                     x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; distinct(bn \<alpha>);
                     bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P D"
  and     r_bang:    "\<And>\<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P C D.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C D. Prop C \<Psi> (P \<parallel> !P) \<pi> Rs A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>) D; \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) Rs ([]) (\<one>) D"
  shows "Prop C \<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D"
using Trans FrP `distinct A\<^sub>P`
proof(nominal_induct  avoiding: A\<^sub>P \<Psi>\<^sub>P C D rule: semantics.strong_induct)
  case(c_input \<Psi> K M xvec N Tvec P A\<^sub>P \<Psi>\<^sub>P C D)
  from `extract_frame (M\<lparr>\<lambda>*xvec N\<rparr>.P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
  have "A\<^sub>P = []" and "\<Psi>\<^sub>P = \<one>"
    by auto
  with `\<Psi> \<turnstile> K \<leftrightarrow> M` `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
       `xvec \<sharp>* \<Psi>` `xvec \<sharp>* M` `xvec \<sharp>* K` `xvec \<sharp>* C`
  show ?case by(blast intro: r_input)
next
  case(Output \<Psi> M K N P A\<^sub>P \<Psi>\<^sub>P)
  from `extract_frame (M\<langle>N\<rangle>.P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
  have "A\<^sub>P = []" and "\<Psi>\<^sub>P = \<one>"
    by auto
  with `\<Psi> \<turnstile> M \<leftrightarrow> K` show ?case
    by(blast intro: r_output)
next
  case(Case \<Psi> P \<pi> Rs \<phi> Cs A\<^sub>c\<^sub>P \<Psi>\<^sub>c\<^sub>P C D)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, \<pi>, Rs, C,\<phi>,Cs)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Rs" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* \<pi>" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>P \<sharp>* Cs"
    by simp+
  note `\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs` FrP `distinct A\<^sub>P`
  moreover from FrP `distinct A\<^sub>P` `\<And>A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D` 
  have "\<And>C D. Prop C \<Psi> P \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D" by simp
  moreover note `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
  moreover from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)" by(metis guarded_stat_eq)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Rs` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<phi>` `A\<^sub>P \<sharp>* Cs`
  ultimately have "Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) Rs ([]) (\<one>) D"
    by(rule_tac r_case)
  thus ?case using `extract_frame(Cases Cs) = \<langle>A\<^sub>c\<^sub>P, \<Psi>\<^sub>c\<^sub>P\<rangle>` by simp
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C D)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, \<alpha>, \<pi>, P', A\<^sub>Q, A\<^sub>P\<^sub>Q, C, \<Psi>\<^sub>Q)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* P'"
    and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<pi>"
    by simp+

  have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` FrP have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+
  
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` FrP `distinct A\<^sub>P` FrQ `distinct A\<^sub>Q`

  moreover from FrP `distinct A\<^sub>P` `\<And>A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D`
  have "\<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D" by simp

  moreover note `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<pi>`
                `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* \<pi>` `distinct(bn \<alpha>)`
                `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`  `bn \<alpha> \<sharp>* Q`  `bn \<alpha> \<sharp>* subject \<alpha>`  `bn \<alpha> \<sharp>* \<Psi>\<^sub>P`  `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q`  `bn \<alpha> \<sharp>* \<pi>` 
                `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C` `bn \<alpha> \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) (\<alpha> \<prec> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) (p\<bullet>D)"
    by(rule_tac r_par1)
  with `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>`
       `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* \<pi>`
       S `distinct_perm p` Aeq
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) (\<alpha> \<prec> (P' \<parallel> Q)) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) (p\<bullet>p\<bullet>D)"
    by(rule_tac r_alpha) (assumption | simp add: eqvts map_option_append_fresh)+
  with \<Psi>eq Aeq `distinct_perm p` show ?case by(simp add: eqvts)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C D)
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, \<alpha>, Q', A\<^sub>P, A\<^sub>P\<^sub>Q, C, \<Psi>\<^sub>P, \<pi>)"
    by(rule fresh_frame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>Q \<sharp>* Q'" and "A\<^sub>Q \<sharp>* \<pi>"
    and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* C" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  from `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* A\<^sub>Q"by simp
  have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain)
  from `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<alpha>` FrQ have "bn \<alpha> \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = ((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` FrP `distinct A\<^sub>P` FrQ `distinct A\<^sub>Q`

  moreover from FrQ `distinct A\<^sub>Q` `\<And>A\<^sub>Q \<Psi>\<^sub>Q C D. \<lbrakk>extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q\<rbrakk> \<Longrightarrow> Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q D`
  have "\<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q D" by simp

  moreover note `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<pi>`
                `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* \<pi>` `distinct(bn \<alpha>)`
                `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`  `bn \<alpha> \<sharp>* Q`  `bn \<alpha> \<sharp>* subject \<alpha>`  `bn \<alpha> \<sharp>* \<Psi>\<^sub>P`  `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* \<pi>`
                `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C` `bn \<alpha> \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) (p\<bullet>D)"
    by(rule_tac r_par2)

  with `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>`
       `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* \<pi>`
       S `distinct_perm p` Aeq
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) (p\<bullet>p\<bullet>D)"
    by(rule_tac r_alpha) (assumption | simp add: eqvts map_option_append_fresh)+
  with \<Psi>eq Aeq `distinct_perm p` show ?case by(simp add: eqvts)
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec xvec Q' A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C D)
  from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
                `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  with `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct(A\<^sub>P@A\<^sub>Q)` `distinct A\<^sub>P\<^sub>Q`
  obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinct_perm p"
             and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = p \<bullet> (A\<^sub>P@A\<^sub>Q)"
    by(rule_tac frame_chain_eq') (assumption | simp)+  
  moreover from c_comm1 have  "Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) (p\<bullet>D)"
    by(rule_tac r_comm1)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* xvec`
                `A\<^sub>Q \<sharp>* xvec` `A\<^sub>P \<sharp>* P'` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P \<sharp>* Q'` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q`
                `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) (p\<bullet>p\<bullet>D)"
    by(rule_tac r_alpha) auto
  with \<Psi>eq Aeq `distinct_perm p` show ?case by simp
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec Q' A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C D)
  from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
                `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  with `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct(A\<^sub>P@A\<^sub>Q)` `distinct A\<^sub>P\<^sub>Q`
  obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinct_perm p"
             and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = p \<bullet> (A\<^sub>P@A\<^sub>Q)"
    by(rule_tac frame_chain_eq') (assumption | simp)+
  moreover from c_comm2 have  "Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) (p\<bullet>D)"
    by(rule_tac r_comm2)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* xvec`
                `A\<^sub>Q \<sharp>* xvec` `A\<^sub>P \<sharp>* P'` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P \<sharp>* Q'` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q`
                `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) None (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) (p\<bullet>p\<bullet>D)"
    by(rule_tac r_alpha) auto
  with \<Psi>eq Aeq `distinct_perm p` show ?case by simp
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P C D)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, M, xvec, yvec, N, P', A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P, C, x, \<pi>)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* xvec"and "A\<^sub>P \<sharp>* yvec" and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* \<pi>"
    and "A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* C" and "x \<sharp> A\<^sub>P"
    by simp+

  from `xvec \<sharp>* P` `A\<^sub>P \<sharp>* xvec` FrP have "xvec \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)
  from `yvec \<sharp>* P` `A\<^sub>P \<sharp>* yvec` FrP have "yvec \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>` FrP
  have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>"
    by simp
  moreover from `x \<sharp> A\<^sub>P` `distinct A\<^sub>P` have "distinct(x#A\<^sub>P)" by simp
  ultimately obtain p where S: "set p \<subseteq> set (x#A\<^sub>P) \<times> set (p \<bullet> (x#A\<^sub>P))" and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>x\<^sub>P = p \<bullet> \<Psi>\<^sub>P" and Aeq: "A\<^sub>x\<^sub>P = (p \<bullet> x)#(p \<bullet> A\<^sub>P)"
    using `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P``x \<sharp> A\<^sub>x\<^sub>P` `distinct A\<^sub>x\<^sub>P`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  note `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` FrP `distinct A\<^sub>P`
  moreover from FrP `distinct A\<^sub>P` `\<And>A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D`
  have "\<And>C D. Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D" by simp
  moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` `x \<in> supp N` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* yvec` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* \<pi>`
                `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P`  `xvec \<sharp>* M`  `xvec \<sharp>* \<Psi>\<^sub>P` `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P`  `yvec \<sharp>* M`  `yvec \<sharp>* \<Psi>\<^sub>P`   `yvec \<sharp>* \<pi>` 
                `A\<^sub>P \<sharp>* C` `x \<sharp> C` `xvec \<sharp>* C` `yvec \<sharp>* C` `xvec \<sharp>* yvec` `distinct xvec` `distinct yvec`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (x#A\<^sub>P) \<Psi>\<^sub>P (p\<bullet>D)"
    by(rule_tac r_open)  
  with `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* yvec` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>` `x \<sharp> A\<^sub>x\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P` `x \<sharp> A\<^sub>P`
       `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> C` `x \<sharp> xvec` `x \<sharp> yvec` Aeq
       S `distinct_perm p`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (p \<bullet> (x#A\<^sub>P)) (p \<bullet> \<Psi>\<^sub>P) (p \<bullet> p \<bullet> D)"
    by(rule_tac A\<^sub>P="x#A\<^sub>P" in r_alpha) (assumption | simp add: abs_fresh fresh_star_def bound_output_fresh)+
  with \<Psi>eq Aeq `distinct_perm p` show ?case by(simp add: eqvts)
next
  case(c_scope \<Psi> P \<pi> \<alpha> P' x A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P C D)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, \<pi>, \<alpha>, P', A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P, C, x)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* P'" and "A\<^sub>P \<sharp>* \<pi>"
    and "A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* C" and "x \<sharp> A\<^sub>P"
    by simp+

  from `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` FrP have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>` FrP
  have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>"
    by simp
  moreover from `x \<sharp> A\<^sub>P` `distinct A\<^sub>P` have "distinct(x#A\<^sub>P)" by simp
  ultimately obtain p where S: "set p \<subseteq> set (x#A\<^sub>P) \<times> set (p \<bullet> (x#A\<^sub>P))" and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>x\<^sub>P = p \<bullet> \<Psi>\<^sub>P" and Aeq: "A\<^sub>x\<^sub>P = (p \<bullet> x)#(p \<bullet> A\<^sub>P)"
    using `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P``x \<sharp> A\<^sub>x\<^sub>P` `distinct A\<^sub>x\<^sub>P`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` FrP `distinct A\<^sub>P`
  moreover from FrP `distinct A\<^sub>P` `\<And>A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D`
  have "\<And>C D. Prop C \<Psi> P \<pi> (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P D" by simp
  moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* \<pi>` `distinct(bn \<alpha>)`
                `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`  `bn \<alpha> \<sharp>* subject \<alpha>`  `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<pi>` `A\<^sub>P \<sharp>* C` `x \<sharp> C` `bn \<alpha> \<sharp>* C` 
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P (p\<bullet>D)"
    by(rule_tac r_scope)
  with `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P` `A\<^sub>P \<sharp>* C` `x \<sharp> A\<^sub>x\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P` `A\<^sub>P \<sharp>* \<pi>` `x \<sharp> A\<^sub>P`
       `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> C` Aeq
       S `distinct_perm p`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (p \<bullet> (x#A\<^sub>P)) (p \<bullet> \<Psi>\<^sub>P) (p\<bullet>p\<bullet>D)"
    by(rule_tac A\<^sub>P="x#A\<^sub>P" in r_alpha) (assumption | simp add: map_option_append_fresh | simp add: abs_fresh fresh_star_def | force)+
  with \<Psi>eq Aeq `distinct_perm p` show ?case by(simp add: eqvts)
next
  case(Bang \<Psi> P \<pi> Rs A\<^sub>b\<^sub>P \<Psi>\<^sub>b\<^sub>P C)

  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, Rs, C, \<pi>)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Rs" and "A\<^sub>P \<sharp>* C"  and "A\<^sub>P \<sharp>* \<pi>" 
    by simp+

  note `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs` `guarded P` FrP `distinct A\<^sub>P`
  moreover from FrP have "extract_frame (P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by simp
  with `distinct A\<^sub>P` `\<And>A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>extract_frame (P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) \<pi> Rs A\<^sub>P \<Psi>\<^sub>P D`
  have "\<And>C D. Prop C \<Psi> (P \<parallel> !P) \<pi> Rs A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>) D" by simp
  moreover from `guarded P` FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)" by(metis guarded_stat_eq)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Rs` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* C`
  ultimately have "Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) Rs ([]) (\<one>) D"
    by(rule_tac r_bang) 
  thus ?case using `extract_frame(!P) = \<langle>A\<^sub>b\<^sub>P, \<Psi>\<^sub>b\<^sub>P\<rangle>` by simp
qed

lemma semantics_frame_induct'[consumes 5, case_names c_alpha c_frame_alpha c_input c_output c_case c_par1 c_par2 c_comm1 c_comm2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a action \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     r_alpha: "\<And>\<Psi> P \<pi> \<alpha> P' p A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P;
                                           bn \<alpha> \<sharp>* C; bn \<alpha> \<sharp>* (p \<bullet> \<alpha>); bn \<alpha> \<sharp>* \<pi>; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C; A\<^sub>P \<sharp>* \<pi>;
                                           set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinct_perm p;
                                           bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow>
                                           Prop C \<Psi> P \<pi> (p \<bullet> \<alpha>) (p \<bullet> P') A\<^sub>P \<Psi>\<^sub>P"
  and     r_frame_alpha: "\<And>\<Psi> P \<pi> A\<^sub>P \<Psi>\<^sub>P p \<alpha> P' C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C; A\<^sub>P \<sharp>* \<pi>;
                                                set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p; A\<^sub>P \<sharp>* subject \<alpha>;
                                                Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> \<alpha> P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>))
                              (K\<lparr>(N[xvec::=Tvec])\<rparr>) (P[xvec::=Tvec]) ([]) (\<one>)"
  and     r_output: "\<And>\<Psi> M K N P C. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) (K\<langle>N\<rangle>) P ([]) (\<one>)"
  and     r_case: "\<And>\<Psi> P \<pi> \<alpha> P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) \<alpha> P' ([]) (\<one>)"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) \<alpha> (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> \<alpha> Q' A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) (M\<lparr>N\<rparr>) P' A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    distinct xvec;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q' A\<^sub>Q \<Psi>\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (Some(\<langle>A\<^sub>P;yvec, K\<rangle>)) (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (Some(\<langle>A\<^sub>Q; zvec, M\<rangle>)) (K\<lparr>N\<rparr>) Q' A\<^sub>Q \<Psi>\<^sub>Q;
                    distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) None (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_open: "\<And>\<Psi> P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P y C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec; xvec \<sharp>* yvec; distinct xvec; distinct yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<pi>;
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* \<pi>; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C;
                     y \<noteq> x; y \<sharp> \<Psi>; y \<sharp> P; y \<sharp> M; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> N; y \<sharp> P'; y \<sharp> A\<^sub>P; y \<sharp> \<Psi>\<^sub>P; y \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>) ([(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_scope: "\<And>\<Psi> P \<pi> \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                     x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>;
                     bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) \<alpha> (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_bang:    "\<And>\<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) \<alpha> P' ([]) (\<one>)"
  shows "Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP `distinct A\<^sub>P` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
proof(nominal_induct \<Psi> P \<pi> Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P D=="()" avoiding: C \<alpha> P' rule: semantics_frame_induct)
  case c_alpha 
  thus ?case using r_frame_alpha
    by auto
next
  case c_input
  thus ?case using r_input
    by(auto simp add: residual_inject)
next
  case c_output
  thus ?case using r_output
    by(auto simp add: residual_inject)
next
  case c_case
  thus ?case using r_case
    by(auto simp add: residual_inject)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C \<alpha>' P'')
  note `\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> Q)" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (P' \<parallel> Q)" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P' \<parallel> Q)"
    by(rule residual_eq)
    
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` `A\<^sub>P \<sharp>* \<alpha>`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P" by(rule_tac c_par1) auto

  moreover note `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* C` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* \<pi>` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C`
                `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) \<alpha> (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac r_par1)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* \<pi>` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> Q)` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<pi>` \<alpha>Eq `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<alpha>'` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* P'` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C`
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac r_alpha) (auto simp add: map_option_append_fresh)
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C \<alpha>' Q'')
  note `\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> Q''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> Q')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> Q'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and Q'eq: "Q'' = p \<bullet> (P \<parallel> Q')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P \<parallel> Q')"
    by(rule residual_eq)
    
  note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` `A\<^sub>Q \<sharp>* \<alpha>`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> \<alpha> Q' A\<^sub>Q \<Psi>\<^sub>Q" by(rule_tac c_par2) auto

  moreover note `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>Q \<sharp>* C` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C`
                `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac r_par2) (auto simp add: map_option_append_fresh)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> Q')` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` \<alpha>Eq `bn \<alpha> \<sharp>* \<alpha>'` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* C`
  have "Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac r_alpha) (auto simp add: map_option_append_fresh)
  with \<alpha>Eq Q'eq `distinct_perm p` show ?case by simp
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C \<alpha> P'')
  moreover from `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q' = \<alpha> \<prec> P''`
  have "\<alpha> = \<tau>" and "P'' = \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q'" and "bn \<alpha> = []"
    by(auto simp add: residual_inject)
  ultimately show ?case using r_comm1
    by auto
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C \<alpha> Q'')
  moreover from `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q' = \<alpha> \<prec> Q''`
  have "\<alpha> = \<tau>" and "Q'' = \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q'" and "bn \<alpha> = []"
    by(auto simp add: residual_inject)  
  ultimately show ?case using r_comm2
    by auto
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C \<alpha> P'')
  note `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
  moreover from `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>` have "(xvec@x#yvec) \<sharp>* (bn \<alpha>)"
    by auto
  moreover from `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `distinct xvec` `distinct yvec`
  have "distinct(xvec@x#yvec)"
    by(auto simp add: fresh_star_def) (simp add: fresh_def name_list_supp)
  moreover note `distinct(bn \<alpha>)`
  moreover from `xvec \<sharp>* M` `x \<sharp> M` `yvec \<sharp>* M` have "(xvec@x#yvec) \<sharp>* M" by auto
  hence "(xvec@x#yvec) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by auto
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P'')" by simp
  ultimately obtain p where S: "(set p) \<subseteq> (set(xvec@x#yvec)) \<times> (set(p \<bullet> (xvec@x#yvec)))" and "distinct_perm p"
             and \<alpha>eq: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>" and P'eq: "P'' = (p \<bullet> P')"
             and A: "(xvec@x#yvec) \<sharp>* ((p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>)"
             and B: "(p \<bullet> (xvec@x#yvec)) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)"
             and C: "(p \<bullet> (xvec@x#yvec)) \<sharp>* P'"
    by(rule_tac residual_eq) (assumption | simp)+
  note `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<in> (supp N)`

  moreover {
    fix C
    from `xvec \<sharp>* M` `yvec \<sharp>* M` have "(xvec@yvec) \<sharp>* M" by simp
    moreover from `distinct xvec` `distinct yvec` `xvec \<sharp>* yvec` have "distinct(xvec@yvec)"
      by auto (simp add: fresh_star_def name_list_supp fresh_def) 
    ultimately have "Prop C \<Psi> P (Some \<pi>) (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P" using `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* yvec` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* \<pi>`
      by(rule_tac c_open) auto
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> xvec" and "y \<sharp> yvec" and "y \<sharp> \<alpha>" and "y \<sharp> P'" and "y \<sharp> A\<^sub>P" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> C" and "y \<sharp> p" and "y \<sharp> \<pi>"
    by(generate_fresh "name") auto
  moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* M` `xvec \<sharp>* \<pi>`
                 `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* \<pi>` `yvec \<sharp>* C` `x \<sharp> C` `xvec \<sharp>* C` `distinct xvec` `distinct yvec`
                 `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `x \<sharp> A\<^sub>P` `xvec \<sharp>* yvec` `xvec \<sharp>* \<Psi>\<^sub>P`
                 `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* yvec` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>` 
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>) ([(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac r_open)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> M) = [(x, y)] \<bullet> p \<bullet> M"
    by(subst perm_compose[symmetric]) simp
  with `y \<sharp> M` `x \<sharp> \<alpha>` \<alpha>eq `y \<sharp> p` `x \<sharp> M` have D: "(([(x, y)] \<bullet> p) \<bullet> M) = p \<bullet> M"
    by(auto simp add: eqvts fresh_chain_simps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> xvec) = [(x, y)] \<bullet> p \<bullet> xvec"
    by(subst perm_compose[symmetric]) simp
  with `y \<sharp> xvec` `x \<sharp> \<alpha>` \<alpha>eq `y \<sharp> p` `x \<sharp> xvec` have E: "(([(x, y)] \<bullet> p) \<bullet> xvec) = p \<bullet> xvec"
    by(auto simp add: eqvts fresh_chain_simps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> yvec) = [(x, y)] \<bullet> p \<bullet> yvec"
    by(subst perm_compose[symmetric]) simp
  with `y \<sharp> yvec` `x \<sharp> \<alpha>` \<alpha>eq `y \<sharp> p` `x \<sharp> yvec` have F: "(([(x, y)] \<bullet> p) \<bullet> yvec) = p \<bullet> yvec"
    by(auto simp add: eqvts fresh_chain_simps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> x) = [(x, y)] \<bullet> p \<bullet> x"
    by(subst perm_compose[symmetric]) simp
  with `y \<noteq> x` `y \<sharp> p` have G: "(([(x, y)] \<bullet> p) \<bullet> y) = p \<bullet> x"
    apply(simp add: fresh_chain_simps calc_atm)
    apply(subgoal_tac "y \<noteq> p \<bullet> x")
    apply(clarsimp)
    using A \<alpha>eq
    apply(simp add: eqvts)
    apply(subst fresh_atm[symmetric])
    apply(simp only: fresh_chain_simps)
    by simp
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> N"
    by(subst perm_compose[symmetric]) simp
  with `y \<sharp> N` `x \<sharp> \<alpha>` `y \<sharp> p` \<alpha>eq have H: "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> N) = p \<bullet> N"
    by(auto simp add: eqvts fresh_chain_simps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') = [(x, y)] \<bullet> p \<bullet> P'"
    by(subst perm_compose[symmetric]) simp
  with `y \<sharp> P'` `x \<sharp> P''` `y \<sharp> p` P'eq have I: "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') = p \<bullet> P'"
    by(auto simp add: eqvts fresh_chain_simps)
  from `y \<sharp> p` `y \<noteq> x` have "y \<noteq> p \<bullet> x"
    apply(subst fresh_atm[symmetric])
    apply(simp only: fresh_chain_simps)
    by simp
  moreover from S have "([(x, y)] \<bullet> set p) \<subseteq> [(x, y)] \<bullet> (set(xvec@x#yvec) \<times> set(p \<bullet> (xvec@x#yvec)))"
    by(simp)
  with `y \<noteq> p \<bullet> x` `(([(x, y)] \<bullet> p) \<bullet> y) = p \<bullet> x` `x \<sharp> xvec` `y \<sharp> xvec` `x \<sharp> yvec` `y \<sharp> yvec` `y \<sharp> p` `x \<sharp> \<alpha>` \<alpha>eq have 
    "set([(x, y)] \<bullet> p) \<subseteq> set(xvec@y#yvec) \<times> set(([(x, y)] \<bullet> p) \<bullet> (xvec@y#yvec))"
    by(simp add: eqvts calc_atm perm_compose)
  moreover note `xvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `yvec \<sharp>* P` `xvec \<sharp>* M` `yvec \<sharp>* M`  `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<pi>` 
                `yvec \<sharp>* C`  S `distinct_perm p` `x \<sharp> C` `xvec \<sharp>* C` `xvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* \<Psi>\<^sub>P` `x \<sharp> \<Psi>`
                `A\<^sub>P \<sharp>* xvec` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* yvec` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>` `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> M` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* N`
                 A B C  \<alpha>eq `A\<^sub>P \<sharp>* \<alpha>` `y \<sharp> \<Psi>` `y \<noteq> x` `y \<sharp> P` `y \<sharp> M` `y \<sharp> \<pi>` `y \<sharp> \<Psi>\<^sub>P` `y \<sharp> C` `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>` `y \<sharp> \<alpha>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `y \<sharp> A\<^sub>P` `y \<sharp> N` `A\<^sub>P \<sharp>* P'` `y \<sharp> P'` `A\<^sub>P \<sharp>* C` P'eq
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) (([(x, y)] \<bullet> p) \<bullet> (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>)) (([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac \<alpha>="M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>" in r_alpha)
    (assumption | simp add: eqvts fresh_left calc_atm abs_fresh frame_fresh_chain | metis UnE fresh_star_list)+
  with \<alpha>eq P'eq D E F G H I show ?case 
    by(simp add: eqvts)
next
 case(c_scope \<Psi> P \<pi> \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C \<alpha>' P'')
  note `\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P') = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (\<lparr>\<nu>x\<rparr>P')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (\<lparr>\<nu>x\<rparr>P')"
    by(rule residual_eq)
    
  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C \<Psi> P \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P" by(rule_tac c_scope) auto

  moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<pi>`
                `x \<sharp> C` `bn \<alpha> \<sharp>* C` `distinct(bn \<alpha>)` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
                `distinct A\<^sub>P` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* C`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) \<alpha> (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac r_scope)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (\<lparr>\<nu>x\<rparr>P')` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* \<alpha>'` \<alpha>Eq `x \<sharp> \<alpha>'` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* \<alpha>'` `x \<sharp> \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* P'` `x \<sharp> C` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>` `bn \<alpha> \<sharp>* \<pi>`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) (p \<bullet> \<alpha>) (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))  (x#A\<^sub>P) \<Psi>\<^sub>P" 
    by(rule_tac r_alpha) (simp add: abs_fresh map_option_append_fresh)+
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(c_bang \<Psi> P A\<^sub>P \<Psi>\<^sub>P C \<alpha> P')
  thus ?case by(rule_tac r_bang) auto 
qed

lemma input_frame_induct[consumes 3, case_names c_alpha c_input c_case c_par1 c_par2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> 'e::fs_name \<Rightarrow> bool"
  and   C    :: "'d::fs_name"
  and   D    :: "'e::fs_name"  

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     r_alpha: "\<And>\<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P p C D. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* C;
                                            set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p;
                                             Prop C \<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P D\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> M N P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P) (p \<bullet> D)"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C D.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>))
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec]) ([]) (\<one>) D"
  and     r_case: "\<And>\<Psi> P \<pi> M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C D. Prop C \<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P D;
                                              (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                              A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) M N P' ([]) (\<one>) D"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P D;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) M N (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<pi> M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> M N Q' A\<^sub>Q \<Psi>\<^sub>Q D;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) M N (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_scope: "\<And>\<Psi> P \<pi> M N P' x A\<^sub>P \<Psi>\<^sub>P C D.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C D. Prop C \<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P D; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; 
                     x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* C; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) M N (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P D"
  and     r_bang:    "\<And>\<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P C D.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                      \<And>C D. Prop C \<Psi> (P \<parallel> !P) \<pi> M N P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>) D; \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) M N P' ([]) (\<one>) D"
  shows "Prop C \<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P D"
using Trans FrP `distinct A\<^sub>P`
apply(nominal_induct \<Psi> P \<pi> Rs=="M\<lparr>N\<rparr> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P D avoiding: C arbitrary: P' rule: semantics_frame_induct)
using r_alpha r_input r_case r_par1 r_par2 r_scope r_bang
by(auto simp add: residual_inject)

lemma output_frame_induct[consumes 3, case_names c_alpha c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) bound_output \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> 'e::fs_name \<Rightarrow> bool"
  and   C    :: "'d::fs_name"
  and   D    :: "'e::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ R_out M B"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     r_alpha: "\<And>\<Psi> P \<pi> M A\<^sub>P \<Psi>\<^sub>P p B C D. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C;
                                         set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p;
                                          Prop C \<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P D\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<pi> M B (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P) (p\<bullet>D)"
  and     r_output: "\<And>\<Psi> M K N P C D. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) K (N \<prec>' P) ([]) (\<one>) D"
  and     r_case: "\<And>\<Psi> P \<pi> M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C D. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ (R_out M B); extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C D. Prop C \<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P D;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (map_option (F_assert o push_prov) \<pi>) M B ([]) (\<one>) D"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<pi> M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P D;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_end_prov_option \<pi> A\<^sub>Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q M \<pi> xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C D.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C D. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q') A\<^sub>Q \<Psi>\<^sub>Q D;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* \<pi>;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* \<pi>;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* \<pi>;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (append_at_front_prov_option \<pi> A\<^sub>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) D"
  and     r_open: "\<And>\<Psi> P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C D.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C D. Prop C \<Psi> P (Some \<pi>) M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P D; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P;  xvec \<sharp>* \<pi>; 
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* \<pi>; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (Some(\<lparr>\<nu>x\<rparr>\<pi>)) M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P') (x#A\<^sub>P) \<Psi>\<^sub>P D"
  and     r_scope: "\<And>\<Psi> P \<pi> M xvec N P' x A\<^sub>P \<Psi>\<^sub>P C D.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C D. Prop C \<Psi> P \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P D;
                     x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* \<pi>;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<pi>;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (map_option (F_res x) \<pi>) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P D"
  and     r_bang:    "\<And>\<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P C D.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ R_out M B; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C D. Prop C \<Psi> (P \<parallel> !P) \<pi> M B A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>) D; \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) M B ([]) (\<one>) D"
  shows "Prop C \<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P D"
proof -
  {
    fix B
    assume "\<Psi> \<rhd> P \<longmapsto>\<pi> @ R_out M B"
    hence "Prop C \<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P D" using FrP `distinct A\<^sub>P`
    proof(nominal_induct \<Psi> P \<pi> Rs=="R_out M B" A\<^sub>P \<Psi>\<^sub>P D avoiding: C arbitrary: B rule: semantics_frame_induct)
      case c_alpha
      thus ?case
        by(auto intro: r_alpha) 
    next
      case c_input
      thus ?case by(simp add: residual_inject)
    next
      case c_output
      thus ?case by(force intro: r_output simp add: residual_inject)
    next
      case c_case
      thus ?case by(force intro: r_case simp add: residual_inject)
    next
      case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C B)
      thus ?case using r_par1
        by(auto simp add: residual_inject action.inject)
    next
      case c_par2
      thus ?case using r_par2
	by(auto simp add: residual_inject action.inject)
    next
      case c_comm1
      thus ?case by(simp add: residual_inject)
    next
      case c_comm2
      thus ?case by(simp add: residual_inject)
    next
      case c_open
      thus ?case by(force intro: r_open simp add: residual_inject)
    next
      case c_scope
      thus ?case using r_scope
        by(force simp add: residual_inject action.inject)
    next
      case c_bang
      thus ?case by(force intro: r_bang simp add: residual_inject)
    qed
  }
  with Trans show ?thesis by(simp add: residual_inject)
qed

lemma tau_frame_induct[consumes 3, case_names c_alpha c_case c_par1 c_par2 c_comm1 c_comm2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     r_alpha: "\<And>\<Psi> P P' A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* C;
                                        set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P); distinct_perm p;
                                         Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     r_case: "\<And>\<Psi> P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P;
                                          (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                          A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) P' ([]) (\<one>)"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>None @ \<tau> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>None @ \<tau> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q Q' A\<^sub>Q \<Psi>\<^sub>Q; 
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P;yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q';
                    A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_scope: "\<And>\<Psi> P P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P; x \<sharp> \<Psi>;
                     x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* C; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_bang:    "\<And>\<Psi> P P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>None @ \<tau> \<prec> P'; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P' ([]) (\<one>)"
  shows "Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P"
proof -
  from Trans have "\<Psi> \<rhd> P \<longmapsto> None @ \<tau> \<prec> P'"
    by(subst tau_no_provenance[symmetric])
  thus ?thesis using FrP `distinct A\<^sub>P`
  proof(nominal_induct \<Psi> P \<pi>=="None::'a frame frame option" Rs=="\<tau> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P D=="()" avoiding: C arbitrary: P' rule: semantics_frame_induct)
    case c_alpha
    thus ?case by(force intro: r_alpha simp add: residual_inject)
  next
    case c_case
    thus ?case by(force intro: r_case simp add: residual_inject)
  next
    case c_par1
    thus ?case by(force intro: r_par1 simp add: residual_inject)
  next
    case c_par2
    thus ?case by(force intro: r_par2 simp add: residual_inject)
  next
    case c_comm1
    thus ?case by(force intro: r_comm1 simp add: residual_inject)
  next
    case c_comm2
    thus ?case by(force intro: r_comm2 simp add: residual_inject)
  next
    case c_scope
    thus ?case by(force intro: r_scope simp add: residual_inject)
  next
    case c_bang
    thus ?case by(force intro: r_bang simp add: residual_inject)
  qed
qed

lemma list_mem_fresh[dest]:
  fixes xvec :: "name list"
  and Cs :: "'t::fs_name list"
  assumes "P \<in> set Cs"
  and "xvec \<sharp>* Cs"
  shows "xvec \<sharp>* P"
  using assms
  by(induct Cs) auto

lemma trans_fresh_provenance:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ Rs"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* \<pi>"
  using assms
  by(nominal_induct avoiding: xvec rule: semantics.strong_inducts)
    (auto simp add: map_option_append_fresh frame_chain_fresh_chain frame_chain_fresh_chain')

lemma input_fresh_derivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> N"

  shows "x \<sharp> P'"
proof -
  have "bn(M\<lparr>N\<rparr>) \<sharp>* subject(M\<lparr>N\<rparr>)" and "distinct(bn(M\<lparr>N\<rparr>))" by simp+
  with `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` show ?thesis using `x \<sharp> P` `x \<sharp> N`
  proof(nominal_induct \<Psi> P \<pi> \<alpha>=="M\<lparr>N\<rparr>" P' avoiding: x rule: semantics_induct)
    case(c_alpha \<Psi> P \<alpha> P' p x)
    thus ?case by simp
  next
    case(c_input \<Psi> M' K xvec N' Tvec P x)
    from `K\<lparr>(N'[xvec::=Tvec])\<rparr> = M\<lparr>N\<rparr>` have "M = K" and Neq_n': "N = N'[xvec::=Tvec]" by(simp add: action.inject)+ 
    note `length xvec = length Tvec` `distinct xvec` then
    moreover have "x \<sharp> Tvec" using `set xvec \<subseteq> supp N'` `x \<sharp> N` Neq_n'
      by(blast intro: subst_term.subst3)
    moreover from `xvec \<sharp>* x` `x \<sharp> M'\<lparr>\<lambda>*xvec N'\<rparr>.P`
    have "x \<sharp> P" by(simp add: input_chain_fresh) (simp add: name_list_supp fresh_def)
    ultimately show ?case using `xvec \<sharp>* x` by auto
  next
    case(c_output \<Psi> M  K N P x)
    thus ?case by simp
  next
    case(c_case \<Psi> P \<pi> P' \<phi> Cs x)
    thus ?case
      by(induct Cs, auto)
  next
    case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> P' xvec Q x)
    thus ?case by simp
  next
    case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> Q' xvec P x)
    thus ?case by simp
  next
    case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q x)
    thus ?case by simp
  next
    case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xwec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q x)
    thus ?case by simp
  next
    case(c_open \<Psi> P M xvec yvec N P' x y)
    thus ?case by simp
  next
    case(c_scope \<Psi> P P' x y)
    thus ?case by(simp add: abs_fresh)
  next
    case(c_bang \<Psi> P P' x)
    thus ?case by simp
  qed
qed
  
lemma input_fresh_chain_derivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* N"
  
  shows "xvec \<sharp>* P'"
using assms
by(induct xvec)
  (auto intro: input_fresh_derivative)

lemma output_fresh_derivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"
  and     "x \<sharp> P"
  and     "x \<sharp> xvec"

  shows "x \<sharp> N"
  and   "x \<sharp> P'"
proof -
  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  moreover from `xvec \<sharp>* M` have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from `distinct xvec` have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))" by simp
  ultimately show "x \<sharp> N" using `x \<sharp> P` `x \<sharp> xvec`
  proof(nominal_induct \<Psi> P \<pi> \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: x arbitrary: M xvec N rule: semantics_induct)
    case(c_alpha \<Psi> P \<pi> \<alpha> P' p x M xvec N)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by(simp add: fresh_star_bij)
    with `distinct_perm p` have "\<alpha>  = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>" by simp
    moreover from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `x \<sharp> xvec` have "x \<sharp> (bn(p \<bullet> \<alpha>))" by simp
    with `(bn \<alpha>) \<sharp>* x` `x \<sharp> xvec` S have "x \<sharp> (p \<bullet> xvec)"
      by(drule_tac pt_fresh_bij1[OF pt_name_inst, OF at_name_inst, where pi=p and x=xvec]) simp
    ultimately have "x \<sharp> (p \<bullet> N)" using `x \<sharp> P` by(rule_tac c_alpha)
    hence "(p \<bullet> x) \<sharp> (p \<bullet> p \<bullet> N)" by(simp add: pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` `bn(\<alpha>) \<sharp>* x` `x \<sharp> (bn(p \<bullet> \<alpha>))`S show ?case by simp
  next
    case c_input
    thus ?case by simp
  next
    case c_output
    thus ?case by(simp add: action.inject)
  next
    case c_case
    thus ?case by(force simp add: action.inject dest: mem_fresh)
  next
    case c_par1
    thus ?case by simp
  next
    case c_par2
    thus ?case by simp
  next
    case c_comm1
    thus ?case by simp
  next
    case c_comm2
    thus ?case by simp
  next
    case(c_open \<Psi> P \<pi> M xvec yvec N P' x y M' zvec N')
    from `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> = M'\<lparr>\<nu>*zvec\<rparr>\<langle>N'\<rangle>` have "zvec = xvec@x#yvec" and "N = N'"
      by(simp add: action.inject)+
    from `y \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<sharp> y`  have "y \<sharp> P" by(simp add: abs_fresh)
    moreover from `y \<sharp> zvec` `zvec = xvec@x#yvec`have "y \<sharp> (xvec@yvec)"
      by simp
    ultimately have "y \<sharp> N" by(rule_tac c_open) auto
    with `N = N'` show ?case by simp
  next
    case c_scope
    thus ?case by(auto simp add: abs_fresh)
  next
    case c_bang
    thus ?case by simp
  qed
next
  note `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  moreover from `xvec \<sharp>* M` have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from `distinct xvec` have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))" by simp
  ultimately show "x \<sharp> P'" using `x \<sharp> P` `x \<sharp> xvec`
  proof(nominal_induct \<Psi> P \<pi> \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: x arbitrary: M xvec N rule: semantics_induct)
    case(c_alpha \<Psi> P \<pi> \<alpha> P' p x M xvec N)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by(simp add: fresh_star_bij)
    with `distinct_perm p` have "\<alpha>  = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>" by simp
    moreover from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `x \<sharp> xvec` have "x \<sharp> (bn(p \<bullet> \<alpha>))" by simp
    with `(bn \<alpha>) \<sharp>* x` `x \<sharp> xvec` S have "x \<sharp> (p \<bullet> xvec)"
      by(drule_tac pt_fresh_bij1[OF pt_name_inst, OF at_name_inst, where pi=p and x=xvec]) simp
    ultimately have "x \<sharp> P'" using `x \<sharp> P` by(rule_tac c_alpha)
    hence "(p \<bullet> x) \<sharp> (p \<bullet> P')" by(simp add: pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    with `distinct_perm p` `bn(\<alpha>) \<sharp>* x` `x \<sharp> (bn(p \<bullet> \<alpha>))`S show ?case by simp
  next
    case c_input
    thus ?case by simp
  next
    case c_output
    thus ?case by(simp add: action.inject)
  next
    case c_case
    thus ?case by(force simp add: action.inject dest: mem_fresh)
  next
    case c_par1
    thus ?case by simp
  next
    case c_par2
    thus ?case by simp
  next
    case c_comm1
    thus ?case by simp
  next
    case c_comm2
    thus ?case by simp
  next
    case(c_open \<Psi> P \<pi> M xvec yvec N P' x y M' zvec N')
    from `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> = M'\<lparr>\<nu>*zvec\<rparr>\<langle>N'\<rangle>` have "zvec = xvec@x#yvec" 
      by(simp add: action.inject)
    from `y \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<sharp> y`  have "y \<sharp> P" by(simp add: abs_fresh)
    moreover from `y \<sharp> zvec` `zvec = xvec@x#yvec`have "y \<sharp> (xvec@yvec)"
      by simp
    ultimately show "y \<sharp> P'" by(rule_tac c_open) auto
  next
    case c_scope
    thus ?case by(auto simp add: abs_fresh)
  next
    case c_bang
    thus ?case by simp
  qed
qed

lemma output_fresh_chain_derivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"

  shows "yvec \<sharp>* N"
  and   "yvec \<sharp>* P'"
using assms
by(induct yvec) (auto intro: output_fresh_derivative)

lemma tau_fresh_derivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
proof -
  have "bn(\<tau>) \<sharp>* subject(\<tau>)" and "distinct(bn(\<tau>))" by simp+
  with `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'` show ?thesis using `x \<sharp> P`
  proof(nominal_induct \<Psi> P \<pi> \<alpha>=="(\<tau>::('a action))" P' avoiding: x rule: semantics_induct)
    case c_alpha
    thus ?case by simp
  next
    case c_input
    thus ?case by simp
  next
    case c_output
    thus ?case by simp
  next 
    case c_case
    thus ?case by(auto dest: mem_fresh)
  next
    case c_par1
    thus ?case by simp
  next
    case c_par2
    thus ?case by simp
  next
    case c_comm1
    thus ?case
      by(force dest: input_fresh_derivative output_fresh_derivative simp add: res_chain_fresh)
  next
    case c_comm2
    thus ?case
      by(force dest: input_fresh_derivative output_fresh_derivative simp add: res_chain_fresh)
  next
    case c_open
    thus ?case by simp
  next
    case c_scope
    thus ?case by(simp add: abs_fresh)
  next
    case c_bang
    thus ?case by simp
  qed
qed

lemma tau_fresh_chain_derivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     "xvec \<sharp>* P"
  
  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tau_fresh_derivative)

lemma free_fresh_derivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P"

  shows   "x \<sharp> P'"
using assms
by(rule_tac action_cases[where \<alpha>=\<alpha>])
  (auto intro: input_fresh_derivative tau_fresh_derivative output_fresh_derivative)

lemma free_fresh_chain_derivative:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   \<alpha>     :: "'a action"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* \<alpha>"

  shows   "xvec \<sharp>* P'"
using assms
by(auto intro: free_fresh_derivative simp add: fresh_star_def)

lemma Input:
  fixes \<Psi>    :: 'b
  and   M    :: 'a
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Tvec :: "'a list"

  assumes "\<Psi> \<turnstile> K \<leftrightarrow> M"
  and     "distinct xvec"
  and     "set xvec \<subseteq> supp N"
  and     "length xvec = length Tvec"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) @ K\<lparr>N[xvec::=Tvec]\<rparr> \<prec> P[xvec::=Tvec]"
proof -
  obtain p where xvec_fresh_psi: "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* \<Psi>"
             and xvec_freshM: "(p \<bullet> xvec) \<sharp>* M"
             and xvec_freshN: "(p \<bullet> xvec) \<sharp>* N"
             and xvec_freshK: "(p \<bullet> xvec) \<sharp>* K"
             and xvec_fresh_tvec: "(p \<bullet> xvec) \<sharp>* Tvec"
             and xvec_freshP: "(p \<bullet> xvec) \<sharp>* P"
             and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
             and dp: "distinct_perm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, K, N, P, Tvec)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)  
  note `\<Psi> \<turnstile> K \<leftrightarrow> M`
  moreover from `distinct xvec` have "distinct(p \<bullet> xvec)"
    by simp
  moreover from `(set xvec) \<subseteq> (supp N)` have "(p \<bullet> (set xvec)) \<subseteq> (p \<bullet> (supp N))"
    by simp
  hence "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
    by(simp add: eqvts)
  moreover from `length xvec = length Tvec` have "length(p \<bullet> xvec) = length Tvec"
    by simp
  ultimately have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>(Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)) @ K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr> \<prec> (p \<bullet> P)[(p \<bullet> xvec)::=Tvec]"
    using xvec_fresh_psi xvec_freshM xvec_freshK xvec_fresh_tvec
    by(rule_tac c_input)
  thus ?thesis using xvec_freshN xvec_freshP S `length xvec = length Tvec` dp
    by(auto simp add: input_chain_alpha' subst_term.renaming renaming)
qed

lemma residual_alpha:
  fixes p :: "name prm"
  and   \<alpha> :: "'a action"
  and   P :: "('a, 'b, 'c) psi"

  assumes "bn(p \<bullet> \<alpha>) \<sharp>* object  \<alpha>"
  and     "bn(p \<bullet> \<alpha>) \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "bn(p \<bullet> \<alpha>) \<sharp>* subject \<alpha>"
  and     "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"

  shows "\<alpha> \<prec> P = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P)"
using assms
apply(rule_tac \<alpha>=\<alpha> in action_cases)
apply(simp only: eqvts bn.simps)
apply simp
apply(simp add: bound_output_chain_alpha'' residual_inject)
by simp

lemma append_at_end_prov_option_eq_fresh:
  assumes "length xvec = length yvec"
  and "xvec \<sharp>* \<pi>"
  and "yvec \<sharp>* \<pi>"
  shows "append_at_end_prov_option \<pi> xvec = append_at_end_prov_option \<pi> yvec"
  using assms
proof(induct \<pi>)
  case None thus ?case by simp
next
  case (Some \<pi>) thus ?case
    unfolding append_at_end_prov_option.simps option.map option.inject
  proof(nominal_induct \<pi> avoiding: xvec yvec rule: frame.strong_inducts)
    case F_res thus ?case
      by(auto simp add: fresh_star_def abs_fresh) (metis set_fresh)
  next
    case (F_assert \<pi> xvec yvec)
    thus ?case
    proof(induct rule: list_induct2)
      case Nil thus ?case by simp
    next
      case(Cons x xvec y yvec)
      moreover hence "x \<sharp> \<lparr>\<nu>*yvec\<rparr>(F_assert \<pi>)"  "y \<sharp> \<lparr>\<nu>*yvec\<rparr>(F_assert \<pi>)"
        by(auto simp add: frame_res_chain_fresh)
      thus ?case using Cons
        by(simp add: frame.inject abs_fun_eq[OF pt_name_inst,OF at_name_inst])
    qed
  qed
qed
    
lemma Par1:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ \<alpha> \<prec> P'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "bn \<alpha> \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* \<alpha>"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_end_prov_option \<pi> A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q   :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and P'   :: "('a, 'b, 'c) psi"
      and A\<^sub>Q   :: "name list"
        and \<pi>   :: "'a frame frame option"
    and Q    :: "('a, 'b, 'c) psi"

    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
    and     "bn \<alpha> \<sharp>* Q"
    and     "bn \<alpha> \<sharp>* subject \<alpha>"
    and     "A\<^sub>Q \<sharp>* \<Psi>"
    and     "A\<^sub>Q \<sharp>* P"
    and     "A\<^sub>Q \<sharp>* \<alpha>"
    and     "distinct A\<^sub>Q"
  
    have  "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_end_prov_option \<pi> A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)"
    proof -
      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "distinct(bn \<alpha>)" by(rule bound_output_distinct)
      obtain q::"name prm" where "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(q \<bullet> \<alpha>) \<sharp>* P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q" and "bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>"
                             and "bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>Q" and "bn(q \<bullet> \<alpha>) \<sharp>* P'" and "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>\<^sub>Q" and "bn(q \<bullet> \<alpha>) \<sharp>* \<pi>"
                             and Sq: "(set q) \<subseteq> (set (bn \<alpha>)) \<times> (set(bn(q \<bullet> \<alpha>)))"
	by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>Q, \<Psi>\<^sub>Q, P',\<pi>)" in name_list_avoiding) (auto simp add: eqvts)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>Q) \<sharp>* P" and "(p \<bullet> A\<^sub>Q) \<sharp>* Q" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<alpha> " and "(p \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>Q" 
                              and "(p \<bullet> A\<^sub>Q) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>Q) \<sharp>* P'" 
                             and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<pi>" and Sp: "(set p) \<subseteq> (set A\<^sub>Q) \<times> (set(p \<bullet> A\<^sub>Q))"
	by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, \<alpha>, bn \<alpha>, q \<bullet> \<alpha>, P', (q \<bullet> P'), \<Psi>\<^sub>Q,\<pi>,A\<^sub>Q)" in name_list_avoiding) auto
      from `distinct(bn \<alpha>)` have "distinct(bn(q \<bullet> \<alpha>))" 
	by(rule_tac \<alpha>=\<alpha> in action_cases) (auto simp add: eqvts)
      from `A\<^sub>Q \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>Q` Sq have "A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)"
	apply(rule_tac \<alpha>=\<alpha> in action_cases)
	apply(simp only: bn.simps eqvts, simp)
	apply(simp add: fresh_chain_simps)
	by simp
      from `bn \<alpha> \<sharp>* subject \<alpha>` have "(q \<bullet> (bn \<alpha>)) \<sharp>* (q \<bullet> (subject \<alpha>))"
	by(simp add: fresh_star_bij)
      hence "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)" by(simp add: eqvts)
      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* P'` `bn \<alpha> \<sharp>* (subject \<alpha>)` Sq
      have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ (q \<bullet> \<alpha>) \<prec> (q \<bullet> P')"
	by(force simp add: residual_alpha)
      hence "A\<^sub>Q \<sharp>* (q \<bullet> P')" using  `bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)` `distinct(bn(q \<bullet> \<alpha>))` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)`
	by(auto intro: free_fresh_chain_derivative)
      from `A\<^sub>Q \<sharp>* P` Trans have "A\<^sub>Q \<sharp>* \<pi>"
        by(rule_tac trans_fresh_provenance)
      hence "(p\<bullet>A\<^sub>Q) \<sharp>* (p\<bullet>\<pi>)"
        by(subst (asm) perm_bool[where pi="p",symmetric]) (simp add: eqvts)
      from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> (p \<bullet> P) \<longmapsto>p\<bullet>\<pi> @ p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> P'))"
	by(rule semantics.eqvt)
      with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)` `(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)` `A\<^sub>Q \<sharp>* (q \<bullet> P')` `(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>`
           `(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>Q) \<sharp>* P` `(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')` Sp
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(p\<bullet>\<pi>) @ (q \<bullet> \<alpha>) \<prec> (q \<bullet> P')" by(simp add: eqvts)
      moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q` Sp have  "extract_frame Q = \<langle>(p \<bullet> A\<^sub>Q), (p \<bullet> \<Psi>\<^sub>Q)\<rangle>"
	by(simp add: frame_chain_alpha' eqvts)
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>Q` `(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)` Sp 
      have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)"
	by(simp add: fresh_alpha_perm)
      moreover from `distinct A\<^sub>Q` have "distinct(p \<bullet> A\<^sub>Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>(append_at_end_prov_option (p\<bullet>\<pi>) (p\<bullet>A\<^sub>Q)) @ (q \<bullet> \<alpha>) \<prec> ((q \<bullet> P') \<parallel> Q)"
	using `(p \<bullet> A\<^sub>Q) \<sharp>* P` `(p \<bullet> A\<^sub>Q) \<sharp>* Q` `(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)`
              `(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')` `(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>` `(bn(q \<bullet> \<alpha>)) \<sharp>* Q` `(bn(q \<bullet> \<alpha>)) \<sharp>* P` 
              `(bn(q \<bullet> \<alpha>)) \<sharp>* (subject (q \<bullet> \<alpha>))` `distinct(bn(q \<bullet> \<alpha>))` `(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<pi>)`
	by(rule_tac c_par1) (assumption | rule trans_fresh_provenance)+
      moreover have "append_at_end_prov_option (p\<bullet>\<pi>) (p\<bullet>A\<^sub>Q) = append_at_end_prov_option \<pi> A\<^sub>Q"
        using `(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* \<pi>` Sp `(p \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>Q`
        by(rule_tac append_at_end_prov_option_perm) simp_all
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>(append_at_end_prov_option (\<pi>) (A\<^sub>Q)) @ (q \<bullet> \<alpha>) \<prec> ((q \<bullet> P') \<parallel> Q)"
        by simp
      thus ?thesis using `bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* P'` `bn \<alpha> \<sharp>* subject \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* Q` `bn \<alpha> \<sharp>* Q` Sq
	by(force simp add: residual_alpha)
    qed
  }
  note Goal = this
  from Trans `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* \<pi>"
    by(rule_tac trans_fresh_provenance)
  with `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
  obtain A\<^sub>Q' where FrQ: "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>" and "A\<^sub>Q' \<sharp>* \<pi>"
    by(rule_tac C="(\<Psi>, P, \<alpha>,\<pi>)" in distinct_frame) auto
  have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> append_at_end_prov_option \<pi> A\<^sub>Q' @ \<alpha> \<prec> P' \<parallel> Q"
  proof(induct rule: action_cases[where \<alpha>=\<alpha>])
    case(c_input M N)
    from Trans FrQ `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>Q' \<sharp>* \<alpha>` `distinct A\<^sub>Q'` `bn \<alpha> \<sharp>* Q`
    show ?case using `\<alpha> = M\<lparr>N\<rparr>`
      by(rule_tac Goal) auto
  next
    case c_tau 
    from Trans FrQ `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>Q' \<sharp>* \<alpha>` `distinct A\<^sub>Q'` `bn \<alpha> \<sharp>* Q`
    show ?case using `\<alpha> = \<tau>` by(rule_tac Goal) auto
  next
    case(c_output M xvec N)
    from `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `A\<^sub>Q' \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* Q` have "xvec \<sharp>* A\<^sub>Q'" and "xvec \<sharp>* Q"
      by simp+
    obtain p where "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* Q"
               and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q'" 
               and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
      by(rule_tac xvec=xvec and c="(N, P', Q, M, A\<^sub>Q')" in name_list_avoiding) auto
    from Trans `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
    with `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P'` S
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
      by(simp add: bound_output_chain_alpha'' create_residual.simps)
    moreover from `xvec \<sharp>* A\<^sub>Q'` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<alpha>` S
    have "A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>)" by(simp add: fresh_chain_simps del: action_fresh_chain)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_end_prov_option \<pi> A\<^sub>Q' @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P') \<parallel> Q"
      using FrQ `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `distinct A\<^sub>Q'` `(p \<bullet> xvec) \<sharp>* Q` `A\<^sub>Q' \<sharp>* \<alpha>`
        `(p \<bullet> xvec) \<sharp>* M` `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
      by(rule_tac Goal) auto
    with `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P'` `(p \<bullet> xvec) \<sharp>* Q` `xvec \<sharp>* Q` S `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
    show ?case
      by(simp add: bound_output_chain_alpha'' eqvts create_residual.simps)
  qed
  moreover note `A\<^sub>Q' \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* \<pi>`
  moreover have "length A\<^sub>Q = length A\<^sub>Q'"
    using FrQ `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
    by (metis frame_chain_eq_length)
  ultimately show ?thesis
    by(subst append_at_end_prov_option_eq_fresh)
qed

lemma append_at_front_prov_option_eq_fresh:
  assumes "length xvec = length yvec"
  and "xvec \<sharp>* \<pi>"
  and "yvec \<sharp>* \<pi>"
  shows "append_at_front_prov_option \<pi> xvec = append_at_front_prov_option \<pi> yvec"
  using assms
proof(induct \<pi>)
  case None thus ?case by simp
next
  case (Some \<pi>) thus ?case
  proof(induct rule: list_induct2)
    case Nil thus ?case by simp
  next
    case(Cons x xvec y yvec)
    moreover hence "x \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>"  "y \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>"
      by(auto simp add: frame_res_chain_fresh)
    thus ?case using Cons
      by(simp add: frame.inject abs_fun_eq[OF pt_name_inst,OF at_name_inst])
  qed
qed

lemma Par2:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>P   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "bn \<alpha> \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>P   :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and P    :: "('a, 'b, 'c) psi"
    and \<pi>   :: "'a frame frame option"

    assume "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'"
    and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
    and     "bn \<alpha> \<sharp>* P"
    and     "bn \<alpha> \<sharp>* subject \<alpha>"
    and     "A\<^sub>P \<sharp>* \<Psi>"
    and     "A\<^sub>P \<sharp>* Q"
    and     "A\<^sub>P \<sharp>* \<alpha>"
    and     "distinct A\<^sub>P"
  
    have  "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')"
    proof -
      from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` have "distinct(bn \<alpha>)" by(rule bound_output_distinct)
      obtain q::"name prm" where "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(q \<bullet> \<alpha>) \<sharp>* P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q" and "bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(q \<bullet> \<alpha>) \<sharp>* \<pi>"
                             and "bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q'" and "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>\<^sub>P"
                             and Sq: "(set q) \<subseteq> (set (bn \<alpha>)) \<times> (set(bn(q \<bullet> \<alpha>)))"
	by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>P, \<Psi>\<^sub>P, Q',\<pi>)" in name_list_avoiding) (auto simp add: eqvts)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>"  and "(p \<bullet> A\<^sub>P) \<sharp>* \<pi>" 
                              and "(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>P) \<sharp>* Q'" 
                              and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P"  and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>P" 
                              and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
	by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, \<alpha>, q \<bullet> \<alpha>, Q', (q \<bullet> Q'), \<Psi>\<^sub>P,A\<^sub>P,\<pi>)" in name_list_avoiding) auto
      from `distinct(bn \<alpha>)` have "distinct(bn(q \<bullet> \<alpha>))" 
	by(rule_tac \<alpha>=\<alpha> in action_cases) (auto simp add: eqvts)
      from `A\<^sub>P \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>P` Sq have "A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)"
	apply(rule_tac \<alpha>=\<alpha> in action_cases)
	apply(simp only: bn.simps eqvts, simp)
	apply(simp add: fresh_chain_simps)
	by simp
      from `bn \<alpha> \<sharp>* subject \<alpha>` have "(q \<bullet> (bn \<alpha>)) \<sharp>* (q \<bullet> (subject \<alpha>))"
	by(simp add: fresh_star_bij)
      hence "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)" by(simp add: eqvts)
      from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* Q'` `bn \<alpha> \<sharp>* (subject \<alpha>)` Sq
      have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ (q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')"
	by(force simp add: residual_alpha)
      hence "A\<^sub>P \<sharp>* (q \<bullet> Q')" using  `bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)` `distinct(bn(q \<bullet> \<alpha>))` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)`
	by(auto intro: free_fresh_chain_derivative)
      from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> (p \<bullet> Q) \<longmapsto>p\<bullet>\<pi> @ p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> Q'))"
	by(rule semantics.eqvt)
      with `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)` `A\<^sub>P \<sharp>* (q \<bullet> Q')`
           `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')` Sp
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(p\<bullet>\<pi>) @ (q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')" by(simp add: eqvts)
      moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P` Sp have  "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
	by(simp add: frame_chain_alpha' eqvts)
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>P` `(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)` Sp 
      have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
	by(simp add: fresh_alpha_perm)
      moreover from `distinct A\<^sub>P` have "distinct(p \<bullet> A\<^sub>P)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>(append_at_front_prov_option (p\<bullet>\<pi>) (p\<bullet>A\<^sub>P)) @ (q \<bullet> \<alpha>) \<prec> (P \<parallel> (q \<bullet> Q'))"
	using `(p \<bullet> A\<^sub>P) \<sharp>* P` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)`
              `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')` `(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>` `(bn(q \<bullet> \<alpha>)) \<sharp>* Q` `(bn(q \<bullet> \<alpha>)) \<sharp>* P` 
              `(bn(q \<bullet> \<alpha>)) \<sharp>* (subject (q \<bullet> \<alpha>))` `distinct(bn(q \<bullet> \<alpha>))`
	by(rule_tac c_par2) (assumption | rule trans_fresh_provenance)+
      moreover from `A\<^sub>P \<sharp>* Q` Trans have "A\<^sub>P \<sharp>* \<pi>"
        by(rule_tac trans_fresh_provenance)
      hence "(p\<bullet>A\<^sub>P) \<sharp>* (p\<bullet>\<pi>)"
        by(subst (asm) perm_bool[where pi="p",symmetric]) (simp add: eqvts)
      have "append_at_front_prov_option (p\<bullet>\<pi>) (p\<bullet>A\<^sub>P) = append_at_front_prov_option \<pi> A\<^sub>P"
        using `(p\<bullet>A\<^sub>P) \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<pi>` Sp `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>P`
      proof(induct \<pi>)
        case None thus ?case by simp
      next
        case (Some \<pi>)
        thus ?case
          unfolding option_fresh_chain
          by(frule_tac frame_chain_alpha) auto
      qed          
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P @ (q \<bullet> \<alpha>) \<prec> (P \<parallel> (q \<bullet> Q'))"
        by simp
      thus ?thesis using `bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* Q'` `bn \<alpha> \<sharp>* subject \<alpha>` `bn(q \<bullet> \<alpha>) \<sharp>* P` `bn \<alpha> \<sharp>* P` Sq
	by(force simp add: residual_alpha) 
    qed
  }
  note Goal = this
  from Trans `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* \<pi>"
    by(rule_tac trans_fresh_provenance)
  with `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
  obtain A\<^sub>P' where FrP: "extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* \<pi>"
    by(rule_tac C="(\<Psi>, Q, \<alpha>,\<pi>)" in distinct_frame) auto
  have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> append_at_front_prov_option \<pi> A\<^sub>P' @ \<alpha> \<prec> P \<parallel> Q'"
  proof(induct rule: action_cases[where \<alpha>=\<alpha>])
    case(c_input M N)
    from Trans FrP `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* Q` `A\<^sub>P' \<sharp>* \<alpha>` `distinct A\<^sub>P'` `bn \<alpha> \<sharp>* P`
    show ?case using `\<alpha> = M\<lparr>N\<rparr>` by(rule_tac Goal) auto 
  next
    case c_tau 
    from Trans FrP `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* Q` `A\<^sub>P' \<sharp>* \<alpha>` `distinct A\<^sub>P'` `bn \<alpha> \<sharp>* P`
    show ?case using `\<alpha> = \<tau>`  by(rule_tac Goal) auto
  next
    case(c_output M xvec N)
    from `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `A\<^sub>P' \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* P` have "xvec \<sharp>* A\<^sub>P'" and "xvec \<sharp>* P"
      by simp+
    obtain p where "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* P"
               and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" 
               and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
      by(rule_tac xvec=xvec and c="(N, Q', P, M, A\<^sub>P')" in name_list_avoiding) auto
    from Trans `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
    with `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q'` S
    have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by(simp add: bound_output_chain_alpha'' create_residual.simps)
    moreover from `xvec \<sharp>* A\<^sub>P'` `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` `A\<^sub>P' \<sharp>* \<alpha>` S
    have "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" by(simp add: fresh_chain_simps del: action_fresh_chain)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi> A\<^sub>P' @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P \<parallel> (p \<bullet> Q')"
      using FrP `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* Q` `distinct A\<^sub>P'` `(p \<bullet> xvec) \<sharp>* P` `A\<^sub>P' \<sharp>* \<alpha>`
           `(p \<bullet> xvec) \<sharp>* M` `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
      by(rule_tac Goal) auto
    with `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q'` `(p \<bullet> xvec) \<sharp>* P` `xvec \<sharp>* P` S `\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>`
    show ?case
      by(simp add: bound_output_chain_alpha'' eqvts create_residual.simps)
  qed
  moreover note `A\<^sub>P' \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<pi>`
  moreover have "length A\<^sub>P = length A\<^sub>P'"
    using FrP `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
    by (metis frame_chain_eq_length)
  ultimately show ?thesis
    by(subst append_at_front_prov_option_eq_fresh)
qed

lemma Open:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<in> supp N"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from Trans have "distinct(xvec@yvec)" by(force dest: bound_output_distinct)
  hence "xvec \<sharp>* yvec" by(induct xvec) auto
  
  obtain p where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P"  and "(p \<bullet> yvec) \<sharp>* M"
             and "(p \<bullet> yvec) \<sharp>* yvec" and "(p \<bullet> yvec) \<sharp>* N" and "(p \<bullet> yvec) \<sharp>* P'"
             and "x \<sharp> (p \<bullet> yvec)" and "(p \<bullet> yvec) \<sharp>* xvec"
             and Sp: "(set p) \<subseteq> (set yvec) \<times> (set(p \<bullet> yvec))"
    by(rule_tac xvec=yvec and c="(\<Psi>, P, M, xvec, yvec, N, P', x)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)
  obtain q where "(q \<bullet> xvec) \<sharp>* \<Psi>" and "(q \<bullet> xvec) \<sharp>* P"  and "(q \<bullet> xvec) \<sharp>* M"
             and "(q \<bullet> xvec) \<sharp>* xvec" and "(q \<bullet> xvec) \<sharp>* N" and "(q \<bullet> xvec) \<sharp>* P'"
             and "x \<sharp> (q \<bullet> xvec)" and "(q \<bullet> xvec) \<sharp>* yvec"
             and "(q \<bullet> xvec) \<sharp>* p" and "(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)"
             and Sq: "(set q) \<subseteq> (set xvec) \<times> (set(q \<bullet> xvec))"
    by(rule_tac xvec=xvec and c="(\<Psi>, P, M, xvec, yvec, p \<bullet> yvec, N, P', x, p)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

  note `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'`
  moreover from `(p \<bullet> yvec) \<sharp>* N` `(q \<bullet> xvec) \<sharp>* N` `xvec \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)` `(p \<bullet> yvec) \<sharp>* xvec` Sp Sq 
  have "((p@q) \<bullet> (xvec @ yvec)) \<sharp>* N" apply(simp only: eqvts) apply(simp only: pt2[OF pt_name_inst])
    by simp
  moreover from `(p \<bullet> yvec) \<sharp>* P'` `(q \<bullet> xvec) \<sharp>* P'` `xvec \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)` `(p \<bullet> yvec) \<sharp>* xvec` Sp Sq 
  have "((p@q) \<bullet> (xvec @ yvec)) \<sharp>* P'" by(simp del: fresh_alpha_perm add: eqvts pt2[OF pt_name_inst])
  moreover from Sp Sq `xvec \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)` `(p \<bullet> yvec) \<sharp>* xvec`
  have Spq: "set(p@q) \<subseteq> set(xvec@yvec) \<times> set((p@q) \<bullet> (xvec@yvec))"
    by(simp add: pt2[OF pt_name_inst] eqvts) blast
  ultimately have "\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*((p@q) \<bullet> (xvec@yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    apply(simp add: create_residual.simps)
    by(erule_tac rev_mp) (subst bound_output_chain_alpha, auto)

  with  Sp Sq `xvec \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)` `(p \<bullet> yvec) \<sharp>* xvec`
  have "\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*((q \<bullet> xvec)@(p \<bullet> yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(simp add: eqvts pt2[OF pt_name_inst] del: fresh_alpha_perm)
  moreover from `x \<in> supp N` have "((p@q) \<bullet> x) \<in> (p@q) \<bullet> (supp N)"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> (q \<bullet> xvec)` `x \<sharp> (p \<bullet> yvec)` Sp Sq
  have "x \<in> supp((p@q)\<bullet> N)" by(simp add: eqvts pt2[OF pt_name_inst])
  moreover from `distinct(xvec@yvec)` have "distinct(q \<bullet> xvec)" and "distinct(p \<bullet> yvec)"
    by auto
  moreover note `x \<sharp> (q \<bullet> xvec)` `x \<sharp> (p \<bullet> yvec)` `x \<sharp> M` `x \<sharp> \<Psi>` 
                `(q \<bullet> xvec) \<sharp>* \<Psi>` `(q \<bullet> xvec) \<sharp>* P` `(q \<bullet> xvec) \<sharp>* M` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)`
                `(p \<bullet> yvec) \<sharp>* \<Psi>` `(p \<bullet> yvec) \<sharp>* P` `(p \<bullet> yvec) \<sharp>* M` `distinct(q \<bullet> xvec)`
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*((q \<bullet> xvec)@x#(p \<bullet> yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(rule_tac c_open) (auto dest: trans_fresh_provenance)
  with `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> (q \<bullet> xvec)` `x \<sharp> (p \<bullet> yvec)`
       `xvec \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)` `(p \<bullet> yvec) \<sharp>* xvec` Sp Sq
  have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*((p@q) \<bullet> (xvec@x#yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(simp add: eqvts pt2[OF pt_name_inst] del: fresh_alpha_perm)
  thus ?thesis using `((p@q) \<bullet> (xvec @ yvec)) \<sharp>* N` `((p@q) \<bullet> (xvec @ yvec)) \<sharp>* P'` Spq
    apply(simp add: create_residual.simps)
    by(erule_tac rev_mp) (subst bound_output_chain_alpha, auto)
qed

lemma Scope:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi> @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  {
    fix \<Psi> P M xvec N P' x

    assume "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    and    "(x::name) \<sharp> \<Psi>"
    and    "x \<sharp> M"
    and    "x \<sharp> xvec"
    and    "x \<sharp> N"

    obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* xvec"  and "(p \<bullet> xvec) \<sharp>* \<pi>" 
                           and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P'" and "x \<sharp> (p \<bullet> xvec)"
                           and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
      by(rule_tac xvec=xvec and c="(\<Psi>, P, M, xvec, N, P', x,\<pi>)" in name_list_avoiding)
        (auto simp add: eqvts fresh_star_prod)
    from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P'` S
    have "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
      by(simp add: bound_output_chain_alpha'' create_residual.simps)
    moreover hence "distinct(p \<bullet> xvec)" by(force dest: bound_output_distinct)
    moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> (p \<bullet> xvec)`
    moreover from `x \<sharp> xvec` `x \<sharp> p \<bullet> xvec` `x \<sharp> N` S have "x \<sharp> (p \<bullet> N)"
      by(simp add: fresh_left del: fresh_alpha_swap)
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P')" using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* M` `(p \<bullet> xvec) \<sharp>* \<pi>`
      by(rule_tac c_scope) auto
    moreover from `x \<sharp> xvec` `x \<sharp> p \<bullet> xvec` S have "p \<bullet> x = x" by simp
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi> @ M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))" by simp
    moreover from `(p \<bullet> xvec) \<sharp>* P'` `x \<sharp> xvec` `x \<sharp> (p \<bullet> xvec)` have "(p \<bullet> xvec) \<sharp>* \<lparr>\<nu>x\<rparr>P'" 
      by(simp add: abs_fresh_star)
    ultimately have"\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>map_option (F_res x) \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using `(p \<bullet> xvec) \<sharp>* N` S
      by(simp add: bound_output_chain_alpha'' create_residual.simps)
  }
  note Goal = this
  show ?thesis
  proof(induct rule: action_cases[where \<alpha>=\<alpha>])
    case(c_input M N)
    with assms show ?case by(force intro: c_scope)
  next
    case(c_output M xvec N)
    with assms show ?case by(force intro: Goal)
  next
    case c_tau
    with assms show ?case by(force intro: c_scope)
  qed
qed
(*
lemma input_alpha:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))"
  and     "(p \<bullet> xvec) \<sharp>* N"
  and     "(p \<bullet> xvec) \<sharp>* P'"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> P \<longmapsto>M\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> P')"
using assms
proof(nominal_induct avoiding: p xvec rule: input_induct)
  case(c_input \<Psi> M K yvec N Tvec P p xvec)
  note `\<Psi> \<turnstile> M \<leftrightarrow> K`
  moreover from `distinct yvec` have "distinct(p \<bullet> yvec)" by simp
  moreover from `set yvec \<subseteq> (supp N)` have "(p \<bullet> (set yvec)) \<subseteq> (p \<bullet> (supp N))"
    by simp
  hence "set(p \<bullet> yvec) \<subseteq> (supp(p \<bullet> N))" by(simp add: eqvts)
  moreover from `length yvec = length Tvec` have "length(p \<bullet> yvec) = length(p \<bullet> Tvec)"
    by simp
  ultimately 
  have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> yvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>(K\<lparr>((p \<bullet> N)[(p \<bullet> yvec)::=(p \<bullet> Tvec)])\<rparr> \<prec> (p \<bullet> P)[(p \<bullet> yvec)::=(p \<bullet> Tvec)])"
    by(rule Input)
  moreover from `length yvec = length Tvec` `distinct yvec` `(p \<bullet> xvec) \<sharp>* (N[yvec::=Tvec])` `(p \<bullet> xvec) \<sharp>* (P[yvec::=Tvec])` `yvec \<sharp>* xvec` `yvec \<sharp>* p`
  have "(set(p \<bullet> xvec)) \<sharp>* N" and "(set(p \<bullet> xvec)) \<sharp>* P"
    apply -
    apply(rule_tac subst_term.subst1_chain)
    apply force+
    by(rule_tac subst1_chain) auto
  with `xvec \<sharp>* (M\<lparr>\<lambda>*yvec N\<rparr>.P)` `set p \<subseteq> (set xvec) \<times> set(p \<bullet> xvec)`
  have "M\<lparr>\<lambda>* yvec N\<rparr>.P = M\<lparr>\<lambda>*(p \<bullet> yvec) (p \<bullet> N)\<rparr>.(p \<bullet> P)"
    apply(auto simp add: psi.inject)
    by(rule input_chain_alpha) (simp add: fresh_star_def)+
  ultimately show ?case by(simp add: eqvts)
next
  case(c_case \<Psi> P M N P' \<phi> Cs p xvec)
  thus ?case by(rule_tac Case) (auto dest: mem_fresh_chain)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M N P' yvec Q p xvec)
  thus ?case
    by(force simp add: eqvts intro: Par1)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M N Q' yvec P p xvec)
  thus ?case by(force simp add: eqvts intro: Par2)
next
  case(c_scope \<Psi> P M N P' x p xvec)
  thus ?case by(force simp add: eqvts fresh_chain_simps intro: Scope)
next
  case(c_bang \<Psi> P M N P' p xvec)
  thus ?case by(force intro: Bang)
qed
*)
lemma input_swap_frame_subject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
using assms
proof(nominal_induct avoiding: x y rule: input_induct)
  case(c_input \<Psi> M K xvec N Tvec P x y)
  from `x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.P` have "x \<sharp> M" by simp
  from `y \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.P` have "y \<sharp> M" by simp
  from `\<Psi> \<turnstile> K \<leftrightarrow> M` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> K) \<leftrightarrow> ([(x, y)] \<bullet> M)"
    by(rule chan_eq_closed)
  with `x \<sharp> M` `y \<sharp> M`  have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> K) \<leftrightarrow> M"
    by(simp)
  thus ?case using `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
    by(rule Input)
next
  case(c_case \<Psi> P \<pi> M N P' \<phi> Cs x y)
  from `x \<sharp> Cases Cs` `y \<sharp> Cases Cs` `(\<phi>, P) mem Cs` have "x \<sharp> \<phi>" and "x \<sharp> P" and "y \<sharp> \<phi>" and "y \<sharp> P"
    by(auto dest: mem_fresh)
  from `x \<sharp> P` `y \<sharp> P` have "([(x ,y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by(rule c_case)
  moreover note `(\<phi>, P) mem Cs`
  moreover from `\<Psi> \<turnstile> \<phi>` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> \<phi>)" by(rule stat_closed)
  with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> \<phi>" by simp
  ultimately show ?case using `guarded P` by(rule Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q x y)
  from `x \<sharp> P \<parallel> Q` have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from `y \<sharp> P \<parallel> Q` have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from `x \<sharp> P` `y \<sharp> P` `\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'`
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(simp add: eqvts)

  moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "([(x, y)] \<bullet> (extract_frame Q)) = ([(x, y)] \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>)"
    by simp
  with `A\<^sub>Q \<sharp>* x` `x \<sharp> Q` `A\<^sub>Q \<sharp>* y` `y \<sharp> Q` have "\<langle>A\<^sub>Q, ([(x, y)] \<bullet> \<Psi>\<^sub>Q)\<rangle> = extract_frame Q"
    by(simp add: eqvts)
  moreover from `A\<^sub>Q \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>Q \<sharp>* x` `A\<^sub>Q \<sharp>* y` have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from `A\<^sub>Q \<sharp>* M` have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>Q \<sharp>* x` `A\<^sub>Q \<sharp>* y` have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* N`
    by(rule_tac Par1) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> M N Q' A\<^sub>P P x y)
  from `x \<sharp> P \<parallel> Q` have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from `y \<sharp> P \<parallel> Q` have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from `x \<sharp> Q` `y \<sharp> Q` `\<And>x y. \<lbrakk>x \<sharp> Q; y \<sharp> Q\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> Q'`
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(simp add: eqvts)

  moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "([(x, y)] \<bullet> (extract_frame P)) = ([(x, y)] \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>)"
    by simp
  with `A\<^sub>P \<sharp>* x` `x \<sharp> P` `A\<^sub>P \<sharp>* y` `y \<sharp> P` have "\<langle>A\<^sub>P, ([(x, y)] \<bullet> \<Psi>\<^sub>P)\<rangle> = extract_frame P"
    by(simp add: eqvts)
  moreover from `A\<^sub>P \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* y` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from `A\<^sub>P \<sharp>* M` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* y` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* N`
    by(rule_tac Par2) auto
next
  case(c_scope \<Psi> P \<pi> M N P' z x y)
  from `x \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> x` have "x \<sharp> P" by(simp add: abs_fresh)
  from `y \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> y` have "y \<sharp> P" by(simp add: abs_fresh)
  from `x \<sharp> P` `y \<sharp> P` `\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by simp
  moreover with `z \<sharp> \<Psi>` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with `z \<sharp> M` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using `z \<sharp> N`
    by(rule_tac Scope) (assumption | simp)+
next
  case(c_bang \<Psi> P M N P' x y)
  thus ?case by(force intro: Bang)
qed

lemma input_perm_frame_subject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
using S
proof(induct p)
  case Nil
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'`
  show ?case by simp
next
  case(Cons a p)
  from `set(a#p) \<subseteq> Xs \<times> Ys` have "set p \<subseteq> Xs \<times> Ys" by auto
  with `set p \<subseteq> Xs \<times> Ys \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'`
  have Trans: "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by simp
  from `set(a#p) \<subseteq> Xs \<times> Ys` show ?case
  proof(cases a, clarsimp)
    fix a b
    assume "a \<in> Xs" and "b \<in> Ys"
    with `Xs \<sharp>* P` `Ys \<sharp>* P`
    have "a \<sharp> P" and "b \<sharp> P"
      by(auto simp add: fresh_star_def)
    with Trans show "([(a, b)] \<bullet> p \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ ([(a, b)] \<bullet> p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
      by(rule input_swap_frame_subject)
  qed  
qed

lemma input_swap_subject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto> \<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` `x \<sharp> P` `y \<sharp> P`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule input_swap_frame_subject)
  with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` show ?thesis
    by simp
qed

lemma input_perm_subject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"
  and     "Xs \<sharp>* \<Psi>"
  and     "Ys \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto> \<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` S `Xs \<sharp>* P` `Ys \<sharp>* P`
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule input_perm_frame_subject)
  with `Xs \<sharp>* \<Psi>` `Ys \<sharp>* \<Psi>` S show ?thesis
    by simp
qed

lemma input_swap_frame:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> M"
  and     "y \<sharp> M"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` `x \<sharp> P` `y \<sharp> P`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule input_swap_frame_subject)
  with `x \<sharp> M` `y \<sharp> M` show ?thesis
    by simp
qed

lemma input_perm_frame:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"
  and     "Xs \<sharp>* M"
  and     "Ys \<sharp>* M"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` S `Xs \<sharp>* P` `Ys \<sharp>* P`
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule input_perm_frame_subject)
  with `Xs \<sharp>* M` `Ys \<sharp>* M` S show ?thesis
    by simp
qed

lemma input_alpha:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))"
  and     "distinct_perm p"
  and     "xvec \<sharp>* P"
  and     "(p \<bullet> xvec) \<sharp>* P"

  shows "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> P')"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` `xvec \<sharp>* P` `(p\<bullet>xvec) \<sharp>* P` have "xvec \<sharp>* \<pi>" "(p\<bullet>xvec) \<sharp>* \<pi>"
    by(auto intro: trans_fresh_provenance)
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'` `set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P`
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by(rule_tac input_perm_frame_subject) auto
  hence "(p \<bullet> p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>p\<bullet>\<pi> @ (p \<bullet> ((p \<bullet> M)\<lparr>N\<rparr> \<prec> P'))" by(rule eqvts)
  with `distinct_perm p` `xvec \<sharp>* P` `(p \<bullet> xvec) \<sharp>* P` `set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))` `xvec \<sharp>* \<pi>` `(p\<bullet>xvec) \<sharp>* \<pi>`
  show ?thesis
    by(simp add: eqvts)
qed

lemma frame_fresh[dest]:
  fixes x  :: name
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"

  shows "x \<sharp> \<Psi>\<^sub>F"
using assms
by(simp add: frame_res_chain_fresh) (simp add: fresh_def name_list_supp)

lemma output_swap_frame_subject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
proof(nominal_induct avoiding: x y rule: output_induct')
  case c_alpha
  thus ?case by(simp add: create_residual.simps bound_output_chain_alpha'')
next
  case(c_output \<Psi> M K N P x y)
  from `x \<sharp> M\<langle>N\<rangle>.P` have "x \<sharp> M" by simp
  from `y \<sharp> M\<langle>N\<rangle>.P` have "y \<sharp> M" by simp
  from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> M) \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(rule chan_eq_closed)
  with `x \<sharp> M` `y \<sharp> M`  have "([(x, y)] \<bullet> \<Psi>) \<turnstile> M \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(simp)
  thus ?case by(rule Output)
next
  case(c_case \<Psi> P \<pi> M xvec N P' \<phi> Cs x y)
  from `x \<sharp> Cases Cs` `y \<sharp> Cases Cs` `(\<phi>, P) mem Cs` have "x \<sharp> \<phi>" and "x \<sharp> P" and "y \<sharp> \<phi>" and "y \<sharp> P"
    by(auto dest: mem_fresh)
  from `x \<sharp> P` `y \<sharp> P` have "([(x ,y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule c_case)
  moreover note `(\<phi>, P) mem Cs`
  moreover from `\<Psi> \<turnstile> \<phi>` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> \<phi>)" by(rule stat_closed)
  with `x \<sharp> \<phi>` `y \<sharp> \<phi>` have "([(x, y)] \<bullet> \<Psi>) \<turnstile> \<phi>" by simp
  ultimately show ?case using `guarded P` by(rule Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M xvec N P' A\<^sub>Q Q x y)
  from `x \<sharp> P \<parallel> Q` have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from `y \<sharp> P \<parallel> Q` have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from `x \<sharp> P` `y \<sharp> P` `\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(simp add: eqvts)

  moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "([(x, y)] \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>) = ([(x, y)] \<bullet> (extract_frame Q))"
    by simp
  with `A\<^sub>Q \<sharp>* x` `x \<sharp> Q` `A\<^sub>Q \<sharp>* y` `y \<sharp> Q` have "\<langle>A\<^sub>Q, ([(x, y)] \<bullet> \<Psi>\<^sub>Q)\<rangle> = extract_frame Q"
    by(simp add: eqvts)
  moreover from `A\<^sub>Q \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>Q \<sharp>* x` `A\<^sub>Q \<sharp>* y` have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from `A\<^sub>Q \<sharp>* M` have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>Q \<sharp>* x` `A\<^sub>Q \<sharp>* y` have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* N` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec`
    by(rule_tac Par1) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> M xvec N Q' A\<^sub>P P x y)
  from `x \<sharp> P \<parallel> Q` have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from `y \<sharp> P \<parallel> Q` have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from `x \<sharp> Q` `y \<sharp> Q` `\<And>x y. \<lbrakk>x \<sharp> Q; y \<sharp> Q\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(simp add: eqvts)

  moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` have "([(x, y)] \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>) = ([(x, y)] \<bullet> (extract_frame P))"
    by simp
  with `A\<^sub>P \<sharp>* x` `x \<sharp> P` `A\<^sub>P \<sharp>* y` `y \<sharp> P` have "\<langle>A\<^sub>P, ([(x, y)] \<bullet> \<Psi>\<^sub>P)\<rangle> = extract_frame P"
    by(simp add: eqvts)
  moreover from `A\<^sub>P \<sharp>* \<Psi>` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* y` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from `A\<^sub>P \<sharp>* M` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `A\<^sub>P \<sharp>* x` `A\<^sub>P \<sharp>* y` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* N` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* xvec`
    by(rule_tac Par2) auto
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' z x y)
  from `x \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> x` have "x \<sharp> P" by(simp add: abs_fresh)
  from `y \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> y` have "y \<sharp> P" by(simp add: abs_fresh)
  from `x \<sharp> P` `y \<sharp> P` `\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>Some \<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>Some \<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
  moreover with `z \<sharp> \<Psi>` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with `z \<sharp> M` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using `z \<in> supp N` `z \<sharp> xvec` `z \<sharp> yvec`
    by(rule_tac Open) (assumption | simp)+
next
  case(c_scope \<Psi> P \<pi> M xvec N P' z x y)
  from `x \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> x` have "x \<sharp> P" by(simp add: abs_fresh)
  from `y \<sharp> \<lparr>\<nu>z\<rparr>P` `z \<sharp> y` have "y \<sharp> P" by(simp add: abs_fresh)
  from `x \<sharp> P` `y \<sharp> P` `\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
  moreover with `z \<sharp> \<Psi>` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with `z \<sharp> M` have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with `z \<sharp> x` `z \<sharp> y` have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using `z \<sharp> N` `z \<sharp> xvec`
    by(rule_tac Scope) (assumption | simp)+
next
  case(c_bang \<Psi> P \<pi> M B x y)
  thus ?case by(force intro: Bang)
qed

lemma output_perm_frame_subject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  {
    fix xvec N P' Xs YS
    assume "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and "xvec \<sharp>* M" and "xvec \<sharp>* yvec" and "xvec \<sharp>* zvec"
    have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using S
    proof(induct p)
      case Nil
      from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
      show ?case by simp
    next
      case(Cons a p)
      from `set(a#p) \<subseteq> set yvec \<times> set zvec` have "set p \<subseteq> set yvec \<times> set zvec" by auto
      then have Trans: "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule Cons)
      from `set(a#p) \<subseteq> set yvec \<times> set zvec` show ?case
      proof(cases a, clarsimp)
	fix x y
	note Trans
	moreover from `xvec \<sharp>* yvec` `xvec \<sharp>* zvec` `set p \<subseteq> set yvec \<times> set zvec` `xvec \<sharp>* M` have "xvec \<sharp>* (p \<bullet> M)"
	  by(simp add: fresh_chain_simps)
	moreover assume "x \<in> set yvec" and "y \<in> set zvec"
	with `yvec \<sharp>* P` `zvec \<sharp>* P` have "x \<sharp> P" and "y \<sharp> P"
	  by(auto simp add: fresh_star_def)
	ultimately show "([(x, y)] \<bullet> p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	  by(rule output_swap_frame_subject)
      qed
    qed
  }
  note Goal = this
  obtain q::"name prm" where "(q \<bullet> xvec) \<sharp>* yvec" and "(q \<bullet> xvec) \<sharp>* zvec" and "(q \<bullet> xvec) \<sharp>* xvec" 
                         and "(q \<bullet> xvec) \<sharp>* N" and "(q \<bullet> xvec) \<sharp>* P'" and "(q \<bullet> xvec) \<sharp>* M"  and "(q \<bullet> xvec) \<sharp>* \<pi>" 
                         and Sq: "(set q) \<subseteq> (set xvec) \<times> (set(q \<bullet> xvec))"
    by(rule_tac xvec=xvec and c="(P, xvec, yvec, zvec, N, M, P',\<pi>)" in name_list_avoiding) auto
  with `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` have "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*(q \<bullet> xvec)\<rparr>\<langle>(q \<bullet> N)\<rangle> \<prec> (q \<bullet> P')"
    by(simp add: bound_output_chain_alpha'' residual_inject)
  hence "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*(q \<bullet> xvec)\<rparr>\<langle>(q \<bullet> N)\<rangle> \<prec> (q \<bullet> P')"
    using `(q \<bullet> xvec) \<sharp>* M` `(q \<bullet> xvec) \<sharp>* yvec` `(q \<bullet> xvec) \<sharp>* zvec`
    by(rule Goal)
  with `(q \<bullet> xvec) \<sharp>* N` `(q \<bullet> xvec) \<sharp>* P'` Sq show ?thesis
    by(simp add: bound_output_chain_alpha'' residual_inject)
qed

lemma output_swap_subject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `xvec \<sharp>* M` `x \<sharp> P` `y \<sharp> P`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule output_swap_frame_subject)
  with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` show ?thesis
    by simp
qed

lemma output_perm_subject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from assms have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
   by(rule_tac output_perm_frame_subject)
  with S `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` show ?thesis
    by simp
qed
 
lemma output_swap_frame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> M"
  and     "y \<sharp> M"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `xvec \<sharp>* M` `x \<sharp> P` `y \<sharp> P`
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ ([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule output_swap_frame_subject)
  with `x \<sharp> M` `y \<sharp> M` show ?thesis
    by simp
qed

lemma output_perm_frame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"
  and     "yvec \<sharp>* M"
  and     "zvec \<sharp>* M"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from assms have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac output_perm_frame_subject)
  with S `yvec \<sharp>* M` `zvec \<sharp>* M` show ?thesis
    by simp
qed

lemma distinct_ip:
  fixes xvec :: "name list"
  and   \<pi> :: "'a::fs_name frame"
  and   C  :: "'bbb::fs_name"
  
  assumes "xvec \<sharp>* C"

  obtains yvec where  "\<lparr>\<nu>*xvec\<rparr>\<pi> = \<lparr>\<nu>*yvec\<rparr>\<pi>" and "distinct yvec" and "yvec \<sharp>* C"
proof -
  assume "\<And>yvec. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>\<pi> = \<lparr>\<nu>*yvec\<rparr>\<pi>; distinct yvec; yvec \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover from assms have "\<exists>yvec. \<lparr>\<nu>*xvec\<rparr>\<pi> = \<lparr>\<nu>*yvec\<rparr>\<pi> \<and> distinct yvec \<and> yvec \<sharp>* C"
  proof(induct xvec)
    case Nil
    thus ?case
      by(rule_tac exI[where x="[]"]) simp
  next
    case(Cons a xvec)
    then obtain yvec where Eq: "\<lparr>\<nu>*xvec\<rparr>\<pi> = \<lparr>\<nu>*yvec\<rparr>\<pi>" and "distinct yvec" and "yvec \<sharp>* C" by force
    from `(a#xvec) \<sharp>* C` have "a \<sharp> C" and "xvec \<sharp>* C" by simp+
    show ?case
    proof(case_tac "a \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>")
      assume "a \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>"
      obtain b::name where "b \<sharp> yvec" and "b \<sharp> \<pi>" and "b \<sharp> C" by(generate_fresh "name", auto)
      have "\<lparr>\<nu>*(a#xvec)\<rparr>\<pi> = \<lparr>\<nu>*(b#yvec)\<rparr>\<pi>"
      proof -
	from Eq have "\<lparr>\<nu>*(a#xvec)\<rparr>\<pi> = \<lparr>\<nu>*(a#yvec)\<rparr>\<pi>" by(simp add: frame.inject)
	moreover from `b \<sharp> \<pi>` have "\<dots> = \<lparr>\<nu>b\<rparr>([(a, b)] \<bullet> \<lparr>\<nu>*yvec\<rparr>(\<pi>))"
          by(induct yvec)
            (auto simp add: frame.inject alpha_res eqvts alpha calc_atm fresh_left abs_fresh)
	ultimately show ?thesis using `a \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>` `b \<sharp> \<pi>`
          by(simp add: frame_res_chain_fresh)
      qed
      moreover from `distinct yvec` `b \<sharp> yvec` have "distinct(b#yvec)" by simp
      moreover from `yvec \<sharp>* C` `b \<sharp> C` have "(b#yvec) \<sharp>* C" by simp+
      ultimately show ?case by blast
    next
      from Eq have "\<lparr>\<nu>*(a#xvec)\<rparr>\<pi> = \<lparr>\<nu>*(a#yvec)\<rparr>\<pi>" by(simp add: frame.inject)
      moreover assume "\<not>(a \<sharp> \<lparr>\<nu>*yvec\<rparr>\<pi>)"
      hence "a \<sharp> yvec" apply(simp add: fresh_def)
	by(induct yvec) (auto simp add: supp_list_nil supp_list_cons supp_atm frame.supp abs_supp)
      with `distinct yvec` have "distinct(a#yvec)" by simp
      moreover from `yvec \<sharp>* C` `a \<sharp> C` have "(a#yvec) \<sharp>* C" by simp+
      ultimately show ?case by blast
    qed
  qed
  ultimately show ?thesis using `xvec \<sharp>* C`
    by blast
qed

lemma Comm1:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   xvec :: "name list"
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  
  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* \<Psi>\<^sub>P"
  and     "yvec \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "zvec \<sharp>* \<Psi>"  
  and     "zvec \<sharp>* P"
  and     "zvec \<sharp>* \<Psi>\<^sub>Q"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and xvec :: "name list"
    and yvec :: "name list"
    and zvec :: "name list"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
      and  "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and  "distinct A\<^sub>P"
      and  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      and  "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
      and  "distinct A\<^sub>Q"
      and  "A\<^sub>P \<sharp>* \<Psi>"
(*      and  "A\<^sub>P \<sharp>* P"*)
      and  "A\<^sub>P \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>"
      and  "yvec \<sharp>* P"
      and  "yvec \<sharp>* Q"    
      and  "yvec \<sharp>* \<Psi>\<^sub>Q"
      and  "yvec \<sharp>* A\<^sub>Q"
      and  "yvec \<sharp>* \<Psi>\<^sub>P"    
      and  "yvec \<sharp>* A\<^sub>P"
      and  "yvec \<sharp>* M"
      and  "yvec \<sharp>* N"
      and  "yvec \<sharp>* P'"
      and  "yvec \<sharp>* Q'"
      and  "yvec \<sharp>* xvec"
      and  "yvec \<sharp>* zvec"    
      and  "A\<^sub>Q \<sharp>* \<Psi>"
      and  "A\<^sub>Q \<sharp>* P"
(*      and  "A\<^sub>Q \<sharp>* Q"*)
      and  "zvec \<sharp>* \<Psi>"
      and  "zvec \<sharp>* P"
      and  "zvec \<sharp>* Q"
      and  "zvec \<sharp>* \<Psi>\<^sub>Q"
      and  "zvec \<sharp>* A\<^sub>Q"
      and  "zvec \<sharp>* \<Psi>\<^sub>P"    
      and  "zvec \<sharp>* A\<^sub>P"
      and  "zvec \<sharp>* K"
      and  "zvec \<sharp>* N"
      and  "zvec \<sharp>* P'"
      and  "zvec \<sharp>* Q'"
      and  "zvec \<sharp>* xvec"
      and  "xvec \<sharp>* P"
      and  "distinct yvec"
      and  "distinct zvec"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -
      obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* (M)"
                             and "(r \<bullet> xvec) \<sharp>* (K)" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                             and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(r \<bullet> xvec) \<sharp>* xvec" and "(r \<bullet> xvec) \<sharp>* (yvec)" and "(r \<bullet> xvec) \<sharp>* (zvec)"
                             and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinct_perm r"
        by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,yvec,zvec)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* (K)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (M)"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q"
                             and Sq: "set q \<subseteq> set A\<^sub>Q \<times> set(q \<bullet> A\<^sub>Q)" and "(q \<bullet> A\<^sub>Q) \<sharp>* xvec" and "(q \<bullet> A\<^sub>Q) \<sharp>* (yvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (zvec)"
        by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, M, K, r \<bullet> N, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P',xvec,yvec,zvec)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* (M)" and "(p \<bullet> A\<^sub>P) \<sharp>* (K)"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')" 
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
        and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
        and "(p \<bullet> A\<^sub>P) \<sharp>* xvec" and "(p \<bullet> A\<^sub>P) \<sharp>* (yvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (zvec)"
        by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, K, r \<bullet> N, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P',xvec,yvec,zvec)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

      have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
(*      
      from `A\<^sub>P \<sharp>* Q` FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      from `A\<^sub>Q \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh_chain) auto !ruh ruh!*)
      from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* A\<^sub>P` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)"
	by(simp add: fresh_chain_simps)

      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'` Sr `distinct_perm r` `xvec \<sharp>* P` `(r \<bullet> xvec) \<sharp>* P`
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')"
	by(rule input_alpha)
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ (q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq `A\<^sub>Q \<sharp>* P` `(q \<bullet> A\<^sub>Q) \<sharp>* P`
	by(rule_tac input_perm_frame_subject) (assumption | simp)+
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*(p\<bullet>A\<^sub>P)\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert (p\<bullet>K))))) @ (q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sp `yvec \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* yvec` `(p\<bullet>A\<^sub>P) \<sharp>* K`
        by(subst (asm) frame_chain_alpha[where p=p and xvec=A\<^sub>P])
          (force simp add: eqvts frame_chain_fresh_chain' frame_chain_fresh_chain)+
      hence P_trans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*(p\<bullet>A\<^sub>P)\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert (p\<bullet>K))))) @ (q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq `A\<^sub>Q \<sharp>* \<Psi>` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>` (*`A\<^sub>Q \<sharp>* M` `(q \<bullet> A\<^sub>Q) \<sharp>* M`*)
	by(simp add: eqvts)
      moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`  Sp `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P`
      have FrP: "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
	by(simp add: frame_chain_alpha)
      moreover from `distinct A\<^sub>P` have "distinct(p \<bullet> A\<^sub>P)"  by simp
      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` Sr `(r \<bullet> xvec) \<sharp>* N` `(r \<bullet> xvec) \<sharp>* Q'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')"
	by(simp add: bound_output_chain_alpha'' create_residual.simps)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ (p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp `A\<^sub>P \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(r \<bullet> xvec) \<sharp>* K` `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)`
        by(rule_tac output_perm_frame_subject) simp+
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*(q\<bullet>A\<^sub>Q)\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert (q\<bullet>M))))) @ (p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sq `zvec \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* zvec` `(q\<bullet>A\<^sub>Q) \<sharp>* M`
        by(subst (asm) frame_chain_alpha[where p=q and xvec=A\<^sub>Q])
          (force simp add: eqvts frame_chain_fresh_chain' frame_chain_fresh_chain)+
      hence Q_trans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*(q\<bullet>A\<^sub>Q)\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert (q\<bullet>M))))) @ (p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp `A\<^sub>P \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>`
	by(simp add: eqvts)
      moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`  Sq `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q`
      have FrQ: "extract_frame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
	by(simp add: frame_chain_alpha)
      moreover from `distinct A\<^sub>Q` have "distinct(q \<bullet> A\<^sub>Q)"  by simp
      moreover note `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>`            
      moreover from `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q` Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)" 
	by(simp add: fresh_chain_simps)
      moreover note `(p \<bullet> A\<^sub>P) \<sharp>* P`       
      moreover from `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` `(p \<bullet> A\<^sub>P) \<sharp>* M` Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)"
	by(simp add: fresh_chain_simps)
      moreover note  `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)`
                     `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>`      
      moreover from `(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
	by(simp add: fresh_chain_simps)
      moreover note `(q \<bullet> A\<^sub>Q) \<sharp>* P` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)``(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')` `(q \<bullet> A\<^sub>Q) \<sharp>* Q` 
      moreover from `(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
	by(simp add: fresh_chain_simps)
      moreover note  `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')`
      moreover note `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)`
      moreover from Q_trans have "distinct(r \<bullet> xvec)" by(force dest: bound_output_distinct)
      moreover note `(r \<bullet> xvec) \<sharp>* \<Psi>`
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
	by(simp add: fresh_chain_simps)
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q` Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
	by(simp add: fresh_chain_simps)
      moreover note `(r \<bullet> xvec) \<sharp>* P` 
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* M` Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"
        by(simp add: fresh_chain_simps)
      moreover note `(r \<bullet> xvec) \<sharp>* Q`
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* K` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"  
	by(simp add: fresh_chain_simps)
      moreover note `distinct yvec` `distinct zvec` `yvec \<sharp>* \<Psi>`
      moreover have "yvec \<sharp>* (p\<bullet>\<Psi>\<^sub>P)"
        using Sp `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover have "yvec \<sharp>* (q\<bullet>\<Psi>\<^sub>Q)"
        using Sq `yvec \<sharp>* \<Psi>\<^sub>Q` `yvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover note `yvec \<sharp>* P`
      moreover have "yvec \<sharp>* (q\<bullet>M)"
        using Sq `yvec \<sharp>* M` `yvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover from `(r \<bullet> xvec) \<sharp>* yvec` have "yvec \<sharp>* (r \<bullet> xvec)"
        by simp
      moreover note `yvec \<sharp>* Q`
      moreover have "yvec \<sharp>* (p\<bullet>A\<^sub>P)"
        using `(p\<bullet>A\<^sub>P) \<sharp>* yvec` by simp
      moreover have "yvec \<sharp>* (q\<bullet>A\<^sub>Q)"
        using `(q\<bullet>A\<^sub>Q) \<sharp>* yvec` by simp
      moreover have "yvec \<sharp>* (r\<bullet>P')"
        using Sr `yvec \<sharp>* P'` `yvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover have "yvec \<sharp>* (r\<bullet>Q')"
        using Sr `yvec \<sharp>* Q'` `yvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover note `yvec \<sharp>* zvec` `zvec \<sharp>* \<Psi>`
      moreover have "zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>P)"
        using Sp `zvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover have "zvec \<sharp>* (q\<bullet>\<Psi>\<^sub>Q)"
        using Sq `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover note `zvec \<sharp>* P`
      moreover have "zvec \<sharp>* (p\<bullet>K)"
        using Sp `zvec \<sharp>* K` `zvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover from `(r\<bullet>xvec) \<sharp>* zvec` have "zvec \<sharp>* (r\<bullet>xvec)"
        by simp
      moreover note `zvec \<sharp>* Q`
      moreover have "zvec \<sharp>* (p\<bullet>A\<^sub>P)"
        using `(p\<bullet>A\<^sub>P) \<sharp>* zvec` by simp
      moreover have "zvec \<sharp>* (q\<bullet>A\<^sub>Q)"
        using `(q\<bullet>A\<^sub>Q) \<sharp>* zvec` by simp
      moreover have "zvec \<sharp>* (r\<bullet>P')"
        using Sr `zvec \<sharp>* P'` `zvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover have "zvec \<sharp>* (r\<bullet>Q')"
        using Sr `zvec \<sharp>* Q'` `zvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))"      
	by(rule c_comm1)
      with `(r \<bullet> xvec) \<sharp>* P'` `(r \<bullet> xvec) \<sharp>* Q'` Sr 
      show ?thesis
	by(subst res_chain_alpha) auto
    qed
  }
  note Goal = this
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and xvec :: "name list"
    and yvec :: "name list"
    and zvec :: "name list"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
      and  "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and  "distinct A\<^sub>P"
      and  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      and  "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
      and  "distinct A\<^sub>Q"
      and  "A\<^sub>P \<sharp>* \<Psi>"
(*      and  "A\<^sub>P \<sharp>* P"*)
      and  "A\<^sub>P \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>"
      and  "yvec \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>\<^sub>P"
      and  "A\<^sub>Q \<sharp>* \<Psi>"
      and  "A\<^sub>Q \<sharp>* P"
(*      and  "A\<^sub>Q \<sharp>* Q"*)
      and  "zvec \<sharp>* \<Psi>"
      and  "zvec \<sharp>* P"
      and  "zvec \<sharp>* \<Psi>\<^sub>Q"
      and  "xvec \<sharp>* P"
      and  "distinct yvec"
      and  "distinct zvec"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -
      obtain s::"name prm" where "(s \<bullet> yvec) \<sharp>* \<Psi>" and "(s \<bullet> yvec) \<sharp>* P" and "(s \<bullet> yvec) \<sharp>* Q" and "(s \<bullet> yvec) \<sharp>* M"
                             and "(s \<bullet> yvec) \<sharp>* K" and "(s \<bullet> yvec) \<sharp>* N" and "(s \<bullet> yvec) \<sharp>* A\<^sub>P" and "(s \<bullet> yvec) \<sharp>* A\<^sub>Q"
                             and "(s \<bullet> yvec) \<sharp>* P'" and "(s \<bullet> yvec) \<sharp>* Q'" and "(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>P" and "(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>Q" and "(s \<bullet> yvec) \<sharp>* xvec" and "(s \<bullet> yvec) \<sharp>* zvec" and "(s \<bullet> yvec) \<sharp>* yvec"
                             and Ss: "(set s) \<subseteq> (set yvec) \<times> (set(s \<bullet> yvec))" and "distinct_perm s"
        by(rule_tac xvec=yvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,zvec,yvec)" in name_list_avoiding) (auto simp add: eqvts fresh_star_prod)
      obtain t::"name prm" where "(t \<bullet> zvec) \<sharp>* \<Psi>" and "(t \<bullet> zvec) \<sharp>* P" and "(t \<bullet> zvec) \<sharp>* Q" and "(t \<bullet> zvec) \<sharp>* M"
                             and "(t \<bullet> zvec) \<sharp>* (s\<bullet>K)" and "(t \<bullet> zvec) \<sharp>* N" and "(t \<bullet> zvec) \<sharp>* A\<^sub>P" and "(t \<bullet> zvec) \<sharp>* A\<^sub>Q"
                             and "(t \<bullet> zvec) \<sharp>* P'" and "(t \<bullet> zvec) \<sharp>* Q'" and "(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>P" and "(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>Q" and "(t \<bullet> zvec) \<sharp>* xvec" and "(t \<bullet> zvec) \<sharp>* (s\<bullet>yvec)" and "(t \<bullet> zvec) \<sharp>* (yvec)" and "(t \<bullet> zvec) \<sharp>* zvec" and "(t \<bullet> zvec) \<sharp>* s"
                             and St: "(set t) \<subseteq> (set zvec) \<times> (set(t \<bullet> zvec))" and "distinct_perm t"
        by(rule_tac xvec=zvec and c="(\<Psi>, P, Q, M, s\<bullet>K, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,s\<bullet>yvec, yvec, zvec, s)" in name_list_avoiding) (auto simp add: eqvts fresh_star_prod)      
(*      
      from `A\<^sub>P \<sharp>* Q` FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      from `A\<^sub>Q \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh_chain) auto !ruh ruh!*)
      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>P\<rparr>(F_assert(\<lparr>\<nu>*(s\<bullet>yvec)\<rparr>(F_assert (s\<bullet>K))))) @ M\<lparr>N\<rparr> \<prec> P'"
        using `(s\<bullet>yvec) \<sharp>* K` Ss
        by(subst (asm) frame_chain_alpha)
          (auto simp add: frame_chain_fresh_chain' frame_chain_fresh_chain)
      hence P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>P\<rparr>(F_assert(\<lparr>\<nu>*(s\<bullet>yvec)\<rparr>(F_assert (s\<bullet>K))))) @ (t\<bullet>M)\<lparr>N\<rparr> \<prec> P'"
        using St `zvec \<sharp>* P` `(t\<bullet>zvec) \<sharp>* P` `zvec \<sharp>* \<Psi>` `(t\<bullet>zvec) \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>Q` `(t\<bullet>zvec) \<sharp>* \<Psi>\<^sub>Q`
        by(drule_tac input_perm_subject) (auto simp add: eqvts)
      moreover have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      moreover note `distinct A\<^sub>P`
      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>Q\<rparr>(F_assert(\<lparr>\<nu>*(t\<bullet>zvec)\<rparr>(F_assert (t\<bullet>M))))) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        using `(t\<bullet>zvec) \<sharp>* M` St
        by(subst (asm) frame_chain_alpha)
          (auto simp add: frame_chain_fresh_chain' frame_chain_fresh_chain)
      hence Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>Q\<rparr>(F_assert(\<lparr>\<nu>*(t\<bullet>zvec)\<rparr>(F_assert (t\<bullet>M))))) @ (s\<bullet>K)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        using Ss `yvec \<sharp>* Q` `(s\<bullet>yvec) \<sharp>* Q` `yvec \<sharp>* \<Psi>` `(s\<bullet>yvec) \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `(s\<bullet>yvec) \<sharp>* \<Psi>\<^sub>P`
        by(auto intro: output_perm_subject)
      moreover have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      moreover note `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>` `(s \<bullet> yvec) \<sharp>* P` `(s \<bullet> yvec) \<sharp>* Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>Q` `(s \<bullet> yvec) \<sharp>* A\<^sub>Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>P`
        `(s \<bullet> yvec) \<sharp>* A\<^sub>P`
      moreover from `(s \<bullet> yvec) \<sharp>* zvec` `(t \<bullet> zvec) \<sharp>* yvec` `(s \<bullet> yvec) \<sharp>* M` `(t \<bullet> zvec) \<sharp>* (s \<bullet> yvec)` St Ss have "(s \<bullet> yvec) \<sharp>* (t \<bullet> M)"
	by(simp add: fresh_chain_simps)
      moreover note `(s \<bullet> yvec) \<sharp>* N`
        `(s \<bullet> yvec) \<sharp>* P'` `(s \<bullet> yvec) \<sharp>* Q'`
        `(s \<bullet> yvec) \<sharp>* xvec`
      moreover have "(s \<bullet> yvec) \<sharp>* (t \<bullet> zvec)" using `(t \<bullet> zvec) \<sharp>* (s \<bullet> yvec)`
        by simp
      moreover note `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P`
        `(t \<bullet> zvec) \<sharp>* \<Psi>` `(t \<bullet> zvec) \<sharp>* P` `(t \<bullet> zvec) \<sharp>* Q`
        `(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>Q` `(t \<bullet> zvec) \<sharp>* A\<^sub>Q`
        `(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>P`
        `(t \<bullet> zvec) \<sharp>* A\<^sub>P` `(t \<bullet> zvec) \<sharp>* (s \<bullet> K)`
        `(t \<bullet> zvec) \<sharp>* N`
        `(t \<bullet> zvec) \<sharp>* P'` `(t \<bullet> zvec) \<sharp>* Q'`
        `(t \<bullet> zvec) \<sharp>* xvec`
        `xvec \<sharp>* P`
      moreover from `distinct yvec` have "distinct(s\<bullet>yvec)" by simp
      moreover from `distinct zvec` have "distinct(t\<bullet>zvec)" by simp
      ultimately show ?thesis
	by(rule Goal)
    qed
  }
  note Goal = this
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
    `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
  moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q`
  obtain A\<^sub>P' where "extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* Q"
    and "\<langle>A\<^sub>P; yvec, K\<rangle> = \<lparr>\<nu>*A\<^sub>P'\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert K)))"
    by(rule_tac C="(\<Psi>, Q)" in distinct_frames_eq) auto
  moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P`
  obtain A\<^sub>Q' where "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P"
    and "\<langle>A\<^sub>Q; zvec, M\<rangle> = \<lparr>\<nu>*A\<^sub>Q'\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert M)))"
    by(rule_tac C="(\<Psi>, P)" in distinct_frames_eq) auto
  moreover from `yvec \<sharp>* \<Psi>` `yvec \<sharp>* Q`  and `yvec \<sharp>* \<Psi>\<^sub>P`
  obtain yvec' where "distinct yvec'" and "yvec' \<sharp>* \<Psi>" and "yvec' \<sharp>* Q"  and "yvec' \<sharp>* \<Psi>\<^sub>P"
    and "\<lparr>\<nu>*yvec\<rparr>(F_assert K) = \<lparr>\<nu>*yvec'\<rparr>(F_assert K)"
    by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>P)" in distinct_frame) auto
  moreover from `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P`  and `zvec \<sharp>* \<Psi>\<^sub>Q`
  obtain zvec' where "distinct zvec'" and "zvec' \<sharp>* \<Psi>" and "zvec' \<sharp>* P"  and "zvec' \<sharp>* \<Psi>\<^sub>Q"
    and "\<lparr>\<nu>*zvec\<rparr>(F_assert M) = \<lparr>\<nu>*zvec'\<rparr>(F_assert M)"
    by(rule_tac C="(\<Psi>, P, \<Psi>\<^sub>Q)" in distinct_frame) auto
  ultimately show ?thesis using `xvec \<sharp>* P`
    by(simp only:) (rule_tac Goal)
qed

lemma Comm2:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   xvec :: "name list"
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  
  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* \<Psi>\<^sub>P"
  and     "yvec \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "zvec \<sharp>* \<Psi>"  
  and     "zvec \<sharp>* P"
  and     "zvec \<sharp>* \<Psi>\<^sub>Q"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and xvec :: "name list"
    and yvec :: "name list"
    and zvec :: "name list"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      and  "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and  "distinct A\<^sub>P"
      and  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'"
      and  "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
      and  "distinct A\<^sub>Q"
      and  "A\<^sub>P \<sharp>* \<Psi>"
      and  "A\<^sub>P \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>"
      and  "yvec \<sharp>* P"
      and  "yvec \<sharp>* Q"    
      and  "yvec \<sharp>* \<Psi>\<^sub>Q"
      and  "yvec \<sharp>* A\<^sub>Q"
      and  "yvec \<sharp>* \<Psi>\<^sub>P"    
      and  "yvec \<sharp>* A\<^sub>P"
      and  "yvec \<sharp>* M"
      and  "yvec \<sharp>* N"
      and  "yvec \<sharp>* P'"
      and  "yvec \<sharp>* Q'"
      and  "yvec \<sharp>* xvec"
      and  "yvec \<sharp>* zvec"    
      and  "A\<^sub>Q \<sharp>* \<Psi>"
      and  "A\<^sub>Q \<sharp>* P"
      and  "zvec \<sharp>* \<Psi>"
      and  "zvec \<sharp>* P"
      and  "zvec \<sharp>* Q"
      and  "zvec \<sharp>* \<Psi>\<^sub>Q"
      and  "zvec \<sharp>* A\<^sub>Q"
      and  "zvec \<sharp>* \<Psi>\<^sub>P"    
      and  "zvec \<sharp>* A\<^sub>P"
      and  "zvec \<sharp>* K"
      and  "zvec \<sharp>* N"
      and  "zvec \<sharp>* P'"
      and  "zvec \<sharp>* Q'"
      and  "zvec \<sharp>* xvec"
      and  "xvec \<sharp>* Q"
      and  "distinct yvec"
      and  "distinct zvec"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -
      obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* (M)"
                             and "(r \<bullet> xvec) \<sharp>* (K)" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                             and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(r \<bullet> xvec) \<sharp>* xvec" and "(r \<bullet> xvec) \<sharp>* (yvec)" and "(r \<bullet> xvec) \<sharp>* (zvec)"
                             and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinct_perm r"
        by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,yvec,zvec)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* (K)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (M)"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q"
                             and Sq: "set q \<subseteq> set A\<^sub>Q \<times> set(q \<bullet> A\<^sub>Q)" and "(q \<bullet> A\<^sub>Q) \<sharp>* xvec" and "(q \<bullet> A\<^sub>Q) \<sharp>* (yvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (zvec)"
        by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, M, K, r \<bullet> N, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P',xvec,yvec,zvec)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* (M)" and "(p \<bullet> A\<^sub>P) \<sharp>* (K)"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')" 
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
        and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
        and "(p \<bullet> A\<^sub>P) \<sharp>* xvec" and "(p \<bullet> A\<^sub>P) \<sharp>* (yvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (zvec)"
        by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, K, r \<bullet> N, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P',xvec,yvec,zvec)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

      have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* A\<^sub>P` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)"
	by(simp add: fresh_chain_simps)
      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` Sr `(r \<bullet> xvec) \<sharp>* N` `(r \<bullet> xvec) \<sharp>* P'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')"
	by(simp add: bound_output_chain_alpha'' create_residual.simps)
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ (q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq `A\<^sub>Q \<sharp>* P` `(q \<bullet> A\<^sub>Q) \<sharp>* P`
	by(rule_tac output_perm_frame_subject) (assumption | simp)+
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*(p\<bullet>A\<^sub>P)\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert (p\<bullet>K))))) @ (q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sp `yvec \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* yvec` `(p\<bullet>A\<^sub>P) \<sharp>* K`
        by(subst (asm) frame_chain_alpha[where p=p and xvec=A\<^sub>P])
          (force simp add: eqvts frame_chain_fresh_chain' frame_chain_fresh_chain)+
      hence P_trans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*(p\<bullet>A\<^sub>P)\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert (p\<bullet>K))))) @ (q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq `A\<^sub>Q \<sharp>* \<Psi>` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>` (*`A\<^sub>Q \<sharp>* M` `(q \<bullet> A\<^sub>Q) \<sharp>* M`*)
	by(simp add: eqvts)
      moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`  Sp `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P`
      have FrP: "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
	by(simp add: frame_chain_alpha)
      moreover from `distinct A\<^sub>P` have "distinct(p \<bullet> A\<^sub>P)"  by simp
      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'` Sr `(r \<bullet> xvec) \<sharp>* N` `(r \<bullet> xvec) \<sharp>* Q'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using
        Sr `distinct_perm r` `xvec \<sharp>* Q` `(r \<bullet> xvec) \<sharp>* Q`
	by(rule_tac input_alpha)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ (p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp `A\<^sub>P \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(r \<bullet> xvec) \<sharp>* K` `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)`
        by(rule_tac input_perm_frame_subject) simp+
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*(q\<bullet>A\<^sub>Q)\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert (q\<bullet>M))))) @ (p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sq `zvec \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* zvec` `(q\<bullet>A\<^sub>Q) \<sharp>* M`
        by(subst (asm) frame_chain_alpha[where p=q and xvec=A\<^sub>Q])
          (force simp add: eqvts frame_chain_fresh_chain' frame_chain_fresh_chain)+
      hence Q_trans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*(q\<bullet>A\<^sub>Q)\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert (q\<bullet>M))))) @ (p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp `A\<^sub>P \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>`
	by(simp add: eqvts)
      moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`  Sq `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q`
      have FrQ: "extract_frame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
	by(simp add: frame_chain_alpha)
      moreover from `distinct A\<^sub>Q` have "distinct(q \<bullet> A\<^sub>Q)"  by simp
      moreover note `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>`            
      moreover from `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q` Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)" 
	by(simp add: fresh_chain_simps)
      moreover note `(p \<bullet> A\<^sub>P) \<sharp>* P`       
      moreover from `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` `(p \<bullet> A\<^sub>P) \<sharp>* M` Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)"
	by(simp add: fresh_chain_simps)
      moreover note  `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')` `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)`
                     `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>`      
      moreover from `(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
	by(simp add: fresh_chain_simps)
      moreover note `(q \<bullet> A\<^sub>Q) \<sharp>* P` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)``(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')` `(q \<bullet> A\<^sub>Q) \<sharp>* Q` 
      moreover from `(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)` Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
	by(simp add: fresh_chain_simps)
      moreover note  `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')`
      moreover note `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)`
      moreover from P_trans have "distinct(r \<bullet> xvec)" by(force dest: bound_output_distinct)
      moreover note `(r \<bullet> xvec) \<sharp>* \<Psi>`
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
	by(simp add: fresh_chain_simps)
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q` Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
	by(simp add: fresh_chain_simps)
      moreover note `(r \<bullet> xvec) \<sharp>* P` 
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>Q` `(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* M` Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"
        by(simp add: fresh_chain_simps)
      moreover note `(r \<bullet> xvec) \<sharp>* Q`
      moreover from `(r \<bullet> xvec) \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)` `(r \<bullet> xvec) \<sharp>* K` Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"  
	by(simp add: fresh_chain_simps)
      moreover note `distinct yvec` `distinct zvec` `yvec \<sharp>* \<Psi>`
      moreover have "yvec \<sharp>* (p\<bullet>\<Psi>\<^sub>P)"
        using Sp `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover have "yvec \<sharp>* (q\<bullet>\<Psi>\<^sub>Q)"
        using Sq `yvec \<sharp>* \<Psi>\<^sub>Q` `yvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover note `yvec \<sharp>* P`
      moreover have "yvec \<sharp>* (q\<bullet>M)"
        using Sq `yvec \<sharp>* M` `yvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover from `(r\<bullet>xvec) \<sharp>* yvec` have "yvec \<sharp>* (r\<bullet>xvec)" by simp
      moreover note `yvec \<sharp>* Q`
      moreover have "yvec \<sharp>* (p\<bullet>A\<^sub>P)"
        using `(p\<bullet>A\<^sub>P) \<sharp>* yvec` by simp
      moreover have "yvec \<sharp>* (q\<bullet>A\<^sub>Q)"
        using `(q\<bullet>A\<^sub>Q) \<sharp>* yvec` by simp
      moreover have "yvec \<sharp>* (r\<bullet>P')"
        using Sr `yvec \<sharp>* P'` `yvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover have "yvec \<sharp>* (r\<bullet>Q')"
        using Sr `yvec \<sharp>* Q'` `yvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* yvec`
	by(simp add: fresh_chain_simps)
      moreover note `yvec \<sharp>* zvec` `zvec \<sharp>* \<Psi>`
      moreover have "zvec \<sharp>* (p\<bullet>\<Psi>\<^sub>P)"
        using Sp `zvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover have "zvec \<sharp>* (q\<bullet>\<Psi>\<^sub>Q)"
        using Sq `zvec \<sharp>* \<Psi>\<^sub>Q` `zvec \<sharp>* A\<^sub>Q`  `(q\<bullet>A\<^sub>Q) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover note `zvec \<sharp>* P`
      moreover have "zvec \<sharp>* (p\<bullet>K)"
        using Sp `zvec \<sharp>* K` `zvec \<sharp>* A\<^sub>P`  `(p\<bullet>A\<^sub>P) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover from `(r\<bullet>xvec) \<sharp>* zvec` have "zvec \<sharp>* (r\<bullet>xvec)" by simp      
      moreover note `zvec \<sharp>* Q`
      moreover have "zvec \<sharp>* (p\<bullet>A\<^sub>P)"
        using `(p\<bullet>A\<^sub>P) \<sharp>* zvec` by simp
      moreover have "zvec \<sharp>* (q\<bullet>A\<^sub>Q)"
        using `(q\<bullet>A\<^sub>Q) \<sharp>* zvec` by simp
      moreover have "zvec \<sharp>* (r\<bullet>P')"
        using Sr `zvec \<sharp>* P'` `zvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)
      moreover have "zvec \<sharp>* (r\<bullet>Q')"
        using Sr `zvec \<sharp>* Q'` `zvec \<sharp>* xvec`  `(r\<bullet>xvec) \<sharp>* zvec`
	by(simp add: fresh_chain_simps)      
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))"
	by(rule c_comm2)
      with `(r \<bullet> xvec) \<sharp>* P'` `(r \<bullet> xvec) \<sharp>* Q'` Sr 
      show ?thesis
	by(subst res_chain_alpha) auto
    qed
  }
  note Goal = this
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and xvec :: "name list"
    and yvec :: "name list"
    and zvec :: "name list"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      and  "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
      and  "distinct A\<^sub>P"
      and  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'"
      and  "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
      and  "distinct A\<^sub>Q"
      and  "A\<^sub>P \<sharp>* \<Psi>"
      and  "A\<^sub>P \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>"
      and  "yvec \<sharp>* Q"
      and  "yvec \<sharp>* \<Psi>\<^sub>P"
      and  "A\<^sub>Q \<sharp>* \<Psi>"
      and  "A\<^sub>Q \<sharp>* P"
      and  "zvec \<sharp>* \<Psi>"
      and  "zvec \<sharp>* P"
      and  "zvec \<sharp>* \<Psi>\<^sub>Q"
      and  "xvec \<sharp>* Q"
      and  "distinct yvec"
      and  "distinct zvec"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -
      obtain s::"name prm" where "(s \<bullet> yvec) \<sharp>* \<Psi>" and "(s \<bullet> yvec) \<sharp>* P" and "(s \<bullet> yvec) \<sharp>* Q" and "(s \<bullet> yvec) \<sharp>* M"
                             and "(s \<bullet> yvec) \<sharp>* K" and "(s \<bullet> yvec) \<sharp>* N" and "(s \<bullet> yvec) \<sharp>* A\<^sub>P" and "(s \<bullet> yvec) \<sharp>* A\<^sub>Q"
                             and "(s \<bullet> yvec) \<sharp>* P'" and "(s \<bullet> yvec) \<sharp>* Q'" and "(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>P" and "(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>Q" and "(s \<bullet> yvec) \<sharp>* xvec" and "(s \<bullet> yvec) \<sharp>* zvec" and "(s \<bullet> yvec) \<sharp>* yvec"
                             and Ss: "(set s) \<subseteq> (set yvec) \<times> (set(s \<bullet> yvec))" and "distinct_perm s"
        by(rule_tac xvec=yvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,zvec,yvec)" in name_list_avoiding) (auto simp add: eqvts fresh_star_prod)
      obtain t::"name prm" where "(t \<bullet> zvec) \<sharp>* \<Psi>" and "(t \<bullet> zvec) \<sharp>* P" and "(t \<bullet> zvec) \<sharp>* Q" and "(t \<bullet> zvec) \<sharp>* M"
                             and "(t \<bullet> zvec) \<sharp>* (s\<bullet>K)" and "(t \<bullet> zvec) \<sharp>* N" and "(t \<bullet> zvec) \<sharp>* A\<^sub>P" and "(t \<bullet> zvec) \<sharp>* A\<^sub>Q"
                             and "(t \<bullet> zvec) \<sharp>* P'" and "(t \<bullet> zvec) \<sharp>* Q'" and "(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>P" and "(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>Q" and "(t \<bullet> zvec) \<sharp>* xvec" and "(t \<bullet> zvec) \<sharp>* (s\<bullet>yvec)" and "(t \<bullet> zvec) \<sharp>* (yvec)" and "(t \<bullet> zvec) \<sharp>* zvec" and "(t \<bullet> zvec) \<sharp>* s"
                             and St: "(set t) \<subseteq> (set zvec) \<times> (set(t \<bullet> zvec))" and "distinct_perm t"
        by(rule_tac xvec=zvec and c="(\<Psi>, P, Q, M, s\<bullet>K, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q',xvec,s\<bullet>yvec, yvec, zvec, s)" in name_list_avoiding) (auto simp add: eqvts fresh_star_prod)      
      from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>P\<rparr>(F_assert(\<lparr>\<nu>*(s\<bullet>yvec)\<rparr>(F_assert (s\<bullet>K))))) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        using `(s\<bullet>yvec) \<sharp>* K` Ss
        by(subst (asm) frame_chain_alpha)
          (auto simp add: frame_chain_fresh_chain' frame_chain_fresh_chain)
      hence P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>P\<rparr>(F_assert(\<lparr>\<nu>*(s\<bullet>yvec)\<rparr>(F_assert (s\<bullet>K))))) @ (t\<bullet>M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        using St `zvec \<sharp>* P` `(t\<bullet>zvec) \<sharp>* P` `zvec \<sharp>* \<Psi>` `(t\<bullet>zvec) \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>Q` `(t\<bullet>zvec) \<sharp>* \<Psi>\<^sub>Q`
        by(auto intro: output_perm_subject)
      moreover have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      moreover note `distinct A\<^sub>P`
      moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>Q\<rparr>(F_assert(\<lparr>\<nu>*(t\<bullet>zvec)\<rparr>(F_assert (t\<bullet>M))))) @ K\<lparr>N\<rparr> \<prec> Q'"
        using `(t\<bullet>zvec) \<sharp>* M` St
        by(subst (asm) frame_chain_alpha)
          (auto simp add: frame_chain_fresh_chain' frame_chain_fresh_chain)
      hence Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<lparr>\<nu>*A\<^sub>Q\<rparr>(F_assert(\<lparr>\<nu>*(t\<bullet>zvec)\<rparr>(F_assert (t\<bullet>M))))) @ (s\<bullet>K)\<lparr>N\<rparr> \<prec> Q'"
        using Ss `yvec \<sharp>* Q` `(s\<bullet>yvec) \<sharp>* Q` `yvec \<sharp>* \<Psi>` `(s\<bullet>yvec) \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `(s\<bullet>yvec) \<sharp>* \<Psi>\<^sub>P`
        by(drule_tac input_perm_subject) auto
      moreover have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      moreover note `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>` `(s \<bullet> yvec) \<sharp>* P` `(s \<bullet> yvec) \<sharp>* Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>Q` `(s \<bullet> yvec) \<sharp>* A\<^sub>Q`
        `(s \<bullet> yvec) \<sharp>* \<Psi>\<^sub>P`
        `(s \<bullet> yvec) \<sharp>* A\<^sub>P`
      moreover from `(s \<bullet> yvec) \<sharp>* zvec` `(t \<bullet> zvec) \<sharp>* yvec` `(s \<bullet> yvec) \<sharp>* M` `(t \<bullet> zvec) \<sharp>* (s \<bullet> yvec)` St Ss have "(s \<bullet> yvec) \<sharp>* (t \<bullet> M)"
	by(simp add: fresh_chain_simps)
      moreover note `(s \<bullet> yvec) \<sharp>* N`
        `(s \<bullet> yvec) \<sharp>* P'` `(s \<bullet> yvec) \<sharp>* Q'`
        `(s \<bullet> yvec) \<sharp>* xvec`
      moreover have "(s \<bullet> yvec) \<sharp>* (t \<bullet> zvec)" using `(t \<bullet> zvec) \<sharp>* (s \<bullet> yvec)`
        by simp
      moreover note `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P`
        `(t \<bullet> zvec) \<sharp>* \<Psi>` `(t \<bullet> zvec) \<sharp>* P` `(t \<bullet> zvec) \<sharp>* Q`
        `(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>Q` `(t \<bullet> zvec) \<sharp>* A\<^sub>Q`
        `(t \<bullet> zvec) \<sharp>* \<Psi>\<^sub>P`
        `(t \<bullet> zvec) \<sharp>* A\<^sub>P` `(t \<bullet> zvec) \<sharp>* (s \<bullet> K)`
        `(t \<bullet> zvec) \<sharp>* N`
        `(t \<bullet> zvec) \<sharp>* P'` `(t \<bullet> zvec) \<sharp>* Q'`
        `(t \<bullet> zvec) \<sharp>* xvec`
        `xvec \<sharp>* Q`
      moreover from `distinct yvec` have "distinct(s\<bullet>yvec)" by simp
      moreover from `distinct zvec` have "distinct(t\<bullet>zvec)" by simp
      ultimately show ?thesis
	by(rule Goal)
    qed
  }
  note Goal = this
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
    `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
  moreover from `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q`
  obtain A\<^sub>P' where "extract_frame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* Q"
    and "\<langle>A\<^sub>P; yvec, K\<rangle> = \<lparr>\<nu>*A\<^sub>P'\<rparr>(F_assert(\<lparr>\<nu>*yvec\<rparr>(F_assert K)))"
    by(rule_tac C="(\<Psi>, Q)" in distinct_frames_eq) auto
  moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P`
  obtain A\<^sub>Q' where "extract_frame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P"
    and "\<langle>A\<^sub>Q; zvec, M\<rangle> = \<lparr>\<nu>*A\<^sub>Q'\<rparr>(F_assert(\<lparr>\<nu>*zvec\<rparr>(F_assert M)))"
    by(rule_tac C="(\<Psi>, P)" in distinct_frames_eq) auto
  moreover from `yvec \<sharp>* \<Psi>` `yvec \<sharp>* Q`  and `yvec \<sharp>* \<Psi>\<^sub>P`
  obtain yvec' where "distinct yvec'" and "yvec' \<sharp>* \<Psi>" and "yvec' \<sharp>* Q"  and "yvec' \<sharp>* \<Psi>\<^sub>P"
    and "\<lparr>\<nu>*yvec\<rparr>(F_assert K) = \<lparr>\<nu>*yvec'\<rparr>(F_assert K)"
    by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>P)" in distinct_frame) auto
  moreover from `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P`  and `zvec \<sharp>* \<Psi>\<^sub>Q`
  obtain zvec' where "distinct zvec'" and "zvec' \<sharp>* \<Psi>" and "zvec' \<sharp>* P"  and "zvec' \<sharp>* \<Psi>\<^sub>Q"
    and "\<lparr>\<nu>*zvec\<rparr>(F_assert M) = \<lparr>\<nu>*zvec'\<rparr>(F_assert M)"
    by(rule_tac C="(\<Psi>, P, \<Psi>\<^sub>Q)" in distinct_frame) auto
  ultimately show ?thesis using `xvec \<sharp>* Q`
    by(simp only:) (rule_tac Goal)
qed
 
lemma semantics_cases_aux[consumes 1, case_names c_input c_output c_case c_par1 c_par2 c_comm1 c_comm2 c_open c_scope c_bang]:
  fixes c\<Psi>  :: 'b
  and   cP  :: "('a, 'b, 'c) psi"
  and   c_rs :: "('a, 'b, 'c) residual"
  and   c\<pi> :: "'a frame frame option"
  and   C   :: "'d::fs_name"
  and   x   :: name

  assumes "\<Psi> \<rhd> cP \<longmapsto> c\<pi> @ c_rs"
  and     r_input: "\<And>M K xvec N Tvec P. \<lbrakk>cP = M\<lparr>\<lambda>*xvec N\<rparr>.P; c\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); c_rs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec];
                                            \<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N; length xvec=length Tvec;
                                            xvec \<sharp>* Tvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop"
  and     r_output: "\<And>M K N P. \<lbrakk>cP = M\<langle>N\<rangle>.P; c\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); c_rs = K\<langle>N\<rangle> \<prec> P; \<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop"
  and     r_case: "\<And>Cs P \<phi> \<pi>. \<lbrakk>cP = Cases Cs; c\<pi> = map_option (F_assert o push_prov) \<pi>; \<Psi> \<rhd> P \<longmapsto> \<pi> @ c_rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"

  and  r_par1: "\<And>\<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q. \<lbrakk>cP = P \<parallel> Q; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; c_rs = \<alpha> \<prec> (P' \<parallel> Q);
               (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto> \<pi> @ (\<alpha> \<prec> P'); extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
               A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* C; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<pi>; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha>  \<sharp>* \<Psi>\<^sub>Q; 
               bn \<alpha>  \<sharp>* Q; bn \<alpha>  \<sharp>* P; bn \<alpha>  \<sharp>* \<pi>; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
               Prop"
  and     r_par2:   "\<And>\<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P. \<lbrakk>cP = P \<parallel> Q; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; c_rs = \<alpha> \<prec> (P \<parallel> Q');
                      (\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* \<pi>; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop"
             
  and     r_comm1: "\<And>\<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec.
                   \<lbrakk>cP = P \<parallel> Q; c\<pi> = None; c_rs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
                    distinct xvec; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> Prop"
  and     r_comm2: "\<And>\<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec.
                   \<lbrakk>cP = P \<parallel> Q; c\<pi> = None; c_rs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
                    xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> Prop"
  and    r_open: "\<And>P \<pi> M xvec yvec N P' x.
                \<lbrakk>cP = \<lparr>\<nu>x\<rparr>P; c\<pi> = Some(\<lparr>\<nu>x\<rparr>\<pi>); c_rs = M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; 
                 \<Psi> \<rhd> P \<longmapsto> Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; x \<sharp> xvec; x \<sharp> yvec; x \<sharp> M; x \<sharp> \<Psi>; distinct xvec; distinct yvec;
                 xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; xvec \<sharp>* \<pi>; yvec \<sharp>* \<pi>; xvec \<sharp>* C; x \<sharp> C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                 Prop"
  and    r_scope: "\<And>P \<pi> \<alpha> P' x. \<lbrakk>cP = \<lparr>\<nu>x\<rparr>P; c\<pi> = map_option (F_res x) \<pi>; c_rs = \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P';
                                 \<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> C; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* \<pi>; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop"
  and    r_bang:  "\<And>P \<pi>. \<lbrakk>cP = !P; c\<pi> = map_option(F_assert o push_prov) \<pi>; \<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ c_rs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  shows Prop
using assms
by(nominal_induct avoiding: C rule: semantics.strong_induct) auto

nominal_primrec
  input_length :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> nat"
  and input_length'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> nat"
  and input_length'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi_case \<Rightarrow> nat"

where
  "input_length (\<zero>) = 0"
| "input_length (M\<langle>N\<rangle>.P) = 0"
| "input_length (M\<lparr>I) = input_length' I"
| "input_length (Case C) = 0"
| "input_length (P \<parallel> Q) = 0"
| "input_length (\<lparr>\<nu>x\<rparr>P) = 0"
| "input_length (\<lbrace>\<Psi>\<rbrace>) = 0"
| "input_length (!P) = 0"

| "input_length' (Trm M P) = 0"
| "input_length' (\<nu> y I) = 1 + (input_length' I)"

| "input_length'' (\<bottom>\<^sub>c) = 0"
| "input_length'' (\<box>\<Phi> \<Rightarrow> P C) = 0"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_nat)+

nominal_primrec bound_output_length :: "('a, 'b, 'c) bound_output \<Rightarrow> nat"
where
  "bound_output_length (B_out M P) = 0"
| "bound_output_length (B_step x B) = (bound_output_length B) + 1"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_nat)+
  
nominal_primrec residual_length :: "('a, 'b, 'c) residual \<Rightarrow> nat"
where
  "residual_length (R_in M N P) = 0"
| "residual_length (R_out M B) = bound_output_length B"
| "residual_length (R_tau P) = 0"
by(rule TrueI)+

lemma input_length_proc[simp]:
  shows "input_length(M\<lparr>\<lambda>*xvec N\<rparr>.P) = length xvec"
by(induct xvec) auto

lemma bound_output_length_simp[simp]:
  shows "residual_length(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P) = length xvec"
by(induct xvec) (auto simp add: residual_inject)

lemma bound_ouput_length_simp2[simp]:
  shows "residual_length(\<alpha> \<prec> P) = length(bn \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct, auto) (auto simp add: residual_inject)

lemmas [simp del] = input_length_input_length'_input_length''.simps residual_length.simps bound_output_length.simps

lemma construct_perm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  
  assumes "length xvec = length yvec"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinct_perm p" and "yvec = p \<bullet> xvec"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinct_perm p; yvec = p \<bullet> xvec\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec"
  proof(induct n arbitrary: xvec yvec)
    case(0 xvec yvec)
    thus ?case by simp
  next
    case(Suc n xvec yvec)
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `length xvec = length yvec` `xvec = x # xvec'`
    obtain y yvec' where "length xvec' = length yvec'" and "yvec = y#yvec'"
      by(case_tac yvec) auto
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    from `Suc n = length xvec` `xvec=x#xvec'` have "n = length xvec'" by simp
    with `length xvec' = length yvec'` `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'`
    obtain p where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "distinct_perm p" and "yvec' = p \<bullet> xvec'"
      by(drule_tac Suc) auto
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from `x \<sharp> xvec'` `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_list_nil fresh_list_cons fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S `distinct_perm p` `x \<noteq> y` have "distinct_perm((x, y)#p)" by auto
    moreover from `yvec' = p \<bullet> xvec'` `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: calc_atm fresh_chain_simps)
    ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma distinct_apend[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"

  shows "(set xvec \<inter> set yvec = {}) = xvec \<sharp>* yvec"
by(auto simp add: fresh_star_def name_list_supp fresh_def)

lemma length_aux:
  fixes xvec :: "name list"
  and   y    :: name
  and   yvec :: "name list"

  assumes "length xvec = length(y#yvec)"

  obtains z zvec where "xvec = z#zvec" and "length zvec = length yvec"
using assms
by(induct xvec arbitrary: yvec y) auto

lemma length_aux2:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "length xvec = length(yvec@y#zvec)"

  obtains xvec1 x xvec2 where "xvec=xvec1@x#xvec2" and "length xvec1 = length yvec" and "length xvec2 = length zvec"
proof -
  assume "\<And>xvec1 x xvec2.
        \<lbrakk>xvec = xvec1 @ x # xvec2; length xvec1 = length yvec;
         length xvec2 = length zvec\<rbrakk>
        \<Longrightarrow> thesis"
  moreover from assms have "\<exists>xvec1 x xvec2. xvec=xvec1@x#xvec2 \<and> length xvec1 = length yvec \<and> length xvec2 = length zvec"
    apply(rule_tac x="take (length yvec) xvec" in exI)
    apply(rule_tac x="hd(drop (length yvec) xvec)" in exI)
    apply(rule_tac x="tl(drop (length yvec) xvec)" in exI)
    by auto
  ultimately show ?thesis by blast
qed

lemma frame_alpha:
  fixes p    :: "name prm"
  and   x y :: "name"
  and   F    :: "'d::fs_name frame"

  assumes xvec_freshF: "y \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>([(y,x)] \<bullet> F)"
  using assms
  by(cases "x = y") (simp_all add: frame.inject alpha fresh_left calc_atm perm_swap)

lemma semantics_cases[consumes 11, case_names c_input c_case c_par1 c_par2 c_comm1 c_comm2 c_scope c_bang]:
  fixes \<Psi>  :: 'b
  and   cP  :: "('a, 'b, 'c) psi"
  and   c\<pi>  :: "'a frame frame option"
  and   c_rs :: "('a, 'b, 'c) residual"
  and   C   :: "'d::fs_name"
  and   x1   :: name
  and   x2   :: name
  and   xvec1 :: "name list"
  and   xvec2 :: "name list"
  and   xvec3 :: "name list"
  and   xvec4 :: "name list"
  and   xvec5 :: "name list"

  assumes "\<Psi> \<rhd> cP \<longmapsto>c\<pi> @ c_rs"
  and     "length xvec1 = input_length cP" and "distinct xvec1"
  and     "length xvec2 = residual_length c_rs" and "distinct xvec2"
  and     "length xvec3 = residual_length c_rs" and "distinct xvec3"
  and     "length xvec4 = residual_length c_rs" and "distinct xvec4"
  and     "length xvec5 = residual_length c_rs" and "distinct xvec5"
  and     r_input: "\<And>M K N Tvec P. (\<lbrakk>xvec1 \<sharp>* \<Psi>; xvec1 \<sharp>* cP; xvec1 \<sharp>* c\<pi>; xvec1 \<sharp>* c_rs\<rbrakk> \<Longrightarrow> cP = M\<lparr>\<lambda>*xvec1 N\<rparr>.P \<and> c\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>) \<and> c_rs = K\<lparr>(N[xvec1::=Tvec])\<rparr> \<prec> P[xvec1::=Tvec] \<and>
                                            \<Psi> \<turnstile> K \<leftrightarrow> M \<and> distinct xvec1 \<and> set xvec1 \<subseteq> supp N \<and> length xvec1=length Tvec \<and>
                                            xvec1 \<sharp>* Tvec \<and> xvec1 \<sharp>* \<Psi> \<and> xvec1 \<sharp>* M \<and> xvec1 \<sharp>* K) \<Longrightarrow> Prop"
  and     r_output: "\<And>M K N P. \<lbrakk>cP = M\<langle>N\<rangle>.P; c\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); c_rs = K\<langle>N\<rangle> \<prec> P; \<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop"
  and     r_case: "\<And>Cs P \<pi> \<phi>. \<lbrakk>cP = Cases Cs; c\<pi> = map_option (F_assert o push_prov) \<pi>; \<Psi> \<rhd> P \<longmapsto>\<pi> @ c_rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"
  and     r_par1: "\<And>\<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q. (\<lbrakk>xvec2 \<sharp>* \<Psi>; xvec2 \<sharp>* cP; xvec2 \<sharp>* c_rs; xvec2 \<sharp>* c\<pi>\<rbrakk> \<Longrightarrow> 
                                         cP = P \<parallel> Q \<and> c_rs = \<alpha> \<prec> (P' \<parallel> Q) \<and> c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q \<and> xvec2 = bn \<alpha> \<and>
                                          \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle> \<and> distinct A\<^sub>Q \<and>
                                          A\<^sub>Q \<sharp>* P \<and> A\<^sub>Q \<sharp>* Q \<and> A\<^sub>Q \<sharp>* \<Psi> \<and> A\<^sub>Q \<sharp>* \<alpha> \<and> A\<^sub>Q \<sharp>* P' \<and> A\<^sub>Q \<sharp>* \<pi> \<and> A\<^sub>Q \<sharp>* C) \<Longrightarrow> Prop"
  and     r_par2: "\<And>\<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P. (\<lbrakk>xvec3 \<sharp>* \<Psi>; xvec3 \<sharp>* cP; xvec3 \<sharp>* c_rs; xvec3 \<sharp>* c\<pi>\<rbrakk> \<Longrightarrow> 
                                         cP = P \<parallel> Q \<and> c_rs = \<alpha> \<prec> (P \<parallel> Q') \<and> c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P \<and> xvec3 = bn \<alpha> \<and> 
                                          \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q' \<and> extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and>
                                          A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* Q \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* \<alpha> \<and> A\<^sub>P \<sharp>* Q' \<and> A\<^sub>P \<sharp>* \<pi> \<and> A\<^sub>P \<sharp>* C) \<Longrightarrow> Prop"
  and     r_comm1: "\<And>\<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec.
                   \<lbrakk>cP = P \<parallel> Q; c_rs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q'; c\<pi> = None;
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
                    distinct xvec; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> Prop"
  and     r_comm2: "\<And>\<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec.
                   \<lbrakk>cP = P \<parallel> Q; c_rs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q'; c\<pi> = None;
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
                    distinct xvec; distinct yvec; distinct zvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* xvec;
                    yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
                    zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K; zvec \<sharp>* xvec;
                    zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> Prop"
  and    r_open:  "\<And>P \<pi> M xvec y yvec N P'. 
                   (\<lbrakk>xvec4 \<sharp>* \<Psi>; xvec4 \<sharp>* cP; xvec4 \<sharp>* c\<pi>; xvec4 \<sharp>* c_rs; x1 \<sharp> \<Psi>; x1 \<sharp> cP; x1 \<sharp> c_rs; x1 \<sharp> c\<pi>; x1 \<sharp> xvec4\<rbrakk> \<Longrightarrow>
                    cP = \<lparr>\<nu>x1\<rparr>P \<and> c_rs = M\<lparr>\<nu>*(xvec@x1#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' \<and> c\<pi> = Some(\<lparr>\<nu>x1\<rparr>\<pi>) \<and> xvec4=xvec@y#yvec \<and>
                    \<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P' \<and> x1 \<in> supp N \<and> x1 \<sharp> xvec \<and> x1 \<sharp> yvec \<and>
                    distinct xvec \<and> distinct yvec \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* P \<and> xvec \<sharp>* M \<and> xvec \<sharp>* yvec \<and>
                    yvec \<sharp>* \<Psi> \<and> yvec \<sharp>* P \<and> yvec \<sharp>* M \<and> yvec \<sharp>* \<pi> \<and> xvec \<sharp>* \<pi>) \<Longrightarrow> Prop"
  and     r_scope: "\<And>P \<pi> \<alpha> P'. (\<lbrakk>xvec5 \<sharp>* \<Psi>; xvec5 \<sharp>* cP; xvec5 \<sharp>* c\<pi>; xvec5 \<sharp>* c_rs; x2 \<sharp> \<Psi>; x2 \<sharp> cP; x2 \<sharp> c_rs; x2 \<sharp> c\<pi>; x2 \<sharp> xvec5\<rbrakk> \<Longrightarrow> 
                                 cP = \<lparr>\<nu>x2\<rparr>P \<and> c_rs = \<alpha> \<prec> \<lparr>\<nu>x2\<rparr>P' \<and> c\<pi> = map_option(F_res x2) \<pi> \<and> xvec5 = bn \<alpha> \<and>
                                 \<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P' \<and> x2 \<sharp> \<Psi> \<and> x2 \<sharp> \<alpha> \<and> bn \<alpha> \<sharp>* subject \<alpha> \<and> distinct(bn \<alpha>)) \<Longrightarrow> Prop"
  and    r_bang:  "\<And>P \<pi>. \<lbrakk>cP = !P; c\<pi> = map_option(F_assert o push_prov) \<pi>;
                               \<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ c_rs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  shows Prop
using `\<Psi> \<rhd> cP \<longmapsto>c\<pi> @ c_rs`
proof(cases rule: semantics_cases_aux[where C="(xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)"])
  case(c_input M K xvec N Tvec P)
  have B: "cP = M\<lparr>\<lambda>*xvec N\<rparr>.P" and C: "c_rs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (P[xvec::=Tvec])"
    and D: "c\<pi> = Some (\<langle>\<epsilon>; \<epsilon>, M\<rangle>)"
    by fact+
  from `xvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "xvec \<sharp>* xvec1" by simp
  
  from `length xvec1 = input_length cP` B have "length xvec1 = length xvec"
    by simp
  then obtain p where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinct_perm p" and "xvec1 = p \<bullet> xvec"
    using `xvec \<sharp>* xvec1` `distinct xvec` `distinct xvec1`
    by(rule_tac construct_perm[where xvec=xvec and yvec=xvec1]) auto
  show ?thesis
  proof(rule r_input[where M=M and K=K and N = "p \<bullet> N" and Tvec=Tvec and P="p \<bullet> P"])
    case goal1
    from B `xvec \<sharp>* xvec1` `xvec1 \<sharp>* cP` have "xvec1 \<sharp>* N" and "xvec1 \<sharp>* P"
      by(auto simp add: fresh_star_def input_chain_fresh name_list_supp) (auto simp add: fresh_def)

    from `cP = M\<lparr>\<lambda>*xvec N\<rparr>.P` S `xvec1 \<sharp>* N` `xvec1 \<sharp>* P` `xvec1 = p \<bullet> xvec`
    have "cP = M\<lparr>\<lambda>*xvec1 (p \<bullet> N)\<rparr>.(p \<bullet> P)"
      apply simp
      by(subst input_chain_alpha) auto
    moreover note D
    moreover from `c_rs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]` S `xvec1 \<sharp>* N` `xvec1 \<sharp>* P` `xvec1 = p \<bullet> xvec` `length xvec = length Tvec` `distinct_perm p`
    have "c_rs =  K\<lparr>((p \<bullet> N)[xvec1::=Tvec])\<rparr> \<prec> (p \<bullet> P)[xvec1::=Tvec]"
      by(simp add: renaming subst_term.renaming)
    moreover note `\<Psi> \<turnstile> K \<leftrightarrow> M`
    moreover from `distinct xvec` `xvec1 = p \<bullet> xvec` have "distinct xvec1" by simp
    moreover from `set xvec \<subseteq> supp N` have "(p \<bullet> set xvec) \<subseteq> (p \<bullet> (supp N))"
      by(simp add: eqvts)
    with `xvec1 = p \<bullet> xvec` have "set xvec1 \<subseteq> supp(p \<bullet> N)" by(simp add: eqvts)
    moreover from `length xvec = length Tvec` `xvec1 = p \<bullet> xvec` have "length xvec1 = length Tvec"
      by simp

    moreover from `xvec1 \<sharp>* c_rs` C `length xvec = length Tvec` `distinct xvec` `set xvec \<subseteq> supp N`
    have "(set xvec1) \<sharp>* Tvec"
      by(rule_tac subst_term.subst3_chain[where T=N]) auto
    hence "xvec1 \<sharp>* Tvec" by simp
    moreover from `xvec \<sharp>* Tvec` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> Tvec)" by(simp add: fresh_star_bij)
    with S `xvec \<sharp>* Tvec` `xvec1 \<sharp>* Tvec` `xvec1 = p \<bullet> xvec` have "xvec1 \<sharp>* Tvec" by simp
    moreover note `xvec1 \<sharp>* \<Psi>`
    moreover from `xvec \<sharp>* M` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" by(simp add: fresh_star_bij)
    with S `xvec \<sharp>* M` `xvec1 \<sharp>* cP` B `xvec1 = p \<bullet> xvec` have "xvec1 \<sharp>* M" by simp
    moreover from `xvec \<sharp>* K` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> K)" by(simp add: fresh_star_bij)
    with S `xvec \<sharp>* K` `xvec1 \<sharp>* c_rs` C `xvec1 = p \<bullet> xvec` have "xvec1 \<sharp>* K" by simp
    ultimately show ?case by blast 
  qed
next
  case(c_output M K N P)
  thus ?thesis by(rule r_output) 
next
  case(c_case Cs P \<phi>)
  thus ?thesis by(rule r_case) 
next
  case(c_par1 \<Psi>\<^sub>Q P \<pi> \<alpha> P' Q A\<^sub>Q)
  have B: "cP = P \<parallel> Q" and C: "c_rs = \<alpha> \<prec> P' \<parallel> Q" and D: "c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q"
    by fact+
  from `bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "bn \<alpha> \<sharp>* xvec2" by simp
  from `A\<^sub>Q \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "A\<^sub>Q \<sharp>* xvec2" and "A\<^sub>Q \<sharp>* C" by simp+
  
  from `length xvec2 = residual_length c_rs` C have "length xvec2 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "xvec2= bn(p \<bullet> \<alpha>)"
    using `bn \<alpha> \<sharp>* xvec2` `distinct(bn \<alpha>)` `distinct xvec2`
    by(rule_tac construct_perm[where xvec="bn \<alpha>" and yvec=xvec2]) (auto simp add: eqvts)
  show ?thesis
  proof(rule r_par1[where P=P and Q=Q and \<alpha>="p \<bullet> \<alpha>" and P'="p \<bullet> P'" and A\<^sub>Q=A\<^sub>Q and \<Psi>\<^sub>Q=\<Psi>\<^sub>Q and \<pi>=\<pi>])
    case goal1
    note `cP = P \<parallel> Q`
    moreover note `c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q`
    moreover from B C S `bn \<alpha> \<sharp>* xvec2` `xvec2 \<sharp>* c_rs` `xvec2 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec2 \<sharp>* cP` `bn \<alpha> \<sharp>* Q`
    have "c_rs = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P') \<parallel> Q"
      apply auto
      by(subst residual_alpha[where p=p]) auto
    moreover note `xvec2 = bn(p \<bullet> \<alpha>)`
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` S B C S `bn \<alpha> \<sharp>* xvec2` `xvec2 \<sharp>* c_rs` `xvec2 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec2 \<sharp>* cP`
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
      by(subst residual_alpha[symmetric]) auto
    moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>`
    moreover from `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* xvec2` S `xvec2 = bn(p \<bullet> \<alpha>)` `distinct_perm p` have "A\<^sub>Q \<sharp>* (p \<bullet> \<alpha>)"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover from `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* xvec2` S `xvec2 = bn(p \<bullet> \<alpha>)` `distinct_perm p` have "A\<^sub>Q \<sharp>* (p \<bullet> P')"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover note `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* \<pi>`
    ultimately show ?case by blast
  qed
next
  case(c_par2 \<Psi>\<^sub>P Q \<pi> \<alpha> Q' P A\<^sub>P)
  have B: "cP = P \<parallel> Q" and C: "c_rs = \<alpha> \<prec> P \<parallel> Q'" and D: "c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P"
    by fact+
  from `bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "bn \<alpha> \<sharp>* xvec3" by simp
  from `A\<^sub>P \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "A\<^sub>P \<sharp>* xvec3" and "A\<^sub>P \<sharp>* C" by simp+
  from `length xvec3 = residual_length c_rs` C have "length xvec3 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "xvec3 = bn(p \<bullet> \<alpha>)"
    using `bn \<alpha> \<sharp>* xvec3` `distinct(bn \<alpha>)` `distinct xvec3`
    by(rule_tac construct_perm[where xvec="bn \<alpha>" and yvec=xvec3]) (auto simp add: eqvts)
  show ?thesis
  proof(rule r_par2[where P=P and Q=Q and \<alpha>="p \<bullet> \<alpha>" and Q'="p \<bullet> Q'" and A\<^sub>P=A\<^sub>P and \<Psi>\<^sub>P=\<Psi>\<^sub>P and \<pi>=\<pi>])
    case goal1
    note `cP = P \<parallel> Q`
    moreover note `c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P`
    moreover from B C S `bn \<alpha> \<sharp>* xvec3` `xvec3 \<sharp>* c_rs` `xvec3 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec3 \<sharp>* cP` `bn \<alpha> \<sharp>* P`
    have "c_rs = (p \<bullet> \<alpha>) \<prec> P \<parallel> (p \<bullet> Q')"
      apply auto
      by(subst residual_alpha[where p=p]) auto
    moreover note `xvec3 = bn(p \<bullet> \<alpha>)`
    moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` S B C S `bn \<alpha> \<sharp>* xvec3` `xvec3 \<sharp>* c_rs` `xvec3 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec3 \<sharp>* cP`
    have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> Q')"
      by(subst residual_alpha[symmetric]) auto
    moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>`
    moreover from `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* xvec3` S `xvec3 = bn(p \<bullet> \<alpha>)` `distinct_perm p` have "A\<^sub>P \<sharp>* (p \<bullet> \<alpha>)"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover from `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* xvec3` S `xvec3 = bn(p \<bullet> \<alpha>)` `distinct_perm p` have "A\<^sub>P \<sharp>* (p \<bullet> Q')"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover note `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<pi>`
    ultimately show ?case by blast
  qed
next
  case(c_comm1 \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec)
  thus ?thesis
    by(rule_tac r_comm1[where P=P and Q=Q]) (assumption | simp)+
next
  case(c_comm2 \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q)
  thus ?thesis by(rule_tac r_comm2[where P=P and Q=Q]) (assumption | simp)+
next
  case(c_open P \<pi> M xvec yvec N P' x)
  have B: "cP = \<lparr>\<nu>x\<rparr>P" and C: "c_rs = M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" and C': "c\<pi> = Some (\<lparr>\<nu>x\<rparr>\<pi>)"
    by fact+
  from `xvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "xvec \<sharp>* xvec4" and "xvec \<sharp>* cP" and "xvec \<sharp>* c_rs" and "x1 \<sharp> xvec" by simp+
  from `x \<sharp> (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "x \<sharp> xvec4" and "x \<sharp> cP" and "x \<sharp> c_rs" and "x \<noteq> x1" by simp+
  from `yvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "yvec \<sharp>* xvec4" and "yvec \<sharp>* cP"  and "yvec \<sharp>* c_rs" and "x1 \<sharp> yvec" by simp+

  from `xvec \<sharp>* c_rs` `x \<sharp> c_rs` `yvec \<sharp>* c_rs` C have "(xvec@x#yvec) \<sharp>* M" by simp
  from `xvec \<sharp>* \<Psi>` `x \<sharp> \<Psi>` `yvec \<sharp>* \<Psi>` have "(xvec@x#yvec) \<sharp>* \<Psi>" by simp
  from `length xvec4 = residual_length c_rs` C obtain xvec' y yvec' where D: "xvec4 = xvec'@y#yvec'" and "length xvec' = length xvec" and "length yvec' = length yvec"
    by(rule_tac length_aux2) auto
  with `distinct xvec` `distinct yvec` `x \<sharp> xvec` `x \<sharp> yvec` `xvec \<sharp>* yvec` `xvec \<sharp>* xvec4` `yvec \<sharp>* xvec4` `x \<sharp> xvec4` `distinct xvec4`
  have "distinct xvec'" and "distinct yvec'" and "xvec' \<sharp>* yvec'" and "x \<noteq> y" and "y \<sharp> xvec'" and "y \<sharp> yvec'" 
   and "x \<sharp> xvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec" and "y \<sharp> yvec" and "xvec \<sharp>* xvec'" and "yvec \<sharp>* yvec'"
    by auto
  from `length xvec' = length xvec` `xvec \<sharp>* xvec'` `distinct xvec` `distinct xvec'` 
  obtain p where Sp: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinct_perm p" and E: "xvec' = p \<bullet> xvec"
    by(metis construct_perm)
  from `length yvec' = length yvec` `yvec \<sharp>* yvec'` `distinct yvec` `distinct yvec'` 
  obtain q where Sq: "set q \<subseteq> set yvec \<times> set(q \<bullet> yvec)" and "distinct_perm q" and F: "yvec' = q \<bullet> yvec"
    by(metis construct_perm)

  show ?thesis
  proof(rule r_open[where P="([(x, x1)] \<bullet> P)" and xvec="p \<bullet> xvec" and y="y" and yvec="q \<bullet> yvec" and N="(p@(x1, x)#q) \<bullet> N" and P'="(p@(x1, x)#q) \<bullet> P'" and M=M and \<pi>="[(x, x1)]\<bullet>\<pi>"])
    case goal1
    from `xvec \<sharp>* xvec4` `x \<sharp> xvec4` `x1 \<sharp> xvec4` `yvec \<sharp>* xvec4` D E F
    have "x \<noteq> y" and "x1 \<noteq> y" and "x1 \<sharp> p \<bullet> xvec" and "x1 \<sharp> q \<bullet> yvec" by simp+
    from `xvec4 \<sharp>* c_rs` `x1 \<sharp> c_rs` C have "xvec4 \<sharp>* M" and "x1 \<sharp> M" by simp+
    moreover from `cP = \<lparr>\<nu>x\<rparr>P` `x \<sharp> cP` `x \<noteq> x1` have "([(x, x1)] \<bullet> cP) = [(x, x1)] \<bullet> \<lparr>\<nu>x\<rparr>P"
      by simp
    with `x \<sharp> cP` `x1 \<sharp> cP` have "cP = \<lparr>\<nu>x1\<rparr>([(x, x1)] \<bullet> P)" by(simp add: eqvts calc_atm)
    moreover from C' have "c\<pi> = Some (\<lparr>\<nu>x1\<rparr>([(x, x1)]\<bullet>\<pi>))"
      using `x \<noteq> x1` `x1 \<sharp> c\<pi>`
      by(simp add: eqvts pt2[OF pt_name_inst] calc_atm abs_fresh frame_fresh_chain' frame_alpha)
        (metis perm_swap)
    moreover from C have "((p@(x1, x)#q) \<bullet> c_rs) = (p@(x1, x)#q) \<bullet> (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by(simp add: fresh_star_bij)
    with Sp Sq `xvec4 \<sharp>* c_rs` D E F `xvec \<sharp>* c_rs` `x \<sharp> c_rs` `yvec \<sharp>* c_rs` `xvec4 \<sharp>* M` `(xvec@x#yvec) \<sharp>* M` `xvec \<sharp>* xvec4` `x \<sharp> xvec4` `yvec \<sharp>* xvec4` `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `y \<sharp> xvec'` `y \<sharp> yvec'` `xvec' \<sharp>* yvec'` `x1 \<sharp> xvec` `x1 \<sharp> yvec` `x1 \<noteq> y` `x1 \<sharp> xvec4` `x1 \<sharp> c_rs` `x1 \<sharp> c_rs` `x \<noteq> x1` `x1 \<sharp> M`
    have "c_rs = M\<lparr>\<nu>*((p \<bullet> xvec)@x1#(q \<bullet> yvec))\<rparr>\<langle>((p@(x1, x)#q) \<bullet> N)\<rangle> \<prec> ((p@(x1, x)#q) \<bullet> P')"
      by(simp add: eqvts pt2[OF pt_name_inst] calc_atm)
    moreover from D E F have "xvec4 = (p \<bullet> xvec)@y#(q \<bullet> yvec)" by simp
    moreover from `\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` have "((p@(x1, x)#q) \<bullet> \<Psi>) \<rhd> ((p@(x1, x)#q) \<bullet> P) \<longmapsto>Some((p@(x1, x)#q) \<bullet> \<pi>) @ ((p@(x1, x)#q) \<bullet> (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'))"
      by(drule_tac semantics.eqvt) (simp add: eqvts)
    with Sp Sq B C D E F `xvec4 \<sharp>* \<Psi>` `(xvec@x#yvec) \<sharp>* \<Psi>` `xvec4 \<sharp>* c_rs` `x \<sharp> xvec4` C D `x \<sharp> c_rs` `yvec \<sharp>* c_rs` `xvec4 \<sharp>* M` `(xvec@x#yvec) \<sharp>* M` `x \<sharp> M` `x1 \<sharp> c_rs` `x \<noteq> x1` `x1 \<sharp> xvec` `x1 \<sharp> yvec` `xvec \<sharp>* xvec4` `yvec \<sharp>* xvec4` `x1 \<sharp> xvec4` `x \<sharp> xvec` `x \<sharp> yvec` `x1 \<sharp> \<Psi>` `xvec4 \<sharp>* cP` `xvec \<sharp>* P` `yvec \<sharp>* P` `xvec' \<sharp>* yvec'` `x1 \<sharp> xvec4` `xvec4 \<sharp>* cP` `yvec \<sharp>* xvec4` `xvec \<sharp>* xvec4` `x \<noteq> x1` `xvec \<sharp>* yvec` `xvec \<sharp>* \<pi>` `yvec \<sharp>* \<pi>` C' `xvec4 \<sharp>* c\<pi>`
    have Trans: "\<Psi> \<rhd> ([(x, x1)] \<bullet> P) \<longmapsto>Some([(x, x1)] \<bullet> \<pi>)  @ M\<lparr>\<nu>*((p \<bullet> xvec)@(q \<bullet> yvec))\<rparr>\<langle>((p@(x1, x)#q) \<bullet> N)\<rangle> \<prec> ((p@(x1, x)#q) \<bullet> P')" 
      by(simp add: eqvts  pt_fresh_bij[OF pt_name_inst, OF at_name_inst] pt2[OF pt_name_inst] name_swap abs_fresh frame_fresh_chain')
    moreover from `x \<in> supp N` have "((p@(x1, x)#q) \<bullet> x) \<in> ((p@(x1, x)#q) \<bullet> supp N)"
      by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
    hence "x1 \<in> supp((p@(x1, x)#q) \<bullet> N)"
      using `x \<sharp> xvec` `x \<sharp> yvec` `x1 \<sharp> xvec` `x1 \<sharp> yvec` `x \<sharp> xvec4` `x1 \<sharp> xvec4` `xvec \<sharp>* xvec4` `yvec \<sharp>* xvec4` `xvec' \<sharp>* yvec'` D E F Sp Sq `x \<noteq> x1`
      by(simp add: eqvts pt2[OF pt_name_inst] calc_atm)
    moreover from `x1 \<sharp> xvec4` D E F have "x1 \<sharp> (p \<bullet> xvec)" and "x1 \<sharp> (q \<bullet> yvec)" by simp+
    moreover from `distinct xvec'` `distinct yvec'` E F have "distinct(p \<bullet> xvec)" and "distinct(q \<bullet> yvec)" by simp+
    moreover from `xvec' \<sharp>* yvec'` E F have "(p \<bullet> xvec) \<sharp>* (q \<bullet> yvec)" by auto
    moreover from `xvec \<sharp>* \<Psi>` have "(p \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with Sp D E `xvec4 \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>` have "(p \<bullet> xvec) \<sharp>* \<Psi>" by(simp add: eqvts)
    moreover from `yvec \<sharp>* \<Psi>` have "(p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with Sq D F `xvec4 \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` have "(q \<bullet> yvec) \<sharp>* \<Psi>" by(simp add: eqvts)
    moreover from `xvec4 \<sharp>* cP` `x \<sharp> xvec4` `x1 \<sharp> xvec4` B D E F have "(p \<bullet> xvec) \<sharp>* ([(x, x1)] \<bullet> P)" and "(q \<bullet> yvec) \<sharp>* ([(x, x1)] \<bullet> P)"
      by simp+
    moreover hence "(q \<bullet> yvec) \<sharp>* Some([(x, x1)] \<bullet> \<pi>)" and  "(p \<bullet> xvec) \<sharp>* Some([(x, x1)] \<bullet> \<pi>)"
      using Trans
      by(blast intro: trans_fresh_provenance)+
    hence "(q \<bullet> yvec) \<sharp>* ([(x, x1)] \<bullet> \<pi>)" and  "(p \<bullet> xvec) \<sharp>* ([(x, x1)] \<bullet> \<pi>)"
      by simp_all
    moreover from `xvec4 \<sharp>* M` C D E F have "(p \<bullet> xvec) \<sharp>* M" and "(q \<bullet> yvec) \<sharp>* M" by simp+
    ultimately show ?case
      by blast
  qed
next
  case(c_scope P \<pi> \<alpha> P' x)
  have B: "cP = \<lparr>\<nu>x\<rparr>P" and C: "c_rs = \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" and C': "c\<pi> = map_option (F_res x) \<pi>"
    by fact+
  from `bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "bn \<alpha> \<sharp>* xvec5" and "x2 \<sharp> bn \<alpha>" by simp+
  from `x \<sharp> (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, c_rs, c\<pi>, C)` have "x \<sharp> xvec5" and "x \<noteq> x2" and "x \<sharp> c_rs" by simp+
  
  from `length xvec5 = residual_length c_rs` C have "length xvec5 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "xvec5= bn(p \<bullet> \<alpha>)"
    using `bn \<alpha> \<sharp>* xvec5` `distinct(bn \<alpha>)` `distinct xvec5`
    by(rule_tac construct_perm[where xvec="bn \<alpha>" and yvec=xvec5]) (auto simp add: eqvts)
  show ?thesis
  proof(rule r_scope[where P="[(x, x2)] \<bullet> P" and \<alpha>="[(x, x2)] \<bullet> p \<bullet> \<alpha>" and P'="[(x, x2)] \<bullet> p \<bullet> P'" and \<pi>="[(x, x2)] \<bullet> \<pi>"])
    case goal1
    from `x2 \<sharp> c_rs` C `x2 \<sharp> bn \<alpha>` `x \<noteq> x2` have "x2 \<sharp> \<alpha>" and "x2 \<sharp> P'" by(auto simp add: abs_fresh)
    moreover from `cP = \<lparr>\<nu>x\<rparr>P` `x2 \<sharp> cP` `x \<noteq> x2` have "cP = \<lparr>\<nu>x2\<rparr>([(x, x2)] \<bullet> P)"
      by(simp add: alpha_res abs_fresh)
    moreover from B C S `bn \<alpha> \<sharp>* xvec5` `xvec5 \<sharp>* c_rs` `xvec5 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec5 \<sharp>* cP` `x \<sharp> \<alpha>` `x \<sharp> xvec5` 
    have "c_rs = (p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P')"
      apply auto
      by(subst residual_alpha[where p=p] alpha_res) (auto simp del: action_fresh)
    hence "([(x, x2)] \<bullet> c_rs) = [(x, x2)] \<bullet> ((p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P'))"
      by simp
    with `x2 \<sharp> c_rs` `x \<sharp> c_rs` have "c_rs = ([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x2\<rparr>([(x, x2)] \<bullet> p \<bullet> P')"
      by(simp add: eqvts calc_atm)
    moreover from `xvec5= bn(p \<bullet> \<alpha>)` have "([(x, x2)] \<bullet> xvec5) = ([(x, x2)] \<bullet> bn(p \<bullet> \<alpha>))"
      by simp
    with `x \<sharp> xvec5` `x2 \<sharp> xvec5` have "xvec5 = bn([(x, x2)] \<bullet> p \<bullet> \<alpha>)"
      by(simp add: eqvts)
    moreover from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` S B C S `bn \<alpha> \<sharp>* xvec5` `xvec5 \<sharp>* c_rs` `xvec5 = bn(p \<bullet> \<alpha>)` `bn \<alpha> \<sharp>* subject \<alpha>` `xvec5 \<sharp>* cP` `x \<sharp> xvec5`
    have "\<Psi> \<rhd> P \<longmapsto>\<pi> @ (p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
      by(subst residual_alpha[symmetric]) auto
    hence "([(x, x2)] \<bullet> \<Psi>) \<rhd> ([(x, x2)] \<bullet> P) \<longmapsto>([(x, x2)] \<bullet> \<pi>) @ ([(x, x2)] \<bullet> ((p \<bullet> \<alpha>) \<prec> (p \<bullet> P')))"
      by(rule eqvt)
    with `x \<sharp> \<Psi>` `x2 \<sharp> \<Psi>` have "\<Psi> \<rhd> ([(x, x2)] \<bullet> P) \<longmapsto>([(x, x2)] \<bullet> \<pi>) @ ([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<prec> ([(x, x2)] \<bullet> p \<bullet> P')"
      by(simp add: eqvts)
    moreover note `x2 \<sharp> \<Psi>`
    moreover from `x \<sharp> \<alpha>` `x2 \<sharp> \<alpha>` `x \<sharp> xvec5` `x2 \<sharp> xvec5` S `x \<noteq> x2` `xvec5 = bn(p \<bullet> \<alpha>)` have "x2 \<sharp> [(x, x2)] \<bullet> p \<bullet> \<alpha>"
      apply(subgoal_tac "x \<sharp> p \<and> x2 \<sharp> p")
      apply(simp add: perm_compose fresh_chain_simps del: action_fresh)
      by(auto dest: fresh_alpha_swap)
    moreover from `bn \<alpha> \<sharp>* subject \<alpha>` have "([(x, x2)] \<bullet> p \<bullet> (bn \<alpha>)) \<sharp>* ([(x, x2)] \<bullet> p \<bullet> (subject \<alpha>))"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    hence "bn([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<sharp>* subject([(x, x2)] \<bullet> p \<bullet> \<alpha>)"
      by(simp add: eqvts)
    moreover from `distinct(bn \<alpha>)` have "distinct([(x, x2)] \<bullet> p \<bullet> (bn \<alpha>))" by simp
    hence "distinct(bn([(x, x2)] \<bullet> p \<bullet> \<alpha>))" by(simp add: eqvts)
    moreover have "c\<pi> = map_option (F_res x2) ([(x, x2)] \<bullet> \<pi>)" using C'
      `x \<noteq> x2` `x2 \<sharp> c\<pi>`
      apply(cases \<pi>)
      by(simp_all add: frame_alpha abs_fresh) (metis perm_swap)
    ultimately show ?case  by blast
  qed
next
  case(c_bang P)
  thus ?thesis by(rule_tac r_bang) auto
qed

lemma par_cases[consumes 5, case_names c_par1 c_par2 c_comm1 c_comm2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ \<alpha> \<prec> T"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     r_par1: "\<And>P' \<pi> A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                                  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P' \<parallel> Q)"
  and     r_par2: "\<And>Q' \<pi> A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                 A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec.
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
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q yvec zvec.
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
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"

  shows "Prop \<alpha> T"
proof -
  from Trans `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q`
  have "bn \<alpha> \<sharp>* c\<pi>"
    by(auto intro: trans_fresh_provenance)
  from Trans have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)
  have "length(bn \<alpha>) = residual_length(\<alpha> \<prec> T)" by simp
  note Trans
  moreover have "length [] = input_length(P \<parallel> Q)" and "distinct []"
    by(auto simp add: input_length_input_length'_input_length''.simps)
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> T)` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> T)` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> T)` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> T)` `distinct(bn \<alpha>)`
  moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> \<alpha>" and "x \<sharp> c\<pi>" and "x \<sharp> T"
    by(generate_fresh "name") auto
  ultimately show ?thesis using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* c\<pi>`
    apply(cases rule: semantics_cases[of _ _ _ _ _ _ _ _ _ _ C x x])
    apply(auto simp add: psi.inject)
    apply(force simp add: residual_inject residual_inject' intro: r_par1)
    apply(force simp add: residual_inject residual_inject' intro: r_par2)
    apply(force simp add: residual_inject residual_inject' intro: r_comm1)
    by(force simp add: residual_inject residual_inject' intro: r_comm2)
qed

lemma par_input_cases[consumes 1, case_names c_par1 c_par2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a
  and   R :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto> c\<pi> @ M\<lparr>N\<rparr> \<prec> R"
  and     r_par1: "\<And>\<pi> P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     r_par2: "\<And>\<pi> Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop R"
proof -
  from Trans obtain \<alpha> where "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ \<alpha> \<prec> R" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* subject \<alpha>" and "\<alpha> = M\<lparr>N\<rparr>" by auto
  thus ?thesis using r_par1 r_par2
    by(induct rule: par_cases) (auto simp add: residual_inject)
qed

lemma par_output_cases[consumes 5, case_names c_par1 c_par2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   xvec :: "name list"
  and   N :: 'a
  and   R :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R"
  and            "xvec \<sharp>* \<Psi>"
  and            "xvec \<sharp>* P"
  and            "xvec \<sharp>* Q"
  and            "xvec \<sharp>* M"
  and     r_par1: "\<And>\<pi> P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* C; A\<^sub>Q \<sharp>* xvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     r_par2: "\<And>\<pi> Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* C; A\<^sub>P \<sharp>* xvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop R"
proof -
  from Trans have "distinct xvec" by(auto dest: bound_output_distinct)
  obtain \<alpha> where "\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
  with Trans `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* Q` `xvec \<sharp>* M`
  have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ \<alpha> \<prec> R" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" "bn \<alpha> \<sharp>* subject \<alpha>"
    by simp+
  thus ?thesis using `\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` r_par1 r_par2 `distinct xvec`
    by(induct rule: par_cases[where C="(xvec, C)"]) (auto simp add: residual_inject)
qed

lemma the_eqvt[eqvt_force]:
  fixes p :: "name prm"
  and   \<alpha> :: "'a action"

  assumes "\<alpha> \<noteq> \<tau>"

  shows "(p \<bullet> the(subject \<alpha>)) = the(p \<bullet> (subject \<alpha>))"
using assms
by(induct rule: action_cases[where \<alpha>=\<alpha>]) auto

lemma the_subject_fresh[simp]:
  fixes \<alpha> :: "'a action"
  and   x :: name

  assumes "\<alpha> \<noteq> \<tau>"

  shows "x \<sharp> the(subject \<alpha>) = x \<sharp> subject \<alpha>"
using assms
by(cases rule: action_cases) auto

lemma the_subject_fresh_chain[simp]:
  fixes \<alpha>    :: "'a action"
  and   xvec :: "name list"

  assumes "\<alpha> \<noteq> \<tau>"

  shows "xvec \<sharp>* the(subject \<alpha>) = xvec \<sharp>* subject \<alpha>"
using assms
by(cases rule: action_cases) auto

abbreviation
  stat_imp_judge ("_ \<hookrightarrow> _" [80, 80] 80)
  where "\<Psi> \<hookrightarrow> \<Psi>' \<equiv> Assertion_stat_imp \<Psi> \<Psi>'"

lemma stat_eq_transition:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<longmapsto> \<pi> @ Rs"
using assms
proof(nominal_induct avoiding: \<Psi>' rule: semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P \<Psi>')
  from `\<Psi> \<simeq> \<Psi>'` `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi>' \<turnstile> M \<leftrightarrow> K"
    by(simp add: Assertion_stat_imp_def Assertion_stat_eq_def)
  thus ?case using `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
    by(rule Input)
next
  case(Output \<Psi> M K N P \<Psi>')
  from `\<Psi> \<simeq> \<Psi>'` `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi>' \<turnstile> M \<leftrightarrow> K"
    by(simp add: Assertion_stat_imp_def Assertion_stat_eq_def) 
  thus ?case by(rule semantics.Output)
next
  case(Case \<Psi> P \<pi> Rs \<phi> Cs \<Psi>')
  then have "\<Psi>' \<rhd> P \<longmapsto> \<pi> @ Rs" by(rule_tac Case)
  moreover note `(\<phi>, P) mem Cs`
  moreover from `\<Psi> \<simeq> \<Psi>'` `\<Psi> \<turnstile> \<phi>` have "\<Psi>' \<turnstile> \<phi>"
    by(simp add: Assertion_stat_imp_def Assertion_stat_eq_def)
  ultimately show ?case using `guarded P` by(rule semantics.Case)
next
  case(c_par1 \<Psi> \<Psi>Q P \<alpha> P' xvec Q \<Psi>')
  thus ?case
    by(rule_tac Par1) (auto intro: Composition)
next
  case(c_par2 \<Psi> \<Psi>P Q \<alpha> Q' xvec P \<Psi>')
  thus ?case
    by(rule_tac Par2) (auto intro: Composition)
next
  case(c_comm1 \<Psi> \<Psi>Q P M N P' xvec \<Psi>P Q K zvec Q' yvec \<Psi>')
  thus ?case
    by(clarsimp, rule_tac Comm1) (blast intro: Composition)+
next
  case(c_comm2 \<Psi> \<Psi>Q P M zvec N P' xvec \<Psi>P Q K Q' yvec \<Psi>')
  thus ?case
    by(clarsimp, rule_tac Comm2) (blast intro: Composition)+
next
  case(c_open \<Psi> P M xvec N P' x yvec \<Psi>')
  thus ?case by(force intro: Open)
next
  case(c_scope \<Psi> P \<alpha> P' x \<Psi>')
  thus ?case by(force intro: Scope)
next
  case(Bang \<Psi> P Rs \<Psi>')
  thus ?case by(force intro: semantics.Bang)
qed

(*lemma input_rename_subject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> L"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> L"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* K"
    
  shows "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'"
using assms
proof(nominal_induct avoiding: K arbitrary: L rule: input_frame_induct)
  case(c_alpha \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P  p K L)
  have S: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)" by fact
  from `\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> K \<leftrightarrow> L` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> K) \<leftrightarrow> (p \<bullet> L)" 
    by(rule chan_eq_closed)
  with S `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* M` `(p \<bullet> A\<^sub>P) \<sharp>* K`
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> (p\<bullet>L)" by(simp add: eqvts)
  moreover from `\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> M \<leftrightarrow> L` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> L)" 
    by(rule chan_eq_closed)
  with S `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* M` `(p \<bullet> A\<^sub>P) \<sharp>* K`
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> (p\<bullet>L)" by(simp add: eqvts)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` 
  moreover have "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> (p\<bullet>L); \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> (p\<bullet>L); A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'"
    by(rule c_alpha)
  ultimately show ?case by blast
next
  case(c_input \<Psi> M K xvec N Tvec P K')
  from `\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> L` have "\<Psi> \<turnstile> K \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> K' \<leftrightarrow> L` have "\<Psi> \<turnstile> K' \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity)
  moreover note `\<Psi> \<turnstile> K \<leftrightarrow> M`
  ultimately have "\<Psi> \<turnstile> K' \<leftrightarrow> M"
    by(rule_tac chan_eq_trans)
  thus ?case using `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
    by(rule Input)
next
  case(c_case \<Psi> P M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P K L)
  from `\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> L` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> L` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K`
  ultimately have "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'"
    by(force intro: c_case)
  thus ?case using `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P` by(rule Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P K)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> L` have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> L"
    by(metis stat_eq_ent Associativity Composition Assertion_stat_eq_trans Commutativity)
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> L` have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> L"
    by(metis stat_eq_ent Associativity Composition Assertion_stat_eq_trans Commutativity)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` 
  ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'"
    by(force intro: c_par1)
  thus ?case using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* N`
    by(rule_tac Par1) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q K)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> L` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> L"
    by(rule stat_eq_ent[OF Assertion_stat_eq_sym[OF Associativity]])
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> L` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> L"
    by(rule stat_eq_ent[OF Assertion_stat_eq_sym[OF Associativity]])
  moreover note `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* K` 
  ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by(force intro: c_par2)
  thus ?case using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* K` `A\<^sub>P \<sharp>* N`
    by(rule_tac Par2) auto
next
  case(c_scope \<Psi> P M N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by force
  with `x \<sharp> \<Psi>` `x \<sharp> K` `x \<sharp> N` show ?case
    by(rule_tac Scope) auto
next
  case(c_bang \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P K)
  from `\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> L` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> K \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> L` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> L"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K`
  ultimately have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by(force intro: c_bang)
  thus ?case using `guarded P` by(rule Bang)
qed
*)
(*
lemma output_rename_subject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> M"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* K"
    
  shows "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
apply(simp add: residual_inject)
proof(nominal_induct avoiding: K arbitrary: L rule: output_frame_induct)
  case(c_alpha \<Psi> P M A\<^sub>P \<Psi>\<^sub>P p B K L)
  have S: "set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P)" by fact
  from `\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> L \<leftrightarrow> M` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> L) \<leftrightarrow> (p \<bullet> M)" 
    by(rule chan_eq_closed)
  with S `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* M` `(p \<bullet> A\<^sub>P) \<sharp>* K`
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> (p\<bullet>L) \<leftrightarrow> M" by(simp add: eqvts)
  moreover from `\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> L \<leftrightarrow> K` have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> L) \<leftrightarrow> (p \<bullet> K)" 
    by(rule chan_eq_closed)
  with S `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>P) \<sharp>* M` `(p \<bullet> A\<^sub>P) \<sharp>* K`
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> (p\<bullet>L) \<leftrightarrow> K" by(simp add: eqvts)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` 
  ultimately show ?case by(blast intro: c_alpha)
next
  case(c_output \<Psi> M K N P K')
  from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> K'` have "\<Psi> \<turnstile> L \<leftrightarrow> K'"
    by(blast intro: stat_eq_ent Identity)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> K` have "\<Psi> \<turnstile> L \<leftrightarrow> K"
    by(blast intro: stat_eq_ent Identity)
  moreover note `\<Psi> \<turnstile> M \<leftrightarrow> K`
  ultimately have "\<Psi> \<turnstile> M \<leftrightarrow> K'"
    by(rule_tac chan_eq_trans)
  thus ?case using Output by(force simp add: residual_inject)
next
  case(c_case \<Psi> P M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P K)
  from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> K` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> K"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> M` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> M"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K`
  ultimately have "\<Psi> \<rhd> P \<longmapsto>R_out K B" by(force intro: c_case)
  thus ?case using `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P` by(rule Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P K)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> K` have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> K"
    by(metis stat_eq_ent Associativity Composition Assertion_stat_eq_trans Commutativity)
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> M` have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> L \<leftrightarrow> M"
    by(metis stat_eq_ent Associativity Composition Assertion_stat_eq_trans Commutativity)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K` 
  ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(force intro: c_par1 simp add: residual_inject)
  thus ?case using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* K`  `A\<^sub>Q \<sharp>* xvec`  `A\<^sub>Q \<sharp>* N` Par1[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(auto simp add: residual_inject)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q K)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> K` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> K"
    by(rule stat_eq_ent[OF Assertion_stat_eq_sym[OF Associativity]])
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> M` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> L \<leftrightarrow> M"
    by(rule stat_eq_ent[OF Assertion_stat_eq_sym[OF Associativity]])
  moreover note `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* K` 
  ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>R_out K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q')" by(force intro: c_par2)
  thus ?case using `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* K` `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* N` Par2[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(auto simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(force simp add: residual_inject)
  with `x \<in> supp N` `x \<sharp> \<Psi>` `x \<sharp> K` `x \<sharp> xvec` `x \<sharp> yvec` Open show ?case
    by(auto simp add: residual_inject)
next
  case(c_scope \<Psi> P M xvec N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(force simp add: residual_inject)
  with `x \<sharp> \<Psi>` `x \<sharp> K` `x \<sharp> xvec` `x \<sharp> N` Scope[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"] show ?case
    by(auto simp add: residual_inject)
next
  case(c_bang \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P K)
  from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> K` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> L \<leftrightarrow> K"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover from `\<Psi> \<otimes> \<one> \<turnstile> L \<leftrightarrow> M` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> L \<leftrightarrow> M"
    by(blast intro: stat_eq_ent Identity composition_sym Assertion_stat_eq_sym)
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* K`
  ultimately have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>R_out K B" by(force intro: c_bang)
  thus ?case using `guarded P` by(rule Bang)
qed
*)
(*
lemma obtain_input_prefix_ultra:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'  :: "('a, 'b, 'c) psi"
  and   A\<^sub>P  :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   B   :: "name list"
  and   C   :: "name list"

  assumes "\<Psi>\<^sub>Q \<otimes> \<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "B \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* B"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* xvec"
  and     "\<Psi>\<^sub>P \<otimes> \<Psi> \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>Q"
  and     "A\<^sub>P \<sharp>* A\<^sub>Q"
  and     "xvec \<sharp>* K"
  and     "distinct xvec"
  and     "C \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* B"
  and     "A\<^sub>Q \<sharp>* C"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* K"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"

  obtains M' K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'" and "B \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'" "C \<sharp>* M'" and "A\<^sub>P \<sharp>* M'"
  and  "\<Psi>\<^sub>Q \<otimes> \<Psi>  \<rhd> P \<longmapsto>M'\<lparr>N\<rparr> \<prec> P'"  and  "\<Psi>\<^sub>P \<otimes> \<Psi> \<rhd> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
using assms
proof(nominal_induct avoiding: B C xvec A\<^sub>Q Q arbitrary: thesis K rule: input_frame_psi_induct)
  case(c_alpha \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P p B C xvec A\<^sub>Q Q)
  from `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
  `distinct_perm p` `(p\<bullet>\<Psi>\<^sub>P) \<otimes> \<Psi> \<rhd> Q \<longmapsto> \<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^sub>P \<sharp>* Q`  `(p\<bullet>A\<^sub>P) \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>`  `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>`
  have "\<Psi>\<^sub>P \<otimes> \<Psi> \<rhd> Q \<longmapsto> \<pi> @ (p\<bullet>K)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(auto simp add: eqvts dest: output_perm_frame_subject)
  moreover from `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
  `distinct_perm p` `xvec \<sharp>* K` `A\<^sub>P \<sharp>* xvec` `(p\<bullet>A\<^sub>P) \<sharp>* xvec`
  have "xvec \<sharp>* (p\<bullet>K)"
      by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover from `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
  `distinct_perm p` `A\<^sub>Q \<sharp>* K` `A\<^sub>P \<sharp>* A\<^sub>Q` `(p\<bullet>A\<^sub>P) \<sharp>* A\<^sub>Q`
  have "A\<^sub>Q \<sharp>* (p\<bullet>K)"
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover have "(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" using `(p \<bullet> A\<^sub>P) \<sharp>* Q` `(p\<bullet>A\<^sub>P) \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>`
    by(auto dest: extract_frame_fresh_chain)
  with `\<Psi> \<otimes> (p\<bullet>\<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K`
    `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
    `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>`  `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M`  `(p\<bullet>A\<^sub>P) \<sharp>* M`
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> (p \<bullet> K)"
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover note `B \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* B` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* xvec` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` `distinct xvec` `C \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q`
  `A\<^sub>P \<sharp>* C` `A\<^sub>Q \<sharp>* B`
  ultimately obtain M' K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'" "B \<sharp>* K'" "A\<^sub>Q \<sharp>* K'" "C \<sharp>* M'"  "A\<^sub>P \<sharp>* M'" "\<Psi>\<^sub>Q \<otimes> \<Psi> \<rhd> P \<longmapsto> \<pi> @ M'\<lparr>N\<rparr> \<prec> P'"
       "\<Psi>\<^sub>P \<otimes> \<Psi> \<rhd> Q \<longmapsto> \<pi> @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(rule_tac c_alpha(15)) auto
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'` have "\<Psi> \<otimes> (p\<bullet>\<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> (p\<bullet>M') \<leftrightarrow> (p\<bullet>K')"
    using `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
      `distinct_perm p` `A\<^sub>P \<sharp>* \<Psi>` `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q`(* `A\<^sub>P \<sharp>* M'` `(p\<bullet>A\<^sub>P) \<sharp>* M'`*)
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover from `B \<sharp>* K'`
    `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
    `distinct_perm p` `A\<^sub>P \<sharp>* B` `(p\<bullet>A\<^sub>P) \<sharp>* B`
  have "B \<sharp>* (p \<bullet> K')"
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover from `A\<^sub>Q \<sharp>* K'`
    `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
    `distinct_perm p` `A\<^sub>P \<sharp>* A\<^sub>Q` `(p\<bullet>A\<^sub>P) \<sharp>* A\<^sub>Q`
  have "A\<^sub>Q \<sharp>* (p \<bullet> K')"
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover from `C \<sharp>* M'`
    `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)`
    `distinct_perm p` `A\<^sub>P \<sharp>* C` `(p\<bullet>A\<^sub>P) \<sharp>* C`
  have "C \<sharp>* (p \<bullet> M')"
    by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
  moreover from `A\<^sub>P \<sharp>* M'`
  have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> M')"
    by(subst perm_bool[where pi="rev p",symmetric]) (simp add: eqvts)
  moreover from `\<Psi>\<^sub>Q \<otimes> \<Psi> \<rhd> P \<longmapsto> \<pi> @ M'\<lparr>N\<rparr> \<prec> P'`
  have "\<Psi>\<^sub>Q \<otimes> \<Psi> \<rhd> P \<longmapsto> \<pi> @ (p \<bullet> M')\<lparr>N\<rparr> \<prec> P'"
    using `set p \<subseteq> set A\<^sub>P \<times> set(p\<bullet>A\<^sub>P)` `A\<^sub>P \<sharp>* P` `(p\<bullet>A\<^sub>P) \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>` `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>`
    by(rule_tac input_perm_subject) auto
  moreover from `\<Psi>\<^sub>P \<otimes> \<Psi> \<rhd> Q \<longmapsto> \<pi> @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
  have "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi> \<rhd> Q \<longmapsto> \<pi> @ (p \<bullet> K')\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    using `set p \<subseteq> set A\<^sub>P \<times> set(p\<bullet>A\<^sub>P)` `A\<^sub>P \<sharp>* Q` `(p\<bullet>A\<^sub>P) \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `(p\<bullet>A\<^sub>P) \<sharp>* \<Psi>`
    by(drule_tac output_perm_frame_subject[where p=p]) (simp add: eqvts)+
  ultimately show ?case
    by(rule_tac c_alpha(16)) auto
next
  case(c_input \<Psi> M L xvec N Tvec P B C yvec A\<^sub>Q Q)
  from `\<Psi> \<turnstile> K \<leftrightarrow> M` have "\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> M"
    by(blast intro: stat_eq_ent Assertion_stat_eq_sym[OF Identity])
  moreover from `B \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)` have "B \<sharp>* M" by simp
  ultimately show ?case by(rule_tac c_input) auto
next
  case(c_case \<Psi> P M K P' \<phi> Cs  A\<^sub>P \<Psi>\<^sub>P B)
  from `(\<phi>, P) mem Cs` `B \<sharp>* (Cases Cs)`
  have "B \<sharp>* (\<phi>, P)"
    by(rule_tac mem_fresh_chain) (assumption|simp)+
  hence "B \<sharp>* P" by simp
  with c_case obtain K where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac c_case) (auto)
  with `\<Psi>\<^sub>P \<simeq> \<one>` show ?case by(blast intro: c_case stat_eq_ent composition_sym Identity)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P B)
  then obtain K where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac c_par1) force+
  thus ?case
    by(metis c_par1 stat_eq_ent Associativity Commutativity Assertion_stat_eq_trans Composition)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q B)
  then obtain K where "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac c_par2) auto
  thus ?case by(metis c_par2 stat_eq_ent Associativity)
next
  case(c_scope \<Psi> P M N P' x A\<^sub>P \<Psi>\<^sub>P B)  
  then obtain K where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac c_scope) auto
  thus ?case by(force intro: c_scope)
next
  case(c_bang \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P B)
  then obtain K where "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac c_bang) auto
  with `\<Psi>\<^sub>P \<simeq> \<one>` show ?case by(metis c_bang stat_eq_ent composition_sym Identity)
qed
*)

lemma par_cases_subject[consumes 7, case_names c_par1 c_par2 c_comm1 c_comm2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   R    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"
  and   avec :: "name list"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ \<alpha> \<prec> R"
  and            "bn \<alpha> \<sharp>* \<Psi>"
  and            "bn \<alpha> \<sharp>* P"
  and            "bn \<alpha> \<sharp>* Q"
  and            "bn \<alpha> \<sharp>* subject \<alpha>"
  and            "avec \<sharp>* P"
  and            "avec \<sharp>* Q"
  and     r_par1: "\<And>\<pi> P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* \<pi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P' \<parallel> Q)"
  and     r_par2: "\<And>\<pi> Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            avec \<sharp>* M; avec \<sharp>* K; distinct xvec; distinct yvec; distinct zvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K; xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
            yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
            yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
            zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
            zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q yvec zvec.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            avec \<sharp>* M; avec \<sharp>* K; distinct xvec; distinct yvec; distinct zvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C;
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K;  xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; yvec \<sharp>* C; zvec \<sharp>* C;
            yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>Q; yvec \<sharp>* P; yvec \<sharp>* M;
            yvec \<sharp>* Q; yvec \<sharp>* A\<^sub>P; yvec \<sharp>* A\<^sub>Q; yvec \<sharp>* P'; yvec \<sharp>* Q'; yvec \<sharp>* zvec;
            zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* K;
            zvec \<sharp>* Q; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* A\<^sub>Q; zvec \<sharp>* P'; zvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"

  shows "Prop \<alpha> R"
using Trans `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>`
proof(induct rule: par_cases[where C="(C, avec)"])
  case(c_par1 P' A\<^sub>Q \<Psi>\<^sub>Q)
  thus ?case by(rule_tac r_par1) auto 
next
  case(c_par2 Q' A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by(rule_tac r_par2) auto
next
  case(c_comm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec)
  thus ?case using `avec \<sharp>* P` `avec \<sharp>* Q`
    apply(rule_tac r_comm1)
    apply assumption+
    by(auto dest!: trans_fresh_provenance[where xvec=avec] simp add: frame_chain_fresh_chain'')
next
  case(c_comm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q yvec zvec)
  thus ?case using `avec \<sharp>* P` `avec \<sharp>* Q`
    apply(rule_tac r_comm2)
    apply assumption+
    by(auto dest!: trans_fresh_provenance[where xvec=avec] simp add: frame_chain_fresh_chain'')  
qed

lemma input_cases[consumes 1, case_names c_input]:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"  
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"  
  and     r_input: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; \<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

  shows "Prop \<alpha> P'"
proof -
  {
    fix xvec N P
    assume Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
       and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* \<alpha>" and "xvec \<sharp>* P'" and "distinct xvec"
       and r_input: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; \<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

    from Trans have "bn \<alpha> = []"
      apply -
      by(ind_cases "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'") (auto simp add: residual_inject)
    from Trans have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)
    have "length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')" by simp
    from Trans have "\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)"
      apply -
      by(ind_cases "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'")(auto simp add: frame.inject psi.inject)    
    note Trans
    moreover have "length xvec = input_length(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by auto
    moreover note `distinct xvec`
    moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
    moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
    moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
    moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
    moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
    moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> \<alpha>" and "x \<sharp> P'" and "x \<sharp> N"
      by(generate_fresh "name") auto
    ultimately have "Prop \<alpha> P'" using `bn \<alpha> = []` `xvec \<sharp>* \<Psi>``xvec \<sharp>* M` `xvec \<sharp>* \<alpha>` `xvec \<sharp>* P'` `\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)`
      apply(cases rule: semantics_cases[of _ _ _ _ _ _ _ _ _ _ C x])  
      apply(force simp add: residual_inject psi.inject frame.inject r_input frame_chain_fresh_chain)
      by(force simp add: residual_inject psi.inject input_chain_fresh frame_chain_fresh_chain)+
  }
  note Goal = this
  moreover obtain p :: "name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* \<pi>"
                                    and "(p \<bullet> xvec) \<sharp>* \<alpha>" and "(p \<bullet> xvec) \<sharp>* P'" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                    and "distinct_perm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, N, P, \<pi>, \<alpha>, P')" in name_list_avoiding) auto
  from Trans `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P` S have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(simp add: input_chain_alpha')
  moreover {
    fix K Tvec
    assume "\<Psi> \<turnstile> K \<leftrightarrow> M"
    moreover assume "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
    hence "(p \<bullet> set(p \<bullet> xvec)) \<subseteq> (p \<bullet> supp(p \<bullet> N))" by simp
    with `distinct_perm p` have "set xvec \<subseteq> supp N" by(simp add: eqvts)
    moreover from Trans have "\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>)"
      apply -
      by(ind_cases "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'")(auto simp add: frame.inject psi.inject)
    moreover assume "length(p \<bullet> xvec) = length(Tvec::'a list)"
    hence "length xvec = length Tvec" by simp
    moreover assume "distinct xvec"
    ultimately have "Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])" 
      by(rule_tac r_input)
    with `length xvec = length Tvec` S `distinct_perm p` `(p \<bullet> xvec) \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P`
    have "Prop (K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr>) ((p \<bullet> P)[(p \<bullet> xvec)::=Tvec])"
      by(simp add: renaming subst_term.renaming)
  }
  moreover from Trans have "distinct xvec" by(rule input_distinct)
  hence "distinct(p \<bullet> xvec)" by simp
  ultimately show ?thesis using `(p \<bullet> xvec) \<sharp>* \<Psi>` `(p \<bullet> xvec) \<sharp>* M` `(p \<bullet> xvec) \<sharp>* \<alpha>` `(p \<bullet> xvec) \<sharp>* P'` `distinct xvec`
    by(rule_tac Goal) assumption+
qed

lemma output_cases[consumes 1, case_names c_output]:
  fixes \<Psi> :: 'b
  and   M  :: 'a
  and   N  :: 'a
  and   P  :: "('a, 'b, 'c) psi"  
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "\<And>K. \<lbrakk>\<pi> = Some(\<langle>\<epsilon>; \<epsilon>, M\<rangle>); \<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop (K\<langle>N\<rangle>) P"

  shows "Prop \<alpha> P'"
using assms
by(cases rule: semantics.cases) (auto simp add: residual_inject psi.inject)

lemma case_cases[consumes 1, case_names c_case]:
  fixes \<Psi> :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes Trans: "\<Psi> \<rhd> (Cases Cs) \<longmapsto> c\<pi> @ Rs"
  and     r_case: "\<And>\<phi> P \<pi>. \<lbrakk>\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs; c\<pi> = map_option (F_assert o push_prov) \<pi>; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"

  shows "Prop"
  using assms
  by(cases rule: semantics.cases) (auto simp add: residual_inject psi.inject)

lemma res_cases[consumes 7, case_names c_open c_res]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>c\<pi> @ \<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     r_open: "\<And>M \<pi> xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P'); c\<pi> = Some(\<lparr>\<nu>x\<rparr>\<pi>); y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec\<rbrakk> \<Longrightarrow>
                                         Prop (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     r_scope:  "\<And>\<pi> P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; c\<pi> = map_option (F_res x) \<pi>\<rbrakk> \<Longrightarrow> Prop \<alpha> (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop \<alpha> P'"
proof -
  from Trans have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)
  have "length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')" by simp
  from Trans have "bn \<alpha> \<sharp>* c\<pi>" using `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* P`
    by(auto intro: trans_fresh_provenance)
  from Trans have "x \<sharp> c\<pi>"
    by(drule_tac trans_fresh_provenance[where xvec="[x]"])
      (auto simp add: abs_fresh)
  note Trans
  moreover have "length [] = input_length(\<lparr>\<nu>x\<rparr>P)" and "distinct []"
    by(auto simp add: input_length_input_length'_input_length''.simps)
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  ultimately show ?thesis using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* c\<pi>` `x \<sharp> c\<pi>`
    apply(cases rule: semantics_cases[of _ _ _ _ _ _ _ _ _ _ _ x x])
    apply(auto simp add: psi.inject alpha abs_fresh residual_inject bound_output_app bound_output.inject eqvts)
    apply(subgoal_tac "y \<in> supp Na")
    apply(rule_tac r_open)
    apply(auto simp add: residual_inject bound_output_app)
    apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm eqvts)
    by(rule r_scope)
qed

lemma res_cases'[consumes 7, case_names c_open c_res]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>c\<pi> @ \<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     r_open: "\<And>M \<pi> xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>Some([(x, y)] \<bullet> \<pi>) @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; c\<pi> = Some(\<lparr>\<nu>x\<rparr>\<pi>); y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec\<rbrakk> \<Longrightarrow>
                                         Prop (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     r_scope:  "\<And>\<pi> P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; c\<pi> = map_option (F_res x) \<pi>\<rbrakk> \<Longrightarrow> Prop \<alpha> (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop \<alpha> P'"
proof -
  from Trans have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)
  have "length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')" by simp
  from Trans have "bn \<alpha> \<sharp>* c\<pi>" using `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* P`
    by(auto intro: trans_fresh_provenance)
  from Trans have "x \<sharp> c\<pi>"
    by(drule_tac trans_fresh_provenance[where xvec="[x]"])
      (auto simp add: abs_fresh)  
  note Trans
  moreover have "length [] = input_length(\<lparr>\<nu>x\<rparr>P)" and "distinct []"
    by(auto simp add: input_length_input_length'_input_length''.simps)
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  moreover note `length(bn \<alpha>) = residual_length(\<alpha> \<prec> P')` `distinct(bn \<alpha>)`
  ultimately show ?thesis using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* c\<pi>` `x \<sharp> c\<pi>`
    apply(cases rule: semantics_cases[of _ _ _ _ _ _ _ _ _ _ _ x x]) 
    apply(auto simp add: psi.inject alpha abs_fresh residual_inject bound_output_app bound_output.inject eqvts)
    apply(subgoal_tac "y \<in> supp Na")
    apply(rule_tac r_open)
    apply(auto simp add: residual_inject bound_output_app)
    apply(drule_tac pi="[(x, y)]" in semantics.eqvt)
    apply(simp add: calc_atm eqvts)
    apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm eqvts)
    by(rule r_scope)
qed

lemma action_par1_dest':
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* R"
  and     "bn \<beta> \<sharp>* R"

  obtains T where "P = T \<parallel> R" and "\<alpha> \<prec> T = \<beta> \<prec> Q"
using assms
apply(cases rule: action_cases[where \<alpha>=\<alpha>])
apply(auto simp add: residual_inject)
by(drule_tac bound_output_par1_dest) auto

lemma action_par2_dest':
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<beta> \<sharp>* Q"

  obtains T where "P = Q \<parallel> T" and "\<alpha> \<prec> T = \<beta> \<prec> R"
using assms
apply(cases rule: action_cases[where \<alpha>=\<alpha>])
apply(auto simp add: residual_inject)
by(drule_tac bound_output_par2_dest) auto

lemma expand_non_tau_frame:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   C    :: "'d::fs_name"
  and   C'   :: "'e::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* C"
  and     "A\<^sub>P \<sharp>* C'"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* C'"
  and     "\<alpha> \<noteq> \<tau>"

  obtains p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct_perm p" and
                              "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" and
                              "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'" and "distinct A\<^sub>P'"
proof -
  assume A: "\<And>p \<Psi>' \<Psi>\<^sub>P' A\<^sub>P'.
        \<lbrakk>set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); (p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'; distinct_perm p;
                              extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>; A\<^sub>P' \<sharp>* P'; A\<^sub>P' \<sharp>* \<alpha>; A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>);
                              A\<^sub>P' \<sharp>* C; (bn(p \<bullet> \<alpha>)) \<sharp>* C'; (bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; distinct A\<^sub>P'\<rbrakk>
        \<Longrightarrow> thesis"

  from Trans have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)

  with Trans `bn \<alpha> \<sharp>* subject \<alpha>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` have "A\<^sub>P \<sharp>* P'"
    by(drule_tac free_fresh_chain_derivative) auto
  {
    fix X :: "name list"
    and Y :: "'b list"
    and Z :: "('a, 'b, 'c) psi list"

    assume "bn \<alpha> \<sharp>* X" and "bn \<alpha> \<sharp>* Y" and "bn \<alpha> \<sharp>* Z" and "A\<^sub>P \<sharp>* X" and "A\<^sub>P \<sharp>* Y" and "A\<^sub>P \<sharp>* Z" 

    with assms obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct_perm p"
                                      and "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                      and "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                      and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                      and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
      using `A\<^sub>P \<sharp>* P'` `distinct(bn \<alpha>)`
    proof(nominal_induct \<Psi> P \<pi> Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P D=="()" avoiding: C C' \<alpha> P' X Y Z arbitrary: thesis rule: semantics_frame_induct)
      case(c_alpha \<Psi> P A\<^sub>P \<Psi>\<^sub>P \<pi> p C C' \<alpha> P' X Y Z)
      then obtain q \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Sq: "set q \<subseteq> set(bn \<alpha>) \<times> set(bn(q \<bullet> \<alpha>))" and Peq_p': "(q \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct_perm q"
                                  and Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (q \<bullet> \<alpha>)"
                                  and "A\<^sub>P' \<sharp>* C" and "(bn(q \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* P'"
                                  and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                  and "(bn(q \<bullet> \<alpha>)) \<sharp>* X" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Z"
	by metis

      have Sp: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)" by fact

      from Sq have "(p \<bullet> set q) \<subseteq> p \<bullet> (set(bn \<alpha>) \<times> set(bn(q \<bullet> \<alpha>)))"
	by(simp add: subset_closed)
      hence "set(p \<bullet> q) \<subseteq> set(bn(p \<bullet> \<alpha>)) \<times> set(p \<bullet> bn(q \<bullet> \<alpha>))"
	by(simp add: eqvts)
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` Sp have "set(p \<bullet> q) \<subseteq> set(bn \<alpha>) \<times> set(bn((p \<bullet> q) \<bullet> \<alpha>))"
	by(simp add: perm_compose bn_eqvt[symmetric])
      moreover from Peq_p' have "(p \<bullet> (q \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')"
	by(simp add: Assertion_stat_eq_closed)
      hence "((p \<bullet> q) \<bullet> p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')"
	apply(subst perm_compose[symmetric])
	by(simp add: eqvts)
      moreover from `distinct_perm q` have "distinct_perm (p \<bullet> q)"
	by simp
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* C'` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> C')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* C'` `(p \<bullet> A\<^sub>P) \<sharp>* C'` Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* C'"
	by(simp add: perm_compose bn_eqvt[symmetric])
      moreover from Fr_p' have "(p \<bullet> extract_frame P') = p \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" by simp
      with `A\<^sub>P \<sharp>* P'` `(p \<bullet> A\<^sub>P) \<sharp>* P'` Sp have "extract_frame P' = \<langle>p \<bullet> A\<^sub>P', p \<bullet> \<Psi>\<^sub>P'\<rangle>"
	by(simp add: eqvts)
      moreover from `A\<^sub>P' \<sharp>* P'` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> P')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* P'` `(p \<bullet> A\<^sub>P) \<sharp>* P'` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* P'" by simp
      moreover from `A\<^sub>P' \<sharp>* \<alpha>` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> \<alpha>)"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* \<alpha>" by simp
      moreover from `A\<^sub>P' \<sharp>* C` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> C)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* C` `(p \<bullet> A\<^sub>P) \<sharp>* C` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* C" by simp
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<alpha>)"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* \<alpha>"
	by(simp add: perm_compose eqvts)
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* P'` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> P')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `(p \<bullet> A\<^sub>P) \<sharp>* P'` Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* P'"
	by(simp add: perm_compose eqvts)
      moreover from `A\<^sub>P' \<sharp>* (q \<bullet> \<alpha>)` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> q \<bullet> \<alpha>)"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with Sp `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` have "(p \<bullet> A\<^sub>P') \<sharp>* ((p \<bullet> q) \<bullet> \<alpha>)"
	by(simp add: perm_compose)
      moreover from `A\<^sub>P' \<sharp>* X` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> X)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* X` `(p \<bullet> A\<^sub>P) \<sharp>* X` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* X" by simp
      moreover from `A\<^sub>P' \<sharp>* Y` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Y)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* Y` `(p \<bullet> A\<^sub>P) \<sharp>* Y` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* Y" by simp
      moreover from `A\<^sub>P' \<sharp>* Z` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Z)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* Z` `(p \<bullet> A\<^sub>P) \<sharp>* Z` Sp have "(p \<bullet> A\<^sub>P') \<sharp>* Z" by simp
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* X` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> X)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* X` `(p \<bullet> A\<^sub>P) \<sharp>* X` Sp have "bn((p \<bullet> q) \<bullet>  \<alpha>) \<sharp>* X"
	by(simp add: perm_compose eqvts)
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* Y` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> Y)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Y` `(p \<bullet> A\<^sub>P) \<sharp>* Y` Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* Y"
	by(simp add: perm_compose eqvts)
      moreover from `(bn(q \<bullet> \<alpha>)) \<sharp>* Z` have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> Z)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* \<alpha>` `(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Z` `(p \<bullet> A\<^sub>P) \<sharp>* Z` Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* Z"
	by(simp add: perm_compose eqvts)
      moreover from `distinct A\<^sub>P'` have "distinct(p \<bullet> A\<^sub>P')" by simp
      ultimately show ?case
	by(rule_tac c_alpha)
    next
      case(c_input \<Psi> M K xvec N Tvec P C C' \<alpha> P' X Y Z)
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extract_frame(P[xvec::=Tvec]) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                      and "A\<^sub>P \<sharp>* (C, P[xvec::=Tvec], \<alpha>, P', X, Y, Z, N)"
	by(rule fresh_frame)
      moreover have "\<one> \<otimes> \<Psi>\<^sub>P \<simeq> \<Psi>\<^sub>P"
	by(blast intro: Identity Commutativity Assertion_stat_eq_trans)
      ultimately show ?case
	by(rule_tac c_input) (assumption | simp add: residual_inject)+
    next
      case(c_output \<Psi> M K N P C C' \<alpha> P' X Y Z)
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                               and "A\<^sub>P \<sharp>* (C, C', P, \<alpha>, N, P', X, Y, Z)"
	by(rule fresh_frame)
      moreover have "\<one> \<otimes> \<Psi>\<^sub>P \<simeq> \<Psi>\<^sub>P"
	by(blast intro: Identity Commutativity Assertion_stat_eq_trans)
      ultimately show ?case by(simp add: residual_inject)
    next
      case(c_case \<Psi> P \<pi> \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P' X Y Z)
      moreover from `bn \<alpha> \<sharp>* (Cases Cs)` `(\<phi>, P) mem Cs` have "bn \<alpha> \<sharp>* P"
      proof -
        from `bn \<alpha> \<sharp>* (Cases Cs)` `(\<phi>, P) mem Cs` have "bn \<alpha> \<sharp>* (\<phi>,P)"
          by(rule_tac mem_fresh_chain) (assumption|simp)+
        thus ?thesis by simp
      qed
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"
                                         and Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                         and Peq_p': "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                         and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                         and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
                                         and "distinct_perm p" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                         and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
	by(rule_tac c_case) (assumption | simp (no_asm_use))+
      moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "(p \<bullet> \<Psi>\<^sub>P) \<simeq> (p \<bullet> \<one>)"
	by(simp add: Assertion_stat_eq_closed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<simeq> \<one>" by(simp add: perm_bottom)
      with Peq_p' have "(\<one> \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
	by(metis Identity Assertion_stat_eq_trans composition' Commutativity Associativity Assertion_stat_eq_sym)
      ultimately show ?case using c_case `bn \<alpha> \<sharp>* P`
	by(rule_tac c_case(23)) (assumption | simp)+
    next
      case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C C' \<alpha>' PQ' X Y Z)
      have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
	by fact+

      note `bn \<alpha>' \<sharp>* subject \<alpha>'`
      moreover from `bn \<alpha>' \<sharp>* (P \<parallel> Q)` have "bn \<alpha>' \<sharp>* P" and "bn \<alpha>' \<sharp>* Q" by simp+    
      moreover with FrP FrQ `A\<^sub>P \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` have "bn \<alpha>' \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q" 
	by(force dest: extract_frame_fresh_chain)+
 
      moreover from `bn \<alpha>' \<sharp>* X` `A\<^sub>Q \<sharp>* \<alpha>'` have "bn \<alpha>' \<sharp>* (X@A\<^sub>Q)" by simp
      moreover from `bn \<alpha>' \<sharp>* Y` `bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q` have "bn \<alpha>' \<sharp>* (\<Psi>\<^sub>Q#Y)" by simp
      moreover from `bn \<alpha>' \<sharp>* Z` `bn \<alpha>' \<sharp>* Q` have "bn \<alpha>' \<sharp>* (Q#Z)" by simp
      moreover from `A\<^sub>P \<sharp>* X` `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* (X@A\<^sub>Q)" by simp
      moreover from `A\<^sub>P \<sharp>* Y` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` have "A\<^sub>P \<sharp>* (\<Psi>\<^sub>Q#Y)" by force
      moreover from `A\<^sub>P \<sharp>* Z` `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (Q#Z)" by simp
      moreover from `\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> PQ'` `bn \<alpha> \<sharp>* Q` `bn \<alpha>' \<sharp>* Q` `bn \<alpha> \<sharp>* \<alpha>'`
      obtain P'' where A: "\<alpha> \<prec> P' = \<alpha>' \<prec> P''" and "PQ' = P'' \<parallel> Q"
	by(metis action_par1_dest')
      moreover from `A\<^sub>P \<sharp>* PQ'` `PQ' = P'' \<parallel> Q` have "A\<^sub>P \<sharp>* P''" by simp
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set (bn(p \<bullet> \<alpha>'))" and Peq_p': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                        and "distinct_perm p" and "(bn(p \<bullet> \<alpha>')) \<sharp>* C'" and Fr_p': "extract_frame P'' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                        and "A\<^sub>P' \<sharp>* P''" and "A\<^sub>P' \<sharp>* \<alpha>'" "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>P' \<sharp>* C" 
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'" and "(bn(p \<bullet> \<alpha>')) \<sharp>* P''" and "distinct A\<^sub>P'"
                                        and "A\<^sub>P' \<sharp>* (X @ A\<^sub>Q)" and "A\<^sub>P' \<sharp>* (\<Psi>\<^sub>Q#Y)"
                                        and "A\<^sub>P' \<sharp>* (Q#Z)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (X @ A\<^sub>Q)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (\<Psi>\<^sub>Q#Y)"
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* (Q#Z)" using c_par1
	by(rule_tac c_par1)

      then have "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q"  and "A\<^sub>P' \<sharp>* Y" 
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* A\<^sub>Q" and "(bn(p \<bullet> \<alpha>')) \<sharp>* X" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Z" and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>Q"
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* Q"
	by(simp del: fresh_chain_simps)+

      from `A\<^sub>Q \<sharp>* PQ'` `PQ' = P'' \<parallel> Q` `A\<^sub>P' \<sharp>* A\<^sub>Q` Fr_p' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'"
	by(force dest: extract_frame_fresh_chain)
      note S
      moreover from Peq_p' have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P' \<otimes> (p \<bullet> \<Psi>\<^sub>Q)"
	by(simp add: eqvts) (metis Composition Associativity Assertion_stat_eq_trans Assertion_stat_eq_sym Commutativity)
      with `(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q` S have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q"
	by simp
      moreover from `PQ' = P'' \<parallel> Q` `A\<^sub>P' \<sharp>* A\<^sub>Q` `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'` `A\<^sub>Q \<sharp>* PQ'` Fr_p' FrQ have "extract_frame PQ' = \<langle>(A\<^sub>P'@A\<^sub>Q), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by simp
      moreover note `distinct_perm p` `(bn(p \<bullet> \<alpha>')) \<sharp>* C'`
      moreover from `A\<^sub>P' \<sharp>* P''` `A\<^sub>P' \<sharp>* Q` `PQ' = P'' \<parallel> Q` have "A\<^sub>P' \<sharp>* PQ'" by simp
      moreover note `A\<^sub>Q \<sharp>* PQ'` `A\<^sub>P' \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` `A\<^sub>P' \<sharp>* C` `A\<^sub>Q \<sharp>* C` `(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'`
      moreover from `bn \<alpha>' \<sharp>* Q` have "(bn(p \<bullet> \<alpha>')) \<sharp>* (p \<bullet> Q)" 
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bn_eqvt[symmetric])
      with `bn \<alpha> \<sharp>* Q` `(bn(p \<bullet> \<alpha>')) \<sharp>* Q` S have "(bn(p \<bullet> \<alpha>')) \<sharp>* Q" by simp
      with `(bn(p \<bullet> \<alpha>')) \<sharp>* P''` `PQ' = P'' \<parallel> Q` have "(bn(p \<bullet> \<alpha>')) \<sharp>* PQ'" by simp
      moreover from `A\<^sub>P' \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* \<alpha>'" by simp
      moreover from `A\<^sub>P' \<sharp>* C` `A\<^sub>Q \<sharp>* C` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* C" by simp
      moreover from `A\<^sub>P' \<sharp>* X` `A\<^sub>Q \<sharp>* X` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* X" by simp
      moreover from `A\<^sub>P' \<sharp>* Y` `A\<^sub>Q \<sharp>* Y` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Y" by simp
      moreover from `A\<^sub>P' \<sharp>* Z` `A\<^sub>Q \<sharp>* Z` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Z" by simp
      moreover from `A\<^sub>P' \<sharp>* PQ'` `A\<^sub>Q \<sharp>* PQ'` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* PQ'" by simp
      moreover from `A\<^sub>P' \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* \<alpha>'" by simp
      moreover from `A\<^sub>Q \<sharp>* \<alpha>'` have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<alpha>')"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bn_eqvt[symmetric])
      with S `A\<^sub>Q \<sharp>* \<alpha>'` `bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* (p \<bullet> \<alpha>')"
	by simp
      with `A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')` `A\<^sub>Q \<sharp>* \<alpha>'` `bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>Q` S have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* (p \<bullet> \<alpha>')"
	by simp
      moreover from `A\<^sub>P' \<sharp>* A\<^sub>Q` `distinct A\<^sub>P'` `distinct A\<^sub>Q` have "distinct(A\<^sub>P'@A\<^sub>Q)" by auto
      moreover note `(bn(p \<bullet> \<alpha>')) \<sharp>* X` `(bn(p \<bullet> \<alpha>')) \<sharp>* Y` `(bn(p \<bullet> \<alpha>')) \<sharp>* Z`
      ultimately show ?case using c_par1
	by metis
    next
      case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C C' \<alpha>' PQ' X Y Z)
      have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and  FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
	by fact+

      note `bn \<alpha>' \<sharp>* subject \<alpha>'`
      moreover from `bn \<alpha>' \<sharp>* (P \<parallel> Q)` have "bn \<alpha>' \<sharp>* Q" and "bn \<alpha>' \<sharp>* P" by simp+    
      moreover with FrP FrQ `A\<^sub>P \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` have "bn \<alpha>' \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q" 
	by(force dest: extract_frame_fresh_chain)+
 
      moreover from `bn \<alpha>' \<sharp>* X` `A\<^sub>P \<sharp>* \<alpha>'` have "bn \<alpha>' \<sharp>* (X@A\<^sub>P)" by simp
      moreover from `bn \<alpha>' \<sharp>* Y` `bn \<alpha>' \<sharp>* \<Psi>\<^sub>P` have "bn \<alpha>' \<sharp>* (\<Psi>\<^sub>P#Y)" by simp
      moreover from `bn \<alpha>' \<sharp>* Z` `bn \<alpha>' \<sharp>* P` have "bn \<alpha>' \<sharp>* (P#Z)" by simp
      moreover from `A\<^sub>Q \<sharp>* X` `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>Q \<sharp>* (X@A\<^sub>P)" by simp
      moreover from `A\<^sub>Q \<sharp>* Y` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q \<sharp>* (\<Psi>\<^sub>P#Y)" by force
      moreover from `A\<^sub>Q \<sharp>* Z` `A\<^sub>Q \<sharp>* P` have "A\<^sub>Q \<sharp>* (P#Z)" by simp
      moreover from `\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> PQ'` `bn \<alpha> \<sharp>* P` `bn \<alpha>' \<sharp>* P` `bn \<alpha> \<sharp>* \<alpha>'`
      obtain Q'' where A: "\<alpha> \<prec> Q' = \<alpha>' \<prec> Q''" and "PQ' = P \<parallel> Q''"
	by(metis action_par2_dest')
      moreover from `A\<^sub>Q \<sharp>* PQ'` `PQ' = P \<parallel> Q''` have "A\<^sub>Q \<sharp>* Q''" by simp
      ultimately obtain p \<Psi>' A\<^sub>Q' \<Psi>\<^sub>Q' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set (bn(p \<bullet> \<alpha>'))" and Qeq_q': "((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>Q'"
                                        and "distinct_perm p" and "(bn(p \<bullet> \<alpha>')) \<sharp>* C'" and Fr_q': "extract_frame Q'' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>"
                                        and "A\<^sub>Q' \<sharp>* Q''" and "A\<^sub>Q' \<sharp>* \<alpha>'" "A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>Q' \<sharp>* C" 
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Q''" and "distinct A\<^sub>Q'"
                                        and "A\<^sub>Q' \<sharp>* (X @ A\<^sub>P)" and "A\<^sub>Q' \<sharp>* (\<Psi>\<^sub>P#Y)"
                                        and "A\<^sub>Q' \<sharp>* (P#Z)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (X @ A\<^sub>P)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (\<Psi>\<^sub>P#Y)"
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* (P#Z)" using c_par2
	by(rule_tac c_par2)

      then have "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* A\<^sub>P" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q' \<sharp>* Y" 
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* A\<^sub>P" and "(bn(p \<bullet> \<alpha>')) \<sharp>* X" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Z" and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>P"
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* P"
	by(simp del: fresh_chain_simps)+

      from `A\<^sub>P \<sharp>* PQ'` `PQ' = P \<parallel> Q''` `A\<^sub>Q' \<sharp>* A\<^sub>P` Fr_q' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'"
	by(force dest: extract_frame_fresh_chain)
      note S
      moreover from Qeq_q' have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q'"
	by(simp add: eqvts) (metis Composition Associativity Assertion_stat_eq_trans Assertion_stat_eq_sym Commutativity)
      with `(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>P` `bn \<alpha>' \<sharp>* \<Psi>\<^sub>P` S have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'"
	by simp
      moreover from `PQ' = P \<parallel> Q''` `A\<^sub>Q' \<sharp>* A\<^sub>P` `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'` `A\<^sub>P \<sharp>* PQ'` Fr_q' FrP have "extract_frame PQ' = \<langle>(A\<^sub>P@A\<^sub>Q'), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'\<rangle>"
	by simp
      moreover note `distinct_perm p` `(bn(p \<bullet> \<alpha>')) \<sharp>* C'`
      moreover from `A\<^sub>Q' \<sharp>* Q''` `A\<^sub>Q' \<sharp>* P` `PQ' = P \<parallel> Q''` have "A\<^sub>Q' \<sharp>* PQ'" by simp
      moreover note `A\<^sub>Q \<sharp>* PQ'` `A\<^sub>Q' \<sharp>* \<alpha>'` `A\<^sub>Q \<sharp>* \<alpha>'` `A\<^sub>Q' \<sharp>* C` `A\<^sub>Q \<sharp>* C` `(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'`
      moreover from `bn \<alpha>' \<sharp>* Q` have "(bn(p \<bullet> \<alpha>')) \<sharp>* (p \<bullet> Q)" 
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bn_eqvt[symmetric])
      with `bn \<alpha> \<sharp>* P` `(bn(p \<bullet> \<alpha>')) \<sharp>* P` S have "(bn(p \<bullet> \<alpha>')) \<sharp>* P" by simp
      with `(bn(p \<bullet> \<alpha>')) \<sharp>* Q''` `PQ' = P \<parallel> Q''` have "(bn(p \<bullet> \<alpha>')) \<sharp>* PQ'" by simp
      moreover from `A\<^sub>Q' \<sharp>* \<alpha>'` `A\<^sub>P \<sharp>* \<alpha>'` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* \<alpha>'" by simp
      moreover from `A\<^sub>Q' \<sharp>* C` `A\<^sub>P \<sharp>* C` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* C" by simp
      moreover from `A\<^sub>Q' \<sharp>* X` `A\<^sub>P \<sharp>* X` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* X" by simp
      moreover from `A\<^sub>Q' \<sharp>* Y` `A\<^sub>P \<sharp>* Y` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from `A\<^sub>Q' \<sharp>* Z` `A\<^sub>P \<sharp>* Z` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from `A\<^sub>Q' \<sharp>* PQ'` `A\<^sub>P \<sharp>* PQ'` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* PQ'" by simp
      moreover from `A\<^sub>Q' \<sharp>* \<alpha>'` `A\<^sub>P \<sharp>* \<alpha>'` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* \<alpha>'" by simp
      moreover from `A\<^sub>P \<sharp>* \<alpha>'` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<alpha>')"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bn_eqvt[symmetric])
      with S `A\<^sub>P \<sharp>* \<alpha>'` `bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* (p \<bullet> \<alpha>')"
	by simp
      with `A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>')` `A\<^sub>P \<sharp>* \<alpha>'` `bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>P` S have "(A\<^sub>P@A\<^sub>Q') \<sharp>* (p \<bullet> \<alpha>')"
	by simp
      moreover note `(bn(p \<bullet> \<alpha>')) \<sharp>* X` `(bn(p \<bullet> \<alpha>')) \<sharp>* Y` `(bn(p \<bullet> \<alpha>')) \<sharp>* Z`
      moreover from `A\<^sub>Q' \<sharp>* A\<^sub>P` `distinct A\<^sub>P` `distinct A\<^sub>Q'` have "distinct(A\<^sub>P@A\<^sub>Q')" by auto
      ultimately show ?case using c_par2
	by metis
    next
      case c_comm1
      thus ?case by(simp add: residual_inject)
    next
      case c_comm2
      thus ?case by(simp add: residual_inject)
    next
      case(c_open \<Psi> P \<pi> M xvec1 xvec2 N P' x A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P'' X Y Z)
      from `M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''` `x \<sharp> xvec1` `x \<sharp> xvec2` `x \<sharp> \<alpha>` `x \<sharp> P''` `distinct(bn \<alpha>)` `A\<^sub>P \<sharp>* \<alpha>` `x \<sharp> \<alpha>`
      obtain yvec1 y yvec2 N' where yvec_eq: "bn \<alpha> = yvec1@y#yvec2" and P'eq_p'': "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>N \<prec>' P' = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N') \<prec>' ([(x, y)] \<bullet> P'')" and "A\<^sub>P \<sharp>* N'" and Subj: "subject \<alpha> = Some M" and "x \<sharp> N'" and \<alpha>eq: "\<alpha> = M\<lparr>\<nu>*(yvec1@y#yvec2)\<rparr>\<langle>N'\<rangle>"
	apply(cases rule: action_cases[where \<alpha>=\<alpha>])
	apply(auto simp add: residual_inject)
        by(rule bound_output_open_dest) blast+
     note `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M`
      moreover from Subj yvec_eq `bn \<alpha> \<sharp>* subject \<alpha>` have "yvec1 \<sharp>* M" "yvec2 \<sharp>* M" by simp+
      moreover from yvec_eq `A\<^sub>P \<sharp>* \<alpha>` have "A\<^sub>P \<sharp>* (yvec1@yvec2)" by simp
      moreover note `A\<^sub>P \<sharp>* C`
      moreover from yvec_eq  `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P` `x \<sharp> \<alpha>` have "(yvec1@yvec2) \<sharp>* P" by simp
      moreover from yvec_eq `bn \<alpha> \<sharp>* C'` `bn \<alpha> \<sharp>* X` `bn \<alpha> \<sharp>* Y` `bn \<alpha> \<sharp>* Z` `distinct(bn \<alpha>)` `x \<sharp> \<alpha>`
      have "(yvec1@yvec2) \<sharp>* C'" and "(yvec1@yvec2) \<sharp>* (x#y#X)" and "(yvec1@yvec2) \<sharp>* Y" and "(yvec1@yvec2) \<sharp>* Z"
	by simp+
      moreover from `A\<^sub>P \<sharp>* X` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* \<alpha>` yvec_eq have "A\<^sub>P \<sharp>* (x#y#X)" by simp
      moreover note `A\<^sub>P \<sharp>* Y` `A\<^sub>P \<sharp>* Z`
      moreover from `A\<^sub>P \<sharp>* N'` `A\<^sub>P \<sharp>* P''` `x \<sharp> A\<^sub>P` `A\<^sub>P \<sharp>* \<alpha>` yvec_eq have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> N')" and  "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> P'')"
	by simp+
      moreover from yvec_eq `distinct(bn \<alpha>)` have "distinct(yvec1@yvec2)" by simp
      moreover from P'eq_p'' have "M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P' = M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P'')"
	by(simp add: residual_inject)
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set (yvec1@yvec2) \<times> set (p \<bullet> (yvec1@yvec2))" and Peq_p': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                        and "distinct_perm p" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* C'" and Fr_p': "extract_frame([(x, y)] \<bullet> P'') = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                        and "A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> P'')" and "A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> N')" and "A\<^sub>P' \<sharp>* C" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')" and "A\<^sub>P' \<sharp>* M" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* (yvec1@yvec2)" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* M" and "distinct A\<^sub>P'"
                                        and "(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> P'')" and "(yvec1@yvec2) \<sharp>* A\<^sub>P'" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'"
                                        and "A\<^sub>P' \<sharp>* (x#y#X)" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* (x#y#X)"
                                        and "(p \<bullet> (yvec1@yvec2)) \<sharp>* Y" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* Z" using `A\<^sub>P \<sharp>* C'`
	apply(rule_tac c_open(4)[where bd="x#y#X"])
        apply assumption+
	prefer 17
        apply simp
        defer
	by(assumption | simp)+

      from `A\<^sub>P' \<sharp>* (x#y#X)` have "x \<sharp> A\<^sub>P'" and "y \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      from `(p \<bullet> (yvec1@yvec2)) \<sharp>* (x#y#X)` have "x \<sharp> (p \<bullet> (yvec1@yvec2))" and  "y \<sharp> (p \<bullet> (yvec1@yvec2))" and  "(p \<bullet> (yvec1@yvec2)) \<sharp>* X" by simp+

      from `x \<sharp> \<alpha>` yvec_eq have "x \<sharp> yvec1" and "x \<noteq> y" and "x \<sharp> yvec2" by simp+
      from `distinct(bn \<alpha>)` yvec_eq have "yvec1 \<sharp>* yvec2" and "y \<sharp> yvec1" and "y \<sharp> yvec2" by simp+
      from `bn \<alpha> \<sharp>* C'` yvec_eq have "yvec1 \<sharp>* C'" and "y \<sharp> C'" and "yvec2 \<sharp>* C'" by simp+

      from S `x \<sharp> \<alpha>` `x \<sharp> p \<bullet> (yvec1@yvec2)` yvec_eq have "x \<sharp> p" by(rule_tac fresh_alpha_swap) (assumption | simp)+
      from S `distinct(bn \<alpha>)` `y \<sharp> p \<bullet> (yvec1@yvec2)` yvec_eq have "y \<sharp> p" by(rule_tac fresh_alpha_swap) (assumption | simp)+

      from yvec_eq S `x \<sharp> yvec1` `x \<sharp> yvec2` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p \<bullet> (yvec1@yvec2)` `y \<sharp> p \<bullet> (yvec1@yvec2)`
      have "set ((y, x)#p) \<subseteq> set(bn \<alpha>) \<times> set(bn(((y, x)#p) \<bullet> \<alpha>))"
	apply(simp add: bn_eqvt[symmetric])
	by(auto simp add: eqvts calc_atm)

      moreover from Peq_p' have "([(y, x)] \<bullet> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>')) \<simeq> [(y, x)] \<bullet> \<Psi>\<^sub>P'"
	by(simp add: Assertion_stat_eq_closed)
      hence "(((y, x)#p) \<bullet> \<Psi>\<^sub>P) \<otimes> ([(y, x)] \<bullet> \<Psi>') \<simeq> ([(y, x)] \<bullet> \<Psi>\<^sub>P')"
	by(simp add: eqvts)
      moreover from `distinct_perm p` S `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` have "distinct_perm((y, x)#p)"
	by simp
      moreover from Fr_p' have "([(x, y)] \<bullet> (extract_frame([(x, y)] \<bullet> P''))) = ([(x, y)] \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>)"
	by simp
      with `x \<sharp> A\<^sub>P'` `y \<sharp> A\<^sub>P'` have "extract_frame P'' = \<langle>A\<^sub>P', ([(y, x)] \<bullet> \<Psi>\<^sub>P')\<rangle>"
	by(simp add: eqvts name_swap)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> N'` `(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')` have "([(y, x)] \<bullet> p \<bullet> (yvec1@yvec2)) \<sharp>* ([(y, x)] \<bullet> [(x, y)] \<bullet> N')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      hence "(((y, x)#p) \<bullet> (yvec1@yvec2)) \<sharp>* N'" by(simp add: name_swap) 
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> C` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `x \<sharp> N'` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* N'" by(simp add: bn_eqvt[symmetric]) (simp add: eqvts perm_compose calc_atm fresh_chain_simps)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> N'` `(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> P'')` have "([(y, x)] \<bullet> p \<bullet> (yvec1@yvec2)) \<sharp>* ([(y, x)] \<bullet> [(x, y)] \<bullet> P'')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      hence "(((y, x)#p) \<bullet> (yvec1@yvec2)) \<sharp>* P''" by(simp add: name_swap) 
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `x \<sharp> P''` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* P''" by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps) 
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> A\<^sub>P'` `(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'` have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* A\<^sub>P'"
	by(simp add: eqvts fresh_chain_simps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> A\<^sub>P')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> A\<^sub>P'` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `y \<sharp> A\<^sub>P'` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* A\<^sub>P'" by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> C'` `(p \<bullet> (yvec1@yvec2)) \<sharp>* C'` have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* C'"
	by(simp add: eqvts fresh_chain_simps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> C')"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> C'` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `y \<sharp> C'` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* C'"  by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> X` `(p \<bullet> (yvec1@yvec2)) \<sharp>* X` have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* X"
	by(simp add: eqvts fresh_chain_simps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> X)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> X` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `bn \<alpha> \<sharp>* X` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* X" by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> Y` `(p \<bullet> (yvec1@yvec2)) \<sharp>* Y` have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* Y"
	by(simp add: eqvts fresh_chain_simps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> Y)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> Y` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `bn \<alpha> \<sharp>* Y` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* Y" by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps)
      moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> Z` `(p \<bullet> (yvec1@yvec2)) \<sharp>* Z` have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* Z"
	by(simp add: eqvts fresh_chain_simps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> Z)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<noteq> y` `x \<sharp> Z` `y \<sharp> yvec1` `y \<sharp> yvec2` `x \<sharp> p` `y \<sharp> p` `bn \<alpha> \<sharp>* Z` yvec_eq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* Z" by(simp add: bn_eqvt[symmetric]) (simp add: perm_compose calc_atm eqvts fresh_chain_simps)
      moreover from `(yvec1@yvec2) \<sharp>* A\<^sub>P'` `y \<sharp> A\<^sub>P'` yvec_eq have "bn \<alpha> \<sharp>* A\<^sub>P'"
	by simp
      moreover from `A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> N')` have "([(x, y)] \<bullet> A\<^sub>P') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> N')"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> A\<^sub>P'` `y \<sharp> A\<^sub>P'` have "A\<^sub>P' \<sharp>* N'" by simp
      with `A\<^sub>P' \<sharp>* M` `(yvec1@yvec2) \<sharp>* A\<^sub>P'` `y \<sharp> A\<^sub>P'` \<alpha>eq have "A\<^sub>P' \<sharp>* \<alpha>" by simp
      moreover hence "(((y, x)#p) \<bullet> A\<^sub>P') \<sharp>* (((y, x)#p) \<bullet> \<alpha>)"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> A\<^sub>P'` `y \<sharp> A\<^sub>P'` S `(yvec1@yvec2) \<sharp>* A\<^sub>P'` `(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'`
      have "A\<^sub>P' \<sharp>* (((y, x)#p) \<bullet> \<alpha>)" by(simp add: eqvts)
      moreover from `A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> P'')` have "([(x, y)] \<bullet> A\<^sub>P') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> P'')"
	by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> A\<^sub>P'` `y \<sharp> A\<^sub>P'` have "A\<^sub>P' \<sharp>* P''" by simp
      moreover from yvec_eq \<alpha>eq `(p \<bullet> (yvec1@yvec2)) \<sharp>* (yvec1@yvec2)` `y \<sharp> p` `x \<sharp> \<alpha>` S `(p \<bullet> (yvec1@yvec2)) \<sharp>* M``(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')` `y \<sharp> yvec1``y \<sharp> yvec2` `x \<sharp> p`
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* \<alpha>"
      apply(simp add: eqvts del: set_append) 
      apply(intro conjI)
      apply(simp add: perm_compose eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose eqvts del: set_append)
      apply(simp add: perm_compose eqvts swap_star_fresh del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) swap_star_fresh calc_atm eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(subst pt_fresh_star_bij[symmetric, OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"])
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      apply(subst pt_fresh_star_bij[symmetric, OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"])
      by(simp add: perm_compose fresh_chain_simps(6) calc_atm eqvts del: set_append)
      moreover note `A\<^sub>P' \<sharp>* C` `A\<^sub>P' \<sharp>* X` `A\<^sub>P' \<sharp>* Y` `A\<^sub>P' \<sharp>* Z` `distinct A\<^sub>P'`

      ultimately show ?case
	by(rule_tac c_open)
    next
      case(c_scope \<Psi> P \<pi> \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C C' \<alpha>' P'' X Y Z)
      from `\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P' = \<alpha>' \<prec> P''` `x \<sharp> \<alpha>` `x \<sharp> \<alpha>'`
      obtain P''' where "\<alpha> \<prec> P' = \<alpha>' \<prec> P'''" and "P'' = \<lparr>\<nu>x\<rparr>P'''"
	apply(cases rule: action_cases[where \<alpha>=\<alpha>])
	apply(auto simp add: residual_inject)
	by(metis bound_output_scope_dest)
      then obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set(bn(p \<bullet> \<alpha>'))" and Peq_p': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                  and "distinct_perm p" and "bn(p \<bullet> \<alpha>') \<sharp>* C'" and Fr_p': "extract_frame P''' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                  and "A\<^sub>P' \<sharp>* P'''" and "A\<^sub>P' \<sharp>* \<alpha>'" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
                                  and "bn(p \<bullet> \<alpha>') \<sharp>* P'''" and "A\<^sub>P' \<sharp>* (x#X)" and "A\<^sub>P' \<sharp>* Y" and "bn(p \<bullet> \<alpha>') \<sharp>* \<alpha>'"
                                  and "A\<^sub>P' \<sharp>* Z" and "bn(p \<bullet> \<alpha>') \<sharp>* (x#X)" and "bn(p \<bullet> \<alpha>') \<sharp>* Y"
                                  and "bn(p \<bullet> \<alpha>') \<sharp>* Z" using c_scope
	by(rule_tac c_scope) (assumption | simp)+
      from `A\<^sub>P' \<sharp>* (x#X)` have "x \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      from `bn(p \<bullet> \<alpha>') \<sharp>* (x#X)` have "x \<sharp> bn(p \<bullet> \<alpha>')" and "bn(p \<bullet> \<alpha>') \<sharp>* X" by simp+

      note S Peq_p' `distinct_perm p` `bn(p \<bullet> \<alpha>') \<sharp>* C'`
      moreover from Fr_p' `P'' = \<lparr>\<nu>x\<rparr>P'''` have "extract_frame P'' = \<langle>(x#A\<^sub>P'), \<Psi>\<^sub>P'\<rangle>" by simp
      moreover from `A\<^sub>P' \<sharp>* P'''` `P'' = \<lparr>\<nu>x\<rparr>P'''` `x \<sharp> A\<^sub>P'` have "(x#A\<^sub>P') \<sharp>* P''" by(simp add: abs_fresh)
      moreover from `A\<^sub>P' \<sharp>* \<alpha>'` `A\<^sub>P' \<sharp>* C`  `x \<sharp> \<alpha>'` `x \<sharp> C` have "(x#A\<^sub>P') \<sharp>* \<alpha>'"  and "(x#A\<^sub>P') \<sharp>* C" by simp+
      moreover note `bn(p \<bullet> \<alpha>') \<sharp>* \<alpha>'`
      moreover from `bn(p \<bullet> \<alpha>') \<sharp>* P'''` `P'' = \<lparr>\<nu>x\<rparr>P'''` `x \<sharp> bn(p \<bullet> \<alpha>')` have "bn(p \<bullet> \<alpha>') \<sharp>* P''" by simp
      moreover from `A\<^sub>P' \<sharp>* \<alpha>'` `x \<sharp> \<alpha>'` have "(x#A\<^sub>P') \<sharp>* \<alpha>'" by simp
      moreover from `A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')` `x \<sharp> \<alpha>'` S `x \<sharp> bn(p \<bullet> \<alpha>')` have "(x#A\<^sub>P') \<sharp>* (p \<bullet> \<alpha>')" 
	by(simp add: subject_eqvt[symmetric] bn_eqvt[symmetric] okject_eqvt[symmetric] fresh_chain_simps)
      moreover from `A\<^sub>P' \<sharp>* X` `x \<sharp> X` have "(x#A\<^sub>P') \<sharp>* X" by simp+
      moreover from `A\<^sub>P' \<sharp>* Y` `x \<sharp> Y` have "(x#A\<^sub>P') \<sharp>* Y" by simp+
      moreover from `A\<^sub>P' \<sharp>* Z` `x \<sharp> Z` have "(x#A\<^sub>P') \<sharp>* Z" by simp+
      moreover note `bn(p \<bullet> \<alpha>') \<sharp>* X` `bn(p \<bullet> \<alpha>') \<sharp>* Y` `bn(p \<bullet> \<alpha>') \<sharp>* Z`
      moreover from `distinct A\<^sub>P'` `x \<sharp> A\<^sub>P'` have "distinct(x#A\<^sub>P')" by simp
      ultimately show ?case by(rule_tac c_scope)
    next
      case(c_bang \<Psi> P \<pi> A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P' X Y Z)
      then obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"
                                  and Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                  and Peq_p': "(p \<bullet> (\<Psi>\<^sub>P \<otimes> \<one>)) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                                  and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                  and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                  and "distinct_perm p" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                  and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
	by(rule_tac c_bang) (assumption | simp (no_asm_use))+
      moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "(p \<bullet> \<Psi>\<^sub>P) \<simeq> (p \<bullet> \<one>)"
	by(simp add: Assertion_stat_eq_closed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<simeq> \<one>" by(simp add: perm_bottom)
      with Peq_p' have "(\<one> \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
	by(simp add: eqvts perm_bottom) (metis Identity Assertion_stat_eq_trans composition' Commutativity Associativity Assertion_stat_eq_sym)
      ultimately show ?case using c_bang
	apply(rule_tac c_bang(19)) by(assumption | simp)+ 
    qed
    
    with A have ?thesis by blast
  }
  moreover have "bn \<alpha> \<sharp>* ([]::name list)" and "bn \<alpha> \<sharp>* ([]::'b list)" and "bn \<alpha> \<sharp>* ([]::('a, 'b, 'c) psi list)"
           and  "A\<^sub>P \<sharp>* ([]::name list)" and "A\<^sub>P \<sharp>* ([]::'b list)" and "A\<^sub>P \<sharp>* ([]::('a, 'b, 'c) psi list)" 
    by simp+
  ultimately show ?thesis by blast
qed

lemma expand_tau_frame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b,'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"

  obtains \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"  and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "distinct A\<^sub>P'"
proof -
  assume A: "\<And>A\<^sub>P' \<Psi>\<^sub>P' \<Psi>'.
        \<lbrakk>extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>; \<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'; A\<^sub>P' \<sharp>* C; A\<^sub>P' \<sharp>* P'; distinct A\<^sub>P'\<rbrakk>
        \<Longrightarrow> thesis"

  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec>P'` `A\<^sub>P \<sharp>* P` have "A\<^sub>P \<sharp>* P'" by(rule tau_fresh_chain_derivative)

  {
    fix X :: "name list"
    and Y :: "'b list"
    and Z :: "('a, 'b, 'c) psi list"

    assume "A\<^sub>P \<sharp>* X"
    and    "A\<^sub>P \<sharp>* Y"
    and    "A\<^sub>P \<sharp>* Z"
    
    with assms `A\<^sub>P \<sharp>* P'` obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C"
                                               and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
    proof(nominal_induct avoiding: C X Y Z arbitrary: thesis rule: tau_frame_induct)
      case(c_alpha \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P p C X Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
	by metis

      have S: "set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P)" by fact

      from Fr_p' have "(p \<bullet> extract_frame P') = p \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" by simp
      with `A\<^sub>P \<sharp>* P'` `(p \<bullet> A\<^sub>P) \<sharp>* P'` S have "extract_frame P' = \<langle>(p \<bullet> A\<^sub>P'), (p \<bullet> \<Psi>\<^sub>P')\<rangle>" by(simp add: eqvts)
      moreover from `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'` have "(p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>')) \<simeq> (p \<bullet> \<Psi>\<^sub>P')" by(rule Assertion_stat_eq_closed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')" by(simp add: eqvts)
      moreover from `A\<^sub>P' \<sharp>* C` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> C)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* C` `(p \<bullet> A\<^sub>P) \<sharp>* C` S have "(p \<bullet> A\<^sub>P') \<sharp>* C" by simp
      moreover from `A\<^sub>P' \<sharp>* P'` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> P')" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* P'` `(p \<bullet> A\<^sub>P) \<sharp>* P'` S have "(p \<bullet> A\<^sub>P') \<sharp>* P'" by simp
      moreover from `A\<^sub>P' \<sharp>* X` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> X)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* X` `(p \<bullet> A\<^sub>P) \<sharp>* X` S have "(p \<bullet> A\<^sub>P') \<sharp>* X" by simp
      moreover from `A\<^sub>P' \<sharp>* Y` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Y)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* Y` `(p \<bullet> A\<^sub>P) \<sharp>* Y` S have "(p \<bullet> A\<^sub>P') \<sharp>* Y" by simp
      moreover from `A\<^sub>P' \<sharp>* Z` have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Z)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `A\<^sub>P \<sharp>* Z` `(p \<bullet> A\<^sub>P) \<sharp>* Z` S have "(p \<bullet> A\<^sub>P') \<sharp>* Z" by simp
      moreover from `distinct A\<^sub>P'` have "distinct(p \<bullet> A\<^sub>P')" by simp
      ultimately show ?case by(rule c_alpha)
    next
      case(c_case \<Psi> P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C B Y Z thesis)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'"
                                and "A\<^sub>P' \<sharp>* B" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
	by(rule_tac c_case) (assumption | simp (no_asm_use))+
      with `\<Psi>\<^sub>P \<simeq> \<one>` `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'` have "\<one> \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
	by(metis Identity Assertion_stat_eq_trans composition' Commutativity Associativity Assertion_stat_eq_sym)
      thus ?case using Fr_p' `A\<^sub>P' \<sharp>* P'` `A\<^sub>P' \<sharp>* C` `A\<^sub>P' \<sharp>* B` `A\<^sub>P' \<sharp>* Y` `A\<^sub>P' \<sharp>* Z` `distinct A\<^sub>P'` using c_case
	by force
    next
      case(c_par1 \<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C X Y Z)
      moreover from `A\<^sub>P \<sharp>* X` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* Y` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* Z`
      have "A\<^sub>P \<sharp>* (X@A\<^sub>Q)" and  "A\<^sub>P \<sharp>* (\<Psi>\<^sub>Q#Y)" and  "A\<^sub>P \<sharp>* (Q#Z)"
	by simp+
      ultimately obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'"
                                      and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" 
                                      and "A\<^sub>P' \<sharp>* (X@A\<^sub>Q)" and "A\<^sub>P' \<sharp>* (\<Psi>\<^sub>Q#Y)" and "A\<^sub>P' \<sharp>* (Q#Z)"
	by metis

      hence "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* Z"
	by simp+

      from `A\<^sub>P' \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* P'` Fr_p' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'" by(force dest: extract_frame_fresh_chain)
      with `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P' \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Fr_p'
      have "extract_frame(P' \<parallel> Q) = \<langle>(A\<^sub>P'@A\<^sub>Q), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp

      moreover from `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'`have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q" 
	by(metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym)

      moreover from `A\<^sub>P' \<sharp>* C` `A\<^sub>Q \<sharp>* C` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* C" by simp
      moreover from `A\<^sub>P' \<sharp>* P'` `A\<^sub>Q \<sharp>* P'` `A\<^sub>P' \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* (P' \<parallel> Q)" by simp
      moreover from `A\<^sub>P' \<sharp>* X` `A\<^sub>Q \<sharp>* X` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* X" by simp
      moreover from `A\<^sub>P' \<sharp>* Y` `A\<^sub>Q \<sharp>* Y` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Y" by simp
      moreover from `A\<^sub>P' \<sharp>* Z` `A\<^sub>Q \<sharp>* Z` have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Z" by simp
      moreover from `A\<^sub>P' \<sharp>* A\<^sub>Q` `distinct A\<^sub>P'` `distinct A\<^sub>Q` have "distinct(A\<^sub>P'@A\<^sub>Q)" by simp
      ultimately show ?case by(rule c_par1)
    next
      case(c_par2 \<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C X Y Z)
      moreover from `A\<^sub>Q \<sharp>* X` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* Y` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Z`
      have "A\<^sub>Q \<sharp>* (X@A\<^sub>P)" and  "A\<^sub>Q \<sharp>* (\<Psi>\<^sub>P#Y)" and  "A\<^sub>Q \<sharp>* (P#Z)"
	by(simp add: fresh_chain_simps)+
      ultimately obtain \<Psi>' A\<^sub>Q' \<Psi>\<^sub>Q' where Fr_q': "extract_frame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "distinct A\<^sub>Q'"
                                       and "\<Psi>\<^sub>Q \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>Q'"and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* Q'" 
                                       and "A\<^sub>Q' \<sharp>* (X@A\<^sub>P)" and "A\<^sub>Q' \<sharp>* (\<Psi>\<^sub>P#Y)" and "A\<^sub>Q' \<sharp>* (P#Z)"
	by metis

      hence "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* A\<^sub>P" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Z"
	by simp+

      from `A\<^sub>Q' \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* Q'` Fr_q' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'" by(force dest: extract_frame_fresh_chain)
      with `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q' \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` Fr_q'
      have "extract_frame(P \<parallel> Q') = \<langle>(A\<^sub>P@A\<^sub>Q'), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'\<rangle>" by simp

      moreover from `\<Psi>\<^sub>Q \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>Q'`have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'" 
	by(metis Associativity Commutativity Composition Assertion_stat_eq_trans Assertion_stat_eq_sym)
      moreover from `A\<^sub>P \<sharp>* C` `A\<^sub>Q' \<sharp>* C` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* C" by simp
      moreover from `A\<^sub>P \<sharp>* P` `A\<^sub>Q' \<sharp>* P` `A\<^sub>P \<sharp>* Q'` `A\<^sub>Q' \<sharp>* Q'` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* (P \<parallel> Q')" by simp
      moreover from `A\<^sub>P \<sharp>* X` `A\<^sub>Q' \<sharp>* X` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* X" by simp
      moreover from `A\<^sub>P \<sharp>* Y` `A\<^sub>Q' \<sharp>* Y` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from `A\<^sub>P \<sharp>* Z` `A\<^sub>Q' \<sharp>* Z` have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from `A\<^sub>Q' \<sharp>* A\<^sub>P` `distinct A\<^sub>P` `distinct A\<^sub>Q'` have "distinct(A\<^sub>P@A\<^sub>Q')" by simp
      ultimately show ?case by(rule c_par2)
    next
      case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec C X Y Z)
      have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" and Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact+
      from P_trans `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* M`
           `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* X` `A\<^sub>P \<sharp>* Y` `A\<^sub>P \<sharp>* Z` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* xvec`
      obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and Peq_p': "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* Q'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "distinct A\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* P'"
	by(rule_tac C="(Q', C, X, Y, Z, A\<^sub>Q, xvec)" and C'="(Q', C, X, Y, Z, A\<^sub>Q, xvec)" in expand_non_tau_frame) auto
      moreover from Q_trans  have "distinct xvec" by(auto dest: bound_output_distinct)
      from Q_trans `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* K` `distinct xvec`
           `A\<^sub>P' \<sharp>* A\<^sub>Q` `A\<^sub>P' \<sharp>* xvec` `A\<^sub>Q \<sharp>* Q` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `xvec \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* N` 
           `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* X` `A\<^sub>Q \<sharp>* Y` `A\<^sub>Q \<sharp>* Z` `xvec \<sharp>* P` `xvec \<sharp>* C` `xvec \<sharp>* X` `xvec \<sharp>* Y` `xvec \<sharp>* Z`
      obtain p \<Psi>'' A\<^sub>Q' \<Psi>\<^sub>Q' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and Qeq_q': "(p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>Q'" and Fr_q': "extract_frame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>"
                             and "A\<^sub>Q' \<sharp>* A\<^sub>P'" and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* N" and "distinct A\<^sub>Q'"
                             and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* X" and "(p \<bullet> xvec) \<sharp>* Y" and "(p \<bullet> xvec) \<sharp>* P"
                             and "(p \<bullet> xvec) \<sharp>* Z" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q'"and "(p \<bullet> xvec) \<sharp>* Q'"
                             and "distinct_perm p" and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* Q'"
	by(rule_tac C="(P, C, X, Y, Z, A\<^sub>P', \<Psi>\<^sub>P)" and C'="(P, C, X, Y, Z, A\<^sub>P', \<Psi>\<^sub>P)" in expand_non_tau_frame) (assumption | simp)+

      from P_trans `A\<^sub>Q' \<sharp>* P` `A\<^sub>Q' \<sharp>* N` `(p \<bullet> xvec) \<sharp>* P` `(p \<bullet> xvec) \<sharp>* N` 
      have "A\<^sub>Q' \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* P'" by(force dest: input_fresh_chain_derivative)+
      with Fr_p' `A\<^sub>Q' \<sharp>* A\<^sub>P'` `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'" by(force dest: extract_frame_fresh_chain)+
      from Fr_q' `A\<^sub>Q' \<sharp>* A\<^sub>P'` `A\<^sub>P' \<sharp>* Q'` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q'` `(p \<bullet> xvec) \<sharp>* Q'` have "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'"
	by(force dest: extract_frame_fresh_chain)+
      
      have "extract_frame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q'), (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')\<rangle>"
      proof -
	from Fr_p' Fr_q' `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'` `A\<^sub>Q' \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'` have "extract_frame(P' \<parallel> Q') = \<langle>(A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
	  by simp
	hence "extract_frame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>(xvec@A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
	  by(induct xvec) auto
	moreover from `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'` `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'` S 
	have "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> \<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert(\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q')))"
	  by(rule_tac frame_chain_alpha) (auto simp add: fresh_star_def frame_res_chain_fresh)
	hence "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert((p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q'))))"
	  using `A\<^sub>P' \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q'` S
	  by(force simp add: eqvts)
	ultimately show ?thesis
	  by(simp add: frame_chain_append)
      qed
	  
      moreover have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> ((p \<bullet> \<Psi>') \<otimes> (p \<bullet> \<Psi>'')) \<simeq> (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')"
      proof -
	have "(\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> (\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> ((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'')"
	  by(metis Associativity Commutativity Composition Assertion_stat_eq_trans)
	moreover from Peq_p' Qeq_q' have "(\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> ((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
	  by(metis Associativity Commutativity Composition Assertion_stat_eq_trans)
	ultimately have "(\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
	  by(metis Assertion_stat_eq_trans)
	hence "(p \<bullet> ((\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>''))) \<simeq> (p \<bullet> (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))"
	  by(rule Assertion_stat_eq_closed)
	with `xvec \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P` S `distinct_perm p` show ?thesis
	  by(simp add: eqvts)
      qed

      moreover from `(p \<bullet> xvec) \<sharp>* C` `A\<^sub>P' \<sharp>* C` `A\<^sub>Q' \<sharp>* C` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* C" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* X` `A\<^sub>P' \<sharp>* X` `A\<^sub>Q' \<sharp>* X` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* X" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* Y` `A\<^sub>P' \<sharp>* Y` `A\<^sub>Q' \<sharp>* Y` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* Z` `A\<^sub>P' \<sharp>* Z` `A\<^sub>Q' \<sharp>* Z` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* P'` `(p \<bullet> xvec) \<sharp>* Q'` `A\<^sub>P' \<sharp>* P'` `A\<^sub>P' \<sharp>* Q' ``A\<^sub>Q' \<sharp>* P'` `A\<^sub>Q' \<sharp>* Q'`
      have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))" by(auto simp add: res_chain_fresh fresh_star_def)
      moreover from `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* A\<^sub>P'` `distinct xvec` `distinct A\<^sub>P'` `distinct A\<^sub>Q'`
       have "distinct((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q')"
	 by auto (simp add: name_list_supp fresh_star_def fresh_def)+

      ultimately show ?case using c_comm1
	by metis
    next
      case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec C X Y Z)
      have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'" by fact+
      from P_trans have "distinct xvec" by(auto dest: bound_output_distinct)
      from P_trans `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `xvec \<sharp>* Q` `distinct xvec` `xvec \<sharp>* M`
                  `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* X` `A\<^sub>P \<sharp>* Y` `A\<^sub>P \<sharp>* Z` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* xvec` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N`
                  `xvec \<sharp>* P` `xvec \<sharp>* C` `xvec \<sharp>* X` `xvec \<sharp>* Y` `xvec \<sharp>* Z` `A\<^sub>Q \<sharp>* xvec` `xvec \<sharp>* \<Psi>\<^sub>Q`
      obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                           and Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and Peq_p': "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* N" and "A\<^sub>P' \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* Q"
                           and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                           and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* X" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" 
                           and "(p \<bullet> xvec) \<sharp>* Y" and "(p \<bullet> xvec) \<sharp>* Z" and "(p \<bullet> xvec) \<sharp>* P'" and "distinct_perm p"
        by(rule_tac C="(C, X, Y, Z, A\<^sub>Q, Q, \<Psi>\<^sub>Q)" and C'="(C, X, Y, Z, A\<^sub>Q, Q, \<Psi>\<^sub>Q)" in expand_non_tau_frame) (assumption | simp)+

      from Q_trans `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* P'` `(p \<bullet> xvec) \<sharp>* A\<^sub>Q`
           `A\<^sub>P' \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* C` `A\<^sub>Q \<sharp>* X` `A\<^sub>Q \<sharp>* Y` `A\<^sub>Q \<sharp>* Z` `A\<^sub>Q \<sharp>* N`  `A\<^sub>Q \<sharp>* K` 
      obtain \<Psi>'' A\<^sub>Q' \<Psi>\<^sub>Q' where Qeq_q': "\<Psi>\<^sub>Q \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>Q'" and Fr_q': "extract_frame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "distinct A\<^sub>Q'"
                             and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* Q'" and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* P'" and "A\<^sub>Q' \<sharp>* (p \<bullet> xvec)"
                             and "A\<^sub>Q' \<sharp>* A\<^sub>P'" and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* P"
	by(rule_tac C="(P, C, P', X, Y, Z, A\<^sub>P', xvec, (p \<bullet> xvec), \<Psi>\<^sub>P)" and C'="(P, C, P', X, Y, Z, A\<^sub>P', xvec, (p \<bullet> xvec), \<Psi>\<^sub>P)" in expand_non_tau_frame) (assumption | simp)+

      from Q_trans `A\<^sub>P' \<sharp>* Q` `A\<^sub>P' \<sharp>* N` `(p \<bullet> xvec) \<sharp>* Q` `(p \<bullet> xvec) \<sharp>* N` 
      have "A\<^sub>P' \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* Q'" by(force dest: input_fresh_chain_derivative)+
      with Fr_q' `A\<^sub>Q' \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* (p \<bullet> xvec)` have "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'" by(force dest: extract_frame_fresh_chain)+
      from Fr_p' `A\<^sub>Q' \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* P'` `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` `(p \<bullet> xvec) \<sharp>* P'` have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'"
	by(force dest: extract_frame_fresh_chain)+

      have "extract_frame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q'), (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')\<rangle>"
      proof -
	from Fr_p' Fr_q' `A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'` `A\<^sub>Q' \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'` have "extract_frame(P' \<parallel> Q') = \<langle>(A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
	  by simp
	hence "extract_frame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>(xvec@A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
	  by(induct xvec) auto
	moreover from `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'` `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'` S 
	have "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> \<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert(\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q')))"
	  by(rule_tac frame_chain_alpha) (auto simp add: fresh_star_def frame_res_chain_fresh)
	hence "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(F_assert((p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q'))))"
	  using `A\<^sub>P' \<sharp>* xvec` `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` `A\<^sub>Q' \<sharp>* xvec` `A\<^sub>Q' \<sharp>* (p \<bullet> xvec)` S
	  by(force simp add: eqvts)
	ultimately show ?thesis
	  by(simp add: frame_chain_append)
      qed
	  
      moreover have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> ((p \<bullet> \<Psi>') \<otimes> (p \<bullet> \<Psi>'')) \<simeq> (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')"
      proof -
	have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>'')"
	  by(metis Associativity Commutativity Composition Assertion_stat_eq_trans)
	moreover from Peq_p' Qeq_q' have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
	  by(metis Associativity Commutativity Composition Assertion_stat_eq_trans)
	ultimately have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
	  by(metis Assertion_stat_eq_trans)
	hence "(p \<bullet> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'')) \<simeq> (p \<bullet> (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))"
	  by(rule Assertion_stat_eq_closed)
	with `xvec \<sharp>* \<Psi>\<^sub>Q` `(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q` S `distinct_perm p` show ?thesis
	  by(simp add: eqvts)
      qed

      moreover from `(p \<bullet> xvec) \<sharp>* C` `A\<^sub>P' \<sharp>* C` `A\<^sub>Q' \<sharp>* C` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* C" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* X` `A\<^sub>P' \<sharp>* X` `A\<^sub>Q' \<sharp>* X` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* X" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* Y` `A\<^sub>P' \<sharp>* Y` `A\<^sub>Q' \<sharp>* Y` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* Z` `A\<^sub>P' \<sharp>* Z` `A\<^sub>Q' \<sharp>* Z` have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from `(p \<bullet> xvec) \<sharp>* P'` `(p \<bullet> xvec) \<sharp>* Q'` `A\<^sub>P' \<sharp>* P'` `A\<^sub>P' \<sharp>* Q' ``A\<^sub>Q' \<sharp>* P'` `A\<^sub>Q' \<sharp>* Q'`
      have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))" by(auto simp add: res_chain_fresh fresh_star_def)
      moreover from `(p \<bullet> xvec) \<sharp>* A\<^sub>P'` ` A\<^sub>Q' \<sharp>* (p \<bullet> xvec)` `A\<^sub>Q' \<sharp>* A\<^sub>P'` `distinct xvec` `distinct A\<^sub>P'` `distinct A\<^sub>Q'`
       have "distinct((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q')"
	 by auto (simp add: name_list_supp fresh_star_def fresh_def)+

      ultimately show ?case using c_comm2 by metis
    next
      case(c_scope \<Psi> P P' x A\<^sub>P \<Psi>\<^sub>P C X Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'"
                                and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'"
                                and "A\<^sub>P' \<sharp>* (x#X)" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" 
	by(rule_tac c_scope(4)[where ba="x#X"]) auto
      from `A\<^sub>P' \<sharp>* (x#X)` have "x \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      moreover from Fr_p' have "extract_frame(\<lparr>\<nu>x\<rparr>P') = \<langle>(x#A\<^sub>P'), \<Psi>\<^sub>P'\<rangle>" by simp
      moreover note `\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'`
      moreover from `x \<sharp> C` `A\<^sub>P' \<sharp>* C` have "(x#A\<^sub>P') \<sharp>* C" by simp
      moreover from  `A\<^sub>P' \<sharp>* P'` have "(x#A\<^sub>P') \<sharp>* (\<lparr>\<nu>x\<rparr>P')" by(simp add: abs_fresh fresh_star_def)
      moreover from `x \<sharp> X` `A\<^sub>P' \<sharp>* X` have "(x#A\<^sub>P') \<sharp>* X" by simp
      moreover from `x \<sharp> Y` `A\<^sub>P' \<sharp>* Y` have "(x#A\<^sub>P') \<sharp>* Y" by simp
      moreover from `x \<sharp> Z` `A\<^sub>P' \<sharp>* Z` have "(x#A\<^sub>P') \<sharp>* Z" by simp
      moreover from `x \<sharp> A\<^sub>P'` `distinct A\<^sub>P'` have "distinct(x#A\<^sub>P')" by simp
      ultimately show ?case by(rule_tac c_scope)
    next
      case(c_bang \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P C B Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Fr_p': "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                and "(\<Psi>\<^sub>P \<otimes> \<one>) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* B" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
	by(rule_tac c_bang) (assumption | simp)+
      with `\<Psi>\<^sub>P \<simeq> \<one>` `(\<Psi>\<^sub>P \<otimes> \<one>) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'` have "\<one> \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
	by(metis Identity Assertion_stat_eq_trans composition' Commutativity Associativity Assertion_stat_eq_sym)
      thus ?case using Fr_p' `A\<^sub>P' \<sharp>* P'` `A\<^sub>P' \<sharp>* C` `A\<^sub>P' \<sharp>* B` `A\<^sub>P' \<sharp>* Y` `A\<^sub>P' \<sharp>* Z` `distinct A\<^sub>P'`
	by(rule_tac c_bang)
    qed
    with A have ?thesis by simp
  }
  moreover have "A\<^sub>P \<sharp>* ([]::name list)" and "A\<^sub>P \<sharp>* ([]::'b list)" and "A\<^sub>P \<sharp>* ([]::('a, 'b, 'c) psi list)" by simp+
  ultimately show ?thesis by blast
qed

lemma expand_frame:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   C    :: "'d::fs_name"
  and   C'   :: "'e::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"
  and     "A\<^sub>P \<sharp>* C'"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* C'"

  obtains p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct_perm p" and
                              "extract_frame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" and
                              "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'" and "distinct A\<^sub>P'"
using assms
apply(cases "\<alpha>=\<tau>")
by(auto intro: expand_tau_frame[where C=C] expand_non_tau_frame[where C=C and C'=C'])

abbreviation
  frame_imp_judge ("_ \<hookrightarrow>\<^sub>F _" [80, 80] 80)
  where "F \<hookrightarrow>\<^sub>F G \<equiv> Frame_stat_imp F G"

lemma Frame_stat_eq_imp_compose:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   H :: "'b frame"
  and   I :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"
  and     "G \<hookrightarrow>\<^sub>F H"
  and     "H \<simeq>\<^sub>F I"

  shows "F \<hookrightarrow>\<^sub>F I"
using assms
by(auto simp add: Frame_stat_eq_def) (blast intro: Frame_stat_imp_trans)

lemma transfer_non_tau_frame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct(bn \<alpha>)"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>F \<sharp>* subject \<alpha>"
  and     "A\<^sub>G \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"
  and     "\<alpha> \<noteq> \<tau>"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
using assms
proof(nominal_induct \<Psi>\<^sub>F P \<pi> Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P D=="()" avoiding: \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G rule: semantics_frame_induct)
  case(c_alpha \<Psi>\<^sub>F P A\<^sub>P \<Psi>\<^sub>P \<pi> p \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>`
  have "(p \<bullet> (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>)) \<hookrightarrow>\<^sub>F (p \<bullet> (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>))"
    by(rule Frame_stat_imp_closed)
  with `A\<^sub>P \<sharp>* A\<^sub>F` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* \<Psi>\<^sub>F` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>G`
    `distinct_perm p` `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  with c_alpha show ?case by force
next
  case(c_input \<Psi>\<^sub>F M K xvec N Tvec P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from c_input have "A\<^sub>F \<sharp>* K" and "A\<^sub>G \<sharp>* K" by(auto simp add: residual_inject)

  from `A\<^sub>F \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)` `A\<^sub>G \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)` have "A\<^sub>F \<sharp>* M" and "A\<^sub>G \<sharp>* M" by simp+
  from `\<Psi>\<^sub>F \<turnstile> K \<leftrightarrow> M`
  have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> K \<leftrightarrow> M"
    by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
  with `A\<^sub>F \<sharp>* M` `A\<^sub>F \<sharp>* K`
  have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F K \<leftrightarrow> M"
    by(force intro: frame_impI)
  with `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F K \<leftrightarrow> M"
    by(simp add: Frame_stat_eq_def Frame_stat_imp_def)
  with `A\<^sub>G \<sharp>* M` `A\<^sub>G \<sharp>* K`
  have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> K \<leftrightarrow> M" by(force dest: frame_impE)
  hence "\<Psi>\<^sub>G \<turnstile> K \<leftrightarrow> M" by(blast intro: stat_eq_ent Identity)
  thus ?case using `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec` using c_input Input
    by(force simp add: residual_inject)
next
  case(c_output \<Psi>\<^sub>F M K N P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from c_output have "A\<^sub>F \<sharp>* K" and "A\<^sub>G \<sharp>* K" by(auto simp add: residual_inject)

  from `A\<^sub>F \<sharp>* (M\<langle>N\<rangle>.P)` `A\<^sub>G \<sharp>* (M\<langle>N\<rangle>.P)` have "A\<^sub>F \<sharp>* M" and "A\<^sub>G \<sharp>* M" by simp+
  from `\<Psi>\<^sub>F \<turnstile> M \<leftrightarrow> K`
  have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
  with `A\<^sub>F \<sharp>* M` `A\<^sub>F \<sharp>* K`
  have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(force intro: frame_impI)
  with `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(simp add: Frame_stat_imp_def) 
  with `A\<^sub>G \<sharp>* M` `A\<^sub>G \<sharp>* K`
  have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" by(force dest: frame_impE)
  hence "\<Psi>\<^sub>G \<turnstile> M \<leftrightarrow> K" by(blast intro: stat_eq_ent Identity) 
  thus ?case using c_output Output by(force simp add: residual_inject) 
next
  case(c_case \<Psi>\<^sub>F P \<pi> \<phi> Cs A\<^sub>P \<Psi>\<^sub>P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans Assertion_stat_eq_sym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover have "A\<^sub>F \<sharp>* (\<phi>,P)"  "A\<^sub>G \<sharp>* (\<phi>,P)"
    using `A\<^sub>F \<sharp>* (Cases Cs)`  `(\<phi>, P) mem Cs` `A\<^sub>G \<sharp>* (Cases Cs)`
    by(drule_tac mem_fresh_chain,force,force)+
  moreover note c_case
  ultimately have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by auto
  moreover note `(\<phi>, P) mem Cs` 
  moreover from `A\<^sub>F \<sharp>* (\<phi>,P)` `A\<^sub>G \<sharp>* (\<phi>,P)` have "A\<^sub>F \<sharp>* \<phi>" and "A\<^sub>G \<sharp>* \<phi>"
    by auto
  from `\<Psi>\<^sub>F \<turnstile> \<phi>` have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
  with `A\<^sub>F \<sharp>* \<phi>` have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frame_impI)
  with `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>` have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
    by(simp add: Frame_stat_imp_def)
  with `A\<^sub>G \<sharp>* \<phi>` have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> \<phi>" by(force dest: frame_impE)
  hence "\<Psi>\<^sub>G \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity)
  ultimately show ?case using `guarded P` c_case Case by(force intro: residual_inject)
next
  case(c_par1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P \<pi> \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P \<alpha>' PQ' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `A\<^sub>F \<sharp>* (P \<parallel> Q)` `A\<^sub>G \<sharp>* (P \<parallel> Q)` have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>`
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
    by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover from `A\<^sub>F \<sharp>* Q` `A\<^sub>G \<sharp>* Q` FrQ `A\<^sub>Q \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>G` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain)+
  moreover note `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` `A\<^sub>F \<sharp>* subject \<alpha>'` `A\<^sub>G \<sharp>* subject \<alpha>'` `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G`
  moreover from `\<alpha> \<prec> P' \<parallel> Q = \<alpha>' \<prec> PQ'` `bn \<alpha> \<sharp>* \<alpha>'` 
  obtain p P'' where "\<alpha> \<prec> P' = \<alpha>' \<prec> P''" and "set p \<subseteq> set(bn \<alpha>') \<times> set(bn \<alpha>)" and "PQ' = P'' \<parallel> (p \<bullet> Q)"
    apply(drule_tac sym)
    by(rule_tac action_par1_dest) (assumption | simp | blast dest: sym)+
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'" using `\<alpha>' \<noteq> \<tau>` by(force intro: c_par1)
  thus ?case using FrQ `(bn \<alpha>) \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>G` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>` using c_par1
    by(metis Par1)
next
  case(c_par2 \<Psi>\<^sub>F \<Psi>\<^sub>P Q \<pi> \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q \<alpha>' PQ' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `A\<^sub>F \<sharp>* (P \<parallel> Q)` `A\<^sub>G \<sharp>* (P \<parallel> Q)` have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity frame_res_chain_pres frame_nil_stat_eq)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>`
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
    by(metis Associativity Assertion_stat_eq_sym frame_res_chain_pres frame_nil_stat_eq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover from `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)+
  moreover note `A\<^sub>F \<sharp>* Q` `A\<^sub>G \<sharp>* Q` `A\<^sub>F \<sharp>* subject \<alpha>'` `A\<^sub>G \<sharp>* subject \<alpha>'` `A\<^sub>Q \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>F` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>G`
  moreover from `\<alpha> \<prec> P \<parallel> Q' = \<alpha>' \<prec> PQ'` `bn \<alpha> \<sharp>* \<alpha>'` 
  obtain p Q'' where "\<alpha> \<prec> Q' = \<alpha>' \<prec> Q''" and "set p \<subseteq> set(bn \<alpha>') \<times> set(bn \<alpha>)" and "PQ' = (p \<bullet> P) \<parallel> Q''"
    apply(drule_tac sym)
    by(rule_tac action_par2_dest) (assumption | simp | blast dest: sym)+
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'" using `\<alpha>' \<noteq> \<tau>` by(force intro: c_par2)
  thus ?case using FrP `(bn \<alpha>) \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` using c_par2
    by(metis Par2)
next
  case c_comm1
  thus ?case by(simp add: residual_inject)
next
  case c_comm2
  thus ?case by(simp add: residual_inject)
next
  case(c_open \<Psi>\<^sub>F P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P \<alpha> P'' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `M\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''` `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> \<alpha>` `x \<sharp> P''` `distinct(bn \<alpha>)`
  obtain xvec' x' yvec' N' where "M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P' =  M\<lparr>\<nu>*(xvec'@yvec')\<rparr>\<langle>([(x, x')] \<bullet> N')\<rangle> \<prec> ([(x, x')] \<bullet> P'')" 
                             and "\<alpha> = M\<lparr>\<nu>*(xvec'@x'#yvec')\<rparr>\<langle>N'\<rangle>"
    apply(cases rule: action_cases[where \<alpha>=\<alpha>])
    apply(auto simp add: residual_inject)
    by(rule bound_output_open_dest) blast+

  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>Some \<pi> @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" using c_open
    by(rule_tac c_open) (assumption | simp)+
  with `x \<in> supp N` `x \<sharp> \<Psi>\<^sub>G` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec`
  have "\<Psi>\<^sub>G \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>Some(\<lparr>\<nu>x\<rparr>\<pi>) @ M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" 
    by(rule_tac Open)
  thus ?case using `\<alpha> = M\<lparr>\<nu>*(xvec'@x'#yvec')\<rparr>\<langle>N'\<rangle>` `M\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
    by simp
next
  case(c_scope \<Psi>\<^sub>F P \<pi> \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P \<alpha>' xP \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P' = \<alpha>' \<prec> xP` `x \<sharp> \<alpha>` `x \<sharp> \<alpha>'` obtain P'' where "xP = \<lparr>\<nu>x\<rparr>P''" and "\<alpha> \<prec> P' = \<alpha>' \<prec> P''"
    by(drule_tac sym) (force intro: action_scope_dest)
  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'" using c_scope by auto
  with `x \<sharp> \<Psi>\<^sub>G` `x \<sharp> \<alpha>'` `\<alpha> \<prec> P' = \<alpha>' \<prec> P''` `xP = \<lparr>\<nu>x\<rparr>P''` show ?case
    by(metis Scope)
next
  case(c_bang \<Psi>\<^sub>F P \<pi> A\<^sub>P \<Psi>\<^sub>P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans Assertion_stat_eq_sym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  with c_bang have "\<Psi>\<^sub>G \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'" by force
  thus ?case using `guarded P` using c_bang by(metis Bang)
qed

lemma transfer_tau_frame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
proof -
  have \<pi> : "\<pi> = None"
    by(simp add: tau_no_provenance[OF `\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'`])
from assms show ?thesis
proof(nominal_induct avoiding: \<Psi>\<^sub>G A\<^sub>F A\<^sub>G rule: tau_frame_induct)
  case(c_alpha \<Psi>\<^sub>F P P' A\<^sub>P \<Psi>\<^sub>P p \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>`
  have "(p \<bullet> (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>)) \<hookrightarrow>\<^sub>F (p \<bullet> (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>))"
    by(rule Frame_stat_imp_closed)
  with `A\<^sub>P \<sharp>* A\<^sub>F` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* \<Psi>\<^sub>F` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` `(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G` `(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>G`
    `distinct_perm p` `set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  with c_alpha show ?case by blast
next
  case(c_case \<Psi>\<^sub>F P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans Assertion_stat_eq_sym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover from `A\<^sub>F \<sharp>* (Cases Cs)``A\<^sub>G \<sharp>* (Cases Cs)` `(\<phi>, P) mem Cs` have "A\<^sub>F \<sharp>* (\<phi>,P)" and "A\<^sub>G \<sharp>* (\<phi>,P)"
      by(rule_tac mem_fresh_chain,simp,simp)+
  moreover note c_case
  ultimately have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'" by force
  moreover note `(\<phi>, P) mem Cs` 
  moreover from `A\<^sub>F \<sharp>* (\<phi>,P)` and `A\<^sub>G \<sharp>* (\<phi>,P)`
  have "A\<^sub>F \<sharp>* \<phi>" and "A\<^sub>G \<sharp>* \<phi>"
      by simp+
  from `\<Psi>\<^sub>F \<turnstile> \<phi>` have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
  with `A\<^sub>F \<sharp>* \<phi>` have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frame_impI)
  with `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>` have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
    by(simp add: Frame_stat_imp_def)
  with `A\<^sub>G \<sharp>* \<phi>` have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> \<phi>" by(force dest: frame_impE)
  hence "\<Psi>\<^sub>G \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity)
  ultimately show ?case using `guarded P`
    by(auto dest: Case simp add: \<pi>)
next
  case(c_par1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `A\<^sub>F \<sharp>* (P \<parallel> Q)` `A\<^sub>G \<sharp>* (P \<parallel> Q)` have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have IH: "\<And>\<Psi> A\<^sub>F A\<^sub>G. \<lbrakk>\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>P\<rangle>; A\<^sub>F \<sharp>* P; A\<^sub>G \<sharp>* P;
                           A\<^sub>P \<sharp>* A\<^sub>F; A\<^sub>P \<sharp>* A\<^sub>G; A\<^sub>P \<sharp>* (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q); A\<^sub>P \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'"
    by fact
  have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>`
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
    by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover from `A\<^sub>F \<sharp>* Q` `A\<^sub>G \<sharp>* Q` FrQ `A\<^sub>Q \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>G` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain)+
  moreover note `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>F` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* \<Psi>\<^sub>G`
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'" by(rule_tac IH) blast+
  thus ?case using FrQ `A\<^sub>Q \<sharp>* \<Psi>\<^sub>G` `A\<^sub>Q \<sharp>* P`
    by(auto dest: Par1 simp add: \<pi>)
next
  case(c_par2 \<Psi>\<^sub>F \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `A\<^sub>F \<sharp>* (P \<parallel> Q)` `A\<^sub>G \<sharp>* (P \<parallel> Q)` have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have IH: "\<And>\<Psi> A\<^sub>F A\<^sub>G. \<lbrakk>\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle>; A\<^sub>F \<sharp>* Q; A\<^sub>G \<sharp>* Q;
                           A\<^sub>Q \<sharp>* A\<^sub>F; A\<^sub>Q \<sharp>* A\<^sub>G; A\<^sub>Q \<sharp>* (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P); A\<^sub>Q \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> Q \<longmapsto>\<pi> @ \<tau> \<prec> Q'"
    by fact
  have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity frame_res_chain_pres frame_nil_stat_eq)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>`
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
    by(metis Associativity Assertion_stat_eq_sym frame_res_chain_pres frame_nil_stat_eq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  moreover from `A\<^sub>F \<sharp>* P` `A\<^sub>G \<sharp>* P` FrP `A\<^sub>P \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>G` have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)+
  moreover note `A\<^sub>F \<sharp>* Q` `A\<^sub>G \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>F` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>G`
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<tau> \<prec> Q'" by(rule_tac IH) blast+
  thus ?case using FrP `A\<^sub>P \<sharp>* \<Psi>\<^sub>G` `A\<^sub>P \<sharp>* Q`
    by(auto dest: Par2 simp add: \<pi>)
next
  case(c_comm1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q yvec zvec \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  moreover have FimpG: "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
  proof -
    have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    ultimately show ?thesis using FimpG
      by(rule_tac Frame_stat_eq_imp_compose)
  qed
  moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
  proof -
    have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    ultimately show ?thesis using FimpG
      by(metis Frame_stat_eq_def Frame_stat_imp_trans frame_int_associativity)
  qed
  moreover have "A\<^sub>F \<sharp>* M"
    using `A\<^sub>F \<sharp>* (P\<parallel>Q)` `zvec \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>F`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  moreover have "A\<^sub>G \<sharp>* M"
    using `A\<^sub>G \<sharp>* (P\<parallel>Q)` `zvec \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* A\<^sub>G`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  moreover have "A\<^sub>G \<sharp>* K"
    using `A\<^sub>G \<sharp>* (P\<parallel>Q)` `yvec \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* A\<^sub>G`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  moreover have "A\<^sub>F \<sharp>* K"
    using `A\<^sub>F \<sharp>* (P\<parallel>Q)` `yvec \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>F`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  ultimately show ?case unfolding \<pi>
    by(force intro: Comm1 transfer_non_tau_frame)
next
  case(c_comm2 \<Psi>\<^sub>F \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q yvec zvec \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  moreover have FimpG: "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
  proof -
    have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    ultimately show ?thesis using FimpG
      by(rule_tac Frame_stat_eq_imp_compose)
  qed
  moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
  proof -
    have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
      by(metis Associativity Composition Assertion_stat_eq_sym Assertion_stat_eq_trans Commutativity frame_res_chain_pres frame_nil_stat_eq)
    ultimately show ?thesis using FimpG
      by(metis Frame_stat_eq_def Frame_stat_imp_trans frame_int_associativity)
  qed
  moreover have "A\<^sub>F \<sharp>* M"
    using `A\<^sub>F \<sharp>* (P\<parallel>Q)` `zvec \<sharp>* A\<^sub>F` `A\<^sub>Q \<sharp>* A\<^sub>F`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  moreover have "A\<^sub>G \<sharp>* M"
    using `A\<^sub>G \<sharp>* (P\<parallel>Q)` `zvec \<sharp>* A\<^sub>G` `A\<^sub>Q \<sharp>* A\<^sub>G`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  moreover have "A\<^sub>G \<sharp>* K"
    using `A\<^sub>G \<sharp>* (P\<parallel>Q)` `yvec \<sharp>* A\<^sub>G` `A\<^sub>P \<sharp>* A\<^sub>G`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  moreover have "A\<^sub>F \<sharp>* K"
    using `A\<^sub>F \<sharp>* (P\<parallel>Q)` `yvec \<sharp>* A\<^sub>F` `A\<^sub>P \<sharp>* A\<^sub>F`
      `\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  ultimately show ?case unfolding \<pi>
    by(force intro: Comm2 transfer_non_tau_frame)
next
  case(c_scope \<Psi>\<^sub>F P P' x A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<tau> \<prec> P'" by auto
  with `x \<sharp> \<Psi>\<^sub>G` show ?case unfolding \<pi>
    by(auto dest: Scope)
next
  case(c_bang \<Psi>\<^sub>F P P' A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans)
  moreover note `\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>`
  moreover from `\<Psi>\<^sub>P \<simeq> \<one>` have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(metis frame_int_composition_sym Identity Assertion_stat_eq_trans Assertion_stat_eq_sym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(rule Frame_stat_eq_imp_compose)
  with c_bang have "\<Psi>\<^sub>G \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ \<tau> \<prec> P'" by force
  thus ?case unfolding \<pi> using `guarded P` by(auto dest: Bang)
qed
qed

lemma transfer_frame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>F \<sharp>* subject \<alpha>"
  and     "A\<^sub>G \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
using assms
proof -
  from `\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "distinct(bn \<alpha>)" by(auto dest: bound_output_distinct)
  thus ?thesis using assms
    by(cases "\<alpha> = \<tau>") (auto intro: transfer_non_tau_frame transfer_tau_frame)
qed

lemma par_cases_input_frame[consumes 7, case_names c_par1 c_par2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ M\<lparr>N\<rparr> \<prec> T"
  and     "extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P\<^sub>Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>P\<^sub>Q \<sharp>* P"
  and     "A\<^sub>P\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* M"
  and     r_par1: "\<And>\<pi> P' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     r_par2: "\<And>\<pi> Q' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop T"
using Trans
proof(induct rule: par_input_cases[of _ _ _ _ _ _ _ "(A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)"])
  case(c_par1 \<pi> P' A\<^sub>Q \<Psi>\<^sub>Q)
  from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` `A\<^sub>P\<^sub>Q \<sharp>* P`
  have "A\<^sub>P\<^sub>Q \<sharp>* \<pi>" by(auto intro: trans_fresh_provenance)
  from `A\<^sub>Q \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)` have "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, M, A\<^sub>Q, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>Q,\<pi>)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<pi>"
    by simp+

  have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'" 
    by(rule_tac input_perm_frame) auto
  with S `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extract_frame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` Aeq have "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extract_frame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` Aeq have "extract_frame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover have "(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>" "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>"
    using Aeq `A\<^sub>P\<^sub>Q \<sharp>* \<pi>` by simp_all
  moreover from `c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q`
  have "c\<pi> = append_at_end_prov_option \<pi> (p\<bullet>A\<^sub>Q)"
    using `A\<^sub>Q \<sharp>* \<pi>` `(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>`
    by(metis append_at_end_prov_option_eq_fresh length_closed)
  ultimately show ?case using `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` Aeq \<Psi>eq
    by(rule_tac r_par1) (assumption | simp)+
next
  case(c_par2 \<pi> Q' A\<^sub>P \<Psi>\<^sub>P)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> Q'` `A\<^sub>P\<^sub>Q \<sharp>* Q`
  have "A\<^sub>P\<^sub>Q \<sharp>* \<pi>" by(auto intro: trans_fresh_provenance)  
  from `A\<^sub>P \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)` have "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, M, A\<^sub>P, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P)"
    by(rule fresh_frame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain) 

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'` S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'" 
    by(rule_tac input_perm_frame) auto
  with S `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> Q'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extract_frame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` Aeq have "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extract_frame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` Aeq have "extract_frame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from `A\<^sub>Q \<sharp>* A\<^sub>P` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover have "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>" "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>"
    using Aeq `A\<^sub>P\<^sub>Q \<sharp>* \<pi>` by simp_all  
  moreover from `c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P`
  have "c\<pi> = append_at_front_prov_option \<pi> (p\<bullet>A\<^sub>P)"
    using `A\<^sub>P \<sharp>* \<pi>` `(p\<bullet>A\<^sub>P) \<sharp>* \<pi>`
    by(metis append_at_front_prov_option_eq_fresh length_closed)
  ultimately show ?case using `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` Aeq \<Psi>eq
    by(rule_tac r_par2) (assumption | simp)+
qed

lemma par_cases_output_frame[consumes 11, case_names c_par1 c_par2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>c\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> T"
  and     "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* Q"
  and     "xvec \<sharp>* M"
  and     "extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P\<^sub>Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>P\<^sub>Q \<sharp>* P"
  and     "A\<^sub>P\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* M"
  and     r_par1: "\<And>\<pi> P' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     r_par2: "\<And>\<pi> Q' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop T"
using Trans `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* Q` `xvec \<sharp>* M`
proof(induct rule: par_output_cases[of _ _ _ _ _ _ _ _ "(A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)"])
  case(c_par1 \<pi> P' A\<^sub>Q \<Psi>\<^sub>Q)
  from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `A\<^sub>P\<^sub>Q \<sharp>* P`
  have "A\<^sub>P\<^sub>Q \<sharp>* \<pi>" by(auto intro: trans_fresh_provenance)  
  from `A\<^sub>Q \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)` have "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, M, A\<^sub>Q, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>Q)"
    by(rule fresh_frame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by simp+

  have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q` FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extract_frame_fresh_chain)

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>P \<sharp>* A\<^sub>Q` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" 
    by(rule_tac output_perm_frame) (assumption | simp)+

  with S `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extract_frame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` Aeq have "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extract_frame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` Aeq have "extract_frame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover have "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>" "(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>"
    using Aeq `A\<^sub>P\<^sub>Q \<sharp>* \<pi>` by simp_all  
  moreover from `c\<pi> = append_at_end_prov_option \<pi> A\<^sub>Q`
  have "c\<pi> = append_at_end_prov_option \<pi> (p\<bullet>A\<^sub>Q)"
    using `A\<^sub>Q \<sharp>* \<pi>` `(p\<bullet>A\<^sub>Q) \<sharp>* \<pi>`
    by(metis append_at_end_prov_option_eq_fresh length_closed)
  ultimately show ?case using `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` Aeq \<Psi>eq
    by(rule_tac r_par1) (assumption | simp)+
next
  case(c_par2 \<pi> Q' A\<^sub>P \<Psi>\<^sub>P)
  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^sub>P\<^sub>Q \<sharp>* Q`
  have "A\<^sub>P\<^sub>Q \<sharp>* \<pi>" by(auto intro: trans_fresh_provenance)    
  from `A\<^sub>P \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)` have "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, M, A\<^sub>P, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P)"
    by(rule fresh_frame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extract_frame_fresh_chain) 

  from `extract_frame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>` FrP FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinct_perm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using `A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q` `distinct A\<^sub>P\<^sub>Q`
    by(rule_tac frame_chain_eq') (assumption | simp add: eqvts)+

  from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" 
    by(rule_tac output_perm_frame) (assumption | simp)+
  with S `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extract_frame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` Aeq have "extract_frame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extract_frame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` Aeq have "extract_frame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from `distinct A\<^sub>P` `distinct A\<^sub>Q` have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from `A\<^sub>Q \<sharp>* A\<^sub>P` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover have "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>" "(p\<bullet>A\<^sub>P) \<sharp>* \<pi>"
    using Aeq `A\<^sub>P\<^sub>Q \<sharp>* \<pi>` by simp_all  
  moreover from `c\<pi> = append_at_front_prov_option \<pi> A\<^sub>P`
  have "c\<pi> = append_at_front_prov_option \<pi> (p\<bullet>A\<^sub>P)"
    using `A\<^sub>P \<sharp>* \<pi>` `(p\<bullet>A\<^sub>P) \<sharp>* \<pi>`
    by(metis append_at_front_prov_option_eq_fresh length_closed)  
  ultimately show ?case using `A\<^sub>P\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P\<^sub>Q \<sharp>* P` `A\<^sub>P\<^sub>Q \<sharp>* Q` `A\<^sub>P\<^sub>Q \<sharp>* M` Aeq \<Psi>eq
    by(rule_tac r_par2) (assumption | simp)+
qed

inductive bang_pred :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
where
  aux1: "bang_pred P (!P)"
  | aux2: "bang_pred P (P \<parallel> !P)"

lemma append_at_end_prov_nil[simp]:
  shows "append_at_end_prov \<pi> [] = \<pi>"
  by(nominal_induct \<pi> rule: frame.strong_induct) auto

lemma bang_induct[consumes 1, case_names c_par1 c_par2 c_comm1 c_comm2 c_bang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> ('a, 'b, 'c) residual \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto> \<pi> @ Rs"
  and     r_par1: "\<And>\<pi> \<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) \<pi> (\<alpha> \<prec> (P' \<parallel> !P))"
  and     r_par2: "\<And>\<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; distinct A\<^sub>P; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; guarded P;
                             \<And>C. Prop C \<Psi> (!P) \<pi> (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> P'))"
  and     r_comm1: "\<And>M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''); extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''
\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_comm2: "\<And>M xvec N P' K A\<^sub>P \<Psi>\<^sub>P  yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>N\<rparr> \<prec> P''); extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_bang: "\<And>\<pi> Rs C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> Rs; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) Rs"
  shows "Prop C \<Psi> (!P) \<pi> Rs"
proof -
  from `\<Psi> \<rhd> !P \<longmapsto> \<pi> @ Rs` have "guarded P"
    by(nominal_induct \<Psi> P=="!P" \<pi> Rs rule: semantics.strong_induct) (auto simp add: psi.inject)
  {
    fix Q  :: "('a, 'b, 'c) psi"
    and \<Psi>' :: 'b

    assume "\<Psi>' \<rhd> Q \<longmapsto> \<pi> @ Rs"
    and    "guarded Q"
    and    "bang_pred P Q"
    and    "\<Psi> \<simeq> \<Psi>'"

    hence "Prop C \<Psi> Q \<pi> Rs" using r_par1 r_par1 r_par2 r_par2 r_comm1 r_comm2 r_bang
    proof(nominal_induct avoiding: \<Psi> C rule: semantics.strong_induct)
      case(c_input \<Psi>' M K xvec N Tvec Q \<Psi> C)
      thus ?case by - (ind_cases "bang_pred P (K\<lparr>\<lambda>*xvec N\<rparr>.Q)")
    next
      case(Output \<Psi>' M K N Q \<Psi> C)
      thus ?case by - (ind_cases "bang_pred P (M\<langle>N\<rangle>.Q)")
    next
      case(Case \<Psi>' Q \<pi> Rs \<phi> Cs \<Psi> C)
      thus ?case by - (ind_cases "bang_pred P (Cases Cs)")
    next
      case(c_par1 \<Psi>' \<Psi>\<^sub>R Q \<pi> \<alpha> P' R A\<^sub>R \<Psi> C)
      have r_par1: "\<And>\<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) \<pi> (\<alpha> \<prec> (P' \<parallel> !P))"
	by fact
      from `bang_pred P (Q \<parallel> R)` have "Q = P" and "R = !P"
	by - (ind_cases "bang_pred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from `R = !P` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from `\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `Q = P` `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>R = \<one>` have "\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
	by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
      hence "Prop C \<Psi> (P \<parallel> !P) \<pi> (\<alpha> \<prec> (P' \<parallel> !P))" using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha>  \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `Q = P` `distinct(bn \<alpha>)`
	by(rule_tac r_par1) auto
      with `R = !P` `Q = P` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` show ?case
        by(auto simp add: option.map_ident)
    next
      case(c_par2 \<Psi>' \<Psi>\<^sub>P R \<pi> \<alpha> P' Q A\<^sub>P \<Psi> C)
      have r_par2: "\<And>\<alpha> P' A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; distinct A\<^sub>P; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; guarded P; \<And>C. Prop C \<Psi> (!P) \<pi> (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> P'))"
        by fact
      from `bang_pred P (Q \<parallel> R)` have "Q = P" and "R = !P"
	by - (ind_cases "bang_pred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from `Q = P` `extract_frame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `guarded P` have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
	by(blast dest: guarded_stat_eq)+
      from `\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `R = !P` `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
	by(metis stat_eq_transition Identity Composition Commutativity Assertion_stat_eq_sym)
      moreover
      {
	fix C
	have "bang_pred P (!P)" by(rule aux1)
	moreover from `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity Assertion_stat_eq_sym Assertion_stat_eq_trans)
	ultimately have "\<And>C. Prop C \<Psi> (!P) \<pi> (\<alpha> \<prec> P')" using c_par2 `R = !P` `guarded P` by simp
      }
      moreover from `A\<^sub>P \<sharp>* R` `R = !P` have "A\<^sub>P \<sharp>* P" by simp
      moreover from `Q = P` `extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` have "extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
        by simp
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) (\<alpha> \<prec> (P \<parallel> P'))" using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha>  \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `Q = P` `distinct(bn \<alpha>)`
         `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `distinct A\<^sub>P` `guarded P`
	by(rule_tac r_par2) auto
      with `R = !P` `Q = P` show ?case by simp
    next
      case(c_comm1 \<Psi>' \<Psi>\<^sub>R Q A\<^sub>P yvec K M N P' \<Psi>\<^sub>P R A\<^sub>R zvec xvec P'' \<Psi> C)
      have r_comm1: "\<And>M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''); extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''
        \<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
        by fact
      from `bang_pred P (Q \<parallel> R)` have "Q = P" and "R = !P"
	by - (ind_cases "bang_pred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from `R = !P` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from `\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'` `Q = P` `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>R = \<one>` have "\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
	by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
      moreover from `Q = P` `extract_frame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `guarded P` have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
	by(blast dest: guarded_stat_eq)+
      moreover from `\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''` `R = !P` `\<Psi>\<^sub>P \<simeq> \<one>` `\<Psi> \<simeq> \<Psi>'` have "\<Psi> \<rhd> !P \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
	by(metis stat_eq_transition Identity Composition Commutativity Assertion_stat_eq_sym)
      hence "\<Psi> \<rhd> !P \<longmapsto>Some (F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
        unfolding `A\<^sub>R = []` by simp
      moreover 
      {
	fix C
	have "bang_pred P (!P)" by(rule aux1)
	moreover from `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity Assertion_stat_eq_sym Assertion_stat_eq_trans)
	ultimately have "\<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'')" using c_comm1 `R = !P` `guarded P` by simp
      }
      moreover from `Q = P` `extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` have "extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
        by simp
      moreover from `Q = P` `A\<^sub>P \<sharp>* Q` `yvec \<sharp>* Q` `zvec \<sharp>* Q` have "A\<^sub>P \<sharp>* P" "yvec \<sharp>* P" "zvec \<sharp>* P"
        by simp_all
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q` `xvec \<sharp>* M` `xvec \<sharp>* K` `xvec \<sharp>* C` `Q = P` `distinct xvec` `distinct A\<^sub>P`
        `distinct yvec` `distinct zvec` `yvec \<sharp>* C` `zvec \<sharp>* C` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* P''` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* M` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* P'` `yvec \<sharp>* P''` `yvec \<sharp>* zvec`  `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* K` `zvec \<sharp>* A\<^sub>P` `zvec \<sharp>* P'` `zvec \<sharp>* P''`
	by(rule_tac r_comm1) simp+
      with `R = !P` `Q = P` show ?case by simp
    next
      case(c_comm2 \<Psi>' \<Psi>\<^sub>R Q A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P R A\<^sub>R zvec P'' \<Psi> C)
      have r_comm2: "\<And>M xvec N P' K A\<^sub>P \<Psi>\<^sub>P  yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>N\<rparr> \<prec> P''); extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
        zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
        by fact
      from `bang_pred P (Q \<parallel> R)` have "Q = P" and "R = !P"
	by - (ind_cases "bang_pred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from `R = !P` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from `\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `Q = P` `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>R = \<one>` have "\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
      moreover from `Q = P` `extract_frame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `guarded P` have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
	by(blast dest: guarded_stat_eq)+
      moreover from `\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> P''` `R = !P` `\<Psi>\<^sub>P \<simeq> \<one>` `\<Psi> \<simeq> \<Psi>'` have "\<Psi> \<rhd> !P \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> P''"
	by(metis stat_eq_transition Identity Composition Commutativity Assertion_stat_eq_sym)
      hence "\<Psi> \<rhd> !P \<longmapsto>Some (F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>N\<rparr> \<prec> P''"
        using `A\<^sub>R = []` by simp
      moreover 
      {
	fix C
	have "bang_pred P (!P)" by(rule aux1)
	moreover from `\<Psi> \<simeq> \<Psi>'` `\<Psi>\<^sub>P \<simeq> \<one>` have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity Assertion_stat_eq_sym Assertion_stat_eq_trans)
	ultimately have "\<And>C. Prop C \<Psi> (!P) (Some (F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>N\<rparr> \<prec> P'')" using c_comm2 `R = !P` `guarded P` by simp
      }
      moreover from `Q = P` `extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` have "extract_frame Q = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
        by simp
      moreover from `Q = P` `A\<^sub>P \<sharp>* Q` `yvec \<sharp>* Q` `zvec \<sharp>* Q` have "A\<^sub>P \<sharp>* P" "yvec \<sharp>* P" "zvec \<sharp>* P"
        by simp_all
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (None) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))" using `xvec \<sharp>* \<Psi>` `xvec \<sharp>* Q` `xvec \<sharp>* M` `xvec \<sharp>* K` `xvec \<sharp>* C` `Q = P` `distinct xvec` `distinct A\<^sub>P`
        `distinct yvec` `distinct zvec` `yvec \<sharp>* C` `zvec \<sharp>* C` `A\<^sub>P \<sharp>* C` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* P''` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* M` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* P'` `yvec \<sharp>* P''` `yvec \<sharp>* zvec`  `zvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* K` `zvec \<sharp>* A\<^sub>P` `zvec \<sharp>* P'` `zvec \<sharp>* P''`
	by(rule_tac r_comm2) simp+
      with `R = !P` `Q = P` show ?case by simp
    next
      case(c_open \<Psi> Q \<pi> M xvec yvec N P' x C)
      thus ?case by - (ind_cases "bang_pred P (\<lparr>\<nu>x\<rparr>Q)")
    next
      case(c_scope \<Psi> Q \<pi> \<alpha> P' x C)
      thus ?case by - (ind_cases "bang_pred P (\<lparr>\<nu>x\<rparr>Q)")
    next
      case(Bang \<Psi>' Q \<pi> Rs \<Psi> C)
      have r_bang: "\<And>Rs C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> Rs; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert \<circ> push_prov) \<pi>) Rs"
	by fact
      from `bang_pred P (!Q)` have "P = Q" 
	by - (ind_cases "bang_pred P (!Q)", auto simp add: psi.inject)
      with `\<Psi>' \<rhd> Q \<parallel> !Q \<longmapsto> \<pi> @ Rs` `\<Psi> \<simeq> \<Psi>'` have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ Rs" by(metis stat_eq_transition Assertion_stat_eq_sym) 
      moreover 
      {
	fix C
	have "bang_pred P (P \<parallel> !P)" by(rule aux2)
	with Bang `P = Q` have "\<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> Rs" by simp
      }
      moreover from `guarded Q` `P = Q` have "guarded P" by simp
      ultimately have "Prop C \<Psi> (!P) (map_option (F_assert \<circ> push_prov) \<pi>) Rs" by(rule r_bang)
      with `P = Q` show ?case by simp
    qed
  }
  with `guarded P` `\<Psi> \<rhd> !P \<longmapsto> \<pi> @ Rs`
  show ?thesis by(force intro: aux1)
qed

lemma bang_input_induct[consumes 1, case_names c_par1 c_par2 c_bang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     r_par1: "\<And>\<pi> P'. \<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P' \<Longrightarrow> Prop \<Psi> (P \<parallel> !P) \<pi> M N (P' \<parallel> !P)"
  and     r_par2: "\<And>\<pi> A\<^sub>P \<Psi>\<^sub>P P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; Prop \<Psi> (!P) \<pi> M N P'\<rbrakk> \<Longrightarrow> Prop \<Psi> (P \<parallel> !P) ( append_at_front_prov_option \<pi> A\<^sub>P) M N (P \<parallel> P')"
  and     r_bang: "\<And>\<pi> P'. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'; Prop \<Psi> (P \<parallel> !P) \<pi> M N P'; guarded P\<rbrakk> \<Longrightarrow> Prop \<Psi> (!P) (map_option (F_assert \<circ> push_prov) \<pi>) M N P'"
  shows "Prop \<Psi> (!P) \<pi> M N P'"
using `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'`
by(nominal_induct \<Psi> P \<pi> Rs=="M\<lparr>N\<rparr> \<prec> P'" arbitrary: P' rule: bang_induct)
  (auto simp add: residual_inject intro: r_par1 r_par2 r_bang simp del: append_at_front_prov_option.simps)

lemma bang_output_induct[consumes 1, case_names c_par1 c_par2 c_bang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) bound_output \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     r_par1: "\<And>\<pi> xvec N P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> !P))"
  and     r_par2: "\<And>\<pi> A\<^sub>P \<Psi>\<^sub>P xvec N P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> (!P) \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P'); xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C; distinct xvec; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* P'\<rbrakk> \<Longrightarrow> 
                                  Prop C \<Psi> (P \<parallel> !P) ( append_at_front_prov_option \<pi> A\<^sub>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> P'))"
  and     r_bang: "\<And>\<pi> B C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi> @ (R_out M B); \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> M B; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert \<circ> push_prov) \<pi>) M B"

  shows "Prop C \<Psi> (!P) \<pi> M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')"
using `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
apply(auto simp add: residual_inject)
by(nominal_induct \<Psi> P \<pi> Rs=="R_out M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')" avoiding: C arbitrary: xvec N P' rule: bang_induct)
(force simp add: residual_inject intro: r_par1 r_par2 r_bang simp del: append_at_front_prov_option.simps)+

lemma bang_tau_induct[consumes 1, case_names c_par1 c_par2 c_comm1 c_comm2 c_bang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto> None @ \<tau> \<prec> P'"
  and     r_par1: "\<And>P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (P' \<parallel> !P)"
  and     r_par2: "\<And>P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>None @ \<tau> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (!P) P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (P \<parallel> P')"
  and     r_comm1: "\<And>M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''
\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_comm2: "\<And>M xvec N P' K A\<^sub>P \<Psi>\<^sub>P  yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>N\<rparr> \<prec> P'';  extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_bang: "\<And>P' C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> None @ \<tau> \<prec> P'; \<And>C. Prop C \<Psi> (P \<parallel> !P) P'; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P'"
  shows "Prop C \<Psi> (!P) P'"
  using `\<Psi> \<rhd> !P \<longmapsto> None @ \<tau> \<prec> P'`
  by(nominal_induct \<Psi> P \<pi>=="None::'a frame frame option" Rs=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: bang_induct)
    (force simp add: residual_inject intro: r_par1 r_par2 r_comm1 r_comm2 r_bang intro: tau_no_provenance'')+

lemma bang_induct'[consumes 2, case_names c_alpha c_par1 c_par2 c_comm1 c_comm2 c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a frame frame option \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"  
  and     r_alpha: "\<And>\<pi> \<alpha> P' p C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>;  bn \<alpha> \<sharp>* C;
                                set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinct_perm p;
                                bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>; bn(p \<bullet> \<alpha>) \<sharp>* P'; Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> P'\<rbrakk> \<Longrightarrow>
  Prop C \<Psi> (P \<parallel> !P) \<pi> (p \<bullet> \<alpha>) (p \<bullet> P')"
  and     r_par1: "\<And>\<pi> \<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> (P' \<parallel> !P)"
  and     r_par2: "\<And>\<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<pi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; distinct A\<^sub>P; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; guarded P;
                             \<And>C. Prop C \<Psi> (!P) \<pi> \<alpha> P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> P')"
  and     r_comm1: "\<And>M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P''; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''
\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_comm2: "\<And>M xvec N P' K A\<^sub>P \<Psi>\<^sub>P  yvec zvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>Some(F_assert(\<langle>zvec, M\<rangle>)) @ K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (Some(F_assert(\<langle>zvec, M\<rangle>))) (K\<lparr>N\<rparr>) P''; extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec; distinct yvec; distinct zvec; yvec \<sharp>* C; zvec \<sharp>* C; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* P'';
             yvec \<sharp>* \<Psi>; yvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* P; yvec \<sharp>* M;
             yvec \<sharp>* A\<^sub>P; yvec \<sharp>* P'; yvec \<sharp>* P''; yvec \<sharp>* zvec;
             zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* K;
             zvec \<sharp>* A\<^sub>P; zvec \<sharp>* P'; zvec \<sharp>* P''\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (None) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     r_bang: "\<And>\<pi> \<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ \<alpha> \<prec> P'; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> P'; guarded P; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (map_option (F_assert o push_prov) \<pi>) \<alpha> P'"
  shows "Prop C \<Psi> (!P) \<pi> \<alpha> P'"
proof -
  from `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "distinct(bn \<alpha>)" by(rule bound_output_distinct)
  with `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* subject \<alpha>` show ?thesis
  proof(nominal_induct \<Psi> P \<pi> Rs=="\<alpha> \<prec> P'" avoiding: C \<alpha> P' rule: bang_induct)
    case(c_par1 \<pi> \<alpha> P' C \<alpha>' P'')
    note  `\<alpha> \<prec> (P' \<parallel> !P) = \<alpha>' \<prec> P''`
    moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* bn \<alpha>'" by simp
    moreover note `distinct(bn \<alpha>)` `distinct(bn \<alpha>')`
    moreover from `bn \<alpha> \<sharp>* subject \<alpha>` have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> !P)" by simp
    moreover from `bn \<alpha>' \<sharp>* subject \<alpha>'` have "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp
    ultimately obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "\<alpha>' = p \<bullet> \<alpha>"
                    and  P'eq: "P'' = p \<bullet> (P' \<parallel> !P)" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> !P)"
      by(rule_tac residual_eq)

    from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `distinct(bn \<alpha>)` 
    have "Prop C \<Psi> (P \<parallel> !P) \<pi> \<alpha> (P' \<parallel> !P)"
      by(rule r_par1)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` S `distinct_perm p` `bn \<alpha> \<sharp>* \<alpha>'` `bn \<alpha> \<sharp>* P''` `\<alpha>' = (p \<bullet> \<alpha>)` P'eq `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> !P)`
    have "Prop C \<Psi> (P \<parallel> !P) \<pi> (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> !P))"
      by(rule_tac r_alpha) 
    with P'eq `\<alpha>' = p \<bullet> \<alpha>` `distinct_perm p` show ?case  by simp
  next
    case(c_par2 \<pi> \<alpha> P' A\<^sub>P \<Psi>\<^sub>P C \<alpha>' P'')
    note  `\<alpha> \<prec> (P \<parallel> P') = \<alpha>' \<prec> P''`
    moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* bn \<alpha>'" by simp
    moreover note `distinct(bn \<alpha>)` `distinct(bn \<alpha>')`
    moreover from `bn \<alpha> \<sharp>* subject \<alpha>` have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> P')" by simp
    moreover from `bn \<alpha>' \<sharp>* subject \<alpha>'` have "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp
    ultimately obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinct_perm p" and "\<alpha>' = p \<bullet> \<alpha>"
                    and  P'eq: "P'' = p \<bullet> (P \<parallel> P')" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> P')"
      by(rule_tac residual_eq)
    
    note `\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'`
    moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "\<And>C. Prop C \<Psi> (!P) \<pi> \<alpha> P'" by(rule_tac c_par2) auto
    moreover note `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha>  \<sharp>* P` `bn \<alpha>  \<sharp>* subject \<alpha>` `bn \<alpha>  \<sharp>* C` `distinct(bn \<alpha>)`
    ultimately have "Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) \<alpha> (P \<parallel> P')"
      using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* P'` `distinct A\<^sub>P` `guarded P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>`
      by(rule_tac r_par2) auto
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` S `distinct_perm p` `bn \<alpha> \<sharp>* \<alpha>'` `bn \<alpha> \<sharp>* P''` `\<alpha>' = (p \<bullet> \<alpha>)` P'eq `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> P')`
    have "Prop C \<Psi> (P \<parallel> !P) (append_at_front_prov_option \<pi> A\<^sub>P) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> P'))"
      by(rule_tac r_alpha)
    with P'eq `\<alpha>' = p \<bullet> \<alpha>` show ?case by simp
  next
    case(c_comm1 M N P' K xvec A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C \<alpha> P''')
    hence "Prop C \<Psi> (P \<parallel> !P) (None) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
      by(rule_tac r_comm1) (assumption | simp)+
    thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') = \<alpha> \<prec> P'''`
      by(simp add: residual_inject)
  next
    case(c_comm2 M xvec N P' K A\<^sub>P \<Psi>\<^sub>P yvec zvec P'' C \<alpha> P''')
    hence "Prop C \<Psi> (P \<parallel> !P) (None) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
      by(rule_tac r_comm2) (assumption | simp)+
    thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') = \<alpha> \<prec> P'''`
      by(simp add: residual_inject)
  next
    case(c_bang C \<alpha> P')
    thus ?case by(auto intro: r_bang)
  qed
qed

lemma input_provenance':
  fixes C::"'ty :: fs_name"
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "A\<^sub>P \<sharp>* \<pi>"  
  shows "\<exists> xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> distinct xvec \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P' \<and> xvec \<sharp>* C \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K)"
proof -
  from Trans obtain A\<^sub>P' \<Psi>\<^sub>P' xvec K where "\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P',\<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* M" and "distinct xvec" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* N" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* A\<^sub>P" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P" and "xvec \<sharp>* N" and "xvec \<sharp>* P'" and "xvec \<sharp>* C" and "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P' \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> M \<leftrightarrow> K"
    by(auto dest!: input_provenance[where C="(C,A\<^sub>P,\<Psi>\<^sub>P)"])
  from `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `extract_frame P = \<langle>A\<^sub>P',\<Psi>\<^sub>P'\<rangle>` `A\<^sub>P' \<sharp>* A\<^sub>P` `distinct A\<^sub>P` `distinct A\<^sub>P'`
  obtain p where p: "set p \<subseteq> set A\<^sub>P' \<times> set(p\<bullet>A\<^sub>P')" "distinct_perm p" and freqs: "A\<^sub>P = p\<bullet>A\<^sub>P'" "\<Psi>\<^sub>P = p\<bullet>\<Psi>\<^sub>P'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P'" and yvec="A\<^sub>P"]) auto
  from `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P' \<sharp>* A\<^sub>P` `\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)` `xvec \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* K"
    by(auto simp add: frame_chain_fresh_chain'')
  hence "\<pi> = Some(\<langle>A\<^sub>P; xvec, (p\<bullet>K)\<rangle>)" using `xvec \<sharp>* A\<^sub>P`
    using `\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)` p `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P' \<sharp>* xvec`
    unfolding freqs
    by(subst (asm) frame_chain_alpha'[where A\<^sub>P="A\<^sub>P'"]) (auto simp add: frame_chain_fresh_chain'' eqvts)
  moreover note `distinct xvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* M` `xvec \<sharp>* P` `xvec \<sharp>* N` `xvec \<sharp>* P'` `xvec \<sharp>* C`
  moreover note `xvec \<sharp>* A\<^sub>P`
  moreover have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> (p\<bullet>K)"
    using `\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> M \<leftrightarrow> K` p `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P' \<sharp>* M`
    unfolding freqs
    by(subst (asm) perm_bool[where pi=p, symmetric]) (simp add: eqvts)
  ultimately show ?thesis
    by force
qed

lemma output_provenance':
  fixes C::"'ty :: fs_name"
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> \<pi> @ R_out M B"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "A\<^sub>P \<sharp>* \<pi>"
  shows "\<exists> xvec K. (\<pi> = Some(\<langle>A\<^sub>P; xvec, K\<rangle>) \<and> distinct xvec \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* M \<and> xvec \<sharp>* P \<and> xvec \<sharp>* B \<and> xvec \<sharp>* C \<and> A\<^sub>P \<sharp>* xvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M)"
proof -
  from Trans obtain A\<^sub>P' \<Psi>\<^sub>P' xvec K where "\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P',\<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* M" and "distinct xvec" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* B" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* A\<^sub>P" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* P" and "xvec \<sharp>* B" and "xvec \<sharp>* C" and "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P' \<sharp>* xvec" and "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> K \<leftrightarrow> M"
    by(auto dest!: output_provenance[where C="(C,A\<^sub>P,\<Psi>\<^sub>P)"])
  from `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `extract_frame P = \<langle>A\<^sub>P',\<Psi>\<^sub>P'\<rangle>` `A\<^sub>P' \<sharp>* A\<^sub>P` `distinct A\<^sub>P` `distinct A\<^sub>P'`
  obtain p where p: "set p \<subseteq> set A\<^sub>P' \<times> set(p\<bullet>A\<^sub>P')" "distinct_perm p" and freqs: "A\<^sub>P = p\<bullet>A\<^sub>P'" "\<Psi>\<^sub>P = p\<bullet>\<Psi>\<^sub>P'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P'" and yvec="A\<^sub>P"]) auto
  from `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P' \<sharp>* A\<^sub>P` `\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)` `xvec \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* K"
    by(auto simp add: frame_chain_fresh_chain'')
  hence "\<pi> = Some(\<langle>A\<^sub>P; xvec, (p\<bullet>K)\<rangle>)" using `xvec \<sharp>* A\<^sub>P`
    using `\<pi> = Some(\<langle>A\<^sub>P'; xvec, K\<rangle>)` p `A\<^sub>P \<sharp>* \<pi>` `A\<^sub>P' \<sharp>* xvec`
    unfolding freqs
    by(subst (asm) frame_chain_alpha'[where A\<^sub>P="A\<^sub>P'"]) (auto simp add: frame_chain_fresh_chain'' eqvts)
  moreover note `distinct xvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* M` `xvec \<sharp>* P` `xvec \<sharp>* B` `xvec \<sharp>* C`
  moreover note `xvec \<sharp>* A\<^sub>P`
  moreover have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> (p\<bullet>K) \<leftrightarrow> M"
    using `\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> K \<leftrightarrow> M` p `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P' \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P' \<sharp>* M`
    unfolding freqs
    by(subst (asm) perm_bool[where pi=p, symmetric]) (simp add: eqvts)
  ultimately show ?thesis
    by force
qed

(* TODO: Move*)
lemma append_at_end_prov_append:
  assumes "xvec \<sharp>* yvec"
  shows "append_at_end_prov (append_at_end_prov \<pi> xvec) yvec = append_at_end_prov \<pi> (xvec@yvec)"
  using assms
  by(nominal_induct \<pi>  avoiding: xvec yvec rule: frame.strong_inducts) simp_all

lemma frame_chain_inject':
  fixes \<pi>::"'d::fs_name frame"
  assumes "\<lparr>\<nu>*yvec\<rparr>\<pi>' = \<lparr>\<nu>*yvec\<rparr>\<pi>"
  shows "\<pi>' = \<pi>"
  using assms
  by(induct yvec) (auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])

lemma frame_chain_inject:
  fixes \<pi>::"'d::fs_name"
  assumes "\<langle>yvec, \<pi>'\<rangle> = \<langle>yvec, \<pi>\<rangle>"
  shows "\<langle>\<epsilon>, \<pi>'\<rangle> = \<langle>\<epsilon>, \<pi>\<rangle>"
  using assms
  by(induct yvec) (auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])

lemma frame_chain_eq'':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'d::fs_name frame"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'d::fs_name frame"

  assumes "\<lparr>\<nu>*xvec\<rparr>\<Psi> = \<lparr>\<nu>*yvec\<rparr>\<Psi>'"
  and "length xvec = length yvec"
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
    have Eq: "\<lparr>\<nu>*xvec\<rparr>\<Psi> = \<lparr>\<nu>*yvec\<rparr>\<Psi>'" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []" using `length xvec = length yvec`
      by(case_tac yvec) (auto simp add: frame.inject)
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<lparr>\<nu>*xvec\<rparr>\<Psi> = \<lparr>\<nu>*yvec\<rparr>\<Psi>'` `xvec = x # xvec'` `length xvec = length yvec`
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>\<Psi> = \<lparr>\<nu>*(y#yvec')\<rparr>\<Psi>'"
      and "yvec = y#yvec'" 
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>\<Psi> = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>\<Psi>'"
      by simp
    from `xvec = x#xvec'` `yvec=y#yvec'` `xvec \<sharp>* yvec`
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from `distinct xvec` `distinct yvec` `xvec=x#xvec'` `yvec=y#yvec'` have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>(\<Psi>::'d frame) = \<lparr>\<nu>*yvec\<rparr>(\<Psi>'::'d frame); length xvec = length yvec; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinct_perm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    from EQ `x \<noteq> y`  `x \<sharp> yvec'` `y \<sharp> yvec'` have "\<lparr>\<nu>*xvec'\<rparr>\<Psi> = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> \<Psi>')"
      by(simp add: frame.inject alpha eqvts)
    moreover note `xvec' \<sharp>* yvec'` `distinct xvec'` `distinct yvec'` `length xvec' = n` IH
    moreover from `length xvec = length yvec` `xvec = x#xvec'` `yvec=y#yvec'`
    have "length xvec' = length yvec'"
      by simp
    ultimately obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinct_perm p" and "yvec' = p \<bullet> xvec'" and "[(x, y)] \<bullet> \<Psi>' = p \<bullet> \<Psi>"
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

(* TODO: move *)
lemma append_at_end_prov_eq_elim:
  fixes \<pi> :: "'a frame frame"
  assumes "xvec \<sharp>* yvec" and "distinct yvec" and "distinct xvec"
  and "\<langle>(xvec @ yvec), \<pi>'\<rangle> = append_at_end_prov \<pi> yvec"
  shows "\<langle>xvec,\<pi>'\<rangle> = \<pi>"
proof -
  obtain zvec \<pi>'' where \<pi>: "\<pi> = \<langle>zvec,\<pi>''\<rangle>" and "distinct zvec" and "zvec \<sharp>* \<pi>'" and "zvec \<sharp>* \<pi>"
    and "zvec \<sharp>* xvec" and "zvec \<sharp>* yvec"
    by(rule_tac fresh_frame[where C="(\<pi>,\<pi>',xvec,yvec)" and F=\<pi>]) auto
  hence eq: "\<lparr>\<nu>*xvec\<rparr>(\<langle>yvec, \<pi>'\<rangle>) = \<lparr>\<nu>*zvec\<rparr>(\<langle>yvec,\<pi>''\<rangle>)"
    using assms
    by(auto simp add: frame_chain_append dest: frame_chain_inject)
  moreover hence "length xvec = length zvec"
    by(auto simp add: frame_chain_append[symmetric] dest: frame_chain_eq_length)
  moreover note `zvec \<sharp>* xvec` `distinct xvec` `distinct zvec` `length xvec = length zvec`
  ultimately obtain p where "(set p) \<subseteq> (set xvec) \<times> set (p\<bullet>xvec)" and "distinct_perm p" and "\<langle>yvec,\<pi>''\<rangle> = p \<bullet> (\<langle>yvec, \<pi>'\<rangle>)" and "zvec = p \<bullet> xvec"
    by(rule_tac frame_chain_eq'') (assumption|simp)+
  with eq
  have "\<langle>p\<bullet>xvec, p\<bullet>\<pi>'\<rangle> = \<pi>" unfolding \<pi> using `xvec \<sharp>* yvec` `zvec \<sharp>* yvec` `zvec \<sharp>* \<pi>'`
    by(subst (asm) frame_chain_alpha[where xvec=xvec and p=p]) (auto simp add: eqvts dest: frame_chain_inject intro: frame_chain_fresh_chain')
  thus ?thesis using `zvec \<sharp>* \<pi>'` `zvec = p \<bullet> xvec` `(set p) \<subseteq> (set xvec) \<times> set (p\<bullet>xvec)`
    unfolding \<pi>
    by(subst frame_chain_alpha[where xvec=xvec and p=p]) (auto simp add: frame_chain_fresh_chain)
qed

lemma append_at_end_prov_option_eq_elim:
  fixes \<pi> :: "'a frame frame option"
  assumes "xvec \<sharp>* yvec" and "distinct yvec" and "distinct xvec"
  and "Some(\<langle>(xvec @ yvec), \<pi>'\<rangle>) = append_at_end_prov_option \<pi> yvec"
  shows "Some(\<langle>xvec,\<pi>'\<rangle>) = \<pi>"
  using assms
  by(induct \<pi>) (auto intro: append_at_end_prov_eq_elim)

lemma append_at_front_prov_option_eq_elim:
  fixes \<pi> :: "'a frame frame option"
  assumes "Some(\<langle>(xvec @ yvec), \<pi>'\<rangle>) = append_at_front_prov_option \<pi> xvec"
  shows "Some(\<langle>yvec,\<pi>'\<rangle>) = \<pi>"
  using assms
  by(induct \<pi>) (auto simp add: frame_chain_append frame_chain_inject')

lemma input_frame_provenance_induct[consumes 5, case_names c_alpha c_prov_alpha c_input c_case c_par1 c_par2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct zvec"
  and     "A\<^sub>P \<sharp>* zvec"
  and     r_alpha: "\<And>\<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* zvec; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* C;
                                            set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p;
                                             Prop C \<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P zvec (p\<bullet>K) M N P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     r_prov_alpha: "\<And>\<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* P'; A\<^sub>P \<sharp>* zvec; zvec \<sharp>* (p \<bullet> zvec); zvec \<sharp>* C;
                                            set p \<subseteq> set zvec \<times> set(p \<bullet> zvec); distinct_perm p;
                                             Prop C \<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P (p\<bullet>zvec) (p\<bullet>K) M N P' A\<^sub>P \<Psi>\<^sub>P"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> K \<leftrightarrow> M; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P) ([]) M
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec]) ([]) (\<one>)"
  and     r_case: "\<And>\<Psi> P zvec K M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; distinct zvec; \<And>C. Prop C \<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P;
                                              (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                              A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* zvec; A\<^sub>P \<sharp>* C; zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* P'; zvec \<sharp>* \<phi>; zvec \<sharp>* Cs; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (A\<^sub>P@zvec) K M N P' ([]) (\<one>)"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P zvec K M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* zvec;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* zvec;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; 
                   zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* P';
                   zvec \<sharp>* Q; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) zvec K M N (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q zvec K M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q zvec K M N Q' A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* zvec;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* zvec;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C;
                   zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* Q';
                   zvec \<sharp>* Q; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) zvec K M N (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_scope: "\<And>\<Psi> P zvec K M N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; 
                     x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* zvec;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; x \<sharp> zvec; zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N;
                     zvec \<sharp>* P'; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) zvec K M N (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_bang:    "\<And>\<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) zvec K M N P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* zvec; A\<^sub>P \<sharp>* C;
                      zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* P'; zvec \<sharp>* \<Psi>\<^sub>P;
                      zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (A\<^sub>P@zvec) K M N P' ([]) (\<one>)"
  shows "Prop C \<Psi> P zvec K M N P' A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP `distinct A\<^sub>P` `distinct zvec` `A\<^sub>P \<sharp>* zvec`
proof(nominal_induct \<Psi> P \<pi>=="Some(\<langle>A\<^sub>P; zvec, K\<rangle>)" M N P' A\<^sub>P \<Psi>\<^sub>P D=="K" avoiding: C zvec arbitrary: K rule: input_frame_induct)
  case(c_input \<Psi> M K xvec N Tvec P C zvec L) thus ?case
    by(auto simp add: frame.inject residual_inject intro: r_input)
next
  case(c_alpha \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P p C zvec K)
  moreover hence "(p\<bullet>A\<^sub>P) \<sharp>* K"
    by(subst perm_bool[where pi=p, symmetric]) (auto simp add: eqvts frame_chain_fresh_chain'')
  with c_alpha have "\<langle>p \<bullet> A\<^sub>P; zvec, p \<bullet> K\<rangle> = \<langle>A\<^sub>P; zvec, K\<rangle>"
    by(subst frame_chain_alpha'[where A\<^sub>P="A\<^sub>P" and p=p]) (auto simp add: eqvts frame_chain_fresh_chain'')
  ultimately show ?case
    by(auto intro: r_alpha)
next
  case(c_case \<Psi> P \<pi> M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and "yvec \<sharp>* \<Psi>" and "yvec \<sharp>* M" and "yvec \<sharp>* N" and "yvec \<sharp>* P'" and "yvec \<sharp>* Cs" and "yvec \<sharp>* \<pi>" and "yvec \<sharp>* \<phi>" and "yvec \<sharp>* Cs" and "yvec \<sharp>* A\<^sub>P" and "yvec \<sharp>* \<Psi>\<^sub>P" and "yvec \<sharp>* C" and "yvec \<sharp>* zvec" and "yvec \<sharp>* K" and "yvec \<sharp>* P"
    using `\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac input_provenance'[where C="(\<phi>,Cs,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P)"]) auto
  with `map_option (F_assert \<circ> push_prov) \<pi> = Some (\<langle>[]; zvec, K\<rangle>)`
  have "\<langle>(A\<^sub>P@yvec), K'\<rangle> = \<langle>zvec, K\<rangle>"
    by(simp add: frame.inject)
  moreover note `yvec \<sharp>* A\<^sub>P` `distinct yvec` `distinct A\<^sub>P` `distinct zvec`
    `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* zvec`
  ultimately obtain p::"name prm" where "set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))" and "distinct_perm p" and peq: "zvec = p\<bullet>(A\<^sub>P@yvec)" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P@yvec" and yvec="zvec"]) auto
  from \<pi> `distinct yvec` `yvec \<sharp>* A\<^sub>P` have "\<And> C. Prop C \<Psi> P yvec K' M N P' A\<^sub>P \<Psi>\<^sub>P"
    by(rule_tac c_case) auto
  moreover from `\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` have "\<Psi> \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K'\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
    unfolding \<pi> by simp
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `guarded P` `\<Psi>\<^sub>P \<simeq> \<one>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* P'` `(\<phi>,P) mem Cs` `\<Psi> \<turnstile> \<phi>` `A\<^sub>P \<sharp>* \<pi>` `yvec \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* C` `supp \<Psi>\<^sub>P = {}` `A\<^sub>P \<sharp>* Cs` `A\<^sub>P \<sharp>* \<phi>` `distinct yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* N` `yvec \<sharp>* P'` `yvec \<sharp>* \<phi>` `yvec \<sharp>* Cs``yvec \<sharp>* \<Psi>\<^sub>P``yvec \<sharp>* C`
  ultimately have "Prop C \<Psi> (Cases Cs) (A\<^sub>P@yvec) K' M N P' ([]) (\<one>)"
    by(rule_tac r_case) (assumption|auto)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Cs` `yvec \<sharp>* Cs` `A\<^sub>P \<sharp>* M` `yvec \<sharp>* M` `A\<^sub>P \<sharp>* N` `yvec \<sharp>* N` `A\<^sub>P \<sharp>* P'` `yvec \<sharp>* P'` `A\<^sub>P \<sharp>* zvec` `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* C` `yvec \<sharp>* C` `distinct_perm p` `set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))`
  ultimately show ?case
    unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* P'" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* P'" "yvec \<sharp>* Q"
    using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac input_provenance'[where C="(\<Psi>,\<Psi>\<^sub>Q,A\<^sub>Q,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P,P',Q)"]) auto
  from `append_at_end_prov_option \<pi> A\<^sub>Q = Some (\<langle>(A\<^sub>P @ A\<^sub>Q); zvec, K\<rangle>)` `A\<^sub>P \<sharp>* A\<^sub>Q` `distinct A\<^sub>P` `distinct A\<^sub>Q`
  have \<pi>': "\<pi> = Some(\<langle>A\<^sub>P; zvec, K\<rangle>)"
    by(metis append_at_end_prov_option_eq_elim)
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+  
  moreover have "Prop C \<Psi> (P \<parallel> Q) yvec K' M N (P' \<parallel> Q) (A\<^sub>P @ A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    using c_par1 yfs `distinct yvec` unfolding \<pi>
    by(rule_tac r_par1) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<pi> M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>Q; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* Q'" "yvec \<sharp>* Q"
    using `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> Q'` `distinct A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* \<pi>`
    by(drule_tac input_provenance'[where C="(\<Psi>,\<Psi>\<^sub>Q,A\<^sub>P,A\<^sub>Q,C,zvec,K,\<Psi>\<^sub>P,\<pi>,Q,Q',P)"]) auto
  from `append_at_front_prov_option \<pi> A\<^sub>P = Some (\<langle>(A\<^sub>P @ A\<^sub>Q); zvec, K\<rangle>)` `A\<^sub>P \<sharp>* A\<^sub>Q` `distinct A\<^sub>P` `distinct A\<^sub>Q`
  have \<pi>': "\<pi> = Some(\<langle>A\<^sub>Q; zvec, K\<rangle>)"
    by(metis append_at_front_prov_option_eq_elim)
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+  
  moreover have "Prop C \<Psi> (P \<parallel> Q) yvec K' M N (P \<parallel> Q') (A\<^sub>P @ A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    using c_par2 yfs `distinct yvec` unfolding \<pi>
    by(rule_tac r_par2) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_scope \<Psi> P \<pi> M N P' x A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* P'" "yvec \<sharp>* \<pi>" "x \<sharp> yvec" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* P'"
    using `\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac input_provenance'[where C="(\<Psi>,x,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P,P')"]) auto
  from `map_option (F_res x) \<pi> = Some (\<langle>(x # A\<^sub>P); zvec, K\<rangle>)`
  have \<pi>': "\<pi> = Some (\<langle>A\<^sub>P; zvec, K\<rangle>)"
    by(induct \<pi>) (auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)  
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+
  moreover have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) yvec K' M N (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    using c_scope yfs `distinct yvec` unfolding \<pi>
    by(rule_tac r_scope) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_bang \<Psi> P \<pi> M N P' A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* P'" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P"
    using `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac input_provenance'[where C="(\<phi>,Cs,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P)"]) auto
  with `map_option (F_assert \<circ> push_prov) \<pi> = Some (\<langle>[]; zvec, K\<rangle>)`
  have "\<langle>(A\<^sub>P@yvec), K'\<rangle> = \<langle>zvec, K\<rangle>"
    by(simp add: frame.inject)
  moreover note `yvec \<sharp>* A\<^sub>P` `distinct yvec` `distinct A\<^sub>P` `distinct zvec`
    `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* zvec`
  ultimately obtain p::"name prm" where "set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))" and "distinct_perm p" and peq: "zvec = p\<bullet>(A\<^sub>P@yvec)" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P@yvec" and yvec="zvec"]) auto
  from \<pi> `distinct yvec` `yvec \<sharp>* A\<^sub>P` have "\<And> C. Prop C \<Psi> (P \<parallel> !P) yvec K' M N P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>)"
    by(rule_tac c_bang) auto
  moreover from `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'` have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K'\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
    unfolding \<pi> by simp
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `guarded P` `\<Psi>\<^sub>P \<simeq> \<one>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `A\<^sub>P \<sharp>* P'` `A\<^sub>P \<sharp>* \<pi>` `yvec \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* C` `supp \<Psi>\<^sub>P = {}` `distinct yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* N` `yvec \<sharp>* P'` `yvec \<sharp>* \<Psi>\<^sub>P``yvec \<sharp>* C`
  ultimately have "Prop C \<Psi> (!P) (A\<^sub>P@yvec) K' M N P' ([]) (\<one>)"
    by(rule_tac r_bang) (assumption|auto)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `yvec \<sharp>* M` `A\<^sub>P \<sharp>* N` `yvec \<sharp>* N` `A\<^sub>P \<sharp>* P'` `yvec \<sharp>* P'` `A\<^sub>P \<sharp>* zvec` `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* C` `yvec \<sharp>* C` `distinct_perm p` `set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))` `yvec \<sharp>* P`
  ultimately show ?case
    unfolding peq
    by(rule_tac r_prov_alpha) auto
qed

lemma output_frame_provenance_induct[consumes 5, case_names c_alpha c_prov_alpha c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) bound_output \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ R_out M B"
  and     FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct zvec"
  and     "A\<^sub>P \<sharp>* zvec"  
  and     r_alpha: "\<And>\<Psi> P zvec K M A\<^sub>P \<Psi>\<^sub>P p B C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* zvec; A\<^sub>P \<sharp>* C;
                                         set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinct_perm p;
                                          Prop C \<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P zvec (p\<bullet>K) M B (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     r_prov_alpha: "\<And>\<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* B; A\<^sub>P \<sharp>* zvec; zvec \<sharp>* (p \<bullet> zvec); zvec \<sharp>* C;
                                            set p \<subseteq> set zvec \<times> set(p \<bullet> zvec); distinct_perm p;
                                             Prop C \<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P (p\<bullet>zvec) (p\<bullet>K) M B A\<^sub>P \<Psi>\<^sub>P"
  and     r_output: "\<And>\<Psi> M K N P C. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) ([]) M K (N \<prec>' P) ([]) (\<one>)"
  and     r_case: "\<And>\<Psi> P zvec K M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; zvec, K\<rangle>) @ (R_out M B); extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; distinct zvec; \<And>C. Prop C \<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Cs; A\<^sub>P \<sharp>* \<phi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* zvec; A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* C; zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* B; zvec \<sharp>* \<phi>; zvec \<sharp>* Cs; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) (A\<^sub>P@zvec) K M B ([]) (\<one>)"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P zvec K M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* zvec;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* zvec;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* zvec; xvec \<sharp>* K;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C;
                   zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* P';
                   zvec \<sharp>* Q; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q M zvec K xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some(\<langle>A\<^sub>Q; zvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q';
                   extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q') A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* zvec;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* zvec;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* zvec; xvec \<sharp>* K;
                   zvec \<sharp>* \<Psi>; zvec \<sharp>* \<Psi>\<^sub>Q; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N; zvec \<sharp>* Q';
                   zvec \<sharp>* Q; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     r_open: "\<And>\<Psi> P zvec K M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P zvec K M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* zvec;
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P;  xvec \<sharp>* zvec; xvec \<sharp>* K;
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* zvec; yvec \<sharp>* K; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C; x \<sharp> zvec; zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N;
                     zvec \<sharp>* P'; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) zvec K M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_scope: "\<And>\<Psi> P zvec K M xvec N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P;
                     x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* zvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* zvec; xvec \<sharp>* K;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; x \<sharp> zvec; zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* M; zvec \<sharp>* N;
                     zvec \<sharp>* P'; zvec \<sharp>* \<Psi>\<^sub>P; zvec \<sharp>* C; distinct zvec\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) zvec K M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     r_bang:    "\<And>\<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ R_out M B; guarded P; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) zvec K M B A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* C;
                      zvec \<sharp>* \<Psi>; zvec \<sharp>* P; zvec \<sharp>* A\<^sub>P; zvec \<sharp>* M; zvec \<sharp>* B; zvec \<sharp>* \<Psi>\<^sub>P; distinct zvec; zvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) (A\<^sub>P@zvec) K M B ([]) (\<one>)"
  shows "Prop C \<Psi> P zvec K M B A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP `distinct A\<^sub>P` `distinct zvec` `A\<^sub>P \<sharp>* zvec`
proof(nominal_induct \<Psi> P \<pi>=="Some(\<langle>A\<^sub>P; zvec, K\<rangle>)" M B A\<^sub>P \<Psi>\<^sub>P D=="K" avoiding: C zvec arbitrary: K rule: output_frame_induct)
  case(c_alpha \<Psi> P M A\<^sub>P \<Psi>\<^sub>P p B C zvec K)
  moreover hence "(p\<bullet>A\<^sub>P) \<sharp>* K"
    by(subst perm_bool[where pi=p, symmetric]) (auto simp add: eqvts frame_chain_fresh_chain'')
  with c_alpha have "\<langle>p \<bullet> A\<^sub>P; zvec, p \<bullet> K\<rangle> = \<langle>A\<^sub>P; zvec, K\<rangle>"
    by(subst frame_chain_alpha'[where A\<^sub>P="A\<^sub>P" and p=p]) (auto simp add: eqvts frame_chain_fresh_chain'')
  ultimately show ?case
    by(auto intro: r_alpha)
next
  case(c_output \<Psi> M K N P C zvec K) thus ?case
    by(auto simp add: frame.inject residual_inject intro: r_output)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<pi> M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* P'" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* P'" "yvec \<sharp>* Q" "yvec \<sharp>* xvec"
    using `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    unfolding residual_inject
    by(drule_tac output_provenance'[where C="(\<Psi>,\<Psi>\<^sub>Q,A\<^sub>Q,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P,P',Q,xvec)"]) auto
  from `append_at_end_prov_option \<pi> A\<^sub>Q = Some (\<langle>(A\<^sub>P @ A\<^sub>Q); zvec, K\<rangle>)` `A\<^sub>P \<sharp>* A\<^sub>Q` `distinct A\<^sub>P` `distinct A\<^sub>Q`
  have \<pi>': "\<pi> = Some(\<langle>A\<^sub>P; zvec, K\<rangle>)"
    by(metis append_at_end_prov_option_eq_elim)
  have "xvec \<sharp>* K'" using \<pi> `xvec \<sharp>* \<pi>` `A\<^sub>P \<sharp>* xvec` `yvec \<sharp>* xvec`
    by(auto simp add: frame_chain_fresh_chain'')
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+
  moreover have "Prop C \<Psi> (P \<parallel> Q) yvec K' M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q)) (A\<^sub>P @ A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    using c_par1 yfs `distinct yvec` `xvec \<sharp>* K'` unfolding \<pi>
    by(rule_tac r_par1) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M \<pi> xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>Q; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* Q'" "yvec \<sharp>* Q" "yvec \<sharp>* xvec"
    using `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `distinct A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* M` `A\<^sub>Q \<sharp>* \<pi>`
    unfolding residual_inject
    by(drule_tac output_provenance'[where C="(\<Psi>,\<Psi>\<^sub>Q,A\<^sub>P,A\<^sub>Q,C,zvec,K,\<Psi>\<^sub>P,\<pi>,Q,Q',P,xvec)"]) auto
  from `append_at_front_prov_option \<pi> A\<^sub>P = Some (\<langle>(A\<^sub>P @ A\<^sub>Q); zvec, K\<rangle>)` `A\<^sub>P \<sharp>* A\<^sub>Q` `distinct A\<^sub>P` `distinct A\<^sub>Q`
  have \<pi>': "\<pi> = Some(\<langle>A\<^sub>Q; zvec, K\<rangle>)"
    by(metis append_at_front_prov_option_eq_elim)
  have "xvec \<sharp>* K'" using \<pi> `xvec \<sharp>* \<pi>` `A\<^sub>Q \<sharp>* xvec` `yvec \<sharp>* xvec`
    by(auto simp add: frame_chain_fresh_chain'')
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+  
  moreover have "Prop C \<Psi> (P \<parallel> Q) yvec K' M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q')) (A\<^sub>P @ A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    using c_par2 yfs `distinct yvec` `xvec \<sharp>* K'` unfolding \<pi>
    by(rule_tac r_par2) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_case \<Psi> P \<pi> M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and "yvec \<sharp>* \<Psi>" and "yvec \<sharp>* M" and "yvec \<sharp>* B" and "yvec \<sharp>* Cs" and "yvec \<sharp>* \<pi>" and "yvec \<sharp>* \<phi>" and "yvec \<sharp>* Cs" and "yvec \<sharp>* A\<^sub>P" and "yvec \<sharp>* \<Psi>\<^sub>P" and "yvec \<sharp>* C" and "yvec \<sharp>* zvec" and "yvec \<sharp>* K" and "yvec \<sharp>* P"
    using `\<Psi> \<rhd> P \<longmapsto> \<pi> @ R_out M B` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac output_provenance'[where C="(\<phi>,Cs,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P)"]) auto
  with `map_option (F_assert \<circ> push_prov) \<pi> = Some (\<langle>[]; zvec, K\<rangle>)`
  have "\<langle>(A\<^sub>P@yvec), K'\<rangle> = \<langle>zvec, K\<rangle>"
    by(simp add: frame.inject)
  moreover note `yvec \<sharp>* A\<^sub>P` `distinct yvec` `distinct A\<^sub>P` `distinct zvec`
    `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* zvec`
  ultimately obtain p::"name prm" where "set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))" and "distinct_perm p" and peq: "zvec = p\<bullet>(A\<^sub>P@yvec)" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P@yvec" and yvec="zvec"]) auto
  from \<pi> `distinct yvec` `yvec \<sharp>* A\<^sub>P` have "\<And> C. Prop C \<Psi> P yvec K' M B A\<^sub>P \<Psi>\<^sub>P"
    by(rule_tac c_case) auto
  moreover from `\<Psi> \<rhd> P \<longmapsto> \<pi> @ R_out M B` have "\<Psi> \<rhd> P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K'\<rangle>) @ R_out M B"
    unfolding \<pi> by simp
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `guarded P` `\<Psi>\<^sub>P \<simeq> \<one>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* B` `(\<phi>,P) mem Cs` `\<Psi> \<turnstile> \<phi>` `A\<^sub>P \<sharp>* \<pi>` `yvec \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* C` `supp \<Psi>\<^sub>P = {}` `A\<^sub>P \<sharp>* Cs` `A\<^sub>P \<sharp>* \<phi>` `distinct yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* B` `yvec \<sharp>* \<phi>` `yvec \<sharp>* Cs``yvec \<sharp>* \<Psi>\<^sub>P``yvec \<sharp>* C`
  ultimately have "Prop C \<Psi> (Cases Cs) (A\<^sub>P@yvec) K' M B ([]) (\<one>)"
    by(rule_tac r_case) (assumption|auto)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Cs` `yvec \<sharp>* Cs` `A\<^sub>P \<sharp>* M` `yvec \<sharp>* M` `A\<^sub>P \<sharp>* B` `yvec \<sharp>* B` `A\<^sub>P \<sharp>* zvec` `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* C` `yvec \<sharp>* C` `distinct_perm p` `set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))`
  ultimately show ?case
    unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_scope \<Psi> P \<pi> M xvec N P' x A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* N" "yvec \<sharp>* P'" "yvec \<sharp>* \<pi>" "x \<sharp> yvec" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P" "yvec \<sharp>* P'" "yvec \<sharp>* xvec"
    using `\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    unfolding residual_inject
    by(drule_tac output_provenance'[where C="(\<Psi>,x,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P,P',xvec)"]) auto
  from `map_option (F_res x) \<pi> = Some (\<langle>(x # A\<^sub>P); zvec, K\<rangle>)`
  have \<pi>': "\<pi> = Some (\<langle>A\<^sub>P; zvec, K\<rangle>)"
    by(induct \<pi>) (auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])
  have "xvec \<sharp>* K'" using \<pi> `xvec \<sharp>* \<pi>` `A\<^sub>P \<sharp>* xvec` `yvec \<sharp>* xvec`
    by(auto simp add: frame_chain_fresh_chain'')
  from \<pi>' have "\<langle>yvec,K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)  
  with `distinct yvec` `distinct zvec` `yvec \<sharp>* zvec`
  obtain p where "set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)" and "distinct_perm p" and peq: "zvec = p \<bullet> yvec" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+
  moreover have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) yvec K' M (\<lparr>\<nu>*xvec\<rparr>N\<prec>'(\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P"
    using c_scope yfs `distinct yvec` using `xvec \<sharp>* K'` unfolding \<pi>
    by(rule_tac r_scope) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_bang \<Psi> P \<pi> M B A\<^sub>P \<Psi>\<^sub>P C zvec K)
  from `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ R_out M B` `A\<^sub>P \<sharp>* P` have "A\<^sub>P \<sharp>* \<pi>"
    by(auto intro!: trans_fresh_provenance)
  obtain yvec K' where
    \<pi>: "\<pi> = Some(\<langle>A\<^sub>P; yvec, K'\<rangle>)" and "distinct yvec" and yfs: "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* B" "yvec \<sharp>* \<pi>" "yvec \<sharp>* A\<^sub>P" "yvec \<sharp>* \<Psi>\<^sub>P" "yvec \<sharp>* C" "yvec \<sharp>* zvec" "yvec \<sharp>* K" "yvec \<sharp>* P"
    using `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ R_out M B` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    by(drule_tac output_provenance'[where C="(\<phi>,Cs,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P)"])
      (auto dest: trans_fresh_provenance)
  with `map_option (F_assert \<circ> push_prov) \<pi> = Some (\<langle>[]; zvec, K\<rangle>)`
  have "\<langle>(A\<^sub>P@yvec), K'\<rangle> = \<langle>zvec, K\<rangle>"
    by(simp add: frame.inject)
  moreover note `yvec \<sharp>* A\<^sub>P` `distinct yvec` `distinct A\<^sub>P` `distinct zvec`
    `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* zvec`
  ultimately obtain p::"name prm" where "set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))" and "distinct_perm p" and peq: "zvec = p\<bullet>(A\<^sub>P@yvec)" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="A\<^sub>P@yvec" and yvec="zvec"]) auto
  from \<pi> `distinct yvec` `yvec \<sharp>* A\<^sub>P` have "\<And> C. Prop C \<Psi> (P \<parallel> !P) yvec K' M B A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>)"
    by(rule_tac c_bang) auto
  moreover from `\<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi> @ R_out M B` have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Some (\<langle>A\<^sub>P; yvec, K'\<rangle>) @ R_out M B"
    unfolding \<pi> by simp
  moreover note `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `guarded P` `\<Psi>\<^sub>P \<simeq> \<one>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* B` `A\<^sub>P \<sharp>* \<pi>` `yvec \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* C` `supp \<Psi>\<^sub>P = {}` `distinct yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* B` `yvec \<sharp>* \<Psi>\<^sub>P``yvec \<sharp>* C`
  ultimately have "Prop C \<Psi> (!P) (A\<^sub>P@yvec) K' M B ([]) (\<one>)"
    by(rule_tac r_bang) (assumption|auto)+
  moreover note `A\<^sub>P \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* M` `yvec \<sharp>* M` `A\<^sub>P \<sharp>* B` `yvec \<sharp>* B` `A\<^sub>P \<sharp>* zvec` `yvec \<sharp>* zvec` `A\<^sub>P \<sharp>* C` `yvec \<sharp>* C` `distinct_perm p` `set p \<subseteq> set(A\<^sub>P@yvec) \<times> set(p\<bullet>(A\<^sub>P@yvec))` `yvec \<sharp>* P`
  ultimately show ?case
    unfolding peq
    by(rule_tac r_prov_alpha) auto
next
  case(c_open \<Psi> P \<pi> M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C zvec K)
  obtain zvec' K' where
    \<pi>: "\<pi> = (\<langle>A\<^sub>P; zvec', K'\<rangle>)" and "distinct zvec'" and yfs: "zvec' \<sharp>* \<Psi>" "zvec' \<sharp>* M" "zvec' \<sharp>* N" "zvec' \<sharp>* P'" "zvec' \<sharp>* \<pi>" "x \<sharp> zvec'" "zvec' \<sharp>* A\<^sub>P" "zvec' \<sharp>* \<Psi>\<^sub>P" "zvec' \<sharp>* C" "zvec' \<sharp>* zvec" "zvec' \<sharp>* K" "zvec' \<sharp>* P" "zvec' \<sharp>* P'" "zvec' \<sharp>* xvec" "zvec' \<sharp>* yvec"
    using `\<Psi> \<rhd> P \<longmapsto> Some \<pi> @ M\<lparr>\<nu>*(xvec @ yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `distinct A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* \<pi>`
    unfolding residual_inject
    by(drule_tac output_provenance'[where C="(\<Psi>,x,C,zvec,K,\<Psi>\<^sub>P,\<pi>,P,P',xvec,yvec)"]) auto
  from `\<lparr>\<nu>x\<rparr>\<pi> = \<langle>(x # A\<^sub>P); zvec, K\<rangle>`
  have \<pi>': "\<pi> = (\<langle>A\<^sub>P; zvec, K\<rangle>)"
    by(auto simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])
  have "xvec \<sharp>* K'" using \<pi> `xvec \<sharp>* \<pi>` `A\<^sub>P \<sharp>* xvec` `zvec' \<sharp>* xvec`
    by(auto simp add: frame_chain_fresh_chain'')
  have "yvec \<sharp>* K'" using \<pi> `yvec \<sharp>* \<pi>` `A\<^sub>P \<sharp>* yvec` `zvec' \<sharp>* yvec`
    by(auto simp add: frame_chain_fresh_chain'')
  from \<pi>' have "\<langle>zvec',K'\<rangle> = \<langle>zvec,K\<rangle>" unfolding \<pi>
    by(auto dest: frame_chain_inject simp add: frame.inject)  
  with `distinct zvec'` `distinct zvec` `zvec' \<sharp>* zvec`
  obtain p where "set p \<subseteq> set zvec' \<times> set(p\<bullet>zvec')" and "distinct_perm p" and peq: "zvec = p \<bullet> zvec'" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq') (assumption|auto)+
  moreover have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) zvec' K' M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N\<prec>'P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    using c_open yfs `distinct zvec'` using `xvec \<sharp>* K'` `yvec \<sharp>* K'` unfolding \<pi>
    by(rule_tac r_open) auto
  ultimately show ?case using yfs unfolding peq
    by(rule_tac r_prov_alpha) auto
qed

lemma comm1_aux:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   N    :: 'a
  and   R'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>R   :: "name list"
  and   \<Psi>\<^sub>R   :: 'b
  and   M    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   A\<^sub>Q   :: "name list"

  assumes R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
  and     FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'"  
  and     QimpP: "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
(*  and     "distinct A\<^sub>P"*)
  and     "distinct A\<^sub>R"
  and     "A\<^sub>R \<sharp>* A\<^sub>P"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
  and     "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* K'"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* R"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* M"
  and     "distinct yvec"
  and     "A\<^sub>R \<sharp>* yvec"
  and     "A\<^sub>R \<sharp>* K'"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* \<Psi>\<^sub>P"
  and     "yvec \<sharp>* K'"
  and     "yvec \<sharp>* R"
  and     "yvec \<sharp>* A\<^sub>P"
  and     "yvec \<sharp>* A\<^sub>Q"
  
  shows "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"  
proof -
  from `A\<^sub>R \<sharp>* yvec` FrR `yvec \<sharp>* R` have "yvec \<sharp>* \<Psi>\<^sub>R"
    by(auto dest: extract_frame_fresh_chain)
  from `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
  obtain \<Psi>' where A: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi>'" and "A\<^sub>R \<sharp>* \<Psi>'"
    by(metis Assertion_stat_eq_refl fresh_comp_chain)
  with R_trans have "\<Psi>' \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" 
    by(rule_tac stat_eq_transition)
  moreover note FrR `distinct A\<^sub>R` `distinct yvec` `A\<^sub>R \<sharp>* yvec`
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'"
    by(blast intro: stat_eq_ent Associativity Assertion_stat_eq_sym)
  moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" using A
    by(blast dest: frame_int_composition Frame_stat_eq_trans Frame_stat_eq_sym)
  with QimpP have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    by(force intro: Frame_stat_eq_imp_compose)
  ultimately show ?thesis
    using `A\<^sub>R \<sharp>* K'` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* \<Psi>`
      `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` (*`distinct A\<^sub>P`*)
      `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* yvec` `A\<^sub>R \<sharp>* K'`
      `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* K'` `yvec \<sharp>* R` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* \<Psi>\<^sub>R`
      (* `A\<^sub>P \<sharp>* zvec` `A\<^sub>R \<sharp>* zvec` `zvec \<sharp>* R` `zvec \<sharp>* P`*)
    unfolding residual_inject
  proof(nominal_induct avoiding: \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K' rule: output_frame_provenance_induct)
    case(c_alpha \<Psi>' R yvec M K A\<^sub>R \<Psi>\<^sub>R p B \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    moreover from `\<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>`
    have "(p \<bullet> \<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>) \<hookrightarrow>\<^sub>F (p \<bullet> \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>)"
      by(rule Frame_stat_imp_closed)
    with `A\<^sub>R \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>'` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* A\<^sub>Q`
      `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
    moreover from `A\<^sub>P \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>P) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "A\<^sub>P \<sharp>* M" by simp
    moreover from `A\<^sub>Q \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>Q) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "A\<^sub>Q \<sharp>* M" by simp
    moreover from `yvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)` have "(p \<bullet> yvec) \<sharp>* \<Psi>\<^sub>R"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* yvec` `(p \<bullet> A\<^sub>R) \<sharp>* yvec` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "yvec \<sharp>* \<Psi>\<^sub>R" by simp
    moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" using c_alpha
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ R_out K' B"
      by simp
    moreover with `(p\<bullet>A\<^sub>R) \<sharp>* R` have "(p\<bullet>A\<^sub>R) \<sharp>* (\<langle>A\<^sub>R; yvec, M\<rangle>)"
      by(auto dest: trans_fresh_provenance)
    ultimately show ?case
      using c_alpha
      by(subst (asm) frame_chain_alpha'[where p=p]) (auto simp add: eqvts frame_chain_fresh_chain'')
  next
    case(c_prov_alpha \<Psi>' R yvec M K B A\<^sub>R \<Psi>\<^sub>R p \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    moreover hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'"
      by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
    moreover from `A\<^sub>P \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>P) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `yvec \<sharp>* A\<^sub>P` `(p \<bullet> yvec) \<sharp>* A\<^sub>P` `set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)` `distinct_perm p`
    have "A\<^sub>P \<sharp>* M" by simp
    moreover from `A\<^sub>Q \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>Q) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `yvec \<sharp>* A\<^sub>Q` `(p \<bullet> yvec) \<sharp>* A\<^sub>Q` `set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)` `distinct_perm p`
    have "A\<^sub>Q \<sharp>* M" by simp
    ultimately show ?case
      by(subst frame_chain_alpha'[symmetric]) (auto dest!: trans_fresh_provenance[where xvec="(p\<bullet>yvec)"] simp add: frame_chain_fresh_chain'')
  next
    case(c_output \<Psi>' M K N R \<Psi> A\<^sub>R \<Psi>\<^sub>R A\<^sub>P K')
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'"
      by(rule_tac stat_eq_ent[OF Identity])
    thus ?case
      by(auto dest: Output simp add: residual_inject)
  next
    case(c_case \<Psi>' R yvec M K B \<phi> Cs A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    from `(A\<^sub>R @ yvec) \<sharp>* (Cases Cs)` `A\<^sub>P \<sharp>* (Cases Cs)`  `A\<^sub>Q \<sharp>* (Cases Cs)` `(\<phi>, R) mem Cs`
    have "A\<^sub>P \<sharp>* R" and "A\<^sub>Q \<sharp>* R" and "yvec \<sharp>* R" and "A\<^sub>R \<sharp>* R" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>Q \<sharp>* \<phi>"
      by auto
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'` `\<Psi>\<^sub>R \<simeq> \<one>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'"
      by (metis Assertion_stat_eq_sym composition_sym stat_eq_ent)
    moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>Q,  \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>`
      moreover from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ R_out K' B"      
      by(rule c_case) fact+
    moreover from `\<Psi>' \<turnstile> \<phi>` have "\<Psi>' \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
    with `A\<^sub>Q \<sharp>* \<phi>` have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frame_impI)
    with `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>` have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
      by(simp add: Frame_stat_imp_def)
    with `A\<^sub>P \<sharp>* \<phi>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> \<phi>"  by(force dest: frame_impE)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity)
    ultimately show ?case using `(\<phi>, R) mem Cs` `guarded R`
      by(drule_tac Case) auto
  next
    case(c_par1 \<Psi>' \<Psi>\<^sub>R\<^sub>2 R\<^sub>1 yvec M K xvec N R\<^sub>1' A\<^sub>R\<^sub>2 R\<^sub>2 A\<^sub>R\<^sub>1 \<Psi>\<^sub>R\<^sub>1 \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    have FrR2: "extract_frame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>" by fact
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'` have "((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> K'"
      by(metis stat_eq_ent Associativity Composition Commutativity)
    moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>`
      moreover have  "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    moreover from `A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P` `A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)` `extract_frame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>` FrR2 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
      by(force dest: extract_frame_fresh_chain)+
    moreover note `distinct yvec`    
    ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>1; yvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R\<^sub>1'" using c_par1
      apply(subst residual_inject)
      by(rule_tac c_par1) (assumption | simp | force)+
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> R\<^sub>1 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>1; yvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R\<^sub>1'"
      by(metis associativity_sym stat_eq_transition)
    thus ?case using c_par1
      by(drule_tac Par1[where A\<^sub>Q=A\<^sub>R\<^sub>2]) (auto simp add: residual_inject)
  next
    case(c_par2 \<Psi>' \<Psi>\<^sub>R\<^sub>1 R\<^sub>2 K yvec M xvec N R\<^sub>2' A\<^sub>R\<^sub>1 R\<^sub>1 A\<^sub>R\<^sub>2 \<Psi>\<^sub>R\<^sub>2 \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    have FrR1: "extract_frame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>" by fact
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'` have "((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"
      by(metis stat_eq_ent Associativity Composition Commutativity)
    moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>`
      moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    moreover from `A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P` `A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)` `extract_frame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>` FrR1 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
      by(force dest: extract_frame_fresh_chain)+
    moreover note `distinct yvec`    
    ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>2; yvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R\<^sub>2'" using c_par2
      apply(subst residual_inject)
      by(rule_tac c_par2) (assumption | simp | force)+
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> R\<^sub>2 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>2; yvec, M\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R\<^sub>2'"
      by(metis associativity_sym stat_eq_transition)
    thus ?case using c_par2
      by(drule_tac Par2[where A\<^sub>P=A\<^sub>R\<^sub>1]) (auto simp add: frame_chain_append residual_inject)
  next
    case(c_open \<Psi>' R zvec K M xvec yvec N R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; zvec, K\<rangle>) @ K'\<lparr>\<nu>*(xvec @ yvec)\<rparr>\<langle>N\<rangle> \<prec> R'"
      apply(subst residual_inject)
      by(rule_tac c_open) (assumption|simp)+
    thus ?case using `x \<sharp> K'` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> xvec` `x \<sharp> yvec` `x \<in> supp N`
      by(drule_tac Open) (auto simp add: residual_inject)
  next
    case(c_scope \<Psi>' R zvec K M xvec N R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; zvec, K\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      apply(subst residual_inject)      
      by(rule_tac c_scope) (assumption|simp)+
    thus ?case using `x \<sharp> K'` `x \<sharp> N` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> xvec`
      by(drule_tac Scope) (auto simp add: residual_inject)
  next
    case(c_bang \<Psi>' R yvec M K B A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'` `\<Psi>\<^sub>R \<simeq> \<one>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'"
      by (metis Assertion_stat_eq_sym composition_sym stat_eq_ent Identity)
    moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
    proof -
      from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>`
      moreover  from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ R_out K' B"
      using c_bang
      by(rule_tac c_bang) (assumption|simp|force)+
    thus ?case using `guarded R`
      by(drule_tac Bang) auto
  qed
qed

lemma comm2_aux:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   N    :: 'a
  and   R'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>R   :: "name list"
  and   \<Psi>\<^sub>R   :: 'b
  and   M    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   A\<^sub>Q   :: "name list"

  assumes R_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'"
  and     FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"  
  and     QimpP: "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
(*  and     "distinct A\<^sub>P"*)
  and     "distinct A\<^sub>R"
  and     "A\<^sub>R \<sharp>* A\<^sub>P"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
  and     "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* K'"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* R"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* M"
  and     "distinct yvec"
  and     "A\<^sub>R \<sharp>* yvec"
  and     "A\<^sub>R \<sharp>* K'"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* \<Psi>\<^sub>P"
  and     "yvec \<sharp>* K'"
  and     "yvec \<sharp>* R"
  and     "yvec \<sharp>* A\<^sub>P"
  and     "yvec \<sharp>* A\<^sub>Q"
  
  shows "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"  
proof -
  from `A\<^sub>R \<sharp>* yvec` FrR `yvec \<sharp>* R` have "yvec \<sharp>* \<Psi>\<^sub>R"
    by(auto dest: extract_frame_fresh_chain)
  from `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>\<^sub>Q`
  obtain \<Psi>' where A: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi>'" and "A\<^sub>R \<sharp>* \<Psi>'"
    by(metis Assertion_stat_eq_refl fresh_comp_chain)
  with R_trans have "\<Psi>' \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; yvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'" 
    by(rule_tac stat_eq_transition)
  moreover note FrR `distinct A\<^sub>R` `distinct yvec` `A\<^sub>R \<sharp>* yvec`
  moreover from `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"
    by(blast intro: stat_eq_ent Associativity Assertion_stat_eq_sym)
  moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" using A
    by(blast dest: frame_int_composition Frame_stat_eq_trans Frame_stat_eq_sym)
  with QimpP have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    by(force intro: Frame_stat_eq_imp_compose)
  ultimately show ?thesis
    using `A\<^sub>R \<sharp>* K'` `A\<^sub>R \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* \<Psi>`
      `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` (*`distinct A\<^sub>P`*)
      `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* yvec` `A\<^sub>R \<sharp>* K'`
      `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* K'` `yvec \<sharp>* R` `yvec \<sharp>* A\<^sub>P` `yvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* \<Psi>\<^sub>R`
      (* `A\<^sub>P \<sharp>* zvec` `A\<^sub>R \<sharp>* zvec` `zvec \<sharp>* R` `zvec \<sharp>* P`*)
  proof(nominal_induct avoiding: \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K' rule: input_frame_provenance_induct)
    case(c_alpha \<Psi>' R yvec M K N R' A\<^sub>R \<Psi>\<^sub>R p \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    moreover from `\<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>`
    have "(p \<bullet> \<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>) \<hookrightarrow>\<^sub>F (p \<bullet> \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>)"
      by(rule Frame_stat_imp_closed)
    with `A\<^sub>R \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P` `A\<^sub>R \<sharp>* \<Psi>'` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'` `A\<^sub>R \<sharp>* \<Psi>\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P` `A\<^sub>R \<sharp>* A\<^sub>Q`
      `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q` `A\<^sub>R \<sharp>* \<Psi>` `(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
    moreover from `A\<^sub>P \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>P) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* A\<^sub>P` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "A\<^sub>P \<sharp>* M" by simp
    moreover from `A\<^sub>Q \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>Q) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* A\<^sub>Q` `(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "A\<^sub>Q \<sharp>* M" by simp
    moreover from `yvec \<sharp>* (p\<bullet>\<Psi>\<^sub>R)` have "(p \<bullet> yvec) \<sharp>* \<Psi>\<^sub>R"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `A\<^sub>R \<sharp>* yvec` `(p \<bullet> A\<^sub>R) \<sharp>* yvec` `set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)` `distinct_perm p`
    have "yvec \<sharp>* \<Psi>\<^sub>R" by simp
    moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M" using c_alpha
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      by simp
    moreover with `(p\<bullet>A\<^sub>R) \<sharp>* R` have "(p\<bullet>A\<^sub>R) \<sharp>* (\<langle>A\<^sub>R; yvec, M\<rangle>)"
      by(auto dest: trans_fresh_provenance)
    ultimately show ?case
      using c_alpha
      by(subst (asm) frame_chain_alpha'[where p=p]) (auto simp add: eqvts frame_chain_fresh_chain'')
  next
    case(c_prov_alpha \<Psi>' R yvec M K N R' A\<^sub>R \<Psi>\<^sub>R p \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    moreover hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"
      by(subst perm_bool[where pi=p,symmetric]) (simp add: eqvts)
    moreover from `A\<^sub>P \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>P) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `yvec \<sharp>* A\<^sub>P` `(p \<bullet> yvec) \<sharp>* A\<^sub>P` `set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)` `distinct_perm p`
    have "A\<^sub>P \<sharp>* M" by simp
    moreover from `A\<^sub>Q \<sharp>* (p\<bullet>M)` have "(p \<bullet> A\<^sub>Q) \<sharp>* M"
      using `distinct_perm p`
      by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
    with `yvec \<sharp>* A\<^sub>Q` `(p \<bullet> yvec) \<sharp>* A\<^sub>Q` `set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)` `distinct_perm p`
    have "A\<^sub>Q \<sharp>* M" by simp
    ultimately show ?case
      by(subst frame_chain_alpha'[symmetric]) (auto dest!: trans_fresh_provenance[where xvec="(p\<bullet>yvec)"] simp add: frame_chain_fresh_chain'')
  next
    case(c_input \<Psi>' M K xvec N Tvec R \<Psi> A\<^sub>R \<Psi>\<^sub>R A\<^sub>P K')
    thus ?case
      by(auto intro: Input dest: stat_eq_ent[OF Identity])
  next
    case(c_case \<Psi>' R yvec M K N R' \<phi> Cs A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    from `(A\<^sub>R @ yvec) \<sharp>* (Cases Cs)` `A\<^sub>P \<sharp>* (Cases Cs)`  `A\<^sub>Q \<sharp>* (Cases Cs)` `(\<phi>, R) mem Cs`
    have "A\<^sub>P \<sharp>* R" and "A\<^sub>Q \<sharp>* R" and "yvec \<sharp>* R" and "A\<^sub>R \<sharp>* R" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>Q \<sharp>* \<phi>"
      by auto
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M` `\<Psi>\<^sub>R \<simeq> \<one>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> M"
      by (metis Assertion_stat_eq_sym composition_sym stat_eq_ent)
    moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>Q,  \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>`
      moreover from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      by(rule c_case) fact+
    moreover from `\<Psi>' \<turnstile> \<phi>` have "\<Psi>' \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity Assertion_stat_eq_sym)
    with `A\<^sub>Q \<sharp>* \<phi>` have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frame_impI)
    with `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>` have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
      by(simp add: Frame_stat_imp_def)
    with `A\<^sub>P \<sharp>* \<phi>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> \<phi>"  by(force dest: frame_impE)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(blast intro: stat_eq_ent Identity)
    ultimately show ?case using `(\<phi>, R) mem Cs` `guarded R`
      by(drule_tac Case) auto
  next
    case(c_par1 \<Psi>' \<Psi>\<^sub>R\<^sub>2 R\<^sub>1 yvec M K N R\<^sub>1' A\<^sub>R\<^sub>2 R\<^sub>2 A\<^sub>R\<^sub>1 \<Psi>\<^sub>R\<^sub>1 \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    have FrR2: "extract_frame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>" by fact
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> K' \<leftrightarrow> M` have "((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> K' \<leftrightarrow> M"
      by(metis stat_eq_ent Associativity Composition Commutativity)
    moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>`
      moreover have  "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    moreover from `A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P` `A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)` `extract_frame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>` FrR2 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
      by(force dest: extract_frame_fresh_chain)+
    moreover note `distinct yvec`    
    ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>1; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R\<^sub>1'" using c_par1
      by(rule_tac c_par1) (assumption | simp | force)+
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> R\<^sub>1 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>1; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R\<^sub>1'"
      by(metis associativity_sym stat_eq_transition)
    thus ?case using c_par1
      by(drule_tac Par1[where A\<^sub>Q=A\<^sub>R\<^sub>2]) auto
  next
    case(c_par2 \<Psi>' \<Psi>\<^sub>R\<^sub>1 R\<^sub>2 yvec M K N R\<^sub>2' A\<^sub>R\<^sub>1 R\<^sub>1 A\<^sub>R\<^sub>2 \<Psi>\<^sub>R\<^sub>2 \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    have FrR1: "extract_frame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>" by fact
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> K' \<leftrightarrow> M` have "((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> K' \<leftrightarrow> M"
      by(metis stat_eq_ent Associativity Composition Commutativity)
    moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>`
      moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
	by(metis Associativity Composition Commutativity Assertion_stat_eq_trans Assertion_stat_eq_sym frame_nil_stat_eq frame_res_chain_pres)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed    
    moreover from `A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P` `A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)` `extract_frame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>` FrR1 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
      by(force dest: extract_frame_fresh_chain)+
    moreover note `distinct yvec`    
    ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>2; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R\<^sub>2'" using c_par2
      by(rule_tac c_par2) (assumption | simp | force)+
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> R\<^sub>2 \<longmapsto>Some (\<langle>A\<^sub>R\<^sub>2; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R\<^sub>2'"
      by(metis associativity_sym stat_eq_transition)
    thus ?case using c_par2
      by(drule_tac Par2[where A\<^sub>P=A\<^sub>R\<^sub>1]) (auto simp add: frame_chain_append)
  next
    case(c_scope \<Psi>' R zvec K M N R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto> Some (\<langle>A\<^sub>R; zvec, K\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      by(rule_tac c_scope) (assumption|simp)+
    thus ?case using `x \<sharp> K'` `x \<sharp> N` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P`
      by(drule_tac Scope) auto
  next
    case(c_bang \<Psi>' R yvec M K N R' A\<^sub>R \<Psi>\<^sub>R \<Psi> A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q K')
    from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M` `\<Psi>\<^sub>R \<simeq> \<one>` have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> K' \<leftrightarrow> M"
      by (metis Assertion_stat_eq_sym composition_sym stat_eq_ent Identity)
    moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
    proof -
      from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      moreover note `\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>`
      moreover  from `\<Psi>\<^sub>R \<simeq> \<one>` have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
	by(metis Identity Commutativity Assertion_stat_eq_sym Composition frame_res_chain_pres frame_nil_stat_eq Assertion_stat_eq_trans)
      ultimately show ?thesis by(rule Frame_stat_eq_imp_compose)
    qed
    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto> Some (\<langle>A\<^sub>R; yvec, M\<rangle>) @ K'\<lparr>N\<rparr> \<prec> R'"
      using c_bang
      by(rule_tac c_bang) (assumption|simp|force)+
    thus ?case using `guarded R`
      by(drule_tac Bang) auto
  qed
qed

lemma input_provenance'':
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; xvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "distinct xvec"
  and "xvec \<sharp>* \<Psi>"
  and "xvec \<sharp>* \<Psi>\<^sub>P"
  and "xvec \<sharp>* M"
  and "A\<^sub>P \<sharp>* xvec"
  shows "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
proof -
  from Trans `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M`
  obtain xvec' K' where feq: "(\<langle>A\<^sub>P; xvec, K\<rangle>) = (\<langle>A\<^sub>P; xvec', K'\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>" "distinct xvec'" and "xvec' \<sharp>* \<Psi>" and "xvec' \<sharp>* M" and "xvec' \<sharp>* P" and "xvec' \<sharp>* N" and "xvec' \<sharp>* P'" and "xvec' \<sharp>* A\<^sub>P" and "xvec' \<sharp>* \<Psi>\<^sub>P" and "xvec' \<sharp>* xvec" and "xvec' \<sharp>* K" and "A\<^sub>P \<sharp>* xvec'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
    by(drule_tac input_provenance'[where C="(A\<^sub>P,\<Psi>\<^sub>P,xvec,K)"]) (auto simp add: frame_chain_fresh_chain)
  from feq have "(\<langle>xvec, K\<rangle>) = (\<langle>xvec', K'\<rangle>)"
    by(metis frame.inject frame_chain_inject')
  with `xvec' \<sharp>* xvec` `distinct xvec` `distinct xvec'`
  obtain p where p: "set p \<subseteq> set xvec' \<times> set(p\<bullet>xvec')" "distinct_perm p" and freqs: "xvec = p\<bullet>xvec'" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="xvec'" and yvec="xvec"]) auto
  with `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'` `xvec \<sharp>* \<Psi>` `xvec' \<sharp>* \<Psi>` `xvec \<sharp>* M` `xvec' \<sharp>* M` `xvec \<sharp>* \<Psi>\<^sub>P` `xvec' \<sharp>* \<Psi>\<^sub>P`
  show ?thesis
    unfolding freqs
    by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
qed

lemma output_provenance'':
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; xvec, K\<rangle>) @ R_out M B"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "distinct xvec"
  and "xvec \<sharp>* \<Psi>"
  and "xvec \<sharp>* \<Psi>\<^sub>P"
  and "xvec \<sharp>* M"
  and "A\<^sub>P \<sharp>* xvec"
  shows "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
proof -
  from Trans `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M`
  obtain xvec' K' where feq: "(\<langle>A\<^sub>P; xvec, K\<rangle>) = (\<langle>A\<^sub>P; xvec', K'\<rangle>)" and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>" "distinct xvec'" and "xvec' \<sharp>* \<Psi>" and "xvec' \<sharp>* M" and "xvec' \<sharp>* P" and "xvec' \<sharp>* B" and "xvec' \<sharp>* A\<^sub>P" and "xvec' \<sharp>* \<Psi>\<^sub>P" and "xvec' \<sharp>* xvec" and "xvec' \<sharp>* K" and "A\<^sub>P \<sharp>* xvec'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M"
    by(drule_tac output_provenance'[where C="(A\<^sub>P,\<Psi>\<^sub>P,xvec,K)"]) (auto simp add: frame_chain_fresh_chain)
  from feq have "(\<langle>xvec, K\<rangle>) = (\<langle>xvec', K'\<rangle>)"
    by(metis frame.inject frame_chain_inject')
  with `xvec' \<sharp>* xvec` `distinct xvec` `distinct xvec'`
  obtain p where p: "set p \<subseteq> set xvec' \<times> set(p\<bullet>xvec')" "distinct_perm p" and freqs: "xvec = p\<bullet>xvec'" "K = p\<bullet>K'"
    by(rule_tac frame_chain_eq'[where xvec="xvec'" and yvec="xvec"]) auto
  with `\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M` `xvec \<sharp>* \<Psi>` `xvec' \<sharp>* \<Psi>` `xvec \<sharp>* M` `xvec' \<sharp>* M` `xvec \<sharp>* \<Psi>\<^sub>P` `xvec' \<sharp>* \<Psi>\<^sub>P`
  show ?thesis
    unfolding freqs
    by(subst perm_bool[where pi=p, symmetric]) (simp add: eqvts)
qed

end

end