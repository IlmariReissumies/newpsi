theory Sim_Struct_Cong
  imports Simulation
begin

lemma partition_list_left:
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem xs"
  and     "distinct(xs@ys)"

  obtains zs where "xs = xs'@y#zs" and "ys'=zs@ys"
using assms
by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma partition_list_right:
 
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem ys"
  and     "distinct(xs@ys)"

  obtains zs where "xs' = xs@zs" and "ys=zs@y#ys'"
using assms
by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

context env begin

lemma res_comm:
  fixes \<Psi>   :: 'b
  and   x   :: name
  and   y   :: name
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   P   :: "('a, 'b, 'c) psi"
  
  assumes "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     R1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"
  and     R2: "\<And>\<Psi>' a b Q. \<lbrakk>a \<sharp> \<Psi>'; b \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>a\<rparr>(\<lparr>\<nu>b\<rparr>Q), \<lparr>\<nu>b\<rparr>(\<lparr>\<nu>a\<rparr>Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(case_tac "x=y")
  assume "x = y"
  thus ?thesis using R1
    by(force intro: reflexive)
next
  assume "x \<noteq> y"
  note `eqvt Rel`
  moreover from `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "[x, y] \<sharp>* \<Psi>" by(simp add: fresh_star_def)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" by(simp add: abs_fresh)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_chain_fresh[where C="(x, y)"])
    case(c_sim \<pi> \<alpha> P')
    from `bn \<alpha> \<sharp>* (x, y)` `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P))` have "x \<sharp> bn \<alpha>" and "y \<sharp> bn \<alpha>" and "bn \<alpha> \<sharp>* P" by simp+
    from `[x, y] \<sharp>* \<alpha>` have "x \<sharp> \<alpha>" and "y \<sharp> \<alpha>" by simp+
    from `[x, y] \<sharp>* P'` have "x \<sharp> P'" and "y \<sharp> P'" by simp+
    from `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P" by(simp add: abs_fresh)
    with `\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> \<alpha>` `y \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>`
    show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `y \<sharp> \<alpha>`
    proof(induct rule: res_cases')
      case(c_open M \<pi>' yvec1 yvec2 y' N P')
      from `yvec1 \<sharp>* yvec2` `distinct yvec1` `distinct yvec2` have "distinct(yvec1@yvec2)" by auto
      from `x \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> M" and "x \<sharp> yvec1" and "x \<noteq> y'" and "x \<sharp> yvec2" and "x \<sharp> N"
	by simp+
      from `y \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>` have "y \<sharp> M" and "y \<sharp> yvec1" and "y \<sharp> yvec2"
	by simp+
      from `\<Psi> \<rhd> ([(y, y')] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>Some([(y, y')] \<bullet> \<pi>') @ M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<noteq> y` `x \<noteq> y'`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>([(y, y')] \<bullet> P) \<longmapsto>Some([(y, y')] \<bullet> \<pi>') @ M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
      moreover note `x \<sharp> \<Psi>`
      moreover from `x \<sharp> N` `x \<sharp> yvec1` `x \<sharp> yvec2` `x \<sharp> M` have "x \<sharp> M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>" by simp
      moreover note `x \<sharp> P'`
      moreover from `yvec1 \<sharp>* \<Psi>` `yvec2 \<sharp>* \<Psi>` have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      moreover from `yvec1 \<sharp>* \<lparr>\<nu>x\<rparr>P` `yvec2 \<sharp>* \<lparr>\<nu>x\<rparr>P` `y \<sharp> yvec1` `y' \<sharp> yvec1` `y \<sharp> yvec2` `y' \<sharp> yvec2` `x \<sharp> yvec1` `x \<sharp> yvec2`
      have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* ([(y, y')] \<bullet> P)" by simp
      moreover from `yvec1 \<sharp>* M` `yvec2 \<sharp>* M` have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>)"
	by simp
      moreover have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = yvec1@yvec2" by simp
      moreover have "subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some M" by simp
      moreover have "object(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some N" by simp
      ultimately show ?case 
      proof(induct rule: res_cases')
	case(c_open M' \<pi>'' xvec1 xvec2 x' N' P')
	from `bn(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = yvec1 @ yvec2` have "yvec1@yvec2 = xvec1@x'#xvec2" by simp
	from `subject(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some M` have "M = M'" by simp
	from `object(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some N` have "N = N'" by simp
	from `x \<sharp> yvec1` `x \<sharp> yvec2` `y' \<sharp> yvec1` `y' \<sharp> yvec2` `y \<sharp> yvec1` `y \<sharp> yvec2`
	have "x \<sharp> (yvec1@yvec2)" and "y \<sharp> (yvec1@yvec2)" and "y' \<sharp> (yvec1@yvec2)" by simp+
	with `yvec1@yvec2 = xvec1@x'#xvec2`
	have "x \<sharp> xvec1" and "x \<noteq> x'" and "x \<sharp> xvec2" and "y \<sharp> xvec1" and "y \<noteq> x'" and "y \<sharp> xvec2"
	  and "y' \<sharp> xvec1" and "x' \<noteq> y'" and "y' \<sharp> xvec2"
	  by auto

	show ?case
	proof(case_tac "x' mem yvec1")
	  assume "x' mem yvec1"
	
	  with `yvec1@yvec2 = xvec1@x'#xvec2` `distinct (yvec1@yvec2)`
	  obtain xvec2' where Eq1: "yvec1=xvec1@x'#xvec2'"
                          and Eq: "xvec2=xvec2'@yvec2"
	    by(rule_tac partition_list_left)
	  from `\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>Some ([(x, x')] \<bullet> \<pi>'') @ M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> xvec1` `y' \<sharp> xvec2` Eq `M=M'` `N = N'`
	  have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>Some(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>'')) @ M'\<lparr>\<nu>*((xvec1@xvec2')@y'#yvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'"
	    by(rule_tac Open) auto
	  then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>Some(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
	    using `x' \<in> supp N'` `x' \<sharp> \<Psi>` `x' \<sharp> M'` `x' \<sharp> xvec1` `x' \<sharp> xvec2` `x' \<noteq> y'` Eq `M=M'` `N=N'`
	    by(rule_tac Open) auto
	  with `x' \<noteq> y'` `x \<noteq> y'` `x' \<sharp> [(y, y')] \<bullet> P`
	  have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>Some(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
	    by(subst alpha_res[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
	  with Eq1 `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'` R1 show ?case
	    by(force simp add: alpha_res abs_fresh)
	next
	  assume "\<not>x' mem yvec1"
	  hence "x' \<sharp> yvec1" by(simp add: fresh_def)
	  from `\<not>x' mem yvec1` `yvec1@yvec2 = xvec1@x'#xvec2`
	  have "x' mem yvec2"
	    by(force simp add: append_eq_append_conv2 append_eq_Cons_conv
                                  fresh_list_append fresh_list_cons)
	  with `yvec1@yvec2 = xvec1@x'#xvec2` `distinct (yvec1@yvec2)`
	  obtain xvec2' where Eq: "xvec1=yvec1@xvec2'"
                          and Eq1: "yvec2=xvec2'@x'#xvec2"
	    by(rule_tac partition_list_right)
	  from `\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>Some([(x, x')] \<bullet> \<pi>'') @ M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> xvec1` `y' \<sharp> xvec2` Eq `M=M'` `N = N'`
	  have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>Some(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>'')) @ M'\<lparr>\<nu>*(yvec1@y'#xvec2'@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'" 
	    by(rule_tac Open) (assumption | simp)+
	  then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>Some(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
	    using `x' \<in> supp N'` `x' \<sharp> \<Psi>` `x' \<sharp> M'` `x' \<sharp> xvec1` `x' \<sharp> xvec2` `x' \<noteq> y'` Eq `M=M'` `N=N'`
	    by(rule_tac Open) auto
	  with `x' \<noteq> y'` `x \<noteq> y'` `x' \<sharp> [(y, y')] \<bullet> P`
	  have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>Some(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
	    by(subst alpha_res[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
	  with Eq1 `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'` R1 show ?case
	    by(force simp add: alpha_res abs_fresh)
	qed
      next
	case(c_res \<pi>'' P')
        from `Some ([(y, y')] \<bullet> \<pi>') = map_option (F_res x) \<pi>''`
        obtain \<pi>''' where \<pi>'': "\<pi>'' = Some \<pi>'''"
          by(induct \<pi>'') auto
	from `\<Psi> \<rhd> ([(y, y')] \<bullet> P) \<longmapsto>\<pi>'' @ M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `y' \<in> supp N` `y' \<sharp> \<Psi>` `y' \<sharp> M` `y' \<sharp> yvec1` `y' \<sharp> yvec2`
	have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P) \<longmapsto>Some(\<lparr>\<nu>y'\<rparr>\<pi>''') @ M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
          unfolding \<pi>''
          by(rule_tac Open)
	with `y' \<sharp> \<lparr>\<nu>x\<rparr>P` `x \<noteq> y'`have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>Some(\<lparr>\<nu>y'\<rparr>\<pi>''') @ M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: alpha_res abs_fresh)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>Some(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>\<pi>''')) @ M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> yvec1` `x \<noteq> y'` `x \<sharp> yvec2` `x \<sharp> N`
	  by(drule_tac Scope) auto
	moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule R1)
	ultimately show ?case by blast
      qed
    next
      case(c_res \<pi>' P')
      from `x \<sharp> \<lparr>\<nu>y\<rparr>P'` `x \<noteq> y` have "x \<sharp> P'" by(simp add: abs_fresh)
      with `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
      show ?case using `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `y \<sharp> \<alpha>`
      proof(induct rule: res_cases')
	case(c_open M \<pi>'' xvec1 xvec2 x' N P')
	from `y \<sharp> M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle>` have "y \<noteq> x'" and "y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>" by simp+
	from `\<Psi> \<rhd> ([(x, x')] \<bullet> P) \<longmapsto>Some ([(x, x')] \<bullet> \<pi>'') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>`
	have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P) \<longmapsto>Some (\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
	  by(drule_tac Scope) auto
	hence "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P)) \<longmapsto>Some (\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
	  using `x' \<in> supp N` `x' \<sharp> \<Psi>` `x' \<sharp> M` `x' \<sharp> xvec1` `x' \<sharp> xvec2`
	  by(rule Open)
	with `y \<noteq> x'` `x \<noteq> y` `x' \<sharp> P` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>Some (\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
	  by(subst alpha_res[where y=x']) (simp add: abs_fresh eqvts calc_atm)+
	moreover have "(\<Psi>, \<lparr>\<nu>y\<rparr>P', \<lparr>\<nu>y\<rparr>P') \<in> Rel" by(rule R1)
	ultimately show ?case by blast
      next
	case(c_res \<pi>'' P')
	from `\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'` `y \<sharp> \<Psi>` `y \<sharp> \<alpha>`
	have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>map_option (F_res y) \<pi>'' @ \<alpha> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(rule Scope)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>map_option (F_res x) (map_option (F_res y) \<pi>'') @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P')" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
	  by(rule Scope)
	moreover from `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P'), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P')) \<in> Rel"
	  by(rule R2)
	ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma par_assoc_left:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   R   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' S T U. (\<Psi>, (S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and     C2: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* S\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>((S \<parallel> T) \<parallel> U), S \<parallel> (\<lparr>\<nu>*xvec\<rparr>(T \<parallel> U))) \<in> Rel"
  and     C3: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* U\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*xvec\<rparr>(S \<parallel> T)) \<parallel> U, \<lparr>\<nu>*xvec\<rparr>(S \<parallel> (T \<parallel> U))) \<in> Rel"
  and     C4: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> PQR) 
  from `bn \<alpha> \<sharp>* (P \<parallel> Q \<parallel> R)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  hence "bn \<alpha> \<sharp>* (Q \<parallel> R)" by simp
  with `\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<pi> @ \<alpha> \<prec> PQR` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: par_cases[where C = "(\<Psi>, P, Q, R, \<alpha>)"])
    case(c_par1 P' \<pi>' A\<^sub>Q\<^sub>R \<Psi>\<^sub>Q\<^sub>R)
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and  "A\<^sub>Q\<^sub>R \<sharp>* R"
      by simp+
    with `extract_frame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R`
    obtain A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R where "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" and FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and  FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
                           and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac merge_frameE) (auto dest: extract_frame_fresh_chain)

    from `A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* \<alpha>`
    have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* \<alpha>"
      by simp+

    from `\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` `\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'"
      by(metis stat_eq_transition Associativity Commutativity Composition)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto> append_at_end_prov_option \<pi>' A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)" using FrQ `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>append_at_end_prov_option(append_at_end_prov_option \<pi>' A\<^sub>Q) A\<^sub>R @ \<alpha> \<prec> ((P' \<parallel> Q) \<parallel> R)" using FrR `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
      by(rule_tac Par1) auto
    moreover have "(\<Psi>, (P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 QR \<pi>' A\<^sub>P \<Psi>\<^sub>P)
    from `A\<^sub>P \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "A\<^sub>P \<sharp>* \<alpha>"
      by simp+
    have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    with `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" by(auto dest: extract_frame_fresh_chain)
    with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    with `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<pi>' @ \<alpha> \<prec> QR`
    show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* R` `bn \<alpha> \<sharp>* subject \<alpha>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R`
    proof(induct rule: par_cases_subject[where C = "(A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)"])
      case(c_par1 \<pi>'' Q' A\<^sub>R \<Psi>\<^sub>R)
      from `A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
	by simp+
      from `A\<^sub>P \<sharp>* R` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi>'' @ \<alpha> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi>'' @ \<alpha> \<prec> Q'" 
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi>'' A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')"
	using FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
	by(rule_tac Par2) (assumption | force)+
      hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>append_at_end_prov_option(append_at_front_prov_option \<pi>'' A\<^sub>P) A\<^sub>R @ \<alpha> \<prec> ((P \<parallel> Q') \<parallel> R)"
	using `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `bn \<alpha> \<sharp>* R` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* \<alpha>`
	by(rule_tac Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(c_par2 \<pi>'' R' A\<^sub>Q \<Psi>\<^sub>Q)
      from `A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>"
	by simp+
      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from `A\<^sub>P \<sharp>* Q` FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<pi>'' @ \<alpha> \<prec> R'`
      have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<pi>'' @ \<alpha> \<prec> R'"
	by(blast intro: stat_eq_transition Associativity)
      moreover from FrP FrQ `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q`  `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` 
      have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> " by simp
      moreover from `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
      moreover from `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* R" by simp
      moreover from `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<alpha>" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>append_at_front_prov_option \<pi>'' (A\<^sub>P@A\<^sub>Q) @ \<alpha> \<prec> ((P \<parallel> Q) \<parallel> R')"
	by(rule Par2)
      moreover have "(\<Psi>, (P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(c_comm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R yvec zvec)
      from `A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+
      from `yvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "yvec \<sharp>* A\<^sub>P" and "yvec \<sharp>* P" and "yvec \<sharp>* Q" and "yvec \<sharp>* \<Psi>" by simp+
      from `zvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "zvec \<sharp>* A\<^sub>P" and "zvec \<sharp>* P" and "zvec \<sharp>* Q" and "zvec \<sharp>* \<Psi>" by simp+      

      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(drule_tac extract_frame_fresh_chain) auto
      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` `A\<^sub>P \<sharp>* R` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* K` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
	by(rule_tac output_fresh_chain_derivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option(Some (\<langle>A\<^sub>Q; yvec, K\<rangle>)) A\<^sub>P @ M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N`
	by(rule_tac Par2) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>Some (\<langle>(A\<^sub>P @ A\<^sub>Q); yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')"
        by(simp add: frame_chain_append)
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by simp
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
	by(metis stat_eq_transition Associativity)
      moreover note `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover have "yvec \<sharp>* \<Psi>\<^sub>P" using `yvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `yvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "yvec \<sharp>* \<Psi>\<^sub>Q" using `yvec \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `yvec \<sharp>* Q`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>P" using `zvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `zvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>Q" using `zvec \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `zvec \<sharp>* Q`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R" using `zvec \<sharp>* A\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `zvec \<sharp>* R`
        by(auto dest: extract_frame_fresh_chain)      
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
          `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* P` `xvec \<sharp>* Q`
        `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* R` `zvec \<sharp>* R` `yvec \<sharp>* P` `zvec \<sharp>* P` `yvec \<sharp>* Q` `zvec \<sharp>* Q`
	by(rule_tac Comm1) (assumption|auto)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
	by(rule C2)
      ultimately show ?case by blast
    next
      case(c_comm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R yvec zvec) 
      from `A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)`
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from `A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from `xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+
      from `yvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "yvec \<sharp>* A\<^sub>P" and "yvec \<sharp>* P" and "yvec \<sharp>* Q" and "yvec \<sharp>* \<Psi>" by simp+
      from `zvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)` have "zvec \<sharp>* A\<^sub>P" and "zvec \<sharp>* P" and "zvec \<sharp>* Q" and "zvec \<sharp>* \<Psi>" by simp+            

      have FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh_chain) auto
      have FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with `A\<^sub>P \<sharp>* R` `A\<^sub>R \<sharp>* A\<^sub>P` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(drule_tac extract_frame_fresh_chain) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` `A\<^sub>P \<sharp>* Q` `xvec \<sharp>* A\<^sub>P` `xvec \<sharp>* M` `distinct xvec` have "A\<^sub>P \<sharp>* N" 
	by(rule_tac output_fresh_chain_derivative) auto

      from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option (Some (\<langle>A\<^sub>Q; yvec, K\<rangle>)) A\<^sub>P @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<Psi>\<^sub>R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* N` `xvec \<sharp>* P` `xvec \<sharp>* A\<^sub>P`
	by(rule_tac Par2) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>Some (\<langle>(A\<^sub>P @ A\<^sub>Q); yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
        by(simp add: frame_chain_append)
      moreover from FrP FrQ `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
	by simp+
      moreover from  `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'"
	by(metis stat_eq_transition Associativity)
      moreover note `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      moreover have "yvec \<sharp>* \<Psi>\<^sub>P" using `yvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `yvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "yvec \<sharp>* \<Psi>\<^sub>Q" using `yvec \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `yvec \<sharp>* Q`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>P" using `zvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `zvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>Q" using `zvec \<sharp>* A\<^sub>Q` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `zvec \<sharp>* Q`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R" using `zvec \<sharp>* A\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `zvec \<sharp>* R`
        by(auto dest: extract_frame_fresh_chain)            
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>R \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>R \<sharp>* R`
          `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>R \<sharp>* K` `A\<^sub>R \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* A\<^sub>R` `xvec \<sharp>* R`
        `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* R` `zvec \<sharp>* R` `yvec \<sharp>* P` `zvec \<sharp>* P` `yvec \<sharp>* Q` `zvec \<sharp>* Q`        
	by(rule_tac Comm2) (assumption | auto)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
	by(rule C2)
      ultimately show ?case by blast
    qed
  next
    case(c_comm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P K xvec QR' A\<^sub>Q\<^sub>R yvec zvec)
    from `xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from `yvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "yvec \<sharp>* Q" and "yvec \<sharp>* R" by simp+
    from `zvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "zvec \<sharp>* Q" and "zvec \<sharp>* R" by simp+    
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'`
    moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>P` have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note `xvec \<sharp>* Q``xvec \<sharp>* R` `xvec \<sharp>* K`
         `extract_frame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: par_cases_output_frame)
      case(c_par1 \<pi> Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from `Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) = append_at_end_prov_option \<pi> A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R` `distinct A\<^sub>R` `distinct A\<^sub>Q`
      have \<pi>: "Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) = \<pi>" unfolding `A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R`
        by(auto intro: append_at_end_prov_option_eq_elim)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(simp add: \<pi>)
      moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(auto dest:  extract_frame_fresh_chain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      moreover have "yvec \<sharp>* \<Psi>\<^sub>P" using `yvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `yvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "yvec \<sharp>* \<Psi>\<^sub>Q" using `yvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `yvec \<sharp>* Q` Aeq
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>P" using `zvec \<sharp>* A\<^sub>P` `extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>` `zvec \<sharp>* P`
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>Q" using `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` `zvec \<sharp>* Q` Aeq
        by(auto dest: extract_frame_fresh_chain)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R" using `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `zvec \<sharp>* R` Aeq
        by(auto dest: extract_frame_fresh_chain)
      moreover have "yvec \<sharp>* \<Psi>\<^sub>R" using `yvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` `yvec \<sharp>* R` Aeq
        by(auto dest: extract_frame_fresh_chain)
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* P` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* Q` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* Q`
	by(rule_tac Comm1) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>R \<sharp>* \<Psi>" by simp
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
	by(drule_tac Par1) (assumption | simp)+
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
	by(rule C3)
      ultimately show ?case by blast
    next
      case(c_par2 \<pi> R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      from `Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) = append_at_front_prov_option \<pi> A\<^sub>Q` `A\<^sub>Q \<sharp>* A\<^sub>R` `distinct A\<^sub>R` `distinct A\<^sub>Q`
      have \<pi>: "Some (\<langle>A\<^sub>R; zvec, M\<rangle>) = \<pi>" unfolding `A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R`
        by(induct \<pi>) (auto simp add: frame_chain_append dest: frame_chain_inject')
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R"
        by fact+      
      from `A\<^sub>Q \<sharp>* R` `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto> \<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'` \<pi>[symmetric] `A\<^sub>Q \<sharp>* A\<^sub>R` `zvec \<sharp>* A\<^sub>Q\<^sub>R` Aeq
      have "A\<^sub>Q \<sharp>* M"
        by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" by simp+
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" by simp
      from `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>Q \<sharp>* P" by simp
      from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by(auto dest: extract_frame_fresh_chain)
      from `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
      have R_trans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" unfolding \<pi> by fact+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>Some (\<langle>(A\<^sub>P@A\<^sub>Q); yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q`
        by(drule_tac Par1) auto
      moreover from FrP `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        using R_trans
        by(metis Associativity stat_eq_transition)
      moreover note FrR
      moreover have "yvec \<sharp>* \<Psi>\<^sub>Q"
        using `yvec \<sharp>* Q` `yvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R"
        using `zvec \<sharp>* R` `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` 
          `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` (*`A\<^sub>P \<sharp>* K'` `A\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R``A\<^sub>R \<sharp>* M'`*) `xvec \<sharp>* P` `xvec \<sharp>* Q`
          `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>`
        `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* R` `zvec \<sharp>* P` `zvec \<sharp>* Q`
	by(rule_tac Comm1) (assumption | force)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
	by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(c_comm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P K QR' A\<^sub>Q\<^sub>R yvec zvec)
    from `A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from `yvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "yvec \<sharp>* Q" and "yvec \<sharp>* R" by simp+
    from `zvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)` have "zvec \<sharp>* Q" and "zvec \<sharp>* R" by simp+        
    from `A\<^sub>P \<sharp>* (Q \<parallel> R)` `xvec \<sharp>* (Q \<parallel> R)` have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
    note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> QR'` `extract_frame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>` `distinct A\<^sub>Q\<^sub>R` 
    moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using `A\<^sub>Q\<^sub>R \<sharp>* Q` `A\<^sub>Q\<^sub>R \<sharp>* R` `A\<^sub>Q\<^sub>R \<sharp>* K`
    proof(induct rule: par_cases_input_frame)
      case(c_par1 \<pi> Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `A\<^sub>Q \<sharp>* A\<^sub>R` `distinct A\<^sub>Q` `distinct A\<^sub>R` `Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) = append_at_end_prov_option \<pi> A\<^sub>R`
      have \<pi>: "Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) = \<pi>"
        unfolding Aeq
        by(rule_tac append_at_end_prov_option_eq_elim)
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note FrP
      moreover from `(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>N\<rparr> \<prec> Q'` have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'"
        unfolding \<pi>
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover note `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>`
      moreover from `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>`
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extract_frame_fresh_chain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>`  `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      moreover have "yvec \<sharp>* \<Psi>\<^sub>R"
        using `yvec \<sharp>* R` `yvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>`
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R"
        using `zvec \<sharp>* R` `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>Q"
        using `zvec \<sharp>* Q` `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* Q` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* Q` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P`
	by(rule_tac Comm2) (assumption | force)+
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto> append_at_end_prov_option None A\<^sub>R @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using `extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>` `A\<^sub>R \<sharp>* Q`
        by(rule_tac Par1) (assumption | simp)+
      hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R"
        by simp
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* R` have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
	by(rule C3)
      ultimately show ?case by blast
    next
      case(c_par2 \<pi> R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from `Some (\<langle>A\<^sub>Q\<^sub>R; zvec, M\<rangle>) = append_at_front_prov_option \<pi> A\<^sub>Q`
      have \<pi>: "Some(\<langle>A\<^sub>R; zvec, M\<rangle>) = \<pi>" unfolding Aeq
        by(rule append_at_front_prov_option_eq_elim)
      from `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>` `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` Aeq 
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have R_trans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>Some(\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'"
        and FrR: "extract_frame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" unfolding \<pi> by fact+
      from P_trans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
	by(metis stat_eq_transition Associativity Commutativity Composition)
      moreover from `A\<^sub>P \<sharp>* R` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R` FrR `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
	by(auto dest: extract_frame_fresh_chain)
      moreover from `A\<^sub>Q\<^sub>R \<sharp>* P` `A\<^sub>Q\<^sub>R \<sharp>* N` `A\<^sub>Q\<^sub>R \<sharp>* xvec` Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" by simp+
      moreover from `A\<^sub>Q \<sharp>* R` R_trans `A\<^sub>Q \<sharp>* A\<^sub>R` `zvec \<sharp>* A\<^sub>Q\<^sub>R`
      have "A\<^sub>Q \<sharp>* M" unfolding Aeq
        by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>append_at_end_prov_option(Some (\<langle>A\<^sub>P; yvec, K\<rangle>)) A\<^sub>Q @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>R` `A\<^sub>Q \<sharp>* K` `xvec \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>`
        by(rule_tac Par1) (assumption|force)+
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>(Some (\<langle>(A\<^sub>P @ A\<^sub>Q); yvec, K\<rangle>)) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)"
        using `A\<^sub>P \<sharp>* A\<^sub>Q`
        by simp
      moreover from FrP `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* \<Psi>\<^sub>Q` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P`
      have "extract_frame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from R_trans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>Some (\<langle>A\<^sub>R; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity stat_eq_transition)
      moreover note FrR
      moreover have "yvec \<sharp>* \<Psi>\<^sub>Q"
        using `yvec \<sharp>* Q` `yvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)
      moreover have "zvec \<sharp>* \<Psi>\<^sub>R"
        using `zvec \<sharp>* R` `zvec \<sharp>* A\<^sub>Q\<^sub>R` `extract_frame R = \<langle>A\<^sub>R,\<Psi>\<^sub>R\<rangle>` 
        by(auto dest: extract_frame_fresh_chain simp add: Aeq)      
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
	using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>Q \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* Q` `A\<^sub>P \<sharp>* R` `A\<^sub>Q \<sharp>* R` `A\<^sub>P \<sharp>* M` `A\<^sub>Q \<sharp>* M` `A\<^sub>P \<sharp>* A\<^sub>R` `A\<^sub>Q \<sharp>* A\<^sub>R`
          `A\<^sub>R \<sharp>* \<Psi>` `A\<^sub>R \<sharp>* P` `A\<^sub>R \<sharp>* Q` `A\<^sub>R \<sharp>* R` `A\<^sub>R \<sharp>* K` `xvec \<sharp>* R`
        `yvec \<sharp>* \<Psi>` `zvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `yvec \<sharp>* R` `zvec \<sharp>* P` `zvec \<sharp>* Q`
	by(rule_tac Comm2) (assumption | force)+
      moreover from `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
	by(metis C1 C4)
      ultimately show ?case by blast
    qed
  qed
qed

lemma par_nil_left:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> \<zero>) \<leadsto>[Rel] P"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> P')
  from `\<Psi> \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` have "\<Psi> \<otimes> S_bottom' \<rhd> P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
    by(metis stat_eq_transition Identity Assertion_stat_eq_sym)
  hence "\<Psi> \<rhd> (P \<parallel> \<zero>) \<longmapsto>\<pi> @ \<alpha> \<prec> (P' \<parallel> \<zero>)"
    by(drule_tac Par1[where Q="\<zero>"]) (auto simp add: option.map_ident)
  moreover have "(\<Psi>, P' \<parallel> \<zero>, P') \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma par_nil_right:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q, (Q \<parallel> \<zero>)) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] (P \<parallel> \<zero>)"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> P')
  note `\<Psi> \<rhd> P \<parallel> \<zero> \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P`
  moreover have "bn \<alpha> \<sharp>* \<zero>" by simp
  ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: par_cases[where C="()"])
    case(c_par1 P' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
    from `extract_frame(\<zero>) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "\<Psi>\<^sub>Q = S_bottom'" by auto
    with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` have "\<Psi> \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'"
      by(metis stat_eq_transition Identity)
    moreover have "(\<Psi>, P', P' \<parallel> \<zero>) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 Q' \<pi>' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>\<pi>' @ \<alpha> \<prec> Q'` have False
      by auto
    thus ?case by simp
  next
    case(c_comm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec)
    thus ?case by(metis nil_trans)
  next
    case(c_comm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
    thus ?case by(metis nil_trans)
  qed
qed

lemma res_nil_left:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

lemma res_nil_right:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<zero> \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>\<zero>"
apply(auto simp add: simulation_def)
by(cases rule: semantics.cases) (auto simp add: psi.inject alpha')

lemma input_push_res_left:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: input_chain_fresh abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ "()"])
    case(c_sim \<pi> \<alpha> P')
    from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `x \<sharp> \<alpha>` `x \<sharp> \<pi>` show ?case
    proof(induct rule: input_cases)
      case(c_input K Tvec)
      have \<pi>: "\<pi> = Some (\<langle>\<epsilon>; \<epsilon>, M\<rangle>)" by fact
      from `x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>` have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
      from `\<Psi> \<turnstile> K \<leftrightarrow> M` `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi> @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
        unfolding \<pi>
	by(rule Input)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>map_option (F_res x) \<pi> @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])" using `x \<sharp> \<Psi>` `x \<sharp> K` `x \<sharp> N[xvec::=Tvec]`
	by(rule_tac Scope) auto
      moreover from `length xvec = length Tvec` `distinct xvec` `set xvec \<subseteq> supp N` `x \<sharp> N[xvec::=Tvec]` have "x \<sharp> Tvec"
	by(rule subst_term.subst3)
      with `x \<sharp> xvec` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec]), (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]) \<in> Rel"
	by(force intro: C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma input_push_res_right:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: input_chain_fresh abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ "()"])
    case(c_sim \<pi> \<alpha> P')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>` 
    moreover from `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P))` `x \<sharp> \<alpha>` have  "bn \<alpha> \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)"
      by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
    proof(induct rule: res_cases)
      case(c_res \<pi>' P')
      have \<pi>: "\<pi> = map_option (F_res x) \<pi>'" by fact
      from `\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` `x \<sharp> \<alpha>` show ?case
      proof(induct rule: input_cases)
	case(c_input K Tvec)
        have \<pi>': "\<pi>' = Some (\<langle>\<epsilon>; \<epsilon>, M\<rangle>)" by fact
	from `x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>` have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
	from `\<Psi> \<turnstile> K \<leftrightarrow> M` `distinct xvec` `set xvec \<subseteq> supp N` `length xvec = length Tvec`
	have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<pi>' @ K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]"
          unfolding \<pi>'
	  by(rule Input)
	moreover from `length xvec = length Tvec` `distinct xvec` `set xvec \<subseteq> supp N` `x \<sharp> N[xvec::=Tvec]` have "x \<sharp> Tvec"
	  by(rule subst_term.subst3)
	with `x \<sharp> xvec` have "(\<Psi>, (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec], \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])) \<in> Rel"
	  by(force intro: C1)
	ultimately show ?case by blast
      qed
    next
      case c_open
      then have False by auto
      thus ?case by simp
    qed
  qed
qed

lemma output_push_res_left:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<leadsto>[Rel] M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ "()"])
    case(c_sim \<pi> \<alpha> P')
    from `\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `x \<sharp> \<alpha>`
    show ?case
    proof(induct rule: output_cases)
      case(c_output K)
      have \<pi>: "\<pi> = Some (\<langle>\<epsilon>; \<epsilon>, M\<rangle>)" by fact
      from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi> @ K\<langle>N\<rangle> \<prec> P"
        unfolding \<pi>
	by(rule Output)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>map_option (F_res x) \<pi> @ K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P" using `x \<sharp> \<Psi>` `x \<sharp> K\<langle>N\<rangle>`
	by(rule Scope)
      moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma output_push_res_right:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ "(M, N)"])
    case(c_sim \<pi> \<alpha> P')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>\<pi> @ \<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P'` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P))` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* (M\<langle>N\<rangle>.P)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* (M, N)` `x \<sharp> \<alpha>`
    proof(induct rule: res_cases)
      case(c_open K \<pi>' xvec1 xvec2 y N' P')
      from `bn(K\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* (M, N)` have "y \<sharp> N" by simp+
      from `\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>Some \<pi>' @ K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')`
      have "N = ([(x, y)] \<bullet> N')"
	apply -
	by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>Some \<pi>' @ K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')")
          (auto simp add: residual_inject psi.inject)
      with `x \<sharp> N` `y \<sharp> N` `x \<noteq> y` have "N = N'"
	by(subst pt_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi="[(x, y)]"])
          (simp add: fresh_left calc_atm)
      with `y \<in> supp N'` `y \<sharp> N` have False by(simp add: fresh_def)
      thus ?case by simp
    next
      case(c_res \<pi>' P')
      from `\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` show ?case
      proof(induct rule: output_cases)
	case(c_output K)
        have \<pi>': "\<pi>' = Some (\<langle>\<epsilon>; \<epsilon>, M\<rangle>)" by fact
	from `\<Psi> \<turnstile> M \<leftrightarrow> K` have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<pi>' @ K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P"
          unfolding \<pi>'
	  by(rule Output)
	moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
	ultimately show ?case by force
      qed
    qed
  qed
qed

lemma case_push_res_left:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<leadsto>[Rel] Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  moreover from `x \<sharp> map fst Cs` have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ Cs])
    case(c_sim \<pi> \<alpha> P'')
    from `\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<longmapsto>\<pi> @ \<alpha> \<prec> P''`
    show ?case
    proof(induct rule: case_cases)
      case(c_case \<phi> P' \<pi>')
      have \<pi>: "\<pi> = map_option (F_assert \<circ> push_prov) \<pi>'" by fact
      from `(\<phi>, P') mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)` 
      obtain P where "(\<phi>, P) mem Cs" and "P' = \<lparr>\<nu>x\<rparr>P" 
	by(induct Cs) auto
      from `guarded P'` `P' = \<lparr>\<nu>x\<rparr>P` have "guarded P" by simp
      from `\<Psi> \<rhd> P' \<longmapsto>\<pi>' @ \<alpha> \<prec> P''` `P' = \<lparr>\<nu>x\<rparr>P` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> \<pi>' @  \<alpha> \<prec> P''"        
	by simp
      moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P''` `bn \<alpha> \<sharp>* \<Psi>` 
      moreover from `(\<phi>, P) mem Cs` `bn \<alpha> \<sharp>* Cs`
      have "bn \<alpha> \<sharp>* (\<phi>, P)" by(rule mem_fresh_chain)
      hence "bn \<alpha> \<sharp>* P" by auto
      ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* Cs`
      proof(induct rule: res_cases)
	case(c_open M \<pi>'' xvec1 xvec2 y N P')
        have \<pi>': "\<pi>' = Some (\<lparr>\<nu>x\<rparr>\<pi>'')" by fact
	from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
	from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs` have "y \<sharp> Cs" by simp
	from `\<Psi> \<rhd> P \<longmapsto>Some \<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')` `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
	have "\<Psi> \<rhd> Cases Cs \<longmapsto> map_option (F_assert \<circ> push_prov) (Some \<pi>'') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(rule Case)
	hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto> ([(x, y)] \<bullet> map_option (F_assert \<circ> push_prov) (Some \<pi>'')) @ ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
	  by(rule semantics.eqvt)
	with `x \<sharp> \<Psi>` `x \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2` `y \<sharp> \<Psi>` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
	have "\<Psi> \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto> Some(F_assert(push_prov([(x, y)] \<bullet> \<pi>''))) @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
	hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> (Cases Cs))  \<longmapsto> (Some(\<lparr>\<nu>y\<rparr>(F_assert(push_prov([(x, y)] \<bullet> \<pi>''))))) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
	  by(rule Open)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs)  \<longmapsto>(Some(\<lparr>\<nu>y\<rparr>(F_assert(push_prov([(x, y)] \<bullet> \<pi>''))))) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<sharp> Cs`
	  by(simp add: alpha_res)
	moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      next
	case(c_res \<pi>'' P')
        have \<pi>: "\<pi>' = map_option (F_res x) \<pi>''" by fact
	from `\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'` `(\<phi>, P) mem Cs` `\<Psi> \<turnstile> \<phi>` `guarded P`
	have "\<Psi> \<rhd> Cases Cs \<longmapsto>map_option (F_assert o push_prov) \<pi>'' @ \<alpha> \<prec> P'"
          by(rule Case)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>map_option (F_res x) (map_option (F_assert o push_prov) \<pi>'') @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
	  by(rule Scope)
	moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      qed
    qed
  qed
qed
 
lemma case_push_res_right:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(Cases Cs)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> map fst Cs` have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ Cs])
    case(c_sim \<pi> \<alpha> P'')
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<pi> @ \<alpha> \<prec> P''` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> P''` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>(Cases Cs)` `x \<sharp> \<alpha>` have "bn \<alpha> \<sharp>* (Cases Cs)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* Cs`
    proof(induct rule: res_cases)
      case(c_open M \<pi>' xvec1 xvec2 y N P')
      from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs` have "y \<sharp> Cs" by simp
      from `\<Psi> \<rhd> Cases Cs \<longmapsto>Some \<pi>' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')`
      show ?case
      proof(induct rule: case_cases)
	case(c_case \<phi> P \<pi>'')
        have \<pi>': "Some \<pi>' = map_option (F_assert \<circ> push_prov) \<pi>''" by fact
        then obtain \<pi>''' where \<pi>'': "\<pi>'' = Some \<pi>'''"
          by(induct \<pi>'') auto
	from `\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')`
	have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto> [(x,y)] \<bullet> \<pi>'' @ ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
	  by(rule semantics.eqvt)
	with `x \<sharp> \<Psi>` `x \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2` `y \<sharp> \<Psi>` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2`
	have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto> Some([(x,y)] \<bullet> \<pi>''') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts \<pi>'')
	hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)  \<longmapsto> Some(\<lparr>\<nu>y\<rparr>([(x,y)] \<bullet> \<pi>''')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
	  by(rule Open)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P  \<longmapsto>Some(\<lparr>\<nu>y\<rparr>([(x,y)] \<bullet> \<pi>''')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using `y \<sharp> Cs` `(\<phi>, P) mem Cs`
	  by(subst alpha_res, auto dest: mem_fresh)
	moreover from `(\<phi>, P) mem Cs` have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
	  by(induct Cs) auto
	moreover note `\<Psi> \<turnstile> \<phi>`
	moreover from `guarded P` have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
	ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>map_option (F_assert o push_prov) (Some(\<lparr>\<nu>y\<rparr>([(x,y)] \<bullet> \<pi>'''))) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
	  by(rule Case)
	moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      qed
    next
      case(c_res \<pi>' P')
      from `\<Psi> \<rhd> Cases Cs \<longmapsto>\<pi>' @ \<alpha> \<prec> P'`
      show ?case
      proof(induct rule: case_cases)
	case(c_case \<phi> P \<pi>'')
	from `\<Psi> \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
	have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> map_option (F_res x) \<pi>'' @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" by(rule Scope)
	moreover from `(\<phi>, P) mem Cs` have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
	  by(induct Cs) auto
	moreover note `\<Psi> \<turnstile> \<phi>`
	moreover from `guarded P` have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
	ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>map_option (F_assert o push_prov) (map_option (F_res x) \<pi>'') @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
	  by(rule Case)
	moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma res_input_cases[consumes 5, case_names c_res]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     "x \<sharp> P'"
  and     r_scope:  "\<And>\<pi>' P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<pi>' @ M\<lparr>N\<rparr> \<prec> P'; \<pi> = map_option (F_res x) \<pi>'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop P'"
proof -
  note Trans `x \<sharp> \<Psi>`
  moreover from `x \<sharp> M` `x \<sharp> N` have "x \<sharp> (M\<lparr>N\<rparr>)" by simp
  moreover note `x \<sharp> P'`
  moreover have "bn(M\<lparr>N\<rparr>) \<sharp>* \<Psi>" and "bn(M\<lparr>N\<rparr>) \<sharp>* P" and "bn(M\<lparr>N\<rparr>) \<sharp>* subject(M\<lparr>N\<rparr>)" and "bn(M\<lparr>N\<rparr>) = []" by simp+
  ultimately show ?thesis
    by(induct rule: res_cases) (auto intro: r_scope)
qed

lemma scope_ext_left:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>', R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> Rel"
  and     C3: "\<And>\<Psi>' zvec R y. \<lbrakk>y \<sharp> \<Psi>'; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  moreover from `x \<sharp> P` have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ x])
    case(c_sim \<pi> \<alpha> PQ)
    from `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` have "bn \<alpha> \<sharp>* Q" by simp
    note `\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<pi> @ \<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q" by simp+
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> PQ`
    proof(induct rule: par_cases[where C=x])
      case(c_par1 P' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
      from `x \<sharp> P' \<parallel> \<lparr>\<nu>x\<rparr>Q` have "x \<sharp> P'" by simp
      have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'" by fact
      from `extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extract_frame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
      then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
      with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>`
      have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>"
        and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> \<alpha>"
	by simp+
      from P_trans `y \<sharp> P` `y \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)` have "y \<sharp> P'"
	by(auto intro: free_fresh_derivative)
      note P_trans
      moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have "extract_frame([(y, x)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" 
	by(simp add: frame.inject alpha' fresh_list_cons eqvts) 
      moreover from `bn \<alpha> \<sharp>* Q` have "([(y, x)] \<bullet> (bn \<alpha>)) \<sharp>* ([(y, x)] \<bullet> Q)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` A have "bn \<alpha> \<sharp>* ([(y, x)] \<bullet> Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> ([(y, x)] \<bullet> Q) \<longmapsto>append_at_end_prov_option \<pi>' A\<^sub>Q' @ \<alpha> \<prec> (P' \<parallel> ([(y, x)] \<bullet> Q))"
	using `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>Q' \<sharp>* \<alpha>`
	by(rule Par1)
      hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)) \<longmapsto>map_option (F_res y) (append_at_end_prov_option \<pi>' A\<^sub>Q') @ \<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))"
	using `y \<sharp> \<Psi>` `y \<sharp> \<alpha>`
	by(rule Scope)
      hence "([(y, x)] \<bullet> \<Psi>) \<rhd> ([(y, x)] \<bullet> (\<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)))) \<longmapsto>([(y, x)] \<bullet> map_option (F_res y) (append_at_end_prov_option \<pi>' A\<^sub>Q')) @ ([(y, x)] \<bullet> (\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))))"
	by(rule semantics.eqvt)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `y \<sharp> P` `x \<sharp> \<alpha>` `y \<sharp> \<alpha>` `x \<sharp> P'` `y \<sharp> P'`
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>([(y, x)] \<bullet> map_option (F_res y) (append_at_end_prov_option \<pi>' A\<^sub>Q')) @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q)"
	by(simp add: eqvts calc_atm)
      moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q)), \<lparr>\<nu>*[]\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> Rel"
	by(rule_tac C2) auto
      ultimately show ?case
	by force
    next
      case(c_par2 xQ' \<pi>' A\<^sub>P \<Psi>\<^sub>P)
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<pi>' @ \<alpha> \<prec> xQ'`
      moreover have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      with `x \<sharp> P` `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" and "x \<sharp> A\<^sub>P"
	by(force dest: extract_frame_fresh)+
      with `x \<sharp> \<Psi>` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note `x \<sharp> \<alpha>`
      moreover from `x \<sharp> P \<parallel> xQ'` have "x \<sharp> xQ'" by simp
      moreover from FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh_chain) auto
      with `bn \<alpha> \<sharp>* \<Psi>` have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      ultimately show ?case using `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<alpha>` `bn \<alpha> \<sharp>* \<Psi>`
      proof(induct rule: res_cases')
	case(c_open M \<pi>'' xvec1 xvec2 y N Q')
	from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
	from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` have "y \<sharp> \<Psi>" by simp
	note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>Some([(x,y)] \<bullet> \<pi>'') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` FrP
	moreover from `bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
	moreover from `A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)` have "A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^sub>P" by simp+
	moreover from `A\<^sub>P \<sharp>* Q` `x \<sharp> A\<^sub>P` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
	ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>append_at_front_prov_option(Some([(x,y)] \<bullet> \<pi>'')) A\<^sub>P @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
	  using `A\<^sub>P \<sharp>* \<Psi>`
	  by(rule_tac Par2) (assumption | simp)+
        hence "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> Some(\<lparr>\<nu>*A\<^sub>P\<rparr>([(x,y)] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
          by simp
	 hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>Some(\<lparr>\<nu>y\<rparr>\<lparr>\<nu>*A\<^sub>P\<rparr>([(x,y)] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
	   using `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
	   by(rule Open)
	 with `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>Some(\<lparr>\<nu>y\<rparr>\<lparr>\<nu>*A\<^sub>P\<rparr>([(x,y)] \<bullet> \<pi>'')) @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
	   by(subst alpha_res[where y=y]) (simp add: fresh_left calc_atm eqvts)+
	moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      next
	case(c_res \<pi>'' Q')
	from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi>'' @ \<alpha> \<prec> Q'` FrP `bn \<alpha> \<sharp>* P`
	have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi>'' A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')" using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>`
	  by(rule Par2)
	hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>map_option (F_res x) (append_at_front_prov_option \<pi>'' A\<^sub>P) @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P \<parallel> Q')" using `x \<sharp> \<Psi>` `x \<sharp> \<alpha>`
	  by(rule Scope)
	moreover from `x \<sharp> \<Psi>` `x \<sharp> P` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q')), \<lparr>\<nu>*[]\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
	  by(rule_tac C2) auto
	ultimately show ?case
	  by force
      qed
    next
      case(c_comm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec xQ' A\<^sub>Q yvec zvec)
      have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with Q_trans have "x \<sharp> N" and "x \<sharp> xQ'" using `xvec \<sharp>* x` `xvec \<sharp>* K` `distinct xvec` 
	by(force intro: output_fresh_derivative)+
      from P_trans `x \<sharp> P` `x \<sharp> N`  have "x \<sharp> P'" by(rule input_fresh_derivative)
      from `x \<sharp> \<lparr>\<nu>x\<rparr>Q` FrQ `A\<^sub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh) auto
      from `x \<sharp> P` FrP `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh) auto
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      from `A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>Q \<sharp>* x` have "A\<^sub>Q \<sharp>* Q" by simp
      note Q_trans
      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover have "x \<sharp> K" using `x \<sharp> P` `A\<^sub>P \<sharp>* x` P_trans `yvec \<sharp>* x`
        by(auto dest!: trans_fresh_provenance[where xvec="[x]"] simp add: frame_res_chain_fresh name_list_supp) (simp_all add: fresh_def)
      from `xvec \<sharp>* x` have "x \<sharp> xvec" by simp
      with `x \<sharp> K` `x \<sharp> N` have "x \<sharp> K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note `x \<sharp> xQ'`
      moreover from `xvec \<sharp>* \<Psi>` `xvec \<sharp>* \<Psi>\<^sub>P` have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `x \<sharp> xvec` have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from `xvec \<sharp>* P` have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from `xvec \<sharp>* \<Psi>` have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* N` have "A\<^sub>Q \<sharp>* (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some K" by simp
      from `xvec \<sharp>* K` have "bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case 
	using `x \<sharp> K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` `bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P` `bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>` `object(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N`
          `bn(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec` `subject(K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some K` `A\<^sub>Q \<sharp>* (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)`
      proof(induct rule: res_cases)
      	case(c_open K' \<pi>' xvec1 xvec2 y N' Q')
        have \<pi>': "Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) = Some (\<lparr>\<nu>x\<rparr>\<pi>')" by fact
	from `x \<sharp> K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> K'"
          by simp_all
	from `bn(K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* P` have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
	from `A\<^sub>Q \<sharp>* (K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>)` have "(xvec1@xvec2) \<sharp>* A\<^sub>Q" and "y \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* K'" by simp+
	from `bn(K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* \<Psi>` have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
	from `object(K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some N` have "N = N'" by simp
	from `bn(K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = xvec` have "xvec = xvec1@y#xvec2" by simp
	from `subject(K'\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some K` have "K = K'" by simp
	from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
	have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
	  by(rule_tac xvec="[y]" in input_alpha) (auto simp add: calc_atm)
	hence P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
	  by(simp add: name_swap)
	have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some \<pi>' @ K'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')" by fact
	with `A\<^sub>Q \<sharp>* x` `y \<sharp> A\<^sub>Q` `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` `xvec1 \<sharp>* K'` `xvec2 \<sharp>* K'`
             `(xvec1@xvec2) \<sharp>* A\<^sub>Q`
	have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using `A\<^sub>Q \<sharp>* Q`
	  by(rule_tac output_fresh_chain_derivative(2)) (assumption | simp)+

	from `extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extract_frame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
	then obtain z A\<^sub>Q' where A: "A\<^sub>Q = z#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
	with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `(xvec1@xvec2) \<sharp>* A\<^sub>Q` `A\<^sub>Q \<sharp>* K'` `A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')` `y \<sharp> A\<^sub>Q` `A\<^sub>Q \<sharp>* N`
	have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^sub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
	  and "z \<sharp> K'" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^sub>Q' \<sharp>* K'" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
	  by auto
        have "Some (\<langle>(z#A\<^sub>Q'); zvec, M\<rangle>) = Some (\<lparr>\<nu>x\<rparr>\<pi>')"
          using \<pi>' by(simp add: A)
        moreover have "z \<sharp> \<pi>'" using Q_trans `z \<sharp> Q`
          by(auto dest!: trans_fresh_provenance[where xvec="[z]"])
        ultimately have \<pi>': "(\<langle>A\<^sub>Q'; zvec, M\<rangle>) = [(x,z)] \<bullet> \<pi>'"
          by(subst (asm) frame_alpha[where y=z]) (simp_all add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst] name_swap)
	from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "z \<sharp> A\<^sub>P" by simp+
	from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> z" and "x \<sharp> A\<^sub>Q'" by simp+

	from `distinct A\<^sub>Q` A have "z \<sharp> A\<^sub>Q'" 
	  by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
	from P_trans `x \<sharp> P` `z \<sharp> P` `x \<noteq> z` have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
	  by(rule_tac xvec="[x]" in input_alpha) (auto simp add: calc_atm)
	moreover note FrP 
	moreover from Q_trans
        have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> Some \<pi>') @ ([(x, z)] \<bullet> (K'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))" 
	  by(rule semantics.eqvt)
	with `x \<sharp> \<Psi>` `z \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `z \<sharp> \<Psi>\<^sub>P` `x \<sharp> K'` `z \<sharp> K'` `x \<sharp> xvec1` `x \<sharp> xvec2` `z \<sharp> xvec1` `z \<sharp> xvec2`
	have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto> Some (\<langle>A\<^sub>Q'; zvec, M\<rangle>) @ K'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')" 
	  by(simp add: eqvts \<pi>'[symmetric])
	moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have "extract_frame([(x, z)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
	  by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
	moreover from `A\<^sub>P \<sharp>* Q` have "([(x, z)] \<bullet> A\<^sub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
	  by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `A\<^sub>P \<sharp>* x` `z \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
	moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, z)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
	  by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `x \<sharp> A\<^sub>Q'` `z \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover have "yvec \<sharp>* ([(x,z)] \<bullet> Q)"
          using `yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `yvec \<sharp>* x` `yvec \<sharp>* A\<^sub>Q` A
          by auto
	ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
	  using `K=K'` `N=N'` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `(xvec1@xvec2) \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* K'` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`
	  by(rule_tac Comm1) (assumption | simp)+
	with`z \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')))"
          by(auto dest: Scope)
	moreover from `x \<sharp> P` `z \<sharp> P` `z \<sharp> Q` have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (P \<parallel> ([(x, z)] \<bullet> Q)))"
	  by(subst alpha_res[of x]) (auto simp add: calc_atm fresh_left name_swap)
	with `x \<sharp> P` `z \<sharp> P` have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
	  by(simp add: eqvts)
	moreover from `z \<noteq> y` `x \<noteq> z` `z \<sharp> P'` `z \<sharp> [(x, y)] \<bullet> Q'` have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))))"
	  by(subst alpha_res[of x]) (auto simp add: res_chain_fresh fresh_left calc_atm name_swap)
	with `x \<sharp> xvec1` `x \<sharp> xvec2` `z \<sharp> xvec1` `z \<sharp> xvec2` have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
	  by(simp add: eqvts)
	moreover from `x \<sharp> P'` `x \<sharp> Q'` `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2`
	  have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
	  by(subst alpha_res[of y]) (auto simp add: res_chain_fresh calc_atm eqvts fresh_left name_swap)
	ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
	  by simp
	moreover from `y \<sharp> \<Psi>` `(xvec1@xvec2) \<sharp>* \<Psi>` `xvec=xvec1@y#xvec2`
	have "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<in> Rel"
	  by(force intro: C3 simp add: res_chain_append)
	ultimately show ?case by blast
      next
	case(c_res \<pi> Q')
	have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
	with `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `xvec \<sharp>* K` `distinct xvec` have "A\<^sub>Q \<sharp>* Q'"
	  by(force dest: output_fresh_chain_derivative)
	
	with `extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extract_frame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
	then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
	with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* Q'`
	have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> K" and "y \<sharp> Q'"
	  and "A\<^sub>Q' \<sharp>* K"
	  by simp_all
        have "Some (\<langle>(y#A\<^sub>Q'); zvec, M\<rangle>) = map_option (F_res x) \<pi>"
          using `Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) = map_option (F_res x) \<pi>`
          by(simp add: A)
        moreover have "y \<sharp> \<pi>" using Q_trans `y \<sharp> Q`
          by(auto dest!: trans_fresh_provenance[where xvec="[y]"])
        ultimately have \<pi>: "Some (\<langle>A\<^sub>Q'; zvec, M\<rangle>) = [(x,y)] \<bullet> \<pi>"
          by(induct \<pi>) (auto simp add: frame_alpha[where x=x and y=y] frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst] name_swap)
	from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
	from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
	
	with A `distinct A\<^sub>Q` have "y \<sharp> A\<^sub>Q'" 
	  by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
	from `x \<sharp> P` `y \<sharp> P` `x \<noteq> y` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
	have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
	  by(rule_tac xvec="[y]" in input_alpha) (auto simp add: calc_atm)
	hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
	  by(simp add: name_swap)
	moreover note FrP
	moreover from  `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
        have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>Some (\<langle>A\<^sub>Q'; zvec, M\<rangle>) @ ([(x, y)] \<bullet> (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))"
          unfolding \<pi>
          by(rule_tac semantics.eqvt)
	with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `y \<sharp> \<Psi>\<^sub>P` `x \<sharp> K` `y \<sharp> K` `x \<sharp> xvec` `y \<sharp> xvec`
	have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>Some (\<langle>A\<^sub>Q'; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')" 
	  by(simp add: eqvts)
	moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have FrQ: "extract_frame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
	  by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
	moreover from `A\<^sub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `A\<^sub>P \<sharp>* x` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
	moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `x \<sharp> A\<^sub>Q'` `y \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover have "yvec \<sharp>* ([(x,y)] \<bullet> Q)"
          using `yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `yvec \<sharp>* x` `yvec \<sharp>* A\<^sub>Q` A
          by auto
	ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
	  using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* K` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`
	  by(rule_tac Comm1) (assumption | simp)+
	with`y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(auto dest: Scope)
	moreover from `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
	  by(subst alpha_res[of x]) (auto simp add: calc_atm fresh_left name_swap)
	with `x \<sharp> P` `y \<sharp> P` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
	  by(simp add: eqvts)
	moreover from `y \<sharp> P'` `y \<sharp> Q'` `x \<sharp> xvec` `y \<sharp> xvec` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
	  by(subst alpha_res[of y]) (auto simp add: res_chain_fresh calc_atm eqvts fresh_left name_swap)
	ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
	  by simp
	moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
	  by(rule C2)
	ultimately show ?case by blast
      qed
    next
      case(c_comm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K xQ' A\<^sub>Q yvec zvec)
      have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from P_trans `x \<sharp> P` have "x \<sharp> N" and "x \<sharp> P'" using `xvec \<sharp>* x` `xvec \<sharp>* M` `distinct xvec` 
	by(force intro: output_fresh_derivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ `A\<^sub>Q \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>Q"
	by(drule_tac extract_frame_fresh) auto
      from `x \<sharp> P` FrP `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
	by(drule_tac extract_frame_fresh) auto
      from `A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* Q" by simp
      from `A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q` `A\<^sub>Q \<sharp>* x` have "A\<^sub>Q \<sharp>* Q" by simp
      from `xvec \<sharp>* x` `xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` have "xvec \<sharp>* Q" by simp

      note Q_trans
      moreover from `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover have "x \<sharp> K" using `x \<sharp> P` `A\<^sub>P \<sharp>* x` P_trans `yvec \<sharp>* x`
        by(auto dest!: trans_fresh_provenance[where xvec="[x]"] simp add: frame_res_chain_fresh name_list_supp) (simp_all add: fresh_def)      
      moreover note `x \<sharp> N`
      moreover from Q_trans `x \<sharp> N` have "x \<sharp> xQ'" by(force dest: input_fresh_derivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: res_input_cases)
	case(c_res \<pi> Q')
	have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>N\<rparr> \<prec> Q'" by fact
	with `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* N` have "A\<^sub>Q \<sharp>* Q'"
	  by(rule_tac input_fresh_chain_derivative)

	with `extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have FrxQ: "\<lparr>\<nu>x\<rparr>(extract_frame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
	then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
	with `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* \<Psi>\<^sub>P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* xvec` `A\<^sub>Q \<sharp>* K` `A\<^sub>Q \<sharp>* Q'` `A\<^sub>Q \<sharp>* N` `A\<^sub>Q \<sharp>* x`
	have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> K" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* K" and "x \<noteq> y"
          by simp_all
        have "Some (\<langle>(y#A\<^sub>Q'); zvec, M\<rangle>) = map_option (F_res x) \<pi>"
          using `Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) = map_option (F_res x) \<pi>`
          by(simp add: A)
        moreover have "y \<sharp> \<pi>"
          using `y \<sharp> Q` Q_trans
          by(auto dest!: trans_fresh_provenance[where xvec="[y]"])
        ultimately have \<pi>: "Some (\<langle>(A\<^sub>Q'); zvec, M\<rangle>) = [(x,y)] \<bullet> \<pi>"
          apply(induct \<pi>)
          apply(auto simp add: frame_alpha[where x=x and y=y])
          by(simp add: frame.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst] name_swap)
	from A `A\<^sub>P \<sharp>* A\<^sub>Q` have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
	from A `A\<^sub>Q \<sharp>* x` have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
	
	with A `distinct A\<^sub>Q` have "y \<sharp> A\<^sub>Q'" 
	  by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

	note P_trans FrP
	moreover from  `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ K\<lparr>N\<rparr> \<prec> Q'` have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>[(x, y)] \<bullet> \<pi> @ ([(x, y)] \<bullet> (K\<lparr>N\<rparr> \<prec> Q'))" 
	  by(rule semantics.eqvt)
	with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `y \<sharp> \<Psi>\<^sub>P` `x \<sharp> K` `y \<sharp> K` `x \<sharp> N` `y \<sharp> N`
	have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto> [(x, y)] \<bullet> \<pi> @ K\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')" 
	  by(simp add: eqvts)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto> Some (\<langle>A\<^sub>Q'; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')"
          by(simp add: \<pi>)
	moreover from A `A\<^sub>Q \<sharp>* x` FrxQ have FrQ: "extract_frame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extract_frame Q"
	  by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
	moreover from `A\<^sub>P \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `A\<^sub>P \<sharp>* x` `y \<sharp> A\<^sub>P` have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
	moreover from `A\<^sub>Q' \<sharp>* Q` have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `x \<sharp> A\<^sub>Q'` `y \<sharp> A\<^sub>Q'` have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
	moreover from `xvec \<sharp>* Q` have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
	with `xvec \<sharp>* x` `y \<sharp> xvec` have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover have "yvec \<sharp>* ([(x,y)] \<bullet> Q)"
          using `yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q` `yvec \<sharp>* x` `yvec \<sharp>* A\<^sub>Q` A
          by auto        
	ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
	  using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`  `A\<^sub>P \<sharp>* A\<^sub>Q'` `A\<^sub>Q' \<sharp>* \<Psi>` `A\<^sub>Q' \<sharp>* P` `A\<^sub>P \<sharp>* M` `A\<^sub>Q' \<sharp>* K`
          `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`
	  by(rule_tac Comm2) (assumption | simp)+
	with`y \<sharp> \<Psi>` have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')))"
          by(auto dest: Scope)
	moreover from `x \<sharp> P` `y \<sharp> P` `y \<sharp> Q` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
	  by(subst alpha_res[of x]) (auto simp add: calc_atm fresh_left name_swap)
	with `x \<sharp> P` `y \<sharp> P` have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
	  by(simp add: eqvts)
	moreover from `x \<sharp> P'` `y \<sharp> P'` `y \<sharp> Q'` `xvec \<sharp>* x` `y \<sharp> xvec` have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
	  by(subst alpha_res[of y]) (auto simp add: res_chain_fresh calc_atm eqvts fresh_left name_swap)
	ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
	  by simp
	moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
	  by(rule C2)
	ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma scope_ext_right:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>, R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
proof -
  note `eqvt Rel` `x \<sharp> \<Psi>`
  moreover from `x \<sharp> P` have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  moreover from `x \<sharp> P` have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: sim_i_fresh[of _ _ _ _ _ "()"])
    case(c_sim \<pi> \<alpha> xPQ)
    from `bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)` `x \<sharp> \<alpha>` have "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* Q" by simp+
    note `\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<pi> @ \<alpha> \<prec> xPQ` `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `x \<sharp> xPQ` `bn \<alpha> \<sharp>* \<Psi>`
    moreover from `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
    ultimately show ?case using `bn \<alpha> \<sharp>* subject \<alpha>` `x \<sharp> \<alpha>`
    proof(induct rule: res_cases)
      case(c_open M \<pi>' xvec1 xvec2 y N PQ)
      from `x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>` have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from `xvec1 \<sharp>* (P \<parallel> Q)` `xvec2 \<sharp>* (P \<parallel> Q)` `y \<sharp> (P \<parallel> Q)`
      have "(xvec1@xvec2) \<sharp>* P" and "(xvec1@xvec2) \<sharp>* Q" and "y \<sharp> P" and "y \<sharp> Q"
	by simp+
      from `\<Psi> \<rhd> P \<parallel> Q \<longmapsto> Some \<pi>' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)`
      have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (P \<parallel> Q)) \<longmapsto> [(x,y)] \<bullet> (Some \<pi>') @ ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)))"
	by(rule semantics.eqvt)
      with `x \<sharp> \<Psi>` `y \<sharp> \<Psi>` `x \<sharp> P` `y \<sharp> P` `x \<sharp> M` `y \<sharp> M` `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2`
      have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> Some([(x,y)] \<bullet>\<pi>') @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> PQ"
	by(simp add: eqvts)
      moreover from `xvec1 \<sharp>* \<Psi>` `xvec2 \<sharp>* \<Psi>` have "(xvec1@xvec2) \<sharp>* \<Psi>" by simp
      moreover note `(xvec1@xvec2) \<sharp>* P`
      moreover from `(xvec1@xvec2) \<sharp>* Q` have "([(x, y)] \<bullet> (xvec1@xvec2)) \<sharp>* ([(x, y)] \<bullet> Q)"
	by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with `x \<sharp> xvec1` `x \<sharp> xvec2` `y \<sharp> xvec1` `y \<sharp> xvec2` have "(xvec1@xvec2) \<sharp>* ([(x, y)] \<bullet> Q)"
	by(auto simp add: eqvts)
      moreover from `xvec1 \<sharp>* M` `xvec2 \<sharp>* M` have "(xvec1@xvec2) \<sharp>* M" by simp
      ultimately show ?case
      proof(induct rule: par_output_cases[where C=y])
	case(c_par1 \<pi>'' P' A\<^sub>Q \<Psi>\<^sub>Q)
	from `y \<sharp> xvec1` `y \<sharp> xvec2` have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
	with `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'` `(xvec1@xvec2) \<sharp>* M` `y \<sharp> P` 
             `distinct xvec1` `distinct xvec2` `xvec1 \<sharp>* xvec2` 
	have "y \<sharp> N" by(force intro: output_fresh_derivative)
	with `y \<in> supp N` have False by(simp add: fresh_def)
	thus ?case by simp
      next
	case(c_par2 \<pi>'' Q' A\<^sub>P \<Psi>\<^sub>P)
        from `Some ([(x, y)] \<bullet> \<pi>') = append_at_front_prov_option \<pi>'' A\<^sub>P`
        obtain \<pi>''' where \<pi>''': "\<pi>'' = Some \<pi>'''"
          by(induct \<pi>'') auto
	have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
	with `y \<sharp> P` `A\<^sub>P \<sharp>* y` have "y \<sharp> \<Psi>\<^sub>P" 
	  apply(drule_tac extract_frame_fresh)
	  by(simp add: frame_res_chain_fresh) (simp add: fresh_def name_list_supp)
	from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto> \<pi>'' @ M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'` `y \<in> supp N` `y \<sharp> \<Psi>` `y \<sharp> \<Psi>\<^sub>P` `y \<sharp> M` `y \<sharp> xvec1` `y \<sharp> xvec2`
	have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>Some(\<lparr>\<nu>y\<rparr>\<pi>''') @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: Open simp add: \<pi>''')
	with `y \<sharp> Q` have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some(\<lparr>\<nu>y\<rparr>\<pi>''') @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
	  by(simp add: alpha_res)
	moreover from `A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)` have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
	with `y \<sharp> Q` have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alpha_res)
	ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>append_at_front_prov_option (Some(\<lparr>\<nu>y\<rparr>\<pi>''')) A\<^sub>P @ M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
	  using FrP `(xvec1@xvec2) \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* M` `y \<sharp> P` `A\<^sub>P \<sharp>* (xvec1@xvec2)` `A\<^sub>P \<sharp>* y` `A\<^sub>P \<sharp>* N`
	  by(rule_tac Par2) auto
	moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
	ultimately show ?case by blast
      qed
    next
      case(c_res \<pi>' PQ)
      from `\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<pi>' @ \<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>`  `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>`
      show ?case
      proof(induct rule: par_cases[where C=x])
	case(c_par1 P' \<pi>'' A\<^sub>Q \<Psi>\<^sub>Q)
	note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>'' @ \<alpha> \<prec> P'`
	moreover with `x \<sharp> P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
	have "x \<sharp> P'" by(force dest: free_fresh_derivative)
	with `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
	  by simp
	moreover from `bn \<alpha> \<sharp>* Q` have "bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
	moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
	moreover from `x \<sharp> \<alpha>` `A\<^sub>Q \<sharp>* \<alpha>` have "(x#A\<^sub>Q) \<sharp>* \<alpha>" by simp
	ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>append_at_end_prov_option \<pi>'' (x#A\<^sub>Q) @ \<alpha> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q)"
	  by(rule Par1)
	moreover from `x \<sharp> P'` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P' \<parallel> (\<lparr>\<nu>x\<rparr>Q)), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q))) \<in> Rel"
	  by(rule_tac C2) auto
	ultimately show ?case
	  by force
      next
	case(c_par2 Q' \<pi> A\<^sub>P \<Psi>\<^sub>P)
	have FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
	with `x \<sharp> P` `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P"
	  apply(drule_tac extract_frame_fresh)
	  by(simp add: frame_res_chain_fresh) (simp add: fresh_def name_list_supp)
	from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi> @ \<alpha> \<prec> Q'` `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> \<alpha>`
	have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>map_option (F_res x) \<pi> @ \<alpha> \<prec> \<lparr>\<nu>x\<rparr>Q'"
	  by(rule_tac Scope) auto
	moreover note FrP `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>`
	moreover from `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: fresh_star_def abs_fresh)
	ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>append_at_front_prov_option (map_option (F_res x) \<pi>) A\<^sub>P @ \<alpha> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* \<alpha>`
	  by(rule Par2)
	moreover from `x \<sharp> P` `x \<sharp> \<Psi>` have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q'))) \<in> Rel"
	  by(rule_tac C2) auto
	ultimately show ?case
	  by force
      next
	case(c_comm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q yvec zvec)
	have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
	have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
	from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extract_frame_fresh) simp
        have "x \<sharp> K" using `A\<^sub>P \<sharp>* x` `yvec \<sharp>* x` `x \<sharp> P` P_trans
          by(auto dest!: trans_fresh_provenance[where xvec="[x]"] simp add: frame_res_chain_fresh)
        (simp_all add: fresh_def name_list_supp)
        note `x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>`
	with `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frame_res_chain_fresh) (simp add: fresh_def name_list_supp)
	show ?case
	proof(case_tac "x \<in> supp N")
	  note P_trans FrP
	  moreover assume "x \<in> supp N"
	  hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<lparr>\<nu>x\<rparr>(\<langle>A\<^sub>Q; zvec, M\<rangle>)) @ K\<lparr>\<nu>*([]@(x#xvec))\<rparr>\<langle>N\<rangle> \<prec> Q'" using Q_trans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> K` `xvec \<sharp>* x`
	    by(rule_tac Open) (assumption | force simp add: fresh_list_nil)+
	  hence Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<langle>(x#A\<^sub>Q); zvec, M\<rangle>) @ K\<lparr>\<nu>*(x#xvec)\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
	  moreover from `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>" 
	    by simp
	  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
	  moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	  moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
	    by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
	  moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
	  moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
	  moreover from `x \<sharp> K` `A\<^sub>Q \<sharp>* K` have "(x#A\<^sub>Q) \<sharp>* K" by simp
	  moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	  moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          moreover have "yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q" using `yvec \<sharp>* Q` `yvec \<sharp>* x`
            by simp
	  ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*(x#xvec)\<rparr>(P' \<parallel> Q')" using `A\<^sub>P \<sharp>* M`
            `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`
	    by(rule_tac Comm1) (assumption | simp)+
	  moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C1)
	  ultimately show ?case by force
	next
	  note P_trans FrP
	  moreover assume "x \<notin> supp N"
	  hence "x \<sharp> N" by(simp add: fresh_def)
	  with Q_trans `x \<sharp> \<Psi>` `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> K` `xvec \<sharp>* x`
	  have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<langle>(x#A\<^sub>Q); zvec, M\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(auto dest: Scope)
	  moreover from P_trans `x \<sharp> P` `x \<sharp> N` have "x \<sharp> P'" by(rule input_fresh_derivative)
	  with `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
	    by simp
	  moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
	  moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	  moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
	    by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
	  moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
	  moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
	  moreover from `x \<sharp> K` `A\<^sub>Q \<sharp>* K` have "(x#A\<^sub>Q) \<sharp>* K" by simp
	  moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	  moreover from `x \<sharp> P` `xvec \<sharp>* P` have "(x#xvec) \<sharp>* P" by(simp)
          moreover have "yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q" using `yvec \<sharp>* Q` `yvec \<sharp>* x`
            by simp          
	  ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* M`
            `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`
	    by(rule_tac Comm1) (assumption | simp)+
	  moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
	  ultimately show ?case by blast
	qed
      next
	case(c_comm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q yvec zvec)
	have P_trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>Some (\<langle>A\<^sub>P; yvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
	have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>Some (\<langle>A\<^sub>Q; zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
	from FrP `x \<sharp> P` have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extract_frame_fresh) simp
	with `A\<^sub>P \<sharp>* x` have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frame_res_chain_fresh) (simp add: fresh_def name_list_supp)
        have "x \<sharp> K" using `A\<^sub>P \<sharp>* x` `yvec \<sharp>* x` `x \<sharp> P` P_trans
          by(auto dest!: trans_fresh_provenance[where xvec="[x]"] simp add: frame_res_chain_fresh)
        (simp_all add: fresh_def name_list_supp)        
	from P_trans `x \<sharp> P` `xvec \<sharp>* x` `distinct xvec` `xvec \<sharp>* M`
	have "x \<sharp> N" and "x \<sharp> P'" by(force intro: output_fresh_derivative)+
	from Q_trans `x \<sharp> \<Psi>`  `x \<sharp> \<Psi>\<^sub>P` `x \<sharp> K` `x \<sharp> N` have Q_trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>Some (\<langle>(x#A\<^sub>Q); zvec, M\<rangle>) @ K\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(auto dest: Scope)
	note P_trans FrP Q_trans
	moreover with `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` have "extract_frame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
	  by simp
	moreover note `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P`
	moreover from  `A\<^sub>P \<sharp>* Q` have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	moreover from `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* x` have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
	  by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
	moreover from `x \<sharp> \<Psi>` `A\<^sub>Q \<sharp>* \<Psi>` have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
	moreover from `x \<sharp> P` `A\<^sub>Q \<sharp>* P` have "(x#A\<^sub>Q) \<sharp>* P" by simp
	moreover from `x \<sharp> K` `A\<^sub>Q \<sharp>* K` have "(x#A\<^sub>Q) \<sharp>* K" by simp
	moreover from `A\<^sub>Q \<sharp>* Q` have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
	moreover from `xvec \<sharp>* Q` have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        moreover have "yvec \<sharp>* \<lparr>\<nu>x\<rparr>Q" using `yvec \<sharp>* Q` `yvec \<sharp>* x`
          by simp
	ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using `A\<^sub>P \<sharp>* M`
            `yvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>\<^sub>P` `zvec \<sharp>* \<Psi>` `zvec \<sharp>* P` `zvec \<sharp>* \<Psi>\<^sub>Q`          
	  by(rule_tac Comm2) (assumption | simp)+
	moreover from `x \<sharp> \<Psi>` `x \<sharp> P'` `xvec \<sharp>* \<Psi>` have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
	ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma sim_par_comm:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' R S. (\<Psi>', R \<parallel> S, S \<parallel> R) \<in> Rel"
  and     C2: "\<And>\<Psi>' R S xvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>R, \<lparr>\<nu>*xvec\<rparr>S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
using `eqvt Rel`
proof(induct rule: simI[of _ _ _ _ "()"])
  case(c_sim \<pi> \<alpha> PQ)
  from `bn \<alpha> \<sharp>* (P \<parallel> Q)` have "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* P" by simp+
  with `\<Psi> \<rhd> Q \<parallel> P \<longmapsto>\<pi> @ \<alpha> \<prec> PQ` `bn \<alpha> \<sharp>* \<Psi>` show ?case using `bn \<alpha> \<sharp>* subject \<alpha>`
  proof(induct rule: par_cases[where C="()"])
    case(c_par1 Q' \<pi>' A\<^sub>P \<Psi>\<^sub>P)
    from `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<pi>' @ \<alpha>\<prec> Q'` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `bn \<alpha> \<sharp>* P` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_front_prov_option \<pi>' A\<^sub>P @ \<alpha> \<prec> (P \<parallel> Q')" by(rule Par2)
    moreover have "(\<Psi>, P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_par2 P' \<pi>' A\<^sub>Q \<Psi>\<^sub>Q)
    from `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `bn \<alpha> \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* \<alpha>` 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>append_at_end_prov_option \<pi>' A\<^sub>Q @ \<alpha> \<prec> (P' \<parallel> Q)" by(rule Par1)
    moreover have "(\<Psi>, P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(c_comm1 \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec P' A\<^sub>P yvec zvec)
    hence "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      by(rule_tac Comm2) (assumption | simp)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using `xvec \<sharp>* \<Psi>` by(rule C2)
    ultimately show ?case by blast
  next
    case(c_comm2 \<Psi>\<^sub>P M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K P' A\<^sub>P)
      hence "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>None @ \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>Q \<sharp>* A\<^sub>P` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `xvec \<sharp>* P` `A\<^sub>P \<sharp>* K` `A\<^sub>Q \<sharp>* M`
      by(rule_tac Comm1) (assumption | simp add: fresh_chain_sym)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using `xvec \<sharp>* \<Psi>` by(rule C2)
    ultimately show ?case by blast
  qed
qed

lemma bang_ext_left:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "guarded P"
  and     "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> !P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(auto simp add: simulation_def dest!: Bang)

lemma bang_ext_right:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> !P \<leadsto>[Rel] !P"
proof(auto simp add: simulation_def)
  fix \<alpha> \<pi> P'
  assume "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'"
  hence "\<exists> \<pi>'. \<Psi> \<rhd> P \<parallel> !P \<longmapsto> \<pi>' @ \<alpha> \<prec> P'"
    apply -
    apply(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<pi> @ \<alpha> \<prec> P'")
    by(auto simp add: psi.inject)
  moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
  ultimately show "\<exists>\<pi>' P''. \<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<pi>' @ \<alpha> \<prec> P'' \<and> (\<Psi>, P'', P') \<in> Rel"
    by blast
qed

end

end