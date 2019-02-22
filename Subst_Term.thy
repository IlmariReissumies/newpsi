theory Subst_Term
  imports Chain
begin

definition well_formed_subst :: "(('d::fs_name) list \<times> ('e::fs_name) list) list \<Rightarrow> bool" where "well_formed_subst \<sigma> = ((filter (\<lambda>(xvec, Tvec). \<not>(length xvec = length Tvec \<and> distinct xvec)) \<sigma>) = [])"

locale subst_type =
  fixes subst :: "'a::fs_name \<Rightarrow> name list \<Rightarrow> 'b::fs_name list \<Rightarrow> 'a" ("_[_::=_]" [80, 80 ,80] 130)

  assumes eq[eqvt]: "\<And>p::name prm. (p \<bullet> (M[xvec::=Tvec])) = ((p \<bullet> M)[(p \<bullet> xvec)::=(p \<bullet> Tvec)])"
  and renaming:     "\<And>xvec Tvec p T. \<lbrakk>length xvec = length Tvec; (set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec);
                                      distinct_perm p; (p \<bullet> xvec) \<sharp>* T\<rbrakk> \<Longrightarrow>
                                      T[xvec::=Tvec] = (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]"
begin

lemma supp_subst:
  fixes M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  shows "(supp(M[xvec::=Tvec])::name set) \<subseteq> ((supp M) \<union> (supp xvec) \<union> (supp Tvec))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M)[([(x, y)] \<bullet> xvec)::=([(x, y)] \<bullet> Tvec)] \<noteq> M[xvec::=Tvec]"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> (M::'a)"
  let ?R = "\<lambda>y xvec. ([(x, y)] \<bullet> xvec) \<noteq> (xvec::name list)"
  let ?S = "\<lambda>y Tvec. ([(x, y)] \<bullet> Tvec) \<noteq> (Tvec::'b list)"
  assume A: "finite {y. ?Q y M}" and B: "finite {y. ?R y xvec}" and C: "finite {y. ?S y Tvec}" and D: "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M}  - {y. ?R y xvec}  - {y. ?S y Tvec})" 
    by(auto intro: Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma subst2[intro]:
  fixes x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> Tvec"

  shows "x \<sharp> M[xvec::=Tvec]"
using assms supp_subst
by(auto simp add: fresh_def)

lemma subst2_chain[intro]:
  fixes yvec :: "name list"
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "yvec \<sharp>* M"
  and     "yvec \<sharp>* xvec"
  and     "yvec \<sharp>* Tvec"

  shows "yvec \<sharp>* M[xvec::=Tvec]"
using assms
by(induct yvec) auto

lemma fs[simp]: "finite ((supp subst)::name set)"
by(simp add: supp_def perm_fun_def eqvts)
(*
lemma subst1_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   Xs   :: "name set"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "Xs \<sharp>* T[xvec::=Tvec]"
  and     "Xs \<sharp>* xvec"

  shows "Xs \<sharp>* T"
using assms
by(auto intro: subst1 simp add: fresh_star_def)
*)
lemma subst4_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "xvec \<sharp>* Tvec"

  shows "xvec \<sharp>* T[xvec::=Tvec]"
proof -
  obtain p where "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* T" and "(p \<bullet> xvec) \<sharp>* xvec"
             and S: "(set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
             and "distinct_perm p"
    by(rule_tac xvec=xvec and c="(T, xvec)" in name_list_avoiding) auto 

  from `length xvec = length Tvec` have "length(p \<bullet> xvec) = length Tvec" by simp
  moreover from `(p \<bullet> xvec) \<sharp>* T` have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> T)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `distinct_perm p` have "xvec \<sharp>* (p \<bullet> T)" by simp
  ultimately have "(set xvec) \<sharp>* (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]" using `xvec \<sharp>* Tvec` `(p \<bullet> xvec) \<sharp>* xvec`
    by auto

  thus ?thesis using `length xvec = length Tvec` `distinct xvec` S `(p \<bullet> xvec) \<sharp>* T` `distinct_perm p`
    by(simp add: renaming)
qed

definition seq_subst :: "'a \<Rightarrow> (name list \<times> 'b list) list \<Rightarrow> 'a" ("_[<_>]" [80, 80] 130)
  where "M[<\<sigma>>] \<equiv> foldl (\<lambda>N. \<lambda>(xvec, Tvec). N[xvec::=Tvec]) M \<sigma>"

lemma seq_subst_nil[simp]:
  "seq_subst M [] = M"
by(simp add: seq_subst_def)

lemma seq_subst_cons[simp]:
  shows "seq_subst M ((xvec, Tvec)#\<sigma>) = seq_subst(M[xvec::=Tvec]) \<sigma>"
  by(simp add: seq_subst_def)

lemma seq_subst_term_append[simp]:
  shows "seq_subst M (\<sigma>@\<sigma>') = seq_subst (seq_subst M \<sigma>) \<sigma>'"
by(induct \<sigma>) (auto simp add: seq_subst_def)

lemma well_formed_subst_eqvt[eqvt]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"

  shows "p \<bullet> (well_formed_subst \<sigma>) = well_formed_subst(p \<bullet> \<sigma>)"
by(induct \<sigma> arbitrary: p) (auto simp add: eqvts well_formed_subst_def)

lemma well_formed_simp[simp]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"
  
  shows "well_formed_subst(p \<bullet> \<sigma>) = well_formed_subst \<sigma>"
by(induct \<sigma>) (auto simp add: eqvts well_formed_subst_def)

lemma well_formed_nil[simp]:
  "well_formed_subst []"
by(simp add: well_formed_subst_def)

lemma well_formed_cons[simp]:
  shows "well_formed_subst((xvec, Tvec)#\<sigma>) = (length xvec = length Tvec \<and> distinct xvec \<and> well_formed_subst \<sigma>)"
by(simp add: well_formed_subst_def) auto

lemma well_formed_append[simp]:
  fixes \<sigma>  :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   \<sigma>' :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"

  shows "well_formed_subst(\<sigma>@\<sigma>') = (well_formed_subst \<sigma> \<and> well_formed_subst \<sigma>')"
by(simp add: well_formed_subst_def)

lemma seq_subst2[intro]:
  fixes \<sigma> :: "(name list \<times> 'b list) list"
  and   T :: 'a
  and   x :: name

  assumes "x \<sharp> \<sigma>"
  and     "x \<sharp> T"

  shows "x \<sharp> T[<\<sigma>>]"
using assms
by(induct \<sigma> arbitrary: T) (clarsimp |  blast)+

lemma seq_subst2_chain[intro]:
  fixes \<sigma>    :: "(name list \<times> 'b list) list"
  and   T    :: 'a
  and   xvec :: "name list"

  assumes "xvec \<sharp>* \<sigma>"
  and     "xvec \<sharp>* T"

  shows "xvec \<sharp>* T[<\<sigma>>]"
using assms
by(induct xvec) auto

end

locale strong_subst_type =
  fixes subst :: "'a::fs_name \<Rightarrow> name list \<Rightarrow> 'b::fs_name list \<Rightarrow> 'a" ("_[_::=_]" [80, 80 ,80] 130)

  assumes eq[eqvt]: "\<And>p::name prm. (p \<bullet> (M[xvec::=Tvec])) = ((p \<bullet> M)[(p \<bullet> xvec)::=(p \<bullet> Tvec)])"
  and subst3:       "\<And>xvec Tvec T x. \<lbrakk>length xvec = length Tvec; distinct xvec; set(xvec) \<subseteq> supp(T); (x::name) \<sharp> T[xvec::=Tvec]\<rbrakk> \<Longrightarrow> x \<sharp> Tvec"
  and renaming:     "\<And>xvec Tvec p T. \<lbrakk>length xvec = length Tvec; (set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec);
                                      distinct_perm p; (p \<bullet> xvec) \<sharp>* T\<rbrakk> \<Longrightarrow>
                                      T[xvec::=Tvec] = (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]"
begin

lemma supp_subst:
  fixes M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  shows "(supp(M[xvec::=Tvec])::name set) \<subseteq> ((supp M) \<union> (supp xvec) \<union> (supp Tvec))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M)[([(x, y)] \<bullet> xvec)::=([(x, y)] \<bullet> Tvec)] \<noteq> M[xvec::=Tvec]"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> (M::'a)"
  let ?R = "\<lambda>y xvec. ([(x, y)] \<bullet> xvec) \<noteq> (xvec::name list)"
  let ?S = "\<lambda>y Tvec. ([(x, y)] \<bullet> Tvec) \<noteq> (Tvec::'b list)"
  assume A: "finite {y. ?Q y M}" and B: "finite {y. ?R y xvec}" and C: "finite {y. ?S y Tvec}" and D: "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M}  - {y. ?R y xvec}  - {y. ?S y Tvec})" 
    by(auto intro: Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?R y xvec) \<and> \<not> (?S y Tvec)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma subst2[intro]:
  fixes x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> Tvec"

  shows "x \<sharp> M[xvec::=Tvec]"
using assms supp_subst
by(auto simp add: fresh_def)

lemma subst2_chain[intro]:
  fixes yvec :: "name list"
  and   M    :: 'a
  and   xvec :: "name list"
  and   Tvec :: "'b list"
  
  assumes "yvec \<sharp>* M"
  and     "yvec \<sharp>* xvec"
  and     "yvec \<sharp>* Tvec"

  shows "yvec \<sharp>* M[xvec::=Tvec]"
using assms
by(induct yvec) auto

lemma fs[simp]: "finite ((supp subst)::name set)"
by(simp add: supp_def perm_fun_def eqvts)
(*
lemma subst1_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   Xs   :: "name set"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "Xs \<sharp>* T[xvec::=Tvec]"
  and     "Xs \<sharp>* xvec"

  shows "Xs \<sharp>* T"
using assms
by(auto intro: subst1 simp add: fresh_star_def)
*)
lemma subst3_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   Xs   :: "name set"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "set xvec \<subseteq> supp T"
  and     "Xs \<sharp>* T[xvec::=Tvec]"

  shows "Xs \<sharp>* Tvec"
using assms
by(auto intro: subst3 simp add: fresh_star_def)

lemma subst4_chain:
  fixes xvec :: "name list"
  and   Tvec :: "'b list"
  and   T    :: 'a

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "xvec \<sharp>* Tvec"

  shows "xvec \<sharp>* T[xvec::=Tvec]"
proof -
  obtain p where "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* T" and "(p \<bullet> xvec) \<sharp>* xvec"
             and S: "(set p) \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
             and "distinct_perm p"
    by(rule_tac xvec=xvec and c="(T, xvec)" in name_list_avoiding) auto 

  from `length xvec = length Tvec` have "length(p \<bullet> xvec) = length Tvec" by simp
  moreover from `(p \<bullet> xvec) \<sharp>* T` have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> T)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with `distinct_perm p` have "xvec \<sharp>* (p \<bullet> T)" by simp
  ultimately have "(set xvec) \<sharp>* (p \<bullet> T)[(p \<bullet> xvec)::=Tvec]" using `xvec \<sharp>* Tvec` `(p \<bullet> xvec) \<sharp>* xvec`
    by auto

  thus ?thesis using `length xvec = length Tvec` `distinct xvec` S `(p \<bullet> xvec) \<sharp>* T` `distinct_perm p`
    by(simp add: renaming)
qed

definition seq_subst :: "'a \<Rightarrow> (name list \<times> 'b list) list \<Rightarrow> 'a" ("_[<_>]" [80, 80] 130)
  where "M[<\<sigma>>] \<equiv> foldl (\<lambda>N. \<lambda>(xvec, Tvec). N[xvec::=Tvec]) M \<sigma>"

lemma seq_subst_nil[simp]:
  "seq_subst M [] = M"
by(simp add: seq_subst_def)

lemma seq_subst_cons[simp]:
  shows "seq_subst M ((xvec, Tvec)#\<sigma>) = seq_subst(M[xvec::=Tvec]) \<sigma>"
  by(simp add: seq_subst_def)

lemma seq_subst_term_append[simp]:
  shows "seq_subst M (\<sigma>@\<sigma>') = seq_subst (seq_subst M \<sigma>) \<sigma>'"
by(induct \<sigma>) (auto simp add: seq_subst_def)

definition well_formed_subst :: "(('d::fs_name) list \<times> ('e::fs_name) list) list \<Rightarrow> bool" where "well_formed_subst \<sigma> = ((filter (\<lambda>(xvec, Tvec). \<not>(length xvec = length Tvec \<and> distinct xvec)) \<sigma>) = [])"

lemma well_formed_subst_eqvt[eqvt]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"

  shows "p \<bullet> (well_formed_subst \<sigma>) = well_formed_subst(p \<bullet> \<sigma>)"
by(induct \<sigma> arbitrary: p) (auto simp add: eqvts well_formed_subst_def)

lemma well_formed_simp[simp]:
  fixes \<sigma> :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   p :: "name prm"
  
  shows "well_formed_subst(p \<bullet> \<sigma>) = well_formed_subst \<sigma>"
by(induct \<sigma>) (auto simp add: eqvts well_formed_subst_def)

lemma well_formed_nil[simp]:
  "well_formed_subst []"
by(simp add: well_formed_subst_def)

lemma well_formed_cons[simp]:
  shows "well_formed_subst((xvec, Tvec)#\<sigma>) = (length xvec = length Tvec \<and> distinct xvec \<and> well_formed_subst \<sigma>)"
by(simp add: well_formed_subst_def) auto

lemma well_formed_append[simp]:
  fixes \<sigma>  :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"
  and   \<sigma>' :: "(('d::fs_name) list \<times> ('e::fs_name) list) list"

  shows "well_formed_subst(\<sigma>@\<sigma>') = (well_formed_subst \<sigma> \<and> well_formed_subst \<sigma>')"
by(simp add: well_formed_subst_def)

lemma seq_subst2[intro]:
  fixes \<sigma> :: "(name list \<times> 'b list) list"
  and   T :: 'a
  and   x :: name

  assumes "x \<sharp> \<sigma>"
  and     "x \<sharp> T"

  shows "x \<sharp> T[<\<sigma>>]"
using assms
by(induct \<sigma> arbitrary: T) (clarsimp |  blast)+

lemma seq_subst2_chain[intro]:
  fixes \<sigma>    :: "(name list \<times> 'b list) list"
  and   T    :: 'a
  and   xvec :: "name list"

  assumes "xvec \<sharp>* \<sigma>"
  and     "xvec \<sharp>* T"

  shows "xvec \<sharp>* T[<\<sigma>>]"
using assms
by(induct xvec) auto

end

end