(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Close_Subst
  imports Agent Subst_Term
begin

context subst_psi
begin

definition close_subst :: "('b::fs_name \<times> ('a::fs_name, 'b, 'c::fs_name) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
where "close_subst Rel \<equiv> {(\<Psi>, P, Q) | \<Psi> P Q. (\<forall>\<sigma>. well_formed_subst \<sigma> \<longrightarrow> (\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel)}"

lemma close_substI:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<And>\<sigma>. well_formed_subst \<sigma> \<Longrightarrow> (\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel"

  shows "(\<Psi>, P, Q) \<in> close_subst Rel"
using assms
by(unfold close_subst_def) auto

lemma close_substE:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "(\<Psi>, P, Q) \<in> close_subst Rel"
  and     "well_formed_subst \<sigma>"

  shows "(\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel"
using assms
by(unfold close_subst_def) auto

lemma close_subst_closed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"

  assumes "eqvt Rel"
  and     "(\<Psi>, P, Q) \<in> close_subst Rel"

  shows "(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> close_subst Rel"
proof(rule close_substI)
  fix \<sigma>
  assume "well_formed_subst(\<sigma>::(name list \<times> 'a list) list)"
  with `(\<Psi>, P, Q) \<in> close_subst Rel` `well_formed_subst \<sigma>`
  have "(\<Psi>, P[<(rev p \<bullet> \<sigma>)>], Q[<(rev p \<bullet> \<sigma>)>]) \<in> Rel"
    by(rule_tac close_substE) auto
  hence "(p \<bullet> \<Psi>, p \<bullet> (P[<(rev p \<bullet> \<sigma>)>]), p \<bullet> (Q[<(rev p \<bullet> \<sigma>)>])) \<in> Rel"
    by(drule_tac p=p in eqvtI[OF `eqvt Rel`]) (simp add: eqvts)
  thus "(p \<bullet> \<Psi>, (p \<bullet> P)[<\<sigma>>], (p \<bullet> Q)[<\<sigma>>]) \<in> Rel"
    by(simp del: seq_subs_def add: eqvts)
qed

lemma close_subst_eqvt:
  assumes "eqvt Rel"

  shows "eqvt(close_subst Rel)"
proof(auto simp add: eqvt_def)
  fix \<Psi> P Q p
  assume "(\<Psi>, P, Q) \<in> close_subst Rel"
  thus "((p::name prm) \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> close_subst Rel"
    by(drule_tac p=p in close_subst_closed[OF `eqvt Rel`]) (simp add: eqvts)
qed

lemma close_subst_unfold:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"

  assumes "(\<Psi>, P, Q) \<in> close_subst Rel"
  and     "well_formed_subst \<sigma>"

  shows "(\<Psi>, P[<\<sigma>>], Q[<\<sigma>>]) \<in> close_subst Rel"
proof(rule close_substI)
  fix \<sigma>'::"(name list \<times> 'a list) list"
  assume "well_formed_subst \<sigma>'"
  with `well_formed_subst \<sigma>` have "well_formed_subst(\<sigma>@\<sigma>')" by simp
  with `(\<Psi>, P, Q) \<in> close_subst Rel` have "(\<Psi>, P[<(\<sigma>@\<sigma>')>], Q[<(\<sigma>@\<sigma>')>]) \<in> Rel"
    by(rule close_substE)
  thus "(\<Psi>, P[<\<sigma>>][<\<sigma>'>], Q[<\<sigma>>][<\<sigma>'>]) \<in> Rel"
    by simp
qed

end

end
  

  


