theory Old_Tau_Chain
  imports Old_Semantics "NewPsi.Tau_Chain"
begin

context old_psi begin

abbreviation old_tau_chain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>\<^sub>O \<tau> \<prec> P'}^*"

abbreviation old_tau_step_chain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sub>\<tau>\<^sub>O _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau>\<^sub>O P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>\<^sub>O \<tau> \<prec> P'}^+"

abbreviation old_tau_context_chain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O _" [80, 80] 80)
where "P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P'"
abbreviation old_tau_context_step_chain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>\<tau>\<^sub>O _" [80, 80] 80)
where "P \<Longrightarrow>\<^sub>\<tau>\<^sub>O P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau>\<^sub>O P'"

lemmas tau_chain_induct[consumes 1, case_names tau_base tau_step] = rtrancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}", simplified] for \<Psi>
lemmas tau_step_chain_induct[consumes 1, case_names tau_base tau_step] = trancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>None @ \<tau> \<prec> P'}", simplified] for \<Psi>

definition old_weak_transition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>  ('a, 'b, 'c) psi \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ : _ \<rhd> _ \<Longrightarrow>\<^sub>O _ \<prec> _" [80, 80, 80, 80, 80] 80)
where
  "\<Psi> : Q \<rhd> P \<Longrightarrow>\<^sub>O \<alpha> \<prec> P' \<equiv> \<exists>P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P'' \<and> (insert_assertion (extract_frame Q) \<Psi>) \<hookrightarrow>\<^sub>F (insert_assertion (extract_frame P'') \<Psi>) \<and>
                                          \<Psi> \<rhd> P'' \<longmapsto>\<^sub>O \<alpha> \<prec> P'"

lemma old_tau_chain_new:
  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P' = \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  by(rule Set.eqset_imp_iff)
    (metis old_semantics_tau_sound old_semantics_complete)

lemma old_tau_step_chain_new:
  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau>\<^sub>O P' = \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  by(rule Set.eqset_imp_iff)
    (metis old_semantics_tau_sound old_semantics_complete)

lemma old_weak_transition_sound:
  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<^sub>O \<alpha> \<prec> P'"
  shows   "\<exists>\<pi>. \<Psi> : Q \<rhd> P \<Longrightarrow> \<pi> @ \<alpha> \<prec> P'"
  using assms
  by(force simp add: old_weak_transition_def weak_transition_def
                     old_tau_chain_new old_tau_step_chain_new
           dest: old_semantics_sound)

lemma old_weak_transition_tau_sound:
  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<^sub>O \<tau> \<prec> P'"
  shows   "\<Psi> : Q \<rhd> P \<Longrightarrow> None @ \<tau> \<prec> P'"
  using assms
  by(force simp add: old_weak_transition_def weak_transition_def
                     old_tau_chain_new old_tau_step_chain_new
           dest: old_semantics_tau_sound)

lemma old_weak_transition_complete:
  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow> \<pi> @ \<alpha> \<prec> P'"
  shows   "\<Psi> : Q \<rhd> P \<Longrightarrow>\<^sub>O \<alpha> \<prec> P'"
  using assms
  by(force simp add: old_weak_transition_def weak_transition_def
                     old_tau_chain_new old_tau_step_chain_new
           dest: old_semantics_complete)

end

end