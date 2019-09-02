(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Old_Weak_Simulation
  imports Old_Simulation Old_Tau_Chain
          "NewPsi.Weak_Simulation" "NewPsi.Weak_Stat_Imp"
          "NewPsi.Weak_Cong_Simulation"
begin

context old_psi begin

definition
  "oldWeakSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto><_>\<^sub>O _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto><Rel>\<^sub>O Q \<equiv> (\<forall>\<Psi>' \<alpha> Q'. \<Psi> \<rhd> Q \<longmapsto>\<^sub>O \<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> \<alpha> \<noteq> \<tau> \<longrightarrow>
                      (\<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<^sub>O \<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel))) \<and> 
                      (\<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>\<^sub>O \<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O P' \<and> (\<Psi>, P', Q') \<in> Rel))"

abbreviation
  oldWeakSimulationNilJudge ("_ \<leadsto><_>\<^sub>O _" [80, 80, 80] 80) where "P \<leadsto><Rel>\<^sub>O Q \<equiv> \<one> \<rhd> P \<leadsto><Rel>\<^sub>O Q"

lemma oldWeakSimulationEq:
  shows "(\<Psi> \<rhd> P \<leadsto><Rel>\<^sub>O Q) = \<Psi> \<rhd> P \<leadsto><Rel> Q" (is "?A = ?B")
proof(rule iffI)
  show "?A \<Longrightarrow> ?B"
    by(clarsimp simp add: weakSimulation_def oldWeakSimulation_def
                          old_tau_chain_new old_tau_step_chain_new)
      (blast dest: old_semantics_complete old_weak_transition_sound old_weak_transition_tau_sound)
next
  show "?B \<Longrightarrow> ?A"
    by(clarsimp simp add: weakSimulation_def oldWeakSimulation_def
                          old_tau_chain_new old_tau_step_chain_new)
      (blast dest: old_semantics_tau_sound old_semantics_sound old_weak_transition_complete)
qed

definition
  "old_weak_stat_imp" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                     ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                     ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<lessapprox><_>\<^sub>O _" [80, 80, 80, 80] 80)
where "\<Psi> \<rhd> P \<lessapprox><Rel>\<^sub>O Q \<equiv> \<forall>\<Psi>'. \<exists>Q' Q''. \<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O Q' \<and> insert_assertion(extract_frame P) \<Psi> \<hookrightarrow>\<^sub>F insert_assertion(extract_frame Q') \<Psi> \<and> \<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau>\<^sub>O Q'' \<and> (\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"

lemma old_weak_stat_imp_eq:
  shows "\<Psi> \<rhd> P \<lessapprox><Rel>\<^sub>O Q = \<Psi> \<rhd> P \<lessapprox><Rel> Q"
  by(simp add: old_weak_stat_imp_def weak_stat_imp_def old_tau_chain_new) 

definition
  "oldWeakCongSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>\<guillemotleft>_\<guillemotright>\<^sub>O _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright>\<^sub>O Q \<equiv> \<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>\<^sub>O \<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau>\<^sub>O P' \<and> (\<Psi>, P', Q') \<in> Rel)"

lemma old_weak_cong_simulation_eq:
  shows "(\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright>\<^sub>O Q) = \<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q" (is "?A = ?B")
proof(rule iffI)
  show "?A \<Longrightarrow> ?B"
    by(clarsimp simp add: weakCongSimulation_def oldWeakCongSimulation_def
                          old_tau_chain_new old_tau_step_chain_new)
      (blast dest: old_semantics_complete old_weak_transition_sound old_weak_transition_tau_sound)
next
  show "?B \<Longrightarrow> ?A"
    by(clarsimp simp add: weakCongSimulation_def oldWeakCongSimulation_def
                          old_tau_chain_new old_tau_step_chain_new)
      (blast dest: old_semantics_tau_sound old_semantics_sound old_weak_transition_complete)
qed

end

end
