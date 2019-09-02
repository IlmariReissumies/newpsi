(* 
   Title: Psi-calculi   
   Based on the AFP entry by Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Old_Weak_Bisimulation
  imports "NewPsi.Weak_Bisimulation" Old_Weak_Simulation "NewPsi.Weak_Stat_Imp"
          "NewPsi.Weak_Congruence"
begin

context old_psi begin

lemma oldMonoCoinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto><{(xc, xb, xa). x xc xb xa}>\<^sub>O P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto><{(xb, xa, xc). y xb xa xc}>\<^sub>O P)"
  unfolding oldWeakSimulationEq
  by(rule monoCoinduct)

lemma monoCoinduct2: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<lessapprox><{(xc, xb, xa). x xc xb xa}>\<^sub>O P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<lessapprox><{(xb, xa, xc). y xb xa xc}>\<^sub>O P)"
  unfolding old_weak_stat_imp_eq
  by(rule monoCoinduct2)

coinductive_set oldWeakBisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  old_step: "\<lbrakk>\<Psi> \<rhd> P \<lessapprox><oldWeakBisim>\<^sub>O Q; \<Psi> \<rhd> P \<leadsto><oldWeakBisim>\<^sub>O Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> oldWeakBisim; (\<Psi>, Q, P) \<in> oldWeakBisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> oldWeakBisim"
monos oldMonoCoinduct monoCoinduct2

abbreviation
  oldWeakBisimJudge ("_ \<rhd> _ \<approx>\<^sub>O _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<approx>\<^sub>O Q \<equiv> (\<Psi>, P, Q) \<in> oldWeakBisim"
abbreviation
  oldWeakBisimNilJudge ("_ \<approx>\<^sub>O _" [70, 70] 65) where "P \<approx>\<^sub>O Q \<equiv> \<one> \<rhd> P \<approx>\<^sub>O Q"

lemma old_weak_bisim_sound:
  assumes "\<Psi> \<rhd> P \<approx>\<^sub>O Q"
  shows "\<Psi> \<rhd> P \<approx> Q"
  using assms
  apply coinduct
  apply(erule oldWeakBisim.cases)
  apply(fastforce simp add: old_weak_stat_imp_eq oldWeakSimulationEq
                            weak_stat_imp_def weakSimulation_def)
  done

lemma old_weak_bisim_complete:
  assumes "\<Psi> \<rhd> P \<approx> Q"
  shows "\<Psi> \<rhd> P \<approx>\<^sub>O Q"
  using assms
  apply coinduct
  apply(erule weakBisim.cases)
  apply(fastforce simp add: old_weak_stat_imp_eq oldWeakSimulationEq
                            weak_stat_imp_def weakSimulation_def)
  done

lemma old_weak_bisim_eq_weak_bisim:
  shows "oldWeakBisim = weakBisim"
  by(auto intro: old_weak_bisim_sound old_weak_bisim_complete)

definition oldWeakPsiCongruence :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<doteq>\<^sub>O _" [70, 70, 70] 65)
where 
  "\<Psi> \<rhd> P \<doteq>\<^sub>O Q \<equiv> \<Psi> \<rhd> P \<approx>\<^sub>O Q \<and> \<Psi> \<rhd> P \<leadsto>\<guillemotleft>oldWeakBisim\<guillemotright>\<^sub>O Q \<and> \<Psi> \<rhd> Q \<leadsto>\<guillemotleft>oldWeakBisim\<guillemotright>\<^sub>O P"

lemma old_weak_psi_congruence_eq:
  "\<Psi> \<rhd> P \<doteq>\<^sub>O Q  =  \<Psi> \<rhd> P \<doteq> Q"
  by(simp add: oldWeakPsiCongruence_def weakPsiCongruence_def
               old_weak_bisim_eq_weak_bisim old_weak_cong_simulation_eq)

definition oldWeakCongruence :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<doteq>\<^sub>O _" [70, 70] 65)
where 
  "P \<doteq>\<^sub>O Q \<equiv> \<forall>\<Psi> \<sigma>. well_formed_subst \<sigma> \<longrightarrow> \<Psi> \<rhd> P[<\<sigma>>] \<doteq>\<^sub>O Q[<\<sigma>>]"

lemma old_weak_congruence_eq:
  "P \<doteq>\<^sub>O Q  =  weakCongruence P Q"
  by(simp add: oldWeakCongruence_def weakCongruence_def old_weak_psi_congruence_eq)

end