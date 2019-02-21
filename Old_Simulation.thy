theory Old_Simulation
  imports Old_Semantics Simulation
begin

context old_psi begin

definition
  "old_simulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                   ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                   ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>[_]\<^sub>O _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>[Rel]\<^sub>O Q \<equiv> \<forall>\<alpha> Q'. \<Psi> \<rhd> Q \<longmapsto>\<^sub>O\<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel)"

abbreviation
  old_simulation_nil_judge ("_ \<leadsto>[_]\<^sub>O _" [80, 80, 80] 80) where "P \<leadsto>[Rel]\<^sub>O Q \<equiv> S_bottom' \<rhd> P \<leadsto>[Rel]\<^sub>O Q"

lemma old_simulation_is_new:
  shows "\<Psi> \<rhd> P \<leadsto>[Rel]\<^sub>O Q = \<Psi> \<rhd> P \<leadsto>[Rel] Q"
  unfolding old_simulation_def simulation_def
  by(metis old_semantics_complete old_semantics_sound)

lemma old_simE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>[Rel]\<^sub>O Q"

  shows "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<^sub>O\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: old_simulation_def)

lemma old_monotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto>[A]\<^sub>O Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto>[B]\<^sub>O Q"
using assms
by(simp (no_asm) add: old_simulation_def) (auto dest: old_simE)

end

end