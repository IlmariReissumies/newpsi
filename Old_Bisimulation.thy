theory Old_Bisimulation
  imports Old_Simulation "NewPsi.Bisimulation"
begin

context old_psi begin

lemma old_mono_coinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto>[{(xc, xb, xa). x xc xb xa}]\<^sub>O P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto>[{(xb, xa, xc). y xb xa xc}]\<^sub>O P)"
by(auto intro: old_monotonic dest:le_funE)

coinductive_set old_bisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  step: "\<lbrakk>(insert_assertion (extract_frame P)) \<Psi> \<simeq>\<^sub>F (insert_assertion (extract_frame Q) \<Psi>);
          \<Psi> \<rhd> P \<leadsto>[old_bisim]\<^sub>O Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> old_bisim; (\<Psi>, Q, P) \<in> old_bisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> old_bisim"
monos old_mono_coinduct

abbreviation
  old_bisim_judge ("_ \<rhd> _ \<sim>\<^sub>O _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<sim>\<^sub>O Q \<equiv> (\<Psi>, P, Q) \<in> old_bisim"
abbreviation
  old_bisim_nil_judge ("_ \<sim>\<^sub>O _" [70, 70] 65) where "P \<sim>\<^sub>O Q \<equiv> S_bottom' \<rhd> P \<sim> Q"

lemma old_bisim_coinduct_aux[consumes 1]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi> \<and>
                                    (\<Psi> \<rhd> P \<leadsto>[(X \<union> old_bisim)]\<^sub>O Q) \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> old_bisim) \<and>
                                    ((\<Psi>, Q, P) \<in> X \<or> (\<Psi>, Q, P) \<in> old_bisim)"

  shows "(\<Psi>, P, Q) \<in> old_bisim"
proof -
  have "X \<union> old_bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> old_bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma old_bisim_coinduct[consumes 1, case_names c_stat_eq c_sim c_ext c_sym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> insert_assertion (extract_frame R) \<Psi>' \<simeq>\<^sub>F insert_assertion (extract_frame S) \<Psi>'"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[(X \<union> old_bisim)]\<^sub>O S"
  and     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> old_bisim"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> (\<Psi>', S, R) \<in> old_bisim"

  shows "(\<Psi>, P, Q) \<in> old_bisim"
proof -
  have "X \<union> old_bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> old_bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma old_bisimE:
  fixes P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "(\<Psi>, P, Q) \<in> old_bisim"

  shows "insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and   "\<Psi> \<rhd> P \<leadsto>[old_bisim]\<^sub>O Q"
  and   "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> old_bisim"
  and   "(\<Psi>, Q, P) \<in> old_bisim"
using assms
by(auto simp add: intro: old_bisim.cases)

lemma old_bisim_weak_coinduct_aux[consumes 1]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi> \<and>
                                     \<Psi> \<rhd> P \<leadsto>[X]\<^sub>O Q \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X) \<and> (\<Psi>, Q, P) \<in> X" 

  shows "(\<Psi>, P, Q) \<in> old_bisim"
using assms
by(coinduct rule: old_bisim_coinduct_aux) (blast intro: old_monotonic)

lemma old_bisim_sound:
  assumes "\<Psi> \<rhd> P \<sim>\<^sub>O Q"
  shows "\<Psi> \<rhd> P \<sim> Q"
  using assms
  by(coinduct rule: bisim_weak_coinduct) (auto intro: old_bisimE simp add: old_simulation_is_new[symmetric])

lemma old_bisim_weak_coinduct[consumes 1, case_names c_stat_eq c_sim c_ext c_sym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insert_assertion (extract_frame P) \<Psi> \<simeq>\<^sub>F insert_assertion (extract_frame Q) \<Psi>"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[X]\<^sub>O Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> old_bisim"
proof -
  have "X \<union> old_bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> old_bisim}" by auto
  with assms show ?thesis
  by(coinduct rule: old_bisim_coinduct) (blast intro: old_monotonic)+
qed

lemma old_bisim_complete:
  assumes "\<Psi> \<rhd> P \<sim> Q"
  shows "\<Psi> \<rhd> P \<sim>\<^sub>O Q"
  using assms
  by(coinduct rule: old_bisim_weak_coinduct) (auto intro: bisimE simp add: old_simulation_is_new)

lemma old_bisim_eq_bisim:
  shows "old_bisim = bisim"
  by(auto intro: old_bisim_sound old_bisim_complete)
  
end

end