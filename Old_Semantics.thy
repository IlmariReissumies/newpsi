theory Old_Semantics
  imports "NewPsi.Semantics"
begin

locale old_psi = env subst_term subst_assert subst_cond S_compose' S_imp' S_bottom' S_chan_eq'
  for subst_term :: "('a::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'a"
  and subst_assert :: "('b::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'b"
  and subst_cond :: "('c::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'c"
  and S_compose'  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and S_imp'      :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  and S_bottom'   :: 'b
  and S_chan_eq'   :: "'a \<Rightarrow> 'a \<Rightarrow> 'c" +

  assumes chan_eq_sym: "S_imp' \<Psi> (S_chan_eq' M N) \<Longrightarrow> S_imp' \<Psi> (S_chan_eq' N M)"
  and chan_eq_trans: "\<lbrakk>S_imp' \<Psi> (S_chan_eq' M N); S_imp' \<Psi> (S_chan_eq' N L)\<rbrakk> \<Longrightarrow> S_imp' \<Psi> (S_chan_eq' M L)"
begin

inductive old_semantics :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) residual \<Rightarrow> bool"
                       ("_ \<rhd> _ \<longmapsto>\<^sub>O _" [50, 50, 50] 50)
where
  c_input:  "\<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N; xvec \<sharp>* Tvec;
            length xvec = length Tvec;
            xvec \<sharp>* \<Psi>; xvec \<sharp>* M; xvec \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<^sub>O K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
| Output: "\<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<^sub>O K\<langle>N\<rangle> \<prec> P"
| Case:   "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O Rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> Cases Cs \<longmapsto>\<^sub>O Rs"

| c_par1:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>)\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<^sub>O\<alpha> \<prec> (P' \<parallel> Q)"
| c_par2:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<^sub>O\<alpha> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* (subject \<alpha>)\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<^sub>O\<alpha> \<prec> (P \<parallel> Q')"
| c_comm1:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>O M\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>O K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; 
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<^sub>O \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| c_comm2:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>O M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>O K\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; 
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<^sub>O \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| c_open:    "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; x \<sharp> xvec; x \<sharp> yvec; x \<sharp> M; x \<sharp> \<Psi>;
              distinct xvec; distinct yvec;
              xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M\<rbrakk> \<Longrightarrow>
              \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<^sub>O M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
| c_scope:  "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<^sub>O\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')"
| Bang:    "\<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>O Rs; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> !P \<longmapsto>\<^sub>O Rs"

abbreviation
  old_semantics_bottom_judge ("_ \<longmapsto>\<^sub>O _" [50, 50] 50) where "P \<longmapsto>\<^sub>O Rs \<equiv> \<one> \<rhd> P \<longmapsto>\<^sub>O Rs"

equivariance old_psi.old_semantics

nominal_inductive2 old_psi.old_semantics
  avoids c_input: "set xvec"
       | c_par1: "set A\<^sub>Q \<union> set(bn \<alpha>)"
       | c_par2: "set A\<^sub>P \<union> set(bn \<alpha>)"
       | c_comm1: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec"
       | c_comm2: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec"
       | c_open:  "{x} \<union> set xvec \<union> set yvec"
       | c_scope: "{x} \<union> set(bn \<alpha>)"
apply(auto intro: subst_term.subst4_chain subst4_chain simp add: abs_fresh residual_fresh)
apply(force simp add: fresh_star_def abs_fresh)
apply(simp add: bound_output_fresh)
apply(simp add: bound_output_fresh_set)
apply(simp add: bound_output_fresh_set)
by(simp add: fresh_star_def abs_fresh)

lemma old_nil_trans[dest]:
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

  shows "\<Psi> \<rhd> \<zero> \<longmapsto>\<^sub>O Rs \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<^sub>OK\<lparr>\<nu>*yvec\<rparr>\<langle>N'\<rangle> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<^sub>O\<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<^sub>OK\<lparr>N'\<rparr> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<^sub>O\<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> \<lbrace>\<Psi>'\<rbrace> \<longmapsto>\<^sub>O Rs \<Longrightarrow> False"
apply(cases rule: old_semantics.cases) apply auto
apply(cases rule: old_semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: old_semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: old_semantics.cases) apply(auto simp add: residual_inject)
apply(cases rule: old_semantics.cases) apply(auto simp add: residual_inject)
by(cases rule: old_semantics.cases) (auto simp add: residual_inject)

lemma old_semantics_induct[consumes 3, case_names c_alpha c_input c_output c_case c_par1 c_par2 c_comm1 c_comm2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* (subject \<alpha>)"
  and     "distinct(bn \<alpha>)"
  and     r_alpha: "\<And>\<Psi> P \<alpha> P' p C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); 
                                    bn \<alpha> \<sharp>* C; bn \<alpha> \<sharp>* (bn(p \<bullet> \<alpha>)); 
                                    set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinct_perm p;
                                    (bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; Prop C \<Psi> P \<alpha> P'\<rbrakk> \<Longrightarrow>
                                     Prop C \<Psi> P (p \<bullet> \<alpha>) (p \<bullet> P')"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              (K\<lparr>(N[xvec::=Tvec])\<rparr>) (P[xvec::=Tvec])"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (K\<langle>N\<rangle>) P"
  and     r_case: "\<And>\<Psi> P \<alpha> P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<alpha> P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                      Prop C \<Psi> (Cases Cs) \<alpha> P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>O\<alpha> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>N\<rparr>) P'; 
                    extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OK\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q'; 
                    extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P'; 
                    extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OK\<lparr>N\<rparr> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>N\<rparr>) Q'; 
                    extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_open:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;  distinct xvec; distinct yvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     r_scope: "\<And>\<Psi> P \<alpha> P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<alpha> P';
                    x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>;
                    bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); x \<sharp> C; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P \<alpha> P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>O\<alpha> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<alpha> P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) \<alpha> P'"

  shows "Prop C \<Psi> P \<alpha> P'"
using `\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'` `bn \<alpha> \<sharp>* (subject \<alpha>)` `distinct(bn \<alpha>)`
proof(nominal_induct x3=="\<alpha> \<prec> P'" avoiding: \<alpha> C arbitrary: P' rule: old_semantics.strong_induct)
  case(c_input \<Psi> M K xvec N Tvec P \<alpha> C P')
  thus ?case by(force intro: r_input simp add: residual_inject)
next
  case(Output \<Psi> M K N P \<alpha> C P')
  thus ?case by(force intro: r_output simp add: residual_inject)
next
  case(Case \<Psi> P \<phi> Cs \<alpha> C P')
  thus ?case by(auto intro: r_case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q \<alpha>' C P'')
  note `\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> Q)" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (P' \<parallel> Q)" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P' \<parallel> Q)"
    by(rule residual_eq)
    
  note `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'` `extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>` `distinct A\<^sub>Q`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P'" by(rule_tac c_par1) auto
  moreover note `A\<^sub>Q \<sharp>* P` `A\<^sub>Q \<sharp>* Q` `A\<^sub>Q \<sharp>* \<Psi>` `A\<^sub>Q \<sharp>* \<alpha>` `A\<^sub>Q \<sharp>* P'` `A\<^sub>Q \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>Q` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q)"
    by(rule_tac r_par1)

  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* bn \<alpha>'` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> Q)` `A\<^sub>Q \<sharp>* C`
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> Q))"
    by(rule_tac r_alpha) auto
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P \<alpha>' C Q'')
  note `\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> Q''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> Q')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> Q'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and Q'eq: "Q'' = p \<bullet> (P \<parallel> Q')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P \<parallel> Q')"
    by(rule residual_eq)
    
  note `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>O\<alpha> \<prec> Q'` `extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>` `distinct A\<^sub>P`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q'" by(rule_tac c_par2) auto

  moreover note `A\<^sub>P \<sharp>* P` `A\<^sub>P \<sharp>* Q` `A\<^sub>P \<sharp>* \<Psi>` `A\<^sub>P \<sharp>* \<alpha>` `A\<^sub>P \<sharp>* Q'` `A\<^sub>P \<sharp>* C`
                `bn \<alpha> \<sharp>* Q` `distinct(bn \<alpha>)` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* \<Psi>\<^sub>P` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C`
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q')"
    by(rule_tac r_par2)
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* Q` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> Q')`
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> Q'))"
    by(rule_tac r_alpha) auto
  with \<alpha>Eq Q'eq `distinct_perm p` show ?case by simp
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac r_comm1) (assumption | simp)+
  thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''`
    by(simp add: residual_inject)
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac r_comm2) (assumption | simp)+
  thus ?case using `\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''`
    by(simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec yvec N P' x \<alpha> C P'')
  note `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
  moreover from `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>` have "(xvec@x#yvec) \<sharp>* (bn \<alpha>)"
    by auto
  moreover from `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `distinct xvec` `distinct yvec`
  have "distinct(xvec@x#yvec)"
    by(auto simp add: fresh_star_def)
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
    
  note `\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<in> (supp N)`

  moreover {
    fix C
    from `xvec \<sharp>* M` `yvec \<sharp>* M` have "(xvec@yvec) \<sharp>* M" by simp
    moreover from `distinct xvec` `distinct yvec` `xvec \<sharp>* yvec` have "distinct(xvec@yvec)"
      by auto
    ultimately have "Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P'" by(rule_tac c_open) auto
  }

  moreover note `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* M`
                 `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M` `yvec \<sharp>* C` `x \<sharp> C` `xvec \<sharp>* C` `distinct xvec` `distinct yvec`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
    by(rule_tac r_open) 

  with `xvec \<sharp>* \<Psi>` `yvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `yvec \<sharp>* P` `xvec \<sharp>* M` `yvec \<sharp>* M` 
       `yvec \<sharp>* C`  S `distinct_perm p` `x \<sharp> C` `xvec \<sharp>* C`
       `x \<sharp> \<Psi>` `x \<sharp> M` `x \<sharp> xvec` `x \<sharp> yvec` A B C
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (p \<bullet> (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)) (p \<bullet> P')"
    by(rule_tac \<alpha>="M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>" in r_alpha) (auto simp add: fresh_star_def abs_fresh)
  with \<alpha>eq P'eq show ?case by simp
next
  case(c_scope \<Psi> P \<alpha> P' x \<alpha>' C P'')
  note `\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P') = \<alpha>' \<prec> P''`
  moreover from `bn \<alpha> \<sharp>* \<alpha>'` have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note `distinct (bn \<alpha>)` `distinct(bn \<alpha>')`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha>' \<sharp>* subject \<alpha>'`
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinct_perm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (\<lparr>\<nu>x\<rparr>P')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (\<lparr>\<nu>x\<rparr>P')"
    by(rule residual_eq)
    
  note `\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'`
  moreover from `bn \<alpha> \<sharp>* subject \<alpha>` `distinct(bn \<alpha>)`
  have "\<And>C. Prop C \<Psi> P \<alpha> P'" by(rule_tac c_scope) auto

  moreover note `x \<sharp> \<Psi>` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha>`
                `x \<sharp> C` `bn \<alpha> \<sharp>* C` `distinct(bn \<alpha>)`
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
    by(rule r_scope) 
  with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `x \<sharp> \<alpha>` `bn \<alpha> \<sharp>* subject \<alpha>` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* (bn \<alpha>')` S `distinct_perm p` `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* (\<lparr>\<nu>x\<rparr>P')`
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (p \<bullet> \<alpha>) (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))"
    by(rule_tac r_alpha) simp+
  with \<alpha>Eq P'eq `distinct_perm p` show ?case by simp
next
  case(Bang \<Psi> P \<alpha> C P')
  thus ?case by(rule_tac r_bang) auto
qed

lemma old_output_induct[consumes 1, case_names c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) bound_output"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) bound_output \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>OR_out M B"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) K (N \<prec>' P)"
  and     r_case: "\<And>\<Psi> P M B \<phi> Cs C.  
                  \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O(R_out M B); \<And>C. Prop C \<Psi> P M B; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                   Prop C \<Psi> (Cases Cs) M B"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q))"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q');
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* P;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q'))"
  and     r_open:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P')"
  and     r_scope: "\<And>\<Psi> P M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;
                    x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' \<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P M B C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>O(R_out M B); guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M B\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) M B"
  shows "Prop C \<Psi> P M B"
using `\<Psi> \<rhd> P \<longmapsto>\<^sub>O(R_out M B)`
proof(nominal_induct \<Psi> P Rs=="(R_out M B)" avoiding: C arbitrary: B rule: old_semantics.strong_induct)
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
  thus ?case by(force intro: r_par1 simp add: residual_inject)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P C)
  thus ?case by(force intro: r_par2 simp add: residual_inject)
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

lemma old_bound_output_bind_object:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "y \<in> set(bn \<alpha>)"

  shows "y \<in> supp(object \<alpha>)"
using assms
proof(nominal_induct avoiding: P' arbitrary: y rule: old_semantics_induct)
  case(c_alpha \<Psi> P \<alpha> P' p P'' y)
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

lemma old_bound_output_distinct:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<alpha> \<prec> P'"

  shows "distinct(bn \<alpha>)"
using assms
thm old_semantics.strong_induct
proof(nominal_induct \<Psi> P x3=="\<alpha> \<prec> P'" avoiding: \<alpha> P' rule: old_semantics.strong_induct)
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
  thus ?case by(force intro: alpha_distinct old_bound_output_bind_object)
next
  case c_par2
  thus ?case by(force intro: alpha_distinct old_bound_output_bind_object)
next 
  case c_comm1
  thus ?case by(simp add: residual_inject)
next
  case c_comm2
  thus ?case by(simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec yvec N P' x \<alpha> P'')
  note `M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''`
  moreover from `xvec \<sharp>* yvec` `x \<sharp> xvec` `x \<sharp> yvec` `distinct xvec` `distinct yvec`
  have "distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
    by auto
  moreover {
    fix y
    from `\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'` `x \<in> supp N` `x \<sharp> xvec` `x \<sharp> yvec` `x \<sharp> M` `x \<sharp> \<Psi>` `distinct xvec` `distinct yvec` `xvec \<sharp>* \<Psi>` `xvec \<sharp>* P` `xvec \<sharp>* M` `xvec \<sharp>* yvec` `yvec \<sharp>* \<Psi>` `yvec \<sharp>* P` `yvec \<sharp>* M`
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule old_semantics.c_open)
    moreover moreover from `xvec \<sharp>* M` `x \<sharp> M` `yvec \<sharp>* M` 
    have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* (subject(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by simp
    moreover note `distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))`
    moreover assume "y \<in> set(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"

    ultimately have "y \<in> supp(object(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by(rule_tac old_bound_output_bind_object)
  }
  moreover from `xvec \<sharp>* \<alpha>` `x \<sharp> \<alpha>` `yvec \<sharp>* \<alpha>`
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* bn \<alpha>" and "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* object \<alpha>" by simp+
  moreover from `xvec \<sharp>* P''` `x \<sharp> P''` `yvec \<sharp>* P''`
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* P''" by simp
  ultimately show ?case by(rule alpha_distinct)
next
  case c_scope
  thus ?case
    by(rule_tac alpha_distinct, auto) (rule_tac old_bound_output_bind_object, auto)
next
  case Bang
  thus ?case by simp
qed

lemma old_input_distinct:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"

  assumes "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<^sub>O Rs"

  shows "distinct xvec"
using assms
by(nominal_induct \<Psi> P=="M\<lparr>\<lambda>*xvec N\<rparr>.P" Rs avoiding: xvec N P rule: old_semantics.strong_induct)
  (auto simp add: psi.inject intro: alpha_input_distinct)

lemma output_induct'[consumes 2, case_names c_alpha c_output c_case c_par1 c_par2 c_open c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     r_alpha: "\<And>\<Psi> P M xvec N P' p C. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;  xvec \<sharp>* C; xvec \<sharp>* (p \<bullet> xvec); 
                                           set p \<subseteq> set xvec \<times> set(p \<bullet> xvec); distinct_perm p;
                                           (p \<bullet> xvec) \<sharp>* N; (p \<bullet> xvec) \<sharp>* P'; Prop C \<Psi> P M xvec N P'\<rbrakk> \<Longrightarrow>
                                           Prop C \<Psi> P M (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P')"
  and     r_output: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) K ([]) N P"
  and     r_case: "\<And>\<Psi> P M xvec N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M xvec N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                             Prop C \<Psi> (Cases Cs) M xvec N P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M xvec N P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M xvec N (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M xvec N Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M xvec N (P \<parallel> Q')"
  and     r_open:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P M (xvec@yvec) N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; 
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (xvec@x#yvec) N P'"
  and     r_scope: "\<And>\<Psi> P M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M xvec N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* P; xvec \<sharp>* M; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M xvec N (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P M xvec N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M xvec N P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) M xvec N P'"
  shows "Prop C \<Psi> P M xvec N P'"
proof -
  note `\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
  moreover from `xvec \<sharp>* M` have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from `\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'` have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))"
    by(rule old_bound_output_distinct)
  ultimately show ?thesis
  proof(nominal_induct \<Psi> P \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: C arbitrary: M xvec N rule: old_semantics_induct)
    case(c_alpha \<Psi> P \<alpha> P' p C M xvec N)
    from `(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>` have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)"
      by(simp add: fresh_bij)
    with `distinct_perm p` have A: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>"
      by(simp add: eqvts)
    with `bn \<alpha> \<sharp>* \<Psi>` `bn \<alpha> \<sharp>* P` `bn \<alpha> \<sharp>* subject \<alpha> ` `bn \<alpha> \<sharp>* C` `bn \<alpha> \<sharp>* bn(p \<bullet> \<alpha>)` `distinct_perm p`
    have "(p \<bullet> xvec) \<sharp>* \<Psi>" and  "(p \<bullet> xvec) \<sharp>* P" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" and  "(p \<bullet> xvec) \<sharp>* C" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> xvec)"
      by auto
    moreover from A `set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))` `distinct_perm p`
    have S: "set p \<subseteq> set(p \<bullet> xvec) \<times> set(p \<bullet> p \<bullet> xvec)" by simp
    moreover note `distinct_perm p`
    moreover from A `bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>` `bn(p \<bullet> \<alpha>) \<sharp>* P'`
    have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> N)" and "(p \<bullet> p \<bullet> xvec) \<sharp>* P'" by simp+
    moreover from A have "Prop C \<Psi> P (p \<bullet> M) (p \<bullet> xvec) (p \<bullet> N) P'"
      by(rule c_alpha)
    ultimately have "Prop C \<Psi> P (p \<bullet> M) (p \<bullet> p \<bullet> xvec) (p \<bullet> p \<bullet> N) (p \<bullet> P')"
      by(rule r_alpha)
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
    thus ?case by(force intro: r_par1)
  next
    case c_par2
    thus ?case by(force intro: r_par2)
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
    thus ?case by(auto intro: r_bang)
  qed
qed

lemma old_input_induct[consumes 1, case_names c_input c_case c_par1 c_par2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'"
  and     r_input: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec])"
  and     r_case: "\<And>\<Psi> P M N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P M N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                        Prop C \<Psi> (Cases Cs) M N P'" 
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M N P'; distinct A\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M N Q'; distinct A\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P \<parallel> Q')"
  and     r_scope: "\<And>\<Psi> P M N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P M N P'; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M N (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P M N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M N P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) M N P'"
  shows "Prop C \<Psi> P M N P'"
using Trans
proof(nominal_induct \<Psi> P Rs=="M\<lparr>N\<rparr> \<prec> P'" avoiding: C arbitrary: P' rule: old_semantics.strong_induct)
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
  thus ?case by(force intro: r_par1 simp add: residual_inject)
next 
  case(c_par2 \<Psi> \<Psi>P Q \<alpha> Q' xvec P C Q'')
  thus ?case by(force intro: r_par2 simp add: residual_inject)
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
  thus ?case by(force intro: r_bang)
qed

lemma old_tau_induct[consumes 1, case_names c_case c_par1 c_par2 c_comm1 c_comm2 c_scope c_bang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<tau> \<prec> P'"
  and     r_case: "\<And>\<Psi> P P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                                    Prop C \<Psi> (Cases Cs) P'"
  and     r_par1: "\<And>\<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>O\<tau> \<prec> P'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P P';
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P' \<parallel> Q)"
  and     r_par2: "\<And>\<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>O\<tau> \<prec> Q'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q Q';
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P \<parallel> Q')"
  and     r_comm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>N\<rparr> \<prec> P'; extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OK\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_comm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<^sub>OM\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';  extract_frame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<^sub>OK\<lparr>N\<rparr> \<prec> Q'; extract_frame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     r_scope: "\<And>\<Psi> P P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<^sub>O\<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; x \<sharp> \<Psi>; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<lparr>\<nu>x\<rparr>P')"
  and     r_bang:    "\<And>\<Psi> P P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<^sub>O\<tau> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P'"
  shows "Prop C \<Psi> P P'"
using Trans
proof(nominal_induct \<Psi> P Rs=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: old_semantics.strong_induct)
  case(c_input M K xvec N Tvec P C)
  thus ?case by(simp add: residual_inject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(simp add: residual_inject)
next
  case(Case \<Psi> P \<phi> Cs C P')
  thus ?case by(force intro: r_case simp add: residual_inject)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q C P'')
  thus ?case by(force intro: r_par1 simp add: residual_inject)
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P C Q'')
  thus ?case by(force intro: r_par2 simp add: residual_inject)
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C PQ)
  thus ?case by(force intro: r_comm1 simp add: residual_inject)
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>P Q' A\<^sub>Q C PQ)
  thus ?case by(force intro: r_comm2 simp add: residual_inject)
next
  case(c_open \<Psi> P M xvec N P' x yvec C P'')
  thus ?case by(simp add: residual_inject)
next
  case(c_scope \<Psi> P \<alpha> P' x C P'')
  thus ?case by(force intro: r_scope simp add: residual_inject)
next
  case(Bang \<Psi> P C P')
  thus ?case by(force intro: r_bang simp add: residual_inject)
qed

lemma old_semantics_complete:
  assumes "\<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"
  shows "\<Psi> \<rhd> P \<longmapsto>\<^sub>O Rs"
  using assms
proof(nominal_induct rule: semantics.strong_induct)
  case c_input
  thus ?case
    by(rule_tac old_semantics.c_input) (auto intro: chan_eq_sym)
next
  case Output
  thus ?case
    by(rule_tac old_semantics.Output)
next
  case Case
  thus ?case
    by(rule_tac old_semantics.Case)
next
  case c_par1
  thus ?case
    by(rule_tac old_semantics.c_par1)
next
  case c_par2
  thus ?case
    by(rule_tac old_semantics.c_par2)
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec xvec Q')
  moreover hence "(\<Psi>\<otimes>\<Psi>\<^sub>P)\<otimes>\<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    apply(rule_tac output_provenance'')
    unfolding residual_inject
    by(assumption|auto)+
  hence "\<Psi>\<otimes>\<Psi>\<^sub>P\<otimes>\<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    by(metis Associativity stat_eq_ent)
  ultimately show ?case
    by(rule_tac old_semantics.c_comm1)
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P A\<^sub>P yvec K M xvec N P' \<Psi>\<^sub>P Q A\<^sub>Q zvec Q')
  moreover hence "(\<Psi>\<otimes>\<Psi>\<^sub>P)\<otimes>\<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
    by(rule_tac input_provenance'') (assumption|auto)+
  hence "\<Psi>\<otimes>\<Psi>\<^sub>P\<otimes>\<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    by(metis Associativity stat_eq_ent chan_eq_sym)
  ultimately show ?case
    by(rule_tac old_semantics.c_comm2)
next
  case c_open
  thus ?case
    by(rule_tac old_semantics.c_open)
next
  case c_scope
  thus ?case
    by(rule_tac old_semantics.c_scope)
next
  case Bang
  thus ?case
    by(rule_tac old_semantics.Bang)
qed

lemma old_semantics_input_sound:
  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O M\<lparr>N\<rparr> \<prec> P'"  
  shows "\<exists> \<pi>. \<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
  using assms
proof(nominal_induct rule: old_input_induct)
  case(c_input \<Psi> M K xvec N Tvec P)
  thus ?case by(metis chan_eq_sym Input)
next
  case(c_case \<Psi> P M N P' \<phi> Cs)
  thus ?case by(metis semantics.Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q)
  thus ?case by(auto dest: Par1)  
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P)
  thus ?case by(auto dest: Par2)
next
  case c_scope
  thus ?case by(auto dest: Scope)
next
  case c_bang
  thus ?case by(auto dest: semantics.Bang)
qed

lemma old_semantics_output_sound:
  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O R_out M B"
  shows "\<exists> \<pi>. \<Psi> \<rhd> P \<longmapsto> \<pi> @ R_out M B"
  using assms
proof(nominal_induct rule: old_output_induct)
  case(c_output \<Psi> M K N P)
  thus ?case
    by(auto dest!: semantics.Output[where P=P] simp add: residual_inject)
next
  case(c_case \<Psi> P M B \<phi> Cs)
  thus ?case by(metis semantics.Case)
next
  case(c_par1 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q)
  thus ?case using Par1[where \<alpha>="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(simp add: residual_inject) blast
next
  case(c_par2 \<Psi> \<Psi>\<^sub>P Q M xvec N Q' A\<^sub>P P)
  thus ?case using Par2[where \<alpha>="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(simp add: residual_inject) blast  
next
  case(c_open \<Psi> P M xvec yvec N P' x)
  moreover then obtain \<pi> where "\<Psi> \<rhd> P \<longmapsto> Some \<pi> @ R_out M (\<lparr>\<nu>*(xvec @ yvec)\<rparr>N \<prec>' P')"
    apply auto
    by(frule_tac output_provenance) auto
  ultimately show ?case using Open
    by(simp add: residual_inject) blast
next
  case(c_scope \<Psi> P M xvec N P' x)
  thus ?case using Scope[where \<alpha>="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(simp add: residual_inject) blast
next
  case c_bang
  thus ?case by(auto dest: semantics.Bang)
qed

lemma old_semantics_output_sound':
  fixes C::"'ty :: fs_name"  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<^sub>O M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "A\<^sub>P \<sharp>* P"
  shows "\<exists> zvec K. \<Psi> \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<and> distinct zvec \<and> zvec \<sharp>* \<Psi> \<and> zvec \<sharp>* M \<and> zvec \<sharp>* P \<and> zvec \<sharp>* xvec \<and> zvec \<sharp>* N \<and> zvec \<sharp>* C \<and> A\<^sub>P \<sharp>* zvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
proof -
  from Trans obtain \<pi> where "\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    unfolding residual_inject
    by(auto dest: old_semantics_output_sound)
  moreover hence "A\<^sub>P \<sharp>* \<pi>" using `A\<^sub>P \<sharp>* P`
    by(auto intro: trans_fresh_provenance)
  ultimately show ?thesis using assms
    unfolding residual_inject
    by(frule_tac output_provenance'[where B="(\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')" and C="(C,xvec,P')"]) force+
qed

lemma old_semantics_input_sound':
  fixes C::"'ty :: fs_name"  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<^sub>O M\<lparr>N\<rparr> \<prec> P'"
  and "extract_frame P = \<langle>A\<^sub>P,\<Psi>\<^sub>P\<rangle>"
  and "distinct A\<^sub>P"
  and "A\<^sub>P \<sharp>* \<Psi>"
  and "A\<^sub>P \<sharp>* M"
  and "A\<^sub>P \<sharp>* P"
  shows "\<exists> zvec K. \<Psi> \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K\<rangle>) @ M\<lparr>N\<rparr> \<prec> P' \<and> distinct zvec \<and> zvec \<sharp>* \<Psi> \<and> zvec \<sharp>* M \<and> zvec \<sharp>* P \<and> zvec \<sharp>* N \<and> zvec \<sharp>* C \<and> A\<^sub>P \<sharp>* zvec \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
proof -
  from Trans obtain \<pi> where "\<Psi> \<rhd> P \<longmapsto> \<pi> @ M\<lparr>N\<rparr> \<prec> P'"
    by(auto dest: old_semantics_input_sound)
  moreover hence "A\<^sub>P \<sharp>* \<pi>" using `A\<^sub>P \<sharp>* P`
    by(auto intro: trans_fresh_provenance)
  ultimately show ?thesis using assms
    by(frule_tac input_provenance') force+
qed

lemma old_semantics_tau_sound:
  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O \<tau> \<prec> P'"  
  shows "\<Psi> \<rhd> P \<longmapsto> None @ \<tau> \<prec> P'"
  using assms
proof(nominal_induct rule: old_tau_induct)
  case c_case
  thus ?case
    by(auto dest: semantics.Case)
next
  case c_par1
  thus ?case
    by(auto dest: Par1)
next
  case c_par2
  thus ?case
    by(auto dest: Par2)
next
  case(c_comm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q)
  then obtain zvec K' where  "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'" "distinct zvec" "zvec \<sharp>* \<Psi>" "zvec \<sharp>* M" "zvec \<sharp>* P" "zvec \<sharp>* N" "zvec \<sharp>* Q" "zvec \<sharp>* A\<^sub>Q" "zvec \<sharp>* \<Psi>\<^sub>Q" "zvec \<sharp>* \<Psi>\<^sub>P" "A\<^sub>P \<sharp>* zvec" "zvec \<sharp>* K" "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
    by(auto dest!: old_semantics_input_sound'[where C="(Q,A\<^sub>Q,\<Psi>\<^sub>Q,\<Psi>\<^sub>P,K,\<Psi>)"])
  from c_comm1 obtain yvec M' where  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" "distinct yvec" "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* P" "yvec \<sharp>* N" "yvec \<sharp>* Q" "A\<^sub>Q \<sharp>* yvec" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>P" "A\<^sub>P \<sharp>* yvec" "yvec \<sharp>* K" "yvec \<sharp>* zvec" "yvec \<sharp>* xvec" "yvec \<sharp>* K'" "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K"
    by(auto dest!: old_semantics_output_sound'[where C="(P,A\<^sub>P,\<Psi>\<^sub>Q,\<Psi>\<^sub>P,K,M,\<Psi>,zvec,K')"])
  hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M' \<leftrightarrow> K'" using `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'`
    by (metis Assertion_stat_eq_sym Assertion_stat_imp_def Associativity associativity_sym chan_eq_sym chan_eq_trans stat_eq_ent)
  hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> K'"
    by(metis Commutativity composition_sym stat_eq_ent)
  have "A\<^sub>P \<sharp>* M'" using `A\<^sub>P \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
    `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* yvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "zvec \<sharp>* M'" using `zvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
    `zvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* zvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "xvec \<sharp>* M'" using `xvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'`
    `A\<^sub>Q \<sharp>* xvec` `yvec \<sharp>* xvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  have "A\<^sub>Q \<sharp>* K'" using `A\<^sub>Q \<sharp>* P` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M\<lparr>N\<rparr> \<prec> P'`
    `A\<^sub>P \<sharp>* A\<^sub>Q` `zvec \<sharp>* A\<^sub>Q`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "A\<^sub>Q \<sharp>* A\<^sub>P" using `A\<^sub>P \<sharp>* A\<^sub>Q` by simp
  have "yvec \<sharp>* A\<^sub>P" using `A\<^sub>P \<sharp>* yvec` by simp
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M'\<lparr>N\<rparr> \<prec> P'"
    by(rule_tac comm2_aux) (fact|rule Frame_stat_imp_refl)+
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(rule_tac comm1_aux[where A\<^sub>P="A\<^sub>P"]) (fact|rule Frame_stat_imp_refl)+
  show ?case
    by(rule_tac Comm1[where M=M' and K=K']) fact+
next
  case(c_comm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q)
  then obtain zvec K' where  "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" "distinct zvec" "zvec \<sharp>* \<Psi>" "zvec \<sharp>* M" "zvec \<sharp>* P" "zvec \<sharp>* N" "zvec \<sharp>* Q" "zvec \<sharp>* A\<^sub>Q" "zvec \<sharp>* \<Psi>\<^sub>Q" "zvec \<sharp>* \<Psi>\<^sub>P" "A\<^sub>P \<sharp>* zvec" "zvec \<sharp>* K" "zvec \<sharp>* xvec" "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M"
    by(auto dest!: old_semantics_output_sound'[where C="(Q,A\<^sub>Q,\<Psi>\<^sub>Q,\<Psi>\<^sub>P,K,\<Psi>)"])
  from c_comm2 obtain yvec M' where  "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'" "distinct yvec" "yvec \<sharp>* \<Psi>" "yvec \<sharp>* M" "yvec \<sharp>* P" "yvec \<sharp>* N" "yvec \<sharp>* Q" "A\<^sub>Q \<sharp>* yvec" "yvec \<sharp>* \<Psi>\<^sub>Q" "yvec \<sharp>* \<Psi>\<^sub>P" "A\<^sub>P \<sharp>* yvec" "yvec \<sharp>* K" "yvec \<sharp>* zvec" "yvec \<sharp>* xvec" "yvec \<sharp>* K'" "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
    by(auto dest!: old_semantics_input_sound'[where C="(P,A\<^sub>P,\<Psi>\<^sub>Q,\<Psi>\<^sub>P,K,M,\<Psi>,zvec,K',xvec)"])
  hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M'" using `\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K` `(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> K' \<leftrightarrow> M`
    by (metis Assertion_stat_eq_sym Assertion_stat_imp_def Associativity associativity_sym chan_eq_sym chan_eq_trans stat_eq_ent)
  hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
    by(metis Commutativity composition_sym stat_eq_ent)
  have "A\<^sub>P \<sharp>* M'" using `A\<^sub>P \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
    `A\<^sub>P \<sharp>* A\<^sub>Q` `A\<^sub>P \<sharp>* yvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "zvec \<sharp>* M'" using `zvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
    `zvec \<sharp>* A\<^sub>Q` `yvec \<sharp>* zvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "xvec \<sharp>* M'" using `xvec \<sharp>* Q` `\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K\<lparr>N\<rparr> \<prec> Q'`
    `A\<^sub>Q \<sharp>* xvec` `yvec \<sharp>* xvec`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')  
  have "A\<^sub>Q \<sharp>* K'" using `A\<^sub>Q \<sharp>* P` `\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'`
    `A\<^sub>P \<sharp>* A\<^sub>Q` `zvec \<sharp>* A\<^sub>Q`
    by(auto dest!: trans_fresh_provenance simp add: frame_chain_fresh_chain'')
  have "A\<^sub>Q \<sharp>* A\<^sub>P" using `A\<^sub>P \<sharp>* A\<^sub>Q` by simp
  have "yvec \<sharp>* A\<^sub>P" using `A\<^sub>P \<sharp>* yvec` by simp
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> Some(\<langle>A\<^sub>P; zvec, K'\<rangle>) @ M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac comm1_aux) (fact|rule Frame_stat_imp_refl)+
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> Some(\<langle>A\<^sub>Q; yvec, M'\<rangle>) @ K'\<lparr>N\<rparr> \<prec> Q'"
    by(rule_tac comm2_aux[where A\<^sub>P="A\<^sub>P"]) (fact|rule Frame_stat_imp_refl)+
  show ?case
    by(rule_tac Comm2[where M=M' and K=K']) fact+
next
  case c_scope
  thus ?case
    by(auto dest: Scope)
next
  case c_bang
  thus ?case
    by(auto dest: semantics.Bang)
qed

lemma old_semantics_sound:
  assumes "\<Psi> \<rhd> P \<longmapsto>\<^sub>O Rs"  
  shows "\<exists> \<pi>. \<Psi> \<rhd> P \<longmapsto> \<pi> @ Rs"
  using assms
  by(nominal_induct rule: residual.strong_induct) (metis old_semantics_tau_sound old_semantics_output_sound old_semantics_input_sound residual_inject)+

end

end