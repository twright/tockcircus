section \<open> tock-Circus \<close>

theory tockcircus
imports tcircus_calc tcircus_timed_conj
begin recall_syntax

subsection \<open> Healthiness Conditions \<close>

text \<open> This is the same as Circus $Skip$, except that it includes an unstable intermediate state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], id\<^sub>s))"

lemma "\<U>(true, []) \<sqsubseteq> \<F>(true, [], id\<^sub>s) ;; \<U>(true, [])"
  by (trr_auto)

definition TC1 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC1(P) = Skip ;; P"

lemma Skip_self_unit: "Skip ;; Skip = Skip"
  by rdes_eq

lemma TC1_idem: "TC1(TC1(P)) = TC1(P)"
  by (simp add: RA1 Skip_self_unit TC1_def)

definition TC2 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC2(P) = P ;; Skip"

lemma TC2_idem: "TC2(TC2(P)) = TC2(P)"
  by (simp add: seqr_assoc Skip_self_unit TC2_def)

definition [upred_defs]: "TC = NRD \<circ> TC2 \<circ> TC1" 

lemma TC_implies_NRD [closure]: "P is TC \<Longrightarrow> P is NRD"
  by (metis (no_types, hide_lams) Healthy_def TC_def NRD_idem comp_apply)

lemma NRD_rdes [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "NRD(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (\<^bold>R(P \<turnstile> Q \<diamondop> R))"
  by (simp add: Healthy_if NRD_rdes_intro assms)

lemma TC1_rdes:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRR(Q)) \<diamondop> TRR(R))"
  using assms
  by (rdes_simp, simp add: TRR_def TRR1_def Healthy_if)

lemma TC1_TRR_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  by (subst TC1_rdes, simp_all add: closure assms wp Healthy_if)

lemma TC2_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile>(Q \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t)"
  using assms by (rdes_simp)

lemma TC_implies_TC1 [closure]: 
  assumes "P is TC"
  shows "P is TC1"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "TC1(TC(P)) = TC(P)"
    by (rdes_eq cls: a simps: TC_def)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TC_implies_TC2 [closure]: 
  assumes "P is TC"
  shows "P is TC2"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "TC2(TC(P)) = TC(P)"
    by (rdes_eq cls: a simps: TC_def)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TC_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R (
      P
    \<turnstile> (Q \<or> \<U>(true, []) \<or> R ;; \<U>(true, []))
    \<diamondop> R ;; II\<^sub>t
  )"
  by (simp add: TC_def rdes_def closure assms rpred wp disj_comm disj_assoc)

lemma TC_closed_seqr [closure]: 
  assumes "P is TC" "Q is TC"
  shows "P ;; Q is TC"
proof -
  have "P ;; Q is TC1"
    by (metis (no_types, hide_lams) Healthy_def RA1 TC1_def TC_implies_TC1 assms(1))
  moreover have "P ;; Q is TC2"
    by (metis (no_types, hide_lams) Healthy_def RA1 TC2_def TC_implies_TC2 assms(2))
  ultimately show ?thesis
    by (metis Healthy_comp NRD_seqr_closure TC_def TC_implies_NRD assms(1) assms(2))
qed

lemma NRD_Sup_closure [closure]:
  assumes "A \<subseteq> \<lbrakk>NRD\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "\<Sqinter> A is NRD"
proof -
  have "NRD (\<Sqinter> A) = (\<Sqinter> (NRD `A))"
    by (simp add: ContinuousD NRD_Continuous assms(2))
  also have "... = (\<Sqinter> A)"
    by (simp only: Healthy_carrier_image assms)
  finally show ?thesis by (simp add: Healthy_def)
qed

lemma intChoice_NRD_closed [closure]:
  assumes "P is NRD" "Q is NRD"
  shows "P \<sqinter> Q is NRD"
  using NRD_Sup_closure[of "{P, Q}"] by (simp add: assms)

lemma TC_closed_disj [closure]:
  assumes "P is TC" "Q is TC"
  shows "P \<sqinter> Q is TC"
proof -
  have "P is NRD" "Q is NRD"
    using assms TC_implies_NRD by blast+
  then have 1: "P \<sqinter> Q is NRD"
    by (simp add: intChoice_NRD_closed)
  have "P is TC1" "Q is TC1"
    using TC_implies_TC1 assms by blast+
  then have 2: "P \<sqinter> Q is TC1"
    by (simp add: Healthy_def TC1_def seqr_inf_distr)
  have "P is TC2" "Q is TC2"
    using TC_implies_TC2 assms by blast+
  then have 3: "P \<sqinter> Q is TC2"
    by (simp add: Healthy_def TC2_def seqr_inf_distr)
  from 1 2 3 show "P \<sqinter> Q is TC"
    by (simp add: Healthy_comp TC_def)
qed

lemma TC_inner_closures [closure]:
  assumes "P is TC"
  shows "pre\<^sub>R(P) is TRC" "peri\<^sub>R(P) is TRR" "post\<^sub>R(P) is TRF" "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])" "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
proof -
  have a: "P is NRD"
    using TC_implies_NRD assms by blast
  have b: "P = TC1(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC1 TC_implies_TC2 a assms)
  hence 1: "P = \<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRR (peri\<^sub>R P)) \<diamondop> TRR (post\<^sub>R P))"
    by (simp add: TC1_rdes TC2_rdes closure assms)
  hence 2: "II\<^sub>t wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
    by (metis TRR_implies_RR TRR_tc_skip a preR_NRD_RR preR_rdes wp_rea_RR_closed)
  thus [closure]: "pre\<^sub>R(P) is TRC"
    by (simp add: NRD_neg_pre_RC TRC_wp_intro a)
  have peri: "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (\<U>(true, []) \<or> TRR (peri\<^sub>R P)))"
    by (subst 1, simp add: rdes closure assms 2)
  also have "... is TRR"
    by (simp add: closure assms)
  finally show [closure]: "peri\<^sub>R(P) is TRR" .
  show "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])"
    by (metis peri rea_impl_disj utp_pred_laws.sup.cobounded1)
  have "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r TRR (post\<^sub>R P))"
    by (metis 1 2 Healthy_Idempotent TRR_implies_RR a postR_rdes preR_NRD_RR trel_theory.HCond_Idempotent)
  also have "... is TRR"
    by (simp add: closure assms)
  finally have [closure]: "post\<^sub>R(P) is TRR" .  
  have "P = TC2(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC2 a assms)
  hence 3: "P = \<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P ;; II\<^sub>t)"
    by (simp add: TC2_rdes closure assms)
  hence "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R P ;; II\<^sub>t)"
    by (metis TRR_implies_RR TRR_tc_skip \<open>post\<^sub>R P is TRR\<close> a postR_rdes preR_NRD_RR rrel_theory.Healthy_Sequence)
  also have "... is TRF"
    by (rule TRF_intro, simp_all add: closure assms unrest)  
  finally show "post\<^sub>R(P) is TRF" .
  have "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])))"
    by (subst 3, simp add: rdes closure)  
  thus "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
    by (metis (no_types, hide_lams) rea_impl_disj utp_pred_laws.sup.cobounded1 utp_pred_laws.sup_commute) 
qed

lemma TC_elim [RD_elim]: "P is TC \<Longrightarrow> Q (\<^bold>R (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)) \<Longrightarrow> Q P"
  by (simp add: NRD_elim TC_implies_NRD)

lemma TC_elim': "P is TC \<Longrightarrow> Q (\<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> \<U>(true, []) \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P)) \<Longrightarrow> Q P"
  by (simp add: NRD_elim TC_implies_NRD TC_inner_closures(4) TC_inner_closures(5) utp_pred_laws.sup_absorb1)
  
lemma TC_intro:
  assumes "P\<^sub>1 is TRC" "P\<^sub>2 is TRR" "P\<^sub>3 is TRF" "P\<^sub>2 \<sqsubseteq> \<U>(true, [])" "P\<^sub>2 \<sqsubseteq> P\<^sub>3 ;; \<U>(true, [])"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) is TC"
proof -
  have "TC1(\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (simp add: TC1_rdes assms closure wp Healthy_if utp_pred_laws.sup_absorb2)
  moreover have "TC2(\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (simp add: TC2_rdes assms closure wp rpred Healthy_if utp_pred_laws.sup_absorb1 utp_pred_laws.sup_absorb2)
  ultimately show ?thesis
    by (simp add: TC_def Healthy_intro NRD_rdes TRC_implies_RC TRF_implies_TRR TRR_implies_RR assms)
qed

subsection \<open> Basic Constructs \<close>

text \<open> The divergent action cannot terminate and exhibits only instability in the pericondition. \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> false)"

lemma Div_TC [closure]: "Div is TC"
  by (rule Healthy_intro, rdes_eq)

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[rdes_def]: "AssignsT \<sigma> = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], \<sigma>))" 

lemma AssignsT_TC [closure]: "\<langle>\<sigma>\<rangle>\<^sub>T is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> A timed deadlock does not terminate, but permits any period of time to pass, always remaining
  in a quiescent state where another $tock$ can occur. \<close>

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R(true\<^sub>r \<turnstile> \<T>({}, {0..}) ;; \<E>(true, [], {}, true) \<diamondop> false)"

lemma "true\<^sub>r is TRC"
  apply (simp add: closure)
  done

lemma "\<T>({}, {0..}) ;; \<E>(true, [], {}, true) is TRR"
  apply(rule Healthy_intro)
  apply(trr_auto)
  done

(*
lemma "(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<sqsubseteq> \<U>(true, [])"
  by (rel_simp)
*)

lemma "false is TRF"
  apply (simp add: closure)
  done

lemma Stop_TC [closure]: "Stop is TC"
  apply (rule Healthy_intro)
  apply (rdes_eq)
  done

text \<open> An untimed deadlock is stable, but does not accept any events. \<close>

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R(true\<^sub>r \<turnstile> \<E>(true, [], {}, false) \<diamondop> false)"

lemma Stop\<^sub>U_TC [closure]: "Stop\<^sub>U is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> SDF: Check the following definition against the tick-tock paper. It only allows prefixing
  of non-tock events for now. \<close>
text \<open> Thomas: this correspondence has now been proven \<close>

definition DoT :: "('e, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("do\<^sub>T'(_')") where
[rdes_def]: "DoT a =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({a}, {0..}) ;; (\<E>(true, [], {a}, true) \<or> \<U>(true, [Evt a]))
  \<diamondop> \<T>({a}, {0..}) ;; \<F>(true, [Evt a], id\<^sub>s))"


definition DoTock :: "('s, 'e) taction" ("dotock") where
[rdes_def]: "DoTock =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({}, {0..}) ;; (\<E>(true, [], {}, true) \<or> \<U>(true, []))
  \<diamondop> \<T>({}, {0..}) ;; \<F>(true, [], id\<^sub>s))"


lemma DoT_TC: "do\<^sub>T(e) is TC"
  by (rule Healthy_intro, rdes_eq)

definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R(true\<^sub>r 
    \<turnstile> ((\<T>({}, {0..<n}) ;; \<E>(true, [], {}, true)) 
       \<or> (\<T>({}, {n}) ;; \<U>(true, [])))
    \<diamondop> \<T>({}, {n}))"

utp_lift_notation Wait

lemma Wait_TC: "Wait n is TC"
  by (rule Healthy_intro, rdes_eq)

subsection \<open> Algebraic Laws \<close>

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Stop \<sqsubseteq> Div"
  by (rdes_refine)

utp_const lift_state_pre

lemma Wait_0: "Wait 0 = Skip"
  by (rdes_eq)

lemma Wait_Wait: "Wait m ;; Wait n = Wait(m + n)"
  apply (rdes_eq_split)
  apply (rel_auto)
  apply (simp_all add: rpred closure seqr_assoc[THEN sym])
  apply (rel_auto)
  done

text \<open> This is a pleasing result although @{const Wait} raises instability, this is swallowed up 
  by the sequential composition. \<close>

lemma Wait_Stop: "Wait m ;; Stop = Stop"
  by (rdes_eq_split, simp_all add: rpred closure seqr_assoc[THEN sym], rel_auto)

lemma "\<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T ;; do\<^sub>T(a) ;; \<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T = 
        \<^bold>R (\<^U>(R1 true) \<turnstile>
         (\<U>(true, []) \<or>
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {a}, true) \<or>
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], \<^U>([x \<mapsto>\<^sub>s &x + 1])))"
  by (rdes_simp, simp add: rpred seqr_assoc usubst)

lemma "Wait(m) ;; do\<^sub>T(a) ;; \<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T = 
      \<^bold>R (true\<^sub>r \<turnstile>
        (\<T>({}, {0..<m}) ;; \<E>(true, [], {}, true) \<or>
         \<T>({}, {m}) ;; \<U>(true, []) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {a}, true) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], [x \<mapsto>\<^sub>s &x + 1]))"
  apply (rdes_simp)
  apply (simp add: rpred seqr_assoc usubst)
  done

definition ExtChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('s, 'e) taction) \<Rightarrow> ('s, 'e) taction" where
[upred_defs]:
"ExtChoice I P =
  \<^bold>R(R1(\<And> i\<in>I \<bullet> pre\<^sub>R(P i)) \<comment> \<open> Require all preconditions \<close>

   \<turnstile> (idle(\<And> i\<in>I \<bullet> idle(peri\<^sub>R(P i))) \<comment> \<open> Allow all idle behaviours \<close>
      \<or> (\<Or> i\<in>I \<bullet> active(peri\<^sub>R(P i)) \<comment> \<open> Allow one active action to resolve the choice ...\<close>
         \<and> (\<And> j\<in>I \<bullet> time(peri\<^sub>R(P j))))) \<comment> \<open> ... whilst the others remain idle \<close>

   \<diamondop> ((\<Or> i\<in>I \<bullet> post\<^sub>R(P i) \<comment> \<open> The postcondition can terminate the external choice without an event ... \<close>
      \<and> (\<And> j\<in>I \<bullet> time(peri\<^sub>R(P j))))))" \<comment> \<open> ... whilst the others remain quiescent and idle \<close>

(*
definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<box>" 69) where
[upred_defs]: "P \<box> Q = ExtChoice {P, Q} id"
*)

(*
lemma
  assumes "P is TRF"
  shows "P = (time\<^sub>I(P) \<or> active\<^sub>I(P))"
  apply(subst (6 3 1) TRFconcretify)
   apply (simp add: assms)
  apply(rel_simp)
  apply(safe)
  oops
*)

definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<box>" 69) where
[upred_defs]:
"P \<box> Q =
  \<^bold>R((pre\<^sub>R(P) \<and> pre\<^sub>R(Q))
  \<turnstile> ((idle\<^sub>I(peri\<^sub>R(P)) \<squnion>\<^sub>t idle\<^sub>I(peri\<^sub>R(Q))) 
   \<or> (time\<^sub>I(peri\<^sub>R(P)) \<and> active\<^sub>I(peri\<^sub>R(Q)))
   \<or> (time\<^sub>I(peri\<^sub>R(Q)) \<and> active\<^sub>I(peri\<^sub>R(P))))
  \<diamondop> (idle\<^sub>E(peri\<^sub>R(P)) \<and> idle\<^sub>I(post\<^sub>R(Q))
   \<or> (idle\<^sub>E(peri\<^sub>R(Q)) \<and> idle\<^sub>I(post\<^sub>R(P)))
   \<or> (time\<^sub>I(peri\<^sub>R(P)) \<and> active\<^sub>I(post\<^sub>R(Q)))
   \<or> (time\<^sub>I(peri\<^sub>R(Q)) \<and> active\<^sub>I(post\<^sub>R(P)))))"

text \<open> Currently broken due to patience \<close>
(*
lemma ExtChoice_empty_peri:
  "peri\<^sub>R (ExtChoice {} P) = (\<T>({}, {0..}) ;; \<E>(true, [], {}, true))" (is "?l = ?r")
proof -
  have "?l = (idle(\<And> i\<in>{} \<bullet> idle(peri\<^sub>R(P i)))
      \<or> (\<Or> i\<in>{} \<bullet> active(peri\<^sub>R(P i))
         \<and> (\<And> j\<in>{} \<bullet> time(peri\<^sub>R(P j)))))"
    by (rel_simp)
  also have "\<dots> = U(idle(true) \<or> false)"
    by (simp add: rpred)
  also have "\<dots> = (idle(true))"
    by simp
  also have "\<dots> = ?r"
    by(rel_auto)
  finally show ?thesis .
qed
*)

(*
lemma ExtChoice_empty:
  "ExtChoice {} P = Stop"
  apply (simp add: ExtChoice_def Stop_def rpred)
  apply(rel_auto)
  done

lemma ExtChoice_single: 
  assumes "P i is TC" "peri\<^sub>R(P i) is TIP"
  shows "ExtChoice {i} P = P i"
proof -
  have 1: "time(peri\<^sub>R (P i)) \<sqsubseteq> post\<^sub>R (P i)"
    by (simp add: time_peri_in_post assms closure)
  show ?thesis
    by (rdes_simp cls: assms simps: ExtChoice_def 1 Healthy_if utp_pred_laws.inf_absorb1)
qed
*)

(*
lemma ExtChoice_rdes_def [rdes_def]:
  assumes "\<And> i. P\<^sub>1(i) is TRC" "\<And> i. P\<^sub>2(i) is TRR" "\<And> i. P\<^sub>3(i) is TRR"
  shows "ExtChoice I (\<lambda> i. \<^bold>R(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) = 
 \<^bold>R ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) 
    \<turnstile> (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j)))) \<diamondop>
        (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j))))"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty rpred Stop_def, rel_auto)
next
  case False
  have "((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>2 i) \<and> (\<And> j\<in>I \<bullet> time(RC2(P\<^sub>1 j) \<Rightarrow>\<^sub>r P\<^sub>2 j)))))
       = ((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j)))))"
      apply (trr_simp cls: assms False, safe)
      apply meson
      apply meson
      apply blast
      apply blast
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply blast+
      done
  hence 1: "((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>2 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>1 j \<Rightarrow>\<^sub>r P\<^sub>2 j)))))
          = ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j)))))"
    by (simp add: Healthy_if assms closure)
  have "((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>3 i) \<and> (\<And> j\<in>I \<bullet> time(RC2(P\<^sub>1 j) \<Rightarrow>\<^sub>r P\<^sub>2 j))))
        = ((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j))))"
    apply (trr_simp cls: assms False, safe)
    apply auto[1]
    apply (meson idleprefix_prefix order.trans)
    apply blast
    done
  hence 2: "((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>3 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>1 j \<Rightarrow>\<^sub>r P\<^sub>2 j))))
        =  ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I \<bullet> time(P\<^sub>2 j))))"
    by (simp add: Healthy_if assms closure)
  show ?thesis
    by (simp add: ExtChoice_def rdes assms closure False Healthy_if)
       (metis (no_types, lifting) "1" "2" rdes_tri_eq_intro rea_impl_mp)
qed
*)

(*
lemma ExtChoice_dual:
  assumes "P is TC" "Q is TC" "peri\<^sub>R P is TIP" "peri\<^sub>R Q is TIP"
  shows "ExtChoice {P, Q} id = P \<box> Q"
  apply (simp add: ExtChoice_def closure assms extChoice_def rpred usup_and uinf_or conj_disj_distr)
  apply (rule rdes_tri_eq_intro)
  apply (simp_all add: assms Healthy_if closure)
  apply(rule TRR_transfer_eq)
  apply (meson TC_inner_closures(1) TC_inner_closures(2) TRC_implies_TRR TRR_conj active_TRR assms(1) assms(2) idle_TRR tconj_TRR time_TRR trel_theory.disj_is_healthy)
  apply (meson TC_inner_closures(1) TC_inner_closures(2) TRC_implies_TRR TRR_conj active_TRR assms(1) assms(2) idle_TRR time_TRR trel_theory.disj_is_healthy)
  (* nitpick *)
  (*apply(rel_auto) *)
  (*
  apply (smt TC_inner_closures(2) TIP_time_active assms(1) assms(2) assms(3) assms(4) conj_comm utp_pred_laws.inf_left_commute utp_pred_laws.sup_commute)
  *)
  oops
*)

text \<open> Proving idempotence of binary external choice is complicated by the need to show that
  @{term "(time(peri\<^sub>R(P)) \<and> post\<^sub>R(P)) = post\<^sub>R(P)"} \<close>

lemma e: "ExtChoice {\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3), \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)} id =
       ExtChoice {True, False} (\<lambda> p. \<^bold>R((if p then P\<^sub>1 else Q\<^sub>1) \<turnstile> (if p then P\<^sub>2 else Q\<^sub>2) \<diamondop> (if p then P\<^sub>3 else Q\<^sub>3)))"
  by (simp add: ExtChoice_def)

(*
lemma extChoice_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is TRC" "P\<^sub>2 is TRR" "P\<^sub>3 is TRR" "Q\<^sub>1 is TRC" "Q\<^sub>2 is TRR" "Q\<^sub>3 is TRR"
  shows
  "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
       \<^bold>R((P\<^sub>1 \<and> Q\<^sub>1) 
        \<turnstile> ((idle(P\<^sub>2) \<squnion>\<^sub>t idle(Q\<^sub>2)) \<or> (time(P\<^sub>2) \<squnion>\<^sub>t active(Q\<^sub>2)) \<or> (time(Q\<^sub>2) \<squnion>\<^sub>t active(P\<^sub>2)))
        \<diamondop> ((time(P\<^sub>2) \<squnion>\<^sub>t Q\<^sub>3) \<or> (time(Q\<^sub>2) \<squnion>\<^sub>t P\<^sub>3)))"
proof -
  have 1: "((P\<^sub>1 \<and> Q\<^sub>1) \<squnion>\<^sub>t (idle(RC2 P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<squnion>\<^sub>t idle(RC2 Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> time(RC2 P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<squnion>\<^sub>t active(RC2 Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> time(RC2 Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<squnion>\<^sub>t active(RC2 P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2)))
       = ((P\<^sub>1 \<and> Q\<^sub>1) \<squnion>\<^sub>t (idle(P\<^sub>2) \<squnion>\<^sub>t idle(Q\<^sub>2) \<or> time(P\<^sub>2) \<squnion>\<^sub>t active(Q\<^sub>2) \<or> time(Q\<^sub>2) \<squnion>\<^sub>t active(P\<^sub>2)))"
    using idleprefix_prefix
    apply(rel_simp)
    apply(safe)
                  apply (smt (z3) order_refl)
    apply (smt (z3) order_class.order.eq_iff)
    apply (smt (z3) order_class.order.eq_iff)
    sledgehammer

    apply (trr_auto cls: assms)
  have 2: "((P\<^sub>1 \<and> Q\<^sub>1) \<and> (time(RC2 P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<and> (RC2 Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) \<or> time(RC2 Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<and> (RC2 P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3)))
           = ((P\<^sub>1 \<and> Q\<^sub>1) \<and> (time(P\<^sub>2) \<and> (Q\<^sub>3) \<or> time(Q\<^sub>2) \<and> (P\<^sub>3)))"
    using idleprefix_prefix by (trr_simp cls: assms, blast)

  from 1 2 show ?thesis
    by (simp add: extChoice_def rpred closure assms Healthy_if rdes, metis (no_types, lifting) rdes_tri_eq_intro)
qed
*)  

lemma [rpred]: "active(\<T>(X, A) ;; \<E>(s, [], E, p)) = false"
  by (rel_auto)

lemma [rpred]: "active\<^sub>I(\<T>(X, A) ;; \<E>(s, [], E, p)) = false"
  by (rel_auto)

lemma [rpred]: "(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<sqsubseteq> \<U>(true, [])"
  apply(trr_auto)
  done

(*
lemma [rpred]:
  assumes "(P \<and> $pat\<acute>) \<sqsubseteq> Q"
  shows "((P \<and> $pat\<acute>) \<squnion>\<^sub>t Q) = Q"
  using assms 
  unfolding upred_ref_iff
  apply rel_auto
  apply blast
  apply (smt (z3))
  by (smt (z3))
*)

lemma "Skip \<box> Stop = Skip"
  apply(rdes_eq_split cls: extChoice_def)
    apply(rel_auto)
   apply(trr_auto)
  apply(trr_auto)
  done
  
lemma "Wait m \<box> Wait m = Wait m"
  apply (rdes_eq_split cls: extChoice_def)
  apply rel_auto
   apply trr_auto
  apply trr_auto
  done

lemma "Wait m \<box> Wait n = Wait U(min m n)"
  apply(rdes_eq_split cls: extChoice_def)
  apply(rel_auto)
   apply(trr_auto)
  apply (meson le_eq_less_or_eq min.cobounded1)  
  apply (metis min.right_idem min.strict_order_iff)
     apply metis
  apply blast  
  apply meson

  apply(trr_simp)
  apply (smt (z3) le_eq_less_or_eq min.commute min_def tocks_idleprefix_fp)
  done

lemma [rpred]: "active\<^sub>I(\<E>(true, [], {}, false)) = false"
  apply(trr_auto)
  done

(*
lemma [rpred]: "time(\<E>(true, [], {}, false)) = \<E>(true, [], {}, false)"
  apply(simp add: tc_stable_def filter_time_def filter_time_urgent_def)
  apply(rel_auto)
  done
*)

lemma "\<U>(true, []) \<squnion>\<^sub>t \<E>(true, [], {}, false) = \<U>(true, [])"
  by (trr_auto)
  

lemma "\<U>(true, []) \<squnion>\<^sub>t \<E>(true, [], {}, false) = \<E>(true, [], {}, true)"
  apply(trr_simp)
  apply(meson)
  nitpick
  oops

(* Now changed to an actual true result *)
lemma "Skip \<box> Stop\<^sub>U =  Skip"
  apply (rdes_eq_split cls: extChoice_def)
  apply (rel_auto)
  apply(trr_auto)
  apply(trr_auto)
  done

lemma "Skip \<box> Div = Skip"
  apply(rdes_eq cls: extChoice_def)
  done

lemma "Wait(n + 1) \<box> Div = Div"
  apply(rdes_eq cls: extChoice_def)
  done

(* Was broken *)
lemma "Wait(n + 1) \<box> Stop\<^sub>U = Stop\<^sub>U"
  apply(rdes_eq_split cls: extChoice_def)
  apply(rel_auto)
  apply(trr_auto)
  apply (metis patience.distinct(1))
  apply(trr_auto)
  done

lemma "Stop \<box> do\<^sub>T(a) = do\<^sub>T(a)"
  apply(rdes_eq_split cls: extChoice_def)
  apply blast
   apply(trr_auto)
  apply (metis idleprefix_tocks tocks_idleprefix_fp)
  apply (trr_auto)
  apply (metis tocks_idleprefix_fp tocks_iff_idleprefix_fp)
  apply (metis idleprefix_tocks tocks_idleprefix_fp)
  done

(* TODO: pending sort hypothesis? *)
lemma "Wait m \<box> Skip = Skip"
  apply (rdes_eq_split cls: extChoice_def)
  apply (rel_auto)
   apply(trr_auto)
  apply(trr_simp)
  apply (metis list.size(3) neq0_conv tocks_Nil tocks_idleprefix_fp)
  done

lemma
  assumes "P is TRR"
  shows "(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t idle\<^sub>I(P) = idle\<^sub>I(P)"
  apply(trr_auto cls: assms)
  oops

lemma "Stop \<box> Stop\<^sub>U = Stop\<^sub>U"
  apply (rdes_eq_split cls: extChoice_def)
  apply(trr_auto)
  apply(trr_auto)
  apply (metis patience.distinct(1) tocks_Nil)
  apply(trr_auto)
  done


lemma "Stop \<box> Div = Div"
  apply (rdes_eq_split cls: extChoice_def)
  apply(trr_auto)
  apply(trr_auto)
  apply (trr_auto)
  done

lemma "Stop \<box> Wait(n) = Wait(n)"
  apply (rdes_eq_split cls: extChoice_def)
  apply(trr_auto)
  apply(trr_auto)
  apply (trr_auto)
  done

lemma "Stop \<box> Skip = Skip"
  apply (rdes_eq_split cls: extChoice_def)
  apply(trr_auto)
  apply(trr_auto)
  apply(trr_auto)
  done


(*
lemma "(Stop \<box> TC(true \<turnstile> ($pat\<acute>) \<diamondop> true\<^sub>r) = TC(true \<turnstile> ($pat\<acute>) \<diamondop> true\<^sub>r))"
  apply (rdes_eq_split cls: extChoice_def)
  apply(trr_auto)
  apply(trr_auto)
   apply (metis patience.distinct(1))
  done
*)

lemma extChoice_stop_unit:
  assumes "P is TC" "(pre\<^sub>R P \<Rightarrow> peri\<^sub>R P) is TRR6"
  shows "Stop \<box> P = P"
  apply (rdes_eq_split cls: assms extChoice_def)
    apply simp
  prefer 2
   apply(trr_auto cls: assms)
  apply (metis append_self_conv hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
  apply (metis append_self_conv hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
   apply(trr_auto cls: assms)
  apply meson
    apply (metis append_self_conv hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
      apply (metis)
  oops

(*
  prefer 2
  apply(trr_auto cls: assms)
  apply blast
  apply (metis append_Nil2 hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
  apply blast
  oops
*)
(*
  apply (rdes_eq_split cls: assms extChoice_def)
    apply(rel_auto)
   apply(rel_auto)
  apply blast
  apply (smt (z3) append_self_conv hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
*)
(*
         apply (metis append_Nil2 hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)
*)

lemma extChoice_commute:
  assumes "P is TC" "Q is TC"
  shows "P \<box> Q = Q \<box> P"
  apply(rdes_eq_split cls: assms extChoice_def)
  apply(simp_all add: conj_comm conj_assoc tconj_comm disj_comm utp_pred_laws.sup_left_commute)
  done

lemma TRC_conj [closure]: "\<lbrakk> P is TRC; Q is TRC \<rbrakk> \<Longrightarrow> (P \<and> Q) is TRC"
  by (simp add: TRC_implies_RC TRC_wp_intro TRR_wp_unit conj_RC_closed wp_rea_conj)

lemma TRF_conj [closure]: "\<lbrakk> P is TRF; Q is TRF \<rbrakk> \<Longrightarrow> (P \<and> Q) is TRF"
  by (simp add: TRF_implies_TRR TRF_intro TRF_unrests(1) TRF_unrests(2) TRR_conj unrest_conj)

(*
definition R1p where
R1p_def [upred_defs]: "R1p (P) = (P \<squnion>\<^sub>t (($tr \<le>\<^sub>u $tr\<acute>) \<and> $pat\<acute>))"

utp_const R1p

lemma "R1 P = R1p P"
  apply(rel_auto)
  apply blast
  oops
*)

(* The definition of R1 is still valid (phew!) *)

lemma "(\<not>\<^sub>r (\<not>\<^sub>r (P \<squnion> Q)) ;; true\<^sub>r) = ((\<not>\<^sub>r ((\<not>\<^sub>r P) \<squnion> (\<not>\<^sub>r Q))) ;; true\<^sub>r)"
  apply (rel_auto)
  oops

lemma "((P \<squnion>\<^sub>t Q) ;; true\<^sub>r) = ((P ;; true\<^sub>r) \<squnion>\<^sub>t (Q ;; true\<^sub>r))"
  apply(rel_auto)
  apply blast+
  oops

lemma RC_pat: "RC(P) = (\<exists> $pat\<acute> \<bullet> RC(P))"
  apply(rel_auto)
  done

lemma conj_RC1_closed [closure]:
  "\<lbrakk> P is RC1; Q is RC1 \<rbrakk> \<Longrightarrow> P \<and> Q is RC1"
  by (simp add: Healthy_def RC1_conj)

lemma conj_RC_closed [closure]:
  assumes "P is RC" "Q is RC"
  shows "(P \<and> Q) is RC"
  by (metis Healthy_def RC_R2_def RC_implies_RR assms comp_apply conj_RC1_closed conj_RR)

(*
lemma "RR(P \<and> Q) = (RR(P) \<and> RR(Q))"
p

proof - 
  have "(RR(P \<and> Q)) = (\<exists> {$ok,$ok\<acute>,$wait,$wait\<acute>} \<bullet> R2(P \<and> Q))"
    by (simp add: RR_def)
  also have "\<dots> = (\<exists> {$ok,$ok\<acute>,$wait,$wait\<acute>} \<bullet> R2(P) \<and> R2(Q))"
    by (simp add: R2_conj)
  also have "\<dots> = ((\<exists> {$ok,$ok\<acute>,$wait,$wait\<acute>} \<bullet> R2(P)) \<and> (\<exists> {$ok,$ok\<acute>,$wait,$wait\<acute>} \<bullet> R2(Q)))"
    apply(rel_auto)
    oops
qed

lemma "RC(P \<and> Q) = (RC(P) \<and> RC(Q))"
proof - 
  have 1: "RC(P) is RC" "RC(P) is RC"
    by (metis (no_types, lifting) Healthy_Idempotent Healthy_def RC1_RR_closed RC1_idem RC_R2_def RR_Idempotent comp_apply)+
  have "RC(P) \<and> RC(Q) is RC"
    by (metis (no_types, lifting) Healthy_Idempotent Healthy_def RC1_RR_closed RC1_conj RC1_idem RC_R2_def RR_Idempotent comp_apply conj_RR)
qed

proof - 
  have "RC (P \<and> Q) = RC2(RC1(RR(P \<and> Q)))"
    by (metis (no_types, hide_lams) Healthy_def RC1_RR_closed RC1_idem RC_def RC_prefix_closed RR_idem comp_apply)
  also have "\<dots> = RC2(RC1(RR P \<and> RR Q))"
    oopsqed

*)

lemma RC_tconj [rpred]: "RC(P \<squnion>\<^sub>t Q) = (RC(P) \<squnion>\<^sub>t RC(Q))"
  oops

lemma RC_tconj [closure]:
  assumes "P is RC" "Q is RC"
  shows "P \<squnion>\<^sub>t Q is RC"
proof -
  have "(P \<squnion>\<^sub>t Q) = (P \<and> Q)"
    using assms
    by (metis Healthy_def' RC_pat out_var_uvar pat_vwb_lens tconj_insistant unrest_as_exists)
  thus ?thesis
    by (simp add: assms utp_rea_cond.conj_RC_closed)
qed

lemma TRC_tconj [closure]: "\<lbrakk> P is TRC; Q is TRC \<rbrakk> \<Longrightarrow> (P \<squnion>\<^sub>t Q) is TRC"
  by (metis (no_types, lifting) Healthy_if RC_pat TRC_conj TRC_implies_RC out_var_uvar pat_vwb_lens tconj_insistant unrest_as_exists)

lemma uns_refine: "P \<sqsubseteq> \<U>(true, []) \<Longrightarrow> idle\<^sub>I(P) \<sqsubseteq> \<U>(true, [])"
  by (rel_auto)

lemma timeI_TRF:
  assumes "P is TRR"
  shows "time\<^sub>I(P) is TRF"
proof -
  have 1: "time(P) is TRR"
    by (simp add: assms time_TRR)
  have 2: "time\<^sub>I(P) is TRR3"
    apply(subst (2) TRRconcretify)
    apply(simp add: assms)
    apply(rel_auto)
    done
  from 1 2 show ?thesis
    using TRF_time_insistant assms by blast
qed

lemma timeI_unrests:
  shows "$ref\<acute> \<sharp> time\<^sub>I(P)" "$pat\<acute> \<sharp> time\<^sub>I(P)"
  by (rel_auto+)

(*
lemma extChoice_closure [closure]:
  assumes "P is TC" "Q is TC"
  shows "P \<box> Q is TC"
  apply (rdes_simp cls: assms extChoice_def)
  apply (rule TC_intro)
      apply (simp_all add: closure assms)
    apply(rule TRF_intro)
  apply (meson TC_inner_closures(1) TC_inner_closures(2) TC_inner_closures(3) TRC_implies_TRR TRF_implies_TRR TRR_closed_impl TRR_conj assms(1) assms(2) time_urgent_TRR trel_theory.disj_is_healthy)
  apply (metis (no_types, lifting) NRD_is_RD RD_healths(2) RD_reactive_tri_design TC_implies_NRD TC_inner_closures(1) TC_inner_closures(2) TC_inner_closures(3) TRC_implies_TRR TRF_conj_closure TRF_time_insistant TRF_unrests(1) TRR_closed_impl TRR_implies_RR assms(1) assms(2) postR_RR postR_rdes tfin_theory.disj_is_healthy)
  apply (metis (no_types, lifting) NRD_is_RD RD_healths(2) RD_reactive_tri_design TC_implies_NRD TC_inner_closures(1) TC_inner_closures(2) TC_inner_closures(3) TRC_implies_TRR TRF_conj_closure TRF_time_insistant TRF_unrests(2) TRR_closed_impl TRR_implies_RR assms(1) assms(2) postR_RR postR_rdes tfin_theory.disj_is_healthy)
   apply(trr_simp cls: assms)
  oops
*)
  (*
  sledgehammer
  apply(rel_simp)
  *)
  (*
  sledgehammer
   apply (simp add: TC_inner_closures(4) assms(1) assms(2) uns_refine utp_pred_laws.le_supI1)
  oops *)

(*
lemma
  assumes "P is TRC" "Q is TRF"
  shows "(P \<Rightarrow>\<^sub>r Q) is TRF"
proof - 
  have "(P \<Rightarrow>\<^sub>r Q) is TRR"
    by (simp add: TRC_implies_TRR TRF_implies_TRR TRR_closed_impl assms)
  have ""
qed
*)

(*
lemma
  shows "\<U>(true, []) is Hpat"
  apply(rel_auto)
  done


lemma
  assumes "R is Hpat"
  shows "((P \<squnion>\<^sub>t Q) \<sqinter> R) = ((P \<sqinter> R) \<squnion>\<^sub>t (Q \<sqinter> R))"
proof -
  have 1: "R = ($pat\<acute> \<and> R)"
    by (metis Healthy_if Hpat_def assms conj_comm)

  show ?thesis
    apply(subst (1 2 3) 1)
    apply(simp add: tconj_alt_def)
    apply(rel_auto)
    oops
*)

lemma extChoice_assoc:
  assumes "P is TC" "Q is TC" "R is TC"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
  apply(rdes_eq_split cls: assms extChoice_def)
    apply simp
  oops

lemma
  assumes "R is Hinsist"
  shows "((P \<squnion>\<^sub>t Q) \<sqinter> R) = ((P \<sqinter> R) \<squnion>\<^sub>t (Q \<sqinter> R))"
proof -
  have 1: "R = (\<exists> $pat\<acute> \<bullet> R)"
    by (metis Healthy_if Hinsist_def assms)

  show ?thesis
    apply(subst (1 2 3) 1)
    apply(rel_auto)
    apply blast+
    done
qed

lemma trr_uns_distrib:
  assumes "P is TRR" "Q is TRR"
  shows "((P \<squnion>\<^sub>t Q) \<sqinter> \<U>(true, [])) = ((P \<sqinter> \<U>(true, [])) \<squnion>\<^sub>t (Q \<sqinter> \<U>(true, [])))"
  sorry
(*
  apply(trr_auto cls: assms)
  apply blast+
  done
*)

lemma
  assumes "P is TRR" "Q is TRR" "R is TRR"
  shows "((P \<squnion>\<^sub>t Q) \<sqinter> R) = ((P \<sqinter> R) \<squnion>\<^sub>t (Q \<sqinter> R))"
  apply(subst (12 10 8 6 5 3 1) TRRconcretify)
  apply(simp_all add: assms)
  apply(simp add: tconj_alt_def)
  apply(rel_auto)
  oops

lemma uns_tconj:
  assumes  "P is TRR" "Q is TRR" "P \<sqsubseteq> \<U>(true, [])" "Q \<sqsubseteq> \<U>(true, [])"
  shows "P \<squnion>\<^sub>t Q \<sqsubseteq> \<U>(true, [])"
proof -
  have 1: "P = (P \<sqinter> \<U>(true, []))" "Q = (Q \<sqinter> \<U>(true, []))"
    by (simp_all add: assms(3) assms(4) semilattice_sup_class.sup_absorb1)
    (* by (simp_all add: assms utp_pred_laws.sup.absorb1) *)

  have "P \<squnion>\<^sub>t Q = (P \<sqinter> \<U>(true, [])) \<squnion>\<^sub>t (Q \<sqinter> \<U>(true, []))"
    using 1 by presburger
  also have "\<dots> = ((P \<squnion>\<^sub>t Q) \<sqinter> \<U>(true, []))"
    by (simp add: assms(1) assms(2) trr_uns_distrib)
  finally show "P \<squnion>\<^sub>t Q \<sqsubseteq> \<U>(true, [])"
    by (meson semilattice_sup_class.sup.order_iff)
qed

lemma TIP_time_active [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active\<^sub>I(P) \<and> time\<^sub>I(P)) = active\<^sub>I(P)"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_blast)
  done

lemma
  assumes "P is TRR"
  shows "P \<sqsubseteq> active\<^sub>I(P)" "P \<sqsubseteq> idle\<^sub>I(P)"
  apply (metis TRR_idle_or_active_insistant assms utp_pred_laws.sup.cobounded2)
  by (metis TRR_idle_or_active_insistant assms utp_pred_laws.sup_ge1)

lemma
  assumes "P is TRR" "P is TIP"
  shows "time\<^sub>I(P) \<sqsubseteq> P"
  by (meson TIP_time_refine assms(1) assms(2))


lemma
  assumes "P is TRR" "P is TIP"
  shows "time\<^sub>I(P) \<sqsubseteq> idle\<^sub>I(P)"
  by (metis TIP_time_refine TRR_idle_or_active_insistant assms(1) assms(2) disj_upred_def semilattice_sup_class.le_sup_iff)

lemma TIP_time_active_red [closure]:
  assumes "P is TRR" "P is TIP"
  shows "time\<^sub>I(P) \<sqsubseteq> active\<^sub>I(P)"
  by (simp add: TIP_time_active_urgent_conj assms(1) assms(2) utp_pred_laws.inf.absorb_iff1)

lemma TIP_time_idle [closure]:
  assumes "P is TRR" "P is TIP"
  shows "P = (idle\<^sub>I(P) \<or> time\<^sub>I(P))"
  oops

lemma extChoice_closure [closure]:
  assumes "P is TC" "Q is TC"
  shows "P \<box> Q is TC"
proof (rdes_simp cls: assms extChoice_def)
  have 1: "pre\<^sub>R P is TRC" "peri\<^sub>R P is TRR" "post\<^sub>R P is TRF"
          "pre\<^sub>R Q is TRC" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    using assms TC_inner_closures by auto

  have 10: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) = TIP(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
           "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) = TIP(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)"
    sorry

  have "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> \<U>(true, [])"
    by (metis (no_types, lifting) TC_inner_closures(4) assms(1) disj_upred_def rea_impl_def semilattice_sup_class.sup.order_iff utp_pred_laws.sup_assoc)
  then have 2: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> \<U>(true, [])"
    by (meson uns_refine)

  have "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (metis TC_inner_closures(4) assms(2) disj_upred_def rea_impl_disj semilattice_sup_class.le_iff_sup)
  then have 3: "idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (meson uns_refine)

  have 4: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (simp add: "1"(1) "1"(2) "1"(4) "1"(5) "2" "3" TRC_implies_TRR TRR_closed_impl idle_TRR_insistant uns_tconj)

  have "(time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q))
    \<sqsubseteq>  (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)
      \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
     ;; \<U>(true, [])"
    apply(trr_auto cls: 1)
    sorry

  have 5: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) = (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<or> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))"
    by (metis "1"(1) "1"(2) TRC_implies_TRR TRR_closed_impl TRR_idle_or_active_insistant disj_comm)

  have 6: "((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)) ;; \<U>(true, []))
      = (((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)) ;; \<U>(true, []))
       \<or> ((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)) ;; \<U>(true, [])))"
    by (metis "1"(4) "1"(5) TRC_implies_TRR TRR_closed_impl TRR_idle_or_active_insistant conj_disj_distr seqr_or_distl)

  have 7: "(time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q))
         \<sqsubseteq> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)) ;; \<U>(true, [])"
    apply(trr_auto cls: 1)
    sorry

  have "(idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q))
      \<sqsubseteq> ((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)) ;; \<U>(true, []))"
    apply(trr_auto cls: 1)
    sorry

  have "pre\<^sub>R P \<and> pre\<^sub>R Q is TRC"
    by (simp add: "1"(1) "1"(4) TRC_conj)
  moreover have 3: "(idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R ;P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)) is TRR"
    by (meson "1"(1) "1"(2) "1"(4) "1"(5) TRC_implies_TRR TRR_closed_impl TRR_conj active_TRR_insistant idle_TRR_insistant tconj_TRR time_TRR time_urgent_TRR trel_theory.disj_is_healthy)
    (* by (meson "1"(1) "1"(2) "1"(4) "1"(5) TRC_implies_TRR TRR_closed_impl active_TRR idle_TRR tconj_TRR time_TRR trel_theory.disj_is_healthy) *)
  moreover have "(time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) is TRF"
    by (metis (no_types, lifting) "1"(1) "1"(2) "1"(3) "1"(4) "1"(5) "1"(6) NRD_is_RD
        RD_reactive_tri_design TC_implies_NRD TRC_implies_TRR TRF_conj TRF_implies_TRR
        TRF_time_insistant TRR_closed_impl TRR_implies_RR assms(1) assms(2) postR_rdes
        tfin_theory.disj_is_healthy)
  moreover have "(idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
               \<sqsubseteq> \<U>(true, [])"
    by (meson "4" utp_pred_laws.sup.coboundedI1)
  moreover have "(idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
               \<sqsubseteq> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)
               \<or>  time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
              ;; \<U>(true, [])"
    apply(subst (4 3 2 1) 10(1))
    apply(subst (4 3 2 1) 10(2))
    apply(trr_simp cls: 1)
    apply(safe)
    sorry (* TODO: How do we prove this? *)
  ultimately show "\<^bold>R ((pre\<^sub>R P \<and> pre\<^sub>R Q)
                   \<turnstile> (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                   \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                   \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
                   \<diamondop> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)
                   \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)))
                   is TC"
    by (meson "1"(1) "1"(2) "1"(4) "1"(5) TC_intro TRC_implies_TRR TRR_closed_impl TRR_conj active_TRR_insistant idle_TRR_insistant tconj_TRR time_urgent_TRR trel_theory.disj_is_healthy)
qed

(*
proof -
  have 1: "pre\<^sub>R P is TRC" "peri\<^sub>R P is TRR" "post\<^sub>R P is TRF"
          "pre\<^sub>R Q is TRC" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    using assms TC_inner_closures by auto
  have " (idle(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<or>
     time(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<or> time(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)) is TRR"
    by (simp add: closure 1 tconj_TRR)
  have 2: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) is TRR"
          "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) is TRR"
    by (simp_all add: 1 TRC_implies_TRR TRR_closed_impl)

  have "time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) is TRF"
       "time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) is TRF"
    by (simp_all add: "2" TRF_time_insistant)

  have "time(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t (pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) is TRF"
    apply(simp add: closure)
  have "idle(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) is TRR" (* \<squnion>\<^sub>t idle(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) is TRF" *)
       "idle(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) is TRR"
    by (simp add: closure 1)+
  then have "idle(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) is TRR"
    using tconj_TRR by blast
qed
*)

lemma extChoice_idem:
  assumes "P is TC" "peri\<^sub>R(P) is TIP"
  shows "P \<box> P = P"
proof -
  have 1: "time\<^sub>I(peri\<^sub>R P) \<sqsubseteq> post\<^sub>R P"
    by (rule time_peri_in_post_insistant, simp_all add: closure assms)
  show ?thesis
    apply (rdes_simp cls: assms extChoice_def)
    apply (rdes_eq_split cls: assms)
      apply (simp add: assms rpred closure)
     apply (simp_all add: assms utp_pred_laws.inf_commute closure rpred)
     prefer 2
    oops

(*
    apply (simp add: "1" conj_comm utp_pred_laws.inf.absorb1)
*)
  
lemma "Stop \<box> \<langle>\<sigma>\<rangle>\<^sub>T = \<langle>\<sigma>\<rangle>\<^sub>T"
  oops
(*
   by (simp add: AssignsT_TC extChoice_unit)
*)

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

section \<open> Timed interrupt \<close>

(*
definition untimed_interrupt :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<triangle>\<^sub>U" 69) where
[upred_defs]:
"P \<triangle>\<^sub>U Q = 
  \<^bold>R((pre\<^sub>R(P) \<and> (post\<^sub>R(P) wp\<^sub>r pre\<^sub>R(Q)))
  \<turnstile> (post\<^sub>R P \<and> peri\<^sub>R Q \<or> (post\<^sub>R P ;; post\<^sub>R Q))
  \<diamondop> (post\<^sub>R P \<and> peri\<^sub>R Q \<or> (post\<^sub>R P ;; post\<^sub>R Q)))"
*)

(*  \<^bold>R((pre\<^sub>R(P) \<and> (post\<^sub>R(P) wp\<^sub>r pre\<^sub>R(Q)))
  \<turnstile> ( ((idle(peri\<^sub>R P) \<and> idle(peri\<^sub>R Q)) ;; active(peri\<^sub>R P))
    \<or> ((idle(peri\<^sub>R P) \<and> idle(peri\<^sub>R Q)) ;; active(peri\<^sub>R Q)))
  \<diamondop> ( ((idle(peri\<^sub>R P) \<and> idle(peri\<^sub>R Q)) ;; active(post\<^sub>R P)))
    \<or> ((idle(peri\<^sub>R P) \<and> idle(peri\<^sub>R Q)) ;; active(post\<^sub>R Q))) *)

(*
lemma
  "(post\<^sub>R P \<and> TC(peri\<^sub>R Q \<lbrakk>idleprefix\<^sub>u(&tt)/&tt\<rbrakk>)) = (post\<^sub>R P \<and> time(peri\<^sub>R Q))"
  apply(rel_auto)
proof -
  have "post\<^sub>R Q is R2"
    using assms
    by (simp add: RR_implies_R2 TC_inner_closures(3) TRF_implies_TRR TRR_implies_RR)
  thus ?thesis
    apply(rel_auto)
    sledgehammer
qed
*)

definition has_trace ("has'(_,_')") where
"has_trace t P = U(\<exists> $st\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P\<lbrakk>t/&tt\<rbrakk>)"

definition has_trace_stateful ("hass'(_,_')") where
"has_trace_stateful t P = U(\<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P\<lbrakk>t/&tt\<rbrakk>)"

definition has_trace_ref ("hasr'(_,_,_')") where
"has_trace_ref t X P = U(\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P\<lbrakk>t,X/&tt,$ref\<acute>\<rbrakk>)"


definition has_trace_ref_pat ("hasrp'(_,_,_,_')") where
"has_trace_ref_pat t X p P = U(\<exists> $st\<acute> \<bullet> P\<lbrakk>t,X,p/&tt,$ref\<acute>,$pat\<acute>\<rbrakk>)"


definition has_trace_ref_pat_stateful ("hassrp'(_,_,_,_')") where
"has_trace_ref_pat_stateful t X p P = U(P\<lbrakk>t,X,p/&tt,$ref\<acute>,$pat\<acute>\<rbrakk>)"

definition tockfiltered :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("tockfiltered\<^sub>u'(_')") where
"tockfiltered P =  U(\<exists> $st\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> P\<lbrakk>filtertocks(&tt)/&tt\<rbrakk>)"

(* :: "'\<theta> reftrace \<Rightarrow> ('s, 'e) taction" *)
fun startswithrefusal ("startswithrefusal\<^sub>u'(_')") where
"startswithrefusal [] = False"|
"startswithrefusal (Evt e # t) = False"|
"startswithrefusal (Tock X # t) = True"


utp_const has_trace has_trace_ref has_trace_ref_pat  has_trace_stateful has_trace_ref_pat_stateful tockfiltered startswithrefusal 
         (*  *)

(*
(peri\<^sub>R P \<or> post\<^sub>R P)
      \<and> (\<exists> $st \<bullet> (peri\<^sub>R Q \<or> post\<^sub>R Q)\<lbrakk>filtertocks\<^sub>u(&tt)/&tt\<rbrakk>)

U(\<exists> X Y Z p q.
           hasrp(&tt, \<guillemotleft>rfset X\<guillemotright>, \<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
         \<and> hasrp(filtertocks\<^sub>u(&tt), \<guillemotleft>rfset Y\<guillemotright>, \<guillemotleft>q\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
         \<and> (\<guillemotleft>Z \<subseteq> X \<union> Y\<guillemotright>)
         \<and> ($ref\<acute> = \<guillemotleft>rfset Z\<guillemotright>)
         \<and> (p \<and> q \<Rightarrow> $pat\<acute>)
      )

(pre\<^sub>R(P) \<and> (post\<^sub>R(P) wp\<^sub>r pre\<^sub>R(Q)))
*)

definition interrupt :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<triangle>" 69) where
[upred_defs]:
"P \<triangle> Q =
\<^bold>R(true\<^sub>r
  \<turnstile> (
      U(\<exists> X Y Z p q.
           hasrp(&tt, \<guillemotleft>rfset X\<guillemotright>, \<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
         \<and> hassrp(filtertocks\<^sub>u(&tt), \<guillemotleft>rfset Y\<guillemotright>, \<guillemotleft>q\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
         \<and> (\<guillemotleft>Z \<subseteq> X \<union> Y\<guillemotright>)
         \<and> ($ref\<acute> = \<guillemotleft>rfset Z\<guillemotright>)
         \<and> (p \<and> q \<Rightarrow> $pat\<acute>)
      )  
      \<or> U(\<exists> p q\<^sub>1 q\<^sub>2 . 
           (&tt = \<guillemotleft>p @ q\<^sub>2\<guillemotright>)
         \<and> (q\<^sub>1 = filtertocks\<^sub>u(&tt))
         \<and> has(\<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
         \<and> hass(\<guillemotleft>q\<^sub>1 @ q\<^sub>2\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
         \<and> \<not>\<^sub>r \<guillemotleft>startswithrefusal\<^sub>u(q\<^sub>2)\<guillemotright>
         \<and> \<guillemotleft>q\<^sub>2\<guillemotright> = [] \<Rightarrow> ($pat\<acute> \<and> $ref\<acute> = rfnil) 
         )
  ) \<diamondop> (
      (post\<^sub>R P \<and> tockfiltered(peri\<^sub>R Q \<or> post\<^sub>R Q) )
    \<or> U(\<exists> p q\<^sub>1 q\<^sub>2 . 
         (&tt = \<guillemotleft>p @ q\<^sub>2\<guillemotright>)
       \<and> (q\<^sub>1 = filtertocks\<^sub>u(&tt))
       \<and> has(\<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
       \<and> hass(\<guillemotleft>q\<^sub>1 @ q\<^sub>2\<guillemotright>, post\<^sub>R Q)
       \<and> \<not>\<^sub>r \<guillemotleft>startswithrefusal\<^sub>u(q\<^sub>2)\<guillemotright>
       )))"

fun intersectRefusalTrace ("intersectRefusalTrace\<^sub>u'(_,_')") where
"intersectRefusalTrace X [] = []"|
"intersectRefusalTrace X (Evt e # t) = Evt e # intersectRefusalTrace X t"|
"intersectRefusalTrace X (Tock Y # t) = Tock (X \<inter> Y) # intersectRefusalTrace X t"


fun ointersectRefusalTrace where
"ointersectRefusalTrace X [] = []"|
"ointersectRefusalTrace X (oevt e # t) = oevt e # ointersectRefusalTrace X t"|
"ointersectRefusalTrace X (otock # t) = otock # ointersectRefusalTrace X t"|
"ointersectRefusalTrace X (otick # t) = otick # ointersectRefusalTrace X t"|
"ointersectRefusalTrace X (oref Y # t) = oref (X \<inter> Y) # ointersectRefusalTrace X t"

fun containsRefusal ("containsRefusal\<^sub>u'(_')") where
"containsRefusal [] = False"|
"containsRefusal (Evt e # t) = containsRefusal t"|
"containsRefusal (Tock Y # t) = True"


fun ocontainsRefusal where
"ocontainsRefusal [] = False"|
"ocontainsRefusal (oevt e # t) = ocontainsRefusal t"|
"ocontainsRefusal (otock # t) = ocontainsRefusal t"|
"ocontainsRefusal (otick # t) = ocontainsRefusal t"|
"ocontainsRefusal (oref Y # t) = True"

(*
definition untimedinterrupt :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<triangle>\<^sub>U" 68) where
[upred_defs]:
"(P \<triangle>\<^sub>U Q) =
\<^bold>R(true\<^sub>r
  \<turnstile> (
      U(\<exists> X Y Z p q.
           hasrp(&tt, \<guillemotleft>rfset X\<guillemotright>, \<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
         \<and> hassrp(filtertocks\<^sub>u(&tt), \<guillemotleft>rfset Y\<guillemotright>, \<guillemotleft>q\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
         \<and> (\<guillemotleft>Z \<subseteq> X \<union> Y\<guillemotright>)
         \<and> ($ref\<acute> = \<guillemotleft>rfset Z\<guillemotright>)
         \<and> (p \<and> q \<Rightarrow> $pat\<acute>)
      )  
      \<or> U(\<exists> p q\<^sub>1 q\<^sub>2 . 
           (&tt = \<guillemotleft>p @ q\<^sub>2\<guillemotright>)
         \<and> (q\<^sub>1 = filtertocks\<^sub>u(&tt))
         \<and> has(\<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
         \<and> hass(\<guillemotleft>q\<^sub>1 @ q\<^sub>2\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
         \<and> \<not>\<^sub>r \<guillemotleft>startswithrefusal\<^sub>u(q\<^sub>2)\<guillemotright>
         \<and> \<guillemotleft>q\<^sub>2\<guillemotright> = [] \<Rightarrow> ($pat\<acute> \<and> $ref\<acute> = rfnil) 
         )
  ) \<diamondop> (
      U(\<exists> p X.
            hass(\<guillemotleft>p\<guillemotright>, post\<^sub>R P)
          \<and> \<guillemotleft>containsRefusal\<^sub>u(p)\<guillemotright>
          \<and> hasr([], \<guillemotleft>rfset X\<guillemotright>, peri\<^sub>R Q \<or> post\<^sub>R Q)
          \<and> &tt = \<guillemotleft>intersectRefusalTrace X p\<guillemotright> )
    \<or> U(post\<^sub>R P \<and> \<not>\<^sub>r\<guillemotleft>containsRefusal\<^sub>u(&tt)\<guillemotright>)
    \<or> U(\<exists> p q X Y .
        hasr(p, \<guillemotleft>rfset X\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
      \<or> hassr(p, post\<^sub>R Q))
    \<or> U(\<exists> p q\<^sub>1 q\<^sub>2 . 
         (&tt = \<guillemotleft>p @ q\<^sub>2\<guillemotright>)
       \<and> (q\<^sub>1 = filtertocks\<^sub>u(&tt))
       \<and> has(\<guillemotleft>p\<guillemotright>, peri\<^sub>R P \<or> post\<^sub>R P)
       \<and> hass(\<guillemotleft>q\<^sub>1 @ q\<^sub>2\<guillemotright>, post\<^sub>R Q)
       \<and> \<not>\<^sub>r \<guillemotleft>startswithrefusal\<^sub>u(q\<^sub>2)\<guillemotright>
       )))"
*)

section \<open> Hiding \<close>



end