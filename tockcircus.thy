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

lemma JC_wait:
  "(( Q \<diamondop> R) ;; J6) = ((Q;;J6) \<diamondop> (R;;J6))"
  by (rel_auto)

lemma
  "((true \<turnstile> Q) ;; (true \<turnstile> J6)) = (true \<turnstile> (Q;;J6))"
  apply(rel_auto)
  apply blast+
  done

lemma
  "((R1(P) \<turnstile> Q) ;; (true\<^sub>r \<turnstile> J6)) = (R1(P) \<turnstile> (Q;;J6))"
  apply(rel_auto)
  oops

lemma TRR6_des: "(TRC(P) \<turnstile> TRR6(Q)) is TRR6"
  apply(subst TRR6_alt_def)
  apply(rel_auto)
  by meson

lemma TRR6_des_TRC: "TRR6(TRC(P) \<turnstile> Q) = (TRC(P) \<turnstile> TRR6 Q)"
proof -
  have "(TRC(P) \<turnstile> TRR6 Q) = TRR6(TRC(P) \<turnstile> TRR6 Q)"
    by (simp add: Healthy_if TRR6_des)
  also have "\<dots> = TRR6(TRC(P) \<turnstile> Q)"
    by (rel_auto)
  finally show ?thesis ..
qed

lemma TRR6_des_RC: "TRR6(RC(P) \<turnstile> Q) = (TRR6(RC(P)) \<turnstile> TRR6(Q))"
  by (rel_auto)

lemma TRR6_wait:
  "(TRR6 (Q \<diamondop> R)) = ((TRR6 Q) \<diamondop> (TRR6 R))"
  by (rel_auto)

lemma TRR6_TRF_wait:
  "R is TRF \<Longrightarrow> (TRR6 (Q \<diamondop> R)) = ((TRR6 Q) \<diamondop> R)"
proof -
  assume 1: "R is TRF"
  have 2: "TRR6 (TRF R) = (TRF R)"
    by (metis "1" Healthy_if TRF_implies_TRR TRR_TRRw TRR_def)
  hence "TRR6(R) = R"
    by (metis "1" Healthy_if)
  thus "(TRR6 (Q \<diamondop> R)) = ((TRR6 Q) \<diamondop> R)"
    by (simp add: TRR6_wait)
qed

definition [rdes_def]: "TC3 (P) = (P \<triangleleft> $wait  \<triangleright> (P ;; J6))" (*(II\<^sub>C \<triangleleft> $wait \<triangleright> ((P ;; J6) \<triangleleft> $ok \<triangleright> P))"*)

utp_const TC3

lemma TC3_idem: "TC3(TC3(P)) = TC3(P)"
  by (rdes_simp; rel_auto)

lemma TC3R3c: "TC3(R3c(P)) = R3c(TRR6 P)"
  apply(rdes_simp)
  apply (rel_auto)
  by (metis (full_types))

lemma TC3R1: "TC3(R1(P)) = R1(TC3 P)"
  apply(rdes_simp)
  by (rel_auto)

lemma TC3R2: "TC3(R2(P)) = R2(TC3 P)"
  apply(rdes_simp)
  by (rel_auto)

lemma TRR6_R1: "TRR6(R1(P)) = R1(TRR6(P))"
  by (rel_auto)

lemma TRR6_R2c: "TRR6(R2c(P)) = R2c(TRR6(P))"
  by (rel_auto)

lemma TRR6_R: "TC3(\<^bold>R(P)) = \<^bold>R(TRR6(P))"
  by (metis R2_comp_def RH_comp TC3R2 TC3R3c comp_apply)

definition [upred_defs]: "TC = NRD \<circ> TC3 \<circ> TC2 \<circ> TC1" 

lemma TC_implies_NRD [closure]: "P is TC \<Longrightarrow> P is NRD"
  by (metis (no_types, hide_lams) Healthy_def TC_def NRD_idem comp_apply)

lemma NRD_rdes [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "NRD(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (\<^bold>R(P \<turnstile> Q \<diamondop> R))"
  by (simp add: Healthy_if NRD_rdes_intro assms)

lemma "TRR6(R1 P) = R1(TRR6 P)"
  by (rel_auto)

lemma "TRR6(R2 P) = R2(TRR6 P)"
  by (rel_auto)

lemma "R3c(TRR6a(P)) = R3c(TRR6a(R3c(P)))"
  by (rel_auto)

lemma TC3_rdes:
  assumes "P is TRC" "Q is TRRw" "R is TRF"
  shows "TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> TRR6(Q) \<diamondop> R)"
(*  apply(rdes_eq_split) *)
proof -
  have "TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (\<^bold>R(TRR6(P \<turnstile> Q \<diamondop> R)))"
    by (simp add: TRR6_R)
  also have "\<dots> = (\<^bold>R(P \<turnstile> TRR6(Q \<diamondop> R)))"
    by (metis Healthy_if TRR6_des_TRC assms(1))
  also have "\<dots> = \<^bold>R(P \<turnstile> TRR6(Q) \<diamondop> R)"
    by (simp add: TRR6_TRF_wait assms(3))
  finally show "?thesis" .
qed

lemma TRR6_TRF: "TRR6(TRF(P)) = TRF(TRR6(P))"
  by (rel_auto; blast)

lemma TRR6_TRC_RC: "TRR6(TRC(RC(P))) = TRC(TRR6(RC(P)))"
  apply rel_auto
  apply blast
  apply blast
  apply blast
  apply meson
  done

lemma TRRw_TRC: "TRRw(TRR6(P)) = TRR6(TRRw(P))"
  by (rel_auto; blast)

lemma TC1_rdes_w:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRRw(Q)) \<diamondop> TRRw(R))"
  using assms
  apply(rdes_eq_split)
  apply blast  
  apply (simp add: Healthy_if TRR1_def TRRw_def)
  by (simp add: Healthy_if TRR1_def TRRw_def)

lemma TC1_NRD [closure]: "P is NRD \<Longrightarrow> TC1(P) is NRD"
proof - 
  assume a: "P is NRD"
  show "TC1(P) is NRD"
    by (rdes_simp cls: a)
qed

lemma TC2_NRD [closure]: "P is NRD \<Longrightarrow> TC2(P) is NRD"
proof - 
  assume a: "P is NRD"
  show "TC2(P) is NRD"
    by (rdes_simp cls: a)
qed

lemma TC3_contract:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(TRR6 P \<turnstile> TRR6 Q \<diamondop> TRR6 R)"
proof -
  have "TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(TRR6(P \<turnstile> Q \<diamondop> R))"
    by (meson TRR6_R)
  also have "\<dots> = \<^bold>R(TRR6(P) \<turnstile> TRR6(Q \<diamondop> R))"
    by (metis Healthy_if TRR6_des_RC assms(1))
  also have "\<dots> = \<^bold>R(TRR6(P) \<turnstile> TRR6(Q) \<diamondop> TRR6(R))"
    by (simp add: TRR6_wait)
  finally show ?thesis .
qed

lemma TRR6_RC1 [closure]: "P is RC \<Longrightarrow> TRR6 P is RC"
proof -
  assume 1: "P is RC"
  show ?thesis
    by (metis "1" Healthy_if Healthy_intro TRR6_closed_wp TRR_TRRw TRR_def trel_theory.top_closed wp_rea_RC_false)
qed

lemma RC_wp [closure]: "P is RC \<Longrightarrow> II\<^sub>t wp\<^sub>r (RC P) is RC"
proof -
  assume 1: "P is RC"
  show ?thesis
    by (simp add: "1" Healthy_if TRR_implies_RR TRR_tc_skip wp_rea_RC)
qed

lemma TC3_NRD [closure]: "P is NRD \<Longrightarrow> TC3(P) is NRD"
proof - 
  assume a: "P is NRD"
  have 1: "P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (rdes_eq cls: a)
  have 2: "pre\<^sub>R P is RC"
    using NRD_neg_pre_RC a by blast
  have 3: "peri\<^sub>R P is RR"
    using NRD_is_RD RD_healths(2) a periR_RR by blast
  have 4: "post\<^sub>R P is RR"
    using NRD_is_RD RD_healths(2) a postR_RR by blast
  show "TC3(P) is NRD"
    by (subst 1)
       (simp add: TC3_contract 2 3 4 closure)
qed

lemma TRR6_uns: "TRR6(\<U>(true, []) \<or> Q) = (\<U>(true, []) \<or> TRR6 Q)"
  by (rel_auto)

(*
lemma "((P ;; J6) ;; Skip) = ((P ;; Skip) ;; J6)"
  apply(simp add: Skip_def)
  apply(rel_auto)
*)

(*
lemma TC2_TC3: "(TC2(TC3(P))) = (TC3(TC2(P)))"
  apply(simp add: TC2_def TC3_def Skip_def)
  apply(rel_auto)
  sledgehammer
*)

lemma TC1_TRRw_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRRw" "R is TRR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  by (subst TC1_rdes_w, simp_all add: closure assms wp Healthy_if)

lemma TC1_TRR_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  by (simp add: TC1_TRRw_rdes TRR_TRRw assms(1) assms(2) assms(3))

lemma TC2w_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRRw" "R is TRRw"
  shows "TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile>(Q \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t)"
  using assms by (rdes_simp)

lemma TC2_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile>(Q \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t)"
  by (simp add: TC2w_rdes TRR_TRRw assms)

lemma TC2_TC1 [closure]: "P is NRD \<Longrightarrow> TC2(TC1(P)) is TC1"
proof -
  assume a: "P is NRD"
  have "TC1(TC2(TC1(P))) = TC2(TC1(P))"
    by (rdes_eq cls: a)
  then show ?thesis
    by (simp add: Healthy_intro)
qed

lemma TC2_TC1_TRR_rdes [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC2(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = \<^bold>R(II\<^sub>t wp\<^sub>r P
                 \<turnstile> ((\<U>(true, []) \<or> TRRw(Q)) \<or> TRRw(R) ;; \<U>(true, []))
                 \<diamondop> TRRw(R) ;; II\<^sub>t)"
proof -
  (*
  have "(TRRw (RR(R))) ;; \<U>(true, []) = RR(R) ;; \<U>(true, [])"
    apply(rel_auto)
    sledgehammer
  *)

  have "TC2(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC2(\<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRRw(Q)) \<diamondop> TRRw(R)))"
    by (simp add: TC1_rdes_w assms)
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r P
                 \<turnstile> ((\<U>(true, []) \<or> TRRw(Q)) \<or> TRRw(R) ;; \<U>(true, []))
                 \<diamondop> TRRw(R) ;; II\<^sub>t)"
    apply(subst TC2w_rdes)
    apply (metis RR_implies_R1 TRC_wp_intro TRR_implies_RR TRR_tc_skip assms(1) tc_skip_self_unit wp_rea_RC wp_rea_seq)
    apply(rel_auto)
    apply(rel_auto)
    apply(rel_auto)
    done
  finally show ?thesis .
qed

lemma TRR6_RC_wp_1: "TRR6(II\<^sub>t wp\<^sub>r (RC P)) = (II\<^sub>t wp\<^sub>r TRR6(RC(P)))"
  by (rel_auto; meson)

lemma TRR6_RC_wp: "TRR6(II\<^sub>t wp\<^sub>r (RC P)) = TRR6(II\<^sub>t wp\<^sub>r TRR6(RC(P)))"
  apply(rel_auto)
  by meson

lemma TRR6_RC_wp_2: "TRR6(II\<^sub>t wp\<^sub>r (RC P)) = (II\<^sub>t wp\<^sub>r RC(P))"
  by (rel_auto)

lemma TRRw_uns: "(\<U>(true, []) \<or> TRRw P) = TRRw(\<U>(true, []) \<or> P)"
  by rel_auto

lemma TC3_TC2_TC1_TRR_rdes [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC3(TC2(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)))) = \<^bold>R(
    II\<^sub>t wp\<^sub>r P
  \<turnstile> (\<U>(true, []) \<or> TRR Q \<or> (TRRw R) ;; \<U>(true, []))
  \<diamondop> TRRw R ;; II\<^sub>t)"
proof - 
  have 1: "TRR6(TRRw Q \<or> (TRRw R) ;; \<U>(true, [])) = (TRR Q \<or> ((TRRw R) ;; \<U>(true, [])))"
    by (rel_auto)
  have 2: "TRR6(R ;; II\<^sub>t) = (R ;; II\<^sub>t)"
    by (rel_auto)
  have 3: "(TRR6 R) ;; \<U>(true, []) = (R ;; \<U>(true, []))"
    apply(rel_auto)
    apply blast+
    by fastforce
  have 4: "(TRR6(R) ;; II\<^sub>t) = (R ;; II\<^sub>t)"
    apply(rel_auto)
    by fastforce

  have "TC3(TC2(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)))) = TC3(\<^bold>R(II\<^sub>t wp\<^sub>r P
    \<turnstile> ((\<U>(true, []) \<or> TRRw(Q)) \<or> TRRw(R) ;; \<U>(true, []))
    \<diamondop> TRRw(R) ;; II\<^sub>t))"
    by (simp add: TC2_TC1_TRR_rdes assms(1) assms(2) assms(3))
  also have "\<dots> = \<^bold>R(TRR6(II\<^sub>t wp\<^sub>r P) \<turnstile> TRR6 (\<U>(true, []) \<or> TRRw Q \<or> TRRw(R) ;; \<U>(true, [])) \<diamondop> TRR6(TRRw R ;; II\<^sub>t))"
    apply(subst TC3_contract)
    apply (simp add: TRR_implies_RR TRR_tc_skip assms(1) wp_rea_RC)
    apply(rel_auto)
    apply(rel_auto)
    by (simp add: utp_pred_laws.sup.assoc)
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> TRR6 (\<U>(true, []) \<or> TRRw Q \<or> TRRw(R) ;; \<U>(true, [])) \<diamondop> TRR6(TRRw R ;; II\<^sub>t))"
    by (metis Healthy_if TRR6_RC_wp_2 assms(1))
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> TRR6 (\<U>(true, []) \<or> TRRw Q \<or> TRRw(R) ;; \<U>(true, [])) \<diamondop> TRRw R ;; II\<^sub>t)"
    by (metis Healthy_if Healthy_intro TRR6_closed_seq TRR_TRRw TRR_def TRR_tc_skip)
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRR6(TRRw Q \<or> TRRw(R) ;; \<U>(true, []))) \<diamondop> TRRw R ;; II\<^sub>t)"
    by (simp add: TRR6_uns)
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRR Q \<or> (TRRw R) ;; \<U>(true, [])) \<diamondop> TRRw R ;; II\<^sub>t)"
    using "1" by presburger
  finally show ?thesis .
qed

(*
lemma TRR6_RR: "P is RR \<Longrightarrow> TRR6 P is RR"
proof -
  assume 1: "P is RR"
  have "RR(TRR6(RR P)) = TRR6(RR P)"
    by (rel_auto)
  thus ?thesis
    by (metis "1" Healthy_def')
qed
*)

lemma TRRw_RR [closure]: "P is RR \<Longrightarrow> TRRw P is RR"
proof -
  assume 1: "P is RR"
  have "RR(TRRw(RR P)) = TRRw(RR P)"
    by (rel_auto)
  thus ?thesis
    by (metis "1" Healthy_def')
qed

lemma TC1_TC2_com:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC1(TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC2(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)))"
  apply(rdes_eq_split cls: assms)
  apply(rel_auto)
  apply(rel_auto)
  apply(rel_auto)
  apply blast+
  done

lemma TC1_TC3:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC3(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC1(TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)))"
proof -
  have "TC3(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC3(\<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRRw Q) \<diamondop> TRRw R))"
    by (simp add: TC1_rdes_w assms)
  also have "\<dots> = \<^bold>R(TRR6(II\<^sub>t wp\<^sub>r P) \<turnstile> TRR6 (\<U>(true, []) \<or> TRRw Q) \<diamondop> TRR6(TRRw R))"
    apply(subst TC3_contract)
    apply(simp add: TRR_implies_RR TRR_tc_skip assms(1) wp_rea_RC)
    apply(rel_auto)
    apply (simp add: Healthy_if TRR1_def TRR_implies_RR TRR_tc_skip TRRw_def assms(3) rrel_theory.Healthy_Sequence)
    apply blast
    done
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r (TRR6 P) \<turnstile> TRR6(\<U>(true, []) \<or> TRRw Q) \<diamondop> TRR6(TRRw R))"
    by (metis Healthy_if TRR6_RC_wp_1 assms(1))
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r (TRR6 P) \<turnstile> (\<U>(true, []) \<or> TRR6(TRRw Q)) \<diamondop> TRR6(TRRw R))"
    by (simp add: TRR6_uns)
  also have "\<dots> = \<^bold>R(II\<^sub>t wp\<^sub>r (TRR6 P) \<turnstile> (\<U>(true, []) \<or> TRRw(TRR6 Q)) \<diamondop> TRRw(TRR6 R))"
    by (simp add: TRRw_TRC)
  also have "\<dots> = TC1(\<^bold>R(TRR6 P \<turnstile> TRR6 Q \<diamondop> TRR6 R))"
    by (simp add: TC1_rdes_w assms closure)
  also have "\<dots> = TC1(TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)))"
    by (simp add: TC3_contract assms)
  finally show ?thesis .
qed

lemma TC2_TC3_rdes:
  assumes "P is TRC" "Q is TRRw" "R is TRRw"
  shows "TC3(TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC2(TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)))"
proof -
  have 1: "TRR6(Q \<or> R ;; \<U>(true, [])) = (TRR6 Q \<or> (R ;; \<U>(true, [])))"
    apply (rel_auto)
    by blast
  have 2: "TRR6(R ;; II\<^sub>t) = (R ;; II\<^sub>t)"
    by (rel_auto)
  have 3: "(TRR6 R) ;; \<U>(true, []) = (R ;; \<U>(true, []))"
    apply(rel_auto)
    apply blast+
    by fastforce
  have 4: "(TRR6(R) ;; II\<^sub>t) = (R ;; II\<^sub>t)"
    apply(rel_auto)
    by fastforce
  have "TC3(TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R))) = TC3(\<^bold>R(P \<turnstile> (Q \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t))"
    by (simp add: TC2w_rdes assms(1) assms(2) assms(3))
  also have "\<dots> = \<^bold>R(TRR6 P \<turnstile> (TRR6(Q) \<or> R ;; \<U>(true, [])) \<diamondop> (R ;; II\<^sub>t))"
    by (metis (no_types, lifting) "1" "2" Healthy_if TRC_TRR6 TRR6_R TRR6_des_TRC TRR6_wait assms(1))
  also have "\<dots> = \<^bold>R(TRR6 P \<turnstile> (TRR6(Q) \<or> (TRR6 R) ;; \<U>(true, [])) \<diamondop> ((TRR6 R) ;; II\<^sub>t))"
    using "3" "4" by presburger
  also have "\<dots> = TC2(\<^bold>R(TRR6 P \<turnstile> TRR6(Q) \<diamondop> TRR6 R))"
    by (metis (no_types, lifting) Healthy_if Healthy_intro TC2w_rdes TRC_TRR6 TRR_def TRRw_TRC assms(1) assms(2) assms(3))
  also have "\<dots> = TC2(TC3(\<^bold>R(P \<turnstile> Q \<diamondop> R)))"
    by (simp add: TC3_contract TRC_implies_RC TRR_implies_RR TRRw_implies_RR assms(1) assms(2) assms(3))
  finally show ?thesis .
qed
(*
lemma TC1_TC3_1:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC3(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R))) is TC1"
proof -
  have "TC1(TC3(TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)))) = TC1(TC3(\<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRRw Q) \<diamondop> TRRw R)))"
    by (simp add: TC1_rdes_w assms)
  also have "\<dots> = TC1(\<^bold>R(TRR6(II\<^sub>t wp\<^sub>r P) \<turnstile> TRR6 (\<U>(true, []) \<or> TRRw Q) \<diamondop> TRR6(TRRw R)))"
    apply(subst TC3_contract)
    apply(simp add: TRR_implies_RR TRR_tc_skip assms(1) wp_rea_RC)
    apply(rel_auto)
    apply (simp add: Healthy_if TRR1_def TRR_implies_RR TRR_tc_skip TRRw_def assms(3) rrel_theory.Healthy_Sequence)
    by blast
  also have "\<dots> = TC1(\<^bold>R(TRR6(II\<^sub>t wp\<^sub>r P) \<turnstile> \<U>(true, []) \<or> TRR Q \<diamondop> TRR R))"
    oops
qed
 *)

lemma TC3_TC1 [closure]: "P is NRD \<Longrightarrow> TC3(TC1(P)) is TC1"
proof -
  assume a: "P is NRD"
  have 1: "P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (rdes_eq cls: a)
  have "TC1(TC3(TC1(P))) = TC1(TC1(TC3(P)))"
    by (metis "1" NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_TC3 a periR_RR postR_RR)
  also have "\<dots> = TC1(TC3(P))"
    by (meson TC1_idem)
  finally have "TC1(TC3(TC1(P))) = TC1(TC3(P))" .
  thus ?thesis
    by (metis "1" Healthy_def NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_TC3 a periR_RR postR_RR)
qed

lemma TC3_TC2 [closure]: "P is NRD \<Longrightarrow> P is TC1 \<Longrightarrow> TC3(TC2(P)) is TC2"
proof -
  assume a: "P is NRD"
  assume b: "P is TC1"
  have 1: "P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (rdes_eq cls: a)
  have 2: "TC1(P) = \<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw(peri\<^sub>R P)) \<diamondop> TRRw(post\<^sub>R P))"
    by (metis "1" NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_rdes_w a periR_RR postR_RR)
  have "TC2(TC3(TC2(P))) = TC2(TC3(TC2(TC1(P))))"
    by (simp add: Healthy_if b)
  also have "\<dots> = TC2(TC3(TC2(\<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw(peri\<^sub>R P)) \<diamondop> TRRw(post\<^sub>R P)))))"
    by (simp add: "2")
  also have "\<dots> = TC2(TC2(TC3(\<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw(peri\<^sub>R P)) \<diamondop> TRRw(post\<^sub>R P)))))"
    apply(subst TC2_TC3_rdes)
    apply (metis NRD_neg_pre_RC R2_implies_R1 RR_implies_R2 TRC_wp_intro TRR_implies_RR TRR_tc_skip a tc_skip_self_unit wp_rea_RC wp_rea_seq)
    apply (simp add: Healthy_intro TRRw_idem TRRw_uns)
    apply (simp add: Healthy_intro TRRw_idem)
    by blast
  also have "\<dots> = TC2(TC3(\<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw(peri\<^sub>R P)) \<diamondop> TRRw(post\<^sub>R P))))"
    by (meson TC2_idem)
  also have "\<dots> = TC3(TC2(\<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw(peri\<^sub>R P)) \<diamondop> TRRw(post\<^sub>R P))))"
    apply(subst TC2_TC3_rdes)
    apply (metis NRD_neg_pre_RC R2_implies_R1 RR_implies_R2 TRC_wp_intro TRR_implies_RR TRR_tc_skip a tc_skip_self_unit wp_rea_RC wp_rea_seq)
    apply (simp add: Healthy_intro TRRw_idem TRRw_uns)
    apply (simp add: Healthy_intro TRRw_idem)
    by blast
  also have "\<dots> = TC3(TC2(TC1(P)))"
    using "2" by presburger
  also have "\<dots> = TC3(TC2(P))"
    by (simp add: Healthy_if b)
  finally have "TC2(TC3(TC2(P))) = TC3(TC2(P))" .
  thus ?thesis
    by (simp add: Healthy_intro)
qed

(*
lemma "TC1(P) is NRD \<Longrightarrow> P is NRD"
proof -
  assume a: "TC1(P) is NRD"

  show "P is NRD"
    (* apply(simp add: closure a) *) 
    oops

lemma "lemma "TC1(P) is NRD \<Longrightarrow> P is NRD"
proof -
  assume a: "TC1(P) is NRD"

  show "P is NRD"
    apply(simp add: closure a)
qed"
*)

(*
lemma TC3_TC2 [closure]: "P is NRD \<Longrightarrow> TC3(TC1(P)) is TC1"
proof -
  assume a: "P is NRD"
  have 1: "P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (rdes_eq cls: a)
  have "TC1(TC3(TC1(P))) = TC1(TC1(TC3(P)))"
    by (metis "1" NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_TC3 a periR_RR postR_RR)
  also have "\<dots> = TC1(TC3(P))"
    by (meson TC1_idem)
  finally have "TC1(TC3(TC1(P))) = TC1(TC3(P))" .
  thus ?thesis
    by (metis "1" Healthy_def NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_TC3 a periR_RR postR_RR)
qed
*)

(*
lemma "NRD(TC1(P)) is TC1"
  sledgehammer

lemma "NRD(TC3(P)) is TC3"
proof -
  assume a: "P is NRD"
  have "TC3(NRD(TC3(NRD(P)))) = NRD(TC3(NRD(P)))"
    apply(rdes_simp)
    apply(rel_simp)
    apply(safe)
    sledgehammer
qed
*)

lemma TC_implies_TC1 [closure]: 
  assumes "P is TC"
  shows "P is TC1"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "P = TC(P)"
    by (simp add: Healthy_if assms)
  also have "\<dots> = NRD(TC3(TC2(TC1(P))))"
    by (simp add: TC_def)
  also have "\<dots> = NRD(TC1(TC3(TC2(TC1(P)))))"
    by (metis Healthy_if TC1_NRD TC2_NRD TC2_TC1 TC3_TC1 a)
  finally have "P = NRD(TC1(TC3(TC2(TC1(P)))))" .
  moreover have "NRD(TC1(TC3(TC2(TC1(P))))) is TC1"
    by (metis Healthy_def' TC1_NRD TC1_idem TC2_NRD TC3_NRD a)
  ultimately show ?thesis
    by presburger
qed

lemma TC_implies_TC2 [closure]: 
  assumes "P is TC"
  shows "P is TC2"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "P = TC(P)"
    by (simp add: Healthy_if assms)
  also have "\<dots> = NRD(TC3(TC2(TC1(P))))"
    by (simp add: TC_def)
  also have "\<dots> = NRD(TC2(TC3(TC2(P))))"
    by (simp add: Healthy_if TC3_TC2 TC_implies_TC1 a assms)
  finally have "P = NRD(TC2(TC3(TC2(P))))" .
  moreover have " NRD(TC2(TC3(TC2(P)))) is TC2"
    by (simp add: Healthy_if TC2_NRD TC3_NRD TC3_TC2 TC_implies_TC1 a assms)
  ultimately show ?thesis
    by presburger
qed

lemma TC_implies_TC3 [closure]: 
  assumes "P is TC"
  shows "P is TC3"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  show "P is TC3"
    by (metis Healthy_if Healthy_intro TC3_NRD TC_def TC_implies_TC1 TC_implies_TC2 a assms comp_def)
qed

lemma TC_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R (
      P
    \<turnstile> (Q \<or> \<U>(true, []) \<or> R ;; \<U>(true, []))
    \<diamondop> R ;; II\<^sub>t
  )"
  apply(simp add: TC_def)
  apply(subst TC3_TC2_TC1_TRR_rdes)
  apply (simp add: TRC_implies_RC assms(1))
  apply (simp add: TRR_implies_RR assms(2))
  apply (simp add: TRR_implies_RR assms(3))
  apply (rdes_eq_split cls: assms)
  apply(blast)
  apply (simp add: Healthy_if TRR_TRRw assms(2) assms(3) utp_pred_laws.sup.left_commute)
  apply (simp add: Healthy_if TRR_TRRw assms(3))
  done

lemma TRR6_seq_comp: "(TRR6(P) ;; TRR6(Q)) is TRR6"
  by (meson Healthy_intro TRR6_closed_seq TRR6_idem)

lemma TC3RD3c: "TC3(RD3c(RH(P))) = RD3c(TC3(RH(P)))"
  apply(rdes_simp)
  apply(rel_auto)
  apply metis+
  done

(*
lemma TC3R1: "TC3(R1(P)) = R1(TC3(P))"
  apply(rdes_simp)
  apply(rel_auto)
  done
*)

lemma "P is NRD \<Longrightarrow> Q is NRD \<Longrightarrow> (TC3(P);;TC3(Q)) is TC3"
proof - 
  assume a: "P is NRD" "Q is NRD"
  have 1: "P = \<^bold>R(P)" "Q = \<^bold>R(Q)"
    by (metis NRD_is_RD RD_reactive_tri_design RH_idem a(1))
       (metis NRD_is_RD RD_reactive_tri_design RH_idem a(2))
  have "(TC3(P) ;; TC3(Q)) = (TC3(NRD(P)) ;; TC3(NRD(Q)))"
    by (simp add: Healthy_if a)
  also have "\<dots> = (NRD(TRR6(P)) ;; NRD(TRR6(Q)))"
    by (metis (no_types, lifting) "1"(1) "1"(2) Healthy_if NRD_def R1_R3c_commute
        R2c_R3c_commute R3c_idem RH_def TC3R3c TC3_NRD a(1) a(2) comp_def)
  also have "\<dots> = ((NRD(NRD(TRR6(P)) ;; NRD(TRR6(Q)))))"
    by (metis Healthy_if NRD_seqr_closure TC3_NRD a(1) a(2) calculation)
    oops
(*
    sledgehammer
qed
*)

lemma TC_closed_seqr [closure]: 
  assumes "P is TC" "Q is TC"
  shows "P ;; Q is TC"
proof -
  have "P ;; Q is TC1"
    by (metis (no_types, hide_lams) Healthy_def RA1 TC1_def TC_implies_TC1 assms(1))
  moreover have "P ;; Q is TC2"
    by (metis (no_types, hide_lams) Healthy_def RA1 TC2_def TC_implies_TC2 assms(2))
  moreover have "P ;; Q is TC3"
    oops
(*
    sorry
  ultimately show ?thesis
    by (metis Healthy_comp NRD_seqr_closure TC_def TC_implies_NRD assms(1) assms(2))
qed
 *)

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
  have "TC3(P \<sqinter> Q) = (TC3 P \<sqinter> TC3 Q)"
    by (rdes_simp; rel_auto)
  then have 4: "P \<sqinter> Q is TC3"
    by (metis Healthy_def TC_implies_TC3 assms)
  from 1 2 3 4 show "P \<sqinter> Q is TC"
    by (simp add: Healthy_comp TC_def)
qed

lemma TRC_neg_TRR6 [closure]: "P is TRC \<Longrightarrow> (\<not>\<^sub>r P is TRR6)"
proof - 
  assume "P is TRC"
  moreover have "TRR6 (\<not>\<^sub>r TRC P) = (\<not>\<^sub>r TRC P)"
    by (rel_auto)
  ultimately show ?thesis
    by (simp add: Healthy_def')
qed


lemma TRC_neg_TRR [closure]: "P is TRC \<Longrightarrow> (\<not>\<^sub>r P is TRR)"
proof - 
  assume "P is TRC"
  then show ?thesis
    by (metis Healthy_if Healthy_intro TRC_TRR1 TRC_neg_TRR6 TRR_def TRRw_closed_neg)
qed

(*
  have "(\<not>\<^sub>r TRC (P)) is TRC"
    apply(rule TRC_wp_intro)
    apply(rule healthy_if)
    apply(rel_auto)
  have "TRC(\<not>\<^sub>r TRC (P)) = (\<not>\<^sub>r TRC (P))"
    apply(rel_simp)
    apply(safe)
    apply (metis Prefix_Order.Nil_prefix dual_order.refl minus_cancel order_class.order.antisym)
    apply(safe)
    done
qed
*)

lemma TC_inner_closures [closure]:
  assumes "P is TC"
  shows "pre\<^sub>R(P) is TRC" "peri\<^sub>R(P) is TRR" "post\<^sub>R(P) is TRF" "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])" "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
proof -
  have a: "P is NRD"
    using TC_implies_NRD assms by blast
  have b: "P = TC1(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC1 TC_implies_TC2 a assms)
  hence 1: "P = \<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRR (peri\<^sub>R P)) \<diamondop> TRR (post\<^sub>R P))"
    by (smt (z3) Healthy_def' NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_rdes_w TC3_contract TC_implies_TC3 TRC_TRR6 TRC_wp_intro TRR6_uns TRR_def TRR_implies_RR TRR_tc_skip TRRw_RR TRRw_uns a assms disj_RR periR_RR postR_RR preR_NRD_RR preR_rdes trel_theory.healthy_top utp_pred_laws.sup_bot_right wp_rea_RR_closed)
  hence 2: "II\<^sub>t wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
    by (metis TRR_implies_RR TRR_tc_skip a preR_NRD_RR preR_rdes wp_rea_RR_closed)
  thus c [closure]: "pre\<^sub>R(P) is TRC"
    by (simp add: NRD_neg_pre_RC TRC_wp_intro a)

  have c1: "pre\<^sub>R(P) = TRC(pre\<^sub>R P)"
    by (simp add: Healthy_if c)
  have c2: "$ref\<acute> \<sharp> pre\<^sub>R(P)"
    using TRC_unrests'(2) c by blast
  have c3: "$pat\<acute> \<sharp> pre\<^sub>R(P)"
    using TRC_unrests'(4) c by blast

  (*
  have d: "TRC(\<not>\<^sub>r TRC (peri\<^sub>R P)) = (\<not>\<^sub>r TRC (P))"
    apply(rel_auto)
    sorry
  *)
   (* apply (metis Prefix_Order.Nil_prefix dual_order.antisym minus_cancel order_refl) *)
  have peri: "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (\<U>(true, []) \<or> TRR (peri\<^sub>R P)))"
    by (subst 1, simp add: rdes closure assms 2)
  also have "... is TRR"
    by (metis (no_types, lifting) Healthy_def TRC_TRR1 TRC_neg_TRR6 TRR6_uns TRR_def TRRw_closed_neg TRRw_uns c rea_impl_def trel_theory.HCond_Idem trel_theory.disj_is_healthy)
  (*
    by (metis Healthy_def TRC_TRR1 TRRw_closed_disj TRR_closed_neg TRRw_idem TRR_uns c rea_impl_def)
   *)
    (* by (simp add: closure assms) *)
  finally show [closure]: "peri\<^sub>R(P) is TRR" .
  show "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])"
    by (metis peri rea_impl_disj utp_pred_laws.sup.cobounded1)
  have "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r TRR (post\<^sub>R P))"
    by (metis "1" "2" Healthy_def' NRD_neg_pre_RC RC_implies_RR TRR_implies_RR a postR_rdes trel_theory.HCond_Idem)
  also have "... is TRR"
    by (smt (z3) Healthy_def NRD_is_RD RD_healths(2) RR_TRR TRC_TRR1 TRC_neg_TRR6 TRR1_def TRR6_J6 TRR6_seq_comp TRR_TRR1_raw TRR_TRRw TRR_def TRR_ident_intro TRR_tc_skip TRRw_closed_disj TRRw_closed_neg a c postR_RR rea_impl_def seqr_or_distl)
  finally have [closure]: "post\<^sub>R(P) is TRR" .  
  have "P = TC2(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC2 a assms)
  hence 3: "P = \<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P ;; II\<^sub>t)"
    using TC2_rdes \<open>peri\<^sub>R P is TRR\<close> \<open>post\<^sub>R P is TRR\<close> c by fastforce
  hence "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R P ;; II\<^sub>t)"
    by (metis TRC_RR TRR_implies_RR TRR_tc_skip \<open>(pre\<^sub>R P \<Rightarrow>\<^sub>r TRR (post\<^sub>R P)) is TRR\<close> \<open>post\<^sub>R P = (pre\<^sub>R P \<Rightarrow>\<^sub>r TRR (post\<^sub>R P))\<close> c postR_rdes seq_RR_closed)
  also have "... is TRF"
    apply(rule TRF_intro)
    using \<open>post\<^sub>R P is TRR\<close> calculation apply presburger
    apply(simp_all add: closure c2 c3 assms unrest)
    done
  finally show "post\<^sub>R(P) is TRF" .
  have "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])))"
    by (subst 3, simp add: rdes closure)  
  thus "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
    by (metis (no_types, hide_lams) rea_impl_disj utp_pred_laws.sup.cobounded1 utp_pred_laws.sup_commute) 
qed

(*
lemma TC_inner_closures [closure]:
  assumes "P is TC"
  shows "pre\<^sub>R(P) is TRC" "peri\<^sub>R(P) is TRRw" "post\<^sub>R(P) is TRF" "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])" "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
proof -
  have a: "P is NRD"
    using TC_implies_NRD assms by blast
  have b: "P = TC1(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC1 TC_implies_TC2 a assms)
  hence 1: "P = \<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRRw (peri\<^sub>R P)) \<diamondop> TRRw (post\<^sub>R P))"
    by (metis NRD_is_RD NRD_neg_pre_RC RD_healths(2) TC1_rdes_w a periR_RR postR_RR)
  hence 2: "II\<^sub>t wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
    by (metis TRR_implies_RR TRR_tc_skip a preR_NRD_RR preR_rdes wp_rea_RR_closed)
  thus c [closure]: "pre\<^sub>R(P) is TRC"
    by (simp add: NRD_neg_pre_RC TRC_wp_intro a)
  have peri: "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (\<U>(true, []) \<or> TRRw (peri\<^sub>R P)))"
    by (subst 1, simp add: rdes closure assms 2)
  also have "... is TRRw"
    by (metis Healthy_def TRC_TRR1 TRRw_closed_disj TRRw_closed_neg TRRw_idem TRRw_uns c rea_impl_def)
    (* by (simp add: closure assms) *)
  finally show [closure]: "peri\<^sub>R(P) is TRRw" .
  show "peri\<^sub>R(P) \<sqsubseteq> \<U>(true, [])"
    by (metis peri rea_impl_disj utp_pred_laws.sup.cobounded1)
  have "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r TRRw (post\<^sub>R P))"
    by (metis "1" "2" NRD_is_RD RD_healths(2) TRRw_RR a postR_RR postR_rdes preR_NRD_RR)
  also have "... is TRRw"
    by (simp add: Healthy_intro TRC_TRR1 TRRw_closed_disj TRRw_closed_neg TRRw_idem c rea_impl_def)
  finally have [closure]: "post\<^sub>R(P) is TRRw" .  
  have "P = TC2(\<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (simp add: Healthy_if NRD_is_RD RD_reactive_tri_design TC_implies_TC2 a assms)
  hence 3: "P = \<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P ;; II\<^sub>t)"
    using TC2w_rdes \<open>peri\<^sub>R P is TRRw\<close> \<open>post\<^sub>R P is TRRw\<close> c by fastforce
  hence "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R P ;; II\<^sub>t)"
    by (metis TRR_implies_RR TRR_tc_skip TRRw_implies_RR \<open>(pre\<^sub>R P \<Rightarrow>\<^sub>r TRRw (post\<^sub>R P)) is TRRw\<close> \<open>post\<^sub>R P = (pre\<^sub>R P \<Rightarrow>\<^sub>r TRRw (post\<^sub>R P))\<close> a postR_rdes preR_NRD_RR rrel_theory.Healthy_Sequence)
  also have "... is TRF"
    by (rule TRF_intro, simp_all add: closure assms unrest)  
  finally show "post\<^sub>R(P) is TRF" .
  have "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; \<U>(true, [])))"
    by (subst 3, simp add: rdes closure)  
  thus "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
    by (metis (no_types, hide_lams) rea_impl_disj utp_pred_laws.sup.cobounded1 utp_pred_laws.sup_commute) 
qed
*)

lemma TC_elim [RD_elim]: "P is TC \<Longrightarrow> Q (\<^bold>R (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)) \<Longrightarrow> Q P"
  by (simp add: NRD_elim TC_implies_NRD)

lemma TC_elim': "P is TC \<Longrightarrow> Q (\<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> \<U>(true, []) \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P)) \<Longrightarrow> Q P"
  by (simp add: NRD_elim TC_implies_NRD TC_inner_closures(4) TC_inner_closures(5) utp_pred_laws.sup_absorb1)
  
lemma TC_intro:
  assumes "P\<^sub>1 is TRC" "P\<^sub>2 is TRR" "P\<^sub>3 is TRF" "P\<^sub>2 \<sqsubseteq> \<U>(true, [])" "P\<^sub>2 \<sqsubseteq> P\<^sub>3 ;; \<U>(true, [])"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) is TC"
proof -
  have "TC1(\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (simp add: TC1_TRR_rdes TRF_implies_TRR assms(1) assms(2) assms(3) assms(4) utp_pred_laws.sup.absorb2)
  moreover have "TC2(\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (simp add: TC2_rdes assms closure wp rpred Healthy_if utp_pred_laws.sup_absorb1 utp_pred_laws.sup_absorb2)
  moreover have "TC3(\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)"
    by (metis Healthy_if TC3_rdes TRR_TRRw TRR_def assms(1) assms(2) assms(3))
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
  \<turnstile> ((idle\<^sub>S(peri\<^sub>R(P)) \<squnion>\<^sub>t idle\<^sub>I(peri\<^sub>R(Q)))
   \<or> (idle\<^sub>S(peri\<^sub>R(Q)) \<squnion>\<^sub>t idle\<^sub>I(peri\<^sub>R(P))) 
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
  apply (metis min.commute min.left_idem min.strict_order_iff)
  apply (metis min.commute min.left_idem min.strict_order_iff)
  apply meson
  apply blast
  apply blast
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply meson
  apply blast
  apply blast
  apply meson
  apply meson
  apply meson
  apply blast
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
  oops
(* TODO: fix proof *)
(*  by (trr_auto) *)
 

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
  oops
(* TODO: fix *)
(*
  apply(trr_auto)
  done
 *)

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
  apply(trr_auto)
  done

lemma "Stop \<box> do\<^sub>T(a) = do\<^sub>T(a)"
  apply(rdes_eq_split cls: extChoice_def)
  apply blast
   apply(trr_simp)
  apply(safe)
        apply (smt (z3) tock_ord_Evt tocks_idleprefix_fp tocks_iff_idleprefix_fp)
       apply (smt (z3) tock_ord_Evt tocks_idleprefix_fp tocks_iff_idleprefix_fp)
      apply fastforce
  using tocks_idleprefix_fp tocks_iff_idleprefix_fp apply auto[1]
  apply (metis tocks_Evt tocks_append)
  apply (meson rmember.simps(1))
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

(*
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
*)

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

lemma uns_refine_S: "P \<sqsubseteq> \<U>(true, []) \<Longrightarrow> idle\<^sub>S(P) \<sqsubseteq> \<U>(true, [])"
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
  oops
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

lemma "\<U>(true, []) \<sqsubseteq> (time\<^sub>I(TRR P) \<and> ((TRF Q) ;; \<U>(true, [])))"
  apply(trr_simp)
  oops

lemma "S \<sqsubseteq> (R \<and> S)"
  by simp

lemma "(R \<or> S) \<sqsubseteq> S"
  by simp

lemma
  assumes "P is TRR"
  shows "time\<^sub>I(P) is TRF"
  using TRF_time_insistant assms by auto

lemma active_TRF [closure]:
  assumes "P is TRF"
  shows "active\<^sub>I(P) is TRF"
proof -
  have 1: "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
    using TRF_unrests assms by auto

  show ?thesis
    apply(rule TRF_intro)
    using TRF_implies_TRR active_TRR_insistant assms apply blast
    using 1(1) apply(rel_auto)
    using 1(2) apply(rel_auto)
    done
qed

lemma time_active_uns:
  assumes "P is TRR" "Q is TRF"
  shows "(time\<^sub>I(P) \<and> (active\<^sub>I(Q) ;; \<U>(true, []))) = ((time\<^sub>I(P) \<and> active\<^sub>I(Q)) ;; \<U>(true, []))"
proof -
  have 1: "time\<^sub>I(P) \<and> active\<^sub>I(Q) is TRF" 
    by (simp add: TRF_conj_closure TRF_time_insistant active_TRF assms(1) assms(2))

  show ?thesis
    apply(simp add: unstable_TRF 1 assms closure)
    apply(rel_auto)
    done
qed

lemma
  assumes "P is TRR"
  shows "P \<sqsubseteq> active\<^sub>I(P)"
  by (metis TRR_idle_or_active_insistant assms disj_upred_def semilattice_sup_class.le_sup_iff trel_theory.utp_po.le_refl)

(*
lemma idle_time:
  shows "idle\<^sub>I(P) = (idle\<^sub>I(P) \<and> time\<^sub>I(P))"
  apply(rel_auto)
  by (metis Prefix_Order.prefixE append_minus)

lemma idle_time_refine:
  shows "time\<^sub>I(P) \<sqsubseteq> idle\<^sub>I(P)"
  by (meson idle_time utp_pred_laws.inf.orderI)
*)

lemma tconj_conj_refine: "(P \<squnion>\<^sub>t Q) \<sqsubseteq> (P \<and> Q)"
  apply(rel_simp)
  by blast

lemma
  assumes "P is TRR" "P is TIP"
  shows "(idle\<^sub>I(P) ;; \<U>(true, [])) \<sqsubseteq> time\<^sub>I(P)"
    apply(subst (4 2) TRRconcretify)
   apply (simp add: assms)
  apply(rel_auto)
  oops

lemma
  assumes "P is TRR" "P is TIP"
  shows "(idle\<^sub>I(P) ;; \<U>(true, [])) = time\<^sub>I(P) ;; \<U>(true, [])"
  apply(subst (6 2) TRRconcretify)
   apply (simp add: assms)
  apply(rel_auto)
  oops

lemma idle_I_idle_E:
  "(idle\<^sub>S(P) \<squnion>\<^sub>t (Q ;; \<U>(true, []))) \<sqsubseteq> (idle\<^sub>E(P) \<and> (Q ;; \<U>(true, [])))"
  "((Q ;; \<U>(true, [])) \<squnion>\<^sub>t idle\<^sub>S(P)) \<sqsubseteq> ((Q ;; \<U>(true, [])) \<and> idle\<^sub>E(P))"
  by rel_blast+

lemma TRF_uns_seqr:
  assumes "P is TRF" "Q is TRR" "$st\<acute> \<sharp> P"
  shows "(P \<and> (Q ;; \<U>(true, []))) = ((P \<and> Q) ;; \<U>(true, []))"
proof -
  have "((\<exists> $st\<acute> \<bullet> TRF P) \<and> (TRR Q ;; \<U>(true, []))) = (((\<exists> $st\<acute> \<bullet> TRF P) \<and> TRR Q) ;; \<U>(true, []))"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2) assms(3) ex_unrest)
qed

lemma extChoice_closure [closure]:
  assumes "P is TC" "Q is TC"
  shows "P \<box> Q is TC"
proof (rdes_simp cls: assms extChoice_def)
  have 1: "pre\<^sub>R P is TRC" "peri\<^sub>R P is TRR" "post\<^sub>R P is TRF"
          "pre\<^sub>R Q is TRC" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    using assms TC_inner_closures by auto
  have 9: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) is TRR" "(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) is TRR" "(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) is TRF"
          "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) is TRR" "(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) is TRR" "(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) is TRF"
    apply (simp add: "1"(1) "1"(2) TRC_neg_TRR rea_impl_def trel_theory.disj_is_healthy)
    apply (simp add: "1"(1) "1"(3) TRC_neg_TRR TRF_implies_TRR rea_impl_def trel_theory.disj_is_healthy)
    apply (metis "1"(1) "1"(3) NRD_is_RD RD_reactive_tri_design TC_implies_NRD TRC_RR TRF_implies_TRR TRR_implies_RR assms(1) postR_rdes)
    apply (simp add: "1"(4) "1"(5) TRC_neg_TRR rea_impl_def trel_theory.disj_is_healthy)
    apply (simp add: "1"(4) "1"(6) TRC_neg_TRR TRF_implies_TRR rea_impl_def trel_theory.disj_is_healthy)
    apply (metis "1"(4) "1"(6) NRD_is_RD RD_reactive_tri_design TC_implies_NRD TRC_RR TRF_implies_TRR TRR_implies_RR assms(2) postR_rdes)
    done
  have 21: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> \<U>(true, [])"
    by (metis (no_types, lifting) TC_inner_closures(4) assms(1) disj_upred_def rea_impl_def semilattice_sup_class.sup.order_iff utp_pred_laws.sup_assoc)
  then have 2: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> \<U>(true, [])"
    by (meson uns_refine)

  have 22: "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (metis TC_inner_closures(4) assms(2) disj_upred_def rea_impl_disj semilattice_sup_class.le_iff_sup)
  then have 3: "idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (meson uns_refine)

  have 4: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (meson "2" "3" "9"(1) "9"(4) idle_TRR_insistant uns_tconj)

  have 41: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (meson "2" "22" "9"(1) "9"(4) idle_TRR_insistant idle_TRR_stateless uns_refine_S uns_tconj)
  have 42: "idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> \<U>(true, [])"
    by (meson "21" "3" "9"(1) "9"(4) idle_TRR_insistant idle_TRR_stateless uns_refine_S uns_tconj)

  have 71: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> ((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))"
    by (metis NRD_is_RD RD_healths(2) RD_reactive_tri_design TC_implies_NRD TC_inner_closures(5) assms(1) postR_RR postR_rdes preR_NRD_RR rea_impl_def utp_pred_laws.sup.coboundedI2)
  from 71 have 72: "active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> active\<^sub>I((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;;  \<U>(true, []))"
    by (metis active_disj_insistant utp_pred_laws.sup.absorb_iff2)
  from 71 have 73: "idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<sqsubseteq> idle\<^sub>I((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))"
    by (metis idle_conj_insistant utp_pred_laws.inf.absorb_iff2)
  have 74: "idle\<^sub>I((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])) = (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))"
    by (rel_auto)


  have 81: "(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> ((pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;;  \<U>(true, []))"
    by (metis NRD_is_RD RD_healths(2) RD_reactive_tri_design TC_implies_NRD TC_inner_closures(5) assms(2) postR_RR postR_rdes preR_NRD_RR rea_impl_def utp_pred_laws.sup.coboundedI2)
  from 81 have 82: "active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> active\<^sub>I((pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))"
    by (metis active_disj_insistant utp_pred_laws.sup.absorb_iff2)
  from 81 have 83: "idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<sqsubseteq> idle\<^sub>I((pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))"
    by (metis idle_conj_insistant utp_pred_laws.inf.absorb_iff2)
  have 84: "idle\<^sub>I((pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, [])) = (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))"
    by (rel_auto)

  have 91: "idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
          \<sqsubseteq> idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))"
    by (metis "83" "84" tconj_mono(2))
  have 92: "idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
          \<sqsubseteq> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))"
    by (metis "73" "74" tconj_mono(2))
  have 93: "(time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q))
          \<sqsubseteq> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, [])))"
    by (metis "82" "9"(5) active_uns utp_pred_laws.inf.orderI utp_pred_laws.inf_idem utp_pred_laws.inf_mono)
  have 94: "(time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
          \<sqsubseteq> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))"
    by (metis "72" "9"(2) active_uns utp_pred_laws.inf.idem utp_pred_laws.inf.orderI utp_pred_laws.inf_mono)

  have 101: "((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))))
           = ((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, []))"
    apply(rule TRF_uns_seqr)
      apply (simp add: "9"(1) idle_TRF_insistant_end)
    apply (simp add: "9"(5) idle_TRR_insistant)
    apply rel_auto
    done
  have 102: "((idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))))
           = ((idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, []))"
    apply(rule TRF_uns_seqr)
    apply (simp add: "9"(4) idle_TRF_insistant_end)
    apply (simp add: "9"(2) idle_TRR_insistant)
    apply rel_auto
    done
  have 103: "(time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, [])))
      = (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, [])"
    by (simp add: "9"(1) "9"(6) time_active_uns)
  have 104: "(time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))
      = (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, [])"
    by (simp add: "9"(3) "9"(4) time_active_uns)

  have "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
       \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
       \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
      \<sqsubseteq> (idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))"
    by (meson "91" "92" "93" "94" utp_pred_laws.sup.mono)
  moreover have "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))
      \<sqsubseteq> (idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))"
    by (metis (no_types, lifting) idle_I_idle_E(1) utp_pred_laws.distrib_sup_le utp_pred_laws.sup.mono utp_pred_laws.sup_inf_distrib1)
  moreover have "(idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> (active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q) ;; \<U>(true, []))
       \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> (active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; \<U>(true, [])))
      = (((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, []))
       \<or> ((idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, []))
       \<or> ((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, []))
       \<or> ((time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, [])))"
    by (simp add: "101" "102" "103" "104")
  moreover have "(((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, []))
       \<or> ((idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, []))
       \<or> ((time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q)) ;; \<U>(true, []))
       \<or> ((time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)) ;; \<U>(true, [])))
       \<sqsubseteq> (((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
       \<or> (idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
       \<or> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
       \<or> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))) ;; \<U>(true, []))"
    by (simp add: seqr_or_distl)
  ultimately have 11: "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                      \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
                      \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                      \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
                     \<sqsubseteq> (((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                       \<or> (idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
                       \<or> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                       \<or> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))) ;; \<U>(true, []))"
    by (smt (z3) order.trans)

  have "pre\<^sub>R P \<and> pre\<^sub>R Q is TRC"
    by (simp add: "1"(1) "1"(4) TRC_conj)
  moreover have "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)) is TRR"
    by (meson "9"(1) "9"(4) TRR_conj active_TRR_insistant idle_TRR_insistant idle_TRR_stateless tconj_TRR time_TRR time_urgent_TRR trel_theory.disj_is_healthy)
  moreover have "((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
                \<or> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))) is TRF"
    by (simp add: "9"(1) "9"(3) "9"(4) "9"(6) TRF_conj_closure TRF_time_insistant active_TRF idle_TRF_insistant idle_TRF_insistant_end tfin_theory.disj_is_healthy)
  moreover have 13: "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
               \<sqsubseteq> \<U>(true, [])"
    by (meson "42" utp_pred_laws.sup.coboundedI1)
  moreover have "(idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
               \<sqsubseteq> (((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
                \<or> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))) ;; \<U>(true, []))"
    using "11" by blast
  ultimately show "\<^bold>R ((pre\<^sub>R P \<and> pre\<^sub>R Q)
                   \<turnstile> (idle\<^sub>S(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> idle\<^sub>S(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<squnion>\<^sub>t idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)
                \<or> time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q)
                \<or> time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))
                   \<diamondop> (((idle\<^sub>E(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> idle\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (idle\<^sub>E(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> idle\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))
                \<or> (time\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<and> active\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R Q))
                \<or> (time\<^sub>I(pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R Q) \<and> active\<^sub>I(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)))))
                   is TC"
    by (meson "9"(1) "9"(4) TC_intro TRR_conj active_TRR_insistant idle_TRR_insistant idle_TRR_stateless tconj_TRR time_urgent_TRR trel_theory.disj_is_healthy)
qed

lemma
  assumes "P is TRR" "Q is TRR"
  shows "idle\<^sub>S(P) \<squnion>\<^sub>t idle\<^sub>I(P) = idle\<^sub>I(P)"
  apply(trr_auto cls: assms)
  oops

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