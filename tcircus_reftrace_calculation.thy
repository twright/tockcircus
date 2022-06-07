section \<open> Tick Tock CSP Operator Reftrace Calculuation \<close>

theory tcircus_reftrace_calculation
  imports "tockcircus" "tcircus_reftrace_semantics" "UTP.utp_full"
begin

subsection \<open> Div \<close>

lemma tttracesDiv: "tttraces Div = {[]}" (is "tttraces Div = ?r")
proof (rule tttracesEqRem)
  show "tttracesTI Div = ?r \<inter> TI"
    apply(simp add: TI_def)
    apply(rdes_simp)
    done
next
  show "tttracesFR Div = ?r \<inter> FR"
    apply(simp add: FR_def)
    apply(rdes_simp)
    apply(rel_auto)
    done
next
  have "?r - FR - TI = ?r"
    by (auto simp add: FR_def TI_def)
  moreover have "tttracesFE Div = ?r"
    apply(rdes_simp simps: FR_def TI_def)
    apply(rel_auto)
    done
  ultimately show "tttracesFE Div = ?r - FR - TI"
    by auto
qed

subsection \<open> Skip \<close>

lemma tttracesSkip: "tttraces Skip = {[], [otick]}" (is "tttraces Skip = ?r")
proof (rule tttracesEqRem)
  have "?r - FR - TI = {[]}"
    by (auto simp add: FR_def TI_def TTT1_def TTT2_def TTT3_def)
  moreover have "tttracesFE Skip = {[]}"
    apply(rdes_simp)
    apply(rel_auto)
    apply(auto simp add: tockifyEmpty)
    done
  ultimately show "tttracesFE Skip = ?r - FR - TI"
    by auto
next
  show "tttracesTI Skip = ?r \<inter> TI"
    apply(rdes_simp simps: TI_def)
    using TTT1_def TTT2_def TTT3_def apply(rel_auto)
    done
next
  show "tttracesFR Skip = ?r \<inter> FR"
    apply(rdes_simp simps: FR_def)
    apply(rel_auto)
    done
qed

subsection \<open> Untimed Stop \<close>

lemma "tttraces Stop\<^sub>U = {[]} \<union> {[oref X] | X . True}" (is "?l = ET \<union> ?r2")
proof (rule tttracesEqRem)
  have "(ET \<union> ?r2) - FR - TI = ET"
    by (auto simp add: FE_def FR_def TI_def TTT1_def TTT2_def TTT3_def)
  moreover have "tttracesFE Stop\<^sub>U = ET"
    apply(rdes_simp)
    apply(rel_auto)
    done
  ultimately show "tttracesFE Stop\<^sub>U = (ET \<union> ?r2) - FR - TI"
    by auto
next
  have "tttracesFR Stop\<^sub>U = ?r2"
    apply(rdes_simp)
    apply(rel_auto)
    done
  moreover have "(ET \<union> ?r2) \<inter> FR = ?r2"
    by (auto simp add: FR_def TTT1_def TTT2_def TTT3_def)
  ultimately show "tttracesFR Stop\<^sub>U = (ET \<union> ?r2) \<inter> FR"
    by blast
next
  have "tttracesTI Stop\<^sub>U = {}"
    by (rdes_simp; rel_auto)
  moreover have "(ET \<union> ?r2) \<inter> TI = {}"
    by (auto simp add: TI_def)
  ultimately show "tttracesTI Stop\<^sub>U = (ET \<union> ?r2) \<inter> TI"
    by blast
qed

subsection \<open> Timed Stop \<close>

lemma "{[]} \<subseteq> tttraces Stop"
  apply(rdes_simp simps: tockifyEmpty)
  apply(rel_auto)
  done

lemma "\<forall> X. [oref X] \<in> tttraces Stop"
  apply(rdes_simp simps: tockifyEmpty)
  apply(rel_auto)
  done

lemma "tttracesFE Stop = {[]}"
  apply(rdes_simp)
  apply(auto simp add: tockifyEmpty)
  sledgehammer

inductive tockSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" where
tockSequence0: "tockSequence X []"|
tockSequence1: "\<lbrakk>tockSequence X t; Y \<subseteq> X\<rbrakk> \<Longrightarrow> tockSequence X (oref Y # tock # t)"

inductive refSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> reftrace \<Rightarrow> bool" where
refSequence0: "refSequence X []"|
refSequence1: "\<lbrakk>refSequence X t; Y \<subseteq> X\<rbrakk> \<Longrightarrow> refSequence X (iref Y # t)"

lemma refSeqEvents: "refSequence X t \<Longrightarrow> events t = []"
  oops
  \<comment>\<open>
  by (induct rule: refSequence.induct; auto)
  \<close>  

(*
lemma refSeqRefEvents: "tockSequence X t \<Longrightarrow> events (t @ [ref Y]) = []"
  by (induct rule: tockSequence.induct; auto)
*)

lemma stopEvents: "t \<in> untickeds \<Longrightarrow> t \<in> tttraces Stop \<Longrightarrow> oevents t = []"
  apply(auto; rel_simp)
  oops

subsection \<open> Internal Choice \<close>

lemma tockifyEq: "(tockify t = tockify s) = (t = s)"
proof 
  show "t = s \<Longrightarrow> tockify t = tockify s"
    by auto
next
  assume "tockify t = tockify s"
  then show "t = s"
    apply(induct t arbitrary: s)
    apply(auto simp add: tockifyEmpty)
    apply(case_tac "a")
    apply(metis (no_types, lifting) list.discI list.inject oevent.distinct(1) oevent.inject(1) tockify.elims tockify.simps(2))
    apply(metis list.discI list.inject oevent.distinct(1) oevent.inject(2) tockify.elims(1) tockify.simps(1))
    done
qed

lemma tockifyRefRev: "tockify t@[oref X,otock] = tockify (t@[iref X])"
  oops

lemma "tttraces (P \<sqinter> Q) = tttraces P \<union> tttraces Q"
proof (rule tttracesEq)
  show "tttraces P \<union> tttraces Q \<subseteq> TTTs"
    using TTTStructure by blast
next
  have "tttracesFE (P \<sqinter> Q) = tttracesFE P \<union> tttracesFE Q"
    by (auto; rel_simp; simp_all add: tockifyEq; metis)
  thus "tttracesFE (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FE"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(1))
next
  have "tttracesFR (P \<sqinter> Q) = tttracesFR P \<union> tttracesFR Q"
    by (auto; rel_simp; simp_all add: tockifyEq; metis)
  thus "tttracesFR (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FR"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(2))
next
  have "tttracesTI (P \<sqinter> Q) = tttracesTI P \<union> tttracesTI Q"
    by (auto; (rel_auto | rel_simp); auto simp add: tockifyEq)
  thus "tttracesTI (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> TI"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(3))
qed

end