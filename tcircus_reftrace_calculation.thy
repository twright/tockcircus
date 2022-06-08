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

inductive tockSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" for X where
tockSequence0: "tockSequence X []"|
tockSequence1: "\<lbrakk>tockSequence X t; Y \<subseteq> X\<rbrakk> \<Longrightarrow> tockSequence X (oref Y # otock # t)"

lemma tockSeqTocks: "(tockSequence X (tockify t)) = (t \<in> tocks X)"
proof (induct t)
  case Nil
  then show ?case
    by (simp add: tockSequence0)
next
  case (Cons a t)
  then show ?case proof (cases a)
    case (Tock Y)
    then have "(a # t \<in> tocks X) \<Longrightarrow> (tockSequence X (tockify (a # t)))" proof -
      assume 1: "a # t \<in> tocks X"
      then have "Y \<subseteq> X"
        by (simp add: Tock tocks_def)
      moreover have "tockSequence X (tockify t)"
        by (metis "1" Cons.hyps Cons_eq_appendI append_self_conv2 tocks_append)
      ultimately show "tockSequence X (tockify (a # t))"
        by (simp add: Tock tockSequence1)
    qed
    moreover have "(tockSequence X (tockify (a # t))) \<Longrightarrow> (a # t \<in> tocks X)" proof -
      assume 2: "tockSequence X (tockify (a # t))"
      then have "t \<in> tocks X"
        using Tock tockSequence.simps Cons.hyps by auto
      moreover have "Y \<subseteq> X"
        by (metis Tock 2 list.discI list.inject oevent.inject(1) tockSequence.simps tockify.simps(2))
      ultimately show "a # t \<in> tocks X"
        by (simp add: Tock tocks_Cons)
    qed
    ultimately show ?thesis
      by auto
  next
    case (Evt e)
    hence "a # t \<notin> tocks X"
      by simp
    moreover hence "\<not> tockSequence X (tockify (a # t))"
      using Evt tockSequence.simps by auto
    ultimately show "(tockSequence X (tockify (a # t))) = (a # t \<in> tocks X)"
      by blast
  qed
qed

lemma tockSequenceTockify: "tockSequence UNIV t \<Longrightarrow> t \<in> range tockify"
proof (induct t rule: tockSequence.induct)
  case (tockSequence0)
  then show ?case
    by (metis range_eqI tockify.simps(3))
next
  case (tockSequence1 t Y)
    assume 2: "t \<in> range tockify"
    then obtain ta where 3: "t = tockify ta"
      by blast
    have "oref Y # otock # t = tockify (Tock Y # ta)"
      by (simp add: "3")
    then show "oref Y # otock # t \<in> range tockify"
      by blast
  qed

lemma tttracesFEStop: "tttracesFE Stop = {t. tockSequence UNIV t}"
  apply(rdes_simp)
  apply(rel_simp)
  by (metis rangeE tockSeqTocks tockSequenceTockify)

lemma tttracesTIStop: "tttracesTI Stop = {}"
  by (rdes_simp)

definition finalRefTockSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" where
  "finalRefTockSequence X t = (\<exists> ta Y. t = ta @ [oref Y] \<and> Y \<subseteq> X \<and> tockSequence X ta)"

inductive refSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> reftrace \<Rightarrow> bool" where
refSequence0: "refSequence X []"|
refSequence1: "\<lbrakk>refSequence X t; Y \<subseteq> X\<rbrakk> \<Longrightarrow> refSequence X (iref Y # t)"

lemma tttracesFRStop: "tttracesFR Stop = {t. finalRefTockSequence UNIV t}"
  apply(rdes_simp)
  apply(rel_simp)
  apply(simp add: finalRefTockSequence_def)
  by (metis (no_types, hide_lams) rangeE tockSeqTocks tockSequenceTockify)

lemma tttracesStop: "tttraces Stop = {t. tockSequence UNIV t \<or> finalRefTockSequence UNIV t}"
  using tttracesFEStop tttracesFRStop tttracesTIStop tttracesCalc by blast


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


subsection \<open> Wait \<close>

fun otimelength :: "'\<theta> oreftrace \<Rightarrow> nat" where
  "otimelength (otock # xs) = Suc (otimelength xs)" |
  "otimelength (oref X # xs) = otimelength xs" |
  "otimelength (oevt e # xs) = otimelength xs" |
  "otimelength (otick # xs) = otimelength xs" |
  "otimelength [] = 0"

lemma tocksTimeLength: "t \<in> tocks X \<Longrightarrow> otimelength(tockify t) = length t"
proof (induct t)
  case Nil
  then show ?case by auto
next
  case (Cons a t)
  then obtain Y where "a = Tock Y"
    by (metis tev.exhaust tocks_Evt)
  then show ?case
    by (metis Cons.hyps Cons.prems length_Cons list.discI list.inject otimelength.simps(1) otimelength.simps(2) tockSeqTocks tockSequence.simps tockify.simps(2))
qed

lemma tttracesTIWait: "tttracesTI (Wait \<guillemotleft>n\<guillemotright>) = {t@[otick]| t. tockSequence UNIV t \<and> (otimelength t = n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength)
  by (metis rangeE tockSeqTocks tocksTimeLength tockSequenceTockify)

lemma tttracesFRWait: "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = {t@[oref X]| t X. tockSequence UNIV t \<and> (otimelength t < n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength)
  by (metis rangeE tockSeqTocks tocksTimeLength tockSequenceTockify)

lemma tttracesFEWait: "tttracesFE (Wait \<guillemotleft>n\<guillemotright>) = {t| t X. tockSequence UNIV t \<and> (otimelength t \<le> n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength)
  by (metis le_eq_less_or_eq rangeE tockSeqTocks tocksTimeLength tockSequenceTockify)

lemma tockSequenceTTTss: "tockSequence UNIV t \<Longrightarrow> t \<in> TTTss"
  by (meson tockSequenceTockify subsetD tockifyTTTss)

lemma tockSequenceRefTTTs: "tockSequence UNIV t \<Longrightarrow> t@[oref X] \<in> TTTs"
proof -
  assume "tockSequence UNIV t"
  then have "t \<in> TTTss"
    using tockSequenceTTTss by blast
  moreover have "[oref X] \<in> TTTs"
    using TTT1_def TTT2_def TTT3_def by auto
  ultimately show "t@[oref X] \<in> TTTs"
    using TTTsAppend by blast
qed

lemma tockSequenceTickTTTs: "tockSequence UNIV t \<Longrightarrow> t@[otick] \<in> TTTs"
proof -
  assume "tockSequence UNIV t"
  then have "t \<in> TTTss"
    using tockSequenceTTTss by blast
  moreover have "[otick] \<in> TTTs"
    using TTT1_def TTT2_def TTT3_def by auto
  ultimately show "t@[otick] \<in> TTTs"
    using TTTsAppend by blast
qed

lemma tttracesWait: "tttraces (Wait \<guillemotleft>n\<guillemotright>) = {t| t X. tockSequence UNIV t \<and> (otimelength t \<le> n)}
                                         \<union> {t@[oref X]| t X. tockSequence UNIV t \<and> (otimelength t < n)}
                                         \<union> {t@[otick]| t. tockSequence UNIV t \<and> (otimelength t = n)}" (is "?l = ?FE \<union> ?FR \<union> ?TI")
proof (rule tttracesCalc)
  show "tttracesFE (Wait \<guillemotleft>n\<guillemotright>) = ?FE"
    using tttracesFEWait by blast
next
  show "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = ?FR"
    using tttracesFRWait by blast
next
  show "tttracesTI (Wait \<guillemotleft>n\<guillemotright>) = ?TI"
    using tttracesTIWait by blast
qed

end