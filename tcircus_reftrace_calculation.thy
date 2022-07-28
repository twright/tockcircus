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
    by (rel_auto)
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

lemma torefsetRange: "reftick \<notin> X \<Longrightarrow> reftock \<notin> X \<Longrightarrow> \<exists> X'. X = torefset X'"
proof -
  assume 1: "reftick \<notin> X"
  assume 2: "reftock \<notin> X"
  have 3: "\<And>x. x \<in> X \<Longrightarrow> \<exists> e. x=refevt e"
  by (metis "1" "2" fromrefevent.cases)
  obtain X' where 4: "X' = {e | e . refevt e \<in> X}"
    by blast
  have "\<And>x. x \<in> X \<Longrightarrow> x \<in> torefset X'"
    using "3" "4" by auto
  moreover have "\<And>x. x \<in> torefset X' \<Longrightarrow> x \<in> X"
    using "4" by auto
  ultimately show ?thesis
    by auto
qed

lemma torefsetReftick: "reftick \<notin> torefset X"
  by simp

lemma torefsetReftock: "reftock \<notin> torefset X"
  by simp

lemma finalrefsetTick: "reftick \<in> finalrefset p refterm X = refterm"
  by (smt (z3) UnE UnI2 finalrefset.elims insertCI refevent.distinct(5) singletonD torefsetReftick)

lemma finalrefsetTock: "(reftock \<in> finalrefset p refterm X) \<noteq> p"
  by (smt (z3) UnE UnI2 finalrefset.elims insertCI insert_absorb refevent.distinct(5) singleton_insert_inj_eq' torefsetReftock)

lemma finalrefsetRange: "\<exists> X' p refterm. X = finalrefset p refterm X'"
proof -
  have "reftock \<in> X \<Longrightarrow> reftick \<in> X \<Longrightarrow> \<exists> X'. X = finalrefset False True X'"
    apply(simp only: finalrefset.simps)
    by (metis (no_types, lifting) Un_insert_right insert_eq_iff insert_is_Un lattice_class.inf_sup_aci(5) mk_disjoint_insert refevent.distinct(5) torefsetRange)
  moreover have "reftock \<in> X \<Longrightarrow> reftick \<notin> X \<Longrightarrow> \<exists> X'. X = finalrefset False False X'"
    apply(simp only: finalrefset.simps)
    by (metis insertI2 insert_is_Un mk_disjoint_insert semilattice_sup_class.sup_commute torefsetRange)
  moreover have "reftock \<notin> X \<Longrightarrow> reftick \<in> X \<Longrightarrow> \<exists> X'. X = finalrefset True True X'"
    apply(simp only: finalrefset.simps)
    by (metis Un_commute insertCI insert_is_Un mk_disjoint_insert torefsetRange)
  moreover have "reftock \<notin> X \<Longrightarrow> reftick \<notin> X \<Longrightarrow> \<exists> X'. X = finalrefset True False X'"
    apply(simp only: finalrefset.simps)
    using torefsetRange by blast
  ultimately show "?thesis"
    by meson
qed

lemma "tttraces Stop\<^sub>U = {[]} \<union> {[oref X] | X . True}" (is "?l = ET \<union> ?r2")
proof (rule tttracesEqRem)
  have "(ET \<union> ?r2) - FR - TI = ET"
    by (auto simp add: FE_def FR_def TI_def TTT1_def TTT2_def TTT3_def)
  moreover have "tttracesFE Stop\<^sub>U = ET"
    apply(rdes_simp)
    by (rel_auto)
  ultimately show "tttracesFE Stop\<^sub>U = (ET \<union> ?r2) - FR - TI"
    by auto
next
  have "tttracesFR Stop\<^sub>U = ?r2"
    apply(rdes_simp)
    apply(rel_auto)
    by (simp add: finalrefsetRange)
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
  apply(rdes_simp simps: tockificationsEmptyS)
  apply(rel_auto)
  done

lemma "\<forall> X. [oref X] \<in> tttraces Stop"
  apply(rdes_simp simps: tockificationsEmptyS)
  (* apply(rel_auto) *)
  oops

inductive tockSequence :: "('\<theta> event) set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" for X where
tockSequence0: "tockSequence X []"|
tockSequence1: "\<lbrakk>tockSequence X t; Y \<subseteq> torefset X \<union> {reftick}\<rbrakk> \<Longrightarrow> tockSequence X (oref Y # otock # t)"

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
      then have "torefset Y \<subseteq> torefset X \<union> {reftick}"
        by force
      moreover have "tockSequence X (tockify t)"
        by (metis "1" Cons.hyps Cons_eq_appendI append_self_conv2 tocks_append)
      ultimately show "tockSequence X (tockify (a # t))"
        apply(simp only: tockify.simps Tock)
        using tockSequence1 by blast
    qed
    moreover have "(tockSequence X (tockify (a # t))) \<Longrightarrow> (a # t \<in> tocks X)"
    proof -
      assume 2: "tockSequence X (tockify (a # t))"
      have "torefset Y \<subseteq> torefset X \<union> {reftick}"
        by (metis Tock 2 list.discI list.inject oevent.inject(1) tockSequence.simps tockify.simps(2))
      then have "Y \<subseteq> X"
        by (rule torefsetSubsetReftick)
      moreover have "t \<in> tocks X"
        using Tock 2 tockSequence.simps Cons.hyps by auto
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

lemma tockSeqTockificationTocks: "s \<in> tockifications t \<Longrightarrow> (tockSequence X s) = (t \<in> tocks X)"
proof (induct t arbitrary: s)
  case Nil
  then show ?case
    by (simp add: tockSequence0)
next
  case (Cons a t)
  assume 0: "s \<in> tockifications (a # t)"
  then show ?case proof (cases a)
    case (Tock Y)
    obtain s' where 3: "(s = oref (torefset Y) # otock # s' \<or> s = oref (torefset Y \<union> {reftick}) # otock # s') \<and> s' \<in> tockifications t"
      using 0 apply(simp only: Tock tockifications.simps)
      by blast
    then have "(a # t \<in> tocks X) \<Longrightarrow> (tockSequence X s)" proof -
      assume 1: "a # t \<in> tocks X"
      then have "Y \<subseteq> X"
        by (simp add: Tock tocks_def)
      then have "torefset Y \<subseteq> torefset X \<union> {reftick}"
        by force
      moreover have "tockSequence X s'"
        by (metis "1" "3" Cons.hyps Cons_eq_appendI append_self_conv2 tocks_append)
      ultimately show "tockSequence X s"
        using "3" tockSequence1 by fastforce
    qed
    moreover have "(tockSequence X s) \<Longrightarrow> (a # t \<in> tocks X)"
    proof -
      assume 2: "tockSequence X s"
      have "torefset Y \<subseteq> torefset X \<union> {reftick}"
        by (smt (verit) "2" "3" Un_subset_iff list.distinct(1) list.inject oevent.inject(1) tockSequence.simps)
      then have "Y \<subseteq> X"
        by (rule torefsetSubsetReftick)
      moreover have "t \<in> tocks X"
        by (metis 2 tockSequence.simps Cons.hyps "3" list.discI list.sel(3))
      ultimately show "a # t \<in> tocks X"
        by (simp add: Tock tocks_Cons)
    qed
    ultimately show ?thesis
      by auto
  next
    case (Evt e)
    hence "a # t \<notin> tocks X"
      by simp
    moreover hence "\<not> tockSequence X s"
      using 0 Evt tockSequence.simps by auto
    ultimately show "(tockSequence X s) = (a # t \<in> tocks X)"
      by blast
  qed
qed

lemma tockSeqRefEquiv: "refEquiv s t \<Longrightarrow> (tockSequence X s = tockSequence X t)"
  oops

(* No longer true
lemma tockSequenceTockify: "tockSequence X t \<Longrightarrow> t \<in> range tockify"
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
      sledgehammer
    then show "oref Y # otock # t \<in> range tockify"
      by blast
  qed
*)

lemma tockSequenceTockifications: "tockSequence X t \<Longrightarrow> t \<in> \<Union> (range tockifications)"
proof (induct t rule: tockSequence.induct)
  case (tockSequence0)
  then show ?case
    by (simp add: tockificationsEmptyS)
next
  case (tockSequence1 t Y)
  assume 2: "t \<in> \<Union> (range tockifications)"
  then obtain ta where 3: "t \<in> tockifications ta"
    by blast
  obtain Ya where 4: "Y - {reftick} = torefset Ya"
    by (smt (verit, ccfv_threshold) Diff_cancel Diff_iff Un_Diff_cancel Un_absorb Un_commute Un_insert_left insert_absorb insert_iff insert_subset tcircus_reftrace_calculation.torefsetRange tcircus_reftrace_calculation.torefsetReftock tockSequence1.hyps(3))
  have "oref (Y) # otock # t \<in> tockifications (Tock Ya # ta)"
    apply(simp add: 3)
    using 4 by auto
  then show "oref Y # otock # t \<in>  \<Union> (range tockifications)"
    by blast
qed

lemma tttracesFEStop: "tttracesFE Stop = {t. tockSequence UNIV t}"
  apply(rdes_simp)
  apply(rel_simp)
  using tockSequenceTockifications tockSeqTocks tockSeqTockificationTocks by force

lemma tttracesTIStop: "tttracesTI Stop = {}"
  by (rdes_simp)

definition finalRefTockSequence :: "'\<theta> set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" where
  "finalRefTockSequence X t = (\<exists> ta Y Ti. (t = ta @ [oref (torefset Y \<union> Ti)]) \<and> Ti \<subseteq> {reftick, reftock} \<and> Y \<subseteq> X \<and> tockSequence X ta)"

lemma finalrefsetForm: "(\<exists>p refterm. u = s @ [oref (finalrefset p refterm X)])
                      = (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock})"
proof -
  have "(\<exists>p refterm. u = s @ [oref (finalrefset p refterm X)])
      = ( (u = s @ [oref (finalrefset False False X)])
        \<or> (u = s @ [oref (finalrefset False True X)])
        \<or> (u = s @ [oref (finalrefset True False X)])
        \<or> (u = s @ [oref (finalrefset True True X)]) )"
    by (metis (full_types))
  also have "\<dots> = ( (u = s @ [oref (torefset X \<union> {reftock})])
                  \<or> (u = s @ [oref (torefset X \<union> {reftock, reftick})])
                  \<or> (u = s @ [oref (torefset X \<union> {})])
                  \<or> (u = s @ [oref (torefset X \<union> {reftick})]) )"
    by simp
  also have "\<dots> = (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock})"
    by blast
  finally show ?thesis
    by blast
qed

lemma finalRefusalSetForm: "
{(s::'\<theta> oreftrace) @ [oref (finalrefset p refterm X)] | t X p refterm s . t \<in> tocks UNIV \<and> s \<in> tockifications t}
           = {s @ [oref (torefset X \<union> Ti)] | X s Ti .
              Ti \<subseteq> {reftick, reftock} \<and> tockSequence UNIV s}
"
proof -
  {
    fix u
    have "(\<exists> t X p refterm s.
          (u::'\<theta> oreftrace) = s @ [oref (finalrefset p refterm X)] \<and> t \<in> tocks UNIV \<and> s \<in> tockifications t)
        = (\<exists> t X s. (\<exists> p refterm.
           u = s @ [oref (finalrefset p refterm X)]) \<and> t \<in> tocks UNIV \<and> s \<in> tockifications t)"
      by metis
    also have "\<dots> = (\<exists> t X s. (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock})
                            \<and> t \<in> tocks UNIV \<and> s \<in> tockifications t)"
      by (simp add: finalrefsetForm)
    also have "\<dots> = (\<exists> t X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock}
                              \<and> t \<in> tocks UNIV \<and> s \<in> tockifications t)"
      by metis
    also have "\<dots> = (\<exists> X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock}
                              \<and> (\<exists> t. t \<in> tocks UNIV \<and> s \<in> tockifications t))"
      by metis
    also have "\<dots> = (\<exists> X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock}
                            \<and> tockSequence UNIV s)"
      by (metis UN_iff tockSequenceTockifications tockSeqTockificationTocks)
    finally have "(\<exists> t X p refterm s.
          u = s @ [oref (finalrefset p refterm X)] \<and> t \<in> tocks UNIV \<and> s \<in> tockifications t)
      = (\<exists> X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick, reftock}
                              \<and> tockSequence UNIV s)" 
      by blast
  }
  thus ?thesis by simp
qed

lemma tttracesFRStop: "tttracesFR Stop = {t::'\<theta> oreftrace. finalRefTockSequence UNIV t}"
  by (rdes_simp; rel_simp)
     (auto simp add: finalRefTockSequence_def finalRefusalSetForm)

lemma tttracesStop: "tttraces Stop = {t. tockSequence UNIV t \<or> finalRefTockSequence UNIV t}"
  using tttracesFEStop tttracesFRStop tttracesTIStop tttracesCalc by blast

subsection \<open> Internal Choice \<close>

(*
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
*)

subsection \<open> Wait \<close>

fun otimelength :: "'\<theta> oreftrace \<Rightarrow> nat" where
  "otimelength (otock # xs) = Suc (otimelength xs)" |
  "otimelength (oref X # xs) = otimelength xs" |
  "otimelength (oevt e # xs) = otimelength xs" |
  "otimelength (otick # xs) = otimelength xs" |
  "otimelength [] = 0"

lemma tocksTimeLength: "t \<in> tocks X \<Longrightarrow> s \<in> tockifications t \<Longrightarrow> otimelength s = length t"
proof (induct t arbitrary: s)
  case Nil
  then show ?case by auto
next
  case (Cons a t)
  assume 1: "s \<in> tockifications (a # t)"
  obtain Y where 2: "a = Tock Y"
    using Cons by (metis tev.exhaust tocks_Evt)
  then obtain s' Z where "s = oref Z # otock # s' \<and> s' \<in> tockifications t"
    using Cons by auto
  then show ?case
    by (metis "2" Cons.hyps Cons.prems(1) length_Cons list.distinct(1) list.sel(3) otimelength.simps(1) otimelength.simps(2) tockSeqTocks tockSequence.simps tockify.simps(2))
qed

lemma tttracesTIWait: "tttracesTI (Wait \<guillemotleft>n\<guillemotright>) = {t@[otick]| t. tockSequence UNIV t \<and> (otimelength t = n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength rangeE tockSequenceTockifications tockSeqTockificationTocks)
  by (metis UN_iff tockSeqTockificationTocks tockSequenceTockifications tocksTimeLength)

lemma tttracesFRWait: "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = {t@[oref X]| t X. tockSequence UNIV t \<and> (otimelength t < n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength tockSeqTockificationTocks finalrefsetRange)
  by (metis UN_iff tockSeqTockificationTocks tockSequenceTockifications tocksTimeLength)

lemma tttracesFEWait: "tttracesFE (Wait \<guillemotleft>n\<guillemotright>) = {t| t X. tockSequence UNIV t \<and> (otimelength t \<le> n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tockSeqTocks tocksTimeLength tockSeqTockificationTocks finalrefsetRange)
  by (metis UN_iff le_eq_less_or_eq tockSeqTockificationTocks tockSequenceTockifications tocksTimeLength)

lemma tockSequenceTTTss: "tockSequence UNIV t \<Longrightarrow> t \<in> TTTss"
  by (meson subset_eq tockSequenceTockifications tockificationsTTTss)

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

subsection \<open> Do \<close>

lemma tocksTockificationsFinal:
  assumes "s \<in> (tockifications (w @ [Evt e]))" and "w \<in> tocks (- {e})"
  shows "\<exists>t. (s = t @ [oevt e]) \<and> tockSequence (- {e}) t"
  using assms(1) apply(simp add: tockificationsAppend)
  using assms(2) using tockSeqTockificationTocks by auto

lemma tocksTockificationsFinalTock:
    "tockSequence (- {e}) t
 \<Longrightarrow> \<exists>ta. t @ [oevt e] \<in> tockifications ta \<and> (\<exists>tb. tb \<in> tocks (- {e}) \<and> (\<exists>x. ta = tb @ x \<and> x \<subseteq>\<^sub>t [Evt e]))"
proof -
  assume 1: "tockSequence (- {e}) t"
  obtain "tc" where 3: "t \<in> tockifications tc"
    using "1" tockSequenceTockifications by auto
  have "t @ [oevt e] \<in> tockifications (tc @ [Evt e])"
    by (simp add: "3" tockificationsAppend)
  moreover have "tc \<in> tocks (- {e})"
    using 1 3 by (simp add: tockSeqTockificationTocks)
  ultimately show ?thesis
    using tock_ord_refl by auto
qed

lemma refevtInFinalrefset: "(refevt e \<in> finalrefset p refterm X) = (e \<in> X)"
  by (cases p; cases refterm; auto)

lemma tttracesDo: "tttraces (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp)
                 = ( {t . tockSequence (-{e}) t}
                   \<union> { t@[oevt e]
                     | t. tockSequence (-{e}) t })
                 \<union> {t@[oref X] | t X . tockSequence (-{e}) t
                              \<and> X \<subseteq> (-{refevt e})}
                 \<union> { t@[oevt e, otick]
                   | t. tockSequence (-{e}) t }" (is "?l = ?FE \<union> ?FR \<union> ?TI")
proof (rule tttracesCalc)
  show "tttracesFE (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?FE"
    apply(rdes_simp)
    apply(rel_auto)
    apply (meson tockSeqTockificationTocks)
    apply (meson tocksTockificationsFinal)
    apply (meson tocksTockificationsFinal)
    apply (metis UN_iff rmember.simps(1) tockSeqTockificationTocks tockSequenceTockifications)
    by (meson tocksTockificationsFinalTock)
next
  show "tttracesFR (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?FR"
    apply(rdes_simp)
    apply(rel_auto)
    using tockSeqTockificationTocks apply blast
    apply (simp add: refevtInFinalrefset)
    by (metis UN_iff finalrefsetRange refevtInFinalrefset tockSeqTockificationTocks tockSequenceTockifications)
next
  show "tttracesTI (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?TI"
    apply (rdes_simp; rel_auto)
    apply (simp add: tocksTockificationsFinal)
    by (meson tocksTockificationsFinalTock)
qed


subsection \<open> Sequential composition \<close>

lemma
"true \<sqsubseteq> Q"
  by (rel_simp)

lemma tracesFERefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFE Q \<subseteq> tttracesFE P"
  apply(rdes_simp)
  apply(rel_simp)
  by blast

lemma tockifySetEq: "({tockify t| t. P} = {tockify t| t. Q}) = ({t. P} = {t. Q})"
  by (auto)

lemma "tttracesFE P \<subseteq> tttracesFE (P ;; Q)"
  oops

lemma "tttracesTI (P ;; Q) = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q}"
  apply(rdes_simp)
  apply(rel_auto)
  oops
  

lemma "tttraces (P ;; Q) = tttracesFE P \<union> tttracesFR Q
    \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttraces Q}"
  apply(rdes_simp)
  apply(rel_auto)
  oops

subsection \<open> External choice \<close>

fun oidleprefix :: "'\<phi> oreftrace \<Rightarrow> '\<phi> oreftrace" where
"oidleprefix (oref X # otock # xs) = oref X # otock # oidleprefix xs"|
"oidleprefix xs = []"

(* Needs some healthiness conditions on p
lemma oidleprefixTockSequence: "tockSequence UNIV (oidleprefix p)"
proof (induct p rule: oidleprefix.induct)
  case (1 X xs)
  have b: "X \<subseteq> torefset UNIV \<union> {reftick}"
    oops
  then show ?case
    apply simp
    apply (simp add: tockSequence1)
next
  case "2_1"
  then show ?case
    by (simp add: tockSequence0)
next
  case ("2_2" vb va)
  then show ?case
    by (simp add: tockSequence0)
next
  case ("2_3" va)
  then show ?case
    by (simp add: tockSequence0)
next
  case ("2_4" va)
  then show ?case
    by (simp add: tockSequence0)
next
  case ("2_5" v)
  then show ?case
    by (simp add: tockSequence0)
next
  case ("2_6" v vd vc)
  then show ?case 
    by (simp add: tockSequence0)
next
case ("2_7" v vd vc)
  then show ?case 
    by (simp add: tockSequence0)
next
  case ("2_8" v vc)
  then show ?case 
    by (simp add: tockSequence0)
qed

lemma "(r = (oidleprefix p :: '\<phi> oreftrace)) = ((tockSequence UNIV r) \<and> (\<forall> r2 . (tockSequence UNIV r2 \<and> r2 \<le> r @ p) \<longrightarrow> r2 \<le> r))"
proof 
  assume 1: "r = oidleprefix p"
  have "tockSequence UNIV r"
    using 1 oidleprefixTockSequence by auto
  {
    fix r2 :: "'\<phi> oreftrace"
    assume "r2 \<le> r @ p"
    then have "tockSequence UNIV r2 \<Longrightarrow> r2 \<le> r"
    proof (induction rule: tockSequence.induct)
    qed
  }
  then have "\<forall> r2 . (tockSequence UNIV r2 \<and> r2 \<le> r @ p) \<longrightarrow> r2 \<le> r"
    by auto
qed
*)
end