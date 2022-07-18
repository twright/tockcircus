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
  apply(rdes_simp simps: tockifyEmpty)
  apply(rel_auto)
  done

lemma "\<forall> X. [oref X] \<in> tttraces Stop"
  apply(rdes_simp simps: tockifyEmpty)
  (*apply(rel_auto)*)
  oops

inductive tockSequence :: "('\<theta> refevent) set \<Rightarrow> '\<theta> oreftrace \<Rightarrow> bool" for X where
tockSequence0: "tockSequence X []"|
tockSequence1: "\<lbrakk>tockSequence X t; Y \<subseteq> X\<rbrakk> \<Longrightarrow> tockSequence X (oref Y # otock # t)"

(*
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
*)

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
    apply(simp_all only: tockify.simps torefset.simps)
    oops
    (*
    apply(metis (no_types, lifting) list.discI list.inject oevent.distinct(1) oevent.inject(1) tockify.elims tockify.simps(2))
    apply(metis list.discI list.inject oevent.distinct(1) oevent.inject(2) tockify.elims(1) tockify.simps(1))
    done
    *)
qed

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

(*
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
*)

subsection \<open> Do \<close>

(*
lemma tocksTockifyFinal: "t \<in> tocks (- {refevt e})
  \<Longrightarrow> \<exists>s. tockify (t @ [Evt e]) = s @ [oevt e] \<and> tockSequence (- {refevt e}) s \<and> (\<exists>X. \<not> refevt e \<in> X)"
  by (metis insert_absorb insert_not_empty tockSeqTocks tockify.simps(1) tockify.simps(3) tockifyAppend)

lemma tocksTockifyFinalTock:
    "tockSequence (- {refevt e}) t
 \<Longrightarrow> \<not> refevt e \<in> X
 \<Longrightarrow> \<exists>ta. t @ [oevt e] = tockify ta \<and> (\<exists>tb. tb \<in> tocks (- {refevt e}) \<and> (\<exists>x. ta = tb @ x \<and> x \<subseteq>\<^sub>t [Evt e]))"
proof -
  assume 1: "tockSequence (- {refevt e}) t"
  assume 2: "\<not> refevt e \<in> X"
  obtain "tc" where 3: "t = tockify tc"
    by (meson tockSequenceTockify "1" image_iff)
  have 3: "t @ [oevt e] = tockify(tc @ [Evt e])"
    by (simp add: "3" tockifyAppend)
  have 4: "tc \<in> tocks (- {refevt e})"
    by (metis "1" "3" append_eq_append_conv tockSeqTocks tockify.simps(1) tockify.simps(3) tockifyAppend)
  show ?thesis
    using "3" "4" tock_ord_refl by auto
qed

lemma tttracesDo: "tttraces (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp)
                 = ( {t . tockSequence (-{refevt e}) t}
                   \<union> { t@[oevt e]
                     | t X . tockSequence (-{refevt e}) t })
                 \<union> {t@[oref X] | t X . tockSequence (-{refevt e}) t
                              \<and> X \<subseteq> (-{refevt e})}
                 \<union> { t@[oevt e, otick]
                   | t X . tockSequence (-{refevt e}) t
                         \<and> X \<subseteq> (-{refevt e})}" (is "?l = ?FE \<union> ?FR \<union> ?TI")
proof (rule tttracesCalc)
  show "tttracesFE (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?FE"
    apply(rdes_simp)
    apply(rel_auto)
    using tockSeqTocks apply blast
    apply (meson tocksTockifyFinal)
    apply (meson tocksTockifyFinal)
    apply (metis image_iff rfnil_mem_dest tockSeqTocks tockSequenceTockify)
    by (meson empty_iff tocksTockifyFinalTock)
next
  show "tttracesFR (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?FR"
    apply(rdes_simp)
    apply(rel_auto)
    using tockSeqTocks apply blast
    by (metis image_iff tockSeqTocks tockSequenceTockify)
next
  show "tttracesTI (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?TI"
    by (rdes_simp; rel_auto; auto simp add: tocksTockifyFinal tocksTockifyFinalTock)
qed

subsection \<open> Sequential composition \<close>

lemma
"true \<sqsubseteq> Q"
  by (rel_simp)

lemma tracesFERefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFE Q \<subseteq> tttracesFE P"
  apply(rdes_simp)
  apply(rel_simp)
  apply(simp add: tockifyEq)
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
  apply(simp_all add: tockifyEq)
  oops

subsection \<open> External choice \<close>

fun oidleprefix :: "'\<phi> oreftrace \<Rightarrow> '\<phi> oreftrace" where
"oidleprefix (oref X # otock # xs) = oref X # otock # oidleprefix xs"|
"oidleprefix xs = []"

lemma oidleprefixTockSequence: "tockSequence UNIV (oidleprefix p)"
proof (induct p rule: oidleprefix.induct)
  case (1 X xs)
  then show ?case
    by (simp add: tockSequence1)
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