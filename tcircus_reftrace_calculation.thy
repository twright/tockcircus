section \<open> Tick Tock CSP Operator Reftrace Calculuation \<close>

theory tcircus_reftrace_calculation
  imports "tockcircus" "tcircus_laws" "tcircus_reftrace_semantics" "UTP.utp_full"
begin


subsection \<open> Div \<close>

lemma tttracesDiv: "tttraces Div = {[]}" (is "tttraces Div = ?r")
proof (rule tttracesEqRem)
  show "tttracesTI Div = ?r \<inter> TI"
    by (rdes_simp simps: TI_def)
next
  show "tttracesFR Div = ?r \<inter> FR"
    by (rdes_simp simps: FR_def; rel_auto)
next
  have "?r - FR - TI = ?r"
    by (auto simp add: FR_def TI_def)
  moreover have "tttracesFE Div = ?r"
    by (rdes_simp simps: FR_def TI_def; rel_auto)
  ultimately show "tttracesFE Div = ?r - FR - TI"
    by auto
qed


subsection \<open> Skip \<close>

lemma tttracesSkip: "tttraces Skip = {[], [otick]}" (is "tttraces Skip = ?r")
proof (rule tttracesEqRem)
  have "?r - FR - TI = {[]}"
    by (auto simp add: FR_def TI_def TTT1_def TTT2_def TTT3_def)
  moreover have "tttracesFE Skip = {[]}"
    by (rdes_simp; rel_auto)
  ultimately show "tttracesFE Skip = ?r - FR - TI"
    by auto
next
  show "tttracesTI Skip = ?r \<inter> TI"
    apply(rdes_simp simps: TI_def)
    using TTT1_def TTT2_def TTT3_def by (rel_auto)
next
  show "tttracesFR Skip = ?r \<inter> FR"
    by (rdes_simp simps: FR_def; rel_auto)
qed


subsection \<open> Untimed Stop \<close>

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
    by (smt (verit, ccfv_threshold) Diff_cancel Diff_iff Un_Diff_cancel Un_absorb Un_commute Un_insert_left insert_absorb insert_iff insert_subset torefsetRange torefsetReftock tockSequence1.hyps(3))
  have "oref (Y) # otock # t \<in> tockifications (Tock Ya # ta)"
    apply(simp add: 3)
    using 4 by auto
  then show "oref Y # otock # t \<in>  \<Union> (range tockifications)"
    by blast
qed

lemma tttracesFEStop: "tttracesFE Stop = {t. tockSequence UNIV t}"
  apply(rdes_simp)
  apply(rel_simp)
  using tockSequenceTockifications tockSeqTockificationTocks by force

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

lemma "tttraces (P \<sqinter> Q) = tttraces P \<union> tttraces Q"
proof (rule tttracesEq)
  show "tttraces P \<union> tttraces Q \<subseteq> TTTs"
    using TTTStructure by blast
next
  have "tttracesFE (P \<sqinter> Q) = tttracesFE P \<union> tttracesFE Q"
    by (auto; rel_simp; blast)
  thus "tttracesFE (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FE"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(1))
next
  have "tttracesFR (P \<sqinter> Q) = tttracesFR P \<union> tttracesFR Q"
    by (auto; rel_simp; blast)
  thus "tttracesFR (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FR"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(2))
next
  have "tttracesTI (P \<sqinter> Q) = tttracesTI P \<union> tttracesTI Q"
    by (auto; rel_simp; blast)
  thus "tttracesTI (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> TI"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(3))
qed


subsection \<open> Conjunction \<close>

lemma finalrefsetInjective: "(finalrefset p refterm X = finalrefset p' refterm' X')
                           = ((p = p') \<and> (refterm = refterm') \<and> (X = X'))"
  by (cases p; cases p'; cases refterm; cases refterm'; auto)


lemma tttracesFERefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFE Q \<subseteq> tttracesFE P"
  apply(rdes_simp)
  apply(rel_simp)
  by blast

lemma tttracesFRRefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFR Q \<subseteq> tttracesFR P"
  apply(rdes_simp)
  apply(rel_simp)
  by blast

lemma tttracesTIRefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesTI Q \<subseteq> tttracesTI P"
  apply(rdes_simp)
  apply(rel_simp)
  by blast

lemma tttracesRefine: "P \<sqsubseteq> Q \<Longrightarrow> tttraces Q \<subseteq> tttraces P"
  by (metis semilattice_inf_class.le_inf_iff tttracesFERefine tttracesFRRefine tttracesSubregions(1) tttracesSubregions(2) tttracesSubregions(3) tttracesSubset tttracesTIRefine)

lemma "tttraces (P \<squnion> Q) \<subseteq> tttraces P"
  by (meson semilattice_inf_class.inf.cobounded1 tttracesRefine)

(* A contradiction to conjunctivity for a nasty process *)

lemma "{[], [oevt 1], [oevt 2]} \<subseteq> tttraces (U(((&tt = [Evt 1] \<or> &tt = []) \<triangleleft> $pat \<triangleright> (&tt = [Evt 2] \<or> &tt = [])) \<and> ($ref = rfnil)))"
  apply(rdes_simp)
  apply(rel_simp)
  apply(auto)
  using tockificationsEmptyS apply blast
  using tockificationsEmptyS apply fastforce
  by force

lemma "{[], [oevt 1], [oevt 2]} \<subseteq> tttraces (U(((&tt = [Evt 1] \<or> &tt = []) \<triangleleft> \<not>$pat \<triangleright> (&tt = [Evt 2] \<or> &tt = [])) \<and> ($ref = rfnil)))"
  apply(rdes_simp)
  apply(rel_simp)
  apply(auto)
  apply(force)
  apply fastforce
  by (metis (mono_tags, lifting) mem_Collect_eq tockifications.simps(1) tockificationsEmptyS)

lemma "(U(((&tt = [Evt 1] \<or> &tt = []) \<triangleleft> $pat \<triangleright> (&tt = [Evt 2] \<or> &tt = [])) \<and> ($ref = rfnil) \<and> (((&tt = [Evt 1] \<or> &tt = []) \<triangleleft> \<not>$pat \<triangleright> (&tt = [Evt 2] \<or> &tt = [])) \<and> ($ref = rfnil)))::nat ttcsp) = U($ref = rfnil \<and> &tt = [])"
  by (rel_auto)

lemma "[oevt 1] \<notin> tttraces (U($ref = rfnil \<and> &tt = []))"
  by (rdes_simp; rel_auto)

(* This law does not make sense even ignoring $pat, in cases
   when processes can perform the same trace on different
   branches. *)

(*
lemma "tttraces (P \<squnion> Q) = tttraces P \<inter> tttraces Q"
proof 
  have "P \<sqsubseteq> P \<squnion> Q" and "Q \<sqsubseteq> P \<squnion> Q"
    by simp_all
  then have "tttraces (P \<squnion> Q) \<subseteq> tttraces P" and "tttraces (P \<squnion> Q) \<subseteq> tttraces Q"
    by (meson tttracesRefine)+
  thus "tttraces (P \<squnion> Q) \<subseteq> tttraces P \<inter> tttraces Q"
    by blast
  {
    fix t
    assume 1: "t \<in> tttracesFE P \<inter> tttracesFE Q"
    have "t \<in> tttracesFE P"
      using 1 by blast
    then obtain s where 2: "t \<in> tockifications s" and 3: "\<not>`(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      by auto
    have "t \<in> tttracesFE Q"
      using 1 by blast
    then obtain s' where 4: "t \<in> tockifications s'" and 5: "\<not>`(\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>s'\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      by auto
    have "s = s'"
      using 2 4 by (meson tockificationsDisjoint)
    then have "\<not>`(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`" and "\<not>`(\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      using 3 5 by blast+
    then have "\<not>( `(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk>
                \<or>  (\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>s\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` )"
      apply(rdes_simp)
      apply(rel_auto)
      nitpick
  }
  have "tttracesFE P \<inter> tttracesFE Q \<subseteq> tttracesFE (P \<squnion> Q)"
    apply(rdes_simp; rel_auto)
    oops
  have "tttracesFR P \<inter> tttracesFR Q \<subseteq> tttracesFR (P \<squnion> Q)"
    apply(rdes_simp; rel_simp)
    apply(simp add: finalrefsetInjective)
    oops
  have "tttracesTI P \<inter> tttracesFE Q \<subseteq> tttracesTI (P \<squnion> Q)"
    apply(rdes_simp; rel_auto)
    apply (metis basic_trans_rules(31) in_set_conv_decomp mem_Collect_eq tockificationsUnticked)
    by (meson UNIV_I UN_iff tockificationsNoTI)
  show "tttraces P \<inter> tttraces Q \<subseteq> tttraces (P \<squnion> Q)"
    apply(rdes_simp; rel_auto)
    oops
qed *)

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
  assume 1: "(a # t) \<in> tocks X"
  assume 2: "s \<in> tockifications (a # t)"
  obtain Y where 3: "a = Tock Y"
    using Cons by (metis tev.exhaust tocks_Evt)
  then obtain s' Z where 4: "s = oref Z # otock # s'" and 5: "s' \<in> tockifications t"
    using Cons by auto
  have "otimelength s' = length t"
    by (metis 1 5 Cons.hyps "2" "4" list.distinct(1) list.sel(3) tockSeqTockificationTocks tockSequence.simps) 
  then show ?case
    by (simp add: "4")
qed

lemma tttracesTIWait: "tttracesTI (Wait \<guillemotleft>n\<guillemotright>) = {t@[otick]| t. tockSequence UNIV t \<and> (otimelength t = n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tocksTimeLength rangeE tockSequenceTockifications tockSeqTockificationTocks)
  by (metis UN_iff tockSeqTockificationTocks tockSequenceTockifications tocksTimeLength)

lemma tttracesFRWait: "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = {t@[oref X]| t X. tockSequence UNIV t \<and> (otimelength t < n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tocksTimeLength tockSeqTockificationTocks finalrefsetRange)
  by (metis UN_iff tockSeqTockificationTocks tockSequenceTockifications tocksTimeLength)

lemma tttracesFEWait: "tttracesFE (Wait \<guillemotleft>n\<guillemotright>) = {t| t X. tockSequence UNIV t \<and> (otimelength t \<le> n)}"
  apply(rdes_simp)
  apply(rel_auto)
  apply(simp_all add: tocksTimeLength tockSeqTockificationTocks finalrefsetRange)
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

lemma "tttracesTI (Q) = {t@s| t s. t@[otick] \<in> tttracesTI II \<and> s \<in> tttracesTI Q}"
  apply(simp)
  apply(rdes_simp) 
  by (rel_auto)

lemma "tttracesTI (Q) = {t@s| t s. t@[otick] \<in> tttracesTI Q \<and> s \<in> tttracesTI II}"
  apply(simp)
  apply(rdes_simp)
  apply(rel_auto)
  apply blast
  by blast

(* Healthiness conditions probably required here! *)
lemma "tttracesTI (P ;; Q) = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q}"
  apply(rdes_simp)
  apply(rel_auto)
  oops


(* It should be possible to generalize this to tick-tock reactive
 * contracts since in this case we can conclude that post\<^sub>R is TRF *)

lemma TRFtttracesTI:
  assumes "P is TRF"
  shows "tttracesTI P = { s @ [otick] | t s .
     `P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$tr,$tr\<acute>,$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>`
               \<and> s \<in> tockifications t}"
  apply(subst (1 9) TRFconcretify)
  apply(simp_all add: assms)
  apply(pred_auto)
  done

(*
lemma TRRtttracesTI:
  assumes "P is TRR"
  shows "tttracesTI P = { s @ [otick] | t s .
     \<not>`\<not>P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>/$tr,$tr\<acute>,$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>`
               \<and> s \<in> tockifications t}"
  apply(subst (8 1) TRRconcretify)
  apply(simp_all add: assms)
  apply(rel_auto)
  sledgehammer
  done
*)

lemma tttracesTITRFSeq:
  assumes "P is TRF" "Q is TRF"
  shows "tttracesTI (P ;; Q) = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q}"
proof -
  have 1: "(P ;; Q) is TRF"
    by (metis (no_types, lifting) Healthy_if Healthy_intro RA1 TRF_def TRF_implies_TRR TRR3_def TRR_closed_seq assms)
  show ?thesis
    apply(simp only: assms 1 TRFtttracesTI)
    apply(simp only: assms TRFTRRSeqExpandTr TRF_implies_TRR)
    apply(rel_auto)
    apply(simp add: tockificationsAppend)
    using append.assoc apply blast
    using tockificationsAppend apply fastforce
    done
qed

(*
lemma "tttracesTI P = tttracesTI ($ref\<acute> =\<^sub>u \<guillemotleft>rfnil\<guillemotright> \<and> \<not>$pat\<acute> \<and> P)"
  apply(rdes_simp)
  apply(pred_auto)
  sledgehammer
*)

(*
Such a result should not be necessary since post\<^sub>R *should* be TRF for TT healthy processes
lemma tttracesTITRFTRRSeq:
  assumes "P is TRF" "Q is TRR"
  shows "tttracesTI (P ;; Q) = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q}"
proof -
  have 1: "(P ;; Q) is TRR"
    by (simp add: TRF_implies_TRR TRR_closed_seq assms)
  show ?thesis
    apply(simp only: assms 1 TRFtttracesTI)
    apply(simp only: assms TRFSeqExpandTr)
    apply(rel_auto)
    apply(simp add: tockificationsAppend)
    using append.assoc apply blast
    using tockificationsAppend apply fastforce
    done
qed
*)

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