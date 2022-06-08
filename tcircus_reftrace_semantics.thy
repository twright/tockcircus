section \<open> Tick Tock CSP UTP Semantics \<close>

theory tcircus_reftrace_semantics
  imports "tcircus_rel" "/home/isabelle/utp-main/theories/rcircus/Refusal_Tests" "UTP.utp_full"
begin

subsection \<open> Refusal trace functions \<close>

fun tooutput :: "'\<theta> reftrace \<Rightarrow> '\<theta> oreftrace" where
"tooutput (Evt e # ts) = oevt e # tooutput ts"|
"tooutput (Tock X # ts) = otock # tooutput ts"|
"tooutput []           = []"

fun tockify :: "'\<theta> reftrace \<Rightarrow> '\<theta> oreftrace" where
"tockify (Evt e # ts) = oevt e # tockify ts"|
"tockify (Tock X # ts) = oref X # otock # tockify ts"|
"tockify []           = []"

lemma tockifyAppend: "tockify(t @ s) = tockify t @ tockify s"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by (cases a; auto)
qed

subsection \<open> Traces \<close>

fun traces :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"traces P = { tooutput t | t . \<not>`\<not>P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,true,false,true/$tr,$tr\<acute>,$ok,$wait,$ok\<acute>\<rbrakk>` }"
(* `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` *)

abbreviation "ET \<equiv> {[]}"

subsection \<open> Refusal Traces \<close>

\<comment>\<open> Need to introduce some final refusals: what is the rule here? \<close>
fun tttracesFE :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFE P = { tockify t | t.
                  \<not>`(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` }"
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { tockify t@[oref X] | t X.
                  \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>` }"
fun tttracesTI :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesTI P = { tockify t @ [otick] | t .
                  \<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` }"
fun tttraces :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttraces P = tttracesFE P \<union> tttracesFR P \<union> tttracesTI P"

lemma tttracesSubset:
  assumes "tttracesFE P \<subseteq> B"
      and "tttracesFR P \<subseteq> B"
      and "tttracesTI P \<subseteq> B"
    shows "tttraces P \<subseteq> B"
  using assms insert_subsetI by auto

subsubsection \<open> Structural Conditions \<close>

definition TTT1 :: "('\<theta> oreftrace) set" where
"TTT1 = { t. \<forall> i::nat . Suc i < length t \<longrightarrow> t ! i \<noteq> otick}"
definition TTT1s :: "('\<theta> oreftrace) set" where
"TTT1s = { t. \<forall> i::nat . Suc i \<le> length t \<longrightarrow> t ! i \<noteq> otick}"

definition TTT2 :: "('\<theta> oreftrace) set" where
"TTT2 = { t . \<forall> i::nat. Suc i < length t \<and> t ! i \<in> range oref \<longrightarrow> t ! (i + 1) = otock}"

definition TTT2s :: "('\<theta> oreftrace) set" where
"TTT2s = { t . \<forall> i::nat. i < length t \<and> t ! i \<in> range oref \<longrightarrow> Suc i < length t \<and> t ! (i + 1) = otock}"
definition TTT3 :: "('\<theta> oreftrace) set" where
"TTT3 = { t . \<forall> i::nat. i < length t \<and> t ! i = otock \<longrightarrow> i > 0 \<and> t ! (i - 1) \<in> range oref}"

abbreviation "TTTs \<equiv> TTT1 \<inter> TTT2 \<inter> TTT3"

abbreviation "TTTss \<equiv> TTT1s \<inter> TTT2s \<inter> TTT3"

subsubsection \<open> Designated Subsets \<close>

abbreviation untickeds :: "('\<theta> oreftrace) set" where
"untickeds \<equiv> {t::'\<theta> oreftrace. otick \<notin> set t}"
abbreviation tickeds :: "('\<theta> oreftrace) set" where
"tickeds \<equiv> {t@[otick] | t. t \<in> untickeds}"

lemma tickedsUntickedsDisj: "untickeds \<inter> tickeds = {}"
  by auto

lemma emptyTTTs: "ET \<subseteq> TTTs"
  by (simp add: TTT1_def TTT2_def TTT3_def)

definition "FR \<equiv> {t@[oref X] | t X  . True} \<inter> TTTs"
definition "TI \<equiv> {t@[otick] | t . True} \<inter> TTTs"
definition "FE \<equiv> TTTs - (FR \<union> TI)"

subsubsection \<open> General Relationships \<close>

lemma distinctRegions:
  shows "ET \<inter> FR = {}"
    and "ET \<inter> TI = {}"
    and "FE \<inter> FR = {}"
    and "FE \<inter> TI = {}"
    and "FR \<inter> TI = {}"
  by (auto simp add: FE_def FR_def TI_def emptyTTTs)

lemma emptyFE: "ET \<subseteq> FE"
  apply (simp add: FE_def FR_def TI_def)
  using emptyTTTs by blast

lemma disjointRegions: "\<lbrakk> A \<in> {FE, FR, TI}; B \<in> {FE, FR, TI}; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
proof -
  assume "A \<in> {FE, FR, TI}"
  moreover assume "B \<in> {FE, FR, TI}"
  moreover assume "\<not> A = B"
  ultimately consider
      "A = FE \<and> B = FR"
    | "A = FE \<and> B = TI"
    | "A = FR \<and> B = FE"
    | "A = FR \<and> B = TI"
    | "A = TI \<and> B = FE"
    | "A = TI \<and> B = FR"
    by auto
  then show "A \<inter> B = {}"
    apply (cases)
    by (auto simp add: FE_def FR_def TI_def)
qed

lemma coveringRegions: "(TTTs::'\<theta> oreftrace set) = FE \<union> FR \<union> TI" (is "TTTs = ?regions")
  by (auto simp add: FE_def FR_def TI_def TTT1_def TTT2_def TTT3_def)

lemma TTT1TickedOrUnticked: "TTT1 = tickeds \<union> untickeds"
proof -
  have "TTT1 \<subseteq> tickeds \<union> untickeds"
    apply (auto simp add: TTT1_def in_set_conv_nth)
    by (metis Suc_inject Suc_lessI hd_drop_conv_nth length_append_singleton less_trans_Suc not_less nth_take take_all take_hd_drop) 
  moreover have "untickeds \<subseteq> TTT1"
    by (auto simp add: TTT1_def in_set_conv_nth)
  moreover have "tickeds \<subseteq> TTT1"
    by (auto simp add: TTT1_def in_set_conv_nth nth_append)
  ultimately show ?thesis by blast
qed

lemma untickedTTT1: "A \<subseteq> TTT1 \<Longrightarrow> A \<inter> tickeds = {} \<Longrightarrow> A \<subseteq> untickeds"
  by (auto simp add: TTT1TickedOrUnticked)

lemma untickedSets: "A \<in> {ET, FE, FR} \<Longrightarrow> A \<subseteq> untickeds"
proof -
  assume "A \<in> {ET, FE, FR}"
  then consider (AET) "A = ET" | (AFE) "A = FE" | (AFR) "A = FR"
    by  auto
  then show "A \<subseteq> untickeds" proof (cases)
    case AET
    then show ?thesis
      by auto
  next
    case AFE
    have "A \<subseteq> TTT1"
      by (auto simp add: AFE FE_def)
    moreover have "A \<inter> tickeds = {}"
      by (auto simp add: AFE FE_def FR_def TI_def TTT3_def)
    ultimately show "A \<subseteq> untickeds"
      by (rule untickedTTT1) 
  next
    case AFR
    have "A \<subseteq> TTT1"
      by (auto simp add: AFR FR_def)
    moreover have "A \<inter> tickeds = {}"
      by (auto simp add: AFR FR_def TTT3_def)
    ultimately show "A \<subseteq> untickeds"
      by (rule untickedTTT1)
  qed
qed


subsubsection \<open> Refusal Trace Structure \<close>

lemma tockifyEmpty: "([] = tockify t) = (t = [])"
  by (metis list.distinct(1) tockify.elims)

lemma tockifyUnticked: "range tockify \<subseteq> (untickeds::'\<theta> oreftrace set)"
proof -
  {
    fix t 
    have "tockify t \<in> (untickeds::'\<theta> oreftrace set)" proof (induct t)
      case Nil
      thus ?case by simp
    next
      case (Cons a ts)
      thus ?case by (cases a; simp_all)
    qed
  }
  thus ?thesis by blast
qed

lemma TTT1sUnticked: "TTT1s = untickeds"
  by (simp add: Suc_le_eq in_set_conv_nth TTT1s_def)

lemma tockifyTTT1s: "range tockify \<subseteq> TTT1s"
  using TTT1sUnticked tockifyUnticked by blast

lemma tockifyTTT1: "range tockify \<subseteq> TTT1"
  using tockifyUnticked TTT1TickedOrUnticked by blast

lemma tttracesFETockify: "tttracesFE P \<subseteq> range tockify"
  by auto

lemma tockifyTicked: "tockify t@[otick] \<in> tickeds"
  using tockifyUnticked by auto

lemma TTT1sAppend: "t \<in> TTT1s \<Longrightarrow> s \<in> TTT1 \<Longrightarrow> t@s \<in> TTT1"
  by (simp add: TTT1s_def TTT1_def nth_append)

lemma tttracesFETTT1: "tttracesFE P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  using tttracesFETockify tockifyTTT1 by auto

lemma tttracesFRTTT1: "tttracesFR P \<subseteq> (TTT1::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t X where "x = tockify t@[oref X]"
    by auto
  then show "x \<in> TTT1"
    by (simp add: TTT1_def;
        metis mem_Collect_eq nth_append nth_mem rangeI subset_eq tockifyUnticked)
qed

lemma tttracesTITTT1: "tttracesTI P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  apply(simp add: TTT1_def)
  by (smt Collect_mono TTT1TickedOrUnticked TTT1_def UnCI mem_Collect_eq tockifyTicked)

lemma tttracesTTT1: "tttraces P \<subseteq> TTT1"
  by (rule tttracesSubset; auto simp only: tttracesFETTT1 tttracesFRTTT1 tttracesTITTT1)

lemma TTT2sStronger: "TTT2s \<subseteq> TTT2"
  by (simp add: Collect_mono TTT2_def TTT2s_def)

lemma TTT2sAppend: "t \<in> TTT2s \<Longrightarrow> s \<in> TTT2 \<Longrightarrow> t @ s \<in> TTT2"
  apply(auto simp add: TTT2_def TTT2s_def)
  by (smt Suc_diff_Suc diff_Suc_Suc linordered_semidom_class.add_diff_inverse nat_add_left_cancel_less not_less_eq not_less_iff_gr_or_eq nth_append range_eqI)

lemma tockifyTTT2s: "range tockify \<subseteq> (TTT2s::'\<theta> oreftrace set)"
proof -
  {
    fix t
    have "tockify t \<in> (TTT2s::'\<theta> oreftrace set)" proof (induct t)
      case Nil
      then show ?case using TTT2s_def by auto
    next
      case (Cons a ts)
      then show ?case proof (cases a)
        case (Tock X)
        thus ?thesis
          apply(auto simp add: TTT2s_def split: tev.splits)
          using Cons.hyps TTT2s_def less_Suc_eq_0_disj apply fastforce
          by (smt Cons.hyps Suc_eq_plus1 TTT2s_def diff_Suc_1 less_Suc_eq_0_disj mem_Collect_eq nth_Cons' oevent.distinct(3) rangeI)
      next
        case (Evt e)
        thus ?thesis
          apply(simp add: TTT2s_def split: tev.splits)
          by (smt Cons.hyps Suc_eq_plus1 TTT2s_def diff_Suc_1 imageE less_Suc_eq_0_disj mem_Collect_eq nth_Cons' oevent.distinct(1))
      qed
    qed
  }
  thus ?thesis by blast
qed

lemma tttracesFETTT2: "tttracesFE P \<subseteq> (TTT2::'\<theta> oreftrace set)"
  using TTT2sStronger tockifyTTT2s by fastforce

lemma tttracesFRTTT2: "tttracesFR P \<subseteq> (TTT2::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t X where "x = tockify t@[oref X]"
    by auto
  moreover have "tockify t \<in> TTT2s"
    using tockifyTTT2s by auto
  moreover have "[oref X] \<in> TTT2"
    using TTT2_def by auto
  ultimately show "x \<in> TTT2"
    using TTT2sAppend by blast
qed

lemma tttracesTITTT2: "tttracesTI P \<subseteq> (TTT2::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesTI P"
  then obtain t where "x = tockify t@[otick]"
    by auto
  moreover have "tockify t \<in> TTT2s"
    using tockifyTTT2s by auto
  moreover have "[otick] \<in> TTT2"
    using TTT2_def by auto
  ultimately show "x \<in> TTT2"
    using TTT2sAppend by blast
qed

lemma tttracesTTT2: "tttraces P \<subseteq> TTT2"
  by (auto simp only: tttracesSubset emptyTTTs tttracesFETTT2 tttracesFRTTT2 tttracesTITTT2)

lemma TTT3Append: "\<lbrakk> t \<in> TTT3; s \<in> TTT3 \<rbrakk> \<Longrightarrow> t @ s \<in> TTT3"
proof -
  assume "t \<in> TTT3"
  hence 1: "\<And>j::nat. j < length t \<and> t!j = otock \<Longrightarrow> j > 0 \<and> t!(j - 1) \<in> range oref"
    using TTT3_def by blast
  assume "s \<in> TTT3"
  hence 2: "\<And>j::nat. j < length s \<and> s!j = otock \<Longrightarrow> j > 0 \<and> s!(j - 1) \<in> range oref"
    using TTT3_def by blast
  {
    fix i
    assume 3: "i < length t + length s"
    assume 4: "(t @ s)!i = otock"
    have "i > 0 \<and> (t @ s)!(i - 1) \<in> range oref" proof (cases "i < length t")
      case True
        hence "(t @ s)!i = t!i"
          by (simp add: nth_append)
        thus ?thesis
          by (metis "1" "4" True less_imp_diff_less nth_append)
      next
        case False
        moreover hence "(t @ s)!i = s!(i - length t)"
          by (simp add: nth_append)
        ultimately have "i > length t \<and> s!(i - length t - 1) \<in> range oref"
          by (smt "2" "3" "4" less_add_same_cancel1 linordered_semidom_class.add_diff_inverse nat_add_left_cancel_less)
        thus ?thesis
          by (smt One_nat_def Suc_diff_Suc cancel_comm_monoid_add_class.diff_zero diff_right_commute gr0I less_Suc_eq not_less_iff_gr_or_eq nth_append)
    qed
  }
  thus "t @ s \<in> TTT3" by (simp add: TTT3_def)
qed


lemma tockifyTTT3: "range tockify \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof -
  {
    fix t
    have "tockify t \<in> (TTT3::'\<theta> oreftrace set)" proof (induct t)
      case Nil
      then show ?case
        by (simp add: TTT3_def)
    next
      case (Cons x ts)
      then show ?case proof (cases x)
        case (Tock X)
        then have "tockify (x # ts) = oref X # otock # tockify ts"
          by simp
        moreover have "[oref X, otock] \<in> TTT3"
          by (simp add: TTT3_def nth_Cons')
        ultimately show ?thesis
          using Cons TTT3Append by fastforce
      next
        case (Evt e)
        then have "tockify (x # ts) = oevt e # tockify ts"
          by simp
        moreover have "[oevt e] \<in> TTT3"
          by (simp add: TTT3_def nth_Cons')
        ultimately show ?thesis
          using Cons TTT3Append by fastforce
      qed
    qed
  }
  thus ?thesis by blast 
qed

lemma tttracesFETTT3: "tttracesFE P \<subseteq> (TTT3::'\<theta> oreftrace set)"
  using tockifyTTT3 tttracesFETockify by auto

lemma tttracesFRTTT3: "tttracesFR P \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t X where "x = tockify t@[oref X]"
    by auto
  moreover have "tockify t \<in> TTT3"
    using tockifyTTT3 by auto
  moreover have "[oref X] \<in> TTT3"
    using TTT3_def by auto
  ultimately show "x \<in> TTT3"
    using TTT3Append by blast
qed

lemma tttracesTITTT3: "tttracesTI P \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesTI P"
  then obtain t where "x = tockify t@[otick]"
    by auto
  moreover have "tockify t \<in> TTT3"
    using tockifyTTT3 by auto
  moreover have "[otick] \<in> TTT3"
    using TTT3_def by auto
  ultimately show "x \<in> TTT3"
    using TTT3Append by blast
qed

lemma tttracesTTT3: "tttraces P \<subseteq> TTT3"
  by (auto simp only: tttracesSubset emptyTTTs tttracesFETTT3 tttracesFRTTT3 tttracesTITTT3)

lemma TTTStructure: "tttraces P \<subseteq> TTT1 \<inter> TTT2 \<inter> TTT3"
  by (meson semilattice_inf_class.inf.bounded_iff tttracesTTT1 tttracesTTT2 tttracesTTT3)

lemma tockifyTTTss: "range tockify \<subseteq> TTTss"
  using tockifyTTT1s tockifyTTT2s tockifyTTT3 by auto

lemma tockifyTTTs: "range tockify \<subseteq> TTT1 \<inter> TTT2 \<inter> TTT3"
  using TTT2sStronger tockifyTTT1 tockifyTTT2s tockifyTTT3 by auto

lemma TTTsAppend: "t \<in> TTTss \<Longrightarrow> s \<in> TTTs \<Longrightarrow> t@s \<in> TTTs"
  by (simp add: TTT1sAppend TTT2sAppend TTT3Append)

subsubsection \<open> Reasoning about tttrace sets \<close>

lemma splitTick: "(P::'\<theta> oreftrace set) \<subseteq> TTT1 \<Longrightarrow> P = (P \<inter> untickeds) \<union> (P \<inter> tickeds)"
  using TTT1TickedOrUnticked by auto

lemma tttracesSubTicked:
  assumes "P \<subseteq> TTT1"
      and "P \<inter> untickeds \<subseteq> Q \<inter> untickeds"
      and "P \<inter> tickeds \<subseteq> Q \<inter> tickeds"
    shows "P \<subseteq> Q"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) semilattice_inf_class.le_infE semilattice_sup_class.le_sup_iff splitTick)

lemma tttracesEqTicked:
  assumes "P \<subseteq> TTT1"
      and "Q \<subseteq> TTT1"
      and "P \<inter> untickeds = Q \<inter> untickeds"
      and "P \<inter> tickeds = Q \<inter> tickeds"
    shows "P = Q"
  by (metis (mono_tags, lifting) assms splitTick)

lemma tockifyNoFR: "ta @ [oref X] \<notin> range tockify"
  by (smt TTT2s_def length_append_singleton lessI mem_Collect_eq not_less_eq nth_append_length rangeI subsetD tockifyTTT2s)

lemma tockifyNoTI: "ta @ [otick] \<notin> range tockify"
  by (smt tockifyUnticked in_mono in_set_conv_decomp mem_Collect_eq)

lemma tttracesDisjointRegions:
  shows "tttracesFR P \<inter> FE = {}"
    and "tttracesTI P \<inter> FE = {}"
    and "tttracesFE P \<inter> FR = {}"
    and "tttracesTI P \<inter> FR = {}"
    and "tttracesFE P \<inter> TI = {}"
    and "tttracesFR P \<inter> TI = {}"
  apply(auto simp add: FE_def FR_def TI_def)
  using tockifyNoTI tockifyNoFR by blast+

lemma tttracesRegionSubsets:
  shows "tttracesFE P \<subseteq> FE"
    and "tttracesFR P \<subseteq> FR"
    and "tttracesTI P \<subseteq> TI"
proof -
  have "tttracesFE P = tttracesFE P \<inter> TTTs"
    using tockifyTTTs by auto
  thus "tttracesFE P \<subseteq> FE"    
    by (metis Un_empty_right coveringRegions distrib_lattice_class.inf_sup_distrib1 semilattice_inf_class.inf.order_iff tttracesDisjointRegions(3) tttracesDisjointRegions(5))
next
  have "tttracesFR P = tttracesFR P \<inter> TTTs"
    by (metis lattice_class.inf_sup_aci(2) semilattice_inf_class.inf.absorb1 tttracesFRTTT1 tttracesFRTTT2 tttracesFRTTT3)
  also have "\<dots> \<subseteq> FR"
    by (auto simp add: FR_def)
  finally show "tttracesFR P \<subseteq> FR"
    by blast
next
  have "tttracesTI P = tttracesTI P \<inter> TTTs"
    by (metis lattice_class.inf_sup_aci(2) semilattice_inf_class.inf.absorb1 tttracesTITTT1 tttracesTITTT2 tttracesTITTT3)
  also have "\<dots> \<subseteq> TI"
    by (auto simp add: TI_def)
  finally show "tttracesTI P \<subseteq> TI"
    by blast
qed

lemma tttracesSubregions:
  shows "tttraces P \<inter> FE = tttracesFE P"
    and "tttraces P \<inter> FR = tttracesFR P"
    and "tttraces P \<inter> TI = tttracesTI P"
proof -
  have "tttraces P \<inter> FE = TTTs \<inter> tttraces P \<inter> FE"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FE)
                        \<union> (tttracesFR P \<inter> FE)
                        \<union> (tttracesTI P \<inter> FE))"
    by force
  also have "\<dots> = TTTs \<inter> tttracesFE P \<inter> FE"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesFE P"
    by (metis Int_absorb2 Int_subset_iff semilattice_inf_class.inf.absorb_iff2 tockifyTTTs tttracesFETockify tttracesRegionSubsets(1))
  finally show "tttraces P \<inter> FE = tttracesFE P"
    by blast
next
  have "tttraces P \<inter> FR = TTTs \<inter> tttraces P \<inter> FR"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FR)
                        \<union> (tttracesFR P \<inter> FR)
                        \<union> (tttracesTI P \<inter> FR))"
    by force
  also have "\<dots> = TTTs \<inter> tttracesFR P \<inter> FR"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesFR P"
    by (metis (no_types, lifting) FR_def Int_absorb1 Int_absorb2 Int_subset_iff tttracesRegionSubsets(2))
  finally show "tttraces P \<inter> FR = tttracesFR P"
    by blast
next
  have "tttraces P \<inter> TI = TTTs \<inter> tttraces P \<inter> TI"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> TI)
                        \<union> (tttracesFR P \<inter> TI)
                        \<union> (tttracesTI P \<inter> TI))"
    by force
  also have "\<dots> = TTTs \<inter> tttracesTI P \<inter> TI"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesTI P"
    by (metis (no_types, lifting) TI_def Int_absorb1 Int_absorb2 Int_subset_iff tttracesRegionSubsets(3))
  finally show "tttraces P \<inter> TI = tttracesTI P"
    by blast
qed

lemma tttracesEq:
  assumes "B \<subseteq> (TTTs::'\<theta> oreftrace set)"
      and "tttracesFE P = B \<inter> FE"
      and "tttracesFR P = B \<inter> FR"
      and "tttracesTI P = B \<inter> TI"
    shows "tttraces P = B"
proof -
  have "tttraces P = tttracesFE P \<union> tttracesFR P \<union> tttracesTI P"
    by simp
  also have "\<dots> =(B \<inter> FE) \<union> (B \<inter> FR) \<union> (B \<inter> TI)"
    using assms(2) assms(3) assms(4) by blast
  also have "\<dots> = B \<inter> (FE \<union> FR \<union> TI)"
    by blast
  also have "\<dots> = B \<inter> TTTs"
    using coveringRegions by blast
  also have "\<dots> = B"
      using assms(1) by blast
  finally show ?thesis
    by blast
qed

lemma tttracesEqRem:
  assumes "tttracesFE P = (B - FR - TI::'\<theta> oreftrace set)"
      and "tttracesFR P = B \<inter> FR"
      and "tttracesTI P = B \<inter> TI"
    shows "tttraces P = B"
proof -
  have "B = (B - FR - TI::'\<theta> oreftrace set) \<union> (B \<inter> FR) \<union> (B \<inter> TI)"
    by force
  also have "\<dots> = tttraces P"
    using assms(1) assms(2) assms(3) calculation by auto
  finally show "tttraces P = B"
    by blast
qed

lemma tttracesCalc:
  assumes "tttracesFE P = A"
      and "tttracesFR P = B"
      and "tttracesTI P = C"
    shows "tttraces P = A \<union> B \<union> C"
  using assms(1) assms(2) assms(3) tttraces.simps by blast

lemma tttracesEqTttraces:
  assumes "tttracesFE P = tttracesFE Q"
      and "tttracesFR P = tttracesFR Q"
      and "tttracesTI P = tttracesTI Q"
    shows "tttraces P = tttraces Q"
  using assms by auto

end