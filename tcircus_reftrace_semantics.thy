section \<open> Tick Tock CSP UTP Semantics \<close>

theory tcircus_reftrace_semantics
  imports "tcircus_rel" "/home/isabelle/utp-main/theories/rcircus/Refusal_Tests" "UTP.utp_full"
begin

subsection \<open> Refusal trace functions \<close>

fun tooutput :: "'\<theta> reftrace \<Rightarrow> '\<theta> oreftrace" where
"tooutput (Evt e # ts) = oevt e # tooutput ts"|
"tooutput (Tock X # ts) = otock # tooutput ts"|
"tooutput []           = []"

fun torefset :: "'\<theta> set \<Rightarrow> '\<theta> refevent set" where
"torefset X = {refevt e | e. e \<in> X}"


lemma torefsetSubsetReftick: "torefset X \<subseteq> torefset Y \<union> {reftick} \<Longrightarrow> X \<subseteq> Y"
proof 
  fix x
  assume 1: "torefset X \<subseteq> torefset Y \<union> {reftick}"
  assume 2: "x \<in> X"
  then have "refevt x \<in> torefset X"
    by simp
  then have "refevt x \<in> torefset Y \<union> {reftick}"
    using "1" by blast
  thus "x \<in> Y"
    by simp
qed

lemma torefsetSubset: "torefset X \<subseteq> torefset Y \<Longrightarrow> X \<subseteq> Y"
  by (meson semilattice_sup_class.le_supI1 torefsetSubsetReftick)

lemma torefsetInjective: "torefset X = torefset Y \<Longrightarrow> X = Y"
proof -
  assume 1: "torefset X = torefset Y"
  {
    fix e
    have "(e \<in> X) = (refevt e \<in> torefset X)"
      by simp
    also have "\<dots> = (refevt e \<in> torefset Y)"
      using "1" by blast
    also have "\<dots> = (e \<in> Y)"
      by simp
    finally have "(e \<in> X) = (e \<in> Y)"
      by auto
  }
  thus ?thesis
    by (simp add: Set.set_eqI)
qed

fun fromrefevent :: "'\<theta> refevent \<Rightarrow> '\<theta> set" where
"fromrefevent (refevt e) = {e}"|
"fromrefevent reftick = {}"|
"fromrefevent reftock = {}"

fun fromrefset :: "'\<theta> refevent set \<Rightarrow> '\<theta> set" where
"fromrefset X = \<Union> {fromrefevent x | x. x\<in>X}"

fun finalrefset :: "bool \<Rightarrow> bool \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> refevent set" where
"finalrefset True False X = torefset X"|
"finalrefset True True X = torefset X \<union> {reftick}"|
"finalrefset False False X = torefset X \<union> {reftock}"|
"finalrefset False True X = torefset X \<union> {reftock, reftick}"

fun tockifications :: "'\<theta> reftrace \<Rightarrow> '\<theta> oreftrace set" where
"tockifications (Evt e # ts) =
  { oevt e # t | t. t \<in> tockifications ts }"|
"tockifications (Tock X # ts) =
    { oref (torefset X) # otock # t | t. t \<in> tockifications ts}
  \<union> { oref (torefset X \<union> {reftick}) # otock # t | t. t \<in> tockifications ts }"|
"tockifications [] = {[]}"

lemma "tockifications ([Tock {}]) = {[oref {}, otock], [oref {reftick}, otock]}"
  by (auto)

lemma "tockifications ([Tock {}, Evt 1]) = {[oref {}, otock, oevt 1], [oref {reftick}, otock, oevt 1]}"
  by (auto)

lemma "{t' @ s' | t' s' . t' \<in> tockifications [Tock {}] \<and> s' \<in> tockifications []} = {[oref {}, otock], [oref {reftick}, otock]}"
  by (auto)


lemma "{t' @ s' | t' s' . t' \<in> tockifications [Tock {}] \<and> s' \<in> tockifications [Evt 1]} = {[oref {}, otock, oevt 1], [oref {reftick}, otock, oevt 1]}"
  by (auto)

lemma tockificationsCons: "tockifications (a # t) = {w @ t' | w t'. w \<in> tockifications [a] \<and> t' \<in> tockifications t}"
proof (cases a)
  case (Tock X)
  have "tockifications [Tock X] = {[oref (torefset X), otock], [oref (torefset X \<union> {reftick}), otock]}"
    by (auto)
  moreover have "tockifications ([Tock X] @ t) = {[oref (torefset X), otock] @ s | s . s \<in> tockifications t}
                                               \<union> {[oref (torefset X \<union> {reftick}), otock] @ s | s . s \<in> tockifications t}"
    by auto
  ultimately show ?thesis
     by (smt (z3) Collect_cong Collect_disj_eq Tock append.simps(1) append.simps(2) append_eq_append_conv insertCI insertE singletonD singletonI)
next
  case (Evt e)
  have "tockifications (Evt e # t) = {[oevt e] @ s | s . s \<in> tockifications t}"
    by simp
  moreover have "tockifications [Evt e] = {[oevt e]}"
    by simp
  ultimately show ?thesis
    by (smt (z3) Collect_cong Evt singletonD singletonI)
qed

lemma tockificationsAppend: "tockifications(t @ s) = { t' @ s' | t' s' . t' \<in> tockifications t \<and> s' \<in> tockifications s }"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then have "tockifications ((a # t) @ s) = tockifications (a # (t @ s))"
    by simp
  also have "\<dots> = {w @ t' | w t'. w \<in> tockifications [a] \<and> t' \<in> tockifications (t @ s)}"
    using tockificationsCons by blast
  also have "\<dots> = {(w @ t'') @ t''' | w t'' t'''. w \<in> tockifications [a] \<and> t'' \<in> tockifications t
                                             \<and> t''' \<in> tockifications s}"
    using Cons.hyps by auto
  also have "\<dots> = {v @ t''' | v t'''. v \<in> {w @ t''| w t'' . w \<in> tockifications [a] \<and> t'' \<in> tockifications t}
                                             \<and> t''' \<in> tockifications s}"
    by blast
  also have "\<dots> = {v @ t''' | v t'''. v \<in> tockifications (a # t) \<and> t''' \<in> tockifications s}"
  proof -
    have "\<And>v. (v \<in> {w @ t''| w t'' . w \<in> tockifications [a] \<and> t'' \<in> tockifications t}) = (v \<in> tockifications (a # t))"
      using tockificationsCons by blast
    thus ?thesis
      by force
  qed
  finally show ?case
    by blast
qed

lemma tockificationsNonEmpty: "{} \<notin> ((range tockifications) :: '\<sigma> oreftrace set set)"
proof -
  {
    fix x :: "'\<sigma> reftrace"
    assume "tockifications x = {}"
    then have False proof (induction x)
      case Nil
      then show ?case by auto
    next
      case (Cons a x)
      then show ?case
        by (cases a; auto)
    qed
  }
  thus ?thesis by auto
qed

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

(*
lemma tockifificationsEq: "((tockifications t \<inter> tockifications s) \<noteq> {}) = (t = s)"
proof
  assume "t = s"
  then show "((tockifications t) \<inter> (tockifications s)) \<noteq> {}"
    using tockificationsNonEmpty by auto
next
  assume "tockifications t \<inter> tockifications s \<noteq> {}"
  then obtain r where "r \<in> tockifications t \<and> r \<in> tockifications s"
    by blast
  then have "refEquiv r (tockify t) \<and> refEquiv r (tockify s)"
    by (simp add: tockificationsTockify)
  then have "refEquiv (tockify t) (tockify s)"
    using refEquivSym refEquivTrans by blast
  then show "t = s"
    by (simp add: refEquivTockify)
qed
*)

subsection \<open> Traces \<close>

fun traces :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"traces P = { tooutput t | t . \<not>`\<not>P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,true,false,true/$tr,$tr\<acute>,$ok,$wait,$ok\<acute>\<rbrakk>` }"
(* `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` *)

abbreviation "ET \<equiv> {[]}"

subsection \<open> Refusal Traces \<close>

\<comment>\<open> Need to introduce some final refusals: what is the rule here? \<close>
fun tttracesFE :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFE P = { s | t s.
                  \<not>`(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`
                \<and> s \<in> tockifications t }"
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset p refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (p::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>p\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$pat\<rbrakk>`
                \<and> s \<in> tockifications t}"
fun tttracesTI :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesTI P = { s @ [otick] | t s .
                  \<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`
               \<and> s \<in> tockifications t}"
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



lemma tockificationsEmpty: "({[]} = tockifications t) = (t = [])"
proof -
  have "t = [] \<Longrightarrow> ET = tockifications t" by auto
  moreover {
    assume "t \<noteq> []"
    then obtain th tr where "t = th # tr"
      by (meson neq_Nil_conv)
    then have "tockifications t \<noteq> {[]}"
      by (cases "th"; auto)
  }
  ultimately show ?thesis by auto
qed

lemma tockificationsEmptyS: "([] \<in> tockifications t) = (t = [])"
proof -
  have "t = [] \<Longrightarrow> ET = tockifications t" by auto
  moreover {
    assume "t \<noteq> []"
    then obtain th tr where "t = th # tr"
      by (meson neq_Nil_conv)
    then have "[] \<notin> tockifications t"
      by (cases "th"; auto)
  }
  ultimately show ?thesis by auto
qed

lemma tockificationsUnticked: "tockifications t \<subseteq> (untickeds::'\<theta> oreftrace set)"
proof (induct t)
  case Nil
  then show ?case
    by auto
next
  case (Cons th tl)
  then have "tockifications (th # tl) = {th' @ tl' | th' tl' . th' \<in> tockifications [th]
                                                     \<and> tl' \<in> tockifications tl}"
    using tockificationsCons by blast
  moreover have "tockifications [th] \<subseteq> untickeds"
    by (cases th; auto)
  ultimately show ?case
    by (smt (z3) Cons.hyps UnE mem_Collect_eq set_append subset_iff)
qed

lemma TTT1sUnticked: "TTT1s = untickeds"
  by (simp add: Suc_le_eq in_set_conv_nth TTT1s_def)

lemma tockificationsTTT1s: "\<Union>(range tockifications) \<subseteq> TTT1s"
  using TTT1sUnticked tockificationsUnticked by blast

lemma tockificationsTTT1: "\<Union>(range tockifications) \<subseteq> TTT1"
  using tockificationsUnticked TTT1TickedOrUnticked by blast

lemma tttracesFETockifications: "tttracesFE P \<subseteq> \<Union>(range tockifications)"
  by auto

lemma tockificationsTicked: "s \<in> tockifications t \<Longrightarrow> s@[otick] \<in> tickeds"
  using tockificationsUnticked by auto

lemma TTT1sAppend: "t \<in> TTT1s \<Longrightarrow> s \<in> TTT1 \<Longrightarrow> t@s \<in> TTT1"
  by (simp add: TTT1s_def TTT1_def nth_append)

lemma tttracesFETTT1: "tttracesFE P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  using tttracesFETockifications tockificationsTTT1 by auto

lemma tttracesFRTTT1: "tttracesFR P \<subseteq> (TTT1::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t s X where "x = s@[oref X] \<and> s \<in> tockifications t"
    by auto
  then show "x \<in> TTT1"
    by (simp add: TTT1_def)
       (metis basic_trans_rules(31) mem_Collect_eq nth_append nth_mem
              tockificationsUnticked)
qed

lemma tttracesTITTT1: "tttracesTI P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  by (simp add: TTT1_def)
     (smt (verit, ccfv_threshold) Collect_mono TTT1TickedOrUnticked TTT1_def
                                  UnCI mem_Collect_eq tockificationsTicked)

lemma tttracesTTT1: "tttraces P \<subseteq> TTT1"
  by (rule tttracesSubset; auto simp only: tttracesFETTT1 tttracesFRTTT1 tttracesTITTT1)

lemma TTT2sStronger: "TTT2s \<subseteq> TTT2"
  by (simp add: Collect_mono TTT2_def TTT2s_def)

lemma TTT2Append: "t \<in> TTT2s \<Longrightarrow> s \<in> TTT2 \<Longrightarrow> t @ s \<in> TTT2"
  apply(auto simp add: TTT2_def TTT2s_def)
  by (smt Suc_diff_Suc diff_Suc_Suc linordered_semidom_class.add_diff_inverse nat_add_left_cancel_less not_less_eq not_less_iff_gr_or_eq nth_append range_eqI)

lemma TTT2sAppend: "t \<in> TTT2s \<Longrightarrow> s \<in> TTT2s \<Longrightarrow> t @ s \<in> TTT2s"
  apply(auto simp add: TTT2s_def)
  apply (smt (z3) Suc_lessI Suc_pred' add.right_neutral cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_Suc_1 diff_right_commute length_greater_0_conv less_Suc_eq less_not_refl list.size(3) not_add_less1 nth_append range_eqI)
  by (smt Suc_diff_Suc diff_Suc_Suc linordered_semidom_class.add_diff_inverse nat_add_left_cancel_less not_less_eq not_less_iff_gr_or_eq nth_append range_eqI)

(* Rather intense! *)
lemma tockificationsTTT2s: "\<Union> (range tockifications) \<subseteq> (TTT2s::'\<theta> oreftrace set)"
proof -
  {
    fix t::"'\<theta> reftrace"
    have "tockifications t \<subseteq> (TTT2s::'\<theta> oreftrace set)" proof (induct t)
      case Nil
      then show ?case
        using TTT2s_def by auto
    next
      case (Cons a ts)
      {
        fix s
        assume "(s \<in> tockifications (a # ts))"
        then obtain sh sl where 3: "s = sh @ sl \<and> sh \<in> tockifications [a] \<and> sl \<in> tockifications ts"
          by (smt (verit) mem_Collect_eq tockificationsCons)
        then consider
          "\<exists> e. sh = [oevt e]"
        | "\<exists> X. (sh = [oref X, otock]) \<and> reftock \<notin> X"
          by(cases a; auto)
        then have "sh \<in> TTT2s" proof(cases)
          case 1
          then show ?thesis
            by (auto simp add: TTT2s_def)
        next
          case 2
          then show ?thesis
            by (simp add: TTT2s_def)
               (metis Suc_lessI gr0I image_iff length_Cons list.size(3) not_less_eq nth_Cons_0 nth_Cons_Suc oevent.distinct(3))
        qed
        moreover have "sl \<in> TTT2s"
            using 3 Cons by auto
          ultimately have "s \<in> TTT2s"
            using 3 TTT2sAppend by blast
      }
      thus ?case by blast
    qed
  }
  thus ?thesis
    by blast
qed

lemma tttracesFETTT2: "tttracesFE P \<subseteq> (TTT2::'\<theta> oreftrace set)"
  using TTT2sStronger tockificationsTTT2s by fastforce

lemma tttracesFRTTT2: "tttracesFR P \<subseteq> (TTT2::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t s X where 1: "x = s@[oref X] \<and> s \<in> tockifications t"
    by auto
  moreover have "s \<in> TTT2s"
    using tockificationsTTT2s 1 by auto
  moreover have "[oref X] \<in> TTT2"
    using TTT2_def by auto
  ultimately show "x \<in> TTT2"
    using TTT2Append by blast
qed
  
lemma tttracesTITTT2: "tttracesTI P \<subseteq> (TTT2::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesTI P"
  then obtain t s where 1: "x = s@[otick] \<and> s \<in> tockifications t"
    by auto
  moreover have "s \<in> TTT2s"
    using tockificationsTTT2s 1 by auto
  moreover have "[otick] \<in> TTT2"
    using TTT2_def by auto
  ultimately show "x \<in> TTT2"
    using TTT2Append by blast
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


lemma tockificationsTTT3: "\<Union> (range tockifications) \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof -
  {
    fix t::"'\<theta> reftrace"
    have "tockifications t \<subseteq> TTT3" proof (induct t)
      case Nil
      then show ?case
        by (simp add: TTT3_def)
    next
      case (Cons x ts)
      {
        fix s
        assume "s \<in> tockifications (x # ts)"
        then obtain sh sl where 4: "s = sh @ sl \<and> sh \<in> tockifications [x] \<and> sl \<in> tockifications ts"
          by (smt (verit) mem_Collect_eq tockificationsCons)
        then consider
          "\<exists> e. sh = [oevt e]"
        | "\<exists> X. (sh = [oref X, otock]) \<and> reftock \<notin> X"
          by (cases x; auto)
        then have "sh \<in> TTT3" proof (cases)
          case 1
          then show ?thesis
            using TTT3_def nth_Cons' by auto
        next
          case 2
          then obtain X where 5: "sh = [oref X, otock]"
            by auto
          then show ?thesis
            by (auto simp add: TTT3_def)
               (metis gr0I nth_Cons_0 oevent.distinct(3))
        qed
        moreover have "sl \<in> TTT3"
          using "4" Cons.hyps by blast
        ultimately have "s \<in> TTT3"
          using "4" TTT3Append by blast
      }
      thus ?case by auto
    qed
  }
  thus ?thesis by blast 
qed

lemma tttracesFETTT3: "tttracesFE P \<subseteq> (TTT3::'\<theta> oreftrace set)"
  using tockificationsTTT3 tttracesFETockifications by auto

lemma tttracesFRTTT3: "tttracesFR P \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesFR P"
  then obtain t s X where 1: "x = s@[oref X] \<and> s \<in> tockifications t"
    by auto
  moreover have "s \<in> TTT3"
    using tockificationsTTT3 1 by auto
  moreover have "[oref X] \<in> TTT3"
    using TTT3_def by auto
  ultimately show "x \<in> TTT3"
    using TTT3Append by blast
qed

lemma tttracesTITTT3: "tttracesTI P \<subseteq> (TTT3::'\<theta> oreftrace set)"
proof
  fix x
  assume "(x::'\<theta> oreftrace) \<in> tttracesTI P"
  then obtain t s where 1: "x = s@[otick] \<and> s \<in> tockifications t"
    by auto
  moreover have "s \<in> TTT3"
    using 1 tockificationsTTT3 by auto
  moreover have "[otick] \<in> TTT3"
    using TTT3_def by auto
  ultimately show "x \<in> TTT3"
    using TTT3Append by blast
qed

lemma tttracesTTT3: "tttraces P \<subseteq> TTT3"
  by (auto simp only: tttracesSubset emptyTTTs tttracesFETTT3 tttracesFRTTT3 tttracesTITTT3)

lemma TTTStructure: "tttraces P \<subseteq> TTT1 \<inter> TTT2 \<inter> TTT3"
  by (meson semilattice_inf_class.inf.bounded_iff tttracesTTT1 tttracesTTT2 tttracesTTT3)

lemma tockificationsTTTss: "\<Union> (range tockifications) \<subseteq> TTTss"
  using tockificationsTTT1s tockificationsTTT2s tockificationsTTT3 by auto

lemma tockificationsTTTs: "\<Union> (range tockifications) \<subseteq> TTT1 \<inter> TTT2 \<inter> TTT3"
  using TTT2sStronger tockificationsTTT1 tockificationsTTT2s tockificationsTTT3 by auto

lemma TTTsAppend: "t \<in> TTTss \<Longrightarrow> s \<in> TTTs \<Longrightarrow> t@s \<in> TTTs"
  by (simp add: TTT1sAppend TTT2Append TTT3Append)

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

lemma TTT2sNoFR: "ta @ [oref X] \<notin> TTT2s"
  by (auto simp add: TTT2s_def)

lemma tockificationsNoFR: "ta @ [oref X] \<notin> \<Union> (range tockifications)"
  by (meson TTT2sNoFR in_mono TTT2s_def tockificationsTTT2s)

lemma tockificationsNoTI: "ta @ [otick] \<notin> \<Union> (range tockifications)"
  by (metis tockificationsUnticked UN_subset_iff in_set_conv_decomp mem_Collect_eq subset_eq)

lemma tttracesDisjointRegions:
  shows "tttracesFR P \<inter> FE = {}"
    and "tttracesTI P \<inter> FE = {}"
    and "tttracesFE P \<inter> FR = {}"
    and "tttracesTI P \<inter> FR = {}"
    and "tttracesFE P \<inter> TI = {}"
    and "tttracesFR P \<inter> TI = {}"
  apply(auto simp add: FE_def FR_def TI_def)
  using tockificationsNoTI tockificationsNoFR by blast+

lemma tttracesRegionSubsets:
  shows "tttracesFE P \<subseteq> FE"
    and "tttracesFR P \<subseteq> FR"
    and "tttracesTI P \<subseteq> TI"
proof -
  have "tttracesFE P = tttracesFE P \<inter> TTTs"
    using tockificationsTTTs by fastforce
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
    by (metis Int_absorb2 Int_subset_iff semilattice_inf_class.inf.absorb_iff2 tockificationsTTTs tttracesFETockifications tttracesRegionSubsets(1))
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