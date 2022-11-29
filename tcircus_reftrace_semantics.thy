section \<open> Tick Tock CSP UTP Semantics \<close>

theory tcircus_reftrace_semantics
  imports "tcircus_rel" "/home/isabelle/utp-main/theories/rcircus/Refusal_Tests" "tcircus_laws" "UTP.utp_full"
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

(* fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset acctock refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (acctock::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  (\<not>`\<not>(peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>False\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$pat\<acute>\<rbrakk>`)
                \<and> (patient P t X \<longrightarrow> acctock)
                \<and> s \<in> tockifications t}"
 * Arg 1: patience (if false then refuse tock)
 * Arg 2: unterminatability (if true then refuse tick)
 *)
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


lemma tockificationsEmpty: "({[]} = tockifications t) = (t = [])"
proof -
  have "t = [] \<Longrightarrow> {[]} = tockifications t" by auto
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
  have "t = [] \<Longrightarrow> {[]} = tockifications t" by auto
  moreover {
    assume "t \<noteq> []"
    then obtain th tr where "t = th # tr"
      by (meson neq_Nil_conv)
    then have "[] \<notin> tockifications t"
      by (cases "th"; auto)
  }
  ultimately show ?thesis by auto
qed

lemma tockificationsCaseEvt:
  assumes "oevt e # s \<in> tockifications t"
  shows "\<exists> t'. (t = Evt e # t' \<and> s \<in> tockifications t')"
proof (cases t rule: tockifications.cases)
  case (1 e ts)
  then show ?thesis
    using assms by force
next
  case (2 X ts)
  then have "False"
    using assms by simp
  then show ?thesis
    by blast
next
  case 3
  then show ?thesis
    using assms by auto
qed

lemma tockificationsCaseTock:
  assumes "oref (torefset X) # otock # s \<in> tockifications t"
  shows "\<exists> t'. (t = Tock X # t' \<and> s \<in> tockifications t')"
proof (cases t rule: tockifications.cases)
  case (1 e ts)
  then show ?thesis
    using assms by auto
next
  case (2 Y ts)
  then show ?thesis
    using assms by auto
next
  case 3
  then show ?thesis
    using assms by auto
qed


lemma tockificationsCaseTockReftick:
  assumes "oref (torefset X \<union> {reftick}) # otock # s \<in> tockifications t"
  shows "\<exists> t'. (t = Tock X # t' \<and> s \<in> tockifications t')"
proof (cases t rule: tockifications.cases)
  case (1 e ts)
  then show ?thesis
    using assms by auto
next
  case (2 Y ts)
  then show ?thesis
    using assms by auto
next
  case 3
  then show ?thesis
    using assms by auto
qed

lemma tockificationsCaseTock':
  assumes "oref X # otock # s \<in> tockifications t"
  shows "\<exists> t' Y. (((X = torefset Y) \<or> (X = torefset Y \<union> {reftick})) \<and> (t = Tock Y # t') \<and> s \<in> tockifications t')"
proof (cases t rule: tockifications.cases)
  case (1 e ts)
  then show ?thesis
    using assms by auto
next
  case (2 Y ts)
  then show ?thesis
    using assms by auto
next
  case 3
  then show ?thesis
    using assms by auto
qed

lemma tockificationsCaseTock'':
  assumes "oref X # s \<in> tockifications t"
  shows "\<exists> t' s' Y. (((X = torefset Y) \<or> (X = torefset Y \<union> {reftick})) \<and> (t = Tock Y # t') \<and> (s = otock # s') \<and> s' \<in> tockifications t')"
proof (cases t rule: tockifications.cases)
  case (1 e ts)
  then show ?thesis
    using assms by auto
next
  case (2 Y ts)
  then show ?thesis
    using assms by auto
next
  case 3
  then show ?thesis
    using assms by auto
qed

lemma tockificationsDisjoint: "s \<in> tockifications t \<Longrightarrow> s \<in> tockifications t' \<Longrightarrow> t = t'"
proof (induct t' arbitrary: s t)
  case Nil
  then show ?case
    using tockificationsEmptyS by auto
next
  case (Cons a t')
  assume 1: "s \<in> tockifications t"
  assume 2: "s \<in> tockifications (a # t')"
  then obtain s' s'' where 3: "s = s' @ s''" and 4: "s' \<in> tockifications [a]" and 5: "s'' \<in> tockifications t'"
    by (smt (verit, best) mem_Collect_eq tockificationsCons)
  {
    have "\<exists> t''. t = a # t'' \<and> s'' \<in> tockifications t''" proof (cases a)
      case (Tock X)
      consider "s' = [oref (torefset X), otock]" | "s' = [oref (torefset X \<union> {reftick}), otock]"
        using 1 4 Tock by auto
      then show ?thesis
        apply(cases)
        using Tock 1 by (simp_all add: 3 tockificationsCaseTock tockificationsCaseTockReftick)
    next
      case (Evt e)
      then show ?thesis
        using 1 4 by (simp add: 3 tockificationsCaseEvt)
    qed
  }
  then obtain t'' where 6: "t = a # t''" and 7: "s'' \<in> tockifications t''"
    using "5" by blast
  have "t' = t''"
    using "5" "7" Cons.hyps by blast
  then show ?case
    by (simp add: "6")
qed

lemma tockificationsEq: "((tockifications t \<inter> tockifications s) \<noteq> {}) = (t = s)"
proof
  assume "t = s"
  then show "((tockifications t) \<inter> (tockifications s)) \<noteq> {}"
    using tockificationsNonEmpty by auto
next
  assume "tockifications t \<inter> tockifications s \<noteq> {}"
  then obtain r where "r \<in> tockifications t \<and> r \<in> tockifications s"
    by blast
  then show "t = s"
    using tockificationsDisjoint by blast
qed

subsection \<open> Traces \<close>

fun traces :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"traces P = { tooutput t | t . \<not>`\<not>P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,true,false,true/$tr,$tr\<acute>,$ok,$wait,$ok\<acute>\<rbrakk>` }"
(* `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` *)

abbreviation "ET \<equiv> {[]}"

(*
fun finalrefset :: "bool \<Rightarrow> bool \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> refevent set" where
"finalrefset True False X = torefset X"|
"finalrefset True True X = torefset X \<union> {reftick}"|
"finalrefset False False X = torefset X \<union> {reftock}"|
"finalrefset False True X = torefset X \<union> {reftock, reftick}"
*)

(*
fun finalrefset :: "bool \<Rightarrow> bool \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> refevent set" where
"finalrefset True False X = torefset X"|
"finalrefset True True X = torefset X \<union> {reftick}"|
"finalrefset False False X = torefset X \<union> {reftock}"|
"finalrefset False True X = torefset X \<union> {reftock, reftick}"
*)


subsection \<open> Refusal Traces \<close>


fun tttracesRRFRI :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesRRFRI (Q) = { s@[oref (finalrefset False refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
                  (\<not>`\<not>Q\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>False\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$ref,$pat\<rbrakk>`)
                \<and> (\<not>patientRR Q t X)
                \<and> s \<in> tockifications t}"

\<comment>\<open> Need to introduce some final refusals: what is the rule here? \<close>
\<comment>\<open> How should p actually be used? \<close>
fun tttracesFE :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFE P = { s | t s.
                  \<not>`(\<not>peri\<^sub>R P \<and> \<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`
                \<and> s \<in> tockifications t }"
fun tttracesFRI :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFRI P = { s@[oref (finalrefset False refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
                  (\<not>`\<not>(peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`)
                \<and> (\<not>patient P t X)
                \<and> s \<in> tockifications t}"
fun tttracesFRP :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFRP P = { s@[oref (finalrefset True refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
                  (\<not>`\<not>(peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`)
                \<and> s \<in> tockifications t}"
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = ((tttracesFRI P) \<union> (tttracesFRP P))"
                (* \<and> (patient P t X \<longrightarrow> acctock) *)
(*
"tttracesFR P = { s@[oref (finalrefset acctock refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (acctock::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  (if acctock
                   then
                      \<not>`\<not>(peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`
                   else
                      \<not>`\<not>((  (\<not> peri\<^sub>R P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>)
                           \<and> (peri\<^sub>R P\<lbrakk>\<guillemotleft>False\<guillemotright>/$pat\<acute>\<rbrakk>)
                           )\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`)
                \<and> s \<in> tockifications t}" *)
(*
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset acctock refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (acctock::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  (\<forall> (p::bool).
                  (p \<longrightarrow> acctock) \<and>
                   \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>p\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$pat\<acute>\<rbrakk>`) 
                \<and> s \<in> tockifications t}"
*)
(*
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset p refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (p::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>p\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$pat\<acute>\<rbrakk>`
                \<and> s \<in> tockifications t}"
*)
(*
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset p refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (p::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`
                \<and> s \<in> tockifications t}" *)
(*
fun tttracesFR :: "'\<theta> ttcsp \<Rightarrow> ('\<theta> oreftrace) set" where
"tttracesFR P = { s@[oref (finalrefset p refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (p::bool) (q::bool) (refterm::bool) (s::'\<theta> oreftrace).
                  \<not>`(\<not>peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>,\<guillemotleft>p\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>,$pat\<acute>\<rbrakk>`
                \<and> (q \<longrightarrow> p)
                \<and> s \<in> tockifications t}" *)
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

named_theorems TTTsimps

definition TTT1 :: "('\<theta> oreftrace) set"  where
[TTTsimps]: "TTT1 = { t. \<forall> i::nat . Suc i < length t \<longrightarrow> t ! i \<noteq> otick}"
definition TTT1s :: "('\<theta> oreftrace) set" where
[TTTsimps]: "TTT1s = { t. \<forall> i::nat . Suc i \<le> length t \<longrightarrow> t ! i \<noteq> otick}"

definition TTT2 :: "('\<theta> oreftrace) set" where
[TTTsimps]: "TTT2 = { t . \<forall> i::nat. Suc i < length t \<and> t ! i \<in> range oref \<longrightarrow> t ! (i + 1) = otock}"

definition TTT2s :: "('\<theta> oreftrace) set" where
[TTTsimps]: "TTT2s = { t . \<forall> i::nat. i < length t \<and> t ! i \<in> range oref \<longrightarrow> Suc i < length t \<and> t ! (i + 1) = otock}"
definition TTT3 :: "('\<theta> oreftrace) set" where
[TTTsimps]: "TTT3 = { t . \<forall> i::nat. i < length t \<and> t ! i = otock \<longrightarrow> i > 0 \<and> t ! (i - 1) \<in> range oref}"

abbreviation "TTTs \<equiv> TTT1 \<inter> TTT2 \<inter> TTT3"

abbreviation "TTTss \<equiv> TTT1s \<inter> TTT2s \<inter> TTT3"

named_theorems TTsimps

definition TT0 :: "('\<theta> oreftrace) set \<Rightarrow> bool"  where
[TTsimps]: "TT0 P = (P \<noteq> {})"

definition TT1 :: "('\<theta> oreftrace) set \<Rightarrow> bool"  where
[TTsimps]: "TT1 P = (\<forall> \<rho> \<sigma>. \<rho> \<le> \<sigma> \<and> \<sigma> \<in> P \<longrightarrow> \<rho> \<in> P)"

definition TT2 :: "('\<theta> oreftrace) set \<Rightarrow> bool"  where
[TTsimps]: "TT2 P = (\<forall> \<rho> \<sigma> X Y. \<rho> @ [oref X] @ \<sigma> \<in> P
                   \<and> (Y \<inter> ({refevt e| e. \<rho> @ [oevt e] \<in> P}
                         \<union> (if \<rho> @ [otick] \<in> P then {reftick} else {})
                         \<union> (if \<rho> @ [oref X, otock] \<in> P then {reftock} else {})) = {})
                 \<longrightarrow> \<rho> @ [oref (X \<union> Y)] \<in> P)"

definition TT3i :: "'\<theta> oreftrace \<Rightarrow> bool"  where
[TTsimps]: "TT3i t = (\<forall> \<rho> \<sigma> X. \<rho> @ [oref X, otock] @ \<sigma> = t \<longrightarrow> reftock \<notin> X)"

definition TT3 :: "('\<theta> oreftrace) set \<Rightarrow> bool"  where
[TTsimps]: "TT3 P = (\<forall> t. t \<in> P \<longrightarrow> TT3i t)"

definition TT4 :: "('\<theta> oreftrace) set \<Rightarrow> bool"  where
[TTsimps]: "TT4 P = (\<forall> \<rho> \<sigma> X. \<rho> @ [oref X] @ \<sigma> \<in> P \<longrightarrow> \<rho> @ [oref (X \<union> {reftick})] @ \<sigma> \<in> P)"


subsubsection \<open> Designated Subsets \<close>

abbreviation untickeds :: "('\<theta> oreftrace) set" where
"untickeds \<equiv> {t::'\<theta> oreftrace. otick \<notin> set t}"
abbreviation tickeds :: "('\<theta> oreftrace) set" where
"tickeds \<equiv> {t@[otick] | t. t \<in> untickeds}"

lemma tickedsUntickedsDisj: "untickeds \<inter> tickeds = {}"
  by auto

lemma emptyTTTs: "ET \<subseteq> TTTs"
  by (simp add: TTTsimps)

definition [TTTsimps]: "FR \<equiv> {t@[oref X] | t X  . True} \<inter> TTTs"
definition [TTTsimps]: "FRI \<equiv> {t@[oref X] | t X  . reftock \<in> X} \<inter> TTTs"
definition [TTTsimps]: "FRP \<equiv> {t@[oref X] | t X  . reftock \<notin> X} \<inter> TTTs"
definition [TTTsimps]: "TI \<equiv> {t@[otick] | t . True} \<inter> TTTs"
definition [TTTsimps]: "FE \<equiv> TTTs - (FR \<union> TI)"

declare in_set_conv_nth[TTTsimps]
declare nth_append[TTTsimps]

subsubsection \<open> General Relationships \<close>

lemma distinctRegions:
  shows "ET \<inter> FR = {}"
    and "ET \<inter> TI = {}"
    and "FE \<inter> FR = {}"
    and "FE \<inter> TI = {}"
    and "FR \<inter> TI = {}"
  by (auto simp add: TTTsimps)

lemma emptyFE: "ET \<subseteq> FE"
  by (simp add: TTTsimps)

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
    by (auto simp add: TTTsimps)
qed

lemma coveringRegions: "(TTTs::'\<theta> oreftrace set) = FE \<union> FR \<union> TI" (is "TTTs = ?regions")
  by (auto simp add: TTTsimps)

lemma disjointFR: "FRI \<inter> FRP = {}"
  by (auto simp add: TTTsimps)

lemma coveringFR: "FRI \<union> FRP = FR"
  by (auto simp add: TTTsimps)

lemma TTT1TickedOrUnticked: "TTT1 = tickeds \<union> untickeds"
proof -
  have "TTT1 \<subseteq> tickeds \<union> untickeds"
    apply (auto simp add: TTTsimps)
    by (metis Suc_inject Suc_lessI hd_drop_conv_nth length_append_singleton less_trans_Suc not_less nth_take take_all take_hd_drop) 
  moreover have "untickeds \<subseteq> TTT1"
    by (auto simp add: TTTsimps)
  moreover have "tickeds \<subseteq> TTT1"
    by (auto simp add: TTTsimps)
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
      by (auto simp add: AFE TTTsimps)
    moreover have "A \<inter> tickeds = {}"
      by (auto simp add: AFE TTTsimps)
    ultimately show "A \<subseteq> untickeds"
      by (rule untickedTTT1) 
  next
    case AFR
    have "A \<subseteq> TTT1"
      by (auto simp add: AFR TTTsimps)
    moreover have "A \<inter> tickeds = {}"
      by (auto simp add: AFR TTTsimps)
    ultimately show "A \<subseteq> untickeds"
      by (rule untickedTTT1)
  qed
qed

lemma TTTsUntickedsFEFR: "TTTs \<inter> untickeds = FE \<union> FR"
  apply(auto simp add: coveringRegions TTTsimps)
  by (metis Suc_lessI le_eq_less_or_eq take_Suc_conv_app_nth take_all)

lemma TTTsTickedsTI: "TTTs \<inter> tickeds = TI"
  by (auto simp add: coveringRegions TTTsimps)

subsubsection \<open> Refusal Trace Structure \<close>

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

lemma tttracesFRITTT1: "tttracesFRI P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT1)

lemma tttracesFRPTTT1: "tttracesFRP P \<subseteq> (TTT1::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT1)

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

lemma tttracesFRITTT2: "tttracesFRI P \<subseteq> (TTT2::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT2)

lemma tttracesFRPTTT2: "tttracesFRP P \<subseteq> (TTT2::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT2)
  
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

lemma tttracesFRITTT3: "tttracesFRI P \<subseteq> (TTT3::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT3)

lemma tttracesFRPTTT3: "tttracesFRP P \<subseteq> (TTT3::'\<theta> oreftrace set)"
  by (metis Un_subset_iff tttracesFR.simps tttracesFRTTT3)

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

section \<open> Healthiness conditions \<close>

subsection \<open> TT0 \<close>

lemma TCtttracesFEEmpty: "P is TC \<Longrightarrow> [] \<in> tttracesFE P"
proof -
  assume "P is TC"
  then obtain R S T
    where 1: "P = \<^bold>R (R \<turnstile> (S \<or> \<U>(true, []) \<or> T ;; \<U>(true, [])) \<diamondop> T ;; II\<^sub>t)"
    using TCform by blast
  show ?thesis
    apply(simp add: 1)
    apply(rdes_calc)
    apply(rel_simp)
    using tockificationsEmptyS by blast
qed

lemma TCtttracesTT0: "P is TC \<Longrightarrow> TT0(tttraces(P))"
proof -
  assume "P is TC"
  then have "[] \<in> tttracesFE P"
    using TCtttracesFEEmpty by blast
  then have "[] \<in> tttraces P"
    by simp
  then show "TT0(tttraces(P))"
    using TT0_def by blast
qed

subsection \<open> TT1 \<close>

text \<open> Not proven since we do not in general expect a UTP reactive theory to have prefix closure.
It is known that this is not required for the algebraic theory. Whilst this could be established via
additional healthiness conditions as in other UTP theories, this is an orthogonal concern to the
rest of the UTP theory. \<close>

subsection \<open> TT2 \<close>

text \<open> Should be doable -- need to think about shape of induction argument and required supporting
lemmata \<close>

subsection \<open> TT3 \<close>

lemma tockificationsTT3i: "s \<in> tockifications t \<Longrightarrow> TT3i s"
proof (simp add: TTsimps; rule; rule; rule; rule; induction t arbitrary: s \<rho> \<sigma> X)
  case Nil
  then show ?case
    by auto
next
  case (Cons x t)
  then show "reftock \<notin> X" proof (cases x)
    case (Tock Y)
    then obtain w Y' where 1: "\<rho> @ [oref X, otock] @ \<sigma> = oref Y' # otock # w" and 2: "(Y' = torefset Y) \<or> (Y' = torefset Y \<union> {reftick})"  and 3: "w \<in> tockifications t"
      using Cons by auto
    moreover have "Y' \<subseteq> torefset Y \<union> {reftick}"
      using "2" by blast
    ultimately show ?thesis
    proof (cases "\<rho>")
      case Nil
      then show ?thesis
        using "1" "2" by force
    next
      case 4: (Cons y tl)
      then have "y = oref Y'"
        using 1 by fastforce
      then show ?thesis
        using 1 3 4
        by (metis (no_types, lifting) Cons.IH append_eq_Cons_conv list.inject oevent.simps(6))
    qed
  next
    case (Evt e)
    then obtain w where 1: "\<rho> @ [oref X, otock] @ \<sigma> = oevt e # w" and 2: "w \<in> tockifications t"
      using Cons by auto
    then show ?thesis
      by (metis (no_types, lifting) Cons.IH Cons_eq_append_conv append_Cons nth_append_length oevent.distinct(1))
  qed
qed

lemma tockificationsCases: "xs \<in> tockifications s \<Longrightarrow>
  (xs = []) \<or> (\<exists> e ys. xs = oevt e # ys) \<or> (\<exists> X ys. xs = oref X # otock # ys)"
proof (cases s)
  case Nil
  assume "xs \<in> tockifications s"
  then have "xs = []"
    by (simp add: Nil tockificationsEmpty)
  then show ?thesis
    by blast
next
  case (Cons a s')
  assume 1: "xs \<in> tockifications s"
  then show ?thesis proof (cases a)
    case (Tock X)
    then have "\<exists> ys Y'. xs = oref Y' # otock # ys"
      using Tock local.Cons 1 by fastforce
    then show ?thesis
      by fastforce
  next
    case (Evt e)
    then have "\<exists> ys. xs = oevt e # ys"
      using Evt local.Cons 1 by fastforce
    then show ?thesis
      by fastforce
  qed
qed

lemma tockificationsRefSplit: "\<rho> @ oref X # \<sigma> \<in> tockifications s
   \<Longrightarrow> \<exists> s' s''. (s = s' @ s'')
               \<and> (\<rho> \<in> tockifications s')
               \<and> (oref X # \<sigma> \<in> tockifications s'')"
proof (induction \<rho> arbitrary: s rule: length_induct)
  case a: (1 \<rho>)
  assume b: "\<rho> @ oref X # \<sigma> \<in> tockifications s"
  then consider "\<rho> @ oref X # \<sigma> = []" | "\<exists> e ys. \<rho> @ oref X # \<sigma> = oevt e # ys" | "\<exists> Y ys. \<rho> @ oref X # \<sigma> = oref Y # otock # ys"
    by (meson tockificationsCases)
  then show ?case proof (cases)
    case 1
    then show ?thesis
      by blast
  next
    case 2
    then obtain e ys where "\<rho> @ oref X # \<sigma> = oevt e # ys"
      by auto
    then obtain \<rho>' where 6: "\<rho> = oevt e # \<rho>'" and 5: "length \<rho>' < length \<rho>"
      by (metis Prefix_Order.strict_prefixI' Prefix_Order.strict_prefix_simps(3) length_Cons lessI list.size(3) neq_Nil_conv nth_Cons_0 nth_append_length oevent.distinct(1))
    then obtain s' where 2: "s = Evt e # s'" and "\<rho>' @ oref X # \<sigma> \<in> tockifications s'"
      using b tockificationsCaseEvt by force
    then obtain s'' s''' where "s' = s'' @ s'''" and 7: "\<rho>' \<in> tockifications s''" and 4: "oref X # \<sigma> \<in> tockifications s'''"
      using a 5 by blast
    moreover then have "s = (Evt e # s'') @ s'''"
      by (simp add: 2)
    moreover have "oevt e # \<rho>' \<in> tockifications (Evt e # s'')"
      using 7 by simp
    ultimately show ?thesis
      using 6 by blast
  next
    case 3
    then obtain Y ys where 4: "\<rho> @ oref X # \<sigma> = oref Y # ys"
      by auto
    then show ?thesis proof (cases "length \<rho>")
      case 0
      then show ?thesis
        by (metis append_Nil b insert_iff length_0_conv tockifications.simps(3))
    next
      case (Suc nat)
      then obtain \<rho>' where 6: "\<rho> = oref Y # \<rho>'" and 5: "length \<rho>' < length \<rho>"
        by (metis 4 Zero_not_Suc hd_append length_0_conv length_Suc_conv lessI list.sel(1))
      then obtain t' s' Y' where 7: 
          "(Y = torefset Y') \<or> (Y = torefset Y' \<union> {reftick})" and 8: "s = Tock Y' # t'" and 9: "\<rho>' @ oref X # \<sigma> = otock # s'" and 10: "s' \<in> tockifications t'"
        by (metis append_Cons b tockificationsCaseTock'')
      obtain \<rho>'' where 11: "\<rho>' = otock # \<rho>''"
        by (metis "9" hd_Cons_tl hd_append list.sel(1) oevent.distinct(3))
      then have 12: "\<rho>'' @ oref X # \<sigma> = s'"
        using "9" by force
     obtain s'' s''' where "t' = s'' @ s'''" and 13: "\<rho>'' \<in> tockifications s''" and 14: "oref X # \<sigma> \<in> tockifications s'''"
       by (metis 11 12 10 6 a.IH length_Cons not_less_eq not_less_iff_gr_or_eq)
      moreover then have "s = (Tock Y' # s'') @ s'''"
        by (simp add: "8")
      moreover have "oref Y #  \<rho>' \<in> tockifications (Tock Y' # s'')"
        apply(simp add: 11 13)
        using 7 by force
      ultimately show ?thesis
        using "6" by blast
    qed
  qed
qed

lemma tockificationsTT4: "TT4(tockifications t)"
proof (clarsimp simp add: TTsimps)
  fix \<rho> X \<sigma> s
  assume 2: "\<rho> @ oref X # \<sigma> \<in> tockifications s"
  then obtain s' s'' where 3: "s = s' @ s''"
                       and 4: "\<rho> \<in> tockifications s'"
                       and 5: "oref X # \<sigma> \<in> tockifications s''"
    by (meson tockificationsRefSplit)
  then obtain s''' \<sigma>' Y
      where 6: "(X = torefset Y) \<or> (X = torefset Y \<union> {reftick})"
        and 7: "s'' = Tock Y # s'''"
        and 8: "\<sigma> = otock # \<sigma>'"
        and 9: "\<sigma>' \<in> tockifications s'''"
    by (meson tockificationsCaseTock'')
  then have "oref (insert reftick X) # otock # \<sigma>' \<in> tockifications s''"
    by (simp add: 4; meson insert_absorb2)
  then show "\<rho> @ oref (insert reftick X) # \<sigma> \<in> tockifications s"
    using "3" "4" "8" tockificationsAppend by fastforce
qed

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
    and "tttracesFRP P \<inter> FE = {}"
    and "tttracesFRI P \<inter> FE = {}"
    and "tttracesTI P \<inter> FE = {}"
    and "tttracesFE P \<inter> FR = {}"
    and "tttracesFE P \<inter> FRP = {}"
    and "tttracesFE P \<inter> FRI = {}"
    and "tttracesTI P \<inter> FR = {}"
    and "tttracesTI P \<inter> FRP = {}"
    and "tttracesTI P \<inter> FRI = {}"
    and "tttracesFE P \<inter> TI = {}"
    and "tttracesFR P \<inter> TI = {}"
  apply(auto simp add: TTTsimps)
  using tockificationsNoTI tockificationsNoFR
  by (force+)

lemma tttracesRegionSubsets:
  shows "tttracesFE P \<subseteq> FE"
    and "tttracesFRI P \<subseteq> FRI"
    and "tttracesFRP P \<subseteq> FRP"
    and "tttracesFR P \<subseteq> FR"
    and "tttracesTI P \<subseteq> TI"
proof -
  have "tttracesFE P = tttracesFE P \<inter> TTTs"
    using tockificationsTTTs by fastforce
  thus "tttracesFE P \<subseteq> FE"
    by (metis Int_Un_eq(3) Un_Int_eq(2) coveringRegions distinctRegions(3) distrib_lattice_class.inf_sup_distrib1 semilattice_inf_class.inf.orderI tttracesDisjointRegions(11) tttracesDisjointRegions(5))
next
  have "tttracesFRI P = tttracesFRI P \<inter> TTTs"
    by (metis lattice_class.inf_sup_aci(2) semilattice_inf_class.inf.absorb1 tttracesFRITTT1 tttracesFRITTT2 tttracesFRITTT3)
  also have "\<dots> \<subseteq> FRI"
    apply (auto simp add: FRI_def)
    by (metis finalrefsetTock)
  finally show "tttracesFRI P \<subseteq> FRI"
    by blast
next
  have "tttracesFRP P = tttracesFRP P \<inter> TTTs"
    by (metis lattice_class.inf_sup_aci(2) semilattice_inf_class.inf.absorb1 tttracesFRPTTT1 tttracesFRPTTT2 tttracesFRPTTT3)
  also have "\<dots> \<subseteq> FRP"
    apply (auto simp add: FRP_def)
    by (metis finalrefsetTock)
  finally show "tttracesFRP P \<subseteq> FRP"
    by blast
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

lemma tttracesFRSubregions:
  shows "tttracesFR P \<inter> FRI = tttracesFRI P"
    and "tttracesFR P \<inter> FRP = tttracesFRP P"
proof -
  have 1: "tttracesFRP P \<inter> FRI = {}"
    by (metis disjointFR disjoint_iff_not_equal in_mono tttracesRegionSubsets(3))
  have "tttracesFR P \<inter> FRI = (tttracesFRI P \<union> tttracesFRP P) \<inter> FRI"
    by simp
  also have "\<dots> = ((tttracesFRI P \<inter> FRI) \<union> (tttracesFRP P \<inter> FRI))"
    by blast
  also have "\<dots> = tttracesFRI P"
    apply(simp only: 1)
    by (metis boolean_algebra_cancel.sup0 semilattice_inf_class.inf.absorb1 tttracesRegionSubsets(2))
  finally show "tttracesFR P \<inter> FRI = tttracesFRI P" .
next
  have 2: "tttracesFRI P \<inter> FRP = {}"
    by (metis disjointFR disjoint_iff_not_equal in_mono tttracesRegionSubsets(2))
  have "tttracesFR P \<inter> FRP = (tttracesFRI P \<union> tttracesFRP P) \<inter> FRP"
    by simp
  also have "\<dots> = ((tttracesFRI P \<inter> FRP) \<union> (tttracesFRP P \<inter> FRP))"
    by blast
  also have "\<dots> = tttracesFRP P"
    apply(simp only: 2)
    by (metis bounded_semilattice_sup_bot_class.sup_bot_left semilattice_inf_class.inf.absorb1 tttracesRegionSubsets(3))
  finally show "tttracesFR P \<inter> FRP = tttracesFRP P" .  
qed

lemma tttracesSubregions:
  shows "tttraces P \<inter> FE = tttracesFE P"
    and "tttraces P \<inter> FRI = tttracesFRI P"
    and "tttraces P \<inter> FRP = tttracesFRP P"
    and "tttraces P \<inter> FR = tttracesFR P"
    and "tttraces P \<inter> TI = tttracesTI P"
proof -
  have "tttraces P \<inter> FE = TTTs \<inter> tttraces P \<inter> FE"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FE)
                        \<union> (tttracesFR P \<inter> FE)
                        \<union> (tttracesTI P \<inter> FE))"
    by (simp add: boolean_algebra_cancel.inf1 distrib_lattice_class.inf_sup_distrib2)
  also have "\<dots> = TTTs \<inter> tttracesFE P \<inter> FE"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesFE P"
    by (metis Int_absorb2 Int_subset_iff semilattice_inf_class.inf.absorb_iff2 tockificationsTTTs tttracesFETockifications tttracesRegionSubsets(1))
  finally show "tttraces P \<inter> FE = tttracesFE P"
    by blast
next
  have "tttraces P \<inter> FRP = TTTs \<inter> tttraces P \<inter> FRP"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FRP)
                        \<union> (tttracesFR P \<inter> FRP)
                        \<union> (tttracesTI P \<inter> FRP))"
    by (simp add: Int_Un_distrib2 semilattice_inf_class.inf.assoc)
  also have "\<dots> = TTTs \<inter> tttracesFRP P \<inter> FRP"
    apply (auto simp only: disjointRegions distinctRegions coveringFR tttracesDisjointRegions)
    apply (metis IntI tttracesFRSubregions(2))
    by (metis IntD1 tttracesFRSubregions(2))
  also have "\<dots> = tttracesFRP P"
    by (metis (no_types, lifting) FRP_def semilattice_inf_class.inf.assoc semilattice_inf_class.inf.right_idem semilattice_inf_class.inf_commute tttracesFRSubregions(2))
  finally show "tttraces P \<inter> FRP = tttracesFRP P"
    by blast
next
  have "tttraces P \<inter> FRI = TTTs \<inter> tttraces P \<inter> FRI"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FRI)
                        \<union> (tttracesFR P \<inter> FRI)
                        \<union> (tttracesTI P \<inter> FRI))"
    by (simp add: Int_Un_distrib2 semilattice_inf_class.inf.assoc)
  also have "\<dots> = TTTs \<inter> tttracesFRI P \<inter> FRI"
    apply (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
    apply (metis IntI tttracesFRSubregions(1))
    by (metis IntD1 tttracesFRSubregions(1))
  also have "\<dots> = tttracesFRI P"
    by (metis (no_types, lifting) FRI_def semilattice_inf_class.inf.assoc semilattice_inf_class.inf.right_idem semilattice_inf_class.inf_commute tttracesFRSubregions(1))
  finally show "tttraces P \<inter> FRI = tttracesFRI P"
    by blast
next
  have "tttraces P \<inter> FR = TTTs \<inter> tttraces P \<inter> FR"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> FR)
                        \<union> (tttracesFR P \<inter> FR)
                        \<union> (tttracesTI P \<inter> FR))"
    by (simp add: Int_Un_distrib2 semilattice_inf_class.inf.assoc)
  also have "\<dots> = TTTs \<inter> tttracesFR P \<inter> FR"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesFR P"
    by (metis (no_types, lifting) FR_def Int_absorb1 Int_absorb2 Int_subset_iff tttracesRegionSubsets(4))
  finally show "tttraces P \<inter> FR = tttracesFR P"
    by blast
next
  have "tttraces P \<inter> TI = TTTs \<inter> tttraces P \<inter> TI"
    using TTTStructure by blast
  also have "\<dots> = TTTs \<inter> ((tttracesFE P \<inter> TI)
                        \<union> (tttracesFR P \<inter> TI)
                        \<union> (tttracesTI P \<inter> TI))"
    by (simp add: distrib_lattice_class.inf_sup_distrib2 semilattice_inf_class.inf.assoc)
  also have "\<dots> = TTTs \<inter> tttracesTI P \<inter> TI"
    by (auto simp only: disjointRegions distinctRegions tttracesDisjointRegions)
  also have "\<dots> = tttracesTI P"
    by (metis (no_types, lifting) TI_def Int_absorb1 Int_absorb2 Int_subset_iff tttracesRegionSubsets(5))
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


lemma tttracesEqFR:
  assumes "B \<subseteq> (TTTs::'\<theta> oreftrace set)"
      and "tttracesFE P = B \<inter> FE"
      and "tttracesFRI P = B \<inter> FRI"
      and "tttracesFRP P = B \<inter> FRP"
      and "tttracesTI P = B \<inter> TI"
    shows "tttraces P = B"
proof (rule tttracesEq)
  show "B \<subseteq> (TTTs::'\<theta> oreftrace set)" "tttracesFE P = B \<inter> FE" "tttracesTI P = B \<inter> TI"
    using assms by auto
next
  show "tttracesFR P = B \<inter> FR"
    by (metis Int_Un_distrib assms(3) assms(4) coveringFR tttracesFR.simps)
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

lemma tttracesEqFRRem:
  assumes "tttracesFE P = (B - FR - TI::'\<theta> oreftrace set)"
      and "tttracesFRI P = B \<inter> FRI"
      and "tttracesFRP P = B \<inter> FRP"
      and "tttracesTI P = B \<inter> TI"
    shows "tttraces P = B"
proof (rule tttracesEqRem)
  show "tttracesFE P = (B - FR - TI)" "tttracesTI P = B \<inter> TI"
    using assms by auto
next
  show "tttracesFR P = B \<inter> FR"
    by (metis Int_Un_distrib assms(2) assms(3) coveringFR tttracesFR.simps)
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