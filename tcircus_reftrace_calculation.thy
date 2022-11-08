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


lemma "peri\<^sub>R Stop\<^sub>U = \<E>(true, [], {}, false)"
  by (rdes_eq)

lemma "$pat\<acute> \<sharp> (\<E>(true, [], {}, false) :: '\<theta> ttcsp)"
  apply pred_auto
  oops

lemma "taut ((\<E>(true, [], {}, false) :: '\<theta> ttcsp) \<Rightarrow> \<not>$pat\<acute>)"
  apply(pred_auto)
  done

lemma "$pat\<acute> \<sharp> (\<E>(true, [], {}, true))"
  apply(pred_simp)
  done

lemma "$pat\<acute> \<sharp> peri\<^sub>R Stop"
  apply(rdes_simp)
  apply(rel_simp)
  done

lemma "$pat\<acute> \<sharp> (\<E>(true, [], {}, true) :: '\<theta> ttcsp)"
  apply pred_auto
  done

lemma "tttraces (Stop\<^sub>U::'\<theta> ttcsp) = {[]} \<union> {[oref X] | X . True}" (is "?l = ET \<union> ?r2")
proof (rule tttracesEqFRRem)
  have "(ET \<union> ?r2) - FR - TI = ET"
    by (auto simp add: FE_def FR_def TI_def TTT1_def TTT2_def TTT3_def)
  moreover have "tttracesFE Stop\<^sub>U = ET"
    apply(rdes_simp)
    by (rel_auto)
  ultimately show "tttracesFE Stop\<^sub>U = (ET \<union> ?r2) - FR - TI"
    by auto
next
  have "tttracesFRP (Stop\<^sub>U::'\<theta> ttcsp) = 
    { s@[oref (finalrefset True refterm X)]
    | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
     t = [] \<and> s \<in> tockifications t}"
    apply(rdes_simp cls: patient_def)
    apply(rel_auto)
    done
  also have "\<dots> = {[oref X] | X . reftock \<notin> X}"
    apply(simp add: FRP_def)
    by (metis (full_types, hide_lams) finalrefsetRange finalrefsetTock)
  also have "\<dots> = ?r2 \<inter> FRP"
    by(auto simp add: TTTsimps)
  finally have "tttracesFRP (Stop\<^sub>U::'\<theta> ttcsp) = (?r2\<inter>FRP)" .
  moreover have "(ET \<union> ?r2) \<inter> FRP = ?r2 \<inter> FRP"
    using coveringFR distinctRegions(1) by auto
  ultimately show "tttracesFRP Stop\<^sub>U = (ET \<union> ?r2) \<inter> FRP"
    by blast

next
  have "tttracesFRI (Stop\<^sub>U::'\<theta> ttcsp) = 
    { s@[oref (finalrefset False refterm X)]
    | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
     t = [] \<and> s \<in> tockifications t}"
    apply(rdes_simp cls: patient_def)
    apply(rel_auto)
    done
  also have "\<dots> = {[oref X] | X . reftock \<in> X}"
    apply(simp add: FRI_def)
    by (metis (full_types, hide_lams) finalrefsetRange finalrefsetTock)
  also have "\<dots> = ?r2 \<inter> FRI"
    by(auto simp add: TTTsimps)
  finally have "tttracesFRI (Stop\<^sub>U::'\<theta> ttcsp) = (?r2\<inter>FRI)" .
  moreover have "(ET \<union> ?r2) \<inter> FRI = ?r2 \<inter> FRI"
    using coveringFR distinctRegions(1) by auto
  ultimately show "tttracesFRI Stop\<^sub>U = (ET \<union> ?r2) \<inter> FRI"
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
  "finalRefTockSequence X t = (\<exists> ta Y Ti. (t = ta @ [oref (torefset Y \<union> Ti)]) \<and> Ti \<subseteq> {reftick} \<and> Y \<subseteq> X \<and> tockSequence X ta)"

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

lemma finalrefsetPatientForm: "(\<exists>refterm. u = s @ [oref (finalrefset True refterm X)])
                      = (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick})"
proof -
  have "(\<exists>refterm. u = s @ [oref (finalrefset True refterm X)])
      = ( (u = s @ [oref (finalrefset True False X)])
        \<or> (u = s @ [oref (finalrefset True True X)]) )"
    by (metis (full_types))
  also have "\<dots> = ( (u = s @ [oref (torefset X \<union> {})])
                  \<or> (u = s @ [oref (torefset X \<union> {reftick})]) )"
    by simp
  also have "\<dots> = (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick})"
    by blast
  finally show ?thesis
    by blast
qed

lemma tttracesFRStop: "tttracesFR Stop = {t::'\<theta> oreftrace. finalRefTockSequence UNIV t}" (is "?l = ?r")
proof -
  have "?l = { s@[oref (finalrefset True refterm X)] | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
                  t \<in> tocks UNIV
                \<and> s \<in> tockifications t}"
    apply(rdes_simp cls: patient_def)
    apply(rel_auto)
    done
  also have "... = { s@[oref (finalrefset True refterm X)] | (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
                    tockSequence UNIV s}"
    using tockSequenceTockifications tockSeqTockificationTocks by force
  also have "... = {s @ [oref (torefset X \<union> Ti)] | X s Ti .
              Ti \<subseteq> {reftick} \<and> tockSequence UNIV s}"
  proof -
     {
        fix u
        have "(\<exists> X refterm s.
              (u::'\<theta> oreftrace) = s @ [oref (finalrefset True refterm X)] \<and> tockSequence UNIV s)
            = (\<exists> X s. (\<exists> refterm.
               u = s @ [oref (finalrefset True refterm X)]) \<and> tockSequence UNIV s)" (is "?l1 = ?r2")
          by blast
        also have "\<dots> = (\<exists> X s. (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick})
                                \<and> tockSequence UNIV s)"
          by (simp add: finalrefsetPatientForm)
        also have "\<dots> = (\<exists> X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick}
                                \<and> tockSequence UNIV s)" (is "?l3 = ?r3")
          by blast
        finally have "?l1 = ?r3" .
      }
      thus ?thesis by simp
  qed
  also have "... = ?r"
    by (auto simp add: finalRefTockSequence_def)
  finally show ?thesis .
qed

lemma tttracesStop: "tttraces Stop = {t. tockSequence UNIV t \<or> finalRefTockSequence UNIV t}"
  using tttracesFEStop tttracesFRStop tttracesTIStop tttracesCalc by blast

subsection \<open> Internal Choice \<close>

(* Need to properly tackle patience of conjunctions *)

(*
lemma "[oref ({reftock})] \<in> tttraces (\<^bold>R(true  \<turnstile> (\<not> $pat)) \<diamondop> false )"
  apply(rdes_calc)
  apply(rel_auto)
  oops
*)

(*
lemma 
  assumes "P is TC" "Q is TC"
  shows "tttracesFR (P \<sqinter> Q) \<subseteq> tttracesFR P \<union> tttracesFR Q"
proof -
  have "tttracesFR (P \<sqinter> Q) = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> ((peri\<^sub>R P \<or> peri\<^sub>R Q))`)
        \<and>
        (patient (P \<sqinter> Q) t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t}"
    apply(rdes_calc)
    apply(rel_auto)
    done
  also have "\<dots> = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`))
        \<and>
        (patient (P \<sqinter> Q) t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t}"
    apply(rdes_calc)
    apply(rel_auto)
    apply(blast+)
    done
  also have "\<dots> = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`))
        \<and>
        ((patient P t X \<or> patient Q t X) \<longrightarrow> acctock) \<and>
        s \<in> tockifications t}"
    by (simp add: assms patient_disj_eq)
  also have "\<dots> = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`
          \<and>
        ((patient P t X \<or> patient Q t X) \<longrightarrow> acctock) \<and>
        s \<in> tockifications t)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)
        \<and>
        ((patient P t X \<or> patient Q t X) \<longrightarrow> acctock) \<and>
        s \<in> tockifications t
        )}"
    apply(rdes_calc)
    apply(rel_auto)
    apply(blast+)
    done
  also have "\<dots> = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`
          \<and>
        (patient P t X \<longrightarrow> acctock) \<and>
        (patient Q t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)
        \<and>
        (patient P t X \<longrightarrow> acctock) \<and>
        (patient Q t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t
        )}"
    apply(rdes_calc)
    done
  also have "\<dots> \<subseteq> {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`
          \<and>
        (patient P t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)
        \<and>
        (patient Q t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t
        )}"
    apply(rel_auto)
    apply(blast+)
    done
  also have "\<dots> = {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`
          \<and>
        (patient P t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t))
        } \<union> {s @ [oref (finalrefset acctock refterm X)]
        | t X acctock refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)
        \<and>
        (patient Q t X \<longrightarrow> acctock) \<and>
        s \<in> tockifications t
        )}"
    apply(rel_auto)
    apply(blast+)
    done
  also have "... = tttracesFR P \<union> tttracesFR Q"
    apply(rdes_calc)
    apply(rel_auto)
    done
  finally show "tttracesFR (P \<sqinter> Q) \<subseteq> tttracesFR P \<union> tttracesFR Q" .
qed

lemma 
  assumes "P is TC" "Q is TC"
  shows "tttracesFR P \<subseteq> tttracesFR (P \<sqinter> Q)"
  apply(simp add: patient_def)
  apply(rdes_calc)
  apply(rel_auto)
  oops
*)

lemma 
  assumes "P is TC" "Q is TC" "\<And> t X. patient P t X = patient Q t X"
  shows "tttraces (P \<sqinter> Q) = tttraces P \<union> tttraces Q"
    (*
       = tttraces (\<^bold>R(pre\<^sub>R P \<and> pre\<^sub>R Q \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))
       \<union> tttraces (\<^bold>R(pre\<^sub>R P \<and> pre\<^sub>R Q \<turnstile> peri\<^sub>R Q \<diamondop> post\<^sub>R Q))"
      (is "tttraces ?PQ = tttraces ?P \<union> tttraces ?Q")
    *)
proof (rule tttracesEqFR)
  show "tttraces P \<union> tttraces Q \<subseteq> TTTs"
    using TTTStructure
    by blast
next
  have "tttracesFE (P \<sqinter> Q) = tttracesFE P \<union> tttracesFE Q"
    apply(rdes_calc)
    apply(rel_auto)
    by (blast+)
    (* by (auto; rel_simp; blast) *)
  thus "tttracesFE (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FE"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(1))
next
  have "tttracesFRP (P \<sqinter> Q) = tttracesFRP P \<union> tttracesFRP Q"
    apply(rdes_calc)
    apply(rel_auto)
    apply(blast+)
    done
  thus "tttracesFRP (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FRP"
    by (metis Int_Un_distrib2 tttracesSubregions(3))
next
  have "tttracesFRI (P \<sqinter> Q) = tttracesFRI P \<union> tttracesFRI Q"
    apply(rdes_simp)
    apply(simp only: patient_disj_eq assms)
    apply(rel_auto)
    apply blast
    apply blast
    (* These rely on assumption 3 *)    
    apply blast
    apply blast
    done
  thus "tttracesFRI (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FRI"
    by (metis Int_Un_distrib2 tttracesSubregions(2))
  (*  by (metis Int_Un_distrib2 tttracesSubregions(3)) *)
  (*
  have "tttracesFRP (P \<sqinter> Q) = {s @ [oref (finalrefset True refterm X)]
        | t X refterm s.
         (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> ((peri\<^sub>R P \<or> peri\<^sub>R Q))`)
        \<and>
        s \<in> tockifications t}"
    apply(rdes_calc)
    apply(rel_auto)
    done
  also have "\<dots> = {s @ [oref (finalrefset True refterm X)]
        | t X refterm s.
         (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> ((peri\<^sub>R P)
                                                              \<or> (peri\<^sub>R Q))`)
        \<and>
        s \<in> tockifications t}"
    apply(rdes_calc)
    done
  also have "\<dots> = {s @ [oref (finalrefset True refterm X)]
        | t X refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`)
        \<or> (\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)) \<and>
        s \<in> tockifications t}"
    apply(rdes_calc)
    apply(rel_auto)
    apply(blast+)
    done
  also have "\<dots> = {s @ [oref (finalrefset True refterm X)]
        | t X refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`
          \<and>
        s \<in> tockifications t))
        } \<union> {s @ [oref (finalrefset True refterm X)]
        | t X refterm s.
         ((\<not> `\<not> [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R Q)`)
        \<and>
        s \<in> tockifications t
        )}"
    apply(rdes_calc)
    apply(rel_auto)
    apply(blast+)
    done
  also have "\<dots> = tttracesFRP P \<union> tttracesFRP Q"
    apply(rdes_calc)
    apply(rel_auto)
    done
  finally have "tttracesFRP (P \<sqinter> Q) = tttracesFRP P \<union> tttracesFRP Q" .
  thus "tttracesFR (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> FR"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(2))
  *)
next
  have 1: "(P \<sqinter> Q) is TC"
    by (simp add: assms TC_closed_disj)
  have "tttracesTI (P \<sqinter> Q) = tttracesTI P \<union> tttracesTI Q"
    apply (rdes_simp)
    apply(rel_auto)
    by blast+
  thus "tttracesTI (P \<sqinter> Q) = (tttraces P \<union> tttraces Q) \<inter> TI"
    by (metis distrib_lattice_class.inf_sup_distrib2 tttracesSubregions(5))
qed

subsection \<open> Refinements \<close>

lemma finalrefsetInjective: "(finalrefset p refterm X = finalrefset p' refterm' X')
                           = ((p = p') \<and> (refterm = refterm') \<and> (X = X'))"
  by (cases p; cases p'; cases refterm; cases refterm'; auto)

lemma "P is NRD \<Longrightarrow> (P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
  by (simp add: NRD_is_RD RD_reactive_tri_design)

lemma TCform:
  assumes "P is TC"
  shows "P = \<^bold>R (pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<or> \<U>(true, []) \<or> post\<^sub>R P ;; \<U>(true, [])) \<diamondop> post\<^sub>R P ;; II\<^sub>t)" (is "P = ?r")
proof -
  have 1: "P is NRD"
    using TC_implies_NRD assms by auto    
  have 2: "pre\<^sub>R P is TRC" "peri\<^sub>R P is TRR" "post\<^sub>R P is TRF"
    using TC_inner_closures  assms by blast+

  have "P = \<^bold>R(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    using 1 by (simp add: NRD_is_RD RD_reactive_tri_design)
  then show ?thesis
    using 2 by (metis Healthy_if TC_rdes TRF_implies_TRR assms)
qed

lemma TCformempty: "[] \<in> tttracesFE (\<^bold>R (P \<turnstile> (Q \<or> \<U>(true, []) \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t))"
  apply(rdes_calc)
  apply(rel_simp)
  using tockificationsEmptyS by blast

lemma TCtttracesFEEmpty: "P is TC \<Longrightarrow> [] \<in> tttracesFE P"
  by (metis TCform TCformempty)

lemma tttracesFERefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFE Q \<subseteq> tttracesFE P"
  apply(rdes_simp)
  apply(rel_simp)
  by meson

(*
lemma tttracesFRRefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesFR Q \<subseteq> tttracesFR P"
  apply(rdes_simp)
  apply(rel_simp)
  by blast
*)

lemma "(P :: '\<phi> ttcsp) \<sqsubseteq> Q \<Longrightarrow> Q = P \<squnion> Q"
  by (rel_auto)

lemma tttracesTIRefine: "P \<sqsubseteq> Q \<Longrightarrow> tttracesTI Q \<subseteq> tttracesTI P"
  apply(rdes_simp)
  apply(rel_simp)
  by meson

subsection \<open> Wait \<close>

fun otimelength :: "'\<theta> oreftrace \<Rightarrow> nat" where
  "otimelength (otock # xs) = Suc (otimelength xs)" |
  "otimelength (oref X # xs) = otimelength xs" |
  "otimelength (oevt e # xs) = otimelength xs" |
  "otimelength (otick # xs) = otimelength xs" |
  "otimelength [] = 0"

lemma otimelengthFinalRef: "otimelength (xs @ [oref X]) = otimelength xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases a; simp)
qed

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


lemma tttracesFRWait: "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = {t | t. finalRefTockSequence UNIV t \<and> (otimelength t < n)}"
proof - 
  have "tttracesFR (Wait \<guillemotleft>n\<guillemotright>) = {
      s@[oref (finalrefset True refterm X)]
    | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
      t \<in> tocks UNIV \<and> length t < n \<and> s \<in> tockifications t}"
    apply(rdes_simp cls: patient_def)
    apply(rel_auto)
    done
    (* by (smt (z3) Collect_cong) *)
  also have "\<dots> = {
      s@[oref (finalrefset True refterm X)]
    | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
      t \<in> tocks UNIV 
    \<and> otimelength s < n \<and> s \<in> tockifications t}"
    using tocksTimeLength by force
  also have "\<dots> = {
      s@[oref (finalrefset True refterm X)]
    | (t::'\<theta> reftrace) (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
      tockSequence UNIV s
    \<and> otimelength s < n
    \<and> s \<in> tockifications t}"
    using tockSeqTockificationTocks by blast
  also have "\<dots> = {
      s@[oref (finalrefset True refterm X)]
    | (X::'\<theta> set) (refterm::bool) (s::'\<theta> oreftrace).
      tockSequence UNIV s
    \<and> otimelength s < n }"
    using tockSequenceTockifications by blast
  also have "\<dots> = {
      s@[oref (torefset X \<union> Ti)]
    | (X::'\<theta> set) Ti (s::'\<theta> oreftrace).
      Ti \<subseteq> {reftick}
    \<and> tockSequence UNIV s
    \<and> otimelength s < n}"
  proof -
    {
      fix u
      have "(\<exists> X refterm s.
            (u::'\<theta> oreftrace) = s @ [oref (finalrefset True refterm X)] \<and> tockSequence UNIV s \<and> otimelength s < n)
          = (\<exists> X s. (\<exists> refterm.
             u = s @ [oref (finalrefset True refterm X)]) \<and> tockSequence UNIV s \<and> otimelength s < n)" (is "?l1 = ?r2")
        by blast
      also have "\<dots> = (\<exists> X s. (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick})
                              \<and> tockSequence UNIV s \<and> otimelength s < n)"
        by (simp add: finalrefsetPatientForm)
      also have "\<dots> = (\<exists> X Ti s. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick}
                              \<and> tockSequence UNIV s \<and> otimelength s < n)" (is "?l3 = ?r3")
        by blast
      finally have "?l1 = ?r3" .
    }
    thus ?thesis by simp
  qed
  also have "\<dots> = {
      s@[oref (torefset X \<union> Ti)]
    | (X::'\<theta> set) Ti (s::'\<theta> oreftrace).
      Ti \<subseteq> {reftick}
    \<and> tockSequence UNIV s
    \<and> otimelength (s@[oref (torefset X \<union> Ti)]) < n}"
    by (simp add: otimelengthFinalRef)
  also have "\<dots> = { s | s.
    finalRefTockSequence UNIV s \<and> otimelength s < n}"
    by (auto simp add: finalRefTockSequence_def)
  finally show ?thesis .  
qed

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
                                         \<union> {t| t X. finalRefTockSequence UNIV t \<and> (otimelength t < n)}
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
                 \<union> {t | t . finalRefTockSequence (-{e}) t }
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
  have "tttracesFR (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = {s @ [oref (finalrefset True refterm X)]
    | t X refterm s.
      t \<in> tocks (- {e}) \<and> X \<subseteq> -{e}
    \<and> s \<in> tockifications t}"
    apply(rdes_simp cls: patient_def)
    apply(rel_simp)
    by (force)
  also have "\<dots> = {s @ [oref (finalrefset True refterm X)]
    | t X refterm s.
      tockSequence (- {e}) s \<and> X \<subseteq> -{e}
    \<and> s \<in> tockifications t}"
    using tockSeqTockificationTocks by blast
  also have "\<dots> = {s @ [oref (finalrefset True refterm X)]
    | X refterm s.
      tockSequence (- {e}) s \<and> X \<subseteq> -{e}}"
    using tockSequenceTockifications by blast
  also have "\<dots> = {s @ [oref (torefset X \<union> Ti)]
    | X Ti s.
      tockSequence (- {e}) s \<and> Ti \<subseteq> {reftick} \<and> X \<subseteq> -{e}}"
  proof -
    {
      fix u::"'\<phi> oreftrace"
      have "(\<exists> X refterm s.
             u = s @ [oref (finalrefset True refterm X)]
           \<and> tockSequence (-{e}) s \<and> X \<subseteq> -{e})
          = (\<exists> X s. (\<exists> refterm.
             u = s @ [oref (finalrefset True refterm X)])
          \<and> tockSequence (-{e}) s \<and> X \<subseteq> -{e})" (is "?l1 = ?r2")
        by blast
      also have "\<dots> = (\<exists> X s. (\<exists>Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick})
                                 \<and> tockSequence (-{e}) s  \<and> X \<subseteq> -{e})"
        by (simp add: finalrefsetPatientForm)
      also have "\<dots> = (\<exists> X s Ti. u = s @ [oref (torefset X \<union> Ti)] \<and> Ti \<subseteq> {reftick}
                               \<and> tockSequence (-{e}) s \<and> X \<subseteq> -{e})" (is "?l3 = ?r3")
        by blast
      finally have "?l1 = ?r3" .
    }
    thus ?thesis by auto
  qed
  also have "\<dots> = {s | s. finalRefTockSequence (- {e}) s}"
    by (auto simp add: finalRefTockSequence_def)
  finally show "tttracesFR (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?FR" .
next
  show "tttracesTI (DoT \<guillemotleft>e\<guillemotright> :: '\<phi> ttcsp) = ?TI"
    apply (rdes_simp; rel_auto)
    apply (simp add: tocksTockificationsFinal)
    by (meson tocksTockificationsFinalTock)
qed

subsection \<open> Sequential composition \<close>

subsubsection \<open> TI Results \<close>

lemma "tttracesTI (Q) = {t@s| t s. t@[otick] \<in> tttracesTI II \<and> s \<in> tttracesTI Q}"
  apply(simp)
  apply(rdes_simp) 
  by (rel_auto)

lemma "tttracesTI (Q) = {t@s| t s. t@[otick] \<in> tttracesTI Q \<and> s \<in> tttracesTI II}"
  apply(simp)
  apply(rdes_simp)
  apply(rel_auto)
  apply blast
  apply blast
  done

lemma TCtttracesTI:
  assumes "P is TC"
  shows "tttracesTI P = { s @ [otick] | t s .
     `post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$tr,$tr\<acute>,$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>`
               \<and> s \<in> tockifications t}"
  apply (simp add: TCpostconcretify assms)
  apply(rel_auto)
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

(*
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
*)

lemma postRSeqSRD:
  assumes "P is NSRD" "Q is NSRD" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "post\<^sub>R(P ;; Q) = (post\<^sub>R P) ;; (post\<^sub>R Q)"
proof -
  have "post\<^sub>R(P;;Q) = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R Q)"
    using assms by rdes_simp
  also have "\<dots> = (true\<^sub>r \<and> post\<^sub>R P wp\<^sub>r true\<^sub>r \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R Q)"
    by (simp add: assms)
  also have "\<dots> = (post\<^sub>R P ;; post\<^sub>R Q)"
    by pred_auto
  finally show ?thesis .
qed

lemma postRSeqNRD:
  assumes "P is NRD" "Q is NRD" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "post\<^sub>R(P ;; Q) = (post\<^sub>R P) ;; (post\<^sub>R Q)"
proof -
  have "post\<^sub>R(P;;Q) = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R Q)"
    apply(simp add: assms(1-2) NRD_is_RD NRD_composition_wp)
    using assms(1-2) apply(rdes_simp)
    done
  also have "\<dots> = (true\<^sub>r \<and> post\<^sub>R P wp\<^sub>r true\<^sub>r \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R Q)"
    by (simp add: assms)
  also have "\<dots> = (post\<^sub>R P ;; post\<^sub>R Q)"
    by pred_auto
  finally show ?thesis .
qed

lemma postRSeqTC:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "post\<^sub>R(P ;; Q) = (post\<^sub>R P) ;; (post\<^sub>R Q)"
  by (simp add: TC_implies_NRD assms postRSeqNRD)

lemma periRSeqNRD:
  assumes "P is NRD" "Q is NRD" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "peri\<^sub>R(P ;; Q) = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
proof -
  have "peri\<^sub>R(P;;Q) = ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
    apply(simp add: assms(1-2) NRD_is_RD NRD_composition_wp)
    using assms(1-2) apply(rdes_simp)
    done
  also have "\<dots> = (true\<^sub>r \<and> post\<^sub>R P wp\<^sub>r true\<^sub>r \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
    by (simp add: assms)
  also have "\<dots> = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
    by pred_auto
  finally show ?thesis .
qed

lemma periRSeqTC:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "peri\<^sub>R(P ;; Q) = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
  by (simp add: TC_implies_NRD assms periRSeqNRD)

lemma tttracesTITCSeq:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "tttracesTI (P ;; Q) = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q}"
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 3: "pre\<^sub>R(P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wp_rea_def)
  have 2: "post\<^sub>R P is TRF" "post\<^sub>R Q is TRF"
    by (simp_all add: TC_inner_closures(3) assms)
  show ?thesis
    apply(simp only: assms 1 3 TCtttracesTI postRSeqTC)
    apply(simp only: assms TRFTRRSeqExpandTr 2 TRF_implies_TRR)
    apply(rel_auto)
    apply(simp_all add: tockificationsAppend)
    using append_assoc apply blast
    using tockificationsAppend apply fastforce
    done
qed

subsubsection \<open> FE Results \<close>

lemma tttracesFETCSeqSub:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "tttracesFE (P ;; Q) \<subseteq> (  tttracesFE P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q})"
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wp_rea_def)
  show ?thesis
    apply(simp add: assms 3 periRSeqTC postRSeqTC)
    apply(simp add: assms TRFTRRSeqExpandTr 2 TRF_implies_TRR)
    apply(rdes_simp)
    apply(rel_auto)
     apply(auto simp add: tockificationsAppend)
    apply blast
     apply blast
    apply blast
    done
qed

lemma tttracesFETCSeqSup2:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "{t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q} \<subseteq> tttracesFE (P ;; Q)" (is "?l \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wp_rea_def)
  have 4: "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R P) = (\<not> post\<^sub>R P)"
          "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R Q) = (\<not> post\<^sub>R Q)"
    by (meson "2" tfin_theory.utp_bottom utp_pred_laws.compl_le_compl_iff utp_pred_laws.sup.absorb2)+
  have 5: "(\<^U>(\<not> R1 true) \<or> (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)) = (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)"
    by (metis "2"(2) "2"(3) tfin_theory.bottom_lower trel_theory.bottom_lower utp_pred_laws.compl_le_compl_iff utp_pred_laws.le_iff_sup utp_pred_laws.le_inf_iff)
  {
    fix x
    assume "(x \<in> ?l)" 
    then obtain t s where "x = t@s" "t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q"
      by blast
    then obtain u w where "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
                "t \<in> tockifications u"
                "\<not>`((\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
                "s \<in> tockifications w"
      by auto
    then have "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
              "\<not>`(\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
              "t@s \<in> tockifications (u@w)"
      by (smt (z3) mem_Collect_eq tockificationsAppend)+
    then have "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q \<or> post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)`"
              "t@s \<in> tockifications (u@w)"
    proof -
      assume 7: "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      assume 8: "\<not>`(\<not>peri\<^sub>R Q \<and> \<not>post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      from 7 8 show "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q \<or> post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)`"
        apply(rdes_calc)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
    qed
    then have "\<not>`\<not>((post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                 \<or> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`"
              "t@s \<in> tockifications (u@w)"
    proof -
      assume "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q \<or> post\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)`"
      thus "\<not>`\<not>((post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                 \<or> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`"      
        by (metis subst_disj utp_pred_laws.inf_sup_distrib1)
    qed
    then have "\<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                 \<or> ((post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`"
          "t@s \<in> tockifications (u@w)"
    proof -
      (*assume "\<not>`\<not>((post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                 \<or> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`" *)
      have "(post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
        apply(simp add: TRFTRRSeqExpandTr 1 2)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
      moreover have "(post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)"
        apply(simp add: TRFTRRSeqExpandTr 1 2 TRF_implies_TRR)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
      ultimately have "((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<or> (post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> ((post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>) \<or> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))"
         by (metis utp_pred_laws.sup_mono)
      then show "\<not>`\<not>((post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                 \<or> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> post\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))` \<Longrightarrow> \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                     \<or> ((post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`"
        by (smt (z3) taut_conj_elim utp_pred_laws.compl_sup utp_pred_laws.le_iff_sup)
    qed
    then have "\<exists> u w. \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                      \<or> ((post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`
                  \<and> x \<in> tockifications (u@w)"
      by (metis \<open>x = t @ s\<close>)
    then have "\<exists> u w. \<not>`\<not>(
                        (peri\<^sub>R P \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                      \<or> ((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>)
                      \<or> ((post\<^sub>R P ;; post\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))`
                  \<and> x \<in> tockifications (u@w)"
      apply(rel_auto)
      apply(blast)+
      done
    then have "x \<in> tttracesFE (P ;; Q)"
      apply rdes_calc
      apply(simp add: assms 1 3 periRSeqTC postRSeqTC)
      apply(rel_auto)
      apply blast+
      done
  }
  then show ?thesis
    by (smt (z3) subsetI)
qed

lemma tttracesFESubTCSeq:
  assumes "(P::'\<theta> ttcsp) is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "(tttracesFE P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q}) \<subseteq> tttracesFE (P ;; Q)" (is "(?l1 \<union> ?l2) \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wpR_R1_right wp_rea_true)
  have "?l1 = {s | s t . s \<in> tockifications t \<and> (\<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` \<or> \<not>`\<not>post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`) }"
    apply(simp add: TCpostconcretify TCpericoncretify assms)
    by (rel_auto)
  also have "\<dots> = {s | s t . s \<in> tockifications t \<and> \<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` }
               \<union> {s | s t . s \<in> tockifications t \<and> \<not>`\<not>post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>` }"
            (is "\<dots> = ?l1a \<union> ?l1b")
    by auto
  finally have 4: "?l1 = ?l1a \<union> ?l1b" .
  have "?l1b = {t |t . t@[otick] \<in> tttracesTI P}"
    apply(auto simp add: TCpostconcretify TCpericoncretify assms)
    apply(rel_auto)+
    done
  moreover have "[] \<in> tttracesFE Q"
    using assms TCtttracesFEEmpty by blast
  ultimately have 5: "?l1b \<subseteq> ?l2"
    by (smt (z3) Collect_mono_iff append_Nil2)
  from 4 5 have 6: "?l1 \<union> ?l2 = ?l1a \<union> ?l2"
    by auto
  moreover have "?l1a \<subseteq> ?r"
    apply(simp add:  assms 3)
    apply(simp add: postRSeqTC periRSeqTC assms)
    apply(simp add: TCpostconcretify TCpericoncretify assms)
    apply(rel_auto)
    done
  moreover have "?l2 \<subseteq> ?r"
    by (smt (z3) Collect_mono_iff assms tttracesFE.simps tttracesFETCSeqSup2)
  ultimately show ?thesis
    using Un_least by blast
qed

lemma tttracesFETCSeq:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "tttracesFE (P ;; Q) = (  tttracesFE P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q})"
  apply(rule)
  using assms tttracesFETCSeqSub apply blast
  using assms tttracesFESubTCSeq apply blast
  done

subsubsection \<open> FR Results \<close>

lemma tttracesFRPTCSeqSub:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "tttracesFRP (P ;; Q) \<subseteq> (  tttracesFRP P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q})"
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  show ?thesis
    apply(simp add: assms 1 periRSeqTC postRSeqTC)
    apply(simp only: assms TRFTRRSeqExpandTr 2 TRF_implies_TRR)
    apply(simp add: assms TCpostconcretify TCpericoncretify)
    apply(rdes_simp)
    apply(rel_auto)
    apply(auto simp add: tockificationsAppend)
    by metis
qed

lemma tttracesFRITCSeqSub:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient P u X \<or> patient Q w X) \<Longrightarrow> (patient (P;;Q) (u@w) X))"
  shows "tttracesFRI (P ;; Q) \<subseteq> (  tttracesFRI P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q})"
        (is "?l \<subseteq> (?r1 \<union> ?r2)")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  show ?thesis
  proof (rule)
    fix s
    assume "s \<in> ?l"
    then obtain z X rt w where 3: "\<not>`(\<not>peri\<^sub>R (P;;Q))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
                                  "s = z@[oref (finalrefset False rt X)]"
                                  "\<not> patient (P;;Q) w X"
                                  "z \<in> tockifications w"
      by (auto; rel_auto)
    
    from 3(1) have  "\<not>`(\<not>(peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      by (simp add: assms 1 periRSeqTC postRSeqTC)
    hence "\<not>`\<not>(peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>` \<or> \<not>`(\<not>(post\<^sub>R P ;; peri\<^sub>R Q))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      by (rel_auto)
    then consider
        (4) "\<not>`\<not>(peri\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      | (5) "\<not>`(\<not>(post\<^sub>R P ;; peri\<^sub>R Q))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      by auto
    thus "s \<in> (?r1 \<union> ?r2)"
    proof (cases)
      case 4
      have "\<not> patient P w X"
        by (metis assms(5) "3"(3) append_Nil2)
      then show ?thesis
        using 4 "3"(2) "3"(4) by (auto)
    next
      case 5
      then have "\<not>`(\<not>(\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> post\<^sub>R P \<lbrakk>[]\<^sub>u,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)))\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
        apply(simp only: assms TRFTRRSeqExpandTr 2 TRF_implies_TRR)
        apply(rel_auto)
        done
      then obtain u v where 6: "w = u@v"
                               "\<not>`\<not>post\<^sub>R P \<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
                               "\<not>`\<not>peri\<^sub>R Q \<lbrakk>[]\<^sub>u,\<guillemotleft>v\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
      then obtain tu tv where 7: "z = tu@tv"
                                 "tu \<in> tockifications u"
                                 "tv \<in> tockifications v"
        by (smt (verit, ccfv_threshold) "3"(4) mem_Collect_eq tockificationsAppend)

      from 6(2) 7(2) have 8: "tu@[otick] \<in> tttracesTI P"
        by (auto; metis (no_types, lifting) subst_not)

      have "\<not> patient Q v X"
        by (metis 3(3) assms(5) 6(1))
      hence 9: "tv@[oref (finalrefset False rt X)] \<in> tttracesFRI Q"
        using 6(3) 7(3) by auto
      
      have "s \<in> ?r2"
        using 8 9 "3"(2) "7"(1) append_assoc by blast
      thus ?thesis
        by auto
    qed
  qed
qed

lemma tttracesFRTCSeqSub:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient P u X \<or> patient Q w X) \<Longrightarrow> (patient (P;;Q) (u@w) X))"
  shows "tttracesFR (P ;; Q) \<subseteq> (  tttracesFR P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFR Q})"
        (is "?l \<subseteq> ?r")
proof -
  have "?l = (tttracesFRI (P;;Q) \<union> tttracesFRP (P;;Q))"
    by auto
  also have "\<dots> \<subseteq> ((  tttracesFRI P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q})
                  \<union> (  tttracesFRP P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q}))"
    (is "?l1 \<subseteq> ((?r1a \<union> ?r1b) \<union> (?r2a \<union> ?r2b))")
  proof -
    have "tttracesFRI (P ;; Q) \<subseteq> (?r1a \<union> ?r1b)"
      by (simp only: tttracesFRITCSeqSub assms)
    moreover have "tttracesFRP (P ;; Q) \<subseteq> (?r2a \<union> ?r2b)"
      by (simp only: tttracesFRPTCSeqSub assms)
    ultimately show ?thesis
      by blast
  qed
  also have "\<dots> = (?r1a \<union> ?r2a) \<union> (?r1b \<union> ?r2b)"
    by blast
  also have "\<dots> = ?r"
    by (auto; metis)
  finally show ?thesis .
qed

lemma tttracesFRPTCSeqSup2:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r"
  shows "{t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q} \<subseteq> tttracesFRP (P ;; Q)" (is "?l \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wp_rea_def)
  have 4: "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R P) = (\<not> post\<^sub>R P)"
          "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R Q) = (\<not> post\<^sub>R Q)"
    by (meson "2" tfin_theory.utp_bottom utp_pred_laws.compl_le_compl_iff utp_pred_laws.sup.absorb2)+
  have 5: "(\<^U>(\<not> R1 true) \<or> (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)) = (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)"
    by (metis "2"(2) "2"(3) tfin_theory.bottom_lower trel_theory.bottom_lower utp_pred_laws.compl_le_compl_iff utp_pred_laws.le_iff_sup utp_pred_laws.le_inf_iff)
  {
    fix x
    assume "(x \<in> ?l)" 
    then obtain t s where 10: "x = t@s" "t@[otick] \<in> tttracesTI P" "s \<in> tttracesFRP Q"
      by blast
    then obtain u v X rt w where "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
                "t \<in> tockifications u"
                "s = v@[oref (finalrefset True rt X)]"
                "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
                "v \<in> tockifications w"
      by (auto simp add: subst_not)
    then have "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
              "s = v@[oref (finalrefset True rt X)]"
              "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
              "t@v \<in> tockifications (u@w)"
      by (smt (z3) mem_Collect_eq tockificationsAppend)+
    then have "s = v@[oref (finalrefset True rt X)]"
              "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`"
              "t@v \<in> tockifications (u@w)"
    proof -
      assume 7: "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      assume 8: "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      from 7 8 show "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`"
        apply(rdes_calc)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
    qed
    then have "s = v@[oref (finalrefset True rt X)]"
              "\<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`"
              "t@v \<in> tockifications (u@w)"
    proof -
      have "(post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk> \<sqsubseteq> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)"
        apply(simp add: TRFTRRSeqExpandTr 1 2)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
      then show "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)` \<Longrightarrow> \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`"
        by (smt (z3) taut_conj_elim utp_pred_laws.compl_sup utp_pred_laws.le_iff_sup)
    next
      assume "t @ v \<in> tockifications (u @ w)"
      thus "t @ v \<in> tockifications (u @ w)"
        by auto
    next
      assume "s = v @ [oref (finalrefset True rt X)]"
      thus "s = v @ [oref (finalrefset True rt X)]"
        by auto
    qed
    then have "\<exists> u v X rt w. \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`
                  \<and> x = v@[oref (finalrefset True rt X)]
                  \<and> v \<in> tockifications (u@w)"
      by (smt (z3) "10"(1) append.assoc)
    then have "x \<in> tttracesFRP (P ;; Q)"
      apply(simp add: assms 1 3 periRSeqTC postRSeqTC)
      apply(rdes_calc)
      by blast
  }
  then show ?thesis
    by (smt (z3) subsetI)
qed

lemma tttracesFRITCSeqSup2:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))"
  shows "{t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q} \<subseteq> tttracesFRI (P ;; Q)" (is "?l \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wp_rea_def)
  have 4: "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R P) = (\<not> post\<^sub>R P)"
          "(\<^U>(\<not> R1 true) \<or> \<not> post\<^sub>R Q) = (\<not> post\<^sub>R Q)"
    by (meson "2" tfin_theory.utp_bottom utp_pred_laws.compl_le_compl_iff utp_pred_laws.sup.absorb2)+
  have 5: "(\<^U>(\<not> R1 true) \<or> (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)) = (\<not> peri\<^sub>R Q \<and> \<not> post\<^sub>R Q)"
    by (metis "2"(2) "2"(3) tfin_theory.bottom_lower trel_theory.bottom_lower utp_pred_laws.compl_le_compl_iff utp_pred_laws.le_iff_sup utp_pred_laws.le_inf_iff)
  {
    fix x
    assume "(x \<in> ?l)" 
    then obtain t s where 10: "x = t@s" "t@[otick] \<in> tttracesTI P" "s \<in> tttracesFRI Q"
      by blast
    then obtain u v X rt w where "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
                "t \<in> tockifications u"
                "s = v@[oref (finalrefset False rt X)]"
                "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
                "\<not>patient Q w X"
                "v \<in> tockifications w"
      by (auto simp add: subst_not)
    then have "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
              "s = v@[oref (finalrefset False rt X)]"
              "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
              "\<not>patient Q w X"
              "t@v \<in> tockifications (u@w)"
      by (smt (z3) mem_Collect_eq tockificationsAppend)+
    then have "s = v@[oref (finalrefset False rt X)]"
              "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`"
              "\<not>patient Q w X"
              "t@v \<in> tockifications (u@w)"
    proof -
      assume 7: "\<not>`(\<not>post\<^sub>R P)\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk>`"
      assume 8: "\<not>`(\<not>peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`"
      from 7 8 show "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)`"
        apply(rdes_calc)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
    qed
    then have "s = v@[oref (finalrefset False rt X)]"
              "\<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`"
              "\<not>patient (P;;Q) (u@w) X"
              "t@v \<in> tockifications (u@w)"
    proof -
      have "(post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk> \<sqsubseteq> (post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> peri\<^sub>R Q\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)"
        apply(simp add: TRFTRRSeqExpandTr 1 2)
        apply(simp add: assms TCpostconcretify TCpericoncretify)
        apply(rel_auto)
        done
      then show "\<not>`\<not>(post\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>u\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> (peri\<^sub>R Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>)` \<Longrightarrow> \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`"
        by (smt (z3) taut_conj_elim utp_pred_laws.compl_sup utp_pred_laws.le_iff_sup)
    next
      assume "t @ v \<in> tockifications (u @ w)"
      thus "t @ v \<in> tockifications (u @ w)"
        by auto
    next
      assume "s = v @ [oref (finalrefset False rt X)]"
      thus "s = v @ [oref (finalrefset False rt X)]"
        by auto
    next
      assume "\<not>patient Q w X"
      thus "\<not>patient (P;;Q) (u@w) X"
        using assms(5) by blast
    qed
    then have "\<exists> u v X rt w. \<not>`\<not>(((post\<^sub>R P ;; peri\<^sub>R Q) \<lbrakk>[]\<^sub>u,\<guillemotleft>u@w\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>))`
                  \<and> x = v@[oref (finalrefset False rt X)]
                  \<and> \<not>patient (P;;Q) (u@w) X
                  \<and> v \<in> tockifications (u@w)"
      by (smt (z3) "10"(1) append.assoc)
    then have "x \<in> tttracesFRI (P ;; Q)"
      apply(simp add: assms 1 3 periRSeqTC postRSeqTC)
      apply(rdes_calc)
      by blast
  }
  then show ?thesis
    by (smt (z3) subsetI)
qed

lemma tttracesFRTCSeqSup2:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))"
  shows "{t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFR Q} \<subseteq> tttracesFR (P ;; Q)" (is "?l \<subseteq> ?r")
proof -
  have "?l \<subseteq> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> (s \<in> tttracesFRP Q \<or> s \<in> tttracesFRI Q)}"
    by (smt (verit, ccfv_threshold) Collect_mono_iff UnE tttracesFR.simps)
  also have "\<dots> \<subseteq> ({t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q}
            \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q})" (is "?l \<subseteq> (?l1 \<union> ?l2)")
    apply(blast)
    done
  also have "\<dots> \<subseteq> tttracesFRP (P ;; Q) \<union> tttracesFRI (P ;; Q)"
  proof -
    have "?l1 \<subseteq> tttracesFRP (P ;; Q)"
      using assms tttracesFRPTCSeqSup2 by blast
    moreover have "?l2 \<subseteq> tttracesFRI (P ;; Q)"
      using assms tttracesFRITCSeqSup2 by blast
    ultimately show ?thesis
      by blast
  qed
  also have "\<dots> = tttracesFR (P ;; Q)"
    by (simp add: semilattice_sup_class.sup.commute)
  finally show ?thesis .
qed

lemma tttracesFRPSupTCSeq:
  assumes "(P::'\<theta> ttcsp) is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))"
  shows "(tttracesFRP P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q}) \<subseteq> tttracesFRP (P ;; Q)" (is "(?l1 \<union> ?l2) \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wpR_R1_right wp_rea_true)
  have "?l1 = {s@[oref (finalrefset True rt X)] | s rt X t . s \<in> tockifications t \<and> (\<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`) }" (is "?l1 = ?l1a")
    apply(simp add: TCpostconcretify TCpericoncretify assms)
    apply (rel_auto)
    apply blast+
    done
  moreover have "?l1a \<subseteq> ?r"
    apply(simp add:  assms 3)
    apply(simp add: postRSeqTC periRSeqTC assms)
    apply(simp add: TCpostconcretify TCpericoncretify assms)
    apply(rel_simp)
    using assms(5) apply blast
    done
  ultimately have "?l1 \<subseteq> ?r"
    by auto
  moreover have "?l2 \<subseteq> ?r"
    by (smt (z3) Collect_mono_iff assms tttracesFRP.simps tttracesFRPTCSeqSup2)
  ultimately show ?thesis
    by (smt (z3) Un_subset_iff)
qed

lemma tttracesFRISupTCSeq:
  assumes "(P::'\<theta> ttcsp) is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))"
  shows "(tttracesFRI P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q}) \<subseteq> tttracesFRI (P ;; Q)" (is "(?l1 \<union> ?l2) \<subseteq> ?r")
proof -
  have 1: "(P ;; Q) is TC"
    by (simp add: assms TC_closed_seqr)
  have 2: "post\<^sub>R P is TRF" "peri\<^sub>R Q is TRR" "post\<^sub>R Q is TRF"
    by (simp_all add: closure assms)
  have 3: "pre\<^sub>R (P ;; Q) = true\<^sub>r"
    by (simp add: NRD_is_RD TC_implies_NRD assms preR_NRD_seq wpR_R1_right wp_rea_true)
  have "?l1 = {s@[oref (finalrefset False rt X)] | s rt X t . s \<in> tockifications t \<and> (\<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`) \<and> \<not> patient P t X }" (is "?l1 = ?l1a")
    apply(simp add: TCpostconcretify TCpericoncretify assms)
    apply (rel_auto)
    apply blast+
    done
  moreover have "?l1a \<subseteq> ?r"
  proof (rule)
    fix x
    assume "x \<in> ?l1a"
    then obtain s rt X t where 4: "x = s@[oref (finalrefset False rt X)]"
                                  "s \<in> tockifications t"
                                  "(\<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`)"
                                  "\<not> patient P t X"
      by auto
    from 4(4) have "\<not> patient (P;;Q) t X"
      by (metis append_Nil2 assms(5))
    moreover from 4(1-3) have "x = s@[oref (finalrefset False rt X)]"
                     "s \<in> tockifications t"
                     "(\<not>`\<not>peri\<^sub>R (P;;Q)\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>rfset X\<guillemotright>/$tr,$tr\<acute>,$ref\<acute>\<rbrakk>`)"
      apply(simp_all add: postRSeqTC periRSeqTC assms)
      apply(simp_all add: TCpostconcretify TCpericoncretify assms)
      apply(rel_auto)
      done
    ultimately show "x \<in> ?r"
      by auto
  qed
  ultimately have "?l1 \<subseteq> ?r"
    by auto
  moreover have "?l2 \<subseteq> ?r"
    by (smt (z3) Collect_mono_iff assms tttracesFRI.simps tttracesFRITCSeqSup2)
  ultimately show ?thesis
    by (smt (z3) Un_subset_iff)
qed

lemma tttracesFRSupTCSeq:
  assumes "(P::'\<theta> ttcsp) is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))" (*  "\<And>u w X. ((patient P u X \<or> patient Q w X) \<Longrightarrow> (patient (P;;Q) (u@w) X))" *)
  shows "(tttracesFR P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFR Q}) \<subseteq> tttracesFR (P ;; Q)" (is "?l \<subseteq> ?r")
proof -
  have "?l = ((tttracesFRI P \<union> tttracesFRP P) \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> (s \<in> (tttracesFRI Q \<union> tttracesFRP Q))})"
    by auto
  also have "\<dots> = ((tttracesFRI P \<union> tttracesFRP P) \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> ((s \<in> tttracesFRI Q) \<or> (s \<in> tttracesFRP Q))})"
    by auto
  also have "\<dots> = ((tttracesFRI P \<union> tttracesFRP P) \<union> ({t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q}) \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q})"
    by (auto; metis)
  also have "\<dots> = ((tttracesFRI P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRI Q})
                 \<union> (tttracesFRP P \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFRP Q}))"
            (is "?l3 = ?l1 \<union> ?l2")
    by blast
  also have "\<dots> \<subseteq> tttracesFRI (P;;Q) \<union> tttracesFRP (P;;Q)"
  proof -
    have "?l1 \<subseteq> tttracesFRI (P ;; Q)"
      using assms tttracesFRISupTCSeq by blast
    moreover have "?l2 \<subseteq> tttracesFRP (P ;; Q)"
      using assms tttracesFRPSupTCSeq by blast
    ultimately show ?thesis
      by blast
  qed
  also have "\<dots> = ?r"
    by auto
  finally show "?l \<subseteq> ?r" .
qed

lemma tttracesFRTCSeq:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))" "\<And>u w X. ((patient P u X \<or> patient Q w X) \<Longrightarrow> (patient (P;;Q) (u@w) X))"
  shows "tttracesFR (P ;; Q) = (  tttracesFR P
                                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFR Q})"
    (is "?l = ?r")
proof -
  have "?l \<subseteq> ?r"
    by (simp only: tttracesFRTCSeqSub assms(1-4) assms(6))
  moreover have "?r \<subseteq> ?l"
    by (simp only: tttracesFRSupTCSeq assms(1-4) assms(5))
  ultimately show ?thesis
    by blast
qed

subsubsection \<open> Overall Result \<close>

lemma tttracesTCSeq:
  assumes "P is TC" "Q is TC" "pre\<^sub>R P = true\<^sub>r" "pre\<^sub>R Q = true\<^sub>r" "\<And>u w X. ((patient (P;;Q) (u@w) X) \<Longrightarrow> (patient P u X \<and> patient Q w X))" "\<And>u w X. ((patient P u X \<or> patient Q w X) \<Longrightarrow> (patient (P;;Q) (u@w) X))"
  shows "tttraces (P;;Q) = tttraces P \<inter> untickeds
                         \<union> {t@s| t s. t@[otick] \<in> tttraces P \<and> s \<in> tttraces Q}" (is "?l = ?r1 \<union> ?r2")
proof -
  have "?r1 = tttraces P \<inter> TTTs \<inter> untickeds"
    using TTTStructure by blast
  also have "\<dots> = tttraces P \<inter> (FE \<union> FR)"
    using TTTsUntickedsFEFR by blast
  also have "\<dots> = tttracesFE P \<union> tttracesFR P"
    by (metis Int_Un_distrib tttracesSubregions(1) tttracesSubregions(4))
  finally have 1: "?r1 = tttracesFE P \<union> tttracesFR P" .

  have "?r2 = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttraces Q}"
  proof -
    {
      fix t
      have "(t@[otick] \<in> tttraces P) = (t@[otick] \<in> tttraces P \<inter> tickeds)"
        by (smt (verit, ccfv_threshold) IntE IntI TTT1TickedOrUnticked UnE in_set_conv_decomp mem_Collect_eq subset_iff tttracesTTT1)
      also have "\<dots> = (t@[otick] \<in> tttraces P \<inter> TTTs \<inter> tickeds)"
        using TTTStructure by blast
      also have "\<dots> = (t@[otick] \<in> tttraces P \<inter> TI)"
        using TTTsTickedsTI by blast
      also have "\<dots> = (t@[otick] \<in> tttracesTI P)"
        using tttracesSubregions(5) by blast
      finally have "(t@[otick] \<in> tttraces P) = (t@[otick] \<in> tttracesTI P)" .
    }
    thus ?thesis
      by blast
  qed
  also have "\<dots> = {t@s| t s. t@[otick] \<in> tttracesTI P
    \<and> (s \<in> tttracesFE Q \<or> s \<in> tttracesFR Q \<or> s \<in> tttracesTI Q)}"
    by auto
  also have "\<dots> = {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFE Q }
                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesFR Q }
                \<union> {t@s| t s. t@[otick] \<in> tttracesTI P \<and> s \<in> tttracesTI Q }" (is "\<dots> = ?FEs \<union> ?FRs \<union> ?TIs")
    by blast
  finally have 2: "?r2 = ?FEs \<union> ?FRs \<union> ?TIs" .

  from 1 2 have "?r1 \<union> ?r2 = (tttracesFE P \<union> tttracesFR P) \<union> (?FEs \<union> ?FRs \<union> ?TIs)"
    by auto
  also have "\<dots> = ((tttracesFE P \<union> ?FEs) \<union> (tttracesFR P \<union> ?FRs) \<union> ?TIs)"
    by auto
  also have "\<dots> = tttracesFE (P ;; Q) \<union> tttracesFR (P ;; Q) \<union> tttracesTI (P ;; Q)"
  proof -
    (* The only reason these cases need to be broken out is that assms(5) and assms(6) are
     * mutually recursive *)
    have "tttracesFE P \<union> ?FEs = tttracesFE (P ;; Q)"
      by (simp only: assms tttracesFETCSeq)
    moreover have "tttracesFR (P ;; Q) = tttracesFR P \<union> ?FRs"
      apply(rule tttracesFRTCSeq)
      apply(simp_all only: assms(1-5))
      apply(simp only: assms(6))
      done
    moreover have "?TIs = tttracesTI (P ;; Q)"
      by (simp only: assms tttracesTITCSeq)
    ultimately show ?thesis
      by auto
  qed
  finally show ?thesis
    by auto
qed

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

(*
lemma TCtttracesFR:
  assumes "P is TC"
  shows "tttracesFR P = { s | t X s .
     \<not>`\<not>peri\<^sub>R P\<lbrakk>[]\<^sub>u,\<guillemotleft>t\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>/$tr,$tr\<acute>,$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>`
      \<and> s \<in> tockifications t}"
  apply simp
  apply(subst (3) TRRconcretify)
   apply(simp add: TC_inner_closures assms)
  apply(pred_auto)
  done
*)
end