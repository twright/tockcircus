theory tcircus_timed_conj
  imports "tcircus_rel" "UTP-Reactive-Designs.utp_rdes_tactics" (* UTP.utp_concurrency *)
begin
definition mk_refvar_set where
  "mk_refvar_set E p = ((torefvars E)
                        \<union> (if p then {} else {reftock}))"

lemma mk_refvar_set_inj:
  "(mk_refvar_set E\<^sub>1 p\<^sub>1 = mk_refvar_set E\<^sub>2 p\<^sub>2)
  = ((E\<^sub>1 = E\<^sub>2) \<and> (p\<^sub>1 = p\<^sub>2))"
  (is "(?l1 = ?l2) = ?r")
proof -
  {
    assume ?r
    then have "?l1 = ?l2"
      by (simp add: mk_refvar_set_def)
  }
  {
    assume "?l1 = ?l2"
    then have 1: "((torefvars E\<^sub>1)
              \<union> (if p\<^sub>1 then {} else {reftock}))
            = ((torefvars E\<^sub>2)
              \<union> (if p\<^sub>2 then {} else {reftock}))"
      (is "(?E1 \<union> ?P1) = (?E2 \<union> ?P2)")
      by (simp add: mk_refvar_set_def)
    moreover have "?P1 \<inter> ?E2 = {}" "?P2 \<inter> ?E1 = {}"
      by (auto simp add: torefvars_def)
    ultimately have "?P1 = ?P2" "?E1 = ?E2"
      using 1 by blast+
    then have ?r
      by (metis empty_not_insert torefvars_inj)
  }
  thus ?thesis
    by auto
qed


lemma mk_refvar_set_evts_patient: "mk_refvar_set (refusedevts X) (patient X) = X"
  apply (auto simp add: patient_def mk_refvar_set_def refusedevts_def torefvars_def)
  apply (metis refvarrefusedevts.elims singletonD)
  apply (metis refvarrefusedevts.elims singleton_iff)
  apply (metis empty_iff refvarrefusedevts.elims singletonD)
  apply (metis insertI1 refvarrefusedevts.cases refvarrefusedevts.simps(2))
  done

lemma refusedevts_alt_def: "refusedevts X = E \<Longrightarrow> patient X = p \<Longrightarrow> X = mk_refvar_set E p"
  using mk_refvar_set_evts_patient by blast

lemma refusedevts_eq: "refusedevts X = refusedevts Y \<Longrightarrow> patient X = patient Y \<Longrightarrow> X = Y"
  by (metis refusedevts_alt_def)

(*
definition merge_refvars where
merge_refvar
*)

(*
definition merge_refusal X Y where
  
*)

(*  :: "(('s, 'e) tt_vars) merge" *)

definition MPatConj :: "(('s, 'e) tt_vars) merge" where [upred_defs]:
"MPatConj = U(
              ($ok\<acute> = $0:ok)
            \<and> ($ok\<acute> = $1:ok)
            \<and> ($wait\<acute> = $0:wait)
            \<and> ($wait\<acute> = $1:wait)
            \<and> ($tr\<acute> = $0:tr)
            \<and> ($tr\<acute> = $1:tr)
            \<and> ($st\<acute> = $0:st)
            \<and> ($st\<acute> = $1:st)
            \<and> ($ref\<acute> = $0:ref)
            \<and> ($ref\<acute> = $1:ref)
            \<and> ($0:pat \<longrightarrow> $1:pat \<longrightarrow> $pat\<acute>)
            )"

(*
            \<and> ($ref\<acute> \<noteq> rfnil \<longrightarrow> $pat\<acute> = ($0:pat \<and> $1:pat)))

*)

lemma MPatConj_sim: "MPatConj is SymMerge"
  apply (rel_auto)
  done

lemma MPatConj_assoc:"AssocMerge MPatConj"
  apply (rel_auto)
  done

definition tconj (infixr "\<squnion>\<^sub>t" 75) where
  [upred_defs]: 
  "(P \<squnion>\<^sub>t Q) = (P \<parallel>\<^bsub>MPatConj\<^esub> Q)"

utp_const tconj

lemma tconj_rfnil1:
  "U(($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>) \<squnion>\<^sub>t ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>))
 = U(($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>) \<or> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>))"
  by (rel_auto)

(*
lemma tconj_rfnil:
  "U((P \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<squnion>\<^sub>t (Q \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))
 = U((P \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<and> (Q \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))"
  apply (rel_auto)
  by blast
*)

lemma tconj_patient:
  "U((P \<and> $pat\<acute>) \<squnion>\<^sub>t (Q \<and> $pat\<acute>))
 = U(P \<and> Q \<and> $pat\<acute>)"
  apply (rel_auto)
  by blast

lemma tconj_insistant:
  assumes "$pat\<acute> \<sharp> P" "$pat\<acute> \<sharp> Q"
  shows
  "(P \<squnion>\<^sub>t Q) = (P \<and> Q)"
proof -
  have "(P \<squnion>\<^sub>t Q) = (((\<exists> $pat\<acute> \<bullet> P) \<squnion>\<^sub>t (\<exists> $pat\<acute> \<bullet> Q)))"
    using assms
    by (simp add: ex_unrest)
  also have "\<dots> = ((\<exists> $pat\<acute> \<bullet> P) \<and> (\<exists> $pat\<acute> \<bullet> Q))"
    by (rel_auto)
  also have "\<dots> = (P \<and> Q)"
    using assms
    by (simp add: ex_unrest)
  finally show "?thesis" .
qed

lemma tconj_rfnil2:
  "U(($ref\<acute> = \<guillemotleft>rfset E\<guillemotright>) \<squnion>\<^sub>t ($ref\<acute> = \<guillemotleft>rfset F\<guillemotright>))
 = U($ref\<acute> = \<guillemotleft>rfset E\<guillemotright> \<and> \<guillemotleft>E = F\<guillemotright>)"
  by (rel_auto)

lemma tconj_assoc:
  "((P \<squnion>\<^sub>t Q) \<squnion>\<^sub>t R) = (P \<squnion>\<^sub>t (Q \<squnion>\<^sub>t R))"
  by (simp add: tconj_def MPatConj_assoc par_by_merge_assoc MPatConj_sim)

lemma tconj_comm:
  "(P \<squnion>\<^sub>t Q) = (Q \<squnion>\<^sub>t P)"
  by (simp add: tconj_def par_by_merge_commute MPatConj_sim)

lemma tconj_alt_def: "(P \<squnion>\<^sub>t Q) = (\<^bold>\<exists> (pat0, pat1) \<bullet> P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>
                                                 \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> $pat\<acute>))"
  by (rel_blast)

lemma tconj_mono:
  assumes "P \<sqsubseteq> Q"
  shows "P \<squnion>\<^sub>t R \<sqsubseteq> Q \<squnion>\<^sub>t R" "R \<squnion>\<^sub>t P \<sqsubseteq> R \<squnion>\<^sub>t Q"
  apply(simp_all add: tconj_alt_def)
  using assms by (rel_blast)+


lemma tconj_TRR [closure]:
  assumes "P is TRR" "Q is TRR"
   shows "P \<squnion>\<^sub>t Q is TRR"
proof -
  have 1: "TRR (\<^bold>\<exists> (pat0, pat1) \<bullet> P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) )
      = (\<^bold>\<exists> (pat0, pat1) \<bullet> TRR (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) ))"
    apply (rel_auto)
    apply blast+
    done
  have "\<And>pat1. (\<^U>(TRR (Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>)) = \<^U>((TRR Q)\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>))"
    apply(rel_auto)
    done
  hence 2: "\<And>pat1. (\<^U>(TRR (Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>)) = \<^U>(Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>))"
    using assms(2) unfolding Healthy_def by metis
  
  have "\<And>pat0. (\<^U>(TRR (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>)) = \<^U>((TRR P)\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>))"
    apply(rel_auto)
    done
  hence 3: "\<And>pat0. (\<^U>(TRR (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>)) = \<^U>(P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>))"
    using assms(1) unfolding Healthy_def by metis
  have 4: "P = R2c(P)" "Q = R2c(Q)"
    using assms
    by (simp_all add: Healthy_if RR_implies_R2c TRR_implies_RR)
  have 5: "P = R1(P)" "Q = R1(Q)"
    using assms
    by (simp_all add: Healthy_if RR_implies_R1 TRR_implies_RR)
  have 6: "P = R2(P)" "Q = R2(Q)"
    using assms
    by (simp_all add: Healthy_if RR_implies_R2 TRR_implies_RR)
  have 7: "(\<^bold>\<exists> (pat0, pat1) \<bullet> TRR (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>))))
         = (\<^bold>\<exists> (pat0, pat1) \<bullet> (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) ))"
    apply (subst (23 19 9 5) TRRconcretify)
    apply (simp add: assms)+
    apply(rel_auto)
    apply ((subst 4(1))?; (subst 4(2))?; (subst (asm) 6(1))?; (subst (asm) 6(2))?; rel_blast)+
    done
  have "(TRR P) \<squnion>\<^sub>t (TRR Q) = (TRR (P \<squnion>\<^sub>t Q))"
    by (simp add: "1" "7" tconj_alt_def Healthy_if assms)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TRF_tconj_conj:
  assumes "P is TRF" "Q is TRF"
  shows "(P \<squnion>\<^sub>t Q) = (P \<and> Q)"
  by (simp add: TRF_unrests(2) assms tconj_insistant)

lemma TRF_conj_closure [closure]:
  assumes "P is TRF" "Q is TRF"
  shows "(P \<and> Q) is TRF"
  by (meson TRF_implies_TRR TRF_intro TRF_unrests(1) TRF_unrests(2) TRR_conj assms unrest_conj)

lemma TRF_tconj_closure [closure]:
  assumes "P is TRF" "Q is TRF"
  shows "(P \<squnion>\<^sub>t Q) is TRF"
  by (simp add: TRF_conj_closure TRF_tconj_conj assms)

(*
lemma tconj_RR:
  assumes "P is RR" "Q is RR"
   shows "P \<squnion>\<^sub>t Q is TRR"
*)

(*
lemma tconj_TRR:
  assumes "P is TRC" "Q is TRC"
  shows "P \<squnion>\<^sub>t Q is RC"
proof -
  have 1: "P is TRR" "Q is TRR"
    by (simp_all add: TRC_implies_TRR assms)
  have 2: "P \<squnion>\<^sub>t Q is TRR"
    by (simp add: 1 tconj_TRR)
  have 3: "P = RC(P)" "Q = RC(Q)"
    apply (metis Healthy_def' TRC_implies_RC assms(1))
    apply (metis Healthy_def' TRC_implies_RC assms(2))
    done
  have 4: "P = RC2(P)" "Q = RC2(Q)"
    apply (metis Healthy_def' TRC_implies_RC2 assms(1))
    apply (metis Healthy_def' TRC_implies_RC2 assms(2))
    done
  have 5: "\<And>p. ((\<exists>a b. p = (conj a b)) = True)"
    by auto
  have "(P \<squnion>\<^sub>t Q) = (RC2 P \<squnion>\<^sub>t RC2 Q)"
    using 4 by auto
  also have "\<dots> = RC2(P \<squnion>\<^sub>t Q)"
    apply(subst (3 2 1) RC2_form_1)
    apply (simp add: "2" TRR_implies_RR)
    apply (simp add: "1"(2) TRR_implies_RR)
    apply (simp add: "1"(1) TRR_implies_RR)
    apply (simp add: tconj_alt_def)
    apply(subst (37 33 18 7) TRRconcretify) 
        apply(simp_all add: 1)
    apply(rel_simp)
    apply(simp add: 5)
    apply(safe)
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.select_convs(3) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.select_convs(3) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    sledgehammer run

    apply(rel_auto)
          prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))    
    prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
  prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.select_convs(3) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    prefer 2 apply (smt (z3) des_vars.ext_inject des_vars.update_convs(1) rp_vars.ext_inject rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
     prefer 2 apply (smt (z3) des_vars.update_convs(1) rp_vars.update_convs(1) tt_vars.surjective tt_vars.update_convs(2))
    oops

  have "RC2(P \<squnion>\<^sub>t Q) = (P \<squnion>\<^sub>t Q)"
    apply(rule TRR_transfer_eq)
    (*
    using 2 apply (metis (no_types, lifting) Healthy_if RC1_def RC_R2_def TRR_closed_neg TRR_closed_seq TRR_implies_RR o_apply rea_not_false trel_theory.top_closed)
     apply (simp add: "2")
    apply(subst (2) 3(1))
    apply(subst (2) 3(2))
    apply(rel_auto)
    sledgehammer
    oops
    *)
qed
*)

(* Not actually needed for anything!

lemma tconj_rdes:
  assumes "P\<^sub>1 is TRC" "P\<^sub>2 is TRR" "P\<^sub>3 is TRF" "Q\<^sub>1 is TRC" "Q\<^sub>2 is TRR" "Q\<^sub>3 is TRF"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<squnion>\<^sub>t \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R(P\<^sub>1 \<or> Q\<^sub>1 \<turnstile> P\<^sub>2 \<squnion>\<^sub>t Q\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>3)"
  apply(rule TRR_transfer_eq)
  apply(simp add: tconj_alt_def)
  oops

lemma tconj_rdes:
  assumes "P\<^sub>1 is TRC" "P\<^sub>2 is TRR" "P\<^sub>3 is TRF" "Q\<^sub>1 is TRC" "Q\<^sub>2 is TRR" "Q\<^sub>3 is TRF"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<squnion>\<^sub>t \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<squnion>\<^sub>t Q\<^sub>2) \<diamondop> (P\<^sub>3 \<and> Q\<^sub>3))"
proof 

  (* (rule rdes_tri_eq_intro)
  have "(P\<^sub>1 \<or> Q\<^sub>1) is TRC"
    by (metis Healthy_if Healthy_intro TRC_def TRC_implies_RC TRC_implies_TRR TRR1_def TRR_left_unit
        assms(1) assms(4) disj_RC_closed trel_theory.disj_is_healthy)
  moreover have "(P\<^sub>2 \<squnion>\<^sub>t Q\<^sub>2) is TRR"
    by (simp add: assms(2) assms(5) tconj_TRR)
  moreover have "(P\<^sub>3 \<and> Q\<^sub>3) is TRF"
    by (simp add: TRF_conj_closure assms(3) assms(6))
  moreover show "\<^bold>R (\<^U>(P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<squnion>\<^sub>t Q\<^sub>2) \<diamondop> (P\<^sub>3 \<and> Q\<^sub>3)) is TC"
    using assms sledgehammer
  *)
qed
*)

(*
abbreviation "neg_pat \<equiv> U(($ok\<acute> = $ok)
            \<and> ($wait\<acute> = $wait)
            \<and> ($tr\<acute> = $tr)
            \<and> ($st\<acute> = $st)
            \<and> ($ref\<acute> = $ref)
            \<and> (($pat \<Rightarrow> $pat\<acute>)))"

lemma tconj_conj_pat:
  "(P \<squnion>\<^sub>t Q) = ((P ;; neg_pat) \<and> (Q ;; neg_pat)) ;; neg_pat"
  apply(rel_auto)
  nitpick
*)

end