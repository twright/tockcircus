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


lemma tconj_TRRw [closure]:
  assumes "P is TRRw" "Q is TRRw"
   shows "P \<squnion>\<^sub>t Q is TRRw"
proof -
  have 1: "TRRw (\<^bold>\<exists> (pat0, pat1) \<bullet> P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) )
      = (\<^bold>\<exists> (pat0, pat1) \<bullet> TRRw (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) ))"
    by rel_blast
  have "\<And>pat1. (TRRw (Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>) = (TRRw Q)\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>)"
    by rel_auto
  hence 2: "\<And>pat1. (TRRw (Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>) = Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk>)"
    using assms(2) unfolding Healthy_def by metis
  
  have "\<And>pat0. (TRRw (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>) = (TRRw P)\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>)"
    by rel_auto
  hence 3: "\<And>pat0. (TRRw (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>) = P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk>)"
    using assms(1) unfolding Healthy_def by metis
  have 4: "P = R2c(P)" "Q = R2c(Q)"
    by (metis (no_types, lifting) Healthy_if R1_RR R2c_R1_seq R2c_RR TRR1_def TRR_implies_RR TRR_tc_skip TRRw_def assms)+
  have 5: "P = R1(P)" "Q = R1(Q)"
    by (metis Healthy_if R1_RR R1_seqr TRR1_def TRR_implies_RR TRR_tc_skip TRRw_def assms)+
  have 6: "P = R2(P)" "Q = R2(Q)"
    apply (metis "4"(1) "5"(1) R2_R2c_def)
    by (metis "4"(2) "5"(2) R2_R2c_def)
  have 7: "(\<^bold>\<exists> (pat0, pat1) \<bullet> TRRw (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>))))
         = (\<^bold>\<exists> (pat0, pat1) \<bullet> (P\<lbrakk>\<guillemotleft>pat0\<guillemotright>/$pat\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>pat1\<guillemotright>/$pat\<acute>\<rbrakk> \<and> (\<guillemotleft>pat0\<guillemotright> \<Rightarrow> \<guillemotleft>pat1\<guillemotright> \<Rightarrow> ($pat\<acute>)) ))"
    apply (subst (23 19 9 5) TRRwconcretify)
    apply (simp add: assms)+
    apply(rel_auto)
    apply ((subst 4(1))?; (subst 4(2))?; (subst (asm) 6(1))?; (subst (asm) 6(2))?; rel_blast)+
    done
  have "(TRRw P) \<squnion>\<^sub>t (TRRw Q) = (TRRw (P \<squnion>\<^sub>t Q))"
    by (simp add: "1" "7" tconj_alt_def Healthy_if assms)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma tconj_TRR6 [closure]:
  assumes "P is TRR6" "Q is TRR6"
   shows "P \<squnion>\<^sub>t Q is TRR6"
proof -
  have "P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P" "Q\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> Q"
    by (meson TRR6_alt_def assms)+
  hence "(P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<squnion>\<^sub>t Q\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>) \<sqsubseteq> (P \<squnion>\<^sub>t Q)"
    by (meson dual_order.trans tconj_mono(1) tconj_mono(2))
  moreover have "(P \<squnion>\<^sub>t Q)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> P\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<squnion>\<^sub>t Q\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk>"
    by (rel_auto)
  ultimately have "(P \<squnion>\<^sub>t Q)\<lbrakk>\<guillemotleft>True\<guillemotright>/$pat\<acute>\<rbrakk> \<sqsubseteq> (P \<squnion>\<^sub>t Q)"
    by (meson dual_order.trans)
  thus ?thesis
    using TRR6_alt_def by blast
qed


lemma tconj_TRR [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "P \<squnion>\<^sub>t Q is TRR"
  by (metis Healthy_if Healthy_intro TRR_TRRw TRR_def assms(1) assms(2) tconj_TRR6 tconj_TRRw)

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

end