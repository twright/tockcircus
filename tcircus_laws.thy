theory tcircus_laws
  imports tockcircus
begin


lemma TRC_unrests:
  assumes "P is TRC"
  shows "$pat \<sharp> TRC(P)" "$pat\<acute> \<sharp> TRC(P)"
        "$ref \<sharp> TRC(P)" "$ref\<acute> \<sharp> TRC(P)"
        "$ok \<sharp> TRC(P)" "$ok\<acute> \<sharp> TRC(P)"
        "$wait \<sharp> TRC(P)" "$wait\<acute> \<sharp> TRC(P)"
  by (rel_auto+)

lemma TRC_unrests':
  assumes "P is TRC"
  shows "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P"
        "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  by (metis Healthy_if TRC_unrests assms)+

lemma TRRUnrestConcretify:
  assumes "$pat \<sharp> P" "$ref \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>)"
  using assms by pred_auto

lemma TRFUnrestConcretify:
  assumes "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>)"
  using assms by pred_auto

lemma TRCconcretify:
  assumes "P is TRC"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>)"
  by (rule TRFUnrestConcretify)
     (simp_all add: TRC_unrests' assms)

lemma TRRconcretify:
  assumes "P is TRR"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>)"
proof -
  have "$pat \<sharp> P" "$ref \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus ?thesis
    by (rule TRRUnrestConcretify)
qed


lemma TRFconcretify:
  assumes "P is TRF"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>)"
proof -
  have "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus ?thesis
    by (rule TRFUnrestConcretify)
qed

lemma TCpostconcretify: "(P::'\<theta> ttcsp) is TC \<Longrightarrow> post\<^sub>R P = P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>"
proof -
  assume 1: "P is TC"
  from 1 have "P is R1"
    by (simp add: closure)
  then have 2: "P = R1(P)"
    by (simp add: Healthy_def)
  show ?thesis
    apply(subst TRFconcretify)
     apply(simp add: 1 closure)
    apply(subst (2) 2)
    apply(rel_auto)
    done
qed


lemma TCpericoncretify: "(P::'\<theta> ttcsp) is TC \<Longrightarrow> peri\<^sub>R P = P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>"
proof -
  assume 1: "P is TC"
  from 1 have "P is R1"
    by (simp add: closure)
  then have 2: "P = R1(P)"
    by (simp add: Healthy_def)
  show ?thesis
    apply(subst TRRconcretify)
     apply(simp add: 1 closure)
    apply(subst (2) 2)
    apply(rel_auto)
    done
qed

lemma TRRSeqExpand:
  fixes P::"('b, 'a) tt_vars hrel" and Q::"('b, 'a) tt_vars hrel"
  assumes "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
      and "$pat \<sharp> Q" "$ref \<sharp> Q" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q" "$wait \<sharp> Q" "$wait\<acute> \<sharp> Q"
  shows "(P ;; Q) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> st\<^sub>0 \<bullet>
                     P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr\<acute>,$st\<acute>\<rbrakk>
                   \<and> Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$st\<rbrakk>)"
  apply(subst (24 3) TRRUnrestConcretify)
  apply(simp_all only: assms)
  apply(subst (30 1) TRFUnrestConcretify)
  apply(simp_all only: assms)
  apply(simp only: seqr_unfold)
  (* apply(simp add: unrest usubst) *)
  apply(rel_auto)
  done

lemma TRRSubstUnrests:
  fixes "tt\<^sub>1"
  assumes "P is TRR"
  shows "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
proof -
  have "$pat \<sharp> P" "$ref \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRR_implies_RR assms)
  thus "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
    by (auto simp add: unrest)
qed

lemma TRFSubstUnrests:
  fixes "tt\<^sub>1"
  assumes "P is TRF"
  shows "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
proof -
  have "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
    by (auto simp add: unrest)
qed

lemma TRFTRRSeqExpandTr:
  assumes "P is TRF" "Q is TRR"
  shows "(P ;; Q) = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> st\<^sub>0 \<bullet>
                       P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$tr\<acute>,$st\<acute>\<rbrakk>
                     \<and> Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$tr\<acute>,$st\<rbrakk>
                     \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
proof -
  have "(P ;; Q) = (R2(P) ;; R2(Q))"
    by (simp add: Healthy_if RR_implies_R2 TRF_implies_TRR TRR_implies_RR assms)
  also have "\<dots> = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet>
     ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
   \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by (simp add: R2_seqr_form)
  also have "\<dots> = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet>
     (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> st\<^sub>0 \<bullet>
                     (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr\<acute>,$st\<acute>\<rbrakk>
                   \<and> (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$st\<rbrakk>)
   \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by (simp add: TRRSeqExpand assms TRRSubstUnrests TRFSubstUnrests)
  also have "\<dots> = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet>
     (\<^bold>\<exists> st\<^sub>0 \<bullet>
                     (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<acute>\<rbrakk>
                   \<and> (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<rbrakk>)
   \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by pred_auto
  also have "\<dots> = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> st\<^sub>0 \<bullet>
                     P\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$tr\<acute>,$st\<acute>\<rbrakk>
                   \<and> Q\<lbrakk>0,\<guillemotleft>tt\<^sub>2\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>/$tr,$tr\<acute>,$st\<rbrakk>
                   \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by pred_auto
  finally show ?thesis .
qed

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

subsubsection \<open> Patience \<close>

definition patient :: "'\<theta> ttcsp \<Rightarrow> '\<theta> reftrace \<Rightarrow> '\<theta> set \<Rightarrow> bool" where
"patient P t X = `[$pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>True\<guillemotright>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (peri\<^sub>R P)`"

definition patientRR :: "'\<theta> ttcsp \<Rightarrow> '\<theta> reftrace \<Rightarrow> '\<theta> set \<Rightarrow> bool" where
"patientRR P t X = `[$pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>True\<guillemotright>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>rfset X\<guillemotright>, $tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> P`"

lemma patientPeri:
  assumes "P is TC"
  shows "patient P t X = patientRR (peri\<^sub>R P) t X"
  using assms by (rdes_simp cls: patient_def patientRR_def)

lemma patientRR_disj_eq:
  "P is TRR \<Longrightarrow> Q is TRR \<Longrightarrow> (patientRR (P \<sqinter> Q) t X = (patientRR P t X \<or> patientRR Q t X))"
proof -
  assume 1: "P is TRR" "Q is TRR"
  have "patientRR P t X \<Longrightarrow> patientRR (P \<sqinter> Q) t X" and "patientRR Q t X \<Longrightarrow> patientRR (P \<sqinter> Q) t X"
    using 1 apply(simp_all add: patientRR_def)
    apply(rdes_simp+)
    apply(rel_auto+)
    done
  moreover have "patientRR (P \<sqinter> Q) t X \<Longrightarrow> patientRR P t X \<or> patientRR Q t X"
    apply(simp_all add: patientRR_def)
    apply(rdes_simp)
    apply(subst (3) TRRconcretify)
    apply(simp add: 1)
    apply(subst (asm) (3) TRRconcretify)
    apply(simp add: 1)
    apply(rel_auto)
    done
  ultimately show ?thesis
    by blast
qed

lemma patient_conj:
"P is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient P t X \<Longrightarrow> patient Q t X \<Longrightarrow> patient (P \<squnion> Q) t X"
proof - 
  assume 1: "P is TC" "Q is TC"
  assume 2: "patient P t X" "patient Q t X"
  from 2 show "patient (P \<squnion> Q) t X"
    apply(simp add: patient_def)
    apply(rel_auto)
    done
qed

lemma patient_conj':
"P is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient (P \<squnion> Q) t X \<Longrightarrow> patient P t X \<and> patient Q t X"
proof - 
  assume 1: "P is TC" "Q is TC"
  assume 3: "patient (P \<squnion> Q) t X"
  have "pre\<^sub>R (P \<squnion> Q) = (pre\<^sub>R P \<or> pre\<^sub>R Q)"
    by (rel_auto)
  from 3 show "patient P t X \<and> patient Q t X"
    apply(simp add: patient_def)
    apply(rdes_simp cls: 1)
    apply(rel_auto)
    done
qed

lemma patient_disj1:
"P is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient P t X \<Longrightarrow> patient (P \<sqinter> Q) t X"
proof - 
  assume 1: "P is TC" "Q is TC"
  assume 3: "patient P t X"
  from 3 show "patient (P \<sqinter> Q) t X"
    apply(simp add: patient_def)
    apply(rdes_simp cls: 1)
    apply(rel_auto)
    done
qed

lemma patient_disj2:
"P is TC \<Longrightarrow> Q is TC \<Longrightarrow> pre\<^sub>R P = pre\<^sub>R Q \<Longrightarrow> patient Q t X \<Longrightarrow> patient (P \<sqinter> Q) t X"
proof - 
  assume 1: "P is TC" "Q is TC"
  assume 2: "pre\<^sub>R P = pre\<^sub>R Q"
  assume 3: "patient Q t X"
  from 3 show "patient (P \<sqinter> Q) t X"
    apply(simp add: patient_def)
    apply(rdes_simp cls: 1 2)
    apply(rel_auto)
    done
qed

lemma patient_disj':
"(P::'\<theta> ttcsp) is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient (P \<sqinter> Q) t X \<Longrightarrow> (patient P t X \<or> patient Q t X)"
proof - 
  assume 1: "P is TC" "Q is TC"
  assume 3: "patient (P \<sqinter> Q) t X"
  from 3 show "patient P t X \<or> patient Q t X"
    apply(simp add: patient_def)
    apply(rdes_simp cls: 1)
    apply(simp add: TCpericoncretify 1)
    apply(rel_auto)
    done
qed

lemma patient_disj_eq:
"(P::'\<theta> ttcsp) is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient (P \<sqinter> Q) t X = (patient P t X \<or> patient Q t X)"
  by (metis patient_disj' patient_disj1 semilattice_sup_class.sup_commute)

(*
lemma patient_seq:
"(P::'\<theta> ttcsp) is TC \<Longrightarrow> Q is TC \<Longrightarrow> patient Q t X = patient (P ;; Q) t X"
  apply(simp add: patient_def)
  apply(rel_auto)
*)


(*
lemma paitent_seq:
  assumes "(P::'\<theta> ttcsp) is TC"
      and "Q is TC"
      and "pre\<^sub>R P = true"
      and "pre\<^sub>R Q = true"
      and "patient P t X"
      and "patient Q t X"
    shows "patient(P;;Q) t X"
proof -
  have 1: "P;;Q is TC"
    using assms by (simp add: TC_closed_seqr)
  have 2: "pre\<^sub>R (P;;Q) = true\<^sub>r"
    using assms(3-4)
    by (rdes_simp cls: assms(1-2))
  show ?thesis
    using assms(5-6)
    apply(simp add: patient_def)
    apply(rdes_simp cls: 1 2)
    apply(rel_simp)
    oops
qed
*)

end