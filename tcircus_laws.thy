theory tcircus_laws
  imports tockcircus
begin


lemma TCpostconcretify: "(P::'\<theta> ttcsp) is TC \<Longrightarrow> post\<^sub>R P = P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$ref\<acute>,$pat,$pat\<acute>\<rbrakk>"
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


lemma TCpericoncretify: "(P::'\<theta> ttcsp) is TC \<Longrightarrow> peri\<^sub>R P = P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>False\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>, \<guillemotleft>False\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$ref,$pat\<rbrakk>"
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
  assumes "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
      and "$ref \<sharp> Q" "$pat \<sharp> Q" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q" "$wait \<sharp> Q" "$wait\<acute> \<sharp> Q"
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
  shows "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
proof -
  have "$ref \<sharp> P" "$pat \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRR_implies_RR assms)
  thus "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
    by (auto simp add: unrest)
qed

lemma TRFSubstUnrests:
  fixes "tt\<^sub>1"
  assumes "P is TRF"
  shows "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
proof -
  have "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus "$ref \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ref\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$pat\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$ok\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>" "$wait\<acute> \<sharp> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>"
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

end