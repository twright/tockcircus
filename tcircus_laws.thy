theory tcircus_laws
  imports tockcircus
begin

lemma TRRUnrestConcretify:
  assumes "$pat \<sharp> P" "$ref \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>)"
  using assms by pred_auto

lemma TRRconcretify:
  assumes "P is TRR"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$ref\<rbrakk>)"
proof -
  have "$pat \<sharp> P" "$ref \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus ?thesis
    by (rule TRRUnrestConcretify)
qed

lemma TRFUnrestConcretify:
  assumes "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>)"
  using assms by pred_auto

lemma TRFconcretify:
  assumes "P is TRF"
  shows "P = U(P\<lbrakk>\<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>True\<guillemotright>,\<guillemotleft>True\<guillemotright>, \<guillemotleft>rfnil\<guillemotright>,\<guillemotleft>rfnil\<guillemotright>/$ok,$ok\<acute>,$wait,$wait\<acute>,$pat,$pat\<acute>,$ref,$ref\<acute>\<rbrakk>)"
proof -
  have "$pat \<sharp> P" "$pat\<acute> \<sharp> P" "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
    by (auto simp add: unrest TRF_implies_TRR TRR_implies_RR assms)
  thus ?thesis
    by (rule TRFUnrestConcretify)
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

end