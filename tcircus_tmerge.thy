theory tcircus_tmerge
  imports tcircus_idle
begin

text \<open> We make the decision that state changes are not observable during idle periods, as this
  would complicate the semantics. They are only revealed at termination and quiescence. \<close>

definition merge_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixr "\<triangleright>\<^sub>t" 65) where
[upred_defs]: 
  "P \<triangleright>\<^sub>t Q = 
    U(R1
      (\<exists> t es. &tt = \<guillemotleft>t @ es\<guillemotright> \<comment> \<open> The trace can be decomposed into two pieces \<close>
            \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<comment> \<open> The first piece is a sequence of tocks \<close>
            \<and> (\<guillemotleft>es\<guillemotright> = [] \<comment> \<open> The second piece is either empty ... \<close>
               \<or> hd(\<guillemotleft>es\<guillemotright>) \<in> range(Evt)) \<comment> \<open> ... or begins with an event \<close>
            \<and> (\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<comment> \<open> The first piece is a trace of @{term P} \<close>
            \<and> Q \<comment> \<open> @{term Q} admits the whole trace \<close>
            ))"

text \<open> There is a trace whose idle prefix is shared by all elements of the set, and at least
  one element which admits the trace plus at least one event. \<close>

utp_const UINFIMUM (1) USUPREMUM (1)

definition tmerge :: "'i set \<Rightarrow> ('i \<Rightarrow> ('s, 'e) taction) \<Rightarrow> ('s, 'e) taction" where
[upred_defs]: 
  "tmerge I P = 
      U(R1
        (\<exists> t es. &tt = \<guillemotleft>t @ es\<guillemotright>
               \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV 
               \<and> (\<guillemotleft>es\<guillemotright> = [] 
                  \<or> hd(\<guillemotleft>es\<guillemotright>) \<in> range(Evt))
               \<and> (\<Squnion> i\<in>I \<bullet> (\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> (@P i)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk>)) 
               \<and> (\<Sqinter> i \<in> I \<bullet> @P i) 
               ))"

syntax
  "_tmerge" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<And>\<^sub>t _\<in>_ \<bullet> _" [0, 0, 10] 10)

translations
  "\<And>\<^sub>t i\<in>I \<bullet> P" == "CONST tmerge I (\<lambda> i. P)"

text \<open> The time merge operator merges the delay traces of one relation with active traces of another. \<close>

utp_const merge_time tmerge


lemma TRR_merge_time [closure]: 
  assumes "P is TRR" "Q is TRR" 
  shows "P \<triangleright>\<^sub>t Q is TRR"
proof -
  have "TRR(P) \<triangleright>\<^sub>t TRR(Q) is TRR"
    by (rel_simp, metis)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed


lemma tmerge_cong:  
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i = Q i"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) = (\<And>\<^sub>t i\<in>I \<bullet> Q i)"
  using assms apply (rel_auto)
  apply (metis idle_active_decomp minus_cancel plus_list_def tocks_idleprefix_fp trace_class.add_diff_cancel_left)
  apply (metis rangeI)
  apply (metis (full_types) append_Nil2)
  apply (metis rangeI)
  done

lemma RR_tmerge [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is RR"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) is RR"
proof -
  have "(\<And>\<^sub>t i\<in>I \<bullet> RR (P i)) is RR"
    by (rel_auto, blast+)
  thus ?thesis
    by (metis Healthy_if assms tmerge_cong)
qed

lemma TRR_tmerge [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is TRR"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) is TRR"
proof -
  have "(\<And>\<^sub>t i\<in>I \<bullet> TRR (P i)) is TRR"
    unfolding Healthy_def by (rrel_auto cls: assms)
  thus ?thesis
    by (metis Healthy_if assms tmerge_cong)
qed

lemma TRR_tmerge_single [closure]: "P i is TRR \<Longrightarrow> tmerge {i} P is TRR"
  by (auto intro: closure)

lemma TRR_tmerge_dual [closure]: "\<lbrakk> P i is TRR; P j is TRR \<rbrakk> \<Longrightarrow> tmerge {i, j} P is TRR"
  by (auto intro: closure)

lemma tmerge_single:
  assumes "P i is TRR" "P i is TIP"
  shows "tmerge {i} P = P i"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_simp')
  apply (metis hd_activesuffix idle_active_decomp idleprefix_tocks)
  done

lemma time_merge_self [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "P \<triangleright>\<^sub>t P = P"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_simp')
  apply (metis hd_activesuffix idle_active_decomp idleprefix_tocks)
  done

lemma tmerge_dual_1:
  assumes "P i is TRR" "P j is TRR"
  shows "tmerge {i, j} P = 
          ((P i \<triangleright>\<^sub>t P i \<and> P j \<triangleright>\<^sub>t P i) \<or> (P i \<triangleright>\<^sub>t P j \<and> P j \<triangleright>\<^sub>t P j))"
  apply (trr_auto cls: assms)
  apply blast

                      apply blast
  apply (metis (no_types) append_Nil2)
  apply blast
  apply blast
  apply blast
  apply auto
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply (metis append_Nil2 list.collapse tocks_Evt)
  apply (metis (no_types) append_self_conv tocks_append)
  apply (smt append_self_conv hd_Cons_tl idleprefix_concat_Evt rangeI tocks_idleprefix_fp)
  apply blast
  apply (metis append_Nil2 hd_Cons_tl tocks_Evt)
  apply (metis append_Nil2 hd_Cons_tl tocks_Evt)
  apply (smt append_Nil2 hd_Cons_tl rangeI tock_prefix_eq tocks_Evt tocks_append)
  done

end