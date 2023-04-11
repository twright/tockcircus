section \<open> Idle and Active Relations \<close>

theory tcircus_idle
  imports tcircus_rel tcircus_timed_conj
begin


definition filter_idle_urgent :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("idle\<^sub>I'(_')") where
[upred_defs]: "filter_idle_urgent P = U(R1(P \<and> (&tt \<in> tocks UNIV)))"


(* \<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> *)
definition filter_time_urgent :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("time\<^sub>I'(_')") where
[upred_defs]: "filter_time_urgent P = U(R1(\<exists> $st\<acute> \<bullet> P\<lbrakk>idleprefix(&tt),rfnil,True/&tt,$ref\<acute>,$pat\<acute>\<rbrakk>))"

definition filter_active_urgent :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("active\<^sub>I'(_')") where 
[upred_defs]: "filter_active_urgent(P) = U(R1(\<exists> t e t'. P \<and> (\<guillemotleft>t\<guillemotright> \<in> tocks UNIV) \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)))"

utp_const filter_time_urgent filter_idle_urgent filter_active_urgent

definition filter_idle :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("idle'(_')") where
[upred_defs]: "filter_idle P = U(idle\<^sub>I(P) \<and> $pat\<acute>)"

definition filter_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("time'(_')") where
[upred_defs]: "filter_time P = U(time\<^sub>I(P) \<and> $pat\<acute>)"

definition filter_active :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("active'(_')") where 
[upred_defs]: "filter_active(P) = U(R1(\<exists> t e t'. (P \<and> $pat\<acute>) \<squnion>\<^sub>t (\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> $pat\<acute>) \<squnion>\<^sub>t (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright> \<and> $pat\<acute>)))"

utp_const filter_idle filter_active filter_time filter_idle_urgent filter_active_urgent filter_time_urgent

lemma S1: "U((\<guillemotleft>t\<guillemotright> \<in> tocks UNIV) \<squnion>\<^sub>t (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)) = U((\<guillemotleft>t\<guillemotright> \<in> tocks UNIV) \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>))"
  by (rel_auto)

lemma conj_tconj:
  assumes "$pat\<acute> \<sharp> Q"
  shows "U(P \<squnion>\<^sub>t (Q \<and> $pat\<acute>)) = U(P \<and> Q \<and> $pat\<acute>)" (is "?l = ?r")
proof - 
  have 1: "Q = (\<forall> $pat\<acute>  \<bullet> Q)" "Q = (\<exists> $pat\<acute>  \<bullet> Q)"
    using assms by (simp_all add: all_unrest ex_unrest)
  have 2: "U(Q \<and> $pat\<acute>) = U((\<forall> $pat\<acute> \<bullet> Q) \<and> $pat\<acute>)"
    using 1 by auto
  have "?l = U(P \<squnion>\<^sub>t ((\<forall> $pat\<acute> \<bullet> Q) \<and> $pat\<acute>))"
    using 2 by auto
  also have "\<dots> = (P \<and> (\<forall> $pat\<acute> \<bullet> Q))"
    apply(rel_auto)
    oops
(*
    sledgehammer
    by (rel_auto; blast)
  also have "\<dots> = ?r"
    using 1 by auto
  finally show ?thesis .
qed
*)

lemma conj_tconj_patient:
  assumes "$pat\<acute> \<sharp> P" "$pat\<acute> \<sharp> Q"
  shows "(P \<squnion>\<^sub>t Q) = (P \<and> Q)" (is "?l = ?r")
proof - 
  have 1: "P = (\<forall> $pat\<acute>  \<bullet> P)" "Q = (\<forall> $pat\<acute>  \<bullet> Q)" "P = (\<exists> $pat\<acute>  \<bullet> P)" "Q = (\<exists> $pat\<acute>  \<bullet> Q)"
    using assms by (simp_all add: all_unrest ex_unrest)
  have "?l = ((\<exists> $pat\<acute>  \<bullet> P) \<squnion>\<^sub>t (\<exists> $pat\<acute> \<bullet> Q))"
    using 1 by auto
  also have "\<dots> = ((\<exists> $pat\<acute>  \<bullet> P) \<and> (\<exists> $pat\<acute> \<bullet> Q))"
    by (rel_auto)
  also have "\<dots> = ?r"
    using 1 by auto
  finally show ?thesis .
qed

lemma idle_form: "idle(P) = U(idle\<^sub>I(P) \<and> $pat\<acute>)"
  by (simp add: filter_idle_def)

(*
lemma active_form: "active(P) = (active\<^sub>I(P) \<and> $pat\<acute>)" (is "?l = ?r")
proof -
  {
    fix t e t'
    have "U((P \<and> $pat\<acute>) \<squnion>\<^sub>t ((\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)) \<and> $pat\<acute>))
        = U((P \<and> $pat\<acute>) \<and> (\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)))"
      by (subst conj_tconj; rel_auto)
  }
  hence 1: "\<And>t e t'. (U((P \<and> $pat\<acute>) \<squnion>\<^sub>t ((\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)) \<and> $pat\<acute>))
        = U(P \<and> $pat\<acute> \<and> (\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>))))"
    by rel_auto
  have "?l = U(R1(\<exists> t e t'. (P \<and> $pat\<acute>) \<squnion>\<^sub>t (\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>) \<and> $pat\<acute>)))"
    apply (simp add: filter_active_def conj_tconj unrest)
    apply rel_blast
    done
  also have "\<dots> = U(R1(\<exists> t e t'. (P \<and> $pat\<acute>) \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (&tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>)))"
    (* apply(auto simp add: 1) *)
    using 1 by rel_auto
  also have "\<dots> = ?r"
    by rel_auto
  finally show ?thesis .
qed
*)

lemma idle_TRR [closure]: assumes "P is TRR" shows "idle(P) is TRR"
proof -
  have "TRR(idle(TRR(P))) = idle(TRR(P))"
    apply (simp add: idle_form)
    apply rel_blast
    done
  thus "idle(P) is TRR" by (metis Healthy_def assms)
qed

lemma idle_TRR_insistant [closure]: assumes "P is TRR" shows "idle\<^sub>I(P) is TRR"
proof -
  have "TRR(idle\<^sub>I(TRR(P))) = idle\<^sub>I(TRR(P))"
    by rel_blast
  thus "idle\<^sub>I(P) is TRR" by (metis Healthy_def assms)
qed

(*
lemma active_TRR [closure]: assumes "P is TRR" shows "active(P) is TRR"
proof -
  have "TRR(active(TRR(P))) = active(TRR(P))"
    apply (simp add: active_form)
    apply (rel_blast)
    done
  thus "active(P) is TRR" by (metis Healthy_def assms)
qed
*)

lemma active_TRR_insistant [closure]: assumes "P is TRR" shows "active\<^sub>I(P) is TRR"
proof -
  have "TRR(active\<^sub>I(TRR(P))) = active\<^sub>I(TRR(P))"
    apply (rel_blast)
    done
  thus "active\<^sub>I(P) is TRR" by (metis Healthy_def assms)
qed

lemma time_TRR [closure]: assumes "P is TRR" shows "time(P) is TRR"
proof -
  have "TRR(time(TRR(P))) = time(TRR(P))" by rel_blast
  thus "time(P) is TRR" by (metis Healthy_def assms)
qed

lemma time_urgent_TRR [closure]: assumes "P is TRR" shows "time\<^sub>I(P) is TRR"
proof -
  have "TRR(time\<^sub>I(TRR(P))) = time\<^sub>I(TRR(P))" by rel_blast
  thus "time\<^sub>I(P) is TRR" by (metis Healthy_def assms)
qed

(*
lemma 
  assumes "P is TRR"
  shows "(P \<squnion>\<^sub>t (time(P) \<and> $pat\<acute>)) is TIP"
  (is "?l is TIP")
  apply (subst conj_tconj)
   apply(rel_auto)
    apply (simp add: Healthy_def)
  apply (trr_auto cls: assms)
  oops
*)
lemma 
  assumes "P is TRR"
  shows "(P \<and> time(P)) is TIP"
  apply (simp add: Healthy_def)
  apply (trr_auto cls: assms)
  oops

(*
lemma active_disj [rpred]: "active(P \<or> Q) = (active(P) \<or> active(Q))"
  apply(simp add: active_form)
  apply rel_auto
  done
*)

lemma idle_conj [rpred]: "idle(P \<and> Q) = (idle(P) \<and> idle(Q))"
  apply(simp add: idle_form)
  apply (rel_auto)
  done

lemma active_disj_insistant [rpred]: "active\<^sub>I(P \<or> Q) = (active\<^sub>I(P) \<or> active\<^sub>I(Q))"
  by rel_auto
  
lemma idle_conj_insistant [rpred]: "idle\<^sub>I(P \<and> Q) = (idle\<^sub>I(P) \<and> idle\<^sub>I(Q))"
  by (rel_auto)


lemma idleI_tconj [rpred]: "idle\<^sub>I(P \<squnion>\<^sub>t Q) = (idle\<^sub>I(P) \<squnion>\<^sub>t idle\<^sub>I(Q))"
  by (rel_blast)

lemma idle_tconj [rpred]: "idle(P \<squnion>\<^sub>t Q) = (idle(P) \<squnion>\<^sub>t idle(Q))"
  apply(simp add: idle_form)
  apply(rel_auto)
  oops
(*
  apply blast+
  done
*)

lemma idle_disj [rpred]: "idle(P \<or> Q) = (idle(P) \<or> idle(Q))"
  apply(simp add: idle_form)
  by (rel_auto)

lemma idle_idem [rpred]: "idle(idle(P)) = idle(P)"
  apply(simp add: idle_form)
  by rel_auto

lemma idle_disj_insistant [rpred]: "idle\<^sub>I(P \<or> Q) = (idle\<^sub>I(P) \<or> idle\<^sub>I(Q))"
  by (rel_auto)

lemma idle_idem_insistant [rpred]: "idle\<^sub>I(idle\<^sub>I(P)) = idle\<^sub>I(P)"
  by rel_auto

lemma idle_true': "idle(true) = U(R1(&tt \<in> tocks UNIV \<and> $pat\<acute>))"
  by rel_auto

lemma idle_true'_insistant: "idle\<^sub>I(true) = U(R1(&tt \<in> tocks UNIV))"
  by rel_auto

(*
lemma active_idem [rpred]: "active(active(P)) = active(P)"
  apply (simp add: active_form)
  by rel_auto
*)

lemma active_idem_insistant [rpred]: "active\<^sub>I(active\<^sub>I(P)) = active\<^sub>I(P)"
  by rel_auto

lemma TRR_idle_or_active_insistant [rpred]:
  assumes "P is TRR"
  shows "(idle\<^sub>I(P) \<or> active\<^sub>I(P)) = (P)"
  apply (trr_auto cls: assms)
  by (metis append_self_conv hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE)  

(*
lemma TRR_idle_or_active [rpred]:
  assumes "P is TRR"
  shows "(idle(P) \<or> active(P)) = (P \<and> $pat\<acute>)" (is "?l = ?r")
proof -
  have "?l = (idle\<^sub>I(P) \<and> $pat\<acute> \<or> active\<^sub>I(P) \<and> $pat\<acute>)"
    by (simp add: idle_form active_form)
  also have "\<dots> = ((idle\<^sub>I(P) \<or> active\<^sub>I(P)) \<and> $pat\<acute>)"
    by rel_auto
  also have "\<dots> = ?r"
    by (simp add: TRR_idle_or_active_insistant assms)
  finally show ?thesis .
qed
*)

lemma refine_eval_dest: "P \<sqsubseteq> Q \<Longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e s"
  by (rel_auto)

lemma Healthy_after: "\<lbrakk> \<And> i. P i is H \<rbrakk> \<Longrightarrow> H \<circ> P = P"
  by (metis (mono_tags, lifting) Healthy_if fun.map_cong fun.map_id0 id_apply image_iff)

lemma idle_skip [rpred]: "idle(II\<^sub>t) = U(II\<^sub>t \<and> $pat\<acute>)"
  apply(simp add: idle_form)
  apply (rel_auto)
  done

lemma idle_skip_urgent [rpred]: "idle\<^sub>I(II\<^sub>t) = (II\<^sub>t)"
  apply (rel_auto)
  done

lemma idle_false [rpred]: "idle(false) = false"
  by (rel_auto)

lemma idle_false_urgent [rpred]: "idle\<^sub>I(false) = false"
  by (rel_auto)

lemma time_disj [rpred]: "time(P \<or> Q) = (time(P) \<or> time(Q))"
  by (rel_auto)

lemma time_disj_urgent [rpred]: "time\<^sub>I(P \<or> Q) = (time\<^sub>I(P) \<or> time\<^sub>I(Q))"
  by (rel_auto)

lemma TIP_has_time [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(P \<and> time\<^sub>I(P)) = P"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply(rel_blast)
  done

lemma TIP_time_refine [closure]:
  assumes "P is TRR" "P is TIP"
  shows "time\<^sub>I(P) \<sqsubseteq> P"
  by (simp add: TIP_has_time assms(1) assms(2) utp_pred_laws.inf.orderI)

(*
lemma TIP_has_time_tconj [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(P \<squnion>\<^sub>t time(P)) = P"
  apply( simp add: filter_time_def)
(*  apply (subst conj_tconj) *)
  apply (simp add: unrest filter_time_urgent_def)
  apply (simp add: TIP_has_time assms(1) assms(2))
  done
*)

lemma TIP_time_active_urgent_tconj [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active\<^sub>I(P) \<squnion>\<^sub>t time\<^sub>I(P)) = active\<^sub>I(P)"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
     apply(rel_simp)+
  oops

lemma TIP_time_active_urgent_conj [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active\<^sub>I(P) \<and> time\<^sub>I(P)) = active\<^sub>I(P)"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply(rel_auto+)
  done

(*
lemma TIP_time_active_tconj [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active(P) \<squnion>\<^sub>t time(P)) = active(P)" (is "?l = ?r")
proof -
  have "?l = (active(P) \<squnion>\<^sub>t (time\<^sub>I(P) \<and> $pat\<acute>))"
    by (simp add: filter_time_def)
  also have "\<dots> = (active(P) \<and> time\<^sub>I(P) \<and> $pat\<acute>)"
    by (simp add: active_form tconj_patient)
  also have "\<dots> = (active\<^sub>I(P) \<and> $pat\<acute> \<and> time\<^sub>I(P) \<and> $pat\<acute>)"
    by (simp add: active_form utp_pred_laws.conj_assoc)
  also have "\<dots> = ((active\<^sub>I(P) \<and> time\<^sub>I(P)) \<and> $pat\<acute>)"
    by (simp add: utp_pred_laws.inf.assoc utp_pred_laws.inf.left_commute)
  also have "\<dots> = (active\<^sub>I(P) \<and> $pat\<acute>)"
    by (simp add: TIP_time_active_urgent_conj assms)
  also have "\<dots> = active(P)"
    by (simp add: active_form)
  finally show ?thesis .
qed
*)

(*
lemma TIP_time_active [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active(P) \<and> time(P)) = active(P)"
  (is "?l = ?r")
proof -
  have "?l = (active(P) \<and> (time\<^sub>I(P) \<and> $pat\<acute>))"
    by (simp add: filter_time_def)
  also have "\<dots> = ((active\<^sub>I(P) \<and> $pat\<acute>) \<and> (time\<^sub>I(P) \<and> $pat\<acute>))"
    by (simp add: active_form)
  also have "\<dots> = (active\<^sub>I(P) \<and> time\<^sub>I(P) \<and> $pat\<acute>)"
    by (simp add: utp_pred_laws.inf_left_commute)
  also have "\<dots> = (active\<^sub>I(P) \<and> $pat\<acute>)"
    by (metis TIP_time_active_urgent_conj assms utp_pred_laws.conj_assoc)
  also have "\<dots> = active(P)"
    by (simp add: active_form)
  finally show "?thesis" .
qed
*)

lemma TRF_time_insistant [closure]:
  "P is TRR \<Longrightarrow> time\<^sub>I(P) is TRF"
  apply (rule TRF_intro)
  apply(simp_all add: closure)
  apply(rel_auto+)
  done

(*
lemma TRF_time [closure]:
  "P is TRR \<Longrightarrow> time(P) is TRF"
  by (rule TRF_intro, simp add: closure unrest, simp_all add: filter_time_def unrest)
*)

end