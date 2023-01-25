theory tcircus_timed_conj
  imports "tcircus_rel" UTP.utp_concurrency
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
            \<and> ($st\<acute> = $1:st
            \<and> ($ref\<acute> = $0:ref)
            \<and> ($ref\<acute> = $1:ref)
            \<and> ($pat\<acute> = ($0:pat \<and> $1:pat)))
            )"

(*

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

lemma tconj_rfnil:
  "U((P \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<squnion>\<^sub>t (Q \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))
 = U((P \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<and> (Q \<and> $pat\<acute> \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))"
  apply (rel_auto)
  by blast

lemma tconj_patient:
  "U((P \<and> $pat\<acute>) \<squnion>\<^sub>t (Q \<and> $pat\<acute>))
 = U((P \<and> $pat\<acute>) \<and> (Q \<and> $pat\<acute>))"
  apply (rel_auto)
  by blast


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