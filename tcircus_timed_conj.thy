theory tcircus_timed_conj
  imports "tcircus_calc" UTP.utp_concurrency
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
            \<and> (\<forall> X Y Z. ((($0:ref = \<guillemotleft>rfset X\<guillemotright>)
                     \<and> ($1:ref = \<guillemotleft>rfset Y\<guillemotright>)
                    \<and> (refusedevts\<^sub>u(Z) = refusedevts\<^sub>u(X)) 
                    \<and> (refusedevts\<^sub>u(Z) = refusedevts\<^sub>u(Y))
                    \<and> (patient(Z) \<Rightarrow> (patient\<^sub>u(X) \<or> patient\<^sub>u(Y)) )
                    \<Rightarrow> ($ref\<acute> = \<guillemotleft>rfset Z\<guillemotright>))))
          \<and> (   (($0:ref = \<guillemotleft>rfnil\<guillemotright>) \<or> ($1:ref = \<guillemotleft>rfnil\<guillemotright>))
               \<Rightarrow> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>))
            )"

(*

*)

lemma MPatConj_sim: "MPatConj is SymMerge"
  apply (rel_auto)
  done

lemma MPatConj_assoc:"AssocMerge MPatConj"
  apply (rel_simp)
  apply(safe)
  oops

definition tconj (infixr "\<squnion>\<^sub>t" 75) where
  [upred_defs]: 
  "(P \<squnion>\<^sub>t Q) = (P \<parallel>\<^bsub>MPatConj\<^esub> Q)"

utp_const tconj


lemma tconj_rfnil1:
  "U(($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>) \<squnion>\<^sub>t ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>))
 = U(($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>) \<or> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>))"
  by (rel_simp)

lemma tconj_rfnil:
  "U((P \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<squnion>\<^sub>t (Q \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))
 = U((P \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)) \<and> (Q \<and> ($ref\<acute> = \<guillemotleft>rfnil\<guillemotright>)))"
  by (rel_auto)

lemma tconj_rfnil2:
  "U(($ref\<acute> = \<guillemotleft>rfset (torefvars E)\<guillemotright>) \<squnion>\<^sub>t ($ref\<acute> = \<guillemotleft>rfset (torefvars F)\<guillemotright>))
 = U($ref\<acute> = \<guillemotleft>rfset (torefvars E)\<guillemotright> \<and> \<guillemotleft>E = F\<guillemotright>)"
  apply(rel_auto)
          apply(simp_all add: patient_torefvars refusedevts_torefvars)
  apply(auto simp add:  torefvars_def refusedevts_def patient_def)
  oops

lemma tconj_rfset:
  "(\<E>(s\<^sub>1,t,torefvars E\<^sub>1) \<squnion>\<^sub>t \<E>(s\<^sub>2, t, torefvars E\<^sub>2)) = \<E>(s\<^sub>1 \<and> s\<^sub>2, t, torefvars (E\<^sub>1 \<union> E\<^sub>2))"
  apply (rel_auto)
  sledgehammer
                 apply (metis refusedevts_eq)
  using refusedevts_eq apply blast
  sledgehammer

end