section \<open> Refusal Tests \<close>

theory Patience_Tests
  imports Main
begin

subsection \<open> Patience Sets \<close>

datatype patience = unpat | pat bool ("[_]\<^sub>\<P>")

instantiation patience :: order
begin
  fun less_eq_patience :: "patience \<Rightarrow> patience \<Rightarrow> bool" where
  "unpat \<le> S = True" |
  "R \<le> unpat = (R = unpat)" |
  "[p]\<^sub>\<P> \<le> [q]\<^sub>\<P> = (p \<longrightarrow> q)"
  definition less_patience :: "patience \<Rightarrow> patience \<Rightarrow> bool" where
  "less_patience S R = (S \<le> R \<and> \<not> R \<le> S)"
instance proof
  fix x y z :: "patience"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_patience_def)
  show "x \<le> x"
    by (cases x, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Patience_Tests.less_eq_patience.elims(2) less_eq_patience.simps(2) patience.inject)
qed
end

(*
abbreviation rsubseteq :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>\<R> _)" [51, 51] 50) where 
"S \<subseteq>\<^sub>\<R> R \<equiv> S \<le> R"

fun rmember :: "'a \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<in>\<^sub>\<R> _)" [51, 51] 50) where
"x \<in>\<^sub>\<R> \<^bold>\<bullet> = False" | "x \<in>\<^sub>\<R> [R]\<^sub>\<R> = (x \<in> R)"

abbreviation rnot_member ("(_/ \<notin>\<^sub>\<R> _)" [51, 51] 50)
  where "rnot_member x A \<equiv> \<not> (x \<in>\<^sub>\<R>  A)"

lemma rfnil_mem_dest [dest]: "x \<in>\<^sub>\<R> \<^bold>\<bullet> \<Longrightarrow> P"
  by (metis rmember.simps(1))
*)

instantiation patience :: lattice
begin
  fun sup_patience :: "patience \<Rightarrow> patience \<Rightarrow> patience"  where
  "sup unpat R = R" |
  "sup S unpat = S" |
  "sup [S]\<^sub>\<P> [R]\<^sub>\<P> = [S \<or> R]\<^sub>\<P>"

  fun inf_patience :: "patience \<Rightarrow> patience \<Rightarrow> patience"  where
  "inf unpat R = unpat" |
  "inf S unpat = unpat" |
  "inf [S]\<^sub>\<P> [R]\<^sub>\<P> = [S \<and> R]\<^sub>\<P>"
instance proof
  fix x y z :: "patience"
  show "inf x y \<le> x"
    by (cases x, simp_all, cases y, simp_all)
  show "inf x y \<le> y"
    by (cases x, simp_all, cases y, simp_all)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<le> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<le> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all, cases y, simp_all, cases y, simp_all)
qed
end

end