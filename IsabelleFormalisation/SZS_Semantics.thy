(*  Title:      SZS_Semantics.thy
    Author:     Johannes Schuster

The model theoretic content of the SZS success ontology.

The logical data is a pair \<langle>Ax, C\<rangle> of a set of axioms and a conjecture.  Every
semantic success value is a condition on the two sets of interpretations

    A = the models of Ax        C = the models of C

together, for the finite variants, with the set Fin of finite interpretations.
The models of \<not>C are the complement of C, so every counter value is obtained
from its mirror by writing - C where the mirror writes C.  That is not a
convention imposed here but the content of \<open>holds_mirror\<close> below, from which
the counter half of the ontology follows as a theorem rather than as a second
set of definitions.
*)

theory SZS_Semantics
  imports SZS_Status
begin

section \<open>The semantic locale\<close>

text \<open>
  \<open>Fin\<close> is the set of finite interpretations.  It is a parameter rather than a
  definition because \<open>'i\<close> is an uninterpreted type of interpretations: nothing
  here depends on how finiteness is realised, only on there being enough room
  on both sides of it, which the assumptions of \<open>szs\<close> below supply.

  \<open>szs_base\<close> carries no assumptions, so that \<open>holds\<close> and everything that is
  purely definitional about it — in particular the mirror theorem — hold for
  any choice of \<open>Fin\<close> whatsoever.
\<close>

locale szs_base =
  fixes Fin :: "'i set"
begin

subsection \<open>The status conditions\<close>

primrec holds :: "success \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "holds SUC A C = True"
| "holds SSU A C = True"
| "holds UNP A C = (A = {} \<longrightarrow> C = {})"
| "holds SAP A C = (A \<noteq> {} \<longrightarrow> C \<noteq> {})"
| "holds TAP A C = (A = UNIV \<longrightarrow> C = UNIV)"
| "holds ESA A C = ((A = {}) = (C = {}))"
| "holds ETA A C = ((A = UNIV) = (C = UNIV))"
| "holds SAT A C = (A \<noteq> {} \<and> A \<inter> C \<noteq> {})"
| "holds FSA A C = (A \<inter> Fin \<noteq> {} \<and> A \<inter> C \<inter> Fin \<noteq> {})"
| "holds THM A C = (A \<subseteq> C)"
| "holds FTH A C = (A \<inter> Fin \<subseteq> C)"
| "holds STH A C = (A \<noteq> {} \<and> A \<subseteq> C)"
  \<comment> \<open>Deviation 1.  The leading \<open>A \<noteq> {}\<close> is the clause the 2008 paper has and the
      current page has dropped.  Without it EQV does not imply SAT, contrary to
      the page's own prose and to Table 1 of the paper.\<close>
| "holds EQV A C = (A \<noteq> {} \<and> A = C)"
| "holds TAC A C = (A \<noteq> {} \<and> C = UNIV)"
| "holds WEC A C = (A \<noteq> {} \<and> A \<subseteq> C \<and> C \<inter> - A \<noteq> {})"
| "holds ETH A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> A = C)"
| "holds TAU A C = (A = UNIV \<and> C = UNIV)"
| "holds FTT A C = (Fin \<subseteq> A \<and> Fin \<subseteq> C)"
| "holds WTC A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> C = UNIV)"
| "holds WTH A C = (A \<noteq> {} \<and> A \<subseteq> C \<and> C \<inter> - A \<noteq> {} \<and> C \<noteq> UNIV)"
  \<comment> \<open>Deviation 2.  Conservative extension is a relation between interpretations
      and does not factor through the model sets, so this is the page's own
      parenthetical consequence.  See \<open>mex_strong\<close> below for the strong reading.\<close>
| "holds MEX A C = (A \<noteq> {} \<and> C \<noteq> {} \<and> C \<subseteq> A)"
| "holds NOC A C = (A \<inter> C \<noteq> {} \<and> A \<inter> - C \<noteq> {})"
| "holds CAX A C = (A = {})"
| "holds SCA A C = (A = {} \<and> C \<noteq> {})"
| "holds TCA A C = (A = {} \<and> C = UNIV)"
| "holds WCA A C = (A = {} \<and> C \<noteq> {} \<and> - C \<noteq> {})"
| "holds CUP A C = (A = {} \<longrightarrow> - C = {})"
| "holds CSP A C = (A \<noteq> {} \<longrightarrow> - C \<noteq> {})"
| "holds CTP A C = (A = UNIV \<longrightarrow> - C = UNIV)"
| "holds ECS A C = ((A = {}) = (- C = {}))"
| "holds ECA A C = ((A = UNIV) = (- C = UNIV))"
| "holds CSA A C = (A \<noteq> {} \<and> A \<inter> - C \<noteq> {})"
| "holds FCS A C = (A \<inter> Fin \<noteq> {} \<and> A \<inter> - C \<inter> Fin \<noteq> {})"
| "holds CTH A C = (A \<subseteq> - C)"
| "holds FCT A C = (A \<inter> Fin \<subseteq> - C)"
| "holds SCT A C = (A \<noteq> {} \<and> A \<subseteq> - C)"
| "holds CEQ A C = (A \<noteq> {} \<and> A = - C)"
| "holds UNC A C = (A \<noteq> {} \<and> - C = UNIV)"
| "holds WCC A C = (A \<noteq> {} \<and> A \<subseteq> - C \<and> - C \<inter> - A \<noteq> {})"
| "holds ECT A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> A = - C)"
| "holds UNS A C = (A = UNIV \<and> - C = UNIV)"
  \<comment> \<open>Deviation 3.  This is the 2008 definition, which is the exact mirror of the
      current FTT.  The present page states FUN existentially, which mirrors
      nothing in the ontology, so one of the two has drifted.\<close>
| "holds FUN A C = (Fin \<subseteq> A \<and> Fin \<subseteq> - C)"
| "holds WUC A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> - C = UNIV)"
| "holds WCT A C = (A \<noteq> {} \<and> A \<subseteq> - C \<and> - C \<inter> - A \<noteq> {} \<and> - C \<noteq> UNIV)"
| "holds CMX A C = (A \<noteq> {} \<and> - C \<noteq> {} \<and> - C \<subseteq> A)"
| "holds SCC A C = (A = {} \<and> - C \<noteq> {})"
| "holds UCA A C = (A = {} \<and> - C = UNIV)"
| "holds TSU A C = True"
| "holds TCP A C = True"
| "holds TSC A C = True"
| "holds VSU A C = True"
| "holds VSG A C = True"
| "holds VSB A C = True"


subsection \<open>The mirror theorem\<close>

theorem holds_mirror: "holds (mirror s) A C = holds s A (- C)"
  by (cases s) auto

corollary holds_mirror': "holds s A (- C) = holds (mirror s) A C"
  by (simp add: holds_mirror)


subsection \<open>Redundant conjuncts\<close>

text \<open>
  Three conditions are stated on the page with a conjunct that the rest of the
  condition already implies.  These are kept in \<open>holds\<close> for fidelity to the
  source and discharged here, so that later proofs work with the short form.
\<close>

lemma holds_SAT_iff: "holds SAT A C = (A \<inter> C \<noteq> {})"
  by auto

lemma holds_CSA_iff: "holds CSA A C = (A \<inter> - C \<noteq> {})"
  by auto

lemma holds_FSA_iff: "holds FSA A C = (A \<inter> C \<inter> Fin \<noteq> {})"
  by auto

lemma holds_FCS_iff: "holds FCS A C = (A \<inter> - C \<inter> Fin \<noteq> {})"
  by auto

lemma holds_NOC_iff: "holds NOC A C = (holds SAT A C \<and> holds CSA A C)"
  by auto

text \<open>
  FiniteTheorem is stated as ``all finite models of Ax are finite models of C''.
  A finite interpretation that is a model of C is a finite model of C, so the
  qualification on the right is vacuous and \<open>holds FTH\<close> may be read either way.
\<close>

lemma holds_FTH_iff: "holds FTH A C = (A \<inter> Fin \<subseteq> C \<inter> Fin)"
  by auto

lemma holds_FCT_iff: "holds FCT A C = (A \<inter> Fin \<subseteq> - C \<inter> Fin)"
  by auto


subsection \<open>Values with no model theoretic content\<close>

lemma holds_trivial: "\<not> model_theoretic s \<Longrightarrow> holds s A C"
  by (cases s) (simp_all add: model_theoretic_def)

lemma holds_SUC: "holds SUC A C"
  by simp

lemma holds_SSU: "holds SSU A C"
  by simp


subsection \<open>The strong reading of ModelExtending\<close>

text \<open>
  \<open>mex_strong ext A C\<close> is the page's literal condition: every model of C is a
  conservative extension of some model of Ax.  It implies \<open>holds MEX\<close> exactly
  when A is closed under the extension relation, which is the assumption the
  page leaves in a parenthesis.  Stating it explicitly keeps the derived order
  valid under both readings, since every edge proved from \<open>holds MEX\<close> is then
  also available under the strong one.
\<close>

definition ext_closed :: "('i \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "ext_closed ext A \<longleftrightarrow> (\<forall>x y. x \<in> A \<longrightarrow> ext y x \<longrightarrow> y \<in> A)"

definition mex_strong :: "('i \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "mex_strong ext A C \<longleftrightarrow> A \<noteq> {} \<and> C \<noteq> {} \<and> (\<forall>y \<in> C. \<exists>x \<in> A. ext y x)"

lemma mex_strong_imp_MEX:
  assumes "ext_closed ext A" and "mex_strong ext A C"
  shows "holds MEX A C"
  using assms unfolding ext_closed_def mex_strong_def by auto

definition cmx_strong :: "('i \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "cmx_strong ext A C \<longleftrightarrow> mex_strong ext A (- C)"

lemma cmx_strong_imp_CMX:
  assumes "ext_closed ext A" and "cmx_strong ext A C"
  shows "holds CMX A C"
  using assms mex_strong_imp_MEX [of ext A "- C"]
  unfolding cmx_strong_def by simp


section \<open>The four relationships\<close>

text \<open>
  The names follow the 2008 paper: \<open>isa\<close> is entailment, \<open>nota\<close> its negation,
  \<open>nevera\<close> incompatibility, and \<open>xora\<close> exhaustive incompatibility.  Defining all
  four here makes the comparison against Table 1 of that paper expressible in
  SZS\_Hierarchy without further machinery.
\<close>

definition isa :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "isa s t \<longleftrightarrow> (\<forall>A C. holds s A C \<longrightarrow> holds t A C)"

definition nota :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nota s t \<longleftrightarrow> (\<exists>A C. holds s A C \<and> \<not> holds t A C)"

definition nevera :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nevera s t \<longleftrightarrow> (\<forall>A C. holds s A C \<longrightarrow> \<not> holds t A C)"

definition xora :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "xora s t \<longleftrightarrow> (\<forall>A C. holds s A C \<noteq> holds t A C)"

lemma nota_iff: "nota s t \<longleftrightarrow> \<not> isa s t"
  unfolding nota_def isa_def by blast

lemma xora_imp_nevera: "xora s t \<Longrightarrow> nevera s t"
  unfolding xora_def nevera_def by blast

lemma nevera_sym: "nevera s t \<Longrightarrow> nevera t s"
  unfolding nevera_def by blast

lemma xora_sym: "xora s t \<Longrightarrow> xora t s"
  unfolding xora_def by blast

lemma isa_refl [simp]: "isa s s"
  unfolding isa_def by blast

lemma isa_trans: "isa s t \<Longrightarrow> isa t u \<Longrightarrow> isa s u"
  unfolding isa_def by blast

lemma isa_antisym_holds: "isa s t \<Longrightarrow> isa t s \<Longrightarrow> holds s A C = holds t A C"
  unfolding isa_def by blast

text \<open>
  \<open>isa\<close> is a preorder, not an order: distinct values may be semantically
  equivalent.  The eight values outside \<open>model_theoretic\<close> are all equivalent to
  each other, which is why they are excluded from the derived hierarchy and
  given stipulated edges instead.
\<close>

lemma isa_trivial:
  assumes "\<not> model_theoretic s" and "\<not> model_theoretic t"
  shows "isa s t"
  unfolding isa_def using holds_trivial [OF assms(2)] by blast

lemma isa_into_trivial: "\<not> model_theoretic t \<Longrightarrow> isa s t"
  unfolding isa_def using holds_trivial by blast

corollary isa_SUC [simp]: "isa s SUC"
  unfolding isa_def by simp


subsection \<open>Mirror compatibility\<close>

theorem isa_mirror: "isa s t \<Longrightarrow> isa (mirror s) (mirror t)"
  unfolding isa_def by (metis holds_mirror)

corollary isa_mirror_iff: "isa (mirror s) (mirror t) \<longleftrightarrow> isa s t"
  by (metis isa_mirror mirror_involution)

corollary nota_mirror_iff: "nota (mirror s) (mirror t) \<longleftrightarrow> nota s t"
  by (simp add: nota_iff isa_mirror_iff)

theorem nevera_mirror_iff: "nevera (mirror s) (mirror t) \<longleftrightarrow> nevera s t"
  unfolding nevera_def by (metis holds_mirror mirror_involution)

theorem xora_mirror_iff: "xora (mirror s) (mirror t) \<longleftrightarrow> xora s t"
  unfolding xora_def by (metis holds_mirror mirror_involution)

end


section \<open>The populated locale\<close>

text \<open>
  For refutations we need a type of interpretations with room on both sides of
  the finiteness boundary: infinitely many finite interpretations and
  infinitely many infinite ones.  Both are true of any real interpretation
  space, and together they give every shape in SZS\_Shapes a witness.
\<close>

locale szs = szs_base Fin for Fin :: "'i set" +
  assumes Fin_infinite: "infinite Fin"
      and coFin_infinite: "infinite (- Fin)"
begin

lemma Fin_nonempty [simp]: "Fin \<noteq> {}"
  using Fin_infinite by auto

lemma coFin_nonempty [simp]: "- Fin \<noteq> {}"
  using coFin_infinite by auto

lemma Fin_neq_UNIV [simp]: "Fin \<noteq> UNIV"
  using coFin_nonempty by blast

lemma UNIV_nonempty [simp]: "(UNIV :: 'i set) \<noteq> {}"
  using Fin_nonempty by auto


subsection \<open>The disputed edges\<close>

text \<open>
  The results below are the ones at issue in the correspondence with the TPTP
  maintainer.  Each is stated as a single lemma so that it can be quoted
  directly.  All of them concern values added to the ontology after the 2008
  validation; the values validated then come through unchanged.
\<close>

paragraph \<open>ModelExtending belongs below Satisfiable.\<close>

lemma isa_MEX_SAT: "isa MEX SAT"
  unfolding isa_def by auto

lemma isa_CMX_CSA: "isa CMX CSA"
  by (simp add: Int_absorb1 isa_def)

lemma not_isa_SAT_MEX: "\<not> isa SAT MEX"
  unfolding isa_def
  by (metis Fin_neq_UNIV Fin_nonempty Int_UNIV_right subset_UNIV subset_antisym szs_base.holds.simps(21)
      szs_base.holds_SAT_iff)

paragraph \<open>EquiTautologous does not preserve satisfiability.\<close>

lemma not_isa_ETA_SAP: "\<not> isa ETA SAP"
proof -
  have "holds ETA Fin {}" by simp
  moreover have "\<not> holds SAP Fin {}" by simp
  ultimately show ?thesis unfolding isa_def by blast
qed

lemma not_isa_ECA_CSP: "\<not> isa ECA CSP"
  by (metis not_isa_ETA_SAP isa_mirror_iff mirror.simps(7) mirror.simps(4))

lemma isa_ETA_TAP: "isa ETA TAP"
  unfolding isa_def by auto

paragraph \<open>Theorem preserves tautologousness, mirroring CounterTheorem.\<close>

lemma isa_THM_TAP: "isa THM TAP"
  unfolding isa_def by auto

lemma isa_CTH_CTP: "isa CTH CTP"
  by (metis isa_THM_TAP isa_mirror mirror.simps(10) mirror.simps(5))

paragraph \<open>The finite variants of the universal values sit above, not below.\<close>

lemma isa_TAU_FTT: "isa TAU FTT"
  unfolding isa_def by auto

lemma not_isa_FTT_TAU: "\<not> isa FTT TAU"
proof -
  have "holds FTT Fin Fin" by simp
  moreover have "\<not> holds TAU Fin Fin" by simp
  ultimately show ?thesis unfolding isa_def by blast
qed

lemma isa_UNS_FUN: "isa UNS FUN"
  by (metis isa_TAU_FTT isa_mirror mirror.simps(17) mirror.simps(18))

lemma not_isa_FUN_UNS: "\<not> isa FUN UNS"
  by (metis not_isa_FTT_TAU isa_mirror_iff mirror.simps(18) mirror.simps(17))

lemma isa_FTT_FTH: "isa FTT FTH"
  unfolding isa_def by auto

lemma isa_THM_FTH: "isa THM FTH"
  unfolding isa_def by auto

paragraph \<open>The finite variants of the existential values sit below.\<close>

lemma isa_FSA_SAT: "isa FSA SAT"
  unfolding isa_def by auto

lemma isa_FCS_CSA: "isa FCS CSA"
  by (metis isa_FSA_SAT isa_mirror mirror.simps(9) mirror.simps(8))

paragraph \<open>The two long cross links of the 2008 figure, absent from the current one.\<close>

lemma isa_CSA_UNP: "isa CSA UNP"
  unfolding isa_def by auto

lemma isa_SAT_CUP: "isa SAT CUP"
  by (metis isa_CSA_UNP isa_mirror mirror.simps(32) mirror.simps(3))

paragraph \<open>Equivalent, with the clause the current page has dropped.\<close>

lemma isa_EQV_SAT: "isa EQV SAT"
  unfolding isa_def by auto

lemma isa_EQV_THM: "isa EQV THM"
  unfolding isa_def by auto

lemma isa_EQV_STH: "isa EQV STH"
  unfolding isa_def by auto

paragraph \<open>Theorem does not imply Satisfiable; the paper's THM nota SAT.\<close>

lemma not_isa_THM_SAT: "\<not> isa THM SAT"
proof -
  have "holds THM {} {}" by simp
  moreover have "\<not> holds SAT {} {}" by simp
  ultimately show ?thesis unfolding isa_def by blast
qed

lemma isa_CAX_THM: "isa CAX THM"
  unfolding isa_def by auto

lemma isa_CAX_CTH: "isa CAX CTH"
  unfolding isa_def by auto

lemma xora_THM_CSA: "xora THM CSA"
  unfolding xora_def by auto

end


section \<open>A concrete instance\<close>

text \<open>
  The naturals with the even numbers standing in for the finite
  interpretations.  Nothing depends on this choice; it exists so that the
  locale is known to be inhabited and so that \<open>nitpick\<close> and \<open>quickcheck\<close> have
  something to work with when a conjectured edge is in doubt.
\<close>

definition Evens :: "nat set" where
  "Evens = {n. even n}"

lemma infinite_Evens: "infinite Evens"
proof -
  have "range (\<lambda>n. 2 * n) \<subseteq> Evens" by (auto simp: Evens_def)
  moreover have "infinite (range (\<lambda>n :: nat. 2 * n))"
    by (simp add: finite_image_iff inj_on_def)
  ultimately show ?thesis using finite_subset by blast
qed

lemma infinite_coEvens: "infinite (- Evens)"
proof -
  have "range (\<lambda>n. 2 * n + 1) \<subseteq> - Evens" by (auto simp: Evens_def)
  moreover have "infinite (range (\<lambda>n :: nat. 2 * n + 1))"
    by (simp add: finite_image_iff inj_on_def)
  ultimately show ?thesis using finite_subset by blast
qed

interpretation szs_nat: szs Evens
  by unfold_locales (rule infinite_Evens, rule infinite_coEvens)


section \<open>Deviations from the published text\<close>

text \<open>
  \begin{description}
  \item[EQV] \<open>holds EQV\<close> carries the leading \<open>A \<noteq> {}\<close>.  The 2008 paper states
    the value with that clause; the current page omits it.  Without it EQV holds
    vacuously when Ax and C are both unsatisfiable, so EQV would not imply SAT,
    contradicting the page's own prose and the proved Table 1.  Recorded as
    \<open>isa_EQV_SAT\<close>.
  \item[MEX, CMX] Stated as the page's parenthetical consequence — every model
    of C is a model of Ax — rather than as conservative extension, which does
    not factor through model sets.  The strong reading is available as
    \<open>mex_strong\<close>, and \<open>mex_strong_imp_MEX\<close> shows that every edge proved here
    also holds under it, given that the models of Ax are closed under extension.
  \item[FUN] Stated as in the 2008 paper, making it the exact mirror of the
    current FTT.  The present page gives FUN an existential first clause, which
    is the mirror of nothing in the ontology.  Under either reading \<open>isa UNS FUN\<close>
    holds and \<open>isa FUN UNS\<close> fails, so the placement correction is independent of
    this choice.
  \end{description}
\<close>

end