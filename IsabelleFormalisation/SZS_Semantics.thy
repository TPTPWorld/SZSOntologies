(*  Title:      SZS_Semantics.thy
    Author:     Johannes Schuster
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause

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
| "holds EQV A C = (A \<noteq> {} \<and> A = C)"
| "holds TAC A C = (A \<noteq> {} \<and> C = UNIV)"
| "holds WEC A C = (A \<noteq> {} \<and> A \<subseteq> C \<and> C \<inter> - A \<noteq> {})"
| "holds ETH A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> A = C)"
| "holds TAU A C = (A = UNIV \<and> C = UNIV)"
| "holds FTT A C = (Fin \<subseteq> A \<and> Fin \<subseteq> C)"
| "holds WTC A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> C = UNIV)"
| "holds WTH A C = (A \<noteq> {} \<and> A \<subseteq> C \<and> C \<inter> - A \<noteq> {} \<and> C \<noteq> UNIV)"
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
| "holds FUN A C = (Fin \<subseteq> A \<and> Fin \<subseteq> - C)"
| "holds WUC A C = (A \<noteq> {} \<and> A \<noteq> UNIV \<and> - C = UNIV)"
| "holds WCT A C = (A \<noteq> {} \<and> A \<subseteq> - C \<and> - C \<inter> - A \<noteq> {} \<and> - C \<noteq> UNIV)"
| "holds CMX A C = (A \<noteq> {} \<and> - C \<noteq> {} \<and> - C \<subseteq> A)"
| "holds SCC A C = (A = {} \<and> - C \<noteq> {})"
| "holds UCA A C = (A = {} \<and> - C = UNIV)"
| "holds TSU A C = True"
| "holds TCP A C = True"
| "holds TCC A C = True"
| "holds VSU A C = True"
| "holds VSG A C = True"
| "holds VSB A C = True"


subsection \<open>The mirror theorem\<close>

theorem holds_mirror: "holds (mirror s) A C = holds s A (- C)"
  by (cases s) auto


subsection \<open>Redundant conjuncts\<close>

text \<open>
  Three conditions carry a conjunct that the rest of the condition already
  implies.  They are kept in \<open>holds\<close> as stated and discharged here, so that
  later proofs work with the short form.
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


section \<open>The four relationships\<close>

text \<open>
  \<open>isa\<close> is entailment, \<open>nota\<close> its negation, \<open>nevera\<close> incompatibility, \<open>xora\<close>
  exhaustive incompatibility, and \<open>mighta\<close> joint satisfiability.  All five are
  defined over \<open>holds\<close>, so each is decided by the shape enumeration of
  SZS_Shapes.
\<close>

definition isa :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "isa s t \<equiv> (\<forall>A C. holds s A C \<longrightarrow> holds t A C)"

definition nota :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nota s t \<equiv> (\<exists>A C. holds s A C \<and> \<not> holds t A C)"

definition nevera :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nevera s t \<equiv> (\<forall>A C. holds s A C \<longrightarrow> \<not> holds t A C)"

definition xora :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "xora s t \<equiv> (\<forall>A C. holds s A C \<noteq> holds t A C)"

definition mighta :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "mighta s t \<equiv> (\<exists>A C. holds s A C \<and> holds t A C)"

lemma nota_iff: "nota s t \<longleftrightarrow> \<not> isa s t"
  unfolding nota_def isa_def by blast

lemma mighta_iff: "mighta s t \<longleftrightarrow> \<not> nevera s t"
  unfolding mighta_def nevera_def by blast

lemma xora_imp_nevera: "xora s t \<Longrightarrow> nevera s t"
  unfolding xora_def nevera_def by blast

lemma nevera_sym: "nevera s t \<Longrightarrow> nevera t s"
  unfolding nevera_def by blast

lemma xora_sym: "xora s t \<Longrightarrow> xora t s"
  unfolding xora_def by blast

lemma mighta_sym: "mighta s t \<Longrightarrow> mighta t s"
  unfolding mighta_def by blast

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

theorem mighta_mirror_iff: "mighta (mirror s) (mirror t) \<longleftrightarrow> mighta s t"
  by (simp add: mighta_iff nevera_mirror_iff)

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

end


section \<open>Signature extension\<close>

text \<open>
  Ax and C need not share a signature: C may be stated over an extension of the
  signature of Ax, and the page's ModelExtending is a condition relating the
  two.  \<open>r\<close> is the reduct map from interpretations of the extended signature to
  interpretations of the signature of Ax.  Two modelling assumptions are made:
  \<open>r\<close> is surjective, so every Ax-structure has an expansion, and \<open>Fin_j\<close> is the
  preimage of \<open>Fin\<close>, so an expansion has the domain of its reduct.  The second
  fails for Henkin frames in which a new type contributes to the structure.
\<close>

locale szs_ext = szs Fin for Fin :: "'i set" +
  fixes r :: "'j \<Rightarrow> 'i"
  assumes surj_r: "surj r"
begin

definition Fin_j :: "'j set" where
  "Fin_j = r -` Fin"

definition mex_sig :: "'i set \<Rightarrow> 'j set \<Rightarrow> bool" where
  "mex_sig A C \<longleftrightarrow> A \<noteq> {} \<and> C \<noteq> {} \<and> r ` C \<subseteq> A"

definition cmx_sig :: "'i set \<Rightarrow> 'j set \<Rightarrow> bool" where
  "cmx_sig A C \<longleftrightarrow> mex_sig A (- C)"

subsection \<open>Preimages\<close>

lemma vimage_empty_iff [simp]: "r -` S = {} \<longleftrightarrow> S = {}"
  using surj_r by (simp add: surj_vimage_empty)

lemma image_vimage_r [simp]: "r ` (r -` S) = S"
  using surj_r by (auto simp: surj_def)

lemma image_subset_vimage: "r ` C \<subseteq> A \<longleftrightarrow> C \<subseteq> r -` A"
  by auto

lemma vimage_infinite:
  assumes "infinite S" shows "infinite (r -` S)"
  by (metis assms finite_imageI image_vimage_r)

lemma szs_Fin_j: "szs Fin_j"
proof unfold_locales
  show "infinite Fin_j"
    unfolding Fin_j_def by (rule vimage_infinite [OF Fin_infinite])
  have "- Fin_j = r -` (- Fin)" by (auto simp: Fin_j_def)
  then show "infinite (- Fin_j)"
    using vimage_infinite [OF coFin_infinite] by simp
qed

subsection \<open>Factorisation\<close>

lemma mex_sig_iff: "mex_sig A C \<longleftrightarrow> szs_base.holds Fin_j MEX (r -` A) C"
  by (simp add: mex_sig_def szs_base.holds.simps image_subset_vimage)

lemma cmx_sig_iff: "cmx_sig A C \<longleftrightarrow> szs_base.holds Fin_j CMX (r -` A) C"
  by (simp add: cmx_sig_def mex_sig_def szs_base.holds.simps image_subset_vimage)

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

end