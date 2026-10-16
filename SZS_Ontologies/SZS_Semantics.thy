(*  Title:      SZS_Semantics.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_Semantics
  imports SZS_Status
begin

section \<open>Semantics\<close>

text \<open>
  Every semantic value is a condition on the set \<open>A\<close> of models of Ax, the set
  \<open>C\<close> of models of C and the set \<open>Fin\<close> of finite interpretations.  The models
  of \<open>\<not> C\<close> are \<open>- C\<close>, and \<open>holds_mirror\<close> derives the counter values from the
  positive ones.
\<close>

subsection \<open>The semantic locale\<close>

text \<open>
  \<open>'i\<close> is an uninterpreted type of interpretations and \<open>Fin\<close> a parameter.
  \<open>szs_base\<close> makes no assumption on \<open>Fin\<close>; \<open>holds\<close> and the mirror theorem hold
  for every choice.
\<close>

locale szs_base =
  fixes Fin :: "'i set"
begin

subsubsection \<open>The status conditions\<close>

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


subsubsection \<open>The mirror theorem\<close>

theorem holds_mirror: "holds (mirror s) A C = holds s A (- C)"
  by (cases s) auto


subsubsection \<open>Redundant conjuncts\<close>

text \<open>
  Three conditions contain a conjunct implied by the rest.  The short forms
  are proved here.
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
  A finite interpretation that is a model of C is a finite model of C, so the
  qualification on the right of FiniteTheorem is vacuous.
\<close>

lemma holds_FTH_iff: "holds FTH A C = (A \<inter> Fin \<subseteq> C \<inter> Fin)"
  by auto

lemma holds_FCT_iff: "holds FCT A C = (A \<inter> Fin \<subseteq> - C \<inter> Fin)"
  by auto


subsubsection \<open>Values with no model theoretic content\<close>

lemma holds_trivial: "\<not> model_theoretic s \<Longrightarrow> holds s A C"
  by (cases s) (simp_all add: model_theoretic_def)

lemma holds_SUC: "holds SUC A C"
  by simp

lemma holds_SSU: "holds SSU A C"
  by simp


subsection \<open>The four relationships\<close>

text \<open>
  \<open>isa\<close> is entailment, \<open>nota\<close> its negation, \<open>nevera\<close> incompatibility, \<open>xora\<close>
  exhaustive incompatibility and \<open>mighta\<close> joint satisfiability.
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
  \<open>isa\<close> is a preorder.  The eight values outside \<open>model_theoretic\<close> are
  equivalent to each other.
\<close>

lemma isa_trivial:
  assumes "\<not> model_theoretic s" and "\<not> model_theoretic t"
  shows "isa s t"
  unfolding isa_def using holds_trivial [OF assms(2)] by blast

lemma isa_into_trivial: "\<not> model_theoretic t \<Longrightarrow> isa s t"
  unfolding isa_def using holds_trivial by blast

corollary isa_SUC [simp]: "isa s SUC"
  unfolding isa_def by simp


subsubsection \<open>Mirror compatibility\<close>

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


subsection \<open>The populated locale\<close>

text \<open>
  The refutations need infinitely many finite and infinitely many infinite
  interpretations.  Under these assumptions every shape of SZS\_Shapes has a
  witness.
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


subsection \<open>Signature extension\<close>

text \<open>
  C may be stated over an extension of the signature of Ax.  ModelExtending is
  meant for Skolemisation: C is over a conservative extension of the signature
  of Ax, and every model of C is a conservative extension of a model of Ax.
  \<open>r\<close> maps an interpretation of the extended signature to its reduct.  \<open>r\<close> is
  assumed surjective, and \<open>Fin_j\<close> is the preimage of \<open>Fin\<close>, so an expansion
  has the domain of its reduct.  The second assumption fails for Henkin frames
  in which a new type contributes to the structure.
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

subsubsection \<open>Preimages\<close>

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

subsubsection \<open>Factorisation\<close>

lemma mex_sig_iff: "mex_sig A C \<longleftrightarrow> szs_base.holds Fin_j MEX (r -` A) C"
  by (simp add: mex_sig_def szs_base.holds.simps image_subset_vimage)

lemma cmx_sig_iff: "cmx_sig A C \<longleftrightarrow> szs_base.holds Fin_j CMX (r -` A) C"
  by (simp add: cmx_sig_def mex_sig_def szs_base.holds.simps image_subset_vimage)

end


subsection \<open>A concrete instance\<close>

text \<open>
  The naturals, with the even numbers as the finite interpretations.  The
  instance shows the locale inhabited and gives \<open>nitpick\<close> and \<open>quickcheck\<close>
  something to run on.
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