(*  Title:      SZS_Shapes.thy
    Author:     Johannes Schuster
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause

An abstraction of \<langle>Ax, C\<rangle> down to a finite space, a decision procedure for
entailment between SZS success values, and its completeness.

Every condition in SZS_Semantics constrains the two sets A and C only through
the four regions

    A \<inter> C      A - C      C - A      -(A \<union> C)

and, for the finite variants, through whether each region contains a finite
interpretation.  Recording for each region whether it is empty, nonempty with
no finite member, or has a finite member gives a space of 81 shapes, of which
65 are realizable.  Entailment between status values is then a finite check.

Everything except \<open>shape_of\<close> is independent of the interpretation type and of
the finiteness parameter, so the check \<open>isa_chk\<close> lives at theory level and is
executable.  The locale supplies only the bridge to the model theory.
*)

theory SZS_Shapes
  imports SZS_Semantics
begin

section \<open>Regions and shapes\<close>

datatype region = AC | AnC | nAC | nAnC

definition all_regions :: "region list" where
  "all_regions = [AC, AnC, nAC, nAnC]"

lemma all_regions_UNIV [simp]: "set all_regions = UNIV"
proof -
  have "r \<in> set all_regions" for r
    by (cases r) (simp_all add: all_regions_def)
  then show ?thesis by auto
qed

text \<open>
  \<open>FEmpty\<close> is an empty region, \<open>FInf\<close> a region that is nonempty but contains no
  finite interpretation, \<open>FFin\<close> a region that contains at least one finite
  interpretation.  \<open>FFin\<close> therefore implies nonemptiness.
\<close>

datatype fill = FEmpty | FInf | FFin

definition all_fills :: "fill list" where
  "all_fills = [FEmpty, FInf, FFin]"

lemma all_fills_UNIV [simp]: "set all_fills = UNIV"
proof -
  have "a \<in> set all_fills" for a
    by (cases a) (simp_all add: all_fills_def)
  then show ?thesis by auto
qed

type_synonym shape = "region \<Rightarrow> fill"

definition mk_shape :: "fill \<Rightarrow> fill \<Rightarrow> fill \<Rightarrow> fill \<Rightarrow> shape" where
  "mk_shape a b c d =
     (\<lambda>r. case r of AC \<Rightarrow> a | AnC \<Rightarrow> b | nAC \<Rightarrow> c | nAnC \<Rightarrow> d)"

lemma mk_shape_simps [simp]:
  "mk_shape a b c d AC = a"
  "mk_shape a b c d AnC = b"
  "mk_shape a b c d nAC = c"
  "mk_shape a b c d nAnC = d"
  by (simp_all add: mk_shape_def)

lemma shape_expand: "\<sigma> = mk_shape (\<sigma> AC) (\<sigma> AnC) (\<sigma> nAC) (\<sigma> nAnC)"
proof (rule ext)
  fix r show "\<sigma> r = mk_shape (\<sigma> AC) (\<sigma> AnC) (\<sigma> nAC) (\<sigma> nAnC) r"
    by (cases r) simp_all
qed

definition quads :: "(fill \<times> fill \<times> fill \<times> fill) list" where
  "quads = [(a, b, c, d). a \<leftarrow> all_fills, b \<leftarrow> all_fills, c \<leftarrow> all_fills, d \<leftarrow> all_fills]"

lemma quads_complete: "(a, b, c, d) \<in> set quads"
  by (cases a; cases b; cases c; cases d) (simp_all add: quads_def all_fills_def)

lemma length_quads: "length quads = 81"
  by (simp add: quads_def all_fills_def)


section \<open>Shape level abbreviations\<close>

text \<open>
  The conditions that recur across the status definitions, expressed on shapes.
  Each is justified against the sets by a lemma in the locale below.
\<close>

definition sA_empty :: "shape \<Rightarrow> bool" where
  "sA_empty \<sigma> \<longleftrightarrow> \<sigma> AC = FEmpty \<and> \<sigma> AnC = FEmpty"

definition sC_empty :: "shape \<Rightarrow> bool" where
  "sC_empty \<sigma> \<longleftrightarrow> \<sigma> AC = FEmpty \<and> \<sigma> nAC = FEmpty"

definition sA_univ :: "shape \<Rightarrow> bool" where
  "sA_univ \<sigma> \<longleftrightarrow> \<sigma> nAC = FEmpty \<and> \<sigma> nAnC = FEmpty"

definition sC_univ :: "shape \<Rightarrow> bool" where
  "sC_univ \<sigma> \<longleftrightarrow> \<sigma> AnC = FEmpty \<and> \<sigma> nAnC = FEmpty"

definition sA_fin :: "shape \<Rightarrow> bool" where
  "sA_fin \<sigma> \<longleftrightarrow> \<sigma> AC = FFin \<or> \<sigma> AnC = FFin"

definition sFin_sub_A :: "shape \<Rightarrow> bool" where
  "sFin_sub_A \<sigma> \<longleftrightarrow> \<sigma> nAC \<noteq> FFin \<and> \<sigma> nAnC \<noteq> FFin"

definition sFin_sub_C :: "shape \<Rightarrow> bool" where
  "sFin_sub_C \<sigma> \<longleftrightarrow> \<sigma> AnC \<noteq> FFin \<and> \<sigma> nAnC \<noteq> FFin"

definition sFin_sub_nC :: "shape \<Rightarrow> bool" where
  "sFin_sub_nC \<sigma> \<longleftrightarrow> \<sigma> AC \<noteq> FFin \<and> \<sigma> nAC \<noteq> FFin"


section \<open>The status conditions on shapes\<close>

text \<open>
  One equation per value, in the order of \<open>holds\<close>.  Note that \<open>- C = {}\<close> is
  \<open>sC_univ\<close>, \<open>- C = UNIV\<close> is \<open>sC_empty\<close>, \<open>- C \<subseteq> A\<close> is \<open>\<sigma> nAnC = FEmpty\<close>, and
  \<open>- C - A\<close> is the region \<open>nAnC\<close>; that is the whole of the translation for the
  counter half.
\<close>

primrec holds_shape :: "success \<Rightarrow> shape \<Rightarrow> bool" where
  "holds_shape SUC \<sigma> = True"
| "holds_shape SSU \<sigma> = True"
| "holds_shape UNP \<sigma> = (sA_empty \<sigma> \<longrightarrow> sC_empty \<sigma>)"
| "holds_shape SAP \<sigma> = (\<not> sA_empty \<sigma> \<longrightarrow> \<not> sC_empty \<sigma>)"
| "holds_shape TAP \<sigma> = (sA_univ \<sigma> \<longrightarrow> sC_univ \<sigma>)"
| "holds_shape ESA \<sigma> = (sA_empty \<sigma> = sC_empty \<sigma>)"
| "holds_shape ETA \<sigma> = (sA_univ \<sigma> = sC_univ \<sigma>)"
| "holds_shape SAT \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AC \<noteq> FEmpty)"
| "holds_shape FSA \<sigma> = (sA_fin \<sigma> \<and> \<sigma> AC = FFin)"
| "holds_shape THM \<sigma> = (\<sigma> AnC = FEmpty)"
| "holds_shape FTH \<sigma> = (\<sigma> AnC \<noteq> FFin)"
| "holds_shape STH \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AnC = FEmpty)"
| "holds_shape EQV \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AnC = FEmpty \<and> \<sigma> nAC = FEmpty)"
| "holds_shape TAC \<sigma> = (\<not> sA_empty \<sigma> \<and> sC_univ \<sigma>)"
| "holds_shape WEC \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AnC = FEmpty \<and> \<sigma> nAC \<noteq> FEmpty)"
| "holds_shape ETH \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sA_univ \<sigma> \<and> \<sigma> AnC = FEmpty \<and> \<sigma> nAC = FEmpty)"
| "holds_shape TAU \<sigma> = (sA_univ \<sigma> \<and> sC_univ \<sigma>)"
| "holds_shape FTT \<sigma> = (sFin_sub_A \<sigma> \<and> sFin_sub_C \<sigma>)"
| "holds_shape WTC \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sA_univ \<sigma> \<and> sC_univ \<sigma>)"
| "holds_shape WTH \<sigma> =
     (\<not> sA_empty \<sigma> \<and> \<sigma> AnC = FEmpty \<and> \<sigma> nAC \<noteq> FEmpty \<and> \<not> sC_univ \<sigma>)"
| "holds_shape MEX \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sC_empty \<sigma> \<and> \<sigma> nAC = FEmpty)"
| "holds_shape NOC \<sigma> = (\<sigma> AC \<noteq> FEmpty \<and> \<sigma> AnC \<noteq> FEmpty)"
| "holds_shape CAX \<sigma> = sA_empty \<sigma>"
| "holds_shape SCA \<sigma> = (sA_empty \<sigma> \<and> \<not> sC_empty \<sigma>)"
| "holds_shape TCA \<sigma> = (sA_empty \<sigma> \<and> sC_univ \<sigma>)"
| "holds_shape WCA \<sigma> = (sA_empty \<sigma> \<and> \<not> sC_empty \<sigma> \<and> \<not> sC_univ \<sigma>)"
| "holds_shape CUP \<sigma> = (sA_empty \<sigma> \<longrightarrow> sC_univ \<sigma>)"
| "holds_shape CSP \<sigma> = (\<not> sA_empty \<sigma> \<longrightarrow> \<not> sC_univ \<sigma>)"
| "holds_shape CTP \<sigma> = (sA_univ \<sigma> \<longrightarrow> sC_empty \<sigma>)"
| "holds_shape ECS \<sigma> = (sA_empty \<sigma> = sC_univ \<sigma>)"
| "holds_shape ECA \<sigma> = (sA_univ \<sigma> = sC_empty \<sigma>)"
| "holds_shape CSA \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AnC \<noteq> FEmpty)"
| "holds_shape FCS \<sigma> = (sA_fin \<sigma> \<and> \<sigma> AnC = FFin)"
| "holds_shape CTH \<sigma> = (\<sigma> AC = FEmpty)"
| "holds_shape FCT \<sigma> = (\<sigma> AC \<noteq> FFin)"
| "holds_shape SCT \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AC = FEmpty)"
| "holds_shape CEQ \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AC = FEmpty \<and> \<sigma> nAnC = FEmpty)"
| "holds_shape UNC \<sigma> = (\<not> sA_empty \<sigma> \<and> sC_empty \<sigma>)"
| "holds_shape WCC \<sigma> = (\<not> sA_empty \<sigma> \<and> \<sigma> AC = FEmpty \<and> \<sigma> nAnC \<noteq> FEmpty)"
| "holds_shape ECT \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sA_univ \<sigma> \<and> \<sigma> AC = FEmpty \<and> \<sigma> nAnC = FEmpty)"
| "holds_shape UNS \<sigma> = (sA_univ \<sigma> \<and> sC_empty \<sigma>)"
| "holds_shape FUN \<sigma> = (sFin_sub_A \<sigma> \<and> sFin_sub_nC \<sigma>)"
| "holds_shape WUC \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sA_univ \<sigma> \<and> sC_empty \<sigma>)"
| "holds_shape WCT \<sigma> =
     (\<not> sA_empty \<sigma> \<and> \<sigma> AC = FEmpty \<and> \<sigma> nAnC \<noteq> FEmpty \<and> \<not> sC_empty \<sigma>)"
| "holds_shape CMX \<sigma> = (\<not> sA_empty \<sigma> \<and> \<not> sC_univ \<sigma> \<and> \<sigma> nAnC = FEmpty)"
| "holds_shape SCC \<sigma> = (sA_empty \<sigma> \<and> \<not> sC_univ \<sigma>)"
| "holds_shape UCA \<sigma> = (sA_empty \<sigma> \<and> sC_empty \<sigma>)"
| "holds_shape TSU \<sigma> = True"
| "holds_shape TCP \<sigma> = True"
| "holds_shape TCC \<sigma> = True"
| "holds_shape VSU \<sigma> = True"
| "holds_shape VSG \<sigma> = True"
| "holds_shape VSB \<sigma> = True"


section \<open>Realizable shapes and the decision procedure\<close>

text \<open>
  A shape is realizable exactly when some region has a finite member.  The
  all-empty shape would require an empty universe; a shape whose nonempty
  regions are all \<open>FInf\<close> would require no finite interpretations to exist at
  all.  Both are excluded by the assumptions of the \<open>szs\<close> locale, and nothing
  else is: 65 of the 81 shapes are realized.
\<close>

definition realizable :: "shape \<Rightarrow> bool" where
  "realizable \<sigma> \<longleftrightarrow> list_ex (\<lambda>r. \<sigma> r = FFin) all_regions"

lemma realizable_iff: "realizable \<sigma> \<longleftrightarrow> (\<exists>r. \<sigma> r = FFin)"
  by (auto simp: realizable_def list_ex_iff)

definition isa_chk :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "isa_chk s t \<equiv>
     list_all (\<lambda>(a, b, c, d).
                 let \<sigma> = mk_shape a b c d
                 in realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>)
              quads"

definition nevera_chk :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nevera_chk s t \<equiv>
     list_all (\<lambda>(a, b, c, d).
                 let \<sigma> = mk_shape a b c d
                 in realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> \<not> holds_shape t \<sigma>)
              quads"

definition xora_chk :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "xora_chk s t \<equiv>
     list_all (\<lambda>(a, b, c, d).
                 let \<sigma> = mk_shape a b c d
                 in realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>)
              quads"

definition nota_chk :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "nota_chk s t \<equiv> \<not> isa_chk s t"

definition mighta_chk :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "mighta_chk s t \<equiv> \<not> nevera_chk s t"

lemma isa_chk_iff:
  "isa_chk s t \<longleftrightarrow> (\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>)"
proof
  assume *: "isa_chk s t"
  show "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>" and "holds_shape s \<sigma>"
    have "(\<sigma> AC, \<sigma> AnC, \<sigma> nAC, \<sigma> nAnC) \<in> set quads" by (rule quads_complete)
    with * have "realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
      unfolding isa_chk_def Let_def
      by (metis (mono_tags, lifting) Ball_set_list_all case_prodD shape_expand)
    with \<open>realizable \<sigma>\<close> \<open>holds_shape s \<sigma>\<close> show "holds_shape t \<sigma>" by blast
  qed
next
  assume "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
  then show "isa_chk s t"
    unfolding isa_chk_def Let_def by (simp add: list_all_iff split_beta)
qed

lemma nevera_chk_iff:
  "nevera_chk s t \<longleftrightarrow> (\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> \<not> holds_shape t \<sigma>)"
proof
  assume *: "nevera_chk s t"
  show "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> \<not> holds_shape t \<sigma>"
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>" and "holds_shape s \<sigma>"
    have "(\<sigma> AC, \<sigma> AnC, \<sigma> nAC, \<sigma> nAnC) \<in> set quads" by (rule quads_complete)
    with * have "realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> \<not> holds_shape t \<sigma>"
      unfolding nevera_chk_def Let_def
      by (metis (mono_tags, lifting) Ball_set_list_all case_prodD shape_expand)
    with \<open>realizable \<sigma>\<close> \<open>holds_shape s \<sigma>\<close> show "\<not> holds_shape t \<sigma>" by blast
  qed
next
  assume "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> \<not> holds_shape t \<sigma>"
  then show "nevera_chk s t"
    unfolding nevera_chk_def Let_def by (simp add: list_all_iff split_beta)
qed

lemma xora_chk_iff:
  "xora_chk s t \<longleftrightarrow> (\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>)"
proof
  assume *: "xora_chk s t"
  show "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>"
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>"
    have "(\<sigma> AC, \<sigma> AnC, \<sigma> nAC, \<sigma> nAnC) \<in> set quads" by (rule quads_complete)
    with * have "realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>"
      unfolding xora_chk_def Let_def
      by (metis (mono_tags, lifting) Ball_set_list_all case_prodD shape_expand)
    with \<open>realizable \<sigma>\<close> show "holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>" by blast
  qed
next
  assume "\<forall>\<sigma>. realizable \<sigma> \<longrightarrow> holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>"
  then show "xora_chk s t"
    unfolding xora_chk_def Let_def by (simp add: list_all_iff split_beta)
qed


section \<open>The bridge to the model theory\<close>

definition reg :: "region \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'i set" where
  "reg r A C =
     (case r of AC \<Rightarrow> A \<inter> C | AnC \<Rightarrow> A - C | nAC \<Rightarrow> C - A | nAnC \<Rightarrow> - (A \<union> C))"

lemma reg_simps [simp]:
  "reg AC A C = A \<inter> C"
  "reg AnC A C = A - C"
  "reg nAC A C = C - A"
  "reg nAnC A C = - (A \<union> C)"
  by (simp_all add: reg_def)

lemma reg_cover: "\<exists>r. x \<in> reg r A C"
  by (cases "x \<in> A"; cases "x \<in> C") (auto intro: exI [of _ AC] exI [of _ AnC]
                                              exI [of _ nAC] exI [of _ nAnC])

context szs_base
begin

definition shape_of :: "'i set \<Rightarrow> 'i set \<Rightarrow> shape" where
  "shape_of A C =
     (\<lambda>r. if reg r A C = {} then FEmpty
          else if reg r A C \<inter> Fin = {} then FInf else FFin)"

lemma shape_of_FEmpty [simp]: "shape_of A C r = FEmpty \<longleftrightarrow> reg r A C = {}"
  by (auto simp: shape_of_def)

lemma shape_of_FFin [simp]: "shape_of A C r = FFin \<longleftrightarrow> reg r A C \<inter> Fin \<noteq> {}"
  by (auto simp: shape_of_def)

lemma shape_of_neq_FFin: "shape_of A C r \<noteq> FFin \<longleftrightarrow> reg r A C \<inter> Fin = {}"
  by (simp add: shape_of_def)

subsection \<open>The abbreviations against the sets\<close>

lemma sA_empty_shape [simp]: "sA_empty (shape_of A C) \<longleftrightarrow> A = {}"
  by (auto simp: sA_empty_def)

lemma sC_empty_shape [simp]: "sC_empty (shape_of A C) \<longleftrightarrow> C = {}"
  by (auto simp: sC_empty_def)

lemma sA_univ_shape [simp]: "sA_univ (shape_of A C) \<longleftrightarrow> A = UNIV"
  by (auto simp: sA_univ_def)

lemma sC_univ_shape [simp]: "sC_univ (shape_of A C) \<longleftrightarrow> C = UNIV"
  by (auto simp: sC_univ_def)

lemma sA_fin_shape [simp]: "sA_fin (shape_of A C) \<longleftrightarrow> A \<inter> Fin \<noteq> {}"
  by (auto simp: sA_fin_def)

lemma sFin_sub_A_shape [simp]: "sFin_sub_A (shape_of A C) \<longleftrightarrow> Fin \<subseteq> A"
  by (auto simp: sFin_sub_A_def shape_of_neq_FFin)

lemma sFin_sub_C_shape [simp]: "sFin_sub_C (shape_of A C) \<longleftrightarrow> Fin \<subseteq> C"
  by (auto simp: sFin_sub_C_def shape_of_neq_FFin)

lemma sFin_sub_nC_shape [simp]: "sFin_sub_nC (shape_of A C) \<longleftrightarrow> Fin \<subseteq> - C"
  by (auto simp: sFin_sub_nC_def shape_of_neq_FFin)

subsection \<open>The bridge lemma\<close>

theorem holds_shape_of: "holds s A C \<longleftrightarrow> holds_shape s (shape_of A C)"
  by (cases s) (auto simp: shape_of_neq_FFin)

end


section \<open>Soundness and completeness of the check\<close>

context szs
begin

lemma realizable_shape_of: "realizable (shape_of A C)"
proof -
  obtain x where x: "x \<in> Fin" using Fin_nonempty by blast
  obtain r where "x \<in> reg r A C" using reg_cover by metis
  with x have "reg r A C \<inter> Fin \<noteq> {}" by blast
  then have "shape_of A C r = FFin" by simp
  then show ?thesis by (auto simp: realizable_iff)
qed

text \<open>
  The converse.  Every realizable shape is the shape of some \<langle>Ax, C\<rangle>.  The
  construction chooses one witness per nonempty region — a finite one for an
  \<open>FFin\<close> region and an infinite one for an \<open>FInf\<close> region — sends everything
  else to a designated \<open>FFin\<close> region, and reads A and C off the resulting
  partition.
\<close>

lemma realizable_witness:
  assumes "realizable \<sigma>"
  shows "\<exists>A C. shape_of A C = \<sigma>"
proof -
  obtain r0 where r0: "\<sigma> r0 = FFin" using assms by (auto simp: realizable_iff)

  obtain f :: "nat \<Rightarrow> 'i" where f: "inj f" "range f \<subseteq> Fin"
    using Fin_infinite infinite_countable_subset by blast
  obtain g :: "nat \<Rightarrow> 'i" where g: "inj g" "range g \<subseteq> - Fin"
    using coFin_infinite infinite_countable_subset by blast

  define idx :: "region \<Rightarrow> nat" where
    "idx r = (case r of AC \<Rightarrow> 0 | AnC \<Rightarrow> 1 | nAC \<Rightarrow> 2 | nAnC \<Rightarrow> 3)" for r
  have idx_inj: "inj idx"
    by (rule injI) (case_tac x; case_tac y; simp add: idx_def)

  define w :: "region \<Rightarrow> 'i" where
    "w r = (if \<sigma> r = FFin then f (idx r) else g (idx r))" for r
  have w_Fin: "\<sigma> r = FFin \<Longrightarrow> w r \<in> Fin" for r
    using f by (auto simp: w_def)
  have w_coFin: "\<sigma> r \<noteq> FFin \<Longrightarrow> w r \<notin> Fin" for r
    using g by (auto simp: w_def)
  have w_inj: "inj w"
  proof (rule injI)
    fix r r' assume "w r = w r'"
    moreover have "\<sigma> r = FFin \<longleftrightarrow> \<sigma> r' = FFin"
      using \<open>w r = w r'\<close> w_Fin w_coFin by metis
    ultimately have "idx r = idx r'"
      using f g by (cases "\<sigma> r = FFin") (auto simp: w_def dest: injD)
    then show "r = r'" using idx_inj by (auto dest: injD)
  qed

  define W :: "region set" where "W = {r. r \<noteq> r0 \<and> \<sigma> r \<noteq> FEmpty}"
  have W_fin: "finite W"
    by (metis List.finite_set all_regions_UNIV rev_finite_subset top_greatest)

  define pick :: "'i \<Rightarrow> region" where
    "pick x = (if \<exists>r \<in> W. x = w r then THE r. r \<in> W \<and> x = w r else r0)" for x
  have pick_w: "r \<in> W \<Longrightarrow> pick (w r) = r" for r
  proof -
    assume r: "r \<in> W"
    have "(THE r'. r' \<in> W \<and> w r = w r') = r"
      by (rule the_equality) (use r w_inj in \<open>auto dest: injD\<close>)
    with r show ?thesis by (auto simp: pick_def)
  qed
  have pick_r0: "\<forall>r \<in> W. x \<noteq> w r \<Longrightarrow> pick x = r0" for x
    by (simp add: pick_def)
  have pick_in_W: "pick x \<noteq> r0 \<Longrightarrow> pick x \<in> W \<and> x = w (pick x)" for x
  proof -
    assume "pick x \<noteq> r0"
    then obtain r where r: "r \<in> W" "x = w r"
      using pick_r0 by auto
    with pick_w show ?thesis by auto
  qed

  define S :: "region \<Rightarrow> 'i set" where "S r = {x. pick x = r}" for r
  have S_disj: "r \<noteq> r' \<Longrightarrow> S r \<inter> S r' = {}" for r r' by (auto simp: S_def)
  have S_cover: "(\<Union>r. S r) = UNIV" by (auto simp: S_def)

  have S_empty: "\<sigma> r = FEmpty \<Longrightarrow> S r = {}" for r
    using r0 pick_in_W W_def S_def by force
  have S_witness: "r \<in> W \<Longrightarrow> S r = {w r}" for r
    using pick_w pick_in_W W_def S_def by force
  have S_r0_big: "- S r0 \<subseteq> w ` W"
    using pick_in_W by (auto simp: S_def)

  define A where "A = S AC \<union> S AnC"
  define C where "C = S AC \<union> S nAC"

  have reg_S: "reg r A C = S r" for r
  proof (cases r)
    case AC show ?thesis using AC S_disj by (auto simp: A_def C_def)
  next
    case AnC show ?thesis using AnC S_disj by (auto simp: A_def C_def)
  next
    case nAC show ?thesis using nAC S_disj by (auto simp: A_def C_def)
  next
    case nAnC
    have "x \<in> - (A \<union> C) \<longleftrightarrow> x \<in> S nAnC" for x
      using S_cover S_disj S_def
      by (smt (verit, del_insts) A_def C_def Compl_iff Un_iff
          mem_Collect_eq region.distinct(11,5,9)
          region.exhaust)
    with nAnC show ?thesis by auto
  qed

  have "shape_of A C r = \<sigma> r" for r
  proof (cases "\<sigma> r")
    case FEmpty
    then show ?thesis using S_empty reg_S by simp
  next
    case FInf
    then have "r \<in> W" using r0 by (auto simp: W_def)
    then have "reg r A C = {w r}" using reg_S S_witness by simp
    moreover have "w r \<notin> Fin" using FInf w_coFin by simp
    ultimately show ?thesis using FInf by (simp add: shape_of_def)
  next
    case FFin
    show ?thesis
    proof (cases "r = r0")
      case False
      then have "r \<in> W" using FFin by (auto simp: W_def)
      then have "reg r A C = {w r}" using reg_S S_witness by simp
      moreover have "w r \<in> Fin" using FFin w_Fin by simp
      ultimately show ?thesis using FFin by simp
    next
      case True
      have "finite (w ` W)" using W_fin by simp
      then have "\<not> Fin \<subseteq> w ` W" using Fin_infinite by (metis finite_subset)
      then obtain x where "x \<in> Fin" "x \<notin> w ` W" by blast
      then have "x \<in> S r0" using S_r0_big by blast
      then have "reg r0 A C \<inter> Fin \<noteq> {}" using reg_S \<open>x \<in> Fin\<close> by auto
      then show ?thesis using True FFin by simp
    qed
  qed
  then have "shape_of A C = \<sigma>" by (rule ext)
  then show ?thesis by blast
qed

subsection \<open>The main equivalences\<close>

theorem isa_iff_chk: "isa s t \<longleftrightarrow> isa_chk s t"
proof
  assume "isa s t"
  show "isa_chk s t"
    unfolding isa_chk_iff
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>" and "holds_shape s \<sigma>"
    then obtain A C where AC: "shape_of A C = \<sigma>" using realizable_witness by blast
    with \<open>holds_shape s \<sigma>\<close> have "holds s A C" by (simp add: holds_shape_of)
    with \<open>isa s t\<close> have "holds t A C" unfolding isa_def by blast
    with AC show "holds_shape t \<sigma>" by (simp add: holds_shape_of)
  qed
next
  assume "isa_chk s t"
  show "isa s t"
    unfolding isa_def
  proof (intro allI impI)
    fix A C assume "holds s A C"
    then have "holds_shape s (shape_of A C)" by (simp add: holds_shape_of)
    with \<open>isa_chk s t\<close> realizable_shape_of
    have "holds_shape t (shape_of A C)" unfolding isa_chk_iff by blast
    then show "holds t A C" by (simp add: holds_shape_of)
  qed
qed

theorem nevera_iff_chk: "nevera s t \<longleftrightarrow> nevera_chk s t"
proof
  assume "nevera s t"
  show "nevera_chk s t"
    unfolding nevera_chk_iff
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>" and "holds_shape s \<sigma>"
    then obtain A C where AC: "shape_of A C = \<sigma>" using realizable_witness by blast
    with \<open>holds_shape s \<sigma>\<close> have "holds s A C" by (simp add: holds_shape_of)
    with \<open>nevera s t\<close> have "\<not> holds t A C" unfolding nevera_def by blast
    with AC show "\<not> holds_shape t \<sigma>" by (simp add: holds_shape_of)
  qed
next
  assume "nevera_chk s t"
  show "nevera s t"
    unfolding nevera_def
  proof (intro allI impI)
    fix A C assume "holds s A C"
    then have "holds_shape s (shape_of A C)" by (simp add: holds_shape_of)
    with \<open>nevera_chk s t\<close> realizable_shape_of
    have "\<not> holds_shape t (shape_of A C)" unfolding nevera_chk_iff by blast
    then show "\<not> holds t A C" by (simp add: holds_shape_of)
  qed
qed

theorem xora_iff_chk: "xora s t \<longleftrightarrow> xora_chk s t"
proof
  assume "xora s t"
  show "xora_chk s t"
    unfolding xora_chk_iff
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>"
    then obtain A C where AC: "shape_of A C = \<sigma>" using realizable_witness by blast
    from \<open>xora s t\<close> have "holds s A C \<noteq> holds t A C" unfolding xora_def by blast
    with AC show "holds_shape s \<sigma> \<noteq> holds_shape t \<sigma>" by (simp add: holds_shape_of)
  qed
next
  assume "xora_chk s t"
  show "xora s t"
    unfolding xora_def
  proof (intro allI)
    fix A C
    have "holds_shape s (shape_of A C) \<noteq> holds_shape t (shape_of A C)"
      using \<open>xora_chk s t\<close> realizable_shape_of unfolding xora_chk_iff by blast
    then show "holds s A C \<noteq> holds t A C" by (simp add: holds_shape_of)
  qed
qed

theorem nota_iff_chk: "nota s t \<longleftrightarrow> nota_chk s t"
  by (simp add: nota_iff nota_chk_def isa_iff_chk)

theorem mighta_iff_chk: "mighta s t \<longleftrightarrow> mighta_chk s t"
  by (simp add: mighta_iff mighta_chk_def nevera_iff_chk)

end


section \<open>Sanity checks\<close>

text \<open>
  The size of the search space, and the mirror symmetry of the decision
  procedure.  Both are statements about \<open>isa_chk\<close>, which is independent of the
  interpretation type; \<open>isa_iff_chk\<close> transfers them to \<open>isa\<close> in any instance of
  \<open>szs\<close>, so the individual edges are recorded once, as the \<open>isa_\<close> lemmas of
  SZS_Semantics, rather than twice.
\<close>

lemma card_realizable_shapes:
  "length (filter (\<lambda>(a, b, c, d). realizable (mk_shape a b c d)) quads) = 65"
  by eval

text \<open>
  The mirror symmetry of the check.  This is a computation over 53 \<times> 53 pairs,
  and it is what exposes an asymmetric reading of a mirror pair in one step.
\<close>

lemma isa_chk_mirror:
  "list_all (\<lambda>s. list_all (\<lambda>t. isa_chk (mirror s) (mirror t) = isa_chk s t) all_success)
            all_success"
  by eval


section \<open>Invariance under signature extension\<close>

text \<open>
  \<open>shape_of_vimage\<close> is the statement the fixed signature reading needs: the
  shape of \<open>\<langle>Ax, C\<rangle>\<close> is the same read over the signature of Ax and over any
  extension of it.  With \<open>holds_shape_of\<close> it gives \<open>holds_vimage\<close>, the
  invariance of all fifty-three conditions, and with \<open>mex_sig_iff\<close> it makes the
  MEX entry of \<open>holds\<close> the page's two-signature condition rather than a
  stipulation.
\<close>

context szs_ext
begin

lemma reg_vimage: "reg q (r -` A) (r -` C) = r -` reg q A C"
  by (cases q) auto

lemma shape_of_vimage:
  "szs_base.shape_of Fin_j (r -` A) (r -` C) = shape_of A C"
proof (rule ext)
  fix q :: region
  have "(reg q (r -` A) (r -` C) = {}) = (reg q A C = {})"
    by (simp add: reg_vimage)
  moreover have "(reg q (r -` A) (r -` C) \<inter> Fin_j = {}) = (reg q A C \<inter> Fin = {})"
    by (simp add: reg_vimage Fin_j_def flip: vimage_Int)
  ultimately show "szs_base.shape_of Fin_j (r -` A) (r -` C) q = shape_of A C q"
    by (simp add: szs_base.shape_of_def shape_of_def)
qed

theorem holds_vimage: "szs_base.holds Fin_j s (r -` A) (r -` C) = holds s A C"
  by (simp add: szs_base.holds_shape_of shape_of_vimage holds_shape_of)

definition isa_ext :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "isa_ext s t \<equiv>
     (\<forall>A C. szs_base.holds Fin_j s (r -` A) C \<longrightarrow> szs_base.holds Fin_j t (r -` A) C)"

theorem isa_ext_iff_chk: "isa_ext s t \<longleftrightarrow> isa_chk s t"
proof
  assume ext: "isa_ext s t"
  show "isa_chk s t"
    unfolding isa_chk_iff
  proof (intro allI impI)
    fix \<sigma> assume "realizable \<sigma>" and "holds_shape s \<sigma>"
    then obtain A C where AC: "shape_of A C = \<sigma>"
      using realizable_witness by blast
    have lift: "szs_base.shape_of Fin_j (r -` A) (r -` C) = \<sigma>"
      by (simp add: shape_of_vimage AC)
    from \<open>holds_shape s \<sigma>\<close> lift
    have "szs_base.holds Fin_j s (r -` A) (r -` C)"
      by (simp add: szs_base.holds_shape_of)
    with ext have "szs_base.holds Fin_j t (r -` A) (r -` C)"
      unfolding isa_ext_def by blast
    with lift show "holds_shape t \<sigma>"
      by (simp add: szs_base.holds_shape_of)
  qed
next
  assume chk: "isa_chk s t"
  show "isa_ext s t"
    unfolding isa_ext_def
  proof (intro allI impI)
    fix A :: "'i set" and C :: "'j set"
    assume "szs_base.holds Fin_j s (r -` A) C"
    then have "holds_shape s (szs_base.shape_of Fin_j (r -` A) C)"
      by (simp add: szs_base.holds_shape_of)
    moreover have "realizable (szs_base.shape_of Fin_j (r -` A) C)"
      by (rule szs.realizable_shape_of [OF szs_Fin_j])
    ultimately have "holds_shape t (szs_base.shape_of Fin_j (r -` A) C)"
      using chk unfolding isa_chk_iff by blast
    then show "szs_base.holds Fin_j t (r -` A) C"
      by (simp add: szs_base.holds_shape_of)
  qed
qed

theorem mex_sig_entails_iff:
  "(\<forall>A C. mex_sig A C \<longrightarrow> szs_base.holds Fin_j t (r -` A) C) \<longleftrightarrow> isa_chk MEX t"
proof -
  have "(\<forall>A C. mex_sig A C \<longrightarrow> szs_base.holds Fin_j t (r -` A) C) = isa_ext MEX t"
    by (simp add: isa_ext_def mex_sig_iff)
  then show ?thesis by (simp add: isa_ext_iff_chk)
qed

theorem entails_mex_sig_iff:
  "(\<forall>A C. szs_base.holds Fin_j s (r -` A) C \<longrightarrow> mex_sig A C) \<longleftrightarrow> isa_chk s MEX"
proof -
  have "(\<forall>A C. szs_base.holds Fin_j s (r -` A) C \<longrightarrow> mex_sig A C) = isa_ext s MEX"
    by (simp add: isa_ext_def mex_sig_iff)
  then show ?thesis by (simp add: isa_ext_iff_chk)
qed

theorem cmx_sig_entails_iff:
  "(\<forall>A C. cmx_sig A C \<longrightarrow> szs_base.holds Fin_j t (r -` A) C) \<longleftrightarrow> isa_chk CMX t"
proof -
  have "(\<forall>A C. cmx_sig A C \<longrightarrow> szs_base.holds Fin_j t (r -` A) C) = isa_ext CMX t"
    by (simp add: isa_ext_def cmx_sig_iff)
  then show ?thesis by (simp add: isa_ext_iff_chk)
qed

theorem entails_cmx_sig_iff:
  "(\<forall>A C. szs_base.holds Fin_j s (r -` A) C \<longrightarrow> cmx_sig A C) \<longleftrightarrow> isa_chk s CMX"
proof -
  have "(\<forall>A C. szs_base.holds Fin_j s (r -` A) C \<longrightarrow> cmx_sig A C) = isa_ext s CMX"
    by (simp add: isa_ext_def cmx_sig_iff)
  then show ?thesis by (simp add: isa_ext_iff_chk)
qed

end

end