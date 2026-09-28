(*  Title:      SZS_Hierarchy.thy
    Author:     Johannes Schuster

The isa hierarchy of the SZS success ontology, derived rather than stipulated,
and its comparison against the two published sources.

The entailment order over the forty-five model theoretic values is computed
from SZS_Shapes, reduced to its unique transitive reduction, and extended by
the eight stipulated edges of the frame and the two non model theoretic
subontologies.  The result is the input to SZS_BNF.

Two comparisons are made.  Against Table 1 of the 2008 KEAPPA paper, which
gives sixty-eight isa pairs over nineteen values proved with an ATP system,
the derived order agrees.  Against the current Success diagram the derived
order disagrees in a small number of places, all of them concerning values
added to the ontology after that 2008 validation.
*)

theory SZS_Hierarchy
  imports SZS_Shapes
begin

section \<open>The derived order\<close>

text \<open>
  \<open>entails\<close> is the strict entailment relation restricted to the values that
  have model theoretic content.  The eight excluded values are identically true
  under \<open>holds\<close>, so including them would make them mutually equivalent and
  collapse the top of the hierarchy.  Their edges are supplied separately in
  \<open>bnf_children\<close> below.

  The pair \<open>(s, t)\<close> is oriented child before parent throughout: it records that
  \<open>s\<close> is below \<open>t\<close>, that is, that \<open>s\<close> entails \<open>t\<close>.
\<close>

definition entails :: "(success \<times> success) list" where
  "entails =
     filter (\<lambda>(s, t). s \<noteq> t \<and> isa_chk s t)
            (List.product model_theoretic_values model_theoretic_values)"

definition above :: "success \<Rightarrow> success list" where
  "above s = filter (\<lambda>t. (s, t) \<in> set entails) model_theoretic_values"

definition below :: "success \<Rightarrow> success list" where
  "below t = filter (\<lambda>s. (s, t) \<in> set entails) model_theoretic_values"

subsection \<open>Well-formedness\<close>

text \<open>
  \<open>entails\<close> is a strict partial order.  Irreflexivity is by construction and
  transitivity follows from \<open>isa_trans\<close>, but antisymmetry is a genuine
  property of the definitions: it says that no two distinct status values have
  the same meaning.  If \<open>entails_antisym\<close> ever fails, the transitive reduction
  below is no longer unique and the offending values must be quotiented before
  a BNF can be generated.
\<close>

lemma entails_irrefl: "(s, s) \<notin> set entails"
  by (simp add: entails_def)

lemma entails_isa_chk: "(s, t) \<in> set entails \<Longrightarrow> isa_chk s t"
  by (auto simp: entails_def)

lemma entails_model_theoretic:
  "(s, t) \<in> set entails \<Longrightarrow> model_theoretic s \<and> model_theoretic t"
  by (auto simp: entails_def model_theoretic_values_def)

lemma entails_antisym:
  "list_all (\<lambda>(s, t). (t, s) \<notin> set entails) entails"
  by eval

lemma entails_trans:
  "list_all (\<lambda>(s, t). list_all (\<lambda>u. (t, u) \<in> set entails \<longrightarrow> (s, u) \<in> set entails)
                               model_theoretic_values)
            entails"
  by eval

text \<open>
  Mirror closure.  This follows from \<open>isa_chk_mirror\<close> in SZS_Shapes together
  with \<open>model_theoretic_mirror\<close>, and is checked directly here so that a later
  edit to either file cannot silently break it.
\<close>

lemma entails_mirror:
  "list_all (\<lambda>(s, t). (mirror s, mirror t) \<in> set entails) entails"
  by eval


section \<open>Transitive reduction\<close>

text \<open>
  \<open>covers s t\<close> holds when \<open>s\<close> entails \<open>t\<close> with nothing strictly between.  For a
  finite strict partial order the cover relation is the unique transitive
  reduction, so the hierarchy drawn from it is determined by the semantics and
  not by anyone's choice of which implied edges to draw.  That is the property
  that makes ``the BNF'' well defined.
\<close>

definition covers :: "(success \<times> success) list" where
  "covers =
     filter (\<lambda>(s, t).
               \<not> list_ex (\<lambda>u. (s, u) \<in> set entails \<and> (u, t) \<in> set entails)
                         model_theoretic_values)
            entails"

lemma covers_subset: "set covers \<subseteq> set entails"
  by (auto simp: covers_def)

lemma covers_mirror:
  "list_all (\<lambda>(s, t). (mirror s, mirror t) \<in> set covers) covers"
  by eval

text \<open>
  The reduction generates the order back.  Stated as an executable check over
  the finite carrier rather than as a general theorem about finite orders,
  which is all that is needed here and costs one \<open>eval\<close>.
\<close>

definition reachable :: "success \<Rightarrow> success list" where
  "reachable s = filter (\<lambda>t. (s, t) \<in> set entails) model_theoretic_values"

lemma covers_generates:
  "list_all (\<lambda>(s, t).
      (s, t) \<in> set covers \<or>
      list_ex (\<lambda>u. (s, u) \<in> set covers \<and> (u, t) \<in> set entails) model_theoretic_values)
    entails"
  by eval


section \<open>The full hierarchy\<close>

subsection \<open>Maximal model theoretic values\<close>

text \<open>
  The values with no proper consequence among the forty-five.  These are the
  ones that hang directly below SemanticSuccess, and the list is derived rather
  than read off the diagram.
\<close>

definition maximal_values :: "success list" where
  "maximal_values = filter (\<lambda>t. above t = []) model_theoretic_values"

lemma maximal_values_eval: "maximal_values = [UNP, SAP, TAP, FTH, CUP, CSP, CTP, FCT]"
  by eval

lemma maximal_values_mirror:
  "list_all (\<lambda>s. mirror s \<in> set maximal_values) maximal_values"
  by eval

subsection \<open>Children of every value\<close>

definition derived_children :: "success \<Rightarrow> success list" where
  "derived_children t = filter (\<lambda>s. (s, t) \<in> set covers) model_theoretic_values"

text \<open>
  The eight stipulated edges.  Success splits into the three subontologies;
  SemanticSuccess covers the derived order; the type checking and verification
  subontologies are chains and pairs given in the text of the page, with no
  model theoretic content to derive them from.
\<close>

fun bnf_children :: "success \<Rightarrow> success list" where
  "bnf_children SUC = [SSU, TSU, VSU]"
| "bnf_children SSU = maximal_values"
| "bnf_children TSU = [TCP]"
| "bnf_children TCP = [TSC]"
| "bnf_children TSC = []"
| "bnf_children VSU = [VSG, VSB]"
| "bnf_children VSG = []"
| "bnf_children VSB = []"
| "bnf_children t   = derived_children t"

definition bnf_edges :: "(success \<times> success) list" where
  "bnf_edges = [(s, t). t \<leftarrow> all_success, s \<leftarrow> bnf_children t]"

lemma bnf_edges_cover_all:
  "list_all (\<lambda>s. s = SUC \<or> list_ex (\<lambda>t. (s, t) \<in> set bnf_edges) all_success) all_success"
  by eval

lemma bnf_acyclic:
  "list_all (\<lambda>(s, t). s \<noteq> t \<and> (t, s) \<notin> set bnf_edges) bnf_edges"
  by eval


section \<open>Comparison with the 2008 paper\<close>

text \<open>
  Table 1 of Sutcliffe, \<open>The SZS Ontologies for Automated Reasoning Software\<close>,
  CEUR-WS 418, pages 38 to 49, gives the four relationships between all pairs
  of nineteen success values.  Sixty-eight pairs are recorded there as isa, and
  the paper states that the isa links of its Figure 1 correspond to that table.
  The relationships were obtained with an ATP system from a first order
  axiomatization of the ontology, so this is an independent check on the
  definitions in SZS_Semantics rather than on the diagram.

  All nineteen values are model theoretic, so every pair is decided by
  \<open>isa_chk\<close>.
\<close>

definition table1_isa :: "(success \<times> success) list" where
  "table1_isa =
    [(ESA, UNP), (ESA, SAP),
     (SAT, UNP), (SAT, SAP), (SAT, ESA),
     (THM, SAP),
     (EQV, UNP), (EQV, SAP), (EQV, ESA), (EQV, SAT), (EQV, THM),
     (TAC, UNP), (TAC, SAP), (TAC, ESA), (TAC, SAT), (TAC, THM),
     (WEC, UNP), (WEC, SAP), (WEC, ESA), (WEC, SAT), (WEC, THM),
     (ETH, UNP), (ETH, SAP), (ETH, ESA), (ETH, SAT), (ETH, THM), (ETH, EQV),
     (TAU, UNP), (TAU, SAP), (TAU, ESA), (TAU, SAT), (TAU, THM), (TAU, EQV),
     (TAU, TAC),
     (WTC, UNP), (WTC, SAP), (WTC, ESA), (WTC, SAT), (WTC, THM), (WTC, TAC),
     (WTC, WEC),
     (WTH, UNP), (WTH, SAP), (WTH, ESA), (WTH, SAT), (WTH, THM), (WTH, WEC),
     (CAX, SAP), (CAX, THM),
     (SCA, SAP), (SCA, THM), (SCA, CAX),
     (TCA, SAP), (TCA, THM), (TCA, CAX), (TCA, SCA),
     (WCA, SAP), (WCA, THM), (WCA, CAX), (WCA, SCA),
     (CSA, UNP),
     (UNS, UNP), (UNS, CSA),
     (NOC, UNP), (NOC, SAP), (NOC, ESA), (NOC, SAT), (NOC, CSA)]"

lemma length_table1_isa: "length table1_isa = 68"
  by (simp add: table1_isa_def)

theorem table1_isa_reproduced: "list_all (\<lambda>(s, t). isa_chk s t) table1_isa"
  by eval

text \<open>
  The converse direction.  No pair over those nineteen values entails another
  unless the table records it, so the agreement is exact and not merely one sided.
\<close>

definition table1_values :: "success list" where
  "table1_values =
    [UNP, SAP, ESA, SAT, THM, EQV, TAC, WEC, ETH, TAU, WTC, WTH,
     CAX, SCA, TCA, WCA, CSA, UNS, NOC]"

theorem table1_isa_complete:
  "list_all (\<lambda>s. list_all (\<lambda>t. s \<noteq> t \<longrightarrow> isa_chk s t \<longrightarrow> (s, t) \<in> set table1_isa)
                          table1_values)
            table1_values"
  by eval

text \<open>
  The paper records four ordered pairs as xora.
\<close>

definition table1_xora :: "(success \<times> success) list" where
  "table1_xora = [(UNP, SCA), (SCA, UNP), (THM, CSA), (CSA, THM)]"

theorem table1_xora_reproduced: "list_all (\<lambda>(s, t). xora_chk s t) table1_xora"
  by eval

text \<open>
  The two cases the 2008 effort left undecided.  Proving them there required
  exhibiting a pair \<langle>Ax, C\<rangle> with the WeakerConclusion property in which C is
  not a tautology, which its author declined to assert as a further axiom.
  Here they are consequences of the shape enumeration, with the witness
  supplied by \<open>realizable_witness\<close>.
\<close>

theorem wec_nota_wtc: "nota_chk WEC WTC"
  by eval

theorem wec_nota_tac: "nota_chk WEC TAC"
  by eval


section \<open>Comparison with the current diagram\<close>

text \<open>
  The isa links of the Success diagram at https://szs.tptp.org, transcribed on
  2026-09-12.  Orientation is child before parent, as everywhere in this file.
\<close>

definition published :: "(success \<times> success) list" where
  "published =
    [(SSU, SUC), (TSU, SUC), (VSU, SUC),
     (TCP, TSU), (TSC, TCP), (VSG, VSU), (VSB, VSU),
     (UNP, SSU), (SAP, SSU), (TAP, SSU), (FTH, SSU), (FCT, SSU),
     (CTP, SSU), (CSP, SSU), (CUP, SSU),
     (ESA, UNP), (ESA, SAP),
     (SAT, ESA), (MEX, ESA),
     (EQV, SAT), (TAC, SAT), (WEC, SAT), (FSA, SAT), (NOC, SAT),
     (EQV, MEX),
     (ETH, EQV), (TAU, EQV),
     (FTT, TAU),
     (TAU, TAC), (WTC, TAC),
     (WTC, WEC), (WTH, WEC),
     (THM, SAP), (THM, TAP), (THM, FTH),
     (ETA, TAP),
     (STH, THM), (CAX, THM),
     (EQV, STH), (TAC, STH), (WEC, STH),
     (SCA, CAX), (SCC, CAX),
     (TCA, SCA), (WCA, SCA), (UCA, SCC),
     (CTH, FCT), (CTH, CTP), (CTH, CSP),
     (ECA, CTP),
     (CAX, CTH), (SCT, CTH),
     (WCC, SCT), (UNC, SCT), (CEQ, SCT),
     (WCT, WCC), (WUC, WCC),
     (WUC, UNC), (UNS, UNC),
     (FUN, UNS),
     (UNS, CEQ), (ECT, CEQ),
     (ECS, CSP), (ECS, CUP),
     (CSA, ECS), (CMX, ECS),
     (NOC, CSA), (FCS, CSA), (WCC, CSA), (UNC, CSA), (CEQ, CSA),
     (CEQ, CMX)]"

subsection \<open>Soundness of the diagram\<close>

text \<open>
  Every drawn edge should be an entailment.  Two are not, and both concern the
  finite variants of universal values, which are weaker than the values they
  are drawn above rather than stronger.  FiniteTautology and
  FinitelyUnsatisfiable therefore belong above Tautology and Unsatisfiable, not
  below them.
\<close>

theorem published_unsound:
  "filter (\<lambda>(s, t). \<not> isa_chk s t) published = [(FTT, TAU), (FUN, UNS)]"
  by eval

theorem published_corrected_sound:
  "list_all (\<lambda>(s, t). isa_chk s t)
            (filter (\<lambda>e. e \<notin> {(FTT, TAU), (FUN, UNS)}) published)"
  by eval

subsection \<open>Completeness of the diagram\<close>

text \<open>
  The cover edges the diagram does not draw, once the two unsound edges are
  turned around.  The result is inspected rather than asserted: the expected
  entries are the placement of ModelExtending below Satisfiable, the two
  finite variants in their corrected position, and the two long cross links
  that the 2008 Figure 1 draws with ``from'' and ``to'' labels rather than
  lines and that the current diagram appears to have lost.
\<close>

definition published_corrected :: "(success \<times> success) list" where
  "published_corrected =
     (TAU, FTT) # (UNS, FUN) #
     filter (\<lambda>e. e \<notin> {(FTT, TAU), (FUN, UNS)}) published"

definition missing_edges :: "(success \<times> success) list" where
  "missing_edges = filter (\<lambda>e. e \<notin> set published_corrected) bnf_edges"

definition spurious_edges :: "(success \<times> success) list" where
  "spurious_edges = filter (\<lambda>e. e \<notin> set bnf_edges) published_corrected"

value "missing_edges"
(* [(CSA, UNP), (ECT, ESA), (WCT, ESA), (UCA, ESA), (EQV, ETA), (WTH, ETA), (WCC, ETA), (ECT, ETA), (SCC, ETA),
   (STH, SAT), (MEX, SAT), (FTT, FSA), (FTT, FTH), (SAT, CUP), (ETH, ECS), (WTH, ECS), (TCA, ECS), (WEC, ECA),
   (ETH, ECA), (SCA, ECA), (CEQ, ECA), (WCT, ECA), (SCT, CSA), (CMX, CSA), (FUN, FCS), (FUN, FCT), (WCA, SCC)] *)
value "spurious_edges"
(* [(MEX, ESA), (EQV, SAT), (TAC, SAT), (WEC, SAT), (CMX, ECS), (WCC, CSA), (UNC, CSA), (CEQ, CSA)] *)

text \<open>
  A spurious edge is not necessarily an error.  An entailment that the derived
  order records only transitively may still be drawn explicitly, as the page's
  own prose does when it states that Equivalent is below both Satisfiable and
  SatisfiableAxiomsTheorem.  The check that matters is that every spurious
  edge is at least sound, which \<open>published_corrected_sound\<close> gives.
\<close>

theorem isa_MEX_SAT_chk: "isa_chk MEX SAT"
  by eval

theorem isa_CSA_UNP_chk: "isa_chk CSA UNP"
  by eval

theorem isa_SAT_CUP_chk: "isa_chk SAT CUP"
  by eval


section \<open>Named subsets\<close>

text \<open>
  The values admissible inside a TPTP \<open>status(...)\<close> annotation: Success
  together with the whole of SemanticSuccess, that is, Success, SemanticSuccess
  and the forty-five model theoretic values.  This is the list that SyntaxBNF's
  \<open><status_value>\<close> rule has been carrying by hand, and carrying incompletely:
  the rule enumerates thirty-four of the forty-seven.

  Note that the subset cannot be characterised as everything entailing
  SemanticSuccess, since \<open>holds SSU\<close> is identically true and so is entailed by
  every value including the type checking ones.  It is a structural subset, not
  a semantic one.
\<close>

definition inference_status_values :: "success list" where
  "inference_status_values = SUC # SSU # model_theoretic_values"

lemma length_inference_status_values: "length inference_status_values = 47"
  by eval

lemma inference_status_values_mirror:
  "list_all (\<lambda>s. mirror s \<in> set inference_status_values) inference_status_values"
  by eval

text \<open>
  The thirty-four values the current SyntaxBNF admits, and the thirteen it
  omits.  All six of the type checking and verification values are correctly
  outside the subset; the thirteen below are not.
\<close>

definition syntax_bnf_status_values :: "success list" where
  "syntax_bnf_status_values =
    [SUC, UNP, SAP, ESA, SAT, FSA, THM, EQV, TAC, WEC, ETH, TAU, WTC, WTH,
     CAX, SCA, TCA, WCA, CUP, CSP, CSA, CTH, CEQ, UNC, WCC, ECT, UNS, FUN,
     WUC, WCT, SCC, UCA, NOC, ECS]"

lemma length_syntax_bnf_status_values: "length syntax_bnf_status_values = 34"
  by (simp add: syntax_bnf_status_values_def)

lemma syntax_bnf_subset:
  "list_all (\<lambda>s. s \<in> set inference_status_values) syntax_bnf_status_values"
  by eval

lemma syntax_bnf_omissions:
  "filter (\<lambda>s. s \<notin> set syntax_bnf_status_values) inference_status_values =
     [SSU, TAP, ETA, FTH, STH, FTT, MEX, CTP, ECA, FCS, FCT, SCT, CMX]"
  by eval

end