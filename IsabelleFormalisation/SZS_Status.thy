(*  Title:      SZS_Status.thy
    Author:     Johannes Schuster

The status values of the SZS success ontology, with their official OneWord
names, their three letter mnemonics, the lower case form used inside a TPTP
status(...) annotation, and the mirror involution that exchanges a value with
its counter value.

This theory is data only: it fixes the vocabulary and the syntactic facts
about it.  The model theoretic content lives in SZS_Semantics, the derived
isa order in SZS_Hierarchy, and the BNF renderer in SZS_BNF.

Naming.  The type is called success rather than status: the no-success and
dataform ontologies are disjoint vocabularies and get their own types, since
nothing is shared between them except the presentation conventions.
*)

theory SZS_Status
  imports Main
begin

section \<open>The success ontology vocabulary\<close>

text \<open>
  Fifty-three values.  The ordering below is the positive part, then the
  contradictory-axioms block, then the counter part, then the type checking
  and verification subontologies.  The counter part is listed in the order
  induced by \<open>mirror\<close> on the positive part, so that the two blocks can be read
  side by side.
\<close>

datatype success =
  \<comment> \<open>frame\<close>
    SUC | SSU
  \<comment> \<open>positive semantic values\<close>
  | UNP | SAP | TAP | ESA | ETA | SAT | FSA | THM | FTH | STH | EQV | TAC | WEC
  | ETH | TAU | FTT | WTC | WTH | MEX | NOC
  \<comment> \<open>contradictory axioms\<close>
  | CAX | SCA | TCA | WCA
  \<comment> \<open>counter semantic values\<close>
  | CUP | CSP | CTP | ECS | ECA | CSA | FCS | CTH | FCT | SCT | CEQ | UNC | WCC
  | ECT | UNS | FUN | WUC | WCT | CMX | SCC | UCA
  \<comment> \<open>type checking and verification\<close>
  | TSU | TCP | TSC | VSU | VSG | VSB

definition all_success :: "success list" where
  "all_success =
    [SUC, SSU,
     UNP, SAP, TAP, ESA, ETA, SAT, FSA, THM, FTH, STH, EQV, TAC, WEC,
     ETH, TAU, FTT, WTC, WTH, MEX, NOC,
     CAX, SCA, TCA, WCA,
     CUP, CSP, CTP, ECS, ECA, CSA, FCS, CTH, FCT, SCT, CEQ, UNC, WCC,
     ECT, UNS, FUN, WUC, WCT, CMX, SCC, UCA,
     TSU, TCP, TSC, VSU, VSG, VSB]"

lemma all_success_UNIV [simp]: "set all_success = UNIV"
proof -
  have "s \<in> set all_success" for s
    by (cases s) (simp_all add: all_success_def)
  then show ?thesis by auto
qed

lemma distinct_all_success: "distinct all_success"
  by eval

lemma length_all_success: "length all_success = 53"
  by (simp add: all_success_def)

lemma finite_success [simp]: "finite (UNIV :: success set)"
  using all_success_UNIV by (metis List.finite_set)

lemma card_success: "card (UNIV :: success set) = 53"
  using all_success_UNIV distinct_all_success length_all_success
  by (metis distinct_card)


section \<open>Spellings\<close>

subsection \<open>OneWord names\<close>

primrec one_word :: "success \<Rightarrow> string" where
  "one_word SUC = ''Success''"
| "one_word SSU = ''SemanticSuccess''"
| "one_word UNP = ''UnsatisfiabilityPreserving''"
| "one_word SAP = ''SatisfiabilityPreserving''"
| "one_word TAP = ''TautologyPreserving''"
| "one_word ESA = ''EquiSatisfiable''"
| "one_word ETA = ''EquiTautologous''"
| "one_word SAT = ''Satisfiable''"
| "one_word FSA = ''FinitelySatisfiable''"
| "one_word THM = ''Theorem''"
| "one_word FTH = ''FiniteTheorem''"
| "one_word STH = ''SatisfiableAxiomsTheorem''"
| "one_word EQV = ''Equivalent''"
| "one_word TAC = ''TautologousConclusion''"
| "one_word WEC = ''WeakerConclusion''"
| "one_word ETH = ''EquivalentTheorem''"
| "one_word TAU = ''Tautology''"
| "one_word FTT = ''FiniteTautology''"
| "one_word WTC = ''WeakerTautologousConclusion''"
| "one_word WTH = ''WeakerTheorem''"
| "one_word MEX = ''ModelExtending''"
| "one_word NOC = ''NoConsequence''"
| "one_word CAX = ''ContradictoryAxioms''"
| "one_word SCA = ''SatisfiableConclusionContradictoryAxioms''"
| "one_word TCA = ''TautologousConclusionContradictoryAxioms''"
| "one_word WCA = ''WeakerConclusionContradictoryAxioms''"
| "one_word CUP = ''CounterUnsatisfiabilityPreserving''"
| "one_word CSP = ''CounterSatisfiabilityPreserving''"
| "one_word CTP = ''CounterTautologyPreserving''"
| "one_word ECS = ''EquiCounterSatisfiable''"
| "one_word ECA = ''EquiCounterTautologous''"
| "one_word CSA = ''CounterSatisfiable''"
| "one_word FCS = ''FinitelyCounterSatisfiable''"
| "one_word CTH = ''CounterTheorem''"
| "one_word FCT = ''FiniteCounterTheorem''"
| "one_word SCT = ''SatisfiableAxiomsCounterTheorem''"
| "one_word CEQ = ''CounterEquivalent''"
| "one_word UNC = ''UnsatisfiableConclusion''"
| "one_word WCC = ''WeakerCounterConclusion''"
| "one_word ECT = ''EquivalentCounterTheorem''"
| "one_word UNS = ''Unsatisfiable''"
| "one_word FUN = ''FinitelyUnsatisfiable''"
| "one_word WUC = ''WeakerUnsatisfiableConclusion''"
| "one_word WCT = ''WeakerCounterTheorem''"
| "one_word CMX = ''CounterModelExtending''"
| "one_word SCC = ''SatisfiableCounterConclusionContradictoryAxioms''"
| "one_word UCA = ''UnsatisfiableConclusionContradictoryAxioms''"
| "one_word TSU = ''TypeCheckSuccess''"
| "one_word TCP = ''TypeCheckPartial''"
| "one_word TSC = ''TypeCheckedComplete''"
| "one_word VSU = ''VerifySuccess''"
| "one_word VSG = ''VerifiedGood''"
| "one_word VSB = ''VerifiedBad''"

subsection \<open>Mnemonics\<close>

text \<open>
  For the success ontology every mnemonic happens to coincide with the
  constructor name, so this function looks redundant.  It is written out
  anyway: the dataform ontology's mnemonics are mixed case (Dat, LDa, NSo) and
  will not coincide with anything, and the two ontologies should be presented
  through the same interface.
\<close>

primrec mnemonic :: "success \<Rightarrow> string" where
  "mnemonic SUC = ''SUC''"
| "mnemonic SSU = ''SSU''"
| "mnemonic UNP = ''UNP''"
| "mnemonic SAP = ''SAP''"
| "mnemonic TAP = ''TAP''"
| "mnemonic ESA = ''ESA''"
| "mnemonic ETA = ''ETA''"
| "mnemonic SAT = ''SAT''"
| "mnemonic FSA = ''FSA''"
| "mnemonic THM = ''THM''"
| "mnemonic FTH = ''FTH''"
| "mnemonic STH = ''STH''"
| "mnemonic EQV = ''EQV''"
| "mnemonic TAC = ''TAC''"
| "mnemonic WEC = ''WEC''"
| "mnemonic ETH = ''ETH''"
| "mnemonic TAU = ''TAU''"
| "mnemonic FTT = ''FTT''"
| "mnemonic WTC = ''WTC''"
| "mnemonic WTH = ''WTH''"
| "mnemonic MEX = ''MEX''"
| "mnemonic NOC = ''NOC''"
| "mnemonic CAX = ''CAX''"
| "mnemonic SCA = ''SCA''"
| "mnemonic TCA = ''TCA''"
| "mnemonic WCA = ''WCA''"
| "mnemonic CUP = ''CUP''"
| "mnemonic CSP = ''CSP''"
| "mnemonic CTP = ''CTP''"
| "mnemonic ECS = ''ECS''"
| "mnemonic ECA = ''ECA''"
| "mnemonic CSA = ''CSA''"
| "mnemonic FCS = ''FCS''"
| "mnemonic CTH = ''CTH''"
| "mnemonic FCT = ''FCT''"
| "mnemonic SCT = ''SCT''"
| "mnemonic CEQ = ''CEQ''"
| "mnemonic UNC = ''UNC''"
| "mnemonic WCC = ''WCC''"
| "mnemonic ECT = ''ECT''"
| "mnemonic UNS = ''UNS''"
| "mnemonic FUN = ''FUN''"
| "mnemonic WUC = ''WUC''"
| "mnemonic WCT = ''WCT''"
| "mnemonic CMX = ''CMX''"
| "mnemonic SCC = ''SCC''"
| "mnemonic UCA = ''UCA''"
| "mnemonic TSU = ''TSU''"
| "mnemonic TCP = ''TCP''"
| "mnemonic TSC = ''TSC''"
| "mnemonic VSU = ''VSU''"
| "mnemonic VSG = ''VSG''"
| "mnemonic VSB = ''VSB''"

subsection \<open>The status(...) form\<close>

text \<open>
  Inside a TPTP inference record a status value is written as the lower case
  mnemonic.  Lower casing is injective over the success ontology, whose
  mnemonics are all upper case; it is \emph{not} injective over the union of
  the three ontologies, where SAT is Satisfiable and Sat is Saturation, and ASS
  is Assumed and Ass is Assurance.  That is why this function is defined here
  and not once for all ontologies.
\<close>

definition lower :: "char \<Rightarrow> char" where
  "lower c =
    (let n = (of_char c :: nat)
     in if 65 \<le> n \<and> n \<le> 90 then char_of (n + 32) else c)"

definition status_value :: "success \<Rightarrow> string" where
  "status_value s = map lower (mnemonic s)"

subsection \<open>Injectivity\<close>

text \<open>
  The three checks below are the mechanical form of a defect class that has
  occurred in practice: until 2026 the dataform ontology gave IIn as the
  mnemonic of both InfiniteInterpretation and IncompleteInterpretation.
\<close>

lemma distinct_one_words: "distinct (map one_word all_success)"
  by eval

lemma distinct_mnemonics: "distinct (map mnemonic all_success)"
  by eval

lemma distinct_status_values: "distinct (map status_value all_success)"
  by eval

lemma inj_one_word: "inj one_word"
proof (rule injI)
  fix s t :: success
  assume "one_word s = one_word t"
  moreover have "inj_on one_word (set all_success)"
    using distinct_one_words by (simp add: distinct_map)
  ultimately show "s = t"
    by (metis UNIV_I all_success_UNIV inj_onD)
qed

lemma inj_mnemonic: "inj mnemonic"
proof (rule injI)
  fix s t :: success
  assume "mnemonic s = mnemonic t"
  moreover have "inj_on mnemonic (set all_success)"
    using distinct_mnemonics by (simp add: distinct_map)
  ultimately show "s = t"
    by (metis UNIV_I all_success_UNIV inj_onD)
qed

lemma inj_status_value: "inj status_value"
proof (rule injI)
  fix s t :: success
  assume "status_value s = status_value t"
  moreover have "inj_on status_value (set all_success)"
    using distinct_status_values by (simp add: distinct_map)
  ultimately show "s = t"
    by (metis UNIV_I all_success_UNIV inj_onD)
qed


section \<open>The mirror involution\<close>

text \<open>
  \<open>mirror s\<close> is the value that says about \<open>\<langle>Ax, \<not>C\<rangle>\<close> what \<open>s\<close> says about
  \<open>\<langle>Ax, C\<rangle>\<close>.  Twenty-one pairs are exchanged and eleven values are fixed.
  Three of the fixed points are fixed for a reason worth recording: CAX
  constrains only Ax, NOC asserts that Ax has models both inside and outside C,
  and WCA asserts that some but not all interpretations model C.  Each of those
  conditions is unchanged under complementing C, and the last is why the
  contradictory-axioms block has five values and not six.  The remaining eight
  fixed points are the frame and the two non model theoretic subontologies.

  SZS_Semantics discharges \<open>holds (mirror s) A C = holds s A (- C)\<close>, from which
  the counter half of the ontology is a theorem rather than a second set of
  definitions.
\<close>

primrec mirror :: "success \<Rightarrow> success" where
  "mirror SUC = SUC"
| "mirror SSU = SSU"
| "mirror UNP = CUP"
| "mirror SAP = CSP"
| "mirror TAP = CTP"
| "mirror ESA = ECS"
| "mirror ETA = ECA"
| "mirror SAT = CSA"
| "mirror FSA = FCS"
| "mirror THM = CTH"
| "mirror FTH = FCT"
| "mirror STH = SCT"
| "mirror EQV = CEQ"
| "mirror TAC = UNC"
| "mirror WEC = WCC"
| "mirror ETH = ECT"
| "mirror TAU = UNS"
| "mirror FTT = FUN"
| "mirror WTC = WUC"
| "mirror WTH = WCT"
| "mirror MEX = CMX"
| "mirror NOC = NOC"
| "mirror CAX = CAX"
| "mirror SCA = SCC"
| "mirror TCA = UCA"
| "mirror WCA = WCA"
| "mirror CUP = UNP"
| "mirror CSP = SAP"
| "mirror CTP = TAP"
| "mirror ECS = ESA"
| "mirror ECA = ETA"
| "mirror CSA = SAT"
| "mirror FCS = FSA"
| "mirror CTH = THM"
| "mirror FCT = FTH"
| "mirror SCT = STH"
| "mirror CEQ = EQV"
| "mirror UNC = TAC"
| "mirror WCC = WEC"
| "mirror ECT = ETH"
| "mirror UNS = TAU"
| "mirror FUN = FTT"
| "mirror WUC = WTC"
| "mirror WCT = WTH"
| "mirror CMX = MEX"
| "mirror SCC = SCA"
| "mirror UCA = TCA"
| "mirror TSU = TSU"
| "mirror TCP = TCP"
| "mirror TSC = TSC"
| "mirror VSU = VSU"
| "mirror VSG = VSG"
| "mirror VSB = VSB"

lemma mirror_involution [simp]: "mirror (mirror s) = s"
  by (cases s) simp_all

lemma bij_mirror: "bij mirror"
  by (rule o_bij [where g = mirror]) (simp_all add: fun_eq_iff comp_def)

lemma surj_mirror: "surj mirror"
  using bij_mirror by (rule bij_is_surj)

lemma inj_mirror: "inj mirror"
  using bij_mirror by (rule bij_is_inj)

definition mirror_fixed_points :: "success set" where
  "mirror_fixed_points = {SUC, SSU, NOC, CAX, WCA, TSU, TCP, TSC, VSU, VSG, VSB}"

lemma mirror_fixed_iff: "mirror s = s \<longleftrightarrow> s \<in> mirror_fixed_points"
  by (cases s) (simp_all add: mirror_fixed_points_def)

lemma card_mirror_fixed_points: "card mirror_fixed_points = 11"
  by (simp add: mirror_fixed_points_def)


section \<open>Model theoretic values\<close>

text \<open>
  Success, SemanticSuccess and the six type checking and verification values
  carry no condition on the models of Ax and C.  Their edges are stipulations
  about software behaviour, not consequences, and they must be excluded from
  the derived order in SZS_Hierarchy: under \<open>holds\<close> they are all identically
  true, so leaving them in collapses the eight of them into one equivalence
  class.  Forty-five values remain, and those are the ones whose isa edges are
  proved rather than asserted.
\<close>

definition model_theoretic :: "success \<Rightarrow> bool" where
  "model_theoretic s \<longleftrightarrow> s \<notin> {SUC, SSU, TSU, TCP, TSC, VSU, VSG, VSB}"

definition model_theoretic_values :: "success list" where
  "model_theoretic_values = filter model_theoretic all_success"

lemma length_model_theoretic_values: "length model_theoretic_values = 45"
  by eval

lemma model_theoretic_mirror [simp]: "model_theoretic (mirror s) = model_theoretic s"
  by (cases s) (simp_all add: model_theoretic_def)

end