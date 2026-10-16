(*  Title:      SZS_BNF.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_BNF
  imports SZS_Hierarchy
begin

section \<open>BNF\<close>

text \<open>
  The BNF of the three SZS ontologies.  The success ontology comes from
  SZS\_Hierarchy as \<open>bnf_edges\<close>; the no-success and dataform ontologies are
  transcribed from \url{https://szs.tptp.org}.  Each ontology is checked to
  have one root, no cycle, every value reachable, no implied edge and distinct
  spellings.  The grammar has one rule per value with children.  It is
  rendered as text and exported from the session; the BNF in the repository
  is checked against it by SZS\_BNF\_Check.
\<close>

subsection \<open>The no-success ontology\<close>

subsubsection \<open>Vocabulary\<close>

datatype nosuccess =
    NOS
  | UNK | STP | INP | NTT | NTY
  | ERR | FOR | GUP
  | OSE | INE | SYE | SEE | TYE | USM | USE
  | USR | RSO | TMO | CTO | WTO | MMO
  | INC | IAP | ICT
  | ASS | OPN | NVE | FVE

definition all_nosuccess :: "nosuccess list" where
  "all_nosuccess =
    [NOS,
     UNK, STP, INP, NTT, NTY,
     ERR, FOR, GUP,
     OSE, INE, SYE, SEE, TYE, USM, USE,
     USR, RSO, TMO, CTO, WTO, MMO,
     INC, IAP, ICT,
     ASS, OPN, NVE, FVE]"

lemma all_nosuccess_UNIV [simp]: "set all_nosuccess = UNIV"
proof -
  have "s \<in> set all_nosuccess" for s
    by (cases s) (simp_all add: all_nosuccess_def)
  then show ?thesis by auto
qed

lemma distinct_all_nosuccess: "distinct all_nosuccess"
  by eval

lemma length_all_nosuccess: "length all_nosuccess = 29"
  by (simp add: all_nosuccess_def)

primrec ns_one_word :: "nosuccess \<Rightarrow> string" where
  "ns_one_word NOS = ''NoSuccess''"
| "ns_one_word UNK = ''Unknown''"
| "ns_one_word STP = ''Stopped''"
| "ns_one_word INP = ''InProgress''"
| "ns_one_word NTT = ''NotTried''"
| "ns_one_word NTY = ''NotTriedYet''"
| "ns_one_word ERR = ''Error''"
| "ns_one_word FOR = ''Forced''"
| "ns_one_word GUP = ''GaveUp''"
| "ns_one_word OSE = ''OSError''"
| "ns_one_word INE = ''InputError''"
| "ns_one_word SYE = ''SyntaxError''"
| "ns_one_word SEE = ''SemanticError''"
| "ns_one_word TYE = ''TypeError''"
| "ns_one_word USM = ''Unsemantic''"
| "ns_one_word USE = ''UsageError''"
| "ns_one_word USR = ''User''"
| "ns_one_word RSO = ''ResourceOut''"
| "ns_one_word TMO = ''Timeout''"
| "ns_one_word CTO = ''CPUTimeout''"
| "ns_one_word WTO = ''WCTimeout''"
| "ns_one_word MMO = ''MemoryOut''"
| "ns_one_word INC = ''Incomplete''"
| "ns_one_word IAP = ''Inappropriate''"
| "ns_one_word ICT = ''Incorrect''"
| "ns_one_word ASS = ''Assumed''"
| "ns_one_word OPN = ''Open''"
| "ns_one_word NVE = ''NotVerified''"
| "ns_one_word FVE = ''FailedVerified''"

primrec %invisible ns_mnemonic :: "nosuccess \<Rightarrow> string" where
  "ns_mnemonic NOS = ''NOS''"
| "ns_mnemonic UNK = ''UNK''"
| "ns_mnemonic STP = ''STP''"
| "ns_mnemonic INP = ''INP''"
| "ns_mnemonic NTT = ''NTT''"
| "ns_mnemonic NTY = ''NTY''"
| "ns_mnemonic ERR = ''ERR''"
| "ns_mnemonic FOR = ''FOR''"
| "ns_mnemonic GUP = ''GUP''"
| "ns_mnemonic OSE = ''OSE''"
| "ns_mnemonic INE = ''INE''"
| "ns_mnemonic SYE = ''SYE''"
| "ns_mnemonic SEE = ''SEE''"
| "ns_mnemonic TYE = ''TYE''"
| "ns_mnemonic USM = ''USM''"
| "ns_mnemonic USE = ''USE''"
| "ns_mnemonic USR = ''USR''"
| "ns_mnemonic RSO = ''RSO''"
| "ns_mnemonic TMO = ''TMO''"
| "ns_mnemonic CTO = ''CTO''"
| "ns_mnemonic WTO = ''WTO''"
| "ns_mnemonic MMO = ''MMO''"
| "ns_mnemonic INC = ''INC''"
| "ns_mnemonic IAP = ''IAP''"
| "ns_mnemonic ICT = ''ICT''"
| "ns_mnemonic ASS = ''ASS''"
| "ns_mnemonic OPN = ''OPN''"
| "ns_mnemonic NVE = ''NVE''"
| "ns_mnemonic FVE = ''FVE''"

subsubsection \<open>The stipulated order\<close>

text \<open>
  Child before parent.
\<close>

definition nosuccess_isa :: "(nosuccess \<times> nosuccess) list" where
  "nosuccess_isa =
    [(OPN, NOS), (NVE, NOS), (ASS, NOS), (UNK, NOS), (ICT, NOS),
     (FVE, NVE),
     (STP, UNK), (INP, UNK), (NTT, UNK),
     (NTY, NTT), (IAP, NTT),
     (FOR, STP), (GUP, STP),
     (INE, ERR), (OSE, ERR),
     (SYE, INE), (SEE, INE), (USE, INE),
     (TYE, SEE), (USM, SEE),
     (USR, FOR), (RSO, FOR),
     (TMO, RSO), (MMO, RSO),
     (CTO, TMO), (WTO, TMO),
     (RSO, GUP), (INC, GUP), (ERR, GUP), (IAP, GUP)]"

lemma length_nosuccess_isa: "length nosuccess_isa = 30"
  by (simp add: nosuccess_isa_def)


subsection \<open>The dataform ontology\<close>

subsubsection \<open>Vocabulary\<close>

text \<open>
  The constructors are the mnemonics.  Interpretation is \<open>Itp\<close>, since \<open>Int\<close> is
  taken.
\<close>

datatype dataform =
    Dat
  | LDa | NLd
  | NSo | Sln
  | Ass | IPr | InI
  | Prf | Itp | Lof
  | Ref | Der | CRf
  | Mod
  | DIn | DMo | FIn | FMo | IIn | IMo
  | HIn | HMo | FHi | FHm | Sat
  | Com | FTx | Ver
  | Non

definition all_dataform :: "dataform list" where
  "all_dataform =
    [Dat,
     LDa, NLd,
     NSo, Sln,
     Ass, IPr, InI,
     Prf, Itp, Lof,
     Ref, Der, CRf,
     Mod,
     DIn, DMo, FIn, FMo, IIn, IMo,
     HIn, HMo, FHi, FHm, Sat,
     Com, FTx, Ver,
     Non]"

lemma all_dataform_UNIV [simp]: "set all_dataform = UNIV"
proof -
  have "d \<in> set all_dataform" for d
    by (cases d) (simp_all add: all_dataform_def)
  then show ?thesis by auto
qed

lemma distinct_all_dataform: "distinct all_dataform"
  by eval

lemma length_all_dataform: "length all_dataform = 30"
  by (simp add: all_dataform_def)

primrec df_one_word :: "dataform \<Rightarrow> string" where
  "df_one_word Dat = ''Data''"
| "df_one_word LDa = ''LogicalData''"
| "df_one_word NLd = ''NonLogicalData''"
| "df_one_word NSo = ''NotASolution''"
| "df_one_word Sln = ''Solution''"
| "df_one_word Ass = ''Assurance''"
| "df_one_word IPr = ''IncompleteProof''"
| "df_one_word InI = ''IncompleteInterpretation''"
| "df_one_word Prf = ''Proof''"
| "df_one_word Itp = ''Interpretation''"
| "df_one_word Lof = ''ListOfFormulae''"
| "df_one_word Ref = ''Refutation''"
| "df_one_word Der = ''Derivation''"
| "df_one_word CRf = ''CNFRefutation''"
| "df_one_word Mod = ''Model''"
| "df_one_word DIn = ''DomainInterpretation''"
| "df_one_word DMo = ''DomainModel''"
| "df_one_word FIn = ''FiniteInterpretation''"
| "df_one_word FMo = ''FiniteModel''"
| "df_one_word IIn = ''InfiniteInterpretation''"
| "df_one_word IMo = ''InfiniteModel''"
| "df_one_word HIn = ''HerbrandInterpretation''"
| "df_one_word HMo = ''HerbrandModel''"
| "df_one_word FHi = ''FormulaHerbrandInterpretation''"
| "df_one_word FHm = ''FormulaHerbrandModel''"
| "df_one_word Sat = ''Saturation''"
| "df_one_word Com = ''Comment''"
| "df_one_word FTx = ''FreeText''"
| "df_one_word Ver = ''Verification''"
| "df_one_word Non = ''None''"

primrec %invisible df_mnemonic :: "dataform \<Rightarrow> string" where
  "df_mnemonic Dat = ''Dat''"
| "df_mnemonic LDa = ''LDa''"
| "df_mnemonic NLd = ''NLd''"
| "df_mnemonic NSo = ''NSo''"
| "df_mnemonic Sln = ''Sln''"
| "df_mnemonic Ass = ''Ass''"
| "df_mnemonic IPr = ''IPr''"
| "df_mnemonic InI = ''InI''"
| "df_mnemonic Prf = ''Prf''"
| "df_mnemonic Itp = ''Int''"
| "df_mnemonic Lof = ''Lof''"
| "df_mnemonic Ref = ''Ref''"
| "df_mnemonic Der = ''Der''"
| "df_mnemonic CRf = ''CRf''"
| "df_mnemonic Mod = ''Mod''"
| "df_mnemonic DIn = ''DIn''"
| "df_mnemonic DMo = ''DMo''"
| "df_mnemonic FIn = ''FIn''"
| "df_mnemonic FMo = ''FMo''"
| "df_mnemonic IIn = ''IIn''"
| "df_mnemonic IMo = ''IMo''"
| "df_mnemonic HIn = ''HIn''"
| "df_mnemonic HMo = ''HMo''"
| "df_mnemonic FHi = ''FHi''"
| "df_mnemonic FHm = ''FHm''"
| "df_mnemonic Sat = ''Sat''"
| "df_mnemonic Com = ''Com''"
| "df_mnemonic FTx = ''FTx''"
| "df_mnemonic Ver = ''Ver''"
| "df_mnemonic Non = ''Non''"

subsubsection \<open>The stipulated order\<close>

definition dataform_isa :: "(dataform \<times> dataform) list" where
  "dataform_isa =
    [(Non, Dat), (LDa, Dat), (NLd, Dat),
     (NSo, LDa), (Sln, LDa),
     (Ass, NSo), (IPr, NSo), (InI, NSo),
     (Prf, Sln), (Itp, Sln), (Lof, Sln),
     (Ref, Prf), (Der, Prf), (CRf, Ref),
     (Mod, Itp),
     (DIn, Itp), (DMo, Mod), (DMo, DIn),
     (FIn, DIn), (FMo, DMo), (FMo, FIn),
     (IIn, DIn), (IMo, DMo), (IMo, IIn),
     (HIn, Itp), (HIn, Lof), (HMo, Mod), (HMo, HIn),
     (FHi, HIn), (FHm, HMo), (FHm, FHi),
     (Sat, FHm),
     (Com, NLd), (FTx, NLd), (Ver, FTx)]"

lemma length_dataform_isa: "length dataform_isa = 35"
  by (simp add: dataform_isa_def)

subsection \<open>Structural checks\<close>

subsubsection \<open>Graph operations\<close>

definition nodes :: "('a::equal \<times> 'a) list \<Rightarrow> 'a list" where
  "nodes E = remdups (map fst E @ map snd E)"

definition parents :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "parents E x = map snd (filter (\<lambda>e. fst e = x) E)"

definition children :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "children E x = map fst (filter (\<lambda>e. snd e = x) E)"

fun close :: "nat \<Rightarrow> ('a::equal \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "close 0 f xs = xs"
| "close (Suc k) f xs =
     (let ys = remdups (xs @ concat (map f xs))
      in if length ys = length xs then xs else close k f ys)"

definition ancestors :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "ancestors E x = close (length (nodes E)) (parents E) (parents E x)"

definition descendants :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "descendants E x = close (length (nodes E)) (children E) (children E x)"

definition roots :: "('a::equal \<times> 'a) list \<Rightarrow> 'a list" where
  "roots E = filter (\<lambda>x. parents E x = []) (nodes E)"

definition acyclic_edges :: "('a::equal \<times> 'a) list \<Rightarrow> bool" where
  "acyclic_edges E = list_all (\<lambda>x. x \<notin> set (ancestors E x)) (nodes E)"

definition rooted :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "rooted E r = list_all (\<lambda>x. x = r \<or> r \<in> set (ancestors E x)) (nodes E)"

definition implied :: "('a::equal \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "implied E =
     filter (\<lambda>(c, p). list_ex (\<lambda>q. q \<noteq> p \<and> p \<in> set (ancestors E q)) (parents E c)) E"

text \<open>
  The number of paths from the root to a value is the number of derivations of
  its word.  \<open>derivations E r x = 0\<close> means that the grammar does not generate
  \<open>x\<close>, \<open>1 <\<close> that it generates \<open>x\<close> in more than one way.
\<close>

fun path_count :: "nat \<Rightarrow> ('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "path_count 0 E r x = (if x = r then 1 else 0)"
| "path_count (Suc k) E r x =
     (if x = r then 1 else sum_list (map (path_count k E r) (parents E x)))"

definition derivations :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "derivations E r x = path_count (length (nodes E)) E r x"

definition generates :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "generates E r xs = list_all (\<lambda>x. 0 < derivations E r x) xs"

definition ambiguous :: "('a::equal \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ambiguous E r xs = filter (\<lambda>x. 1 < derivations E r x) xs"

subsubsection \<open>The success ontology\<close>

text \<open>
  \<open>bnf_acyclic\<close> in SZS\_Hierarchy excludes two-cycles; \<open>acyclic_edges\<close>
  excludes cycles of any length.
\<close>

lemma nodes_bnf_edges: "length (nodes bnf_edges) = 53"
  by eval

lemma nodes_bnf_edges_complete:
  "list_all (\<lambda>s. s \<in> set (nodes bnf_edges)) all_success"
  by eval

lemma roots_bnf_edges: "roots bnf_edges = [SUC]"
  by eval

lemma acyclic_bnf_edges: "acyclic_edges bnf_edges"
  by eval

lemma rooted_bnf_edges: "rooted bnf_edges SUC"
  by eval

lemma implied_bnf_edges: "implied bnf_edges = []"
  by eval

subsubsection \<open>The no-success ontology\<close>

lemma nodes_nosuccess_isa: "length (nodes nosuccess_isa) = 29"
  by eval

lemma nodes_nosuccess_complete:
  "list_all (\<lambda>s. s \<in> set (nodes nosuccess_isa)) all_nosuccess"
  by eval

lemma roots_nosuccess_isa: "roots nosuccess_isa = [NOS]"
  by eval

lemma acyclic_nosuccess_isa: "acyclic_edges nosuccess_isa"
  by eval

lemma rooted_nosuccess_isa: "rooted nosuccess_isa NOS"
  by eval

subsubsection \<open>The dataform ontology\<close>

lemma nodes_dataform_isa: "length (nodes dataform_isa) = 30"
  by eval

lemma nodes_dataform_complete:
  "list_all (\<lambda>d. d \<in> set (nodes dataform_isa)) all_dataform"
  by eval

lemma roots_dataform_isa: "roots dataform_isa = [Dat]"
  by eval

lemma acyclic_dataform_isa: "acyclic_edges dataform_isa"
  by eval

lemma rooted_dataform_isa: "rooted dataform_isa Dat"
  by eval

lemma implied_dataform_isa: "implied dataform_isa = []"
  by eval

subsubsection \<open>Spellings across the three ontologies\<close>

definition all_one_words :: "string list" where
  "all_one_words =
     map one_word all_success @ map ns_one_word all_nosuccess @
     map df_one_word all_dataform"

definition all_mnemonics :: "string list" where
  "all_mnemonics =
     map mnemonic all_success @ map ns_mnemonic all_nosuccess @
     map df_mnemonic all_dataform"

lemma length_all_one_words: "length all_one_words = 112"
  by eval

lemma distinct_all_one_words: "distinct all_one_words"
  by eval

lemma distinct_all_mnemonics: "distinct all_mnemonics"
  by eval

text \<open>
  Lower casing is not injective on the union: Satisfiable and Saturation both
  give \<open>sat\<close>, Assumed and Assurance both give \<open>ass\<close>.  Only the success
  ontology is written in lower case.
\<close>

definition lowered_collisions :: "string list" where
  "lowered_collisions =
     remdups (filter (\<lambda>w. 1 < length (filter (\<lambda>v. v = w) (map (map lower) all_mnemonics)))
                     (map (map lower) all_mnemonics))"

lemma lowered_collisions_eval: "lowered_collisions = [''ass'', ''sat'']"
  by eval

lemma distinct_status_values_success: "distinct (map status_value all_success)"
  by (rule distinct_status_values)


subsection \<open>Layout\<close>

definition sp :: char where "sp = CHR 0x20"

definition nl :: string where "nl = [CHR 0x0A]"

definition dq :: string where "dq = [CHR 0x22]"

definition unlines :: "string list \<Rightarrow> string" where
  "unlines ls = concat (map (\<lambda>l. l @ nl) ls)"

definition pad :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "pad n s = s @ replicate (n - length s) sp"

definition lhs_col :: nat where "lhs_col = 24"

definition line_width :: nat where "line_width = 79"

fun pack :: "nat \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> string list" where
  "pack w ind cur [] = [cur]"
| "pack w ind cur (a # as) =
     (if length cur + 3 + length a \<le> w - 2
      then pack w ind (cur @ '' | '' @ a) as
      else (cur @ '' |'') # pack w ind (ind @ a) as)"

definition bnf_rule :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "bnf_rule lhs alts =
     (case alts of
        [] \<Rightarrow> []
      | a # as \<Rightarrow>
          pack line_width (replicate (lhs_col + 5) sp)
               (pad lhs_col lhs @ '' ::= '' @ a) as)"

definition comment :: "string \<Rightarrow> string list" where
  "comment s = [''%----'' @ s]"

definition banner :: "string list" where
  "banner = [replicate 78 (CHR 0x2D)]"


subsection \<open>The grammar\<close>

text \<open>
  \<open>semantic\<close> is the success ontology without the type checking and
  verification values, which cannot occur in an inference record.
\<close>

definition semantic :: "success \<Rightarrow> bool" where
  "semantic s \<longleftrightarrow> s \<notin> {TSU, TCP, TCC, VSU, VSG, VSB}"

definition inference_status_values :: "success list" where
  "inference_status_values = filter semantic all_success"

lemma length_inference_status_values: "length inference_status_values = 47"
  by eval

subsubsection \<open>Rules from the hierarchy\<close>

text \<open>
  The left hand side of a rule is the OneWord in angle brackets, the first
  alternative the OneWord as a terminal, the remaining alternatives the
  children.  A leaf gets \<open><X> ::= X\<close>.  \<open>override\<close> supplies the alternatives of
  Assumed, which takes arguments.
\<close>

type_synonym production = "string \<times> string list"

definition node_ref :: "('a::equal \<Rightarrow> string) \<Rightarrow> 'a \<Rightarrow> string" where
  "node_ref word x = ''<'' @ word x @ ''>''"

definition rules_of ::
  "('a::equal \<Rightarrow> string) \<Rightarrow> ('a \<Rightarrow> string list option) \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a list
   \<Rightarrow> production list" where
  "rules_of word override E xs =
     map (\<lambda>x. (node_ref word x,
               case override x of
                 Some alts \<Rightarrow> alts
               | None \<Rightarrow> word x # map (node_ref word) (children E x)))
         xs"

definition bnf_lines_of :: "production list \<Rightarrow> string list" where
  "bnf_lines_of rs = concat (map (\<lambda>r. bnf_rule (fst r) (snd r)) rs)"

definition no_override :: "'a \<Rightarrow> string list option" where
  "no_override x = None"

definition assumed_override :: "nosuccess \<Rightarrow> string list option" where
  "assumed_override s =
     (if s = ASS then Some [''Assumed(<Unknown>,<Success>)''] else None)"

definition success_rules :: "production list" where
  "success_rules = rules_of one_word no_override bnf_edges all_success"

definition nosuccess_rules :: "production list" where
  "nosuccess_rules = rules_of ns_one_word assumed_override nosuccess_isa all_nosuccess"

definition dataform_rules :: "production list" where
  "dataform_rules = rules_of df_one_word no_override dataform_isa all_dataform"

subsubsection \<open>The argument of Assumed\<close>

definition unknown_values :: "nosuccess list" where
  "unknown_values =
     filter (\<lambda>s. s = UNK \<or> s \<in> set (descendants nosuccess_isa UNK)) all_nosuccess"

lemma length_unknown_values: "length unknown_values = 23"
  by eval

lemma ASS_not_unknown: "ASS \<notin> set unknown_values"
  by eval

subsubsection \<open>The document\<close>

definition section_comment :: "string \<Rightarrow> string list" where
  "section_comment s = [] # comment s"

definition szs_rule :: production where
  "szs_rule = (''<SZS>'', [''<Success>'', ''<NoSuccess>'', ''<Data>''])"

definition inference_status_rule :: production where
  "inference_status_rule =
     (''<inference_status_value>'', map status_value inference_status_values)"

definition all_rules :: "production list" where
  "all_rules =
     szs_rule # success_rules @ nosuccess_rules @ dataform_rules @
     [inference_status_rule]"

definition szs_bnf_lines :: "string list" where
  "szs_bnf_lines =
     banner @
     comment ''The SZS ontologies, generated from SZS_BNF.thy'' @
     section_comment ''A status value, as used in a % SZS status line'' @
     bnf_lines_of [szs_rule] @
     section_comment ''The success ontology'' @
     bnf_lines_of success_rules @
     section_comment ''The no-success ontology'' @
     bnf_lines_of nosuccess_rules @
     section_comment ''The dataform ontology, as used in a % SZS output line'' @
     bnf_lines_of dataform_rules @
     section_comment ''A success ontology value inside a TPTP inference record'' @
     bnf_lines_of [inference_status_rule] @
     banner"

subsubsection \<open>The rule set is well formed\<close>

definition nonterminal_alts :: "production list \<Rightarrow> string list" where
  "nonterminal_alts rs =
     remdups (filter (\<lambda>a. a \<noteq> [] \<and> hd a = CHR 0x3C) (concat (map snd rs)))"

definition terminal_discipline ::
  "('a::equal \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> production list \<Rightarrow> bool" where
  "terminal_discipline word xs rs =
     list_all (\<lambda>x. list_all (\<lambda>r. word x \<in> set (snd r) \<longrightarrow> fst r = node_ref word x) rs)
              xs"

lemma distinct_rule_names: "distinct (map fst all_rules)"
  by eval

lemma count_all_rules: "length all_rules = 114"
  by eval

lemma count_success_rules: "length success_rules = 53"
  by eval

lemma count_nosuccess_rules: "length nosuccess_rules = 29"
  by eval

lemma count_dataform_rules: "length dataform_rules = 30"
  by eval

lemma terminal_discipline_success: "terminal_discipline one_word all_success all_rules"
  by eval

lemma terminal_discipline_nosuccess: "terminal_discipline ns_one_word all_nosuccess all_rules"
  by eval

lemma terminal_discipline_dataform: "terminal_discipline df_one_word all_dataform all_rules"
  by eval

lemma alts_have_rules:
  "list_all (\<lambda>a. a \<in> set (map fst all_rules)) (nonterminal_alts all_rules)"
  by eval

lemma assumed_arguments_have_rules:
  "''<Unknown>'' \<in> set (map fst all_rules) \<and> ''<Success>'' \<in> set (map fst all_rules)"
  by eval

subsubsection \<open>What the grammar generates\<close>

text \<open>
  Every value is generated.  The nonterminals are the OneWords, which are
  distinct across the ontologies by \<open>distinct_all_one_words\<close>.
\<close>

lemma generates_success: "generates bnf_edges SUC all_success"
  by eval

lemma generates_nosuccess: "generates nosuccess_isa NOS all_nosuccess"
  by eval

lemma generates_dataform: "generates dataform_isa Dat all_dataform"
  by eval

text \<open>
  A value with two parents is generated by two rules, so the grammar is
  ambiguous: Tautology is below Equivalent, TautologousConclusion and
  FiniteTautology.  The counts are recorded; pruning would discard isa edges.
\<close>

definition ambiguous_success :: "success list" where
  "ambiguous_success = ambiguous bnf_edges SUC all_success"

definition ambiguous_nosuccess :: "nosuccess list" where
  "ambiguous_nosuccess = ambiguous nosuccess_isa NOS all_nosuccess"

definition ambiguous_dataform :: "dataform list" where
  "ambiguous_dataform = ambiguous dataform_isa Dat all_dataform"

lemma length_ambiguous_success: "length ambiguous_success = 35"
  by eval

lemma length_ambiguous_nosuccess: "length ambiguous_nosuccess = 6"
  by eval

lemma length_ambiguous_dataform: "length ambiguous_dataform = 8"
  by eval

lemma derivations_TAU: "derivations bnf_edges SUC TAU = 20"
  by eval

lemma derivations_UNS: "derivations bnf_edges SUC UNS = 20"
  by eval

text \<open>
  Fifteen success values are leaves; the other thirty-eight get a rule.
\<close>


subsection \<open>Export\<close>

text \<open>
  The document is exported from the generated SML, where a \<open>String.literal\<close>
  is a native string.
\<close>

definition szs_ontology_bnf :: String.literal where
  "szs_ontology_bnf = String.implode (unlines szs_bnf_lines)"

code_reflect SZS_Code
  functions szs_ontology_bnf

ML \<open>writeln SZS_Code.szs_ontology_bnf\<close>

text \<open>
  \<open>@{szs_bnf}\<close> typesets the grammar; the appendix of the document uses it.
\<close>

ML \<open>
  val _ =
    Theory.setup
      (Document_Output.antiquotation_raw \<^binding>\<open>szs_bnf\<close> (Scan.succeed ())
        (fn _ => fn () =>
          Latex.string
            ("{\\scriptsize\\begin{verbatim}\n" ^ SZS_Code.szs_ontology_bnf ^ "\\end{verbatim}}")))
\<close>

text \<open>
  The document is a session export; nothing is written to the file system.
  \<^verbatim>\<open>isabelle export -d . -x '*:SZSOntology.bnf' SZS_Ontologies\<close> writes it to
  \<^verbatim>\<open>export/\<close>.
\<close>

ML \<open>
  fun export name s =
    Export.export \<^theory> (Path.binding0 (Path.basic name)) (XML.blob [s]);

  val _ = export "SZSOntology.bnf" SZS_Code.szs_ontology_bnf;
\<close>

text \<open>
  \<open>writeln\<close> shows the document with its line breaks.
\<close>

end
