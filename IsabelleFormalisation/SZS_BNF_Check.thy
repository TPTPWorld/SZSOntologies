(*  Title:      SZS_BNF_Check.thy
    Author:     Johannes Schuster
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause

The check of BNF/SZSOntology.bnf against the formalisation.

The BNF is the source of truth for the SZS ontologies.  This theory reads it
when it is processed, so that the build fails when the file and the
formalisation disagree.  The success part is compared with the grammar that
SZS_BNF derives from the definitions, up to the order of rules and of
alternatives; a new success value in the BNF therefore needs its definition
formalised before the build passes again.  The no-success and dataform parts
carry no definitions, and for them the checks are structural: one root,
acyclic, every rule reachable, every referenced nonterminal defined, and one
terminal per rule, the rule's own.

Every lemma below is proved by evaluation over the data read from the file.
A failing lemma names the property that the current BNF violates.
*)

theory SZS_BNF_Check
  imports SZS_BNF
begin

external_file "../BNF/SZSOntology.bnf"

section \<open>Reading the file\<close>

text \<open>
  A rule starts with \<open><\<close> in column one and continues on indented lines;
  comment, banner and blank lines are skipped.  Alternatives are split at
  \<open>|\<close> and trimmed.
\<close>

ML \<open>
structure SZS_BNF_File =
struct

val path =
  Path.append (Resources.master_directory \<^theory>)
    (Path.explode "../BNF/SZSOntology.bnf");

fun starts_with c s = size s > 0 andalso String.sub (s, 0) = c;

fun group [] acc = rev acc
  | group (l :: ls) acc =
      if starts_with #"<" l then group ls ([l] :: acc)
      else if starts_with #" " l andalso not (null acc)
      then group ls ((hd acc @ [l]) :: tl acc)
      else group ls acc;

fun parse_rule ls =
  let val s = space_implode " " (map Symbol.trim_blanks ls) in
    case first_field "::=" s of
      SOME (lhs, rhs) =>
        (Symbol.trim_blanks lhs, map Symbol.trim_blanks (space_explode "|" rhs))
    | NONE => error ("Malformed rule in " ^ Path.print path ^ ": " ^ s)
  end;

val rules : (string * string list) list =
  map parse_rule (group (split_lines (File.read path)) []);

end
\<close>

text \<open>
  The rules become a HOL constant, so that the checks are lemmas.
\<close>

local_setup \<open>
  let
    val T = HOLogic.mk_prodT (HOLogic.literalT, HOLogic.listT HOLogic.literalT);
    fun rule (lhs, alts) =
      HOLogic.mk_prod
        (HOLogic.mk_literal lhs,
         HOLogic.mk_list HOLogic.literalT (map HOLogic.mk_literal alts));
    val t = HOLogic.mk_list T (map rule SZS_BNF_File.rules);
    val b = \<^binding>\<open>bnf_file_rules\<close>;
  in
    Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, @{attributes [code]}), t)) #> snd
  end
\<close>

definition file_rules :: "production list" where
  "file_rules = map (\<lambda>r. (String.explode (fst r), map String.explode (snd r))) bnf_file_rules"


section \<open>Sub-grammars\<close>

definition is_nonterminal :: "string \<Rightarrow> bool" where
  "is_nonterminal a \<longleftrightarrow> a \<noteq> [] \<and> hd a = CHR ''<'' \<and> last a = CHR ''>''"

definition rule_alts :: "production list \<Rightarrow> string \<Rightarrow> string list" where
  "rule_alts rs n = concat (map snd (filter (\<lambda>r. fst r = n) rs))"

definition rule_children :: "production list \<Rightarrow> string \<Rightarrow> string list" where
  "rule_children rs n = filter is_nonterminal (rule_alts rs n)"

definition reachable :: "production list \<Rightarrow> string \<Rightarrow> string list" where
  "reachable rs n = close (length rs) (rule_children rs) [n]"

definition subgrammar :: "production list \<Rightarrow> string \<Rightarrow> production list" where
  "subgrammar rs n = filter (\<lambda>r. fst r \<in> set (reachable rs n)) rs"

definition rule_edges :: "production list \<Rightarrow> (string \<times> string) list" where
  "rule_edges rs =
     concat (map (\<lambda>r. map (\<lambda>c. (c, fst r)) (filter is_nonterminal (snd r))) rs)"

definition file_success :: "production list" where
  "file_success = subgrammar file_rules ''<Success>''"

definition file_nosuccess :: "production list" where
  "file_nosuccess = subgrammar file_rules ''<NoSuccess>''"

definition file_dataform :: "production list" where
  "file_dataform = subgrammar file_rules ''<Data>''"


section \<open>Well-formedness\<close>

definition same_set :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "same_set xs ys \<longleftrightarrow> list_all (\<lambda>x. x \<in> set ys) xs \<and> list_all (\<lambda>y. y \<in> set xs) ys"

definition ident :: "string \<Rightarrow> string" where
  "ident a = takeWhile (\<lambda>c. c \<noteq> CHR ''('') a"

definition own_terminal :: "production \<Rightarrow> bool" where
  "own_terminal r \<longleftrightarrow>
     (case filter (\<lambda>a. \<not> is_nonterminal a) (snd r) of
        [a] \<Rightarrow> ''<'' @ ident a @ ''>'' = fst r
      | _ \<Rightarrow> False)"

definition closed :: "production list \<Rightarrow> bool" where
  "closed rs \<longleftrightarrow>
     list_all (\<lambda>a. a \<in> set (map fst rs))
              (concat (map (\<lambda>r. filter is_nonterminal (snd r)) rs))"

definition well_formed :: "production list \<Rightarrow> string \<Rightarrow> bool" where
  "well_formed rs root \<longleftrightarrow>
     distinct (map fst rs) \<and>
     list_all own_terminal rs \<and>
     closed rs \<and>
     roots (rule_edges rs) = [root] \<and>
     acyclic_edges (rule_edges rs) \<and>
     rooted (rule_edges rs) root"


section \<open>The checks\<close>

subsection \<open>The document\<close>

lemma file_rule_names_distinct: "distinct (map fst file_rules)"
  by eval

lemma file_szs_rule:
  "rule_alts file_rules ''<SZS>'' = [''<Success>'', ''<NoSuccess>'', ''<Data>'']"
  by eval

lemma file_rules_partitioned:
  "same_set (map fst file_rules)
     (''<SZS>'' # ''<inference_status_value>'' #
      map fst (file_success @ file_nosuccess @ file_dataform))"
  by eval

lemma file_ontologies_disjoint:
  "distinct (map fst (file_success @ file_nosuccess @ file_dataform))"
  by eval

subsection \<open>The success ontology, against the definitions\<close>

definition rule_eq :: "production \<Rightarrow> production \<Rightarrow> bool" where
  "rule_eq r s \<longleftrightarrow> fst r = fst s \<and> same_set (snd r) (snd s)"

definition same_rules :: "production list \<Rightarrow> production list \<Rightarrow> bool" where
  "same_rules rs ss \<longleftrightarrow>
     list_all (\<lambda>r. list_ex (rule_eq r) ss) rs \<and> list_all (\<lambda>s. list_ex (rule_eq s) rs) ss"

lemma file_success_well_formed: "well_formed file_success ''<Success>''"
  by eval

lemma file_success_is_derived: "same_rules file_success success_rules"
  by eval

lemma file_inference_status_values:
  "distinct (rule_alts file_rules ''<inference_status_value>'') \<and>
   same_set (rule_alts file_rules ''<inference_status_value>'')
            (map status_value inference_status_values)"
  by eval

subsection \<open>The no-success ontology\<close>

lemma file_nosuccess_well_formed: "well_formed file_nosuccess ''<NoSuccess>''"
  by eval

lemma file_assumed_arguments:
  "rule_alts file_rules ''<Assumed>'' = [''Assumed(<Unknown>,<Success>)''] \<and>
   ''<Unknown>'' \<in> set (map fst file_nosuccess) \<and>
   ''<Success>'' \<in> set (map fst file_success)"
  by eval

subsection \<open>The dataform ontology\<close>

lemma file_dataform_well_formed: "well_formed file_dataform ''<Data>''"
  by eval

lemma file_dataform_no_implied_edges: "implied (rule_edges file_dataform) = []"
  by eval


section \<open>Diagnostics\<close>

text \<open>
  When the success part disagrees with the definitions, the lemma
  \<open>file_success_is_derived\<close> fails without saying where.  The block below
  reports the differing rules as warnings first, so that the build log names
  them.
\<close>

definition success_rules_lit :: "(String.literal \<times> String.literal list) list" where
  "success_rules_lit =
     map (\<lambda>r. (String.implode (fst r), map String.implode (snd r))) success_rules"

code_reflect SZS_Check_Code
  functions success_rules_lit

ML \<open>
local
  val derived = SZS_Check_Code.success_rules_lit;
  val in_file = SZS_BNF_File.rules;
  fun same_set xs ys = subset (op =) (xs, ys) andalso subset (op =) (ys, xs);
  fun show (lhs, alts) = lhs ^ " ::= " ^ space_implode " | " alts;
  fun report what (lhs, alts) =
    (case AList.lookup (op =) in_file lhs of
      NONE => warning (what ^ " missing from the BNF: " ^ show (lhs, alts))
    | SOME alts' =>
        if same_set alts alts' then ()
        else warning (what ^ " differs from the BNF:\n  derived: " ^ show (lhs, alts) ^
                      "\n  BNF:     " ^ show (lhs, alts')));
in
  val _ = List.app (report "Derived success rule") derived;
end
\<close>

end
