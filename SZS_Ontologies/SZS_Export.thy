(*  Title:      SZS_Export.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_Export
  imports SZS_TPTP
begin

section \<open>Problem export\<close>

text \<open>
  The 76 edges of \<open>covers\<close> as TF0 and TH0 problems, exported under
  \<^verbatim>\<open>TF0/SZS_<s>_isa_<t>.p\<close> and \<^verbatim>\<open>TH0/\<close>.
  \<^verbatim>\<open>isabelle export -d . -x 'SZS_Ontologies.SZS_Export:T*/*' -p 1 -O Problems SZS_Ontologies\<close>
  writes the files.
\<close>

code_reflect SZS_TPTP_Code
  functions tf0_problems th0_problems

ML \<open>
  fun export (name, s) =
    Export.export \<^theory> (Path.binding0 (Path.explode name)) (XML.blob [s]);

  val _ = List.app export SZS_TPTP_Code.tf0_problems;
  val _ = List.app export SZS_TPTP_Code.th0_problems;
\<close>

text_raw \<open>\appendix\<close>

section \<open>The generated BNF\<close>

text \<open>@{szs_bnf}\<close>

end
