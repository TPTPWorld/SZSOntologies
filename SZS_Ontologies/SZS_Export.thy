(*  Title:      SZS_Export.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_Export
  imports SZS_TPTP SZS_Relations
begin

section \<open>Export\<close>

text \<open>
  The 76 edges of \<open>covers\<close> as TF0 and TH0 problems, exported under
  \<^verbatim>\<open>TF0/SZS_<s>_isa_<t>.p\<close> and \<^verbatim>\<open>TH0/\<close>, and the five relations
  of SZS\_Relations with the classified pairs, exported under
  \<^verbatim>\<open>Relations/<relation>.txt\<close> and \<^verbatim>\<open>Relations/pairs.txt\<close>.
  \<^verbatim>\<open>isabelle export -d . -x 'SZS_Ontologies.SZS_Export:T*/*' -p 1 -O Problems SZS_Ontologies\<close>
  and
  \<^verbatim>\<open>isabelle export -d . -x 'SZS_Ontologies.SZS_Export:Relations/*' -p 1 -O . SZS_Ontologies\<close>
  write the files.
\<close>

code_reflect SZS_Export_Code
  functions tf0_problems th0_problems relation_files

ML \<open>
  fun export (name, s) =
    Export.export \<^theory> (Path.binding0 (Path.explode name)) (XML.blob [s]);

  val _ = List.app export SZS_Export_Code.tf0_problems;
  val _ = List.app export SZS_Export_Code.th0_problems;
  val _ = List.app export SZS_Export_Code.relation_files;
\<close>

text_raw \<open>\appendix\<close>

section \<open>The generated BNF\<close>

text \<open>@{szs_bnf}\<close>

end
