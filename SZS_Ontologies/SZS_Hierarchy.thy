(*  Title:      SZS_Hierarchy.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_Hierarchy
  imports SZS_Shapes
begin

section \<open>Hierarchy\<close>

text \<open>
  The entailment order over the forty-five model theoretic values is computed
  from SZS\_Shapes and reduced to its transitive reduction.  Fifteen
  stipulated edges for the frame and the two non model theoretic subontologies
  are added.  SZS\_BNF generates the grammar from the result.
\<close>

subsection \<open>The derived order\<close>

text \<open>
  \<open>entails\<close> is strict entailment restricted to the model theoretic values.
  Pairs \<open>(s, t)\<close> are oriented child before parent: \<open>s\<close> entails \<open>t\<close>.
\<close>

definition entails :: "(success \<times> success) list" where
  "entails =
     filter (\<lambda>(s, t). s \<noteq> t \<and> isa_chk s t)
            (List.product model_theoretic_values model_theoretic_values)"

definition above :: "success \<Rightarrow> success list" where
  "above s = filter (\<lambda>t. (s, t) \<in> set entails) model_theoretic_values"

definition below :: "success \<Rightarrow> success list" where
  "below t = filter (\<lambda>s. (s, t) \<in> set entails) model_theoretic_values"

subsubsection \<open>Well-formedness\<close>

text \<open>
  \<open>entails\<close> is a strict partial order.  Antisymmetry says that distinct values
  have distinct meanings; without it the transitive reduction is not unique.
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
  "list_all (\<lambda>(s, t). list_all (\<lambda>u. (t, u) \<in> set entails \<longrightarrow> (s, u) \<in> set entails) model_theoretic_values)
            entails"
  by eval

text \<open>
  Mirror closure, checked directly.
\<close>

lemma entails_mirror:
  "list_all (\<lambda>(s, t). (mirror s, mirror t) \<in> set entails) entails"
  by eval


subsection \<open>Transitive reduction\<close>

text \<open>
  \<open>covers s t\<close> holds when \<open>s\<close> entails \<open>t\<close> with nothing strictly between.  For
  a finite strict partial order the cover relation is the unique transitive
  reduction.
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
  The reduction generates the order back, checked by evaluation over the
  finite carrier.
\<close>

lemma covers_generates:
  "list_all (\<lambda>(s, t).
      (s, t) \<in> set covers \<or>
      list_ex (\<lambda>u. (s, u) \<in> set covers \<and> (u, t) \<in> set entails) model_theoretic_values)
    entails"
  by eval


subsection \<open>The full hierarchy\<close>

subsubsection \<open>Maximal model theoretic values\<close>

text \<open>
  The values with no proper consequence among the forty-five.  They hang
  directly below SemanticSuccess.
\<close>

definition maximal_values :: "success list" where
  "maximal_values = filter (\<lambda>t. above t = []) model_theoretic_values"

lemma maximal_values_eval: "maximal_values = [UNP, SAP, TAP, FTH, CUP, CSP, CTP, FCT]"
  by eval

lemma maximal_values_mirror:
  "list_all (\<lambda>s. mirror s \<in> set maximal_values) maximal_values"
  by eval

subsubsection \<open>Children of every value\<close>

definition cover_children :: "success \<Rightarrow> success list" where
  "cover_children t = filter (\<lambda>s. (s, t) \<in> set covers) model_theoretic_values"

text \<open>
  The stipulated edges.  Success splits into the three subontologies,
  SemanticSuccess covers the derived order, and the type checking and
  verification subontologies are chains and pairs.
\<close>

fun bnf_children :: "success \<Rightarrow> success list" where
  "bnf_children SUC = [SSU, TSU, VSU]"
| "bnf_children SSU = maximal_values"
| "bnf_children TSU = [TCP]"
| "bnf_children TCP = [TCC]"
| "bnf_children TCC = []"
| "bnf_children VSU = [VSG, VSB]"
| "bnf_children VSG = []"
| "bnf_children VSB = []"
| "bnf_children t   = cover_children t"

definition bnf_edges :: "(success \<times> success) list" where
  "bnf_edges = [(s, t). t \<leftarrow> all_success, s \<leftarrow> bnf_children t]"

lemma bnf_edges_cover_all:
  "list_all (\<lambda>s. s = SUC \<or> list_ex (\<lambda>t. (s, t) \<in> set bnf_edges) all_success) all_success"
  by eval

lemma bnf_acyclic:
  "list_all (\<lambda>(s, t). s \<noteq> t \<and> (t, s) \<notin> set bnf_edges) bnf_edges"
  by eval

end
