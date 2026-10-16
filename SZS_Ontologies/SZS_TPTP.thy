(*  Title:      SZS_TPTP.thy
    Author:     Johannes Schuster and Geoff Sutcliffe
    Copyright:  2026 Geoff Sutcliffe and Johannes Schuster
    License:    BSD-3-Clause
*)

theory SZS_TPTP
  imports SZS_BNF
begin

section \<open>TPTP problems\<close>

text \<open>
  The status conditions as first-order formulas over \<open>a\<close>, \<open>c\<close> and \<open>fin\<close>, and
  the derived edges as TPTP problems.  \<open>cond_of_holds\<close> relates the formula of
  a value to \<open>holds\<close>, and \<open>edge_problem_isa\<close> the problem of an edge to \<open>isa\<close>.
  The printers are unverified.
\<close>

subsection \<open>Formulas\<close>

datatype pred = PA | PC | PFin

datatype fo =
    Top
  | Atom pred nat
  | Neg fo
  | Conj fo fo
  | Disj fo fo
  | Imp fo fo
  | Iff fo fo
  | All fo
  | Ex fo

text \<open>
  Binders are de Bruijn indices over one sort.
\<close>

primrec sel :: "pred \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'i set" where
  "sel PA A C Fin = A"
| "sel PC A C Fin = C"
| "sel PFin A C Fin = Fin"

primrec fo_sem :: "'i set \<Rightarrow> 'i set \<Rightarrow> 'i set \<Rightarrow> 'i list \<Rightarrow> fo \<Rightarrow> bool" where
  "fo_sem A C Fin env Top = True"
| "fo_sem A C Fin env (Atom p n) = (env ! n \<in> sel p A C Fin)"
| "fo_sem A C Fin env (Neg \<phi>) = (\<not> fo_sem A C Fin env \<phi>)"
| "fo_sem A C Fin env (Conj \<phi> \<psi>) = (fo_sem A C Fin env \<phi> \<and> fo_sem A C Fin env \<psi>)"
| "fo_sem A C Fin env (Disj \<phi> \<psi>) = (fo_sem A C Fin env \<phi> \<or> fo_sem A C Fin env \<psi>)"
| "fo_sem A C Fin env (Imp \<phi> \<psi>) = (fo_sem A C Fin env \<phi> \<longrightarrow> fo_sem A C Fin env \<psi>)"
| "fo_sem A C Fin env (Iff \<phi> \<psi>) = (fo_sem A C Fin env \<phi> \<longleftrightarrow> fo_sem A C Fin env \<psi>)"
| "fo_sem A C Fin env (All \<phi>) = (\<forall>x. fo_sem A C Fin (x # env) \<phi>)"
| "fo_sem A C Fin env (Ex \<phi>) = (\<exists>x. fo_sem A C Fin (x # env) \<phi>)"

abbreviation a :: fo where "a \<equiv> Atom PA 0"
abbreviation c :: fo where "c \<equiv> Atom PC 0"
abbreviation fin :: fo where "fin \<equiv> Atom PFin 0"


subsection \<open>The status conditions\<close>

text \<open>
  One closed formula per value, transcribed from \<open>holds\<close>: \<open>X = {}\<close> is
  \<open>Neg (Ex x)\<close>, \<open>X \<noteq> {}\<close> is \<open>Ex x\<close>, \<open>X = UNIV\<close> is \<open>All x\<close>, \<open>X \<noteq> UNIV\<close> is
  \<open>Ex (Neg x)\<close>, and \<open>- C\<close> is \<open>Neg c\<close>.  Values without model theoretic content
  get \<open>Top\<close>.
\<close>

primrec cond_of :: "success \<Rightarrow> fo" where
  "cond_of SUC = Top"
| "cond_of SSU = Top"
| "cond_of UNP = Imp (Neg (Ex a)) (Neg (Ex c))"
| "cond_of SAP = Imp (Ex a) (Ex c)"
| "cond_of TAP = Imp (All a) (All c)"
| "cond_of ESA = Iff (Neg (Ex a)) (Neg (Ex c))"
| "cond_of ETA = Iff (All a) (All c)"
| "cond_of SAT = Conj (Ex a) (Ex (Conj a c))"
| "cond_of FSA = Conj (Ex (Conj a fin)) (Ex (Conj (Conj a c) fin))"
| "cond_of THM = All (Imp a c)"
| "cond_of FTH = All (Imp (Conj a fin) c)"
| "cond_of STH = Conj (Ex a) (All (Imp a c))"
| "cond_of EQV = Conj (Ex a) (All (Iff a c))"
| "cond_of TAC = Conj (Ex a) (All c)"
| "cond_of WEC = Conj (Conj (Ex a) (All (Imp a c))) (Ex (Conj c (Neg a)))"
| "cond_of ETH = Conj (Conj (Ex a) (Ex (Neg a))) (All (Iff a c))"
| "cond_of TAU = Conj (All a) (All c)"
| "cond_of FTT = Conj (All (Imp fin a)) (All (Imp fin c))"
| "cond_of WTC = Conj (Conj (Ex a) (Ex (Neg a))) (All c)"
| "cond_of WTH = Conj (Conj (Conj (Ex a) (All (Imp a c))) (Ex (Conj c (Neg a)))) (Ex (Neg c))"
| "cond_of MEX = Conj (Conj (Ex a) (Ex c)) (All (Imp c a))"
| "cond_of NOC = Conj (Ex (Conj a c)) (Ex (Conj a (Neg c)))"
| "cond_of CAX = Neg (Ex a)"
| "cond_of SCA = Conj (Neg (Ex a)) (Ex c)"
| "cond_of TCA = Conj (Neg (Ex a)) (All c)"
| "cond_of WCA = Conj (Conj (Neg (Ex a)) (Ex c)) (Ex (Neg c))"
| "cond_of CUP = Imp (Neg (Ex a)) (Neg (Ex (Neg c)))"
| "cond_of CSP = Imp (Ex a) (Ex (Neg c))"
| "cond_of CTP = Imp (All a) (All (Neg c))"
| "cond_of ECS = Iff (Neg (Ex a)) (Neg (Ex (Neg c)))"
| "cond_of ECA = Iff (All a) (All (Neg c))"
| "cond_of CSA = Conj (Ex a) (Ex (Conj a (Neg c)))"
| "cond_of FCS = Conj (Ex (Conj a fin)) (Ex (Conj (Conj a (Neg c)) fin))"
| "cond_of CTH = All (Imp a (Neg c))"
| "cond_of FCT = All (Imp (Conj a fin) (Neg c))"
| "cond_of SCT = Conj (Ex a) (All (Imp a (Neg c)))"
| "cond_of CEQ = Conj (Ex a) (All (Iff a (Neg c)))"
| "cond_of UNC = Conj (Ex a) (All (Neg c))"
| "cond_of WCC = Conj (Conj (Ex a) (All (Imp a (Neg c)))) (Ex (Conj (Neg c) (Neg a)))"
| "cond_of ECT = Conj (Conj (Ex a) (Ex (Neg a))) (All (Iff a (Neg c)))"
| "cond_of UNS = Conj (All a) (All (Neg c))"
| "cond_of FUN = Conj (All (Imp fin a)) (All (Imp fin (Neg c)))"
| "cond_of WUC = Conj (Conj (Ex a) (Ex (Neg a))) (All (Neg c))"
| "cond_of WCT = Conj (Conj (Conj (Ex a) (All (Imp a (Neg c)))) (Ex (Conj (Neg c) (Neg a)))) (Ex c)"
| "cond_of CMX = Conj (Conj (Ex a) (Ex (Neg c))) (All (Imp (Neg c) a))"
| "cond_of SCC = Conj (Neg (Ex a)) (Ex (Neg c))"
| "cond_of UCA = Conj (Neg (Ex a)) (All (Neg c))"
| "cond_of TSU = Top"
| "cond_of TCP = Top"
| "cond_of TCC = Top"
| "cond_of VSU = Top"
| "cond_of VSG = Top"
| "cond_of VSB = Top"

context szs_base
begin

theorem cond_of_holds: "fo_sem A C Fin [] (cond_of s) = holds s A C"
  by (cases s; simp add: set_eq_iff subset_iff del: all_not_in_conv; blast?)

end


subsubsection \<open>Mirror\<close>

text \<open>
  \<open>fo_mirror\<close> exchanges \<open>c\<close> and \<open>Neg c\<close>.  NOC and WCA are self-mirror with a
  \<open>c\<close> conjunct; their images have the conjuncts swapped.
\<close>

fun fo_mirror :: "fo \<Rightarrow> fo" where
  "fo_mirror (Atom PC n) = Neg (Atom PC n)"
| "fo_mirror (Neg (Atom PC n)) = Atom PC n"
| "fo_mirror (Neg \<phi>) = Neg (fo_mirror \<phi>)"
| "fo_mirror (Conj \<phi> \<psi>) = Conj (fo_mirror \<phi>) (fo_mirror \<psi>)"
| "fo_mirror (Disj \<phi> \<psi>) = Disj (fo_mirror \<phi>) (fo_mirror \<psi>)"
| "fo_mirror (Imp \<phi> \<psi>) = Imp (fo_mirror \<phi>) (fo_mirror \<psi>)"
| "fo_mirror (Iff \<phi> \<psi>) = Iff (fo_mirror \<phi>) (fo_mirror \<psi>)"
| "fo_mirror (All \<phi>) = All (fo_mirror \<phi>)"
| "fo_mirror (Ex \<phi>) = Ex (fo_mirror \<phi>)"
| "fo_mirror \<phi> = \<phi>"

lemma fo_sem_mirror: "fo_sem A C Fin env (fo_mirror \<phi>) = fo_sem A (- C) Fin env \<phi>"
  by (induction \<phi> arbitrary: env rule: fo_mirror.induct) simp_all

lemma cond_of_mirror:
  "s \<noteq> NOC \<Longrightarrow> s \<noteq> WCA \<Longrightarrow> cond_of (mirror s) = fo_mirror (cond_of s)"
  by (cases s) simp_all


subsection \<open>Edges as problems\<close>

definition edge_problem :: "success \<Rightarrow> success \<Rightarrow> fo" where
  "edge_problem s t = Imp (cond_of s) (cond_of t)"

definition fin_nonempty :: fo where
  "fin_nonempty = Ex fin"

context szs_base
begin

theorem edge_problem_isa:
  "(\<forall>A C. fo_sem A C Fin [] (edge_problem s t)) \<longleftrightarrow> isa s t"
  by (simp add: edge_problem_def isa_def cond_of_holds)

lemma fin_nonempty_sem: "fo_sem A C Fin [] fin_nonempty \<longleftrightarrow> Fin \<noteq> {}"
  by (auto simp: fin_nonempty_def)

text \<open>
  The direction of \<open>isa_iff_chk\<close> the problems need, under the one assumption
  they use.
\<close>

lemma realizable_shape_of_nonempty:
  assumes "Fin \<noteq> {}" shows "realizable (shape_of A C)"
proof -
  obtain x where x: "x \<in> Fin" using assms by blast
  obtain r where "x \<in> reg r A C" using reg_cover by metis
  with x have "reg r A C \<inter> Fin \<noteq> {}" by blast
  then have "shape_of A C r = FFin" by simp
  then show ?thesis by (auto simp: realizable_iff)
qed

theorem isa_chk_isa: "Fin \<noteq> {} \<Longrightarrow> isa_chk s t \<Longrightarrow> isa s t"
  unfolding isa_def
proof (intro allI impI)
  fix A C assume "Fin \<noteq> {}" and "isa_chk s t" and "holds s A C"
  then have "holds_shape s (shape_of A C)" by (simp add: holds_shape_of)
  with \<open>isa_chk s t\<close> realizable_shape_of_nonempty [OF \<open>Fin \<noteq> {}\<close>]
  have "holds_shape t (shape_of A C)" unfolding isa_chk_iff by blast
  then show "holds t A C" by (simp add: holds_shape_of)
qed

theorem covers_valid:
  "(s, t) \<in> set covers \<Longrightarrow> Fin \<noteq> {} \<Longrightarrow> fo_sem A C Fin [] (edge_problem s t)"
  using covers_subset entails_isa_chk isa_chk_isa edge_problem_isa by blast

end

subsubsection \<open>Which edges need the assumption\<close>

text \<open>
  \<open>isa_chk_base\<close> checks all shapes with a nonempty universe, so it decides
  \<open>isa\<close> for every \<open>Fin\<close>.  Two edges fail it.
\<close>

definition inhabited :: "shape \<Rightarrow> bool" where
  "inhabited \<sigma> \<longleftrightarrow> list_ex (\<lambda>r. \<sigma> r \<noteq> FEmpty) all_regions"

definition isa_chk_base :: "success \<Rightarrow> success \<Rightarrow> bool" where
  "isa_chk_base s t \<equiv>
     list_all (\<lambda>(a, b, c, d).
                 let \<sigma> = mk_shape a b c d
                 in inhabited \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>)
              quads"

lemma isa_chk_base_iff:
  "isa_chk_base s t \<longleftrightarrow> (\<forall>\<sigma>. inhabited \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>)"
proof
  assume *: "isa_chk_base s t"
  show "\<forall>\<sigma>. inhabited \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
  proof (intro allI impI)
    fix \<sigma> assume "inhabited \<sigma>" and "holds_shape s \<sigma>"
    have "(\<sigma> AC, \<sigma> AnC, \<sigma> nAC, \<sigma> nAnC) \<in> set quads" by (rule quads_complete)
    with * have "inhabited \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
      unfolding isa_chk_base_def Let_def
      by (metis (mono_tags, lifting) Ball_set_list_all case_prodD shape_expand)
    with \<open>inhabited \<sigma>\<close> \<open>holds_shape s \<sigma>\<close> show "holds_shape t \<sigma>" by blast
  qed
next
  assume "\<forall>\<sigma>. inhabited \<sigma> \<longrightarrow> holds_shape s \<sigma> \<longrightarrow> holds_shape t \<sigma>"
  then show "isa_chk_base s t"
    unfolding isa_chk_base_def Let_def by (simp add: list_all_iff split_beta)
qed

context szs_base
begin

lemma inhabited_shape_of: "inhabited (shape_of A C)"
proof -
  obtain r where "(undefined :: 'i) \<in> reg r A C" using reg_cover by metis
  then have "shape_of A C r \<noteq> FEmpty" by auto
  then show ?thesis by (auto simp: inhabited_def list_ex_iff)
qed

theorem isa_chk_base_isa: "isa_chk_base s t \<Longrightarrow> isa s t"
  unfolding isa_def
proof (intro allI impI)
  fix A C assume "isa_chk_base s t" and "holds s A C"
  then have "holds_shape s (shape_of A C)" by (simp add: holds_shape_of)
  with \<open>isa_chk_base s t\<close> inhabited_shape_of
  have "holds_shape t (shape_of A C)" unfolding isa_chk_base_iff by blast
  then show "holds t A C" by (simp add: holds_shape_of)
qed

end

lemma covers_needing_fin:
  "filter (\<lambda>(s, t). \<not> isa_chk_base s t) covers = [(FTT, FSA), (FUN, FCS)]"
  by eval


subsection \<open>Printing\<close>

text \<open>
  Variables are \<open>I1, I2, \<dots>\<close> by binder depth, as in the KRS problems of the
  TPTP library.  Binary formulas are parenthesised.
\<close>

fun nat_string :: "nat \<Rightarrow> string" where
  "nat_string n =
     (if n < 10 then [char_of (48 + n)]
      else nat_string (n div 10) @ [char_of (48 + n mod 10)])"

definition var_name :: "nat \<Rightarrow> string" where
  "var_name d = ''I'' @ nat_string d"

fun print_fo :: "(pred \<Rightarrow> string \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> fo \<Rightarrow> string" where
  "print_fo app srt d Top = ''$true''"
| "print_fo app srt d (Atom p n) = app p (var_name (d - n))"
| "print_fo app srt d (Neg \<phi>) = ''~ '' @ print_fo app srt d \<phi>"
| "print_fo app srt d (Conj \<phi> \<psi>) =
     ''( '' @ print_fo app srt d \<phi> @ '' & '' @ print_fo app srt d \<psi> @ '' )''"
| "print_fo app srt d (Disj \<phi> \<psi>) =
     ''( '' @ print_fo app srt d \<phi> @ '' | '' @ print_fo app srt d \<psi> @ '' )''"
| "print_fo app srt d (Imp \<phi> \<psi>) =
     ''( '' @ print_fo app srt d \<phi> @ '' => '' @ print_fo app srt d \<psi> @ '' )''"
| "print_fo app srt d (Iff \<phi> \<psi>) =
     ''( '' @ print_fo app srt d \<phi> @ '' <=> '' @ print_fo app srt d \<psi> @ '' )''"
| "print_fo app srt d (All \<phi>) =
     ''( ! ['' @ var_name (d + 1) @ '': '' @ srt @ ''] : '' @ print_fo app srt (d + 1) \<phi> @ '' )''"
| "print_fo app srt d (Ex \<phi>) =
     ''( ? ['' @ var_name (d + 1) @ '': '' @ srt @ ''] : '' @ print_fo app srt (d + 1) \<phi> @ '' )''"

definition tf0_app :: "pred \<Rightarrow> string \<Rightarrow> string" where
  "tf0_app p v = (case p of PA \<Rightarrow> ''a'' | PC \<Rightarrow> ''c'' | PFin \<Rightarrow> ''fin'') @ ''('' @ v @ '')''"

definition th0_app :: "pred \<Rightarrow> string \<Rightarrow> string" where
  "th0_app p v = ''('' @ (case p of PA \<Rightarrow> ''A'' | PC \<Rightarrow> ''C'' | PFin \<Rightarrow> ''fin'') @ '' @ '' @ v @ '')''"

definition tf0 :: "fo \<Rightarrow> string" where
  "tf0 = print_fo tf0_app ''interp'' 0"

definition th0 :: "fo \<Rightarrow> string" where
  "th0 = print_fo th0_app ''$i'' 0"

subsubsection \<open>Problem files\<close>

definition problem_name :: "success \<Rightarrow> success \<Rightarrow> string" where
  "problem_name s t = ''SZS_'' @ mnemonic s @ ''_isa_'' @ mnemonic t"

definition formula_name :: "success \<Rightarrow> success \<Rightarrow> string" where
  "formula_name s t = ''isa_'' @ status_value s @ ''_'' @ status_value t"

definition hrule :: string where
  "hrule = ''%'' @ replicate 78 (CHR ''-'')"

definition header :: "string \<Rightarrow> success \<Rightarrow> success \<Rightarrow> string list" where
  "header lang s t =
     [hrule,
      ''% File     : '' @ problem_name s t @ '' : SZS Ontologies v1.0.0.'',
      ''% Domain   : Knowledge Representation'',
      ''% Problem  : '' @ mnemonic s @ '' isa '' @ mnemonic t,
      ''% Version  : Especial.'',
      ''% English  : '' @ one_word s @ '' isa '' @ one_word t @ '' in the SZS success ontology.'',
      ''% Refs     : [Sut08] Sutcliffe (2008), The SZS Ontologies for Automated Rea'',
      ''%          : [SS26]  Schuster & Sutcliffe (2026), The SZS Ontologies.'',
      ''% Source   : [SS26]'',
      ''% Names    :'',
      ''% Status   : Theorem'',
      ''% Rating   : ?'',
      ''% SPC      : '' @ lang @ ''_THM_NEQ_NAR'',
      ''% Comments : Generated by SZS_Export of the AFP entry SZS_Ontologies from the'',
      ''%            cover relation of SZS_Hierarchy.  The conjecture is the formula'',
      ''%            edge_problem '' @ mnemonic s @ '' '' @ mnemonic t @ '' of SZS_TPTP, which by edge_problem_isa'',
      ''%            and cond_of_holds states isa '' @ mnemonic s @ '' '' @ mnemonic t @ ''; the axiom is the'',
      ''%            assumption of covers_valid.'',
      hrule]"

definition tf0_problem :: "success \<Rightarrow> success \<Rightarrow> string" where
  "tf0_problem s t = unlines (header ''TF0'' s t @
     [''tff(interp_type,type,'',
      ''    interp: $tType ).'',
      '''',
      ''tff(a_type,type,'',
      ''    a: interp > $o ).'',
      '''',
      ''tff(c_type,type,'',
      ''    c: interp > $o ).'',
      '''',
      ''tff(fin_type,type,'',
      ''    fin: interp > $o ).'',
      '''',
      ''%----There is a finite interpretation'',
      ''tff(fin_nonempty,axiom,'',
      ''    '' @ tf0 fin_nonempty @ '' ).'',
      '''',
      ''%----'' @ one_word s @ '' isa '' @ one_word t,
      ''tff('' @ formula_name s t @ '',conjecture,'',
      ''    '' @ tf0 (edge_problem s t) @ '' ).'',
      '''',
      hrule])"

definition th0_problem :: "success \<Rightarrow> success \<Rightarrow> string" where
  "th0_problem s t = unlines (header ''TH0'' s t @
     [''thf(fin_type,type,'',
      ''    fin: $i > $o ).'',
      '''',
      ''%----There is a finite interpretation'',
      ''thf(fin_nonempty,axiom,'',
      ''    '' @ th0 fin_nonempty @ '' ).'',
      '''',
      ''%----'' @ one_word s @ '' isa '' @ one_word t,
      ''thf('' @ formula_name s t @ '',conjecture,'',
      ''    ! [A: $i > $o,C: $i > $o] :'',
      ''      '' @ th0 (edge_problem s t) @ '' ).'',
      '''',
      hrule])"

definition tf0_problems :: "(String.literal \<times> String.literal) list" where
  "tf0_problems =
     [(String.implode (''TF0/'' @ problem_name s t @ ''.p''), String.implode (tf0_problem s t)).
      (s, t) \<leftarrow> covers]"

definition th0_problems :: "(String.literal \<times> String.literal) list" where
  "th0_problems =
     [(String.implode (''TH0/'' @ problem_name s t @ ''.p''), String.implode (th0_problem s t)).
      (s, t) \<leftarrow> covers]"

lemma length_tf0_problems: "length tf0_problems = 76"
  by eval

end
