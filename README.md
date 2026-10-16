# SZSOntologies

`BNF/SZSOntology.bnf` is the source of truth for the three SZS ontologies.
Everything else is derived from it or checked against it:

- `BNF/BNFLinker.sedscript` turns it into the hyperlinked page published
  at <https://tptpworld.github.io/SZSOntologies/> (rebuilt on every push
  to `master`).
- `SZS_Ontologies/` formalises the success ontology and derives its isa
  hierarchy from the definitions.  It is the Archive of Formal Proofs
  entry, and is self-contained: it reads nothing outside its directory.
- `Check/SZS_BNF_Check.thy` reads the BNF when it is processed and proves
  that the BNF's success part is that hierarchy, and that the no-success
  and dataform parts are well formed (one root, acyclic, every referenced
  nonterminal defined, one terminal per rule).  It is a repository-only
  session on top of the entry.
- `Problems/` holds one TF0 and one TH0 problem per edge of the derived
  hierarchy, exported by `SZS_Ontologies/SZS_Export.thy`.  Each conjecture
  is proved in Isabelle to state the edge's entailment.

CI builds both sessions on every push and pull request, checks that
`Problems/` equals the current export, and runs E, Vampire and
Zipperposition on every problem.  An edit to the BNF therefore fails CI
until the formalisation accounts for it; for a new success value that means
formalising its definition.

## Building locally

    isabelle build -D .

`ROOTS` lists both sessions, `SZS_Ontologies` and `SZS_Check`.  The BNF is
a declared dependency of `SZS_Check`, so a change to it triggers a rebuild.
The theories never write into `BNF/` or `Problems/`; the problems are
session exports, materialised by

    isabelle export -d . -p 1 -O Problems -x 'SZS_Ontologies.SZS_Export:T*/*' SZS_Ontologies

Without a local Isabelle, `Containerfile` provides the toolchain
(Isabelle2025-2 with a prebuilt HOL heap):

    podman build -t szs-isabelle -f Containerfile .
    podman run --rm --userns=keep-id --user "$(id -u):$(id -g)" -v "$PWD:/work:ro,Z" szs-isabelle build -v -D /work

## Licence

The theories in `SZS_Ontologies/` and `Check/` are BSD-3-Clause; everything else is CC BY 4.0.  
See `LICENSES/`.
