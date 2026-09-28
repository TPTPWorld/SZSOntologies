# SZSOntologies

`BNF/SZSOntology.bnf` is the source of truth for the three SZS ontologies.
Everything else is derived from it or checked against it:

- `BNF/BNFLinker.sedscript` turns it into the hyperlinked page published
  at <https://tptpworld.github.io/SZSOntologies/> (rebuilt on every push
  to `master`).
- `IsabelleFormalisation/` formalises the success ontology and derives
  its isa hierarchy from the definitions.  `SZS_BNF_Check.thy` reads the
  BNF when it is processed and proves that the BNF's success part is that
  hierarchy, and that the no-success and dataform parts are well formed
  (one root, acyclic, every referenced nonterminal defined, one terminal
  per rule).

CI builds the theories on every push and pull request.  An edit to the
BNF therefore fails CI until the formalisation accounts for it; for a new
success value that means formalising its definition.

## Building locally

    isabelle build -D IsabelleFormalisation

The BNF is a declared dependency of the session, so a change to it
triggers a rebuild.  The theories never write into `BNF/`.

Without a local Isabelle, `Containerfile` provides the toolchain
(Isabelle2025-2 with a prebuilt HOL heap):

    podman build -t szs-isabelle -f Containerfile .
    podman run --rm --userns=keep-id --user "$(id -u):$(id -g)" -v "$PWD:/work:ro,Z" szs-isabelle build -v -D /work/IsabelleFormalisation

## Licence

The theories in `IsabelleFormalisation/` are BSD-3-Clause; everything
else is CC BY 4.0.  See `LICENSES/`.
