# SZSOntologies

Isabelle/HOL formalisation of the SZS success ontology, its derived BNF, and
(in progress) a TF0/TH0 export of the derived hierarchy.  `PLAN.md` (local,
untracked) holds the work plan, the open decisions and their defaults.

## Layout

- `BNF/SZSOntology.bnf` — source of truth.  Never written by a build.
- `SZS_Ontologies/` — the AFP entry, submitted verbatim.  Self-contained:
  no `external_file` outside it, no session dependencies beyond `HOL`.
- `Check/` — repository-only session `SZS_Check`; reads the BNF and proves
  it agrees with the formalisation.
- `Problems/` — generated TF0/TH0 problems, committed, diffed by CI (planned).
- `ROOTS` lists both sessions.

## Commands

- Build everything: `isabelle build -D .`
- Export the generated problems (once `SZS_Export` exists):
  `isabelle export -d . -x 'SZS_Ontologies.SZS_Export:T*/*' -p 1 -O Problems SZS_Ontologies`
- Check the ATP backends before relying on them: `atp_mcp doctor`

## Invariants

- Theories never write into `BNF/` or `Problems/`; CI diffs both.
- The mathematics (definitions in `SZS_Semantics`, `SZS_Shapes`,
  `SZS_Hierarchy`) is not changed without a note; after submission the
  entry must stay "monotone" (additions only).
- `SZS_Ontologies/` must build alone, on the current Isabelle release,
  with `-o document=pdf`.

## Exporter loop

edit → `isabelle build -D .` → `isabelle export …` → `lint_problem` on
every file → TF0: `query_backend` (`backend: "local_exec"`, E) → TH0:
`compare_provers` (`Leo-III`, `Zipperposition`) → every status must equal
the file's `% Status` line.

## Isabelle via MCP

`prove_isabelle` runs against the resident `atp_mcp` server configured in
`.claude/atp_mcp.exs` (session `SZS_Ontologies`, the repository as session dir).
Build the heap with `isabelle build -D .` before the first call, or the
session start times out.  To try a lemma:

    theory Scratch imports SZS_Ontologies.SZS_Semantics begin … end

Edit the theories themselves in jEdit, not through `prove_isabelle`.
