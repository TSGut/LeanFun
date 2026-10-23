# Contributing to LeanFun

Open an issue before starting a larger change. Setup is in the
[README](README.md#building-and-checking). Before a pull request, run:

```sh
lake build --wfail
lake env lean scripts/CheckAxioms.lean
python test/test_review.py
leanblueprint pdf && leanblueprint web
lake exe checkdecls blueprint/lean_decls
python scripts/check_blueprint_graph.py --proofs --nodes <labels you added or changed>
```

## Lean

- Mirror Mathlib paths under `LeanFun/Mathlib/`, use Mathlib naming, and reuse existing definitions whenever possible.
- Keep definitions uniform whenever possible. Special cases, renormalisations and limits go in theorems.
- Cite a reference in every mathematical docstring, preferably the
  [DLMF](https://dlmf.nist.gov/) or *Approximation Theory and Approximation Practice* or something like it. Papers are fine too if no collected work exists.
- Every statement must keep its classical meaning. Mathlib assigns values where classical mathematics leaves things undefined, such as `x / 0`, integrals of non-integrable functions, sums of divergent series and real powers of negative numbers. A statement must never depend on such a value. Put domains in types where possible, then use predicates such as `HasSum` or `Integrable`, and otherwise hypotheses.
- Definitions have their domain in the type, so they have no values outside it. Boundary behaviour is stated classically, for example as a limit.
- No `sorry`, new axioms or `native_decide`. Toolchain and Mathlib bumps are left to the maintainer.

## RevOLVER (`blueprint/src/`)

- Statements are the source of truth. Raise a needed extra hypothesis instead of weakening a statement.
- `\leanok` only when the linked Lean compiles and matches the text. `\mathlibok` only for existing Mathlib results.
- Node text states mathematics, including any library convention that changes the meaning. Definition nodes contain only the definition.
- `\uses` lists exactly the direct dependencies of a node, with no redundant or cyclic edges. The graph checker above enforces this.
- Keep labels through minor changes and never reuse an old one.

## Review, versions and licence

For now, only the maintainer edits `review/statements.toml`. Mention in your pull request if you change a reviewed node. Releases are semantic versions are also for now only tagged by the maintainer.

Contributions are licensed under the [MIT licence](LICENSE).
