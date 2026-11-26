# Mathlib-first policy

Scope: all Lean files in this directory.

- Before introducing a mathematical definition or construction, inspect the pinned Mathlib version for an existing definition, equivalent formulation and supporting lemmas.
- Prefer native Mathlib typeclasses, bundled morphisms, group constructions, group actions, category theory and topology. Thin compatibility aliases are acceptable; do not duplicate axioms or standard recursive definitions.
- Record convention changes explicitly (especially left vs right quandle operations, commutators and automorphism composition).
- Keep all 69 issue statements and source links. Distinguish complete statements, conditional specifications, and missing source-specific constructions.
- This project currently formalizes **problem statements only**, not solutions. Do not add solution theorems, `sorry`, `admit` or new axioms.
- Proofs required to construct lawful mathematical objects (e.g. typeclass instances) are allowed; they are not proofs of the research problems.
- Run `lake build` and verify the exact commit before claiming compilation. Compilation does not establish source equivalence.
