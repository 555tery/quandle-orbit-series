import QuandleResearch.Theory.Interfaces

/-!
# Issue 4: Inoue Question 2.4 (2013) — quandle cocycle invariants and Milnor invariants
https://github.com/555tery/quandle-orbit-series/issues/4

Formalization status: PARTIAL.
Remaining obligation: Actual cocycle and Milnor invariants, coefficients, indeterminacy and meaningful relation; arbitrary relations do not count as answers.

Source and target from the issue:
## Source / published question
A. Inoue, §2 in T. Ohtsuki (ed.), [Problems on Low-dimensional Topology, 2013](https://www.kurims.kyoto-u.ac.jp/~ildt/2013/prob13.pdf), p. 6, Question 2.4: how are quandle cocycle invariants related to Milnor's \(\mu\)-invariants?

## Motivation
Use the quasi-trivial (reduced) unitriangular quandles proposed for Question 5.25 to study link-homotopy and finite quandle colourings.
-/

namespace QuandleResearch.Issue004
noncomputable section

def verifiesRelation {Link C M : Type} (cocycle : Link → C) (milnor : Link → M)
    (relation : C → M → Prop) : Prop := ∀ l, relation (cocycle l) (milnor l)

end
end QuandleResearch.Issue004
