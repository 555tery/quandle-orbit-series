import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.QuandleCocycles

/-!
# Issue 4: Inoue Question 2.4 (2013) — quandle cocycle invariants and Milnor invariants
https://github.com/555tery/quandle-orbit-series/issues/4

Formalization status: PARTIAL.
Remaining obligation: Actual finite-target quandle 2-cocycle weights and multiplicities are specified. Milnor invariants and indeterminacy remain external; the requested relationship is descriptive.

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

/-- Concrete cocycle side of the requested relationship.
The Milnor invariant, its indeterminacy and the precise proposed
relation remain to be supplied independently. -/
def verifiesCocycleRelation {n : Nat} {Link M : Type}
    (diagram : Link → ArcPresentation n) (milnor : Link → M)
    (Q : Quandle) (A : Type) [AddCommGroup A]
    (theta : Q.carrier → Q.carrier → A)
    (relation : (Fin n → A → Nat) → M → Prop) : Prop :=
  Finite Q.carrier → Q.Reduced → IsReducedTwoCocycle Q theta →
    ∀ l, relation ((diagram l).cocycleMultiplicity Q theta) (milnor l)

end
end QuandleResearch.Issue004
