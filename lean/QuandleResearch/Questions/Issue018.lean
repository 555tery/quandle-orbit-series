import QuandleResearch.Theory.Interfaces

/-!
# Issue 18: Bardakov–Nasybullov Problem 3.5 (2019) — free abelian enveloping groups
https://github.com/555tery/quandle-orbit-series/issues/18

Formalization status: PARTIAL.
Remaining obligation: Supply an independent classification predicate, not the target predicate itself.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1902.02154, printed p. 6](https://arxiv.org/pdf/1902.02154#page=6). Original PDF formulation checked.

## Target
Classify quandles with free abelian enveloping groups, without an explicit finiteness restriction in the question.
-/

namespace QuandleResearch.Issue018
noncomputable section

def FreeAbelian (G : Type) [Group G] : Prop :=
  ∃ X : Type, Nonempty (G ≃* Multiplicative (X →₀ Int))
def verifiesClassification (answer : Quandle → Prop) : Prop :=
  ∀ (Q : Quandle) (E : Enveloping Q), answer Q ↔ FreeAbelian E.G.carrier

end
end QuandleResearch.Issue018
