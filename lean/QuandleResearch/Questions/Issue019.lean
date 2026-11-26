import QuandleResearch.Theory.Interfaces

/-!
# Issue 19: Bardakov–Nasybullov Problem 3.6 (2019) — nilpotent enveloping groups
https://github.com/555tery/quandle-orbit-series/issues/19

Formalization status: PARTIAL.
Remaining obligation: Supply an independent classification predicate, not the target predicate itself.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1902.02154, printed p. 7](https://arxiv.org/pdf/1902.02154#page=7). Original PDF formulation checked.

## Target
Classify quandles whose enveloping group is nilpotent.
-/

namespace QuandleResearch.Issue019
noncomputable section

def verifiesClassification (answer : Quandle → Prop) : Prop :=
  ∀ (Q : Quandle) (E : Enveloping Q), answer Q ↔ Nilpotent E.G.carrier

end
end QuandleResearch.Issue019
