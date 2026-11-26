import QuandleResearch.Theory.Interfaces

/-!
# Issue 7: Research: Engel groups and quantitative normal-closure depth (Question 5.25)
https://github.com/555tery/quandle-orbit-series/issues/7

Formalization status: PARTIAL.
Remaining obligation: Reference family and exact group filtration; this is only one candidate research question.

Source and target from the issue:
## Motivation
The first family in [Question 5.25](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-25) is based on finite label restrictions of Noce–Tracey–Traustason's indexed group (the m=2 case of a broader Hadjievangelou–Traustason construction). The manuscript computes an orbit filtration with j=floor(log_3 n)+1 while local reductivity k=2.

## Research questions
Can the precise filtration be used to obtain new quantitative information about Engel elements, normal-closure towers and finite nilpotent groups? Can smaller finite sections realize the same separation of indices?
-/

namespace QuandleResearch.Issue007
noncomputable section

def smallerExamples (referenceSize : Nat → Nat) : Prop :=
  ∀ bound, ∃ Q : Quandle, Finite Q.carrier ∧
    ExactIndex Q.rack.LocallyReductive 2 ∧
    ∃ j, bound ≤ j ∧ ExactIndex Q.rack.Trivializing j ∧ Nat.card Q.carrier < referenceSize j

end
end QuandleResearch.Issue007
