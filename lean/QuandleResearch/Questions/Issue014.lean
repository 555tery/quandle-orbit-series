import QuandleResearch.Theory.Interfaces

/-!
# Issue 14: BCNW Question 5.25 — bounds on local reductivity, orbit depth and reductivity
https://github.com/555tery/quandle-orbit-series/issues/14

Formalization status: PARTIAL.
Remaining obligation: Check BCNW convention and exact index offsets against source.

Source and target from the issue:
## Source / published open question
Bonatto–Crans–Nasybullov–Whitney, *Quandles with orbit series conditions*, [arXiv:2004.10227v3, Question 5.25](https://arxiv.org/html/2004.10227v3). For finite quandles with local reductivity index \(k\), trivializing orbit-series index \(j\), and reductivity index \(i\), can \(j\) be bounded in terms of \(k\), or \(i\) in terms of \(j\)?
-/

namespace QuandleResearch.Issue014
noncomputable section

def boundJByK : Prop :=
  ∃ f : Nat → Nat, ∀ (Q : Quandle) (k j : Nat), Finite Q.carrier →
    ExactIndex Q.rack.LocallyReductive k → ExactIndex Q.rack.Trivializing j → j ≤ f k
def boundIByJ : Prop :=
  ∃ f : Nat → Nat, ∀ (Q : Quandle) (j i : Nat), Finite Q.carrier →
    ExactIndex Q.rack.Trivializing j → ExactIndex Q.rack.Reductive i → i ≤ f j

end
end QuandleResearch.Issue014
