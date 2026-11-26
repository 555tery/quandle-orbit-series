import QuandleResearch.Theory.Interfaces

/-!
# Issue 1: Byard–Cai–Jones–Vuong–Yetter §6 — construction of profinite quandles from connected pieces
https://github.com/555tery/quandle-orbit-series/issues/1

Formalization status: PARTIAL.
Remaining obligation: Profinite topology, Stone-indexed semi-disjoint unions and transfinite construction.

Source and target from the issue:
## Source / explicitly proposed open research question
Byard, Cai, Jones, Vuong, Yetter, *On Profinite Quandles*, [arXiv:2406.15387v2, §6, first research direction](https://arxiv.org/html/2406.15387v2#S6), 2024. Can all profinite quandles be constructed from algebraically connected profinite quandles by an analogue of semi-disjoint unions indexed by Stone spaces, using transfinite induction? This is an explicitly proposed question, not a separately numbered conjecture.

## Motivation
Extend the pointwise extension bound in [Question 5.7](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-7) to profinite quandles.
-/

namespace QuandleResearch.Issue001
noncomputable section

def question (Profinite : Quandle → Prop) (Construction : Type)
    (stoneTransfiniteConstruction : Construction → Quandle → Prop) : Prop :=
  ∀ Q, Profinite Q → ∃ c, stoneTransfiniteConstruction c Q

end
end QuandleResearch.Issue001
