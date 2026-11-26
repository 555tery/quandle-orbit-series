import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.Profinite

/-!
# Issue 1: Byard–Cai–Jones–Vuong–Yetter §6 — construction of profinite quandles from connected pieces
https://github.com/555tery/quandle-orbit-series/issues/1

Formalization status: PARTIAL.
Remaining obligation: Profinite inverse limits and topology are explicit. StoneUnion and Constructible specify one proposed reading of the open-ended construction in §6; verify its adequacy, especially transfinite limit stages.

Source and target from the issue:
## Source / explicitly proposed open research question
Byard, Cai, Jones, Vuong, Yetter, *On Profinite Quandles*, [arXiv:2406.15387v2, §6, first research direction](https://arxiv.org/html/2406.15387v2#S6), 2024. Can all profinite quandles be constructed from algebraically connected profinite quandles by an analogue of semi-disjoint unions indexed by Stone spaces, using transfinite induction? This is an explicitly proposed question, not a separately numbered conjecture.

## Motivation
Extend the pointwise extension bound in [Question 5.7](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-7) to profinite quandles.
-/

namespace QuandleResearch.Issue001
noncomputable section

/-- Candidate precise interpretation of the research direction in §6. -/
def question : Prop :=
  ∀ T : TopologicalQuandle, Profinite T → Constructible T

end
end QuandleResearch.Issue001
