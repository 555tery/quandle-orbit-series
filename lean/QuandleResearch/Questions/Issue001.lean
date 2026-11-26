import QuandleResearch.Theory.Profinite

/-!
# Issue 1: Byard–Cai–Jones–Vuong–Yetter §6 — construction of profinite quandles from connected pieces
https://github.com/555tery/quandle-orbit-series/issues/1

Formalization status: PARTIAL.
Remaining obligation: Definition 5.1 now uses Mathlib's actual profinite completion of Inn(Q), not abstract Inn(Q) transitivity. Explicit mesh assembly and compatible child identifications are specified. The source leaves the exact transfinite procedure open; limit reconstruction and CI remain to be checked.

Source and target from the issue:
## Source / explicitly proposed open research question
Byard, Cai, Jones, Vuong, Yetter, *On Profinite Quandles*, [arXiv:2406.15387v2, §6, first research direction](https://arxiv.org/html/2406.15387v2#S6), 2024. Can all profinite quandles be constructed from algebraically connected profinite quandles by an analogue of semi-disjoint unions indexed by Stone spaces, using transfinite induction? This is an explicitly proposed question, not a separately numbered conjecture.

## Motivation
Extend the pointwise extension bound in [Question 5.7](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-7) to profinite quandles.
-/

namespace QuandleResearch.Issue001
noncomputable section

/-- Earlier candidate, restricted to well-founded trees of Stone unions.
It has no explicit ordinal limit stage and is not the literal §6 question. -/
def wellFoundedTreeQuestion : Prop :=
  ∀ T : TopologicalQuandle, Nonempty T.Q.carrier →
    Profinite T → Constructible T

/-- Proposed precise version of the §6 direction with explicit
transfinite successor and limit stages. It is a decomposition statement,
not a claim to have solved or fully disambiguated the construction question. -/
def question : Prop :=
  ∀ T : TopologicalQuandle, Nonempty T.Q.carrier →
    Profinite T → Nonempty (TransfiniteDecomposition T)

end
end QuandleResearch.Issue001
