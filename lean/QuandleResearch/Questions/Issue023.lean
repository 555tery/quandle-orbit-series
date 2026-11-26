import QuandleResearch.Theory.Interfaces

/-!
# Issue 23: Bardakov–Nasybullov–Singh Problem 4.15 (2019) — semidirect products of (bi)quandles
https://github.com/555tery/quandle-orbit-series/issues/23

Formalization status: PARTIAL.
Remaining obligation: Design constraints only; need a meaningful action, embedding and product structure.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 20](https://arxiv.org/pdf/1908.08301v1#page=20). Original PDF formulation checked.

## Target
Give a general definition of a semidirect product of (bi)quandles.
-/

namespace QuandleResearch.Issue023
noncomputable section

def quandleCandidate (A B C : Quandle) (e : C.carrier ≃ A.carrier × B.carrier) : Prop :=
  C.Hom B (fun x => (e x).2)
def biquandleCandidate (A B C : Biquandle) (e : C.carrier ≃ A.carrier × B.carrier) : Prop :=
  C.Hom B (fun x => (e x).2)

end
end QuandleResearch.Issue023
