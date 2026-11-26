import QuandleResearch.Theory.Interfaces

/-!
# Issue 21: Bardakov–Nasybullov–Singh Problem 2.4 (2019) — adjoint of the quandle embedding
https://github.com/555tery/quandle-orbit-series/issues/21

Formalization status: PARTIAL.
Remaining obligation: Only hom-set shape; define embedding, functors and naturality before claiming an adjunction.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 6](https://arxiv.org/pdf/1908.08301v1#page=6). Original PDF formulation checked.

## Target
Determine the adjoint(s) to the functor B: Qnd → Bqnd, assigning the biquandle with operations x*y and x (the quandle embedding).
-/

namespace QuandleResearch.Issue021
noncomputable section

def leftAdjointCandidate (B : Quandle → Biquandle) (L : Biquandle → Quandle)
    (homEquiv : ∀ X Y, {f : (L X).carrier → Y.carrier // (L X).Hom Y f} ≃
      {f : X.carrier → (B Y).carrier // X.Hom (B Y) f}) : Prop := Nonempty (PLift (∀ X Y, Function.Bijective (homEquiv X Y)))
def rightAdjointCandidate (B : Quandle → Biquandle) (R : Biquandle → Quandle)
    (homEquiv : ∀ X Y, {f : X.carrier → (R Y).carrier // X.Hom (R Y) f} ≃
      {f : (B X).carrier → Y.carrier // (B X).Hom Y f}) : Prop :=
  ∀ X Y, Function.Bijective (homEquiv X Y)

end
end QuandleResearch.Issue021
