import QuandleResearch.Theory.Interfaces

/-!
# Issue 22: Bardakov–Nasybullov–Singh Problem 4.1 (2019) — adjoint of the associated-quandle functor
https://github.com/555tery/quandle-orbit-series/issues/22

Formalization status: PARTIAL.
Remaining obligation: Only hom-set shape; functors and naturality remain to be formalized.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 13](https://arxiv.org/pdf/1908.08301v1#page=13). Original PDF formulation checked.

## Target
Determine the adjoint(s) of Q: Bqnd → Qnd, the associated-quandle functor.
-/

namespace QuandleResearch.Issue022
noncomputable section

def leftAdjointCandidate (L : Quandle → Biquandle)
    (homEquiv : ∀ X Y, {f : (L X).carrier → Y.carrier // (L X).Hom Y f} ≃
      {f : X.carrier → Y.associated.carrier // X.Hom Y.associated f}) : Prop :=
  ∀ X Y, Function.Bijective (homEquiv X Y)
def rightAdjointCandidate (R : Quandle → Biquandle)
    (homEquiv : ∀ X Y, {f : X.associated.carrier → Y.carrier // X.associated.Hom Y f} ≃
      {f : X.carrier → (R Y).carrier // X.Hom (R Y) f}) : Prop :=
  ∀ X Y, Function.Bijective (homEquiv X Y)

end
end QuandleResearch.Issue022
