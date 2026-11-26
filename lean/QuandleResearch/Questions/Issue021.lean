import QuandleResearch.Theory.Interfaces

/-!
# Issue 21: Bardakov–Nasybullov–Singh Problem 2.4 (2019) — adjoint of the quandle embedding
https://github.com/555tery/quandle-orbit-series/issues/21

Formalization status: PARTIAL.
Remaining obligation: Universal-arrow specification in the BNS convention; candidate constructions and independent source audit are still required.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 6](https://arxiv.org/pdf/1908.08301v1#page=6). Original PDF formulation checked.

## Target
Determine the adjoint(s) to the functor B: Qnd → Bqnd, assigning the biquandle with operations x*y and x (the quandle embedding).
-/

namespace QuandleResearch.Issue021
noncomputable section

/-- Morphisms B → embedding(Q), with trivial beta on the target. -/
def toEmbedded (B : Biquandle) (Q : Quandle) (f : B.carrier → Q.carrier) : Prop :=
  B.associated.Hom Q f ∧ ∀ x y, f (B.beta y x) = f x
/-- Morphisms embedding(Q) → B, with trivial beta on the source. -/
def fromEmbedded (Q : Quandle) (B : Biquandle) (f : Q.carrier → B.carrier) : Prop :=
  Q.Hom B.associated f ∧ ∀ x y, B.beta (f y) (f x) = f x
/-- Universal arrows characterize a left adjoint to the embedding. -/
def leftAdjointCandidate (L : Biquandle → Quandle)
    (unit : ∀ B, B.carrier → (L B).carrier) : Prop :=
  ∀ B, toEmbedded B (L B) (unit B) ∧
    ∀ Q (f : B.carrier → Q.carrier), toEmbedded B Q f →
      ∃! h : (L B).carrier → Q.carrier, (L B).Hom Q h ∧ h ∘ unit B = f
/-- Universal arrows characterize a right adjoint to the embedding. -/
def rightAdjointCandidate (R : Biquandle → Quandle)
    (counit : ∀ B, (R B).carrier → B.carrier) : Prop :=
  ∀ B, fromEmbedded (R B) B (counit B) ∧
    ∀ Q (f : Q.carrier → B.carrier), fromEmbedded Q B f →
      ∃! h : Q.carrier → (R B).carrier, Q.Hom (R B) h ∧ counit B ∘ h = f
def leftAdjointExists : Prop :=
  ∃ (L : Biquandle → Quandle) (unit : ∀ B, B.carrier → (L B).carrier),
    leftAdjointCandidate L unit
def rightAdjointExists : Prop :=
  ∃ (R : Biquandle → Quandle) (counit : ∀ B, (R B).carrier → B.carrier),
    rightAdjointCandidate R counit

end
end QuandleResearch.Issue021
