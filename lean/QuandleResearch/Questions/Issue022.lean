import QuandleResearch.Theory.Interfaces

/-!
# Issue 22: Bardakov–Nasybullov–Singh Problem 4.1 (2019) — adjoint of the associated-quandle functor
https://github.com/555tery/quandle-orbit-series/issues/22

Formalization status: PARTIAL.
Remaining obligation: Universal-arrow specification for both adjoints in the BNS convention; candidate constructions and independent source audit are still required.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 13](https://arxiv.org/pdf/1908.08301v1#page=13). Original PDF formulation checked.

## Target
Determine the adjoint(s) of Q: Bqnd → Qnd, the associated-quandle functor.
-/

namespace QuandleResearch.Issue022
noncomputable section

/-- Universal arrow for L ⊣ associated. -/
def leftAdjointCandidate (L : Quandle → Biquandle)
    (unit : ∀ Q, Q.carrier → (L Q).carrier) : Prop :=
  ∀ Q, Q.Hom (L Q).associated (unit Q) ∧
    ∀ B (f : Q.carrier → B.carrier), Q.Hom B.associated f →
      ∃! h : (L Q).carrier → B.carrier, (L Q).Hom B h ∧ h ∘ unit Q = f
/-- Universal arrow for associated ⊣ R. -/
def rightAdjointCandidate (R : Quandle → Biquandle)
    (counit : ∀ Q, (R Q).carrier → Q.carrier) : Prop :=
  ∀ Q, (R Q).associated.Hom Q (counit Q) ∧
    ∀ B (f : B.carrier → Q.carrier), B.associated.Hom Q f →
      ∃! h : B.carrier → (R Q).carrier, B.Hom (R Q) h ∧ counit Q ∘ h = f
def leftAdjointExists : Prop :=
  ∃ (L : Quandle → Biquandle) (unit : ∀ Q, Q.carrier → (L Q).carrier),
    leftAdjointCandidate L unit
def rightAdjointExists : Prop :=
  ∃ (R : Quandle → Biquandle) (counit : ∀ Q, (R Q).carrier → Q.carrier),
    rightAdjointCandidate R counit

end
end QuandleResearch.Issue022
