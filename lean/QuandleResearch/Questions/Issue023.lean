import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.Categories

/-!
# Issue 23: Bardakov–Nasybullov–Singh Problem 4.15 (2019) — semidirect products of (bi)quandles
https://github.com/555tery/quandle-orbit-series/issues/23

Formalization status: PARTIAL.
Remaining obligation: Corollary 4.14 is now encoded exactly. The requested general definition is open-ended; split-product compatibility below is a proposed formal specification, not a source-defined axiom system.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1908.08301v1, printed p. 20](https://arxiv.org/pdf/1908.08301v1#page=20). Original PDF formulation checked.

## Target
Give a general definition of a semidirect product of (bi)quandles.
-/

namespace QuandleResearch.Issue023
noncomputable section

/-- Source Corollary 4.14 uses Conj_{-1}(Aut(A)):
in its notation psi(a*b) = psi(b) psi(a) psi(b)⁻¹. -/
def IsAction (A B : Quandle) (psi : B.carrier → Equiv.Perm A.carrier) : Prop :=
  (∀ b, A.Aut (psi b)) ∧
    ∀ a b, psi (B.op a b) = psi b * psi a * (psi b)⁻¹

def specialUnder (A B : Quandle) (psi : B.carrier → Equiv.Perm A.carrier)
    (x y : A.carrier × B.carrier) : A.carrier × B.carrier :=
  (psi y.2 (A.op x.1 y.1), x.2)
def specialOver (A B : Quandle) (psi : B.carrier → Equiv.Perm A.carrier)
    (x y : A.carrier × B.carrier) : A.carrier × B.carrier :=
  (psi y.2 x.1, B.op x.2 y.2)

/-- A biquandle realizes exactly the source's known construction.
This specifies the benchmark, without proving Corollary 4.14. -/
def RealizesSpecial (A B : Quandle) (psi : B.carrier → Equiv.Perm A.carrier)
    (C : Biquandle) (e : C.carrier ≃ A.carrier × B.carrier) : Prop :=
  ∀ x y : C.carrier,
    e (C.under x y) = specialUnder A B psi (e x) (e y) ∧
    e (C.over x y) = specialOver A B psi (e x) (e y)

/-- Candidate compatibility for a general definition: it must include
the displayed special case up to the given product identification.
The design of the general construction is the requested answer. -/
def extendsCorollary414
    (isProduct : Biquandle → Biquandle → Biquandle → Prop) : Prop :=
  ∀ (A B : Quandle) (psi : B.carrier → Equiv.Perm A.carrier)
    (C : Biquandle) (e : C.carrier ≃ A.carrier × B.carrier),
    IsAction A B psi → RealizesSpecial A B psi C e →
      isProduct (embedded A) (embedded B) C

/-- The ordinary direct product should be an instance of a proposed
semidirect-product definition. This is a proposed test, not a theorem
from the text of Problem 4.15. -/
def includesQuandleDirectProducts
    (isProduct : Quandle → Quandle → Quandle → Prop) : Prop :=
  ∀ (A B C : Quandle) (e : C.carrier ≃ A.carrier × B.carrier),
    (∀ x y : C.carrier, e (C.op x y) =
      (A.op (e x).1 (e y).1, B.op (e x).2 (e y).2)) →
      isProduct A B C

end
end QuandleResearch.Issue023
