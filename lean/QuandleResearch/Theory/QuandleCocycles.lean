import QuandleResearch.Theory.LinkPresentations

/-! Inoue, arXiv:1205.5891, §§2–3, conditions C1–C3 and
Problems on Low-dimensional Topology (2013), §2.
Use Mathlib additive groups, finite sums and cardinality of finite fibres.
No duplicate theory of group cohomology: this is quandle cohomology,
with a different cocycle equation. -/
namespace QuandleResearch
noncomputable section
open scoped BigOperators

def IsQuandleTwoCocycle (Q : Quandle) {A : Type} [AddCommGroup A]
    (theta : Q.carrier → Q.carrier → A) : Prop :=
  (∀ x, theta x x = 0) ∧
  ∀ x y z, theta x y + theta (Q.op x y) z =
    theta x z + theta (Q.op x z) (Q.op y z)

def IsReducedTwoCocycle (Q : Quandle) {A : Type} [AddCommGroup A]
    (theta : Q.carrier → Q.carrier → A) : Prop :=
  IsQuandleTwoCocycle Q theta ∧
  ∀ (x : Q.carrier) (g : Q.Inn), theta x (g.val x) = 0

namespace ArcPresentation

def weight {n : Nat} (D : ArcPresentation n) (Q : Quandle)
    {A : Type} [AddCommGroup A] (theta : Q.carrier → Q.carrier → A)
    (f : D.Coloring Q) (i : Fin n) : A :=
  ∑ c : D.Crossing,
    if D.component (D.underSource c) = i then
      if D.positive c then theta (f.val (D.underSource c)) (f.val (D.overArc c))
      else -theta (f.val (D.underSource c)) (f.val (D.overArc c))
    else 0

/-- Multiplicity function of the multiset of weights, for finite Q.
The finite-target restriction prevents Nat.card from collapsing
infinite multiplicities. -/
def cocycleMultiplicity {n : Nat} (D : ArcPresentation n) (Q : Quandle)
    {A : Type} [AddCommGroup A] (theta : Q.carrier → Q.carrier → A)
    (i : Fin n) (a : A) : Nat :=
  Nat.card {f : D.Coloring Q // D.weight Q theta f i = a}

end ArcPresentation

def SameCocycleData {n : Nat} (D E : ArcPresentation n) : Prop :=
  ∀ (Q : Quandle), Nonempty Q.carrier → Finite Q.carrier → Q.Reduced →
    ∀ (A : Type) [AddCommGroup A] (theta : Q.carrier → Q.carrier → A),
      IsReducedTwoCocycle Q theta →
      ∀ (i : Fin n) (a : A), D.cocycleMultiplicity Q theta i a =
        E.cocycleMultiplicity Q theta i a
end
end QuandleResearch
