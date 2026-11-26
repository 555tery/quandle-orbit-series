import QuandleResearch.Theory.Interfaces

/-!
# Issue 3: Research: explicit unitriangular quandles and multipermutation levels (Question 5.25)
https://github.com/555tery/quandle-orbit-series/issues/3

Formalization status: PARTIAL.
Remaining obligation: Unitriangular matrices and the conjugacy-class carrier now fixed. Multipermutation-level comparison needs the precise retraction convention.

Source and target from the issue:
## Motivation
Simplify the second construction of [Question 5.25](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-25) using classical matrix groups, and investigate set-theoretic Yang–Baxter applications.
-/

namespace QuandleResearch.Issue003
noncomputable section

abbrev Mat (m : Nat) := Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2)
def IsUnitriangular {m : Nat} (A : Mat m) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0
def UT (m : Nat) : Subgroup (Mat m)ˣ :=
  Subgroup.closure {A | IsUnitriangular A.val}
def elementary {m : Nat} (i : Fin m) : Mat m :=
  fun a b => if a = b then 1 else
    if a.val = i.val ∧ b.val = i.val+1 then 1 else 0
def conjugacyCarrier (m : Nat) : Set (UT m) :=
  {z | ∃ (i : Fin m) (a g : UT m),
    a.val.val = elementary i ∧ z = g⁻¹*a*g}
def IsModel (m : Nat) (Q : Quandle) : Prop :=
  ∃ e : Q.carrier ≃ ↥(conjugacyCarrier m),
    ∀ x y, (e (Q.op x y)).val = (e y).val⁻¹ * (e x).val * (e y).val
def candidate (m : Nat) (Q : Quandle) : Prop :=
  2 ≤ m → IsModel m Q →
    Q.Involutory ∧ Nat.card Q.carrier = m * 2^(m-1) ∧
    ExactIndex Q.rack.LocallyReductive 2 ∧ ExactIndex Q.rack.Trivializing 2 ∧
    ExactIndex Q.rack.Reductive m ∧ lowerCentral Q.Inn (m-1) = ⊥ ∧
    (∀ x : Q.carrier, Nat.card {y // Q.rack.OrbitRel Set.univ x y} = 2^(m-1)) ∧
    (∀ x : Q.carrier, Q.rack.TrivialOn (Q.rack.orbit Set.univ x)) ∧
    Nonempty (Q.Inn ≃* ((UT m) ⧸ Subgroup.center (UT m)))
def modelExists (m : Nat) : Prop := 2 ≤ m → ∃ Q : Quandle, IsModel m Q

end
end QuandleResearch.Issue003
