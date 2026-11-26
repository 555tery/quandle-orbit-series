import QuandleResearch.Theory.Interfaces

/-!
# Issue 3: Research: explicit unitriangular quandles and multipermutation levels (Question 5.25)
https://github.com/555tery/quandle-orbit-series/issues/3

Formalization status: PARTIAL.
Remaining obligation: Construct the specified unitriangular group/quandle family; exact orbit count, central quotient and multipermutation level remain to be encoded.

Source and target from the issue:
## Motivation
Simplify the second construction of [Question 5.25](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-25) using classical matrix groups, and investigate set-theoretic Yang–Baxter applications.
-/

namespace QuandleResearch.Issue003
noncomputable section

def candidate (Q : Quandle) (m : Nat) : Prop :=
  2 ≤ m → Q.Involutory ∧ Nat.card Q.carrier = m * 2^(m-1) ∧
    ExactIndex Q.rack.LocallyReductive 2 ∧ ExactIndex Q.rack.Trivializing 2 ∧
    ExactIndex Q.rack.Reductive m ∧ lowerCentral Q.Inn (m-1) = ⊥ ∧
    (∀ x : Q.carrier, Nat.card {y // Q.rack.OrbitRel Set.univ x y} = 2^(m-1)) ∧
    (∀ x : Q.carrier, Q.rack.TrivialOn (Q.rack.orbit Set.univ x))

end
end QuandleResearch.Issue003
