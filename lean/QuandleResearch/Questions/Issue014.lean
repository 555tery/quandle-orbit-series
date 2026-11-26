import QuandleResearch.Theory.OrbitSeriesCore

/-!
# Issue 14 — BCNW Question 5.25
Source: Bonatto, Crans, Nasybullov, Whitney, Quandles with orbit series
conditions, J. Algebra 567 (2021), 284–309.
https://arxiv.org/html/2004.10227v3
https://github.com/555tery/quandle-orbit-series/issues/14

Formalization status: STATEMENT (source audit; CI must verify this revision).
The question asks for uniform bounds on finite nonempty quandles.
No proof of either answer is included. The two parts are independent.
-/

namespace QuandleResearch.Issue014
open BCNW
universe u

/-- A specified uniform bound for the first part:
LR_k intersect finite quandles is contained in tOS_j. -/
def IsBoundJByK (k j : Nat) : Prop :=
  ∀ (X : Type u) [_root_.Quandle X] [Finite X] [Nonempty X],
    LocallyReductive (X := X) k → Trivializing (X := X) j

/-- A specified uniform bound for the second part:
tOS_j intersect finite quandles is contained in R_i. -/
def IsBoundIByJ (j i : Nat) : Prop :=
  ∀ (X : Type u) [_root_.Quandle X] [Finite X] [Nonempty X],
    Trivializing (X := X) j → Reductive (X := X) i

/-- Question 5.25(a), uniform bound depending only on k. -/
def boundJByK : Prop :=
  ∀ k : Nat, 0 < k → ∃ j : Nat, 0 < j ∧ IsBoundJByK.{u} k j

/-- Question 5.25(b), uniform bound depending only on j. -/
def boundIByJ : Prop :=
  ∀ j : Nat, 0 < j → ∃ i : Nat, 0 < i ∧ IsBoundIByJ.{u} j i

/-- The two proposed negative answers are separately specified.
A failure of the conjunction is not a negative answer to both parts. -/
def negativeA : Prop := ¬ boundJByK.{u}
def negativeB : Prop := ¬ boundIByJ.{u}
def bothNegative : Prop := negativeA.{u} ∧ negativeB.{u}

/-- Stronger fixed-input counterexample specification relevant to the
working manuscript. These are targets, not asserted results. -/
def unboundedJAt (k : Nat) : Prop :=
  ∀ j : Nat, 0 < j → ∃ (X : Type u) (q : _root_.Quandle X),
    letI := q
    Finite X ∧ Nonempty X ∧ LocallyReductive (X := X) k ∧
      ¬ Trivializing (X := X) j

def unboundedIAt (j : Nat) : Prop :=
  ∀ i : Nat, 0 < i → ∃ (X : Type u) (q : _root_.Quandle X),
    letI := q
    Finite X ∧ Nonempty X ∧ Trivializing (X := X) j ∧
      ¬ Reductive (X := X) i

def manuscriptTargets : Prop := unboundedJAt.{u} 2 ∧ unboundedIAt.{u} 2

/-- Exact positive index profile, for checking the concrete families
later, without making exactness a hypothesis of Question 5.25. -/
def HasProfile (X : Type u) [_root_.Quandle X] (k j i : Nat) : Prop :=
  ExactPositiveIndex (LocallyReductive (X := X)) k ∧
  ExactPositiveIndex (Trivializing (X := X)) j ∧
  ExactPositiveIndex (Reductive (X := X)) i

end QuandleResearch.Issue014
