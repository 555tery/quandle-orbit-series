import QuandleResearch.Basic.Quandle
import QuandleResearch.Theory.OrbitSeriesCore
import QuandleResearch.Theory.Groups

namespace QuandleResearch
noncomputable section
namespace Rack
/-- Compatibility API: the source definitions now live in the native
unbundled BCNW core, independent of the group-theoretic research tasks. -/
abbrev translationGroup (R : Rack) (s : Set R.carrier) : Subgroup (Equiv.Perm R.carrier) :=
  BCNW.translationGroup s
abbrev OrbitRel (R : Rack) (s : Set R.carrier) (x z : R.carrier) : Prop :=
  BCNW.orbitRel s x z
abbrev orbit (R : Rack) (s : Set R.carrier) (x : R.carrier) : Set R.carrier :=
  BCNW.orbitIn s x
abbrev IsSeries (R : Rack) (s : Set R.carrier) (a : Nat → Set R.carrier) : Prop :=
  BCNW.IsOrbitSeries s a
abbrev OS (R : Rack) (s : Set R.carrier) : Prop := BCNW.OS s
abbrev OSBound (R : Rack) (s : Set R.carrier) (k : Nat) : Prop := BCNW.OSBound s k
def OSomega (R : Rack) (s : Set R.carrier) : Prop := ∃ k, R.OSBound s k
abbrev principalSeries (R : Rack) (s : Set R.carrier) (x : R.carrier) : Nat → Set R.carrier :=
  BCNW.principalSeries s x
def PointDepth (R : Rack) (s : Set R.carrier) (x : R.carrier) (n : Nat) : Prop :=
  R.principalSeries s x n = R.principalSeries s x (n+1) ∧
    ∀ m < n, R.principalSeries s x m ≠ R.principalSeries s x (m+1)
def TrivialOn (R : Rack) (s : Set R.carrier) : Prop := ∀ x ∈ s, ∀ y ∈ s, R.op x y = x
abbrev Trivializing (R : Rack) (k : Nat) : Prop := BCNW.Trivializing (X := R.carrier) k
abbrev TrivializingEventually (R : Rack) : Prop := BCNW.TrivializingEventually (X := R.carrier)
def TrivializingOmega (R : Rack) : Prop := ∃ k, R.Trivializing k
abbrev leftFold (R : Rack) (x : R.carrier) (ys : List R.carrier) : R.carrier :=
  BCNW.leftFold x ys
abbrev Reductive (R : Rack) (k : Nat) : Prop := BCNW.Reductive (X := R.carrier) k
abbrev LocallyReductive (R : Rack) (k : Nat) : Prop := BCNW.LocallyReductive (X := R.carrier) k
end Rack
def ExactIndex (P : Nat → Prop) (k : Nat) : Prop := P k ∧ ∀ m < k, ¬ P m
/-- Published BCNW families are indexed by positive integers. -/
def PositiveExactIndex (P : Nat → Prop) (k : Nat) : Prop :=
  0 < k ∧ P k ∧ ∀ m, 0 < m → m < k → ¬ P m
namespace Quandle
abbrev Inn (Q : Quandle) : Subgroup (Equiv.Perm Q.carrier) := Q.rack.translationGroup Set.univ
abbrev Connected (Q : Quandle) : Prop := MulAction.IsPretransitive Q.Inn Q.carrier
/-- Darné v3 Definition 2.1: nilpotence of the inner group.
His class c corresponds to Mathlib lower central index c-1. -/
abbrev Nilpotent (Q : Quandle) : Prop := Group.IsNilpotent Q.Inn
def NilpotentClassAtMost (Q : Quandle) (c : Nat) : Prop :=
  0 < c ∧ Subgroup.lowerCentralSeries (⊤ : Subgroup Q.Inn) (c-1) = ⊥
/-- Darné v3 Definition 2.20, literally: distinct elements are
separated by a surjective morphism to a nilpotent quandle. -/
def ResiduallyNilpotent (Q : Quandle) : Prop :=
  ∀ x y : Q.carrier, x ≠ y → ∃ (R : Quandle) (f : Q.HomType R),
    Function.Surjective f ∧ R.Nilpotent ∧ f x ≠ f y
/-- Equivalent criterion in the text following Definition 2.20.
Equivalence is a statement, not a new assumption or a proved result. -/
def ResiduallyNilpotentByOrbits (Q : Quandle) : Prop :=
  ∀ x y : Q.carrier,
    (∀ n : Nat, y ∈ (MulAction.orbit (lowerCentral Q.Inn n) x : Set Q.carrier)) → x = y
end Quandle
end
end QuandleResearch
