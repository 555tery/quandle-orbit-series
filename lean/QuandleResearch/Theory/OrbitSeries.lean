import QuandleResearch.Basic.Quandle
import QuandleResearch.Theory.Groups

namespace QuandleResearch
noncomputable section
namespace Rack
def OrbitRel (R : Rack) (s : Set R.carrier) :=
  Relation.EqvGen (fun x z : R.carrier => x ∈ s ∧ z ∈ s ∧ ∃ y ∈ s, R.op x y = z)
def orbit (R : Rack) (s : Set R.carrier) (x : R.carrier) : Set R.carrier :=
  {z | z ∈ s ∧ R.OrbitRel s x z}
def IsSeries (R : Rack) (s : Set R.carrier) (a : Nat → Set R.carrier) : Prop :=
  a 0 = s ∧ ∀ n, ∃ x ∈ a n, a (n+1) = R.orbit (a n) x
def OS (R : Rack) (s : Set R.carrier) : Prop :=
  ∀ a, R.IsSeries s a → ∃ n, a n = a (n+1)
def OSBound (R : Rack) (s : Set R.carrier) (k : Nat) : Prop :=
  ∀ a, R.IsSeries s a → ∃ n ≤ k, a n = a (n+1)
def OSomega (R : Rack) (s : Set R.carrier) : Prop := ∃ k, R.OSBound s k
def principalSeries (R : Rack) (s : Set R.carrier) (x : R.carrier) : Nat → Set R.carrier
  | 0 => s
  | n+1 => R.orbit (R.principalSeries s x n) x
def PointDepth (R : Rack) (s : Set R.carrier) (x : R.carrier) (n : Nat) : Prop :=
  R.principalSeries s x n = R.principalSeries s x (n+1) ∧
    ∀ m < n, R.principalSeries s x m ≠ R.principalSeries s x (m+1)
def TrivialOn (R : Rack) (s : Set R.carrier) : Prop := ∀ x ∈ s, ∀ y ∈ s, R.op x y = x
def Trivializing (R : Rack) (k : Nat) : Prop :=
  ∀ a, R.IsSeries Set.univ a → R.TrivialOn (a k)
/-- Right-convention translation of the BCNW left-nested expression:
the varying first operand becomes the varying right operand. -/
def leftFold (R : Rack) (x : R.carrier) (ys : List R.carrier) : R.carrier :=
  ys.foldl (fun a b => R.op b a) x
def Reductive (R : Rack) (k : Nat) : Prop :=
  ∀ x y ys, ys.length = k → R.leftFold x ys = R.leftFold y ys
def LocallyReductive (R : Rack) (k : Nat) : Prop :=
  ∀ x y, R.leftFold x (List.replicate k y) = y
end Rack
def ExactIndex (P : Nat → Prop) (k : Nat) : Prop := P k ∧ ∀ m < k, ¬ P m
namespace Quandle
def Inn (Q : Quandle) : Subgroup (Equiv.Perm Q.carrier) := Subgroup.closure (Set.range Q.rack.right)
def Connected (Q : Quandle) : Prop := ∀ x y, ∃ g : Q.Inn, g.val x = y
def ResiduallyNilpotent (Q : Quandle) : Prop :=
  ∀ x y, (∀ n, ∃ g : Q.Inn, g ∈ lowerCentral Q.Inn n ∧ g.val x = y) → x = y
end Quandle
end
end QuandleResearch
