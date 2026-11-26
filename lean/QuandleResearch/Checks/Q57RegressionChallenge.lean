import QuandleResearch.Checks.Q57StatementChallenge
import Mathlib.Tactic

/-! Separate expected signatures for the source-facing regressions.
The carrier operations are concrete, not assumed. -/
namespace QuandleResearch.Q57.SemanticRegression
open BCNW Issue013 StatementAudit
universe u

section Congruence
variable {X : Type u} [_root_.Quandle X]

def PaperCongruence (r : Setoid X) : Prop :=
  ∀ a b c d : X, r.r a b → r.r c d →
    r.r (Shelf.act a c) (Shelf.act b d) ∧
    ∀ x y : X, Shelf.act a x = c → Shelf.act b y = d → r.r x y

private axiom expected_congruence_iff_paper (r : Setoid X) :
    PaperCongruence r ↔ ∃ c : QuandleCongruence X, c.toSetoid = r

theorem congruence_iff_paper (r : Setoid X) :
    PaperCongruence r ↔ ∃ c : QuandleCongruence X, c.toSetoid = r := expected_congruence_iff_paper r

end Congruence

section Series
variable {X : Type u} [_root_.Quandle X]

def PaperSeries (s : Set X) (a : Nat → Set X) : Prop :=
  a 0 = s ∧ (∀ n, IsSubrack (a n)) ∧
    ∃ x : Nat → X, ∀ n, x n ∈ a n ∧ a (n+1) = orbitIn (a n) (x n)

private axiom expected_series_iff_paper (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔ PaperSeries s a

theorem series_iff_paper (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔ PaperSeries s a := expected_series_iff_paper s a

private axiom expected_connected_bound_zero
    (h : ∀ x : X, orbitIn Set.univ x = Set.univ) :
    OSBound (Set.univ : Set X) 0

theorem connected_bound_zero
    (h : ∀ x : X, orbitIn Set.univ x = Set.univ) :
    OSBound (Set.univ : Set X) 0 := expected_connected_bound_zero h

private axiom expected_connected_D3 :
    OSBound (Set.univ : Set (Quandle.Dihedral 3)) 0

theorem connected_D3 :
    OSBound (Set.univ : Set (Quandle.Dihedral 3)) 0 := expected_connected_D3

end Series

section Trivial
abbrev T2 := Bool
local instance : Quandle T2 where
  act _ y := y
  invAct _ y := y
  self_distrib := rfl
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  fix := rfl

private axiom expected_trivial_orbit (s : Set T2) (x : T2) (hx : x ∈ s) :
    orbitIn s x = {x}

theorem trivial_orbit (s : Set T2) (x : T2) (hx : x ∈ s) :
    orbitIn s x = {x} := expected_trivial_orbit s x hx

private axiom expected_T2_bound_one : OSBound (Set.univ : Set T2) 1

theorem T2_bound_one : OSBound (Set.univ : Set T2) 1 := expected_T2_bound_one

def trivialSeries (n : Nat) : Set T2 :=
  if n = 0 then Set.univ else {false}

private axiom expected_T2_not_bound_zero : ¬ OSBound (Set.univ : Set T2) 0

theorem T2_not_bound_zero : ¬ OSBound (Set.univ : Set T2) 0 := expected_T2_not_bound_zero

end Trivial

section InfiniteDihedral
abbrev Dinf := Int
local instance : Quandle Dinf where
  act a b := (2 : Int)*a-b
  invAct a b := (2 : Int)*a-b
  self_distrib := by intro a b c; change 2*a-(2*b-c)=2*(2*a-b)-(2*a-c); ring
  left_inv := by intro a b; change 2*a-(2*a-b)=b; ring
  right_inv := by intro a b; change 2*a-(2*a-b)=b; ring
  fix := by intro a; change 2*a-a=a; ring

def multiples (d : Int) : Set Dinf := {z | ∃ k : Int, (z : Int) = d*k}

private axiom expected_orbit_zero_multiples (d : Int) :
    orbitIn (multiples d) (0 : Int) = multiples (2*d)

theorem orbit_zero_multiples (d : Int) :
    orbitIn (multiples d) (0 : Int) = multiples (2*d) := expected_orbit_zero_multiples d

def infiniteSeries (n : Nat) : Set Dinf := multiples ((2 : Int)^n)

private axiom expected_infiniteSeries_valid : IsOrbitSeries Set.univ infiniteSeries

theorem infiniteSeries_valid : IsOrbitSeries Set.univ infiniteSeries := expected_infiniteSeries_valid

private axiom expected_infiniteSeries_strict (n : Nat) :
    infiniteSeries n ≠ infiniteSeries (n+1)

theorem infiniteSeries_strict (n : Nat) :
    infiniteSeries n ≠ infiniteSeries (n+1) := expected_infiniteSeries_strict n

private axiom expected_Dinf_not_OS : ¬ OS (Set.univ : Set Dinf)

theorem Dinf_not_OS : ¬ OS (Set.univ : Set Dinf) := expected_Dinf_not_OS

end InfiniteDihedral
end QuandleResearch.Q57.SemanticRegression
