import QuandleResearch.Checks.Q57StatementAudit
import Mathlib.Tactic

/-! Independent source-facing regressions: BCNW v3 §2.2, equation (7),
Examples 4.3, 4.4 and 4.9. No proof of either answer is imported. -/
namespace QuandleResearch.Q57.SemanticRegression
open BCNW Issue013 StatementAudit
universe u

section Congruence
variable {X : Type u} [_root_.Quandle X]

/-- The two implications in the authors' prose, using a bare equivalence relation. -/
def PaperCongruence (r : Setoid X) : Prop :=
  ∀ a b c d : X, r.r a b → r.r c d →
    r.r (Shelf.act a c) (Shelf.act b d) ∧
    ∀ x y : X, Shelf.act a x = c → Shelf.act b y = d → r.r x y

theorem congruence_iff_paper (r : Setoid X) :
    PaperCongruence r ↔ ∃ c : QuandleCongruence X, c.toSetoid = r := by
  constructor
  · intro h
    refine ⟨{ toSetoid := r, act_compat := ?_, inv_compat := ?_ }, rfl⟩
    · intro a b x y hab hxy
      exact (h a b x y hab hxy).1
    · intro a b x y hab hxy
      exact (h a b x y hab hxy).2 _ _
        (Rack.act_invAct_eq a x) (Rack.act_invAct_eq b y)
  · rintro ⟨c, rfl⟩ a b x y hab hxy
    exact ⟨c.act_compat hab hxy, fun z w hz hw =>
      c.source_inverse_condition hab hxy hz hw⟩

end Congruence

section Series
variable {X : Type u} [_root_.Quandle X]

/-- Explicit sequence of choices as in the construction preceding (7). -/
def PaperSeries (s : Set X) (a : Nat → Set X) : Prop :=
  a 0 = s ∧ (∀ n, IsSubrack (a n)) ∧
    ∃ x : Nat → X, ∀ n, x n ∈ a n ∧ a (n+1) = orbitIn (a n) (x n)

theorem series_iff_paper (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔ PaperSeries s a := by
  constructor
  · intro h
    classical
    exact ⟨h.1, h.2.1, fun n => Classical.choose (h.2.2 n),
      fun n => Classical.choose_spec (h.2.2 n)⟩
  · rintro ⟨h0, hs, x, hx⟩
    exact ⟨h0, hs, fun n => ⟨x n, (hx n).1, (hx n).2⟩⟩

theorem singleton_subrack (x : X) : IsSubrack ({x} : Set X) := by
  intro y hy z hz
  have hy' : y = x := hy
  have hz' : z = x := hz
  subst y
  subst z
  simp

theorem singleton_orbit (x : X) : orbitIn ({x} : Set X) x = {x} := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    have he : z = x := hz
    subst z
    exact ⟨rfl, MulAction.mem_orbit_self x⟩

/-- Connectedness implies exact stabilization at stage zero, not at one. -/
theorem connected_bound_zero
    (h : ∀ x : X, orbitIn Set.univ x = Set.univ) :
    OSBound (Set.univ : Set X) 0 := by
  intro a ha
  obtain ⟨x, hx, he⟩ := ha.2.2 0
  have h1 : a 1 = Set.univ := by simpa only [ha.1, h x] using he
  exact ⟨0, le_rfl, ha.1.trans h1.symm⟩

theorem connected_D3 :
    OSBound (Set.univ : Set (Quandle.Dihedral 3)) 0 := by
  apply connected_bound_zero
  intro x
  ext z
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    refine ⟨Set.mem_univ _, (walk_iff_orbit _ _ _).mp ?_⟩
    have h : ∃ y : Quandle.Dihedral 3, Shelf.act y x = z := by
      change ∃ y : ZMod 3, 2*y-x=z
      refine ⟨2*(z+x), ?_⟩
      have h4 : (4 : ZMod 3) = 1 := by decide
      calc
        2*(2*(z+x))-x = 4*(z+x)-x := by ring
        _ = z := by rw [h4]; ring
    obtain ⟨y, hy⟩ := h
    rw [← hy]
    exact Walk.forward Walk.nil ⟨y, Set.mem_univ _, rfl⟩
end Series

section Trivial
/-- The two-element trivial quandle from the orbit-tree examples. -/
def T2 := Bool
local instance : Quandle T2 where
  act _ y := y
  invAct _ y := y
  self_distrib := rfl
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  fix := rfl

theorem trivial_orbit (s : Set T2) (x : T2) (hx : x ∈ s) :
    orbitIn s x = {x} := by
  ext z
  constructor
  · intro hz
    have hw := (walk_iff_orbit _ _ _).mpr hz.2
    induction hw with
    | nil => rfl
    | forward h hg ih =>
      obtain ⟨y, hy, rfl⟩ := hg
      exact ih
    | backward h hg ih =>
      obtain ⟨y, hy, rfl⟩ := hg
      exact ih
  · intro hz
    have he : z = x := hz
    subst z
    exact ⟨hx, MulAction.mem_orbit_self x⟩

theorem T2_bound_one : OSBound (Set.univ : Set T2) 1 := by
  intro a ha
  obtain ⟨x, hx, he⟩ := ha.2.2 0
  have h1 : a 1 = {x} := he.trans (trivial_orbit _ _ hx)
  obtain ⟨y, hy, hy'⟩ := ha.2.2 1
  have h2 : y = x := by rw [h1] at hy; exact hy
  subst y
  have h3 : a 2 = {x} := by rw [hy', h1, singleton_orbit]
  exact ⟨1, le_rfl, h1.trans h3.symm⟩

def trivialSeries (n : Nat) : Set T2 :=
  if n = 0 then Set.univ else {false}

theorem T2_not_bound_zero : ¬ OSBound (Set.univ : Set T2) 0 := by
  intro h
  have hs : IsOrbitSeries Set.univ trivialSeries := by
    refine ⟨rfl, ?_, ?_⟩
    · intro n
      by_cases hn : n = 0
      · simp only [trivialSeries, hn, if_true]
        intro y hy x hx
        exact ⟨Set.mem_univ _, Set.mem_univ _⟩
      · simp only [trivialSeries, hn, if_false]
        exact singleton_subrack false
    · intro n
      refine ⟨false, ?_, ?_⟩
      · by_cases hn : n = 0 <;> simp [trivialSeries, hn]
      · have hx : (false : T2) ∈ trivialSeries n := by
          by_cases hn : n = 0 <;> simp [trivialSeries, hn]
        rw [trivial_orbit _ _ hx]
        simp [trivialSeries]
  obtain ⟨n, hn, he⟩ := h _ hs
  have hn' : n = 0 := Nat.eq_zero_of_le_zero hn
  subst n
  have ht : (true : T2) ∈ trivialSeries 0 := Set.mem_univ _
  rw [he] at ht
  simpa [trivialSeries] using ht
end Trivial

section InfiniteDihedral

/-- Example 4.9, with the exact operation on integers from the paper. -/
def Dinf := Int
local instance : Quandle Dinf where
  act a b := (2 : Int)*a-b
  invAct a b := (2 : Int)*a-b
  self_distrib := by intro a b c; change 2*a-(2*b-c)=2*(2*a-b)-(2*a-c); ring
  left_inv := by intro a b; change 2*a-(2*a-b)=b; ring
  right_inv := by intro a b; change 2*a-(2*a-b)=b; ring
  fix := by intro a; change 2*a-a=a; ring

def multiples (d : Int) : Set Dinf := {z | ∃ k : Int, (z : Int) = d*k}

theorem multiples_subrack (d : Int) : IsSubrack (multiples d) := by
  rintro y ⟨i, hi⟩ x ⟨j, hj⟩
  constructor <;> refine ⟨2*i-j, ?_⟩ <;>
    change 2*(y : Int)-(x : Int)=d*(2*i-j) <;> rw [hi,hj] <;> ring

theorem orbit_zero_multiples (d : Int) :
    orbitIn (multiples d) (0 : Int) = multiples (2*d) := by
  ext z
  constructor
  · intro hz
    have hw := (walk_iff_orbit _ _ _).mpr hz.2
    induction hw with
    | nil => exact ⟨0, by ring⟩
    | forward h hg ih =>
      obtain ⟨y, ⟨i, hi⟩, rfl⟩ := hg
      obtain ⟨j,hj⟩ := ih
      refine ⟨i-j, ?_⟩
      change 2*(y : Int)-_ = 2*d*(i-j)
      rw [hi,hj]
      ring
    | backward h hg ih =>
      obtain ⟨y, ⟨i, hi⟩, rfl⟩ := hg
      obtain ⟨j,hj⟩ := ih
      refine ⟨i-j, ?_⟩
      change 2*(y : Int)-_ = 2*d*(i-j)
      rw [hi,hj]
      ring
  · rintro ⟨k,hk⟩
    refine ⟨⟨2*k, by rw [hk]; ring⟩, (walk_iff_orbit _ _ _).mp ?_⟩
    have hw : Walk ((_root_.Rack.act' : Dinf → Equiv.Perm Dinf) '' multiples d)
        (0 : Int) ((_root_.Rack.act' (d*k : Int)) (0 : Int)) :=
      Walk.forward Walk.nil ⟨(d*k : Int), ⟨k,rfl⟩, rfl⟩
    have he : (_root_.Rack.act' (d*k : Int)) (0 : Int) = z := by
      change 2*(d*k)-0 = z
      rw [hk]
      ring
    exact he ▸ hw

def infiniteSeries (n : Nat) : Set Dinf := multiples ((2 : Int)^n)

theorem infiniteSeries_valid : IsOrbitSeries Set.univ infiniteSeries := by
  refine ⟨?_, fun n => multiples_subrack _, ?_⟩
  · ext z
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact ⟨z, by simp [pow_zero]⟩
  · intro n
    refine ⟨(0 : Int), ⟨0, by ring⟩, ?_⟩
    change multiples ((2 : Int)^(n+1)) =
      orbitIn (multiples ((2 : Int)^n)) (0 : Int)
    rw [orbit_zero_multiples, pow_succ, mul_comm ((2 : Int)^n) 2]

theorem infiniteSeries_strict (n : Nat) :
    infiniteSeries n ≠ infiniteSeries (n+1) := by
  intro h
  let d : Int := 2^n
  have hd : 0 < d := pow_pos (by decide) _
  have hm : (d : Dinf) ∈ infiniteSeries n := ⟨1, by simp [d]⟩
  rw [h] at hm
  obtain ⟨k,hk⟩ := hm
  have he : d = d*2*k := by
    change d = ((2 : Int)^(n+1))*k at hk
    simpa only [d, pow_succ] using hk
  have hz : d*(1-2*k)=0 := by linear_combination he
  rcases mul_eq_zero.mp hz with h0 | h0
  · omega
  · omega

theorem Dinf_not_OS : ¬ OS (Set.univ : Set Dinf) := by
  intro h
  obtain ⟨n,hn⟩ := h _ infiniteSeries_valid
  exact infiniteSeries_strict n hn

end InfiniteDihedral

#print axioms congruence_iff_paper
#print axioms series_iff_paper
#print axioms connected_D3
#print axioms T2_bound_one
#print axioms T2_not_bound_zero
#print axioms Dinf_not_OS

end QuandleResearch.Q57.SemanticRegression
