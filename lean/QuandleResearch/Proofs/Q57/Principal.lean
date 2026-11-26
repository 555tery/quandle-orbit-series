import QuandleResearch.Questions.Issue013
import QuandleResearch.Proofs.Q525.OrbitLemmas

/-! Elementary orbit-series infrastructure for Question 5.7.
The positive extension theorem and the infinite disjoint-union
counterexample are separate obligations. -/
namespace QuandleResearch.Q57
open BCNW Issue013
variable {X Y : Type*} [_root_.Quandle X] [_root_.Quandle Y]

theorem map_invAct (f : ShelfHom X Y) (x y : X) :
    f (_root_.Rack.invAct x y) = _root_.Rack.invAct (f x) (f y) := by
  apply (_root_.Rack.act' (f x)).injective
  change Shelf.act (f x) (f (_root_.Rack.invAct x y)) =
    Shelf.act (f x) (_root_.Rack.invAct (f x) (f y))
  rw [← f.map_act]
  simp

theorem fibre_isSubrack (f : ShelfHom X Y) (b : Y) : IsSubrack (fibre f b) := by
  intro y hy x hx
  change f y ∈ ({b} : Set Y) at hy
  change f x ∈ ({b} : Set Y) at hx
  have hy' := Set.mem_singleton_iff.mp hy
  have hx' := Set.mem_singleton_iff.mp hx
  constructor
  · change f (Shelf.act y x) ∈ ({b} : Set Y)
    rw [f.map_act,hy',hx']
    simp
  · change f (_root_.Rack.invAct y x) ∈ ({b} : Set Y)
    rw [map_invAct,hy',hx']
    simp

theorem translationGroup_mono {s t : Set X} (h : s ⊆ t) :
    translationGroup s ≤ translationGroup t := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x,hx,rfl⟩
  exact translation_mem (h hx)

theorem orbitIn_mono {s t : Set X} (h : s ⊆ t) (x : X) :
    orbitIn s x ⊆ orbitIn t x := by
  intro y hy
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy.2
  refine ⟨h hy.1, MulAction.mem_orbit_iff.mpr ?_⟩
  exact ⟨⟨g.val,translationGroup_mono h g.property⟩,hg⟩

theorem principal_mono {s t : Set X} (h : s ⊆ t) (x : X) (n : Nat) :
    principalSeries s x n ⊆ principalSeries t x n := by
  induction n with
  | zero => exact h
  | succ n ih => exact orbitIn_mono ih x

theorem principal_tail (s : Set X) (x : X) (r m : Nat) :
    principalSeries (principalSeries s x r) x m = principalSeries s x (r+m) := by
  induction m with
  | zero => simp [principalSeries]
  | succ m ih =>
    change orbitIn (principalSeries (principalSeries s x r) x m) x =
      orbitIn (principalSeries s x (r+m)) x
    rw [ih]

theorem stable_succ {s : Set X} {x : X} {n : Nat} (h : StableAt s x n) :
    StableAt s x (n+1) := by
  change principalSeries s x (n+1) = orbitIn (principalSeries s x (n+1)) x
  change principalSeries s x n = principalSeries s x (n+1) at h
  conv_rhs => rw [← h]
  rfl

theorem stable_later {s : Set X} {x : X} {n m : Nat}
    (h : StableAt s x n) (hnm : n ≤ m) : StableAt s x m := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ k hk ih => exact stable_succ ih

theorem stable_of_OS {s : Set X} (hs : IsSubrack s) (h : OS s)
    {x : X} (hx : x ∈ s) : ∃ n, StableAt s x n :=
  h _ (principal_isOrbitSeries hs hx)

theorem stable_of_OSBound {s : Set X} (hs : IsSubrack s)
    {n : Nat} (h : OSBound s n) {x : X} (hx : x ∈ s) :
    StableAt s x n := by
  obtain ⟨r,hr,he⟩ := h _ (principal_isOrbitSeries hs hx)
  exact stable_later he hr

/-- Sandwich step from the manuscript. It is valid for ambient
principal series and does not use the connected-base group argument. -/
theorem sandwich_stable {s e : Set X} {x : X} {r m : Nat}
    (hlo : principalSeries s x r ⊆ e) (hhi : e ⊆ s)
    (hm : StableAt s x m) : StableAt e x m := by
  have heq (i : Nat) (hi : m ≤ i) :
      principalSeries s x i = principalSeries s x (r+i) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Nat.succ_add]
      exact ih.trans (stable_later hm (by omega))
  have hsame (i : Nat) (hi : m ≤ i) :
      principalSeries e x i = principalSeries s x i := by
    have hlo' := principal_mono hlo x i
    rw [principal_tail, ← heq i hi] at hlo'
    exact Set.Subset.antisymm (principal_mono hhi x i) hlo'
  change principalSeries e x m = principalSeries e x (m+1)
  rw [hsame m le_rfl,hsame (m+1) (by omega)]
  exact hm

end QuandleResearch.Q57
