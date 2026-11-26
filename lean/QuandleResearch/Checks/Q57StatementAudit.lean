import QuandleResearch.Questions.Issue013

/-! Statement-only audit of BCNW Question 5.7 (arXiv:2004.10227v3).
These definitional equalities expose the quantifiers without assuming or
proving either answer. See §§2.1, 2.2, 4.1 and 5.1 of the source.
No imports from Proofs/Q57 or Proofs/Q525. -/

namespace QuandleResearch.Q57.StatementAudit
open BCNW Issue013
universe u v

-- Section 4.1: every series stabilizes, with a bound depending on it.
example {X : Type u} [_root_.Quandle X] (s : Set X) :
    OS s ↔ ∀ a : Nat → Set X, IsOrbitSeries s a →
      ∃ k : Nat, a k = a (k+1) := Iff.rfl

-- Section 4.1: one positive bound for all series in this quandle.
example {X : Type u} [_root_.Quandle X] (s : Set X) :
    OSomega s ↔ ∃ n : Nat, 0 < n ∧
      ∀ a : Nat → Set X, IsOrbitSeries s a →
        ∃ k : Nat, k ≤ n ∧ a k = a (k+1) := Iff.rfl

-- Section 2.2: a full fibre is the congruence class, not an
-- arbitrarily chosen subquandle of it.
example {X : Type u} {Y : Type v} [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (b : Y) :
    fibre f b = {x : X | f x = b} := rfl

-- Question 5.7(a), explicitly expanded.
example : extensionOS.{u,v} ↔
    ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
      [Nonempty X] [Nonempty Y] (f : ShelfHom X Y),
      Function.Surjective f →
      (∀ a : Nat → Set Y, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ b : Y, ∀ a : Nat → Set X, IsOrbitSeries {x : X | f x = b} a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ a : Nat → Set X, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1)) := Iff.rfl

-- Question 5.7(b): the fibre bound is inside the quantifier over b.
-- The source bound is outside the quantifier over source series.
example : extensionOSomega.{u,v} ↔
    ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
      [Nonempty X] [Nonempty Y] (f : ShelfHom X Y),
      Function.Surjective f →
      (∃ n : Nat, 0 < n ∧
        ∀ a : Nat → Set Y, IsOrbitSeries Set.univ a →
          ∃ k : Nat, k ≤ n ∧ a k = a (k+1)) →
      (∀ b : Y, ∃ m : Nat, 0 < m ∧
        ∀ a : Nat → Set X, IsOrbitSeries {x : X | f x = b} a →
          ∃ k : Nat, k ≤ m ∧ a k = a (k+1)) →
      (∃ l : Nat, 0 < l ∧
        ∀ a : Nat → Set X, IsOrbitSeries Set.univ a →
          ∃ k : Nat, k ≤ l ∧ a k = a (k+1)) := Iff.rfl

-- This is the proposed answer, NOT an assertion that it holds.
example : answer.{u,v} ↔ (extensionOS.{u,v} ∧ ¬ extensionOSomega.{u,v}) :=
  Iff.rfl


-- A ShelfHom between racks automatically preserves inverse translations.
-- This verifies that no extra congruence compatibility is omitted.
theorem map_invAct {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (x y : X) :
    f (_root_.Rack.invAct x y) = _root_.Rack.invAct (f x) (f y) := by
  apply (_root_.Rack.act' (f x)).injective
  change Shelf.act (f x) (f (_root_.Rack.invAct x y)) =
    Shelf.act (f x) (_root_.Rack.invAct (f x) (f y))
  rw [← f.map_act]
  simp

-- A full fibre really is a subquandle in the ambient-set representation.
theorem fibre_isSubrack {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (b : Y) : IsSubrack (fibre f b) := by
  intro y hy x hx
  change f y ∈ ({b} : Set Y) at hy
  change f x ∈ ({b} : Set Y) at hx
  have hy' := Set.mem_singleton_iff.mp hy
  have hx' := Set.mem_singleton_iff.mp hx
  constructor
  · change f (Shelf.act y x) ∈ ({b} : Set Y)
    rw [f.map_act, hy', hx']
    simp
  · change f (_root_.Rack.invAct y x) ∈ ({b} : Set Y)
    rw [map_invAct, hy', hx']
    simp

theorem fibre_nonempty {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (hf : Function.Surjective f) (b : Y) :
    (fibre f b).Nonempty := by
  obtain ⟨x, hx⟩ := hf b
  exact ⟨x, Set.mem_singleton_iff.mpr hx⟩

-- Expose all orbit choices and the generated permutation group.
-- No constant anchor or nonempty infinite intersection is imposed.
example {X : Type u} [_root_.Quandle X] (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔
      a 0 = s ∧ (∀ n, IsSubrack (a n)) ∧
        ∀ n, ∃ x ∈ a n,
          a (n+1) = a n ∩ MulAction.orbit
            (Subgroup.closure ((_root_.Rack.act' : X → Equiv.Perm X) '' a n)) x :=
  Iff.rfl

-- Verify that layers cannot grow; the source's descending condition is
-- not an additional assumption.
theorem series_step_subset {X : Type u} [_root_.Quandle X]
    {s : Set X} {a : Nat → Set X} (ha : IsOrbitSeries s a) (n : Nat) :
    a (n+1) ⊆ a n := by
  obtain ⟨x, _, hx⟩ := ha.2.2 n
  rw [hx]
  exact Set.inter_subset_left

end QuandleResearch.Q57.StatementAudit
