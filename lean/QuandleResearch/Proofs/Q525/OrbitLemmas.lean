import QuandleResearch.Theory.OrbitSeriesCore
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-! Infrastructure for the proofs of Question 5.25.
Reference: q525_preprint_en.tex, §2 (Definitions and a reductivity
criterion), §3.3 (The quandle and its depth), §4.2 (Orbits and indices).
No group-construction result is assumed as an axiom. -/
namespace QuandleResearch.BCNW
variable {X : Type*} [_root_.Rack X]

theorem orbitIn_subset (s : Set X) (x : X) : orbitIn s x ⊆ s :=
  Set.inter_subset_left

theorem self_mem_orbitIn {s : Set X} {x : X} (hx : x ∈ s) :
    x ∈ orbitIn s x :=
  ⟨hx, MulAction.mem_orbit_self x⟩

theorem translation_mem {s : Set X} {y : X} (hy : y ∈ s) :
    _root_.Rack.act' y ∈ translationGroup s :=
  Subgroup.subset_closure ⟨y, hy, rfl⟩

/-- Orbits of a subrack are subracks, with both inverse and forward closure. -/
theorem orbitIn_isSubrack {s : Set X} (hs : IsSubrack s) (a : X) :
    IsSubrack (orbitIn s a) := by
  intro y hy x hx
  have hy' : y ∈ s := hy.1
  have hx' : x ∈ s := hx.1
  let g : translationGroup s := ⟨_root_.Rack.act' y, translation_mem hy'⟩
  have h1 := MulAction.mem_orbit_of_mem_orbit g hx.2
  have h2 := MulAction.mem_orbit_of_mem_orbit g⁻¹ hx.2
  exact ⟨⟨(hs y hy' x hx').1, h1⟩, ⟨(hs y hy' x hx').2, h2⟩⟩

theorem univ_isSubrack : IsSubrack (Set.univ : Set X) := by
  intro y hy x hx
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem principal_mem_and_subrack {s : Set X} (hs : IsSubrack s)
    {x : X} (hx : x ∈ s) (n : Nat) :
    x ∈ principalSeries s x n ∧ IsSubrack (principalSeries s x n) := by
  induction n with
  | zero => exact ⟨hx, hs⟩
  | succ n ih =>
    exact ⟨self_mem_orbitIn ih.1, orbitIn_isSubrack ih.2 x⟩

/-- Every principal sequence really is one of the series quantified
over in the original statement: no unproved extension assumption. -/
theorem principal_isOrbitSeries {s : Set X} (hs : IsSubrack s)
    {x : X} (hx : x ∈ s) : IsOrbitSeries s (principalSeries s x) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro n
    exact (principal_mem_and_subrack hs hx n).2
  · intro n
    exact ⟨x, (principal_mem_and_subrack hs hx n).1, rfl⟩

theorem principal_antitone (s : Set X) (x : X) :
    Antitone (principalSeries s x) :=
  antitone_nat_of_succ_le fun n => orbitIn_subset (principalSeries s x n) x

/-- If the marked n-th term still contains two distinct points,
then it witnesses failure of the uniform tOS_n condition. -/
theorem not_trivializing_of_principal {x y : X} {n : Nat}
    (hy : y ∈ principalSeries Set.univ x n) (hne : y ≠ x) :
    ¬ Trivializing (X := X) n := by
  intro h
  have hx : x ∈ (Set.univ : Set X) := Set.mem_univ _
  obtain ⟨r, hr, z, hz⟩ :=
    h (principalSeries Set.univ x) (principal_isOrbitSeries univ_isSubrack hx)
  have hxr : x ∈ principalSeries Set.univ x r :=
    (principal_mem_and_subrack univ_isSubrack hx r).1
  have hyr : y ∈ principalSeries Set.univ x r :=
    principal_antitone Set.univ x hr hy
  rw [hz] at hxr hyr
  exact hne ((Set.mem_singleton_iff.mp hyr).trans
    (Set.mem_singleton_iff.mp hxr).symm)

/-- A subrack is trivial when every translation of its own points fixes them. -/
def TrivialOn (s : Set X) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, Shelf.act a b = b

/-- This proof uses Mathlib's stabilizer and closure API:
if generators fix x, the generated group fixes x. -/
theorem orbitIn_eq_singleton_of_trivial {s : Set X} {x : X}
    (hs : TrivialOn s) (hx : x ∈ s) :
    orbitIn s x = {x} := by
  have hle : translationGroup s ≤ MulAction.stabilizer (Equiv.Perm X) x := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    change Shelf.act a x = x
    exact hs a ha x hx
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy.2
    have hfix := hle g.property
    change g.val x = x at hfix
    change g.val x = y at hg
    exact Set.mem_singleton_iff.mpr (hg.symm.trans hfix)
  · intro hy
    have h := Set.mem_singleton_iff.mp hy
    subst y
    exact self_mem_orbitIn hx

/-- The sufficient direction of the tOS_2 criterion in §2 of the
manuscript: trivial inner orbits imply singleton terms at step two. -/
theorem trivializingTwo_of_trivial_orbits
    (h : ∀ x : X, TrivialOn (orbitIn Set.univ x)) :
    Trivializing (X := X) 2 := by
  intro a ha
  obtain ⟨x, hx, hfirst⟩ := ha.2.2 0
  have h1 : a 1 = orbitIn Set.univ x := by
    simpa [ha.1] using hfirst
  obtain ⟨y, hy, hsecond⟩ := ha.2.2 1
  have ht : TrivialOn (a 1) := by rw [h1]; exact h x
  exact ⟨2, le_rfl, y, hsecond.trans (orbitIn_eq_singleton_of_trivial ht hy)⟩

/-- The same hypothesis yields the LR_2 identity (§4.2). -/
theorem locallyReductiveTwo_of_trivial_orbits
    (h : ∀ x : X, TrivialOn (orbitIn Set.univ x)) :
    LocallyReductive (X := X) 2 := by
  intro a b
  have hb : b ∈ orbitIn Set.univ b := self_mem_orbitIn (Set.mem_univ b)
  let g : translationGroup (Set.univ : Set X) :=
    ⟨_root_.Rack.act' a, translation_mem (Set.mem_univ a)⟩
  have hab : Shelf.act a b ∈ orbitIn Set.univ b :=
    ⟨Set.mem_univ _, MulAction.mem_orbit b g⟩
  exact h b (Shelf.act a b) hab b hb

end QuandleResearch.BCNW
