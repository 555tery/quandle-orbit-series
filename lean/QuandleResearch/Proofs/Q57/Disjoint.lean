import QuandleResearch.Proofs.Q57.DihedralDepth
import Mathlib.Data.Sigma.Basic

/-! The disjoint sum of the finite dihedral quandles, BCNW Example 4.2.
Cross-component translations are the identity. All carriers are native
Mathlib ZMod and Sigma types. -/
namespace QuandleResearch.Q57.Disjoint
open BCNW Issue013 DihedralDepth

abbrev Total := Σ k : Nat, D k

def sumAct (a b : Total) : Total :=
  if h : a.1 = b.1 then
    ⟨b.1, Shelf.act (h ▸ a.2) b.2⟩
  else b

@[simp] theorem sumAct_same (k : Nat) (a b : D k) :
    sumAct ⟨k,a⟩ ⟨k,b⟩ = ⟨k,Shelf.act a b⟩ := by
  simp [sumAct]

theorem sumAct_diff {i j : Nat} (h : i ≠ j) (a : D i) (b : D j) :
    sumAct ⟨i,a⟩ ⟨j,b⟩ = ⟨j,b⟩ := by
  simp [sumAct,h]

theorem sumAct_involutive (a b : Total) : sumAct a (sumAct a b) = b := by
  obtain ⟨i,a⟩ := a
  obtain ⟨j,b⟩ := b
  by_cases h : i = j
  · subst j
    simp only [sumAct_same]
    exact congrArg (Sigma.mk i) (Quandle.dihedralAct.inv (2^i) a b)
  · rw [sumAct_diff h,sumAct_diff h]

instance totalQuandle : Quandle Total where
  act := sumAct
  invAct := sumAct
  left_inv := sumAct_involutive
  right_inv := sumAct_involutive
  fix := by
    rintro ⟨k,a⟩
    simp
  self_distrib := by
    rintro ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp only [sumAct_same]
        exact congrArg (Sigma.mk i) Shelf.self_distrib
      · simp only [sumAct_same,sumAct_diff hik]
    · by_cases hjk : j = k
      · subst k
        simp only [sumAct_same,sumAct_diff hij]
      · by_cases hik : i = k
        · subst k
          simp only [sumAct_same,sumAct_diff hij,sumAct_diff hjk]
        · simp only [sumAct_diff hij,sumAct_diff hjk,sumAct_diff hik]

abbrev Base := Nat
local instance baseQuandle : Quandle Base where
  act _ y := y
  invAct _ y := y
  self_distrib := rfl
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  fix := rfl

def projection : ShelfHom Total Base where
  toFun := Sigma.fst
  map_act' := by
    rintro ⟨i,a⟩ ⟨j,b⟩
    change (sumAct ⟨i,a⟩ ⟨j,b⟩).1 = j
    by_cases h : i = j
    · subst j
      rw [sumAct_same]
    · rw [sumAct_diff h]

theorem projection_surjective : Function.Surjective projection :=
  fun k => ⟨⟨k,zero k⟩,rfl⟩

def incl (k : Nat) : ShelfHom (D k) Total where
  toFun := Sigma.mk k
  map_act' := by
    intro a b
    exact (sumAct_same k a b).symm

theorem incl_injective (k : Nat) : Function.Injective (incl k) :=
  sigma_mk_injective

theorem fibre_eq_range (k : Nat) : fibre projection k = Set.range (incl k) := by
  ext z
  constructor
  · obtain ⟨j,a⟩ := z
    intro hz
    have he : j = k := hz
    subst j
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    rfl

theorem fibre_OSomega (k : Nat) : OSomega (fibre projection k) := by
  apply OSomega_of_finite
  rw [fibre_eq_range]
  letI : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩
  letI : Finite (D k) := by
    change Finite (ZMod (2^k))
    infer_instance
  exact Set.finite_range (incl k)

theorem base_OSomega : OSomega (Set.univ : Set Base) := by
  refine ⟨1,by decide,?_⟩
  intro a ha
  have horb (s : Set Base) (x : Base) (hx : x ∈ s) :
      orbitIn s x = {x} := orbitIn_eq_singleton_of_trivial (fun _ _ _ _ => rfl) hx
  obtain ⟨x,hx,he⟩ := ha.2.2 0
  have h1 := he.trans (horb _ _ hx)
  obtain ⟨y,hy,he'⟩ := ha.2.2 1
  have hxy : y = x := by rw [h1] at hy; exact hy
  subst y
  have h2 := he'.trans (horb _ _ hy)
  exact ⟨1,le_rfl,h1.trans h2.symm⟩

/-- Every ambient walk starting in a component is a walk in that
component, with all cross-component steps deleted. -/
theorem walk_stays_in_component (k : Nat) (x : D k) {z : Total}
    (hw : StatementAudit.Walk
      ((_root_.Rack.act' : Total → Equiv.Perm Total) '' Set.univ)
      (incl k x) z) :
    ∃ y : D k, incl k y = z ∧
      StatementAudit.Walk ((_root_.Rack.act' : D k → Equiv.Perm (D k)) '' Set.univ)
        x y := by
  induction hw with
  | nil => exact ⟨x,rfl,StatementAudit.Walk.nil⟩
  | forward h hg ih =>
    obtain ⟨y,rfl,hy⟩ := ih
    obtain ⟨⟨i,a⟩,_,rfl⟩ := hg
    by_cases hi : i = k
    · subst i
      refine ⟨Shelf.act a y,?_,StatementAudit.Walk.forward (g := Rack.act' a)
        hy ⟨a,Set.mem_univ _,rfl⟩⟩
      exact (sumAct_same k a y).symm
    · refine ⟨y,?_,hy⟩
      exact (sumAct_diff hi a y).symm
  | backward h hg ih =>
    obtain ⟨y,rfl,hy⟩ := ih
    obtain ⟨⟨i,a⟩,_,rfl⟩ := hg
    by_cases hi : i = k
    · subst i
      refine ⟨Rack.invAct a y,?_,StatementAudit.Walk.backward (g := Rack.act' a)
        hy ⟨a,Set.mem_univ _,rfl⟩⟩
      exact (sumAct_same k a y).symm
    · refine ⟨y,?_,hy⟩
      exact (sumAct_diff hi a y).symm

theorem first_orbit (k : Nat) (x : D k) :
    orbitIn Set.univ (incl k x) = incl k '' orbitIn Set.univ x := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨y,he,hw⟩ := walk_stays_in_component k x
      ((StatementAudit.walk_iff_orbit _ _ _).mpr hz.2)
    exact ⟨y,⟨Set.mem_univ _,(StatementAudit.walk_iff_orbit _ _ _).mp hw⟩,he⟩
  · rw [StatementAudit.image_orbitIn (incl k) (incl_injective k)]
    exact orbitIn_mono (Set.subset_univ _) _

theorem principal_image (k : Nat) (x : D k) (n : Nat) :
    principalSeries Set.univ (incl k x) (n+1) =
      incl k '' principalSeries Set.univ x (n+1) := by
  induction n with
  | zero => exact first_orbit k x
  | succ n ih =>
    change orbitIn (principalSeries Set.univ (incl k x) (n+1)) (incl k x) =
      incl k '' orbitIn (principalSeries Set.univ x (n+1)) x
    rw [ih,StatementAudit.image_orbitIn (incl k) (incl_injective k)]

theorem total_not_OSomega : ¬ OSomega (Set.univ : Set Total) := by
  rintro ⟨n,hn,hb⟩
  let k := n+1
  have he := stable_of_OSBound univ_isSubrack hb (Set.mem_univ (incl k (zero k)))
  change principalSeries Set.univ (incl k (zero k)) n =
    principalSeries Set.univ (incl k (zero k)) (n+1) at he
  have hn' : n = (n-1)+1 := by omega
  have hl := principal_image k (zero k) (n-1)
  rw [← hn'] at hl
  rw [hl,principal_image] at he
  exact DihedralDepth.not_stable n
    (StatementAudit.eq_of_image_eq (incl k) (incl_injective k) he)

theorem negative_small : ¬ extensionOSomega.{0,0} := by
  intro h
  letI : Nonempty Total := ⟨⟨0,zero 0⟩⟩
  exact total_not_OSomega (h Total Base projection projection_surjective base_OSomega fibre_OSomega)

#print axioms negative_small
end QuandleResearch.Q57.Disjoint
