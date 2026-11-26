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


/-! An independent finite-walk semantics for generated permutation orbits.
This is definition infrastructure, not a proof of either extension answer. -/
section OrbitSemantics

variable {A : Type*}

/-- Finite sequences of generators and inverse generators. -/
inductive Walk (S : Set (Equiv.Perm A)) (a : A) : A → Prop
  | nil : Walk S a a
  | forward {z : A} (h : Walk S a z) {g : Equiv.Perm A}
      (hg : g ∈ S) : Walk S a (g z)
  | backward {z : A} (h : Walk S a z) {g : Equiv.Perm A}
      (hg : g ∈ S) : Walk S a (g.symm z)

theorem walk_iff_orbit (S : Set (Equiv.Perm A)) (a z : A) :
    Walk S a z ↔ z ∈ MulAction.orbit (Subgroup.closure S) a := by
  constructor
  · intro h
    induction h with
    | nil => exact MulAction.mem_orbit_self _
    | forward h hg ih =>
      let g' : Subgroup.closure S := ⟨_, Subgroup.subset_closure hg⟩
      exact MulAction.mem_orbit_of_mem_orbit g' ih
    | backward h hg ih =>
      let g' : Subgroup.closure S := ⟨_, Subgroup.subset_closure hg⟩
      exact MulAction.mem_orbit_of_mem_orbit g'⁻¹ ih
  · intro hz
    let H : Subgroup (Equiv.Perm A) :=
      { carrier := {g | ∀ t : A, Walk S a t ↔ Walk S a (g t)}
        one_mem' := by intro t; rfl
        mul_mem' := by
          intro g h hg hh t
          exact (hh t).trans (hg (h t))
        inv_mem' := by
          intro g hg t
          change Walk S a t ↔ Walk S a (g.symm t)
          simpa only [Equiv.apply_symm_apply] using (hg (g.symm t)).symm }
    have hS : S ⊆ H := by
      intro g hg t
      constructor
      · intro ht
        exact Walk.forward ht hg
      · intro ht
        have h := Walk.backward ht hg
        simpa only [Equiv.symm_apply_apply] using h
    have hH : Subgroup.closure S ≤ H := (Subgroup.closure_le H).mpr hS
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hz
    change g.val a = z at hg
    have hp : ∀ t : A, Walk S a t ↔ Walk S a (g.val t) :=
      hH g.property
    rw [← hg]
    exact (hp a).mp Walk.nil

variable {X : Type u} [_root_.Quandle X]

/-- The actual left translation of the subtype s, with actual inverse.
This does not assume that the ambient and intrinsic inner groups coincide. -/
def restrictedTranslation {s : Set X} (hs : IsSubrack s) (y : s) :
    Equiv.Perm s where
  toFun x := ⟨Shelf.act y.val x.val, (hs y.val y.property x.val x.property).1⟩
  invFun x := ⟨(_root_.Rack.act' y.val).symm x.val,
    (hs y.val y.property x.val x.property).2⟩
  left_inv x := Subtype.ext ((_root_.Rack.act' y.val).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((_root_.Rack.act' y.val).apply_symm_apply x.val)

def intrinsicGenerators {s : Set X} (hs : IsSubrack s) :
    Set (Equiv.Perm s) := Set.range (restrictedTranslation hs)

/-- Lift an ambient walk to the subtype, tracking membership at every step. -/
theorem lift_walk {s : Set X} (hs : IsSubrack s) (x : s) {z : X}
    (h : Walk ((_root_.Rack.act' : X → Equiv.Perm X) '' s) x.val z) :
    ∃ hz : z ∈ s, Walk (intrinsicGenerators hs) x (⟨z, hz⟩ : s) := by
  induction h with
  | nil => exact ⟨x.property, Walk.nil⟩
  | forward h hg ih =>
    obtain ⟨hz, hw⟩ := ih
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨(hs y hy _ hz).1,
      Walk.forward hw ⟨(⟨y, hy⟩ : s), rfl⟩⟩
  | backward h hg ih =>
    obtain ⟨hz, hw⟩ := ih
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨(hs y hy _ hz).2,
      Walk.backward hw ⟨(⟨y, hy⟩ : s), rfl⟩⟩

/-- Forgetting the subtype turns an intrinsic walk into an ambient walk. -/
theorem forget_walk {s : Set X} (hs : IsSubrack s) (x z : s)
    (h : Walk (intrinsicGenerators hs) x z) :
    Walk ((_root_.Rack.act' : X → Equiv.Perm X) '' s) x.val z.val := by
  induction h with
  | nil => exact Walk.nil
  | forward h hg ih =>
    obtain ⟨y, rfl⟩ := hg
    exact Walk.forward ih ⟨y.val, y.property, rfl⟩
  | backward h hg ih =>
    obtain ⟨y, rfl⟩ := hg
    exact Walk.backward ih ⟨y.val, y.property, rfl⟩

/-- The BCNW ambient orbit is precisely the image of the intrinsic orbit
on the subtype. No faithfulness of the restriction homomorphism is needed. -/
theorem orbitIn_eq_intrinsic_image {s : Set X} (hs : IsSubrack s) (x : s) :
    orbitIn s x.val = Subtype.val ''
      MulAction.orbit (Subgroup.closure (intrinsicGenerators hs)) x := by
  ext z
  constructor
  · intro hz
    have hw := (walk_iff_orbit _ _ _).mpr hz.2
    obtain ⟨hz', hw'⟩ := lift_walk hs x hw
    exact ⟨⟨z, hz'⟩, (walk_iff_orbit _ _ _).mp hw', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hw := (walk_iff_orbit _ _ _).mpr hy
    exact ⟨y.property, (walk_iff_orbit _ _ _).mp (forget_walk hs x y hw)⟩

end OrbitSemantics


section CongruenceSemantics

variable {X : Type u} [_root_.Quandle X]

/-- The source's §2.2 equivalence relation respecting both operations. -/
structure QuandleCongruence (X : Type u) [_root_.Quandle X] extends Setoid X where
  act_compat : ∀ {a b x y : X}, r a b → r x y →
    r (Shelf.act a x) (Shelf.act b y)
  inv_compat : ∀ {a b x y : X}, r a b → r x y →
    r (Rack.invAct a x) (Rack.invAct b y)

namespace QuandleCongruence

variable (c : QuandleCongruence X)

/-- The implicit inverse compatibility condition in BCNW §2.2. -/
theorem source_inverse_condition {a b x y z w : X}
    (hab : c.r a b) (hzw : c.r z w)
    (hx : Shelf.act a x = z) (hy : Shelf.act b y = w) :
    c.r x y := by
  have h := c.inv_compat hab hzw
  rw [← hx, ← hy] at h
  simpa only [Rack.invAct_act_eq] using h

abbrev Carrier := Quotient c.toSetoid

def mk (x : X) : c.Carrier := Quotient.mk c.toSetoid x

def quotientAct (a b : c.Carrier) : c.Carrier :=
  Quotient.liftOn₂ a b (fun x y => c.mk (Shelf.act x y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.act_compat hx hy))

def quotientInv (a b : c.Carrier) : c.Carrier :=
  Quotient.liftOn₂ a b (fun x y => c.mk (Rack.invAct x y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.inv_compat hx hy))

/-- Genuine quotient by the given setoid, not an assumed homomorphic image. -/
instance quotientQuandle : _root_.Quandle c.Carrier where
  act := c.quotientAct
  invAct := c.quotientInv
  self_distrib := by
    intro a b d
    refine Quotient.inductionOn₃ a b d ?_
    intro x y z
    change c.mk (Shelf.act x (Shelf.act y z)) =
      c.mk (Shelf.act (Shelf.act x y) (Shelf.act x z))
    rw [Shelf.self_distrib]
  left_inv := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change c.mk (Rack.invAct x (Shelf.act x y)) = c.mk y
    rw [Rack.invAct_act_eq]
  right_inv := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change c.mk (Shelf.act x (Rack.invAct x y)) = c.mk y
    rw [Rack.act_invAct_eq]
  fix := by
    intro a
    refine Quotient.inductionOn a ?_
    intro x
    change c.mk (Shelf.act x x) = c.mk x
    rw [_root_.Quandle.fix]

def projection : ShelfHom X c.Carrier where
  toFun := c.mk
  map_act' := rfl

theorem projection_surjective : Function.Surjective c.projection := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

def classOf (x : X) : Set X := {z | c.r z x}

theorem fibre_projection (x : X) :
    fibre c.projection (c.projection x) = c.classOf x := by
  ext z
  change c.mk z = c.mk x ↔ c.r z x
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- The kernel is a congruence, including inverse-operation compatibility. -/
def kernel {Y : Type v} [_root_.Quandle Y] (f : ShelfHom X Y) :
    QuandleCongruence X where
  r x y := f x = f y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  act_compat := by
    intro a b x y hab hxy
    change f (Shelf.act a x) = f (Shelf.act b y)
    rw [f.map_act, f.map_act, hab, hxy]
  inv_compat := by
    intro a b x y hab hxy
    change f (Rack.invAct a x) = f (Rack.invAct b y)
    rw [map_invAct, map_invAct, hab, hxy]

/-- The homomorphism induced from the actual kernel quotient. -/
def factor {Y : Type v} [_root_.Quandle Y] (f : ShelfHom X Y) :
    ShelfHom (kernel f).Carrier Y where
  toFun := Quotient.lift f (fun _ _ h => h)
  map_act' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact f.map_act

theorem factor_injective {Y : Type v} [_root_.Quandle Y] (f : ShelfHom X Y) :
    Function.Injective (factor f) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  exact Quotient.sound h

theorem factor_surjective {Y : Type v} [_root_.Quandle Y]
    (f : ShelfHom X Y) (hf : Function.Surjective f) :
    Function.Surjective (factor f) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  exact ⟨(kernel f).mk x, hx⟩

theorem kernel_class_fibre {Y : Type v} [_root_.Quandle Y]
    (f : ShelfHom X Y) (x : X) :
    (kernel f).classOf x = fibre f (f x) := rfl

end QuandleCongruence
end CongruenceSemantics

end QuandleResearch.Q57.StatementAudit
