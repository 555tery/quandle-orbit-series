import QuandleResearch.Questions.Issue013

/-! Isolated comparator signature module for Question 5.7.
The expected signatures and concrete definitions are frozen separately
from the audit proofs. No proof module imports this file. No challenge
axiom is permitted in the submitted audit. This verifies statement
infrastructure, not either answer to the research question. -/
namespace QuandleResearch.Q57.StatementAudit
open BCNW Issue013
universe u v

private axiom expected_os_expanded {X : Type u} [_root_.Quandle X] (s : Set X) :
    OS s ↔ ∀ a : Nat → Set X, IsOrbitSeries s a →
      ∃ k : Nat, a k = a (k+1)

theorem os_expanded {X : Type u} [_root_.Quandle X] (s : Set X) :
    OS s ↔ ∀ a : Nat → Set X, IsOrbitSeries s a →
      ∃ k : Nat, a k = a (k+1) := expected_os_expanded s

private axiom expected_osomega_expanded {X : Type u} [_root_.Quandle X] (s : Set X) :
    OSomega s ↔ ∃ n : Nat, 0 < n ∧
      ∀ a : Nat → Set X, IsOrbitSeries s a →
        ∃ k : Nat, k ≤ n ∧ a k = a (k+1)

theorem osomega_expanded {X : Type u} [_root_.Quandle X] (s : Set X) :
    OSomega s ↔ ∃ n : Nat, 0 < n ∧
      ∀ a : Nat → Set X, IsOrbitSeries s a →
        ∃ k : Nat, k ≤ n ∧ a k = a (k+1) := expected_osomega_expanded s

private axiom expected_orbitSeries_expanded {X : Type u} [_root_.Quandle X] (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔
      a 0 = s ∧ (∀ n, IsSubrack (a n)) ∧
        ∀ n, ∃ x ∈ a n,
          a (n+1) = a n ∩ MulAction.orbit
            (Subgroup.closure ((_root_.Rack.act' : X → Equiv.Perm X) '' a n)) x

theorem orbitSeries_expanded {X : Type u} [_root_.Quandle X] (s : Set X) (a : Nat → Set X) :
    IsOrbitSeries s a ↔
      a 0 = s ∧ (∀ n, IsSubrack (a n)) ∧
        ∀ n, ∃ x ∈ a n,
          a (n+1) = a n ∩ MulAction.orbit
            (Subgroup.closure ((_root_.Rack.act' : X → Equiv.Perm X) '' a n)) x := expected_orbitSeries_expanded s a

private axiom expected_extensionOS_expanded : extensionOS.{u,v} ↔
    ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
      [Nonempty X] [Nonempty Y] (f : ShelfHom X Y),
      Function.Surjective f →
      (∀ a : Nat → Set Y, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ b : Y, ∀ a : Nat → Set X, IsOrbitSeries {x : X | f x = b} a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ a : Nat → Set X, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1))

theorem extensionOS_expanded : extensionOS.{u,v} ↔
    ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
      [Nonempty X] [Nonempty Y] (f : ShelfHom X Y),
      Function.Surjective f →
      (∀ a : Nat → Set Y, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ b : Y, ∀ a : Nat → Set X, IsOrbitSeries {x : X | f x = b} a →
        ∃ k : Nat, a k = a (k+1)) →
      (∀ a : Nat → Set X, IsOrbitSeries Set.univ a →
        ∃ k : Nat, a k = a (k+1)) := expected_extensionOS_expanded

private axiom expected_extensionOSomega_expanded : extensionOSomega.{u,v} ↔
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
          ∃ k : Nat, k ≤ l ∧ a k = a (k+1))

theorem extensionOSomega_expanded : extensionOSomega.{u,v} ↔
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
          ∃ k : Nat, k ≤ l ∧ a k = a (k+1)) := expected_extensionOSomega_expanded

private axiom expected_fibre_isSubrack {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (b : Y) : IsSubrack (fibre f b)

theorem fibre_isSubrack {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (b : Y) : IsSubrack (fibre f b) := expected_fibre_isSubrack f b

private axiom expected_fibre_nonempty {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (hf : Function.Surjective f) (b : Y) :
    (fibre f b).Nonempty

theorem fibre_nonempty {X : Type u} {Y : Type v}
    [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (hf : Function.Surjective f) (b : Y) :
    (fibre f b).Nonempty := expected_fibre_nonempty f hf b

section OrbitSemantics
variable {A : Type*}

inductive Walk (S : Set (Equiv.Perm A)) (a : A) : A → Prop
  | nil : Walk S a a
  | forward {z : A} (h : Walk S a z) {g : Equiv.Perm A}
      (hg : g ∈ S) : Walk S a (g z)
  | backward {z : A} (h : Walk S a z) {g : Equiv.Perm A}
      (hg : g ∈ S) : Walk S a (g.symm z)

private axiom expected_walk_iff_orbit (S : Set (Equiv.Perm A)) (a z : A) :
    Walk S a z ↔ z ∈ MulAction.orbit (Subgroup.closure S) a

theorem walk_iff_orbit (S : Set (Equiv.Perm A)) (a z : A) :
    Walk S a z ↔ z ∈ MulAction.orbit (Subgroup.closure S) a := expected_walk_iff_orbit S a z

variable {X : Type u} [_root_.Quandle X]

def restrictedTranslation {s : Set X} (hs : IsSubrack s) (y : s) :
    Equiv.Perm s where
  toFun x := ⟨Shelf.act y.val x.val, (hs y.val y.property x.val x.property).1⟩
  invFun x := ⟨(_root_.Rack.act' y.val).symm x.val,
    (hs y.val y.property x.val x.property).2⟩
  left_inv x := Subtype.ext ((_root_.Rack.act' y.val).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((_root_.Rack.act' y.val).apply_symm_apply x.val)

def intrinsicGenerators {s : Set X} (hs : IsSubrack s) :
    Set (Equiv.Perm s) := Set.range (restrictedTranslation hs)

private axiom expected_orbitIn_eq_intrinsic_image {s : Set X} (hs : IsSubrack s) (x : s) :
    orbitIn s x.val = Subtype.val ''
      MulAction.orbit (Subgroup.closure (intrinsicGenerators hs)) x

theorem orbitIn_eq_intrinsic_image {s : Set X} (hs : IsSubrack s) (x : s) :
    orbitIn s x.val = Subtype.val ''
      MulAction.orbit (Subgroup.closure (intrinsicGenerators hs)) x := expected_orbitIn_eq_intrinsic_image hs x

end OrbitSemantics

section CongruenceSemantics
variable {X : Type u} [_root_.Quandle X]

structure QuandleCongruence (X : Type u) [_root_.Quandle X] extends Setoid X where
  act_compat : ∀ {a b x y : X}, r a b → r x y →
    r (Shelf.act a x) (Shelf.act b y)
  inv_compat : ∀ {a b x y : X}, r a b → r x y →
    r (Rack.invAct a x) (Rack.invAct b y)

namespace QuandleCongruence

variable (c : QuandleCongruence X)

private axiom expected_source_inverse_condition {a b x y z w : X}
    (hab : c.r a b) (hzw : c.r z w)
    (hx : Shelf.act a x = z) (hy : Shelf.act b y = w) :
    c.r x y

theorem source_inverse_condition {a b x y z w : X}
    (hab : c.r a b) (hzw : c.r z w)
    (hx : Shelf.act a x = z) (hy : Shelf.act b y = w) :
    c.r x y := expected_source_inverse_condition c hab hzw hx hy

abbrev Carrier := Quotient c.toSetoid

def classMk (x : X) : c.Carrier := Quotient.mk c.toSetoid x

def quotientAct (a b : c.Carrier) : c.Carrier :=
  Quotient.liftOn₂ a b (fun x y => c.classMk (Shelf.act x y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.act_compat hx hy))

def quotientInv (a b : c.Carrier) : c.Carrier :=
  Quotient.liftOn₂ a b (fun x y => c.classMk (Rack.invAct x y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.inv_compat hx hy))

/-- Genuine quotient by the given setoid, not an assumed homomorphic image. -/
instance quotientQuandle : _root_.Quandle c.Carrier where
  act := c.quotientAct
  invAct := c.quotientInv
  self_distrib := by
    intro a b d
    refine Quotient.inductionOn₃ a b d ?_
    intro x y z
    change c.classMk (Shelf.act x (Shelf.act y z)) =
      c.classMk (Shelf.act (Shelf.act x y) (Shelf.act x z))
    rw [Shelf.self_distrib]
  left_inv := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change c.classMk (Rack.invAct x (Shelf.act x y)) = c.classMk y
    rw [Rack.invAct_act_eq]
  right_inv := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    change c.classMk (Shelf.act x (Rack.invAct x y)) = c.classMk y
    rw [Rack.act_invAct_eq]
  fix := by
    intro a
    refine Quotient.inductionOn a ?_
    intro x
    change c.classMk (Shelf.act x x) = c.classMk x
    rw [_root_.Quandle.fix]

def projection : ShelfHom X c.Carrier where
  toFun := c.classMk
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
  change c.classMk z = c.classMk x ↔ c.r z x
  exact ⟨Quotient.exact, Quotient.sound⟩

end QuandleCongruence
end CongruenceSemantics

section SourceFormulation
open QuandleCongruence

def congruenceOS : Prop :=
  ∀ (X : Type u) [_root_.Quandle X] [Nonempty X] (c : QuandleCongruence X),
    OS (Set.univ : Set c.Carrier) → (∀ x : X, OS (c.classOf x)) →
      OS (Set.univ : Set X)

/-- Literal congruence formulation of §2.2, for the second class. -/
def congruenceOSomega : Prop :=
  ∀ (X : Type u) [_root_.Quandle X] [Nonempty X] (c : QuandleCongruence X),
    OSomega (Set.univ : Set c.Carrier) → (∀ x : X, OSomega (c.classOf x)) →
      OSomega (Set.univ : Set X)

private axiom expected_extensionOS_iff_congruenceOS :
    extensionOS.{u,u} ↔ congruenceOS.{u}

theorem extensionOS_iff_congruenceOS :
    extensionOS.{u,u} ↔ congruenceOS.{u} := expected_extensionOS_iff_congruenceOS

private axiom expected_extensionOSomega_iff_congruenceOSomega :
    extensionOSomega.{u,u} ↔ congruenceOSomega.{u}

theorem extensionOSomega_iff_congruenceOSomega :
    extensionOSomega.{u,u} ↔ congruenceOSomega.{u} := expected_extensionOSomega_iff_congruenceOSomega

private axiom expected_extensionOS_of_congruenceOS
    (h : congruenceOS.{u}) : extensionOS.{u,v}

theorem extensionOS_of_congruenceOS
    (h : congruenceOS.{u}) : extensionOS.{u,v} := expected_extensionOS_of_congruenceOS h

private axiom expected_extensionOSomega_of_congruenceOSomega
    (h : congruenceOSomega.{u}) : extensionOSomega.{u,v}

theorem extensionOSomega_of_congruenceOSomega
    (h : congruenceOSomega.{u}) : extensionOSomega.{u,v} := expected_extensionOSomega_of_congruenceOSomega h

end SourceFormulation
end QuandleResearch.Q57.StatementAudit
