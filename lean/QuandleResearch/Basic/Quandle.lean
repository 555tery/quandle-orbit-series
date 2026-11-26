import Mathlib

namespace QuandleResearch

/-- Right convention: x ▷ y = right y x. -/
structure Rack where
  carrier : Type
  right : carrier → Equiv.Perm carrier
  selfDistrib : ∀ x y z, right z (right y x) = right (right z y) (right z x)

structure Quandle where
  rack : Rack
  idem : ∀ x, rack.right x x = x

namespace Rack
def op (R : Rack) (x y : R.carrier) := R.right y x
def Hom (R S : Rack) (f : R.carrier → S.carrier) : Prop :=
  ∀ x y, f (R.op x y) = S.op (f x) (f y)
def IsSubrack (R : Rack) (s : Set R.carrier) : Prop :=
  ∀ y ∈ s, ∀ x ∈ s, R.right y x ∈ s ∧ (R.right y).symm x ∈ s
end Rack

namespace Quandle
abbrev carrier (Q : Quandle) := Q.rack.carrier
def op (Q : Quandle) := Q.rack.op
def Hom (Q R : Quandle) (f : Q.carrier → R.carrier) : Prop := Q.rack.Hom R.rack f
def Iso (Q R : Quandle) : Prop := ∃ e : Q.carrier ≃ R.carrier, Q.Hom R e
def Aut (Q : Quandle) (e : Equiv.Perm Q.carrier) : Prop := Q.Hom Q e
def Trivial (Q : Quandle) : Prop := ∀ x y, Q.op x y = x
def Involutory (Q : Quandle) : Prop := ∀ x y, Q.op (Q.op x y) y = x
def FreeOn (Q : Quandle) {X : Type} (gen : X → Q.carrier) : Prop :=
  ∀ (R : Quandle) (f : X → R.carrier),
    ∃! h : Q.carrier → R.carrier, Q.Hom R h ∧ ∀ x, h (gen x) = f x
def IsFree (Q : Quandle) : Prop := ∃ (X : Type) (gen : X → Q.carrier), Q.FreeOn gen
def DoublyTransitive (Q : Quandle) : Prop :=
  ∀ a b c d : Q.carrier, a ≠ b → c ≠ d →
    ∃ e : Equiv.Perm Q.carrier, Q.Aut e ∧ e a = c ∧ e b = d
end Quandle
end QuandleResearch
