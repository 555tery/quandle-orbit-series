import QuandleResearch.Theory.OrbitSeriesCore
import Mathlib

/-! Mathlib-first: these bundles store a carrier and the native Mathlib
typeclass. No rack or quandle axioms are duplicated. The source's
right convention x ▷ y is Mathlib's Shelf.act y x. -/
namespace QuandleResearch

structure Rack where
  carrier : Type
  law : _root_.Rack carrier

attribute [instance] Rack.law

structure Quandle where
  carrier : Type
  law : _root_.Quandle carrier

attribute [instance] Quandle.law

namespace Rack
abbrev right (R : Rack) (y : R.carrier) : Equiv.Perm R.carrier :=
  _root_.Rack.act' y
abbrev op (R : Rack) (x y : R.carrier) : R.carrier := Shelf.act y x
abbrev HomType (R S : Rack) := ShelfHom R.carrier S.carrier
def Hom (R S : Rack) (f : R.carrier → S.carrier) : Prop :=
  ∃ h : R.HomType S, (h : R.carrier → S.carrier) = f
abbrev IsSubrack (R : Rack) (s : Set R.carrier) : Prop := BCNW.IsSubrack s
end Rack

namespace Quandle
abbrev rack (Q : Quandle) : Rack := ⟨Q.carrier, Q.law.toRack⟩
abbrev op (Q : Quandle) := Q.rack.op
abbrev HomType (Q R : Quandle) := ShelfHom Q.carrier R.carrier
def Hom (Q R : Quandle) (f : Q.carrier → R.carrier) : Prop :=
  ∃ h : Q.HomType R, (h : Q.carrier → R.carrier) = f
def Iso (Q R : Quandle) : Prop := ∃ e : Q.carrier ≃ R.carrier, Q.Hom R e
def Aut (Q : Quandle) (e : Equiv.Perm Q.carrier) : Prop := Q.Hom Q e
def Trivial (Q : Quandle) : Prop := ∀ x y, Q.op x y = x
abbrev Involutory (Q : Quandle) : Prop := _root_.Rack.IsInvolutory Q.carrier
def FreeOn (Q : Quandle) {X : Type} (gen : X → Q.carrier) : Prop :=
  ∀ (R : Quandle) (f : X → R.carrier),
    ∃! h : Q.HomType R, ∀ x, h (gen x) = f x
def IsFree (Q : Quandle) : Prop := ∃ (X : Type) (gen : X → Q.carrier), Q.FreeOn gen
def DoublyTransitive (Q : Quandle) : Prop :=
  ∀ a b c d : Q.carrier, a ≠ b → c ≠ d →
    ∃ e : Equiv.Perm Q.carrier, Q.Aut e ∧ e a = c ∧ e b = d
end Quandle
end QuandleResearch
