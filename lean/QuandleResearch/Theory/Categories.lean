import QuandleResearch.Basic.Biquandle
import Mathlib.CategoryTheory.Adjunction.Basic

/-! Native Mathlib categories on the bundled quandle objects and on the
BNS biquandles. Category and functor laws below verify the definitions,
not solutions to the research questions. -/
namespace QuandleResearch
open CategoryTheory

instance quandleCategory : Category.{0} Quandle where
  Hom Q R := Q.HomType R
  id Q := ShelfHom.id Q.carrier
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

namespace Biquandle
def HomType (B C : Biquandle) :=
  {f : B.associated.HomType C.associated //
    ∀ x y, f (B.beta y x) = C.beta (f y) (f x)}

def idHom (B : Biquandle) : B.HomType B :=
  ⟨ShelfHom.id B.carrier, by intros; rfl⟩

def compHom {A B C : Biquandle} (f : A.HomType B) (g : B.HomType C) : A.HomType C :=
  ⟨g.val.comp f.val, by
    intro x y
    change g.val (f.val (A.beta y x)) = C.beta (g.val (f.val y)) (g.val (f.val x))
    rw [f.property x y, g.property]⟩
end Biquandle

instance biquandleCategory : Category.{0} Biquandle where
  Hom := Biquandle.HomType
  id := Biquandle.idHom
  comp := Biquandle.compHom
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- The trivial family of automorphisms is the BNS quandle embedding. -/
def embedded (Q : Quandle) : Biquandle where
  associated := Q
  beta := fun _ => Equiv.refl Q.carrier
  betaAut := by
    intro y
    exact ⟨ShelfHom.id Q.carrier, rfl⟩
  compatibility := by intros; rfl
  diagonal := Function.bijective_id

/-- B : Qnd → Bqnd. -/
def quandleEmbedding : Quandle ⥤ Biquandle where
  obj := embedded
  map f := ⟨f, by intros; rfl⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Q : Bqnd → Qnd. -/
def associatedFunctor : Biquandle ⥤ Quandle where
  obj B := B.associated
  map f := f.val
  map_id := by intros; rfl
  map_comp := by intros; rfl

end QuandleResearch
