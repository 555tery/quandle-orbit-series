import QuandleResearch.Theory.EnvelopingGroup
import QuandleResearch.Basic.Biquandle
import QuandleResearch.Theory.Braces

namespace QuandleResearch
noncomputable section
/-- Source-specific braid presentations and generator formulas remain open
formalization obligations; these interfaces require genuine group maps. -/
structure TwoProjections where
  G : GroupObject
  P : GroupObject
  H : GroupObject
  pureMap : G.carrier →* P.carrier
  otherMap : G.carrier →* H.carrier
def TwoProjections.intersection (D : TwoProjections) : Subgroup D.G.carrier :=
  D.pureMap.ker ⊓ D.otherMap.ker
structure Representation where
  source : GroupObject
  target : GroupObject
  map : source.carrier →* target.carrier
def Representation.Faithful (R : Representation) : Prop := Function.Injective R.map
structure KnotInterface where
  knot : Type
  equiv : Setoid knot
  fundamentalQ : knot → Quandle
  fundamentalBQ : knot → Biquandle
structure PartialCategoryInterface where
  admissible : PartialOperations → Prop
  morphism : (A B : PartialOperations) → (A.carrier → B.carrier) → Prop
  preserves : ∀ A B f, morphism A B f → A.WeakHom B f
  id : ∀ A, admissible A → morphism A A (fun x => x)
  comp : ∀ A B C f g, morphism A B f → morphism B C g → morphism A C (g ∘ f)
def PartialCategoryInterface.FreeOn (I : PartialCategoryInterface) (A : PartialOperations)
    {X : Type} (gen : X → A.carrier) : Prop :=
  I.admissible A ∧ ∀ B, I.admissible B → ∀ f : X → B.carrier,
    ∃! h : A.carrier → B.carrier, I.morphism A B h ∧ ∀ x, h (gen x) = f x
end
end QuandleResearch
