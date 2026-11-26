import QuandleResearch.Basic.Quandle

namespace QuandleResearch
/-- BNS quandle-automorphism convention, not an asserted equivalence theorem
with the strong-switch convention used in older sources. -/
structure Biquandle where
  associated : Quandle
  beta : associated.carrier → Equiv.Perm associated.carrier
  betaAut : ∀ y, associated.Aut (beta y)
  compatibility : ∀ x y z,
    beta (beta y (associated.op x y)) (beta y z) = beta (beta x y) (beta x z)
  diagonal : Function.Bijective (fun y => beta y y)

namespace Biquandle
abbrev carrier (B : Biquandle) := B.associated.carrier
def under (B : Biquandle) (x y : B.carrier) := B.beta y (B.associated.op x y)
def over (B : Biquandle) (x y : B.carrier) := B.beta y x
def Hom (B C : Biquandle) (f : B.carrier → C.carrier) : Prop :=
  B.associated.Hom C.associated f ∧ ∀ x y, f (B.beta y x) = C.beta (f y) (f x)
def Iso (B C : Biquandle) : Prop := ∃ e : B.carrier ≃ C.carrier, B.Hom C e
def Rigid (B : Biquandle) : Prop := ∀ e : Equiv.Perm B.carrier, B.Hom B e → e = 1
def FreeOn (B : Biquandle) {X : Type} (gen : X → B.carrier) : Prop :=
  ∀ (C : Biquandle) (f : X → C.carrier),
    ∃! h : B.carrier → C.carrier, B.Hom C h ∧ ∀ x, h (gen x) = f x
end Biquandle

def ValidTrivialFamily {A : Type} (beta : A → Equiv.Perm A) : Prop :=
  Function.Bijective (fun y => beta y y) ∧
    ∀ x y z, beta (beta y x) (beta y z) = beta (beta x y) (beta x z)
def IsoTrivialFamily {A : Type} (beta gamma : A → Equiv.Perm A) : Prop :=
  ∃ e : Equiv.Perm A, ∀ x y, e (beta y x) = gamma (e y) (e x)

/-- Raw partial operations. Source-specific admissibility and morphisms are
not yet fixed; see Issue066. -/
structure PartialOperations where
  carrier : Type
  under : carrier → carrier → Option carrier
  over : carrier → carrier → Option carrier
namespace PartialOperations
def WeakHom (A B : PartialOperations) (f : A.carrier → B.carrier) : Prop :=
  (∀ x y z, A.under x y = some z → B.under (f x) (f y) = some (f z)) ∧
  (∀ x y z, A.over x y = some z → B.over (f x) (f y) = some (f z))
end PartialOperations
end QuandleResearch
