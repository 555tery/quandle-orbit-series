import QuandleResearch.Theory.EnvelopingGroup

namespace QuandleResearch
noncomputable section
namespace Quandle

/-- Standard enveloping group presentation in the right-quandle convention:
e_(x▷y) = e_y⁻¹ e_x e_y. -/
def envelopingRels (Q : Quandle) : Set (FreeGroup Q.carrier) :=
  {r | ∃ x y : Q.carrier,
    r = FreeGroup.of (Q.op x y) *
      ((FreeGroup.of y)⁻¹ * FreeGroup.of x * FreeGroup.of y)⁻¹}
abbrev EnvGroup (Q : Quandle) := PresentedGroup Q.envelopingRels
def envGen (Q : Quandle) (x : Q.carrier) : Q.EnvGroup := PresentedGroup.of x
def Injective (Q : Quandle) : Prop := Function.Injective Q.envGen
end Quandle
end
end QuandleResearch
