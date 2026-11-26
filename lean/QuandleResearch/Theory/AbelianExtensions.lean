import QuandleResearch.Theory.Groups

namespace QuandleResearch
noncomputable section
/-- An extension described by a normalized multiplicative 2-cocycle on
abelian kernel and quotient. The product is written using the source's
choice of section, with the kernel written multiplicatively. -/
structure AbelianExtensionData where
  A : Type
  B : Type
  aGroup : CommGroup A
  bGroup : CommGroup B
attribute [instance] AbelianExtensionData.aGroup AbelianExtensionData.bGroup
structure ExtensionCocycle (D : AbelianExtensionData) where
  action : D.B →* (D.A ≃* D.A)
  cocycle : D.B → D.B → D.A
  normalizedLeft : ∀ b, cocycle 1 b = 1
  normalizedRight : ∀ b, cocycle b 1 = 1
  cocycleLaw : ∀ b c d, cocycle b c * cocycle (b*c) d =
    action b (cocycle c d) * cocycle b (c*d)
namespace ExtensionCocycle
def product {D : AbelianExtensionData} (C : ExtensionCocycle D)
    (x y : D.A × D.B) : D.A × D.B :=
  (x.1 * C.action x.2 y.1 * C.cocycle x.2 y.2, x.2*y.2)
/-- Any group law on the pair type is required to coincide with the
cocycle product; this is a compatibility condition, not an assumption
that arbitrary extension data already has a proved group instance. -/
def Realizes {D : AbelianExtensionData} (C : ExtensionCocycle D)
    (law : Group (D.A × D.B)) : Prop :=
  ∀ x y, law.mul x y = C.product x y
end ExtensionCocycle
end
end QuandleResearch
