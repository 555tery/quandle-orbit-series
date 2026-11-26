import QuandleResearch.Theory.OrbitSeries

namespace QuandleResearch
noncomputable section
/-- Universal-property specification of the enveloping group.
No existence theorem or concrete quotient construction is asserted here. -/
structure Enveloping (Q : Quandle) where
  G : GroupObject
  gen : Q.carrier → G.carrier
  relation : ∀ x y, gen (Q.op x y) = (gen y)⁻¹ * gen x * gen y
  universal : ∀ (H : GroupObject) (f : Q.carrier → H.carrier),
    (∀ x y, f (Q.op x y) = (f y)⁻¹ * f x * f y) →
      ∃! h : G.carrier →* H.carrier, ∀ x, h (gen x) = f x
def Enveloping.InjectiveQuandle {Q : Quandle} (E : Enveloping Q) : Prop :=
  Function.Injective E.gen
end
end QuandleResearch
