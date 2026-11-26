import QuandleResearch.Theory.OrbitSeries

/-! Native Mathlib enveloping group. With the source's right-conjugation
convention x ▷ y = y⁻¹xy, its generators are the inverses of the
canonical Mathlib generators. Mathlib's native map and universal property
remain available as Rack.toEnvelGroup.map / univ / univ_uniq. -/
namespace QuandleResearch
noncomputable section
namespace Quandle

abbrev EnvGroup (Q : Quandle) := _root_.Rack.EnvelGroup Q.carrier
def envGen (Q : Quandle) (x : Q.carrier) : Q.EnvGroup :=
  (_root_.Rack.toEnvelGroup Q.carrier x)⁻¹
def Injective (Q : Quandle) : Prop := Function.Injective Q.envGen

end Quandle
end
end QuandleResearch
