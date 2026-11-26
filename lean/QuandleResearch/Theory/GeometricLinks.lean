import QuandleResearch.Theory.LinkPresentations
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Ordered parametrized links in S³, using native metric spheres,
continuous maps and homotopies. The link-homotopy condition below forbids
intersections between distinct components but allows self-intersections.
Inoue, Problems on Low-dimensional Topology (2013), §2, p.5 uses ambient
isotopies and self-crossing changes; the correspondence to this continuous
model requires the usual tame/smooth category restriction and is not
proved here. -/
namespace QuandleResearch
noncomputable section

abbrev Sphere (d : Nat) :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1)
abbrev Disk :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)

def circleBoundary (x : Sphere 1) : Disk :=
  ⟨x.val, Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp x.property))⟩

structure GeometricLink (n : Nat) where
  curve : ContinuousMap (Fin n × Sphere 1) (Sphere 3)
  injective : Function.Injective curve

namespace GeometricLink

/-- The usual continuous description of link-homotopy. Component labels
and parametrizations are retained. No equality of invariants is assumed. -/
def LinkHomotopic {n : Nat} (L M : GeometricLink n) : Prop :=
  ∃ H : ContinuousMap.Homotopy L.curve M.curve,
    ∀ (t : unitInterval) (i j : Fin n) (x y : Sphere 1),
      i ≠ j → H (t,(i,x)) ≠ H (t,(j,y))

/-- Pairwise disjoint embedded spanning disks for the selected sublink.
This is the geometric unlink criterion in the tame category. -/
def UnlinkOn {n : Nat} (L : GeometricLink n) (s : Set (Fin n)) : Prop :=
  ∃ disks : Fin n → ContinuousMap Disk (Sphere 3),
    (∀ i ∈ s, Function.Injective (disks i) ∧
      ∀ x : Sphere 1, disks i (circleBoundary x) = L.curve (i,x)) ∧
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Set.range (disks i)) (Set.range (disks j))

def Unlink {n : Nat} (L : GeometricLink n) : Prop := L.UnlinkOn Set.univ

def Brunnian {n : Nat} (L : GeometricLink n) : Prop :=
  ¬ L.Unlink ∧ ∀ i : Fin n, L.UnlinkOn ({i}ᶜ)

end GeometricLink

/-- Compact connected topological surface embedded in S⁴. The
orientation/local-flatness requirements of the smooth surface-knot
category must be added when using this geometric input. -/
structure EmbeddedSurface where
  carrier : Type
  topology : TopologicalSpace carrier
  compact : letI := topology; CompactSpace carrier
  hausdorff : letI := topology; T2Space carrier
  connected : letI := topology; ConnectedSpace carrier
  charts : letI := topology; ChartedSpace (EuclideanSpace ℝ (Fin 2)) carrier
  map : letI := topology; ContinuousMap carrier (Sphere 4)
  injective : Function.Injective map

end
end QuandleResearch
