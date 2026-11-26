import QuandleResearch.Theory.OrbitSeries
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.SetTheory.Ordinal.Basic

/-! Byard–Cai–Jones–Vuong–Yetter, arXiv:2406.15387v2,
Definitions 3.1–3.5 and 3.16. Stone topology alone is not profiniteness.
The Stone-indexed union below is a proposed precise interpretation of the
research direction in §6, not a definition supplied by the authors. -/
namespace QuandleResearch
open CategoryTheory
noncomputable section

structure TopologicalQuandle where
  Q : Quandle
  topology : TopologicalSpace Q.carrier
  continuousOp : letI := topology
                 Continuous (fun p : Q.carrier × Q.carrier => Q.op p.1 p.2)
  continuousInv : letI := topology
                  Continuous (fun p : Q.carrier × Q.carrier => (Q.rack.right p.2).symm p.1)

attribute [instance] TopologicalQuandle.topology

/-- A finite inverse system, indexed by a directed poset.
The underlying diagram is a native Mathlib functor, so identity and
composition laws do not need to be repeated. The additional data are
exactly the finite quandle laws and preservation of those laws.
Surjectivity is optional in Definition 3.5 and is assumed later in
Remark 3.8 of the source. -/
structure FiniteQuandleDiagram (J : Type) [PartialOrder J] where
  diagram : Jᵒᵖ ⥤ Type
  law : ∀ i : Jᵒᵖ, _root_.Quandle (diagram.obj i)
  finiteObj : ∀ i, Finite (diagram.obj i)
  mapAct : ∀ (i j : Jᵒᵖ) (f : i ⟶ j),
    letI := law i
    letI := law j
    ∀ x y : diagram.obj i,
      diagram.map f (Shelf.act x y) = Shelf.act (diagram.map f x) (diagram.map f y)

namespace FiniteQuandleDiagram

def SurjectiveMaps {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J) : Prop :=
  ∀ (i j : Jᵒᵖ) (f : i ⟶ j), Function.Surjective (D.diagram.map f)

/-- Mathlib's compatible sections are the concrete underlying
set of the categorical inverse limit (Types.limitEquivSections).
The quandle operation is coordinatewise, and the topology is the
initial topology of the coordinate maps to discrete finite factors.
No assertion that every Stone topological quandle is profinite is made. -/
def IsLimit {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J)
    (T : TopologicalQuandle) : Prop :=
  ∃ e : T.Q.carrier ≃ D.diagram.sections,
    (∀ i : Jᵒᵖ,
      letI := D.law i
      ∀ x y : T.Q.carrier,
        (e (T.Q.op x y)).val i = Shelf.act ((e y).val i) ((e x).val i)) ∧
    T.topology = ⨅ i : Jᵒᵖ,
      TopologicalSpace.induced (fun x : T.Q.carrier => (e x).val i)
        (⊥ : TopologicalSpace (D.diagram.obj i))

end FiniteQuandleDiagram

/-- Definition 3.5, with the canonical topology from §3.2. -/
def Profinite (T : TopologicalQuandle) : Prop :=
  ∃ (J : Type) (_ : PartialOrder J),
    Nonempty J ∧ IsDirected J (· ≤ ·) ∧
    ∃ D : FiniteQuandleDiagram J, D.IsLimit T

/-- Same definition with the additional surjectivity convention of
Remark 3.8; equivalence is not postulated as an axiom. -/
def ProfiniteSurjective (T : TopologicalQuandle) : Prop :=
  ∃ (J : Type) (_ : PartialOrder J),
    Nonempty J ∧ IsDirected J (· ≤ ·) ∧
    ∃ D : FiniteQuandleDiagram J, D.SurjectiveMaps ∧ D.IsLimit T

/-- A Stone space is Mathlib's native profinite topological space.
This is only the indexing space, not the definition of a profinite quandle. -/
abbrev StoneIndex := _root_.Profinite.{0}

/-- A proposed Stone-indexed semi-disjoint union: a continuous projection
whose fibres carry the given topological quandle structures. Right
translations preserve each fibre. No sufficiency theorem is asserted. -/
structure StoneUnion (T : TopologicalQuandle) (I : StoneIndex)
    (F : I → TopologicalQuandle) where
  proj : T.Q.carrier → I
  continuousProj : Continuous proj
  surjectiveProj : Function.Surjective proj
  preservesIndex : ∀ x y, proj (T.Q.op x y) = proj x
  incl : ∀ i, (F i).Q.carrier → T.Q.carrier
  inclHom : ∀ i, (F i).Q.Hom T.Q (incl i)
  inclInjective : ∀ i, Function.Injective (incl i)
  imageFiber : ∀ i, Set.range (incl i) = {x | proj x = i}
  fiberTopology : ∀ i, (F i).topology = TopologicalSpace.induced (incl i) T.topology

/-- Closure under the proposed constructor, starting with algebraically
connected profinite quandles. Well-founded constructor trees encode
iterated unions; this is one candidate formulation of the transfinite
construction, not a claim that §6 specified a unique operation. -/
inductive Constructible : TopologicalQuandle → Prop
  | connected (T : TopologicalQuandle) :
      Profinite T → Nonempty T.Q.carrier → T.Q.Connected → Constructible T
  | stoneUnion (T : TopologicalQuandle) (I : StoneIndex)
      (F : I → TopologicalQuandle) :
      Profinite T → StoneUnion T I F →
      (∀ i, Constructible (F i)) → Constructible T

/-- A profinite piece of the ambient quandle, identified with an actual
subset by a homomorphism and the subspace topology. -/
structure ProfinitePiece (T : TopologicalQuandle) (s : Set T.Q.carrier) where
  piece : TopologicalQuandle
  profinite : Profinite piece
  incl : piece.Q.HomType T.Q
  injective : Function.Injective incl
  image : Set.range incl = s
  inducedTopology : piece.topology =
    TopologicalSpace.induced (fun x : piece.Q.carrier => incl x) T.topology

/-- Candidate meaning of a transfinite Stone-indexed semi-disjoint
decomposition, read top-down. The author does not specify this
definition in §6. At each successor, the cells of the next partition
inside a parent are exactly fibres of a continuous map to a Stone
space, and right translations by points in the parent preserve fibres.
At limits, the partition is the intersection of the earlier partitions.
Each cell has the structure of a profinite subquandle; terminal cells
are algebraically connected, not just topologically connected.

The operations on the parent are retained as part of each piece.
Thus this is a precise candidate decomposition problem, not yet a
complete prescription for constructing all interaction maps bottom-up. -/
structure TransfiniteDecomposition (T : TopologicalQuandle) where
  height : Ordinal.{0}
  partition : Ordinal.{0} → Setoid T.Q.carrier
  root : ∀ x y, (partition 0).r x y
  refines : ∀ a b, a ≤ b → b ≤ height →
    ∀ x y, (partition b).r x y → (partition a).r x y
  cell : ∀ a, a ≤ height → ∀ x : T.Q.carrier,
    ProfinitePiece T {y | (partition a).r x y}
  successor : ∀ (a : Ordinal.{0}) (ha : a ≤ height), a+1 ≤ height →
    ∀ (x : T.Q.carrier),
    let C := cell a ha x
    ∃ (I : StoneIndex) (proj : ContinuousMap C.piece.Q.carrier I),
      Function.Surjective proj ∧
      (∀ u v, proj (C.piece.Q.op u v) = proj u) ∧
      (∀ u v, proj u = proj v ↔
        (partition (a+1)).r (C.incl u) (C.incl v))
  limitStage : ∀ a, a ≤ height → a ≠ 0 →
    (∀ b < a, b+1 < a) →
    ∀ x y, (partition a).r x y ↔ ∀ b < a, (partition b).r x y
  terminal : ∀ x : T.Q.carrier, (cell height le_rfl x).piece.Q.Connected

end
end QuandleResearch
