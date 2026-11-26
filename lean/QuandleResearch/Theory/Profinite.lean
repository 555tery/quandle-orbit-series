import QuandleResearch.Theory.OrbitSeries
import Mathlib.Topology.Category.Profinite.Basic

/-! Byard–Cai–Jones–Vuong–Yetter, arXiv:2406.15387v2,
Definitions 3.1–3.5 and 3.16. Stone topology alone is not profiniteness.
The Stone-indexed union below is a proposed precise interpretation of the
research direction in §6, not a definition supplied by the authors. -/
namespace QuandleResearch
noncomputable section

structure TopologicalQuandle where
  Q : Quandle
  topology : TopologicalSpace Q.carrier
  continuousOp : letI := topology
                 Continuous (fun p : Q.carrier × Q.carrier => Q.op p.1 p.2)
  continuousInv : letI := topology
                  Continuous (fun p : Q.carrier × Q.carrier => (Q.rack.right p.2).symm p.1)

attribute [instance] TopologicalQuandle.topology

structure InverseSystem where
  index : Type
  order : PartialOrder index
  nonempty : Nonempty index
  directed : letI := order
             ∀ i j : index, ∃ k, i ≤ k ∧ j ≤ k
  obj : index → Quandle
  finiteObj : ∀ i, Finite (obj i).carrier
  transition : letI := order
               ∀ i j : index, i ≤ j → (obj j).carrier → (obj i).carrier
  mapHom : letI := order
           ∀ i j (h : i ≤ j), (obj j).Hom (obj i) (transition i j h)
  mapId : letI := order
          ∀ i, transition i i le_rfl = id
  mapComp : letI := order
            ∀ i j k (h : i ≤ j) (h' : j ≤ k),
              transition i k (le_trans h h') = transition i j h ∘ transition j k h'

attribute [instance] InverseSystem.order

namespace InverseSystem
def Coherent (D : InverseSystem) (x : ∀ i, (D.obj i).carrier) : Prop :=
  ∀ i j (h : i ≤ j), x i = D.transition i j h (x j)
abbrev Limit (D : InverseSystem) := {x : ∀ i, (D.obj i).carrier // D.Coherent x}
/-- The underlying bijection, coordinate homomorphisms and initial topology
specify the inverse limit without postulating an arbitrary predicate. -/
def IsLimit (D : InverseSystem) (T : TopologicalQuandle) : Prop :=
  ∃ e : T.Q.carrier ≃ D.Limit,
    (∀ i, T.Q.Hom (D.obj i) (fun x => (e x).val i)) ∧
    T.topology = ⨅ i : D.index,
      TopologicalSpace.induced (fun x : T.Q.carrier => (e x).val i)
        (⊥ : TopologicalSpace (D.obj i).carrier)
end InverseSystem

def Profinite (T : TopologicalQuandle) : Prop :=
  ∃ D : InverseSystem, D.IsLimit T

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
      Profinite T → T.Q.Connected → Constructible T
  | stoneUnion (T : TopologicalQuandle) (I : StoneIndex)
      (F : I → TopologicalQuandle) :
      Profinite T → StoneUnion T I F →
      (∀ i, Constructible (F i)) → Constructible T

end
end QuandleResearch
