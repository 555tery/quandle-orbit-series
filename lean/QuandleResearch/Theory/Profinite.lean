import QuandleResearch.Basic.Quandle
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
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

/-- Native finite-type diagram with additional quandle structures. -/
structure FiniteQuandleDiagram (J : Type) [PartialOrder J] where
  diagram : Jᵒᵖ ⥤ FintypeCat
  law : ∀ i : Jᵒᵖ, _root_.Quandle (diagram.obj i)
  mapAct : ∀ (i j : Jᵒᵖ) (f : i ⟶ j),
    letI := law i
    letI := law j
    ∀ x y : diagram.obj i,
      diagram.map f (Shelf.act x y) = Shelf.act (diagram.map f x) (diagram.map f y)

namespace FiniteQuandleDiagram

def SurjectiveMaps {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J) : Prop :=
  ∀ (i j : Jᵒᵖ) (f : i ⟶ j), Function.Surjective (D.diagram.map f)

/-- Use the library's finite discrete spaces and their native limit cone. -/
abbrev stoneDiagram {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J) :=
  D.diagram ⋙ FintypeCat.toProfinite

noncomputable def stoneLimit {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J) :=
  _root_.Profinite.limitCone D.stoneDiagram

/-- Native limit topology, and the coordinatewise operation of Proposition 3.4. -/
def IsLimit {J : Type} [PartialOrder J] (D : FiniteQuandleDiagram J)
    (T : TopologicalQuandle) : Prop :=
  ∃ e : T.Q.carrier ≃ₜ D.stoneLimit.pt,
    ∀ i : Jᵒᵖ,
      letI := D.law i
      ∀ x y : T.Q.carrier,
        let pi : D.stoneLimit.pt → D.diagram.obj i :=
          fun z => D.stoneLimit.π.app i z
        pi (e (T.Q.op x y)) =
          @Shelf.act (D.diagram.obj i) (D.law i).toRack.toShelf
            (pi (e y)) (pi (e x))

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

/-- The actual profinite completion of the abstract inner group, not
the diagram-dependent inverse limit of finite inner groups (Definition
4.1). Mathlib already provides the completion and canonical dense map. -/
abbrev completedInn (T : TopologicalQuandle) :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of T.Q.Inn)

/-- The action from Proposition 4.5, specified by extending the
canonical action on the dense image of Inn(Q). Ordinary left actions
are used instead of the source's right-action notation.
The action is not required to be faithful after completion. -/
def IsCompletedInnerAction (T : TopologicalQuandle)
    (rho : completedInn T →* Equiv.Perm T.Q.carrier) : Prop :=
  (∀ (g : T.Q.Inn) (x : T.Q.carrier),
    rho (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of T.Q.Inn) g) x = g.val x) ∧
  Continuous (fun p : completedInn T × T.Q.carrier => rho p.1 p.2)

/-- Definition 5.1: profinitely algebraically connected. In §6 the
authors expressly use "algebraically connected" in this sense, NOT
transitivity of the abstract Inn(Q), and not connectedness of the
underlying topological space. -/
def ProfinitelyConnected (T : TopologicalQuandle) : Prop :=
  Nonempty T.Q.carrier ∧
    ∃ rho : completedInn T →* Equiv.Perm T.Q.carrier,
      IsCompletedInnerAction T rho ∧
      ∀ x y : T.Q.carrier, ∃ g : completedInn T, rho g x = y

/-- Useful equivalent characterization to be verified separately
using Proposition 4.5 and density of the canonical map. It is not used
as an unproved axiom in the statement of the problem. -/
def DenseInnerOrbits (T : TopologicalQuandle) : Prop :=
  Nonempty T.Q.carrier ∧ ∀ x : T.Q.carrier,
    Dense (MulAction.orbit T.Q.Inn x)

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

/-- Generalization of the finite mesh of Ehrman–Gurpinar–Thibault–Yetter,
Definition 3.3 and Theorem 3.2. We use the Mathlib augmentation
generator (not its inverse): its action is the source's right
translation, with ordinary composition of permutations.
The compatibility law is the full right self-distributivity equation
on all triples, avoiding special cases for repeated indices. -/
structure StoneMesh (I : StoneIndex) (F : I → TopologicalQuandle) where
  action : ∀ i j : I, _root_.Rack.EnvelGroup (F j).Q.carrier →*
    Equiv.Perm (F i).Q.carrier
  automorphism : ∀ i j (g : _root_.Rack.EnvelGroup (F j).Q.carrier),
    (F i).Q.Aut (action i j g)
  diagonal : ∀ i (y : (F i).Q.carrier),
    action i i (_root_.Rack.toEnvelGroup (F i).Q.carrier y) = (F i).Q.rack.right y
  compatible : ∀ i j k (x : (F i).Q.carrier) (y : (F j).Q.carrier)
      (z : (F k).Q.carrier),
    let a := fun (u v : I) (w : (F v).Q.carrier) =>
      action u v (_root_.Rack.toEnvelGroup (F v).Q.carrier w)
    a i k z (a i j y x) = a i j (a j k z y) (a i k z x)

namespace StoneMesh
def op {I : StoneIndex} {F : I → TopologicalQuandle} (M : StoneMesh I F)
    (x y : Σ i : I, (F i).Q.carrier) : Σ i : I, (F i).Q.carrier :=
  ⟨x.1, M.action x.1 y.1
    (_root_.Rack.toEnvelGroup (F y.1).Q.carrier y.2) x.2⟩

def invOp {I : StoneIndex} {F : I → TopologicalQuandle} (M : StoneMesh I F)
    (x y : Σ i : I, (F i).Q.carrier) : Σ i : I, (F i).Q.carrier :=
  ⟨x.1, (M.action x.1 y.1
    (_root_.Rack.toEnvelGroup (F y.1).Q.carrier y.2)).symm x.2⟩
end StoneMesh

/-- Candidate Stone-indexed assembly. The total-space topology is data,
NOT the disjoint-sum topology; this distinction is necessary for the
Cantor-quandle example. The operation and inverse operation come from
the mesh, not from an arbitrary predicate on a pre-existing quandle.
The homeomorphism verifies that this assembly realizes T. -/
structure StoneAssembly (T : TopologicalQuandle) (I : StoneIndex)
    (F : I → TopologicalQuandle) where
  pieceProfinite : ∀ i, Profinite (F i)
  pieceNonempty : ∀ i, Nonempty (F i).Q.carrier
  mesh : StoneMesh I F
  topology : TopologicalSpace (Σ i : I, (F i).Q.carrier)
  projectionContinuous : letI := topology
                         Continuous (fun x : Σ i : I, (F i).Q.carrier => x.1)
  fiberTopology : ∀ i, (F i).topology =
    TopologicalSpace.induced (fun x : (F i).Q.carrier => (⟨i, x⟩ : Σ j : I, (F j).Q.carrier))
      topology
  continuousOp : letI := topology
                 Continuous (fun p : (Σ i : I, (F i).Q.carrier) ×
                   (Σ i : I, (F i).Q.carrier) => mesh.op p.1 p.2)
  continuousInv : letI := topology
                  Continuous (fun p : (Σ i : I, (F i).Q.carrier) ×
                    (Σ i : I, (F i).Q.carrier) => mesh.invOp p.1 p.2)
  identify : letI := topology; T.Q.carrier ≃ₜ (Σ i : I, (F i).Q.carrier)
  preserves : ∀ x y : T.Q.carrier,
    identify (T.Q.op x y) = mesh.op (identify x) (identify y)

/-- Bottom-up closure under the explicit mesh assembly. This is a
well-founded assembly-tree interpretation, distinct from the ordinal
partition formulation below. Neither is claimed equivalent to the
open-ended source question. -/
inductive Constructible : TopologicalQuandle → Prop
  | connected (T : TopologicalQuandle) :
      Profinite T → ProfinitelyConnected T → Constructible T
  | stoneUnion (T : TopologicalQuandle) (I : StoneIndex)
      (F : I → TopologicalQuandle) :
      Profinite T → StoneAssembly T I F →
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
are profinitely algebraically connected in the exact sense of Definition 5.1.

Each successor has explicit mesh and total-space topology data. Limit
stages are expressed as intersections of partitions, not a prescribed
bottom-up limit constructor. This remains a candidate interpretation. -/
structure TransfiniteDecomposition (T : TopologicalQuandle) where
  height : Ordinal.{0}
  partition : Ordinal.{0} → Setoid T.Q.carrier
  root : ∀ x y, (partition 0).r x y
  refines : ∀ a b, a ≤ b → b ≤ height →
    ∀ x y, (partition b).r x y → (partition a).r x y
  cell : ∀ a, a ≤ height → ∀ x : T.Q.carrier,
    ProfinitePiece T {y | (partition a).r x y}
  successor : ∀ (a : Ordinal.{0}) (ha : a ≤ height) (hs : a+1 ≤ height),
    ∀ (x : T.Q.carrier),
    let C := cell a ha x
    ∃ (I : StoneIndex) (F : I → TopologicalQuandle)
      (A : StoneAssembly C.piece I F),
      (∀ u v : C.piece.Q.carrier,
        (A.identify u).1 = (A.identify v).1 ↔
          (partition (a+1)).r (C.incl u) (C.incl v)) ∧
      ∀ u : C.piece.Q.carrier,
        let i := (A.identify u).1
        let child := cell (a+1) hs (C.incl u)
        ∃ e : (F i).Q.carrier ≃ₜ child.piece.Q.carrier,
          (∀ v w, e ((F i).Q.op v w) = child.piece.Q.op (e v) (e w)) ∧
          ∀ v, child.incl (e v) =
            C.incl (A.identify.symm ⟨i,v⟩)
  limitStage : ∀ a, a ≤ height → a ≠ 0 →
    (∀ b < a, b+1 < a) →
    ∀ x y, (partition a).r x y ↔ ∀ b < a, (partition b).r x y
  terminal : ∀ x : T.Q.carrier, ProfinitelyConnected (cell height le_rfl x).piece

end
end QuandleResearch
