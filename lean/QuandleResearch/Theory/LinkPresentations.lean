import QuandleResearch.Basic.StrongBiquandle
import QuandleResearch.Theory.ReducedQuandles

/-! Algebraic presentation data from oriented link diagrams. These are
the crossing relations, not a formalization of planar realizability,
Reidemeister moves, or embeddings of surfaces. A geometric layer must
supply actual diagrams and their equivalence. -/
namespace QuandleResearch
noncomputable section

/-- At a crossing the two under-arcs are ordered so that the relation
is source ▷ over = target, irrespective of crossing sign.
The sign is used in the cocycle weight. -/
structure ArcPresentation (n : Nat) where
  arcCount : Nat
  crossingCount : Nat
  component : Fin arcCount → Fin n
  underSource : Fin crossingCount → Fin arcCount
  underTarget : Fin crossingCount → Fin arcCount
  overArc : Fin crossingCount → Fin arcCount
  positive : Fin crossingCount → Bool
  sameUnderComponent : ∀ c, component (underSource c) = component (underTarget c)

namespace ArcPresentation
abbrev Arc {n : Nat} (D : ArcPresentation n) := Fin D.arcCount
abbrev Crossing {n : Nat} (D : ArcPresentation n) := Fin D.crossingCount

def IsColoring {n : Nat} (D : ArcPresentation n) (Q : Quandle)
    (f : D.Arc → Q.carrier) : Prop :=
  ∀ c : D.Crossing, Q.op (f (D.underSource c)) (f (D.overArc c)) = f (D.underTarget c)

abbrev Coloring {n : Nat} (D : ArcPresentation n) (Q : Quandle) :=
  {f : D.Arc → Q.carrier // D.IsColoring Q f}

/-- The presented quandle represents the functor of all arc colorings. -/
def PresentsQuandle {n : Nat} (D : ArcPresentation n) (Q : Quandle)
    (gen : D.Arc → Q.carrier) : Prop :=
  D.IsColoring Q gen ∧ ∀ (R : Quandle) (f : D.Coloring R),
    ∃! h : Q.HomType R, ∀ a, h (gen a) = f.val a

/-- The reduced fundamental quandle represents colorings in reduced
targets; the ordinary presentation and the quotient can also be
specified separately with Quandle.IsReducedQuotient. -/
def PresentsReduced {n : Nat} (D : ArcPresentation n) (Q : Quandle)
    (gen : D.Arc → Q.carrier) : Prop :=
  Q.Reduced ∧ D.IsColoring Q gen ∧
    ∀ (R : Quandle), R.Reduced → ∀ f : D.Coloring R,
      ∃! h : Q.HomType R, ∀ a, h (gen a) = f.val a

end ArcPresentation

inductive CrossingKind
  | positive | negative | virtual
  deriving DecidableEq

/-- Four labels at each crossing, in the switch convention. Virtual
crossings apply the twist. The geometric diagram is an external input. -/
structure SemiArcPresentation where
  arcCount : Nat
  crossingCount : Nat
  inLeft : Fin crossingCount → Fin arcCount
  inRight : Fin crossingCount → Fin arcCount
  outLeft : Fin crossingCount → Fin arcCount
  outRight : Fin crossingCount → Fin arcCount
  kind : Fin crossingCount → CrossingKind

namespace SemiArcPresentation
abbrev Arc (D : SemiArcPresentation) := Fin D.arcCount
abbrev Crossing (D : SemiArcPresentation) := Fin D.crossingCount

def crossingMap {X : Type} (D : SemiArcPresentation)
    (S V : Equiv.Perm (X × X)) (c : D.Crossing) : X × X → X × X :=
  match D.kind c with
  | .positive => S
  | .negative => S.symm
  | .virtual => V

def IsColoring {X : Type} (D : SemiArcPresentation)
    (S V : Equiv.Perm (X × X)) (f : D.Arc → X) : Prop :=
  ∀ c : D.Crossing,
    D.crossingMap S V c (f (D.inLeft c), f (D.inRight c)) =
      (f (D.outLeft c), f (D.outRight c))

abbrev Coloring (D : SemiArcPresentation) (B : StrongBiquandle) :=
  {f : D.Arc → B.carrier // D.IsColoring B.switch (Equiv.prodComm B.carrier B.carrier) f}

def PresentsBiquandle (D : SemiArcPresentation) (B : StrongBiquandle)
    (gen : D.Arc → B.carrier) : Prop :=
  D.IsColoring B.switch (Equiv.prodComm B.carrier B.carrier) gen ∧
    ∀ (C : StrongBiquandle) (f : D.Coloring C),
      ∃! h : B.carrier → C.carrier, B.Hom C h ∧ ∀ a, h (gen a) = f.val a
end SemiArcPresentation
end
end QuandleResearch
