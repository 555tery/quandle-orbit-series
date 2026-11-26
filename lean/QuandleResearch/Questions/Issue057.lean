import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.LinkPresentations

/-!
# Issue 57: BNS §1 (2019) — classical knots with equal quandles and different biquandles
https://github.com/555tery/quandle-orbit-series/issues/57

Formalization status: PARTIAL.
Remaining obligation: Fundamental quandle and strong biquandle specified by actual crossing relations; classical realizability and geometric domain remain external.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, arXiv:1908.08301v1 (2019), J. Pure Appl. Algebra 226 (2022), 106936, DOI 10.1016/j.jpaa.2021.106936, [printed p.2, introduction](https://arxiv.org/pdf/1908.08301v1#page=2). Verified on PDF page image. Classical-knot part of the unnumbered question stated by the authors.

## Target
Do there exist two classical knots with isomorphic fundamental quandles but nonisomorphic fundamental biquandles? Use the knot orientation/mirror conventions appropriate to the source.

## Source context / scope
Audit results about the associated quandle of a fundamental biquandle, and Ishikawa's knot quandle/biquandle correspondence. The separate surface-knot part is tracked in its own issue.
-/

namespace QuandleResearch.Issue057
noncomputable section

def question (K : KnotInterface) : Prop :=
  ∃ x y, (K.fundamentalQ x).Iso (K.fundamentalQ y) ∧ ¬ (K.fundamentalBQ x).Iso (K.fundamentalBQ y)

/-- The geometric domain must consist of classical knots with actual
diagram presentations; the algebraic invariants are no longer arbitrary. -/
def existsPresented {Knot : Type} (arc : Knot → ArcPresentation 1)
    (semi : Knot → SemiArcPresentation) : Prop :=
  ∃ (x y : Knot) (Q R : Quandle) (B C : StrongBiquandle)
    (qx : (arc x).Arc → Q.carrier) (qy : (arc y).Arc → R.carrier)
    (bx : (semi x).Arc → B.carrier) (by' : (semi y).Arc → C.carrier),
    (arc x).PresentsQuandle Q qx ∧ (arc y).PresentsQuandle R qy ∧
    (semi x).PresentsBiquandle B bx ∧ (semi y).PresentsBiquandle C by' ∧
    Q.Iso R ∧ ¬ B.Iso C

end
end QuandleResearch.Issue057
