import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.GeometricLinks

/-!
# Issue 58: BNS §1 (2019) — surface knots with equal quandles and different biquandles
https://github.com/555tery/quandle-orbit-series/issues/58

Formalization status: PARTIAL.
Remaining obligation: Compact connected embedded surfaces in S4 and presentation-based algebraic invariants now available. Orientability/local flatness and the broken-surface diagram correspondence still need encoding.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, arXiv:1908.08301v1 (2019), J. Pure Appl. Algebra 226 (2022), 106936, DOI 10.1016/j.jpaa.2021.106936, [printed p.2, introduction](https://arxiv.org/pdf/1908.08301v1#page=2). Verified on PDF page image. Surface-knot part of the unnumbered question stated by the authors.

## Target
Do there exist two surface knots with isomorphic fundamental quandles but nonisomorphic fundamental biquandles? Preserve the definition of surface knots used in the original context.

## Source context / scope
The source explicitly cites Ashihara [1] for the negative answer within ribbon 2-knots or ribbon torus-knots. That is not an answer for all surface knots. Audit more general reconstruction theorems separately from the classical case.
-/

namespace QuandleResearch.Issue058
noncomputable section

def question (K : KnotInterface) : Prop :=
  ∃ x y, (K.fundamentalQ x).Iso (K.fundamentalQ y) ∧ ¬ (K.fundamentalBQ x).Iso (K.fundamentalBQ y)

/-- Sheet and semisheet relations along double curves have the same
algebraic format as the crossing relations. The two diagram maps must
be obtained from the actual broken-surface diagram of each surface. -/
def existsPresented (arc : EmbeddedSurface → ArcPresentation 1)
    (semi : EmbeddedSurface → SemiArcPresentation) : Prop :=
  ∃ (x y : EmbeddedSurface) (Q R : Quandle) (B C : StrongBiquandle)
    (qx : (arc x).Arc → Q.carrier) (qy : (arc y).Arc → R.carrier)
    (bx : (semi x).Arc → B.carrier) (by' : (semi y).Arc → C.carrier),
    (arc x).PresentsQuandle Q qx ∧ (arc y).PresentsQuandle R qy ∧
    (semi x).PresentsBiquandle B bx ∧ (semi y).PresentsBiquandle C by' ∧
    Q.Iso R ∧ ¬ B.Iso C

end
end QuandleResearch.Issue058
