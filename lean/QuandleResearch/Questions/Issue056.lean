import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.LinkPresentations

/-!
# Issue 56: Fenn–Jordan-Santana–Kauffman conjecture — completeness of fundamental virtual knot biquandle
https://github.com/555tery/quandle-orbit-series/issues/56

Formalization status: PARTIAL.
Remaining obligation: Fundamental strong biquandle specified by actual crossing relations; geometric virtual knot equivalence and source scope remain.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, arXiv:1908.08301v1 (2019), J. Pure Appl. Algebra 226 (2022), 106936, DOI 10.1016/j.jpaa.2021.106936, [printed p.2, introduction](https://arxiv.org/pdf/1908.08301v1#page=2). The authors explicitly recall the unresolved conjecture of their reference [23], *Biquandles and virtual links* (2004); verified on PDF page image.

## Target
Determine in what precise equivalence sense the fundamental biquandle is a complete invariant of virtual knots, or give a counterexample. The BNS source uses qualified wording about completeness; verify the original [23] formulation and conventions before treating any example as a solution.

## Source context / scope
Do not confuse the fundamental biquandle with counts of colorings by finite biquandles or completeness of the classical knot quandle. Original conjecture is not attributed to Nasybullov.
-/

namespace QuandleResearch.Issue056
noncomputable section

def question (K : KnotInterface) : Prop :=
  ∀ x y, (K.fundamentalBQ x).Iso (K.fundamentalBQ y) ↔ K.equiv.r x y

/-- Fundamental objects are now required to present the specified
crossing relations. The geometric equivalence convention is not yet
fixed by this module. -/
def completePresented {Knot : Type} (diagram : Knot → SemiArcPresentation)
    (equiv : Setoid Knot) : Prop :=
  ∀ (x y : Knot) (B C : StrongBiquandle)
    (gx : (diagram x).Arc → B.carrier) (gy : (diagram y).Arc → C.carrier),
    (diagram x).PresentsBiquandle B gx → (diagram y).PresentsBiquandle C gy →
      (B.Iso C ↔ equiv.r x y)

end
end QuandleResearch.Issue056
