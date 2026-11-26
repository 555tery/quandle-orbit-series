import QuandleResearch.Theory.Interfaces

/-!
# Issue 57: BNS §1 (2019) — classical knots with equal quandles and different biquandles
https://github.com/555tery/quandle-orbit-series/issues/57

Formalization status: PARTIAL.
Remaining obligation: Instantiate with classical knots and actual fundamental invariants.

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

end
end QuandleResearch.Issue057
