import QuandleResearch.Theory.Interfaces

/-!
# Issue 58: BNS §1 (2019) — surface knots with equal quandles and different biquandles
https://github.com/555tery/quandle-orbit-series/issues/58

Formalization status: PARTIAL.
Remaining obligation: Instantiate with surface knots and actual fundamental invariants.

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

end
end QuandleResearch.Issue058
