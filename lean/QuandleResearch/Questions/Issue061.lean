import QuandleResearch.Theory.Interfaces

/-!
# Issue 61: Kourovka 19.7(b) — linearity of pure virtual braid groups VP_n, n≥4
https://github.com/555tery/quandle-orbit-series/issues/61

Formalization status: PARTIAL.
Remaining obligation: Construct VP_n and verify field scope.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov, *Multi-switches and representations of braid groups*, arXiv:1907.09230v1 (2019), J. Algebra Appl. 23 (2024), 2430003, [printed p.17, §5, immediately after Proposition 5](https://arxiv.org/pdf/1907.09230v1#page=17). Verified on PDF page image. Original problem cited by the authors as Kourovka Notebook 19.7(b).

## Target
Determine whether VP_n is linear for n≥4 (admits a faithful finite-dimensional representation over a field). Equivalently, study linearity of VB_n, using VP_n of finite index. Retain the quantification over n and check field conventions in the original Kourovka entry.

## Source context / scope
Proposition 5 of the source proves linearity of VB_3 only. Nonfaithfulness of specific representations does not imply nonlinearity. Distinct from #27 (minimum faithful dimension of VP_3) and #29–30 (specific representations).
-/

namespace QuandleResearch.Issue061
noncomputable section

def question (VP : Nat → GroupObject) : Prop := ∀ n, 4 ≤ n → Linear (VP n).carrier

end
end QuandleResearch.Issue061
