import QuandleResearch.Theory.Interfaces

/-!
# Issue 59: Burau faithfulness problem for B_4 — recorded by Bardakov–Nasybullov (2019)
https://github.com/555tery/quandle-orbit-series/issues/59

Formalization status: PARTIAL.
Remaining obligation: Construct B_4 and the unreduced Burau matrices over Laurent polynomials.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov, *Multi-switches and representations of braid groups*, arXiv:1907.09230v1 (2019), J. Algebra Appl. 23 (2024), 2430003, [printed p.16, §5](https://arxiv.org/pdf/1907.09230v1#page=16). Verified on PDF page image. Classical problem expressly described as open in the text, not originally posed by Nasybullov.

## Target
Determine whether the Burau representation of the classical braid group B_4 is faithful. In the source the unreduced representation sends σ_i to I_{i−1}⊕[[1−t,t],[1,0]]⊕I_{n−i−1} over Z[t,t^{-1}].

## Source context / scope
Distinguish faithful over the Laurent polynomial ring from specialized representations; compare reduced/unreduced conventions. The paper notes faithfulness for n=2,3 and nonfaithfulness for n≥5. Current status to be audited separately.
-/

namespace QuandleResearch.Issue059
noncomputable section

def question (burau : Representation) : Prop := burau.Faithful

end
end QuandleResearch.Issue059
