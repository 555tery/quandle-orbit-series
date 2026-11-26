import QuandleResearch.Theory.Interfaces

/-!
# Issue 60: Gassner faithfulness problem for P_n, n≥4 — recorded by Bardakov–Nasybullov (2019)
https://github.com/555tery/quandle-orbit-series/issues/60

Formalization status: PARTIAL.
Remaining obligation: Construct pure braid groups and Fox derivative Gassner matrices.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov, *Multi-switches and representations of braid groups*, arXiv:1907.09230v1 (2019), J. Algebra Appl. 23 (2024), 2430003, [printed p.16, §5, formula (11)](https://arxiv.org/pdf/1907.09230v1#page=16). Verified on PDF page image. Classical question explicitly stated as unresolved, not attributed to Nasybullov.

## Target
For n>3, determine whether the Gassner representation of the classical pure braid group P_n over Z[t_1^{±1},…,t_n^{±1}] is faithful. Use the Fox-derivative construction and generator matrices of formula (11).

## Source context / scope
Do not conflate Gassner with the Burau specialization t_1=…=t_n or with its extensions to welded/virtual braid groups. Search each n and possible general reduction in later audit.
-/

namespace QuandleResearch.Issue060
noncomputable section

def question (gassner : Nat → Representation) : Prop := ∀ n, 3 < n → (gassner n).Faithful

end
end QuandleResearch.Issue060
