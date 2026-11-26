import QuandleResearch.Theory.Interfaces

/-!
# Issue 51: Kourovka 19.90 — nilpotent multiplicative group and nonsolvable additive group (infinite skew braces)
https://github.com/555tery/quandle-orbit-series/issues/51

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated problem
Li, Nasybullov, Zadvornov, *Comparison of addition and multiplication in a skew brace*, [arXiv:2511.22322v1, pp.1–2](https://arxiv.org/pdf/2511.22322v1#page=1), listed problem 1; also Gorshkov–Nasybullov [arXiv:2006.00466v1, §1](https://arxiv.org/abs/2006.00466). Original question attributed to Kourovka Notebook Problem 19.90, not to the authors of these papers. Wording checked on page images.

## Target
Does a skew brace A exist with nilpotent multiplicative group (A,∘) and nonsolvable additive group (A,+)? No finiteness or two-sided assumption.

## Source context
The source distinguishes finite case (its problem 2, stated as already solved) from the general case. Known two-sided bounds are described on p.2. Do not close the general question based solely on finite or two-sided cases.
-/

namespace QuandleResearch.Issue051
noncomputable section

def question : Prop := ∃ B : SkewBrace, B.nilpotentMul ∧ ¬ B.solvableAdd

end
end QuandleResearch.Issue051
