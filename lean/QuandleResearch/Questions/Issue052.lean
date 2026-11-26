import QuandleResearch.Theory.Interfaces

/-!
# Issue 52: Smoktunowicz–Vendramin conjecture / Kourovka 19.90 — finite skew braces with solvable additive group
https://github.com/555tery/quandle-orbit-series/issues/52

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated problem
Gorshkov–Nasybullov, *Finite skew braces with solvable additive group*, [arXiv:2006.00466v1, pp.1–2](https://arxiv.org/pdf/2006.00466v1#page=1); Li–Nasybullov–Zadvornov, *Comparison of addition and multiplication in a skew brace*, [arXiv:2511.22322v1, p.2](https://arxiv.org/pdf/2511.22322v1#page=2), listed problem 4. Conjecture expressly attributed to Smoktunowicz and Vendramin, not Nasybullov. Same problem in both papers: register once.

## Target
Prove or disprove: for every finite skew brace A, solvability of (A,+) implies solvability of (A,∘). Equivalently, decide existence of a finite counterexample.

## Source context
Gorshkov–Nasybullov Theorem 3.1 restricts the minimal counterexample, Corollary 2.2 handles 3∤|A|; Li–Nasybullov–Zadvornov Theorem 5.2 handles cyclic additive derived subgroup. The infinite counterexample discussed in both papers does not settle the finite conjecture. These are source context, not a new current-status audit.
-/

namespace QuandleResearch.Issue052
noncomputable section

def question : Prop := ∀ B : SkewBrace, Finite B.carrier → B.solvableAdd → B.solvableMul

end
end QuandleResearch.Issue052
