import QuandleResearch.Theory.Interfaces

/-!
# Issue 49: Bardakov–Nasybullov–Singh Question 6.4 (2017) — finite quandles with doubly transitive automorphism group
https://github.com/555tery/quandle-orbit-series/issues/49

Formalization status: PARTIAL.
Remaining obligation: Independent structural classification required.

Source and target from the issue:
## Source / explicitly formulated problem
Bardakov, Nasybullov, Singh, *Automorphism groups of quandles and related groups*, [arXiv:1705.10607v3, p.12](https://arxiv.org/pdf/1705.10607v3#page=12), Monatsh. Math. 189 (2019), 1–21. Explicit Question 6.4, verified on the page image.

## Target
Classify finite quandles Q such that Aut(Q) acts 2-transitively on Q. Include trivial quandles and the authors' convention for degrees exceeding |Q|; distinguish Aut(Q) from Inn(Q).

## Source context
Theorem 6.2 handles 3-transitivity; Question 6.4 is the remaining case. This was missed in the earlier scan of the same paper (#20). Search two-transitive/primitive permutation groups, affine quandles and classifications of doubly transitive racks in the separate answer audit.
-/

namespace QuandleResearch.Issue049
noncomputable section

def verifiesClassification (answer : Quandle → Prop) : Prop :=
  ∀ Q, Finite Q.carrier → (answer Q ↔ Q.DoublyTransitive)

end
end QuandleResearch.Issue049
