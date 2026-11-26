import QuandleResearch.Theory.Interfaces

/-!
# Issue 66: Fenn–Ilyutko–Kauffman–Manturov Problem 28C (2014) — existence of free partial biquandles
https://github.com/555tery/quandle-orbit-series/issues/66

Formalization status: PARTIAL.
Remaining obligation: Establish author's partial-biquandle category, admissibility, morphisms and generator scope.

Source and target from the issue:
## Source / explicitly stated problem
R. Fenn, D. P. Ilyutko, L. H. Kauffman, V. O. Manturov, *Unsolved problems in virtual knot theory and combinatorial knot theory*, Banach Center Publications 103 (2014), 9–61, §8.1, Problem 28, printed p. 34. [Journal PDF, p.34](https://www.impan.pl/shop/en/publication/transaction/download/product/86155#page=26), [DOI](https://doi.org/10.4064/bc103-0-1), [arXiv v1, p.31](https://arxiv.org/pdf/1409.2823v1#page=31). Journal and preprint page images verified. The letters A/B/C are local tracking labels, not original numbering.

Original third question asks whether free partial biquandles exist; the authors suggest a negative answer.

## Target
Determine whether the free partial biquandle exists on a given set of generators, in the intended meaning of 'partial biquandle' in the 2014 paper. The precise category, admissible domains of operations, morphisms, and universal property must be established from the authors' definitions and earlier works before giving a yes/no answer.
-/

namespace QuandleResearch.Issue066
noncomputable section

def question (I : PartialCategoryInterface) : Prop :=
  ∀ X : Type, ∃ (A : PartialOperations) (gen : X → A.carrier), I.FreeOn A gen

end
end QuandleResearch.Issue066
