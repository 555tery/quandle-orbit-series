import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 59: Burau faithfulness problem for B_4 — recorded by Bardakov–Nasybullov (2019)
https://github.com/555tery/quandle-orbit-series/issues/59

Formalization status: PARTIAL.
Remaining obligation: Concrete Laurent group algebra and Burau matrix images; verify matrix convention and typecheck.

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

open Braids
/-- The Laurent ring Z[t,t⁻¹] is the additive group algebra Z[Z].
The monomial t is supported at exponent 1 with coefficient 1. -/
abbrev Laurent := LaurentPolynomial Int
def t : Laurent := LaurentPolynomial.T 1
def burauEntry (i : Index 4) (a b : Fin 4) : Laurent :=
  if a = left i ∧ b = left i then 1-t else
  if a = left i ∧ b = right i then t else
  if a = right i ∧ b = left i then 1 else
  if a = right i ∧ b = right i then 0 else if a = b then 1 else 0
def question : Prop :=
  ∃ f : B 4 →* (Matrix (Fin 4) (Fin 4) Laurent)ˣ,
    (∀ i : Index 4, ∀ a b,
      (f (PresentedGroup.of (rels := classicalRels 4) i)).val a b =
        burauEntry i a b) ∧ Function.Injective f

end
end QuandleResearch.Issue059
