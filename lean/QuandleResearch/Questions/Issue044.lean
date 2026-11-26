import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 44: Bardakov et al. Problem 2 (2020) — kernel of the integral flat virtual braid representation Delta
https://github.com/555tery/quandle-orbit-series/issues/44

Formalization status: PARTIAL.
Remaining obligation: Concrete FVB and integral matrix target; Delta generator matrices still required.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov et al. (including T. Nasybullov), *Representations of flat virtual braids which do not preserve the forbidden relations*, [arXiv:2010.03162v1](https://arxiv.org/pdf/2010.03162v1), printed p. 13..

## Target
Determine ker(Δ) for the specific representation Δ:FVB_n→GL_{3n}(Z) in Theorem 3. Use the matrices defined in that theorem, not the different representation Θ.

## Source context / leads for later audit
Theorem 3 distinguishes Δ from Θ by the elements (ρ_iσ_{i+1})^6. The original problem is about the entire kernel.
-/

namespace QuandleResearch.Issue044
noncomputable section

open Braids
def verifiesKernel (delta : ∀ n, FVB n →* (Matrix (Fin (3*n)) (Fin (3*n)) Int)ˣ)
    (answer : ∀ n, Subgroup (FVB n)) : Prop :=
  ∀ n, 2 ≤ n → (delta n).ker = answer n

end
end QuandleResearch.Issue044
