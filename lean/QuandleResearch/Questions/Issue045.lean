import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 45: Bardakov et al. Problem 3 (2020) — presentations of intersections of pure and Rabenda kernels
https://github.com/555tery/quandle-orbit-series/issues/45

Formalization status: PARTIAL.
Remaining obligation: Concrete presentations and both kernel-image subgroups; verify Gauss relations and source projection conventions.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov et al. (including T. Nasybullov), *Representations of flat virtual braids which do not preserve the forbidden relations*, [arXiv:2010.03162v1](https://arxiv.org/pdf/2010.03162v1), printed p. 19..

## Target
Find generators and defining relations for VP_n∩H_n, FVP_n∩FH_n, and GVP_n∩GH_n, with the two projection kernels defined in §2.

## Source context / leads for later audit
Section 5 gives normal generators, which need not constitute an ordinary generating set. Related #31; test the finite-index Reidemeister–Schreier approach in the later audit.
-/

namespace QuandleResearch.Issue045
noncomputable section

open Braids
def verifiesPresentations (virtual flat gauss : Nat → Presentation) : Prop :=
  ∀ n, 2 ≤ n →
    Presents (virtual n) (intersection (virtualRels n)) ∧
    Presents (flat n) (intersection (flatRels n)) ∧
    Presents (gauss n) (intersection (gaussRels n))

end
end QuandleResearch.Issue045
