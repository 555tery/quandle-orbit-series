import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 30: Bardakov et al. Problem 5.2 (2021) — faithful parameters of Psi_{k,l}
https://github.com/555tery/quandle-orbit-series/issues/30

Formalization status: PARTIAL.
Remaining obligation: Capital Psi on F_(n+1) encoded directly; literal F_(n-1) in Problem 5.2 conflicts with preceding definition. Source right action converted using inverse automorphisms.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 24](https://arxiv.org/pdf/2107.03875#page=24). Original PDF formulation checked.

## Target
Determine whether there exist integers k,l for which Ψ_{k,l} is faithful for all n > 2.
-/

namespace QuandleResearch.Issue030
noncomputable section

open Braids
/-- The displayed definition immediately preceding Problem 5.2 uses F_(n+1).
The occurrence of F_(n-1) in the question is recorded as a textual discrepancy. -/
def question : Prop :=
  ∃ k l : Int, ∀ n : Nat, 2 < n →
    ∃ f : UB n →* (ExtendedFree n ≃* ExtendedFree n),
      IsCapitalPsi k l f ∧ Function.Injective f

end
end QuandleResearch.Issue030
