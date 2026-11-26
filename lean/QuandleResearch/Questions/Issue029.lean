import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 29: Bardakov et al. Problem 5.1 (2021) — faithfulness of extended psi_{k,k}
https://github.com/555tery/quandle-orbit-series/issues/29

Formalization status: PARTIAL.
Remaining obligation: Concrete UB and source psi generator images; verify extension on sigma and right-action convention against source.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 24](https://arxiv.org/pdf/2107.03875#page=24). Original PDF formulation checked.

## Target
Determine whether the extended representation ψ̃_{k,k}: UB_n → Aut(F_n) is faithful for k ≠ 0.
-/

namespace QuandleResearch.Issue029
noncomputable section

open Braids
def question : Prop :=
  ∀ (n : Nat) (k : Int), 2 ≤ n → k ≠ 0 →
    ∃ f : UB n →* (FreeGroup (Fin n) ≃* FreeGroup (Fin n)),
      IsExtendedPsi k k f ∧ Function.Injective f

end
end QuandleResearch.Issue029
