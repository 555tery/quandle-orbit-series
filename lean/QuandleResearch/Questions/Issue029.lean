import QuandleResearch.Theory.Interfaces

/-!
# Issue 29: Bardakov et al. Problem 5.1 (2021) — faithfulness of extended psi_{k,k}
https://github.com/555tery/quandle-orbit-series/issues/29

Formalization status: PARTIAL.
Remaining obligation: Construct UB_n and the extended representation.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 24](https://arxiv.org/pdf/2107.03875#page=24). Original PDF formulation checked.

## Target
Determine whether the extended representation ψ̃_{k,k}: UB_n → Aut(F_n) is faithful for k ≠ 0.
-/

namespace QuandleResearch.Issue029
noncomputable section

def question (psi : Nat → Int → Representation) : Prop :=
  ∀ n k, k ≠ 0 → (psi n k).Faithful

end
end QuandleResearch.Issue029
