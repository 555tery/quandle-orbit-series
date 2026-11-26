import QuandleResearch.Theory.Interfaces

/-!
# Issue 30: Bardakov et al. Problem 5.2 (2021) — faithful parameters of Psi_{k,l}
https://github.com/555tery/quandle-orbit-series/issues/30

Formalization status: PARTIAL.
Remaining obligation: Construct UB_n and Psi_{k,l} by source generator formulas.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 24](https://arxiv.org/pdf/2107.03875#page=24). Original PDF formulation checked.

## Target
Determine whether there exist integers k,l for which Ψ_{k,l} is faithful for all n > 2.
-/

namespace QuandleResearch.Issue030
noncomputable section

def question (psi : Nat → Int → Int → Representation) : Prop :=
  ∃ k l, ∀ n, 2 < n → (psi n k l).Faithful

end
end QuandleResearch.Issue030
