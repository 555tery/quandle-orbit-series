import QuandleResearch.Theory.Interfaces

/-!
# Issue 25: Bardakov et al. Question 3.1 (2021) — torsion orders in virtual braid quotient
https://github.com/555tery/quandle-orbit-series/issues/25

Formalization status: PARTIAL.
Remaining obligation: Construct VB_n/VP_n′ and its distinguished symmetric subgroup.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 14](https://arxiv.org/pdf/2107.03875#page=14). Original PDF formulation checked.

## Target
Determine all finite orders of elements in VB_n/VP_n′ that lie outside the distinguished S_n subgroup.
-/

namespace QuandleResearch.Issue025
noncomputable section

def verifiesOrders (G : Type) [Group G] (sn : Subgroup G) (answer : Nat → Prop) : Prop :=
  ∀ k, answer k ↔ 0 < k ∧ ∃ x : G, x ∉ sn ∧ orderOf x = k

end
end QuandleResearch.Issue025
