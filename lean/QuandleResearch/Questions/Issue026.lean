import QuandleResearch.Theory.Interfaces

/-!
# Issue 26: Bardakov et al. Question 3.2 (2021 preprint) — classify Bieberbach subgroups of VB_n/VP_n′
https://github.com/555tery/quandle-orbit-series/issues/26

Formalization status: PARTIAL.
Remaining obligation: Construct quotient and geometric Bieberbach predicate; explicit classification required.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 14](https://arxiv.org/pdf/2107.03875#page=14). Original PDF formulation checked.

## Target
Determine which Bieberbach subgroups occur in VB_n/VP_n′.
-/

namespace QuandleResearch.Issue026
noncomputable section

def verifiesClassification (G : Type) [Group G] (bieberbach answer : Subgroup G → Prop) : Prop :=
  ∀ H, answer H ↔ bieberbach H

end
end QuandleResearch.Issue026
