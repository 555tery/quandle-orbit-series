import QuandleResearch.Theory.Interfaces

/-!
# Issue 27: Bardakov et al. Question 4.1 (2021) — minimal faithful linear dimension of VP_3
https://github.com/555tery/quandle-orbit-series/issues/27

Formalization status: PARTIAL.
Remaining obligation: Construct VP_3 and verify field scope.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 18](https://arxiv.org/pdf/2107.03875#page=18). Original PDF formulation checked.

## Target
Determine the minimum dimension of a faithful linear representation of the pure virtual braid group VP_3.
-/

namespace QuandleResearch.Issue027
noncomputable section

def minimalDimension (VP3 : GroupObject) (d : Nat) : Prop :=
  LinearDim VP3.carrier d ∧ ∀ e, LinearDim VP3.carrier e → d ≤ e

end
end QuandleResearch.Issue027
