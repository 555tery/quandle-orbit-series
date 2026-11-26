import QuandleResearch.Theory.Interfaces

/-!
# Issue 31: Bardakov et al. Question 5.1 (2021) — presentation of UP_n
https://github.com/555tery/quandle-orbit-series/issues/31

Formalization status: PARTIAL.
Remaining obligation: Construct UP_n as the source kernel.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 26](https://arxiv.org/pdf/2107.03875#page=26). Original PDF formulation checked.

## Target
For n > 3, find generators and defining relations of the pure universal braid group UP_n.
-/

namespace QuandleResearch.Issue031
noncomputable section

def verifiesPresentation (UP : Nat → GroupObject) (answer : Nat → Presentation) : Prop :=
  ∀ n, 3 < n → Presents (answer n) (UP n).carrier

end
end QuandleResearch.Issue031
