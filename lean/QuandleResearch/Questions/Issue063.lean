import QuandleResearch.Theory.Interfaces

/-!
# Issue 63: Bardakov et al. Question 3.4 (2022 journal version) — which virtual braid quotients are Bieberbach groups?
https://github.com/555tery/quandle-orbit-series/issues/63

Formalization status: PARTIAL.
Remaining obligation: Construct quotient and Bieberbach predicate; distinct from #26.

Source and target from the issue:
## Source and exact scope

Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, Journal of Group Theory 25 (2022), 679–712, [DOI:10.1515/jgth-2021-0114, §3, Question 3.4](https://www.degruyterbrill.com/document/doi/10.1515/jgth-2021-0114/html). The publisher's full text was rechecked on 25 November 2026.

The printed question reads: “Which of the groups VB_n/VP_n′ are Bieberbach groups?”

This is distinct from the stronger subgroup-classification question in [arXiv:2107.03875v1, Question 3.2](https://arxiv.org/abs/2107.03875v1), tracked in #26. We do not assume that the change of wording was intentional.
-/

namespace QuandleResearch.Issue063
noncomputable section

def verifiesClassification (quotient : Nat → GroupObject)
    (bieberbach : GroupObject → Prop) (answer : Nat → Prop) : Prop :=
  ∀ n, 0 < n → (answer n ↔ bieberbach (quotient n))

end
end QuandleResearch.Issue063
