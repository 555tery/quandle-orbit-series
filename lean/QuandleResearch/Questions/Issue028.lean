import QuandleResearch.Theory.Interfaces

/-!
# Issue 28: Bardakov et al. Question 4.2 (2021) — image of H_n under Psi
https://github.com/555tery/quandle-orbit-series/issues/28

Formalization status: PARTIAL.
Remaining obligation: Construct H_n as the stated kernel and Psi by source generator formulas.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 18](https://arxiv.org/pdf/2107.03875#page=18). Original PDF formulation checked.

## Target
Describe Ψ(H_n), where H_n is the kernel of the map VB_n → S_n sending σ_i to 1 and ρ_i to the adjacent transposition; use the representation Ψ defined in §3, equations (30)–(31).
-/

namespace QuandleResearch.Issue028
noncomputable section

def verifiesImage (G H : GroupObject) (psi : G.carrier →* H.carrier)
    (K : Subgroup G.carrier) (answer : Subgroup H.carrier) : Prop :=
  K.map psi = answer

end
end QuandleResearch.Issue028
