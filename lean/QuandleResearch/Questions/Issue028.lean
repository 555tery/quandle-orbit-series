import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 28: Bardakov et al. Question 4.2 (2021) — image of H_n under Psi
https://github.com/555tery/quandle-orbit-series/issues/28

Formalization status: PARTIAL.
Remaining obligation: Concrete VB and H_n; Psi generator matrices and Laurent ring still required.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 18](https://arxiv.org/pdf/2107.03875#page=18). Original PDF formulation checked.

## Target
Describe Ψ(H_n), where H_n is the kernel of the map VB_n → S_n sending σ_i to 1 and ρ_i to the adjacent transposition; use the representation Ψ defined in §3, equations (30)–(31).
-/

namespace QuandleResearch.Issue028
noncomputable section

open Braids
def verifiesImage {K : Type} [Group K] (psi : ∀ n, VB n →* K)
    (answer : Nat → Subgroup K) : Prop :=
  ∀ n, 2 ≤ n → (H n).map (psi n) = answer n

end
end QuandleResearch.Issue028
