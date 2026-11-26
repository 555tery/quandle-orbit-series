import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 26: Bardakov et al. Question 3.2 (2021 preprint) — classify Bieberbach subgroups of VB_n/VP_n′
https://github.com/555tery/quandle-orbit-series/issues/26

Formalization status: PARTIAL.
Remaining obligation: Concrete quotient and algebraic Bieberbach condition; independent subgroup classification and geometric convention audit remain.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 14](https://arxiv.org/pdf/2107.03875#page=14). Original PDF formulation checked.

## Target
Determine which Bieberbach subgroups occur in VB_n/VP_n′.
-/

namespace QuandleResearch.Issue026
noncomputable section

open Braids
/-- Algebraic characterization: torsion-free, finitely generated and
virtually free abelian (including rank zero). The geometric equivalence
and the intended ambient subgroup classification still need audit. -/
def Bieberbach (G : Type) [Group G] : Prop :=
  FinitelyGenerated G ∧ (∀ x : G, 0 < orderOf x → x = 1) ∧
    ∃ H : Subgroup G, H.Normal ∧ Finite (G ⧸ H) ∧
      ∃ d : Nat, Nonempty (H ≃* Multiplicative (Fin d → Int))
def verifiesClassification (answer : ∀ n, Subgroup (VBmodVPderived n) → Prop) : Prop :=
  ∀ n (H : Subgroup (VBmodVPderived n)), 2 ≤ n → (answer n H ↔ Bieberbach H)

end
end QuandleResearch.Issue026
