import QuandleResearch.Theory.Interfaces

/-!
# Issue 2: Research: stabilization of normal-closure towers in group extensions
https://github.com/555tery/quandle-orbit-series/issues/2

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Motivation
Generalize the finite-defect subnormality/absorption argument from [Question 5.7](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-7) and its [October operator-series revision](https://github.com/555tery/quandle-orbit-series/tree/42036b2d9c0aef3e21a6b68d9739bc1049919c0a/question-5-7).

## Candidate theorem
For H <= G define T_0=G, T_{i+1}=<H^{T_i}>, and let delta(G,H) be the first stabilization index. For N normal in G, investigate

$$\delta(G,H)\le\delta(G/N,HN/N)+\delta(NH,H).$$

When HN/N normally generates G/N, define U_0=NH and U_{i+1}=<H^{U_i}>. The proposed key identity is T_i=U_i T_{i+1}. Prove via normal generation of T_i/T_{i+1}, surjectivity of T_i intersect NH onto this quotient, and finite-defect subnormality of U_i there. Reduce the general case to a stabilized quotient tower. Test sharpness using dihedral semidirect products C_(2^(r+m)) ⋊ C_2.
-/

namespace QuandleResearch.Issue002
noncomputable section

def question (G : Type) [Group G] (N H : Subgroup G) [N.Normal]
    (a b c : Nat) : Prop :=
  TowerDepth H ⊤ a → TowerDepth (H.map (QuotientGroup.mk' N)) ⊤ b →
  TowerDepth H (N ⊔ H) c → a ≤ b + c

end
end QuandleResearch.Issue002
