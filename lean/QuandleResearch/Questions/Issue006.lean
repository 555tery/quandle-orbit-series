import QuandleResearch.Theory.Interfaces

/-!
# Issue 6: Research: operator-series absorption in groups, modules and universal algebra
https://github.com/555tery/quandle-orbit-series/issues/6

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Motivation
Recover the standalone group-with-operators theorem from the [October Question 5.7 revision](https://github.com/555tery/quandle-orbit-series/tree/42036b2d9c0aef3e21a6b68d9739bc1049919c0a/question-5-7) and determine its scope independently of quandles.

## Starting result
For A <= Aut(G) preserving N normal in G, define D_i=[G,_i A], R_i=[N,_i A]. If [G/N,A]=G/N, the previous proof gives D_i=R_i D_{i+1}; iterating yields D_i=R_i D_j for j>=i. In the abelian case this is the elementary ideal-power identity J^i M=J^i N+J^{i+1}M when J(M/N)=M/N.
-/

namespace QuandleResearch.Issue006
noncomputable section

def absorption (G : Type) [Group G] (A : Subgroup (G ≃* G)) (N : Subgroup G) [N.Normal] : Prop :=
  (∀ a ∈ A, ∀ x ∈ N, a x ∈ N) →
  operatorStep A ⊤ ⊔ N = ⊤ →
  ∀ i j, i ≤ j →
    (operatorSeries A (⊤ : Subgroup G) i : Set G) =
      setProduct (operatorSeries A N i) (operatorSeries A (⊤ : Subgroup G) j)

end
end QuandleResearch.Issue006
