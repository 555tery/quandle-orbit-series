import QuandleResearch.Theory.Interfaces

/-!
# Issue 43: Bardakov et al. Problem 1 (2020) — kernel of the flat virtual braid representation theta
https://github.com/555tery/quandle-orbit-series/issues/43

Formalization status: PARTIAL.
Remaining obligation: Construct FVB_n and theta using source formulas.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov et al. (including T. Nasybullov), *Representations of flat virtual braids which do not preserve the forbidden relations*, [arXiv:2010.03162v1](https://arxiv.org/pdf/2010.03162v1), printed p. 9..

## Target
Determine ker(θ) for the representation θ:FVB_n→Aut(F_{2n}) in Theorem 1, defined by σ_i: x_i↦x_{i+1}y_{i+1}, x_{i+1}↦x_i y_{i+1}^{−1}, and ρ_i swapping x_i,x_{i+1} and y_i,y_{i+1}, fixing the other generators.

## Source context / leads for later audit
Corollary 1 gives a lower bound by the normal closure of (ρ_iσ_{i+1})^6 and an upper bound FVP_n∩FH_n. The case n=2 is handled in Proposition 7.
-/

namespace QuandleResearch.Issue043
noncomputable section

def verifiesKernel (theta : Representation) (answer : Subgroup theta.source.carrier) : Prop :=
  theta.map.ker = answer

end
end QuandleResearch.Issue043
