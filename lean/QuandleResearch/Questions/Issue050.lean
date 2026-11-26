import QuandleResearch.Theory.Interfaces

/-!
# Issue 50: Cattabriga–Matveev–Mulazzani–Nasybullov Conjecture (2018) — complexity of closed nonorientable Seifert fibre spaces
https://github.com/555tery/quandle-orbit-series/issues/50

Formalization status: PARTIAL.
Remaining obligation: Construct Seifert spaces, admissibility, complexity, Euler characteristic and S function.

Source and target from the issue:
## Source / explicitly formulated problem
Cattabriga, Matveev, Mulazzani, Nasybullov, *On the complexity of non-orientable Seifert fibre spaces*, [arXiv:1704.06721v4, p.36](https://arxiv.org/pdf/1704.06721v4#page=36), Indiana Univ. Math. J. 69 (2020), 421–451. Conjecture at the end of the paper, verified on page image.

## Target
For a nonorientable closed irreducible and RP²-irreducible Seifert fibre space M={b;(ε,g,(t,k));(|);((p₁,q₁),…,(pᵣ,qᵣ))}, prove or disprove c(M)=6(1−χ)+6t+Σⱼ(S(pⱼ,qⱼ)+1), with all parameters and S as defined in the source. χ is the Euler characteristic of the capped base surface, not the orbifold Euler characteristic.

## Source context
Formula (4) is an upper bound; authors note it is attained in all cases in the census available to them. Need lower bounds or counterexamples; preserve irreducibility and nonorientability assumptions.
-/

namespace QuandleResearch.Issue050
noncomputable section

def question {Space : Type} (eligible : Space → Prop) (complexity t : Space → Nat)
    (chi : Space → Int) (exceptional : Space → List (Nat × Nat)) (S : Nat → Nat → Nat) : Prop :=
  ∀ M, eligible M → (complexity M : Int) =
    6 * (1 - chi M) + 6 * (t M : Int) +
      ((exceptional M).map (fun p => S p.1 p.2 + 1)).sum

end
end QuandleResearch.Issue050
