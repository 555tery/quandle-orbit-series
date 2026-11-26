import QuandleResearch.Theory.Interfaces

/-!
# Issue 54: Fel’shtyn–Nasybullov Conjecture S (2015) — S-infinity or virtual solvability
https://github.com/555tery/quandle-orbit-series/issues/54

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated problem
Fel’shtyn, Nasybullov, *The R∞ and S∞ properties for linear algebraic groups*, [arXiv:1506.02464v3, p.17](https://arxiv.org/pdf/1506.02464v3#page=17), J. Group Theory 19 (2016), 901–921. Explicit Conjecture S on the page image, a version of the earlier Fel’shtyn–Troitsky conjecture with the finite-center restriction removed.

## Target
Every infinite finitely generated residually finite group has the S∞ property or is virtually solvable. For each Ψ∈Out(G), S(Ψ) counts the isogredience classes of automorphisms representing Ψ; S∞ means every such count is infinite.

## Source context
Lemma 6 identifies S(Ψ) with the Reidemeister number of the induced automorphism of G/Z(G). The authors give an implication from Conjecture R (companion issue); audit the precise assumptions, including residual finiteness of the central quotient, and whether the unrestricted conjecture or implications have known answers.
-/

namespace QuandleResearch.Issue054
noncomputable section

def question : Prop :=
  ∀ (G : Type) [Group G] [Infinite G], FinitelyGenerated G → ResiduallyFinite G →
    SInfinity G ∨ VirtuallySolvable G

end
end QuandleResearch.Issue054
