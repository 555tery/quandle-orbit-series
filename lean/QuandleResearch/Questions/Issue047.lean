import QuandleResearch.Theory.Interfaces

/-!
# Issue 47: Nasybullov Problem 2 (2017) — width of the identity twisted conjugacy class
https://github.com/555tery/quandle-orbit-series/issues/47

Formalization status: PARTIAL.
Remaining obligation: Construct GL_n and the entrywise automorphisms under the source field hypotheses.

Source and target from the issue:
## Source / explicitly formulated question
Nasybullov, *Reidemeister spectrum of special and general linear groups over some fields contains 1*, [arXiv:1708.06280v2, p.12](https://arxiv.org/pdf/1708.06280v2#page=12). Verified against the original PDF page.

## Target
Under the hypotheses of §4 (algebraically closed characteristic-zero F, entrywise φ induced by field automorphism, R(φ) finite), can every matrix of GL_n(F) be written as a product of at most k<3 elements of [I_n]_φ ∪ ([I_n]_φ)⁻¹?

## Source context / leads for later audit
The source proves width at most 3 in Proposition 6 (verify numbering in journal version) and relates the question to Problem 1. A positive R=1 answer there gives width 1.
-/

namespace QuandleResearch.Issue047
noncomputable section

def question (G : GroupObject) (entrywise : Set (G.carrier ≃* G.carrier)) : Prop :=
  ∀ f ∈ entrywise, FiniteReidemeister f → widthAtMost (twisted f) (⊤ : Subgroup G.carrier) 2

end
end QuandleResearch.Issue047
