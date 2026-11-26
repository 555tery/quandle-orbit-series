import QuandleResearch.Theory.Interfaces

/-!
# Issue 10: Gonçalves–Nasybullov Problem 1 (2017) — sharp verbal-width bounds
https://github.com/555tery/quandle-orbit-series/issues/10

Formalization status: PARTIAL.
Remaining obligation: Verify verbal word, indexing and sharpness scope against source.

Source and target from the issue:
## Source
Gonçalves–Nasybullov, [arXiv:1705.06842v1](https://arxiv.org/abs/1705.06842v1), Problem 1, p. 7: find sharp estimates for wid(gamma_k(G)), k>=4, in the setting of their preceding finite-generation and twisted-class subgroup results.
-/

namespace QuandleResearch.Issue010
noncomputable section

def sharpBound (bound : Nat → Nat → Nat) : Prop :=
  ∀ n k, 4 ≤ k →
    (∀ (G : Type) [Group G], NGenerated G n → AllInner G →
      widthAtMost (Set.range (wordValue (G := G) k)) (lowerCentral G (k-1)) (bound n k)) ∧
    (∀ b, (∀ (G : Type) [Group G], NGenerated G n → AllInner G →
      widthAtMost (Set.range (wordValue (G := G) k)) (lowerCentral G (k-1)) b) → bound n k ≤ b)

end
end QuandleResearch.Issue010
