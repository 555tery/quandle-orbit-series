import QuandleResearch.Theory.Interfaces

/-!
# Issue 12: Research: Bardakov–Nasybullov–Singh Problem 4.12 — biquandle structures on trivial quandles
https://github.com/555tery/quandle-orbit-series/issues/12

Formalization status: PARTIAL.
Remaining obligation: An explicit classification model, not a tautological parameterization.

Source and target from the issue:
## Source
Bardakov–Nasybullov–Singh, [arXiv:1908.08301v1](https://arxiv.org/abs/1908.08301v1), Problem 4.12: classify biquandle structures on the trivial n-element quandle T_n.
-/

namespace QuandleResearch.Issue012
noncomputable section

def classification (n : Nat) (Param : Type) (model : Param → Fin n → Equiv.Perm (Fin n)) : Prop :=
  (∀ p, ValidTrivialFamily (model p)) ∧
  ∀ beta : Fin n → Equiv.Perm (Fin n), ValidTrivialFamily beta ↔
    ∃ p, IsoTrivialFamily beta (model p)

end
end QuandleResearch.Issue012
