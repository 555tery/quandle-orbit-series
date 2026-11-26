import QuandleResearch.Theory.Interfaces

/-!
# Issue 16: Ercan–Güloğlu Remark 7.9 — ideality of iterated left-nilpotent residuals
https://github.com/555tery/quandle-orbit-series/issues/16

Formalization status: PARTIAL.
Remaining obligation: Check residual definition against paper; embeddings encode the iterates without constructing them.

Source and target from the issue:
## Source / published question
G. Ercan and İ. Ş. Güloğlu, *The Left-Nilpotent Residual and Its Supplements in Finite Skew Braces*, [arXiv:2609.06994v1, Remark 7.9](https://arxiv.org/html/2609.06994v1#S7), 2026.
For \(R_0(X)=X,\ R_{n+1}(X)=\mathfrak R_L(R_n(X))\), are all \(R_n(X)\) ideals of the original finite skew brace \(X\)? The authors establish automorphism invariance, but leave ideality open.
-/

namespace QuandleResearch.Issue016
noncomputable section

def question : Prop :=
  ∀ (B : SkewBrace) (R : Nat → SkewBrace) (e : ∀ n, SkewBrace.Embedding (R n) B)
    (step : ∀ n, SkewBrace.Embedding (R (n+1)) (R n)), Finite B.carrier →
    Set.range (e 0).map = Set.univ →
    (∀ n, Set.range (step n).map = (R n).leftResidual) →
    (∀ n x, (e (n+1)).map x = (e n).map ((step n).map x)) →
    ∀ n, B.IsIdeal (Set.range (e n).map)

end
end QuandleResearch.Issue016
