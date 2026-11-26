import QuandleResearch.Theory.Interfaces

/-!
# Issue 15: Ercan–Güloğlu Conjecture 6.1 — ideality of the final left-series term
https://github.com/555tery/quandle-orbit-series/issues/15

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / published conjecture
G. Ercan and İ. Ş. Güloğlu, *The Left-Nilpotent Residual and Its Supplements in Finite Skew Braces*, [arXiv:2609.06994v1, Conjecture 6.1](https://arxiv.org/html/2609.06994v1#S6), 7 September 2026.
For every finite skew brace \(X\) of nilpotent type, is the stable term \(L_\infty(X)\) of the left series an ideal (equivalently, equal to the left-nilpotent residual)?
-/

namespace QuandleResearch.Issue015
noncomputable section

def question : Prop :=
  ∀ B : SkewBrace, Finite B.carrier → B.nilpotentType → B.IsIdeal B.stableLeft

end
end QuandleResearch.Issue015
