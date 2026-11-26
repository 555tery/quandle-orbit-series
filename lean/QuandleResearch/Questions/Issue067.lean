import QuandleResearch.Theory.Interfaces

/-!
# Issue 67: Darné §2.4 (2026 v3) — converse of residual nilpotency Proposition 2.21
https://github.com/555tery/quandle-orbit-series/issues/67

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly stated open question
Jacques Darné, *Nilpotent quandles*, [arXiv:2205.02480v3, printed p. 16, immediately after Proposition 2.21](https://arxiv.org/pdf/2205.02480v3#page=16). Source text and PDF page image checked. This is distinct from the already resolved classification problem #19.

## Target
Does residual nilpotency of Inn(Q) imply residual nilpotency of Q, with no finiteness or injectivity assumption? Equivalently, when the lower central series of Inn(Q) has trivial intersection, must its orbit equivalence relations have trivial intersection? Use Definition 2.20 and the universal nilpotent quotients of §2.2.
-/

namespace QuandleResearch.Issue067
noncomputable section

def question : Prop := ∀ Q : Quandle, ResiduallyNilpotent Q.Inn → Q.ResiduallyNilpotent

end
end QuandleResearch.Issue067
