import QuandleResearch.Theory.Interfaces

/-!
# Issue 68: Darné Remark 2.22 (2026 v3) — residual nilpotency of the enveloping group
https://github.com/555tery/quandle-orbit-series/issues/68

Formalization status: PARTIAL.
Remaining obligation: Verify residual nilpotency indexing against Darné v3; known implications are still statements, not proofs.

Source and target from the issue:
## Source / explicitly stated open relation
Jacques Darné, *Nilpotent quandles*, [arXiv:2205.02480v3, p. 16, Remark 2.22](https://arxiv.org/pdf/2205.02480v3#page=16). Source text and PDF page image checked. The author leaves the relationship with residual nilpotency of G(Q) unclear; Proposition 2.24 settles one direction under injectivity.

## Target
Determine the implications (or counterexamples) between residual nilpotency of Q, G(Q), and Inn(Q) involving G(Q). Preserve the distinction between general and injective quandles. The separate question Inn(Q)⇒Q from Proposition 2.21 is tracked independently.
-/

namespace QuandleResearch.Issue068
noncomputable section

def envToQ : Prop := ∀ (Q : Quandle) (E : Enveloping Q),
  ResiduallyNilpotent E.G.carrier → Q.ResiduallyNilpotent
def qToEnv : Prop := ∀ (Q : Quandle) (E : Enveloping Q),
  Q.ResiduallyNilpotent → ResiduallyNilpotent E.G.carrier
def envToInn : Prop := ∀ (Q : Quandle) (E : Enveloping Q),
  ResiduallyNilpotent E.G.carrier → ResiduallyNilpotent Q.Inn
def innToEnv : Prop := ∀ (Q : Quandle) (E : Enveloping Q),
  ResiduallyNilpotent Q.Inn → ResiduallyNilpotent E.G.carrier
def envToQInjective : Prop := ∀ (Q : Quandle) (E : Enveloping Q), E.InjectiveQuandle →
  ResiduallyNilpotent E.G.carrier → Q.ResiduallyNilpotent
def qToEnvInjective : Prop := ∀ (Q : Quandle) (E : Enveloping Q), E.InjectiveQuandle →
  Q.ResiduallyNilpotent → ResiduallyNilpotent E.G.carrier
def envToInnInjective : Prop := ∀ (Q : Quandle) (E : Enveloping Q), E.InjectiveQuandle →
  ResiduallyNilpotent E.G.carrier → ResiduallyNilpotent Q.Inn
def innToEnvInjective : Prop := ∀ (Q : Quandle) (E : Enveloping Q), E.InjectiveQuandle →
  ResiduallyNilpotent Q.Inn → ResiduallyNilpotent E.G.carrier

end
end QuandleResearch.Issue068
