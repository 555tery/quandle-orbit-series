import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.ConcreteEnveloping

/-!
# Issue 18: Bardakov–Nasybullov Problem 3.5 (2019) — free abelian enveloping groups
https://github.com/555tery/quandle-orbit-series/issues/18

Formalization status: PARTIAL.
Remaining obligation: Concrete enveloping group presentation; independent structural classification is the requested answer, not part of the problem statement.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1902.02154, printed p. 6](https://arxiv.org/pdf/1902.02154#page=6). Original PDF formulation checked.

## Target
Classify quandles with free abelian enveloping groups, without an explicit finiteness restriction in the question.
-/

namespace QuandleResearch.Issue018
noncomputable section

def FreeAbelian (G : Type) [Group G] : Prop :=
  ∃ X : Type, Nonempty (G ≃* Multiplicative (X →₀ Int))
def targetClass (Q : Quandle) : Prop := FreeAbelian Q.EnvGroup
def verifiesClassification (answer : Quandle → Prop) : Prop :=
  ∀ Q, answer Q ↔ targetClass Q

end
end QuandleResearch.Issue018
