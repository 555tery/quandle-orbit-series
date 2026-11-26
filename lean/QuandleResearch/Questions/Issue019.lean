import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.ConcreteEnveloping

/-!
# Issue 19: Bardakov–Nasybullov Problem 3.6 (2019) — nilpotent enveloping groups
https://github.com/555tery/quandle-orbit-series/issues/19

Formalization status: PARTIAL.
Remaining obligation: Concrete enveloping group presentation; independent structural classification is the requested answer, not part of the problem statement.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1902.02154, printed p. 7](https://arxiv.org/pdf/1902.02154#page=7). Original PDF formulation checked.

## Target
Classify quandles whose enveloping group is nilpotent.
-/

namespace QuandleResearch.Issue019
noncomputable section

def targetClass (Q : Quandle) : Prop := Nilpotent Q.EnvGroup
def verifiesClassification (answer : Quandle → Prop) : Prop :=
  ∀ Q, answer Q ↔ targetClass Q

end
end QuandleResearch.Issue019
