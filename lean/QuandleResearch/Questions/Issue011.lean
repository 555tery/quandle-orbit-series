import QuandleResearch.Theory.Interfaces

/-!
# Issue 11: Bardakov–Nasybullov–Singh Problem 5.21 (2019) — arbitrarily large rigid biquandles
https://github.com/555tery/quandle-orbit-series/issues/11

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source
Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, [arXiv:1908.08301v1](https://arxiv.org/abs/1908.08301v1), Problem 5.21. Is there a threshold N beyond which every finite biquandle has a nonidentity automorphism? The authors expect a negative answer, i.e. arbitrarily large finite biquandles B with Aut(B)=1.
-/

namespace QuandleResearch.Issue011
noncomputable section

def thresholdExists : Prop :=
  ∃ N : Nat, ∀ B : Biquandle, Finite B.carrier → N ≤ Nat.card B.carrier → ¬ B.Rigid
def arbitrarilyLargeRigid : Prop :=
  ∀ N : Nat, ∃ B : Biquandle, Finite B.carrier ∧ N ≤ Nat.card B.carrier ∧ B.Rigid

end
end QuandleResearch.Issue011
