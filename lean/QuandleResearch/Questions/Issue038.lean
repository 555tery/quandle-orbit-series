import QuandleResearch.Theory.Interfaces

/-!
# Issue 38: BNN Question 5 (2013) — classification under endomorphism, automorphism and inner conditions
https://github.com/555tery/quandle-orbit-series/issues/38

Formalization status: PARTIAL.
Remaining obligation: Independent structural descriptions required; arbitrary predicates are not solutions.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 33..

## Target
Describe groups G satisfying [e]_φ≤G for (a) every endomorphism φ, (b) every automorphism φ, (c) every inner automorphism φ. These are distinct conditions; retain all three parts.

## Source context / leads for later audit
Related BNN Conjecture 1, Conjecture 2, and #8–10.
-/

namespace QuandleResearch.Issue038
noncomputable section

def endClassification (answer : GroupObject → Prop) : Prop :=
  ∀ G, answer G ↔ AllEnd G.carrier
def autClassification (answer : GroupObject → Prop) : Prop :=
  ∀ G, answer G ↔ AllAut G.carrier
def innerClassification (answer : GroupObject → Prop) : Prop :=
  ∀ G, answer G ↔ AllInner G.carrier

end
end QuandleResearch.Issue038
