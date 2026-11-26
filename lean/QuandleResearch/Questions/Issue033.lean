import QuandleResearch.Theory.Interfaces

/-!
# Issue 33: BNN Conjecture 2 (2013) — centerless groups and inner twisted classes
https://github.com/555tery/quandle-orbit-series/issues/33

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 29; also Kourovka Notebook 18.15..

## Target
For a nontrivial centerless group G, must there exist an inner automorphism φ such that [e]_φ is not a subgroup? The nontriviality convention excludes the trivial group.

## Source context / leads for later audit
Compare #8 and the centerless/min-n results in the source.
-/

namespace QuandleResearch.Issue033
noncomputable section

def question : Prop :=
  ∀ (G : Type) [Group G], (∃ x : G, x ≠ 1) → Centerless G → ¬ AllInner G

end
end QuandleResearch.Issue033
