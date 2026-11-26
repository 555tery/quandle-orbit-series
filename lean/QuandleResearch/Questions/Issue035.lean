import QuandleResearch.Theory.Interfaces

/-!
# Issue 35: BNN Question 2 (2013) — class-two bound for finite groups
https://github.com/555tery/quandle-orbit-series/issues/35

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 26..

## Target
If a finite group G has [e]_h a subgroup for all h∈G, can the nilpotency class in Corollary 4 be bounded by two?

## Source context / leads for later audit
The later Gonçalves–Nasybullov paper explicitly discusses an answer in Example 1; record for independent verification later, not a new open-status claim.
-/

namespace QuandleResearch.Issue035
noncomputable section

def question : Prop := ∀ (G : Type) [Group G] [Finite G], AllInner G → lowerCentral G 2 = ⊥

end
end QuandleResearch.Issue035
