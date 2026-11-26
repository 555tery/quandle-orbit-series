import QuandleResearch.Theory.Interfaces

/-!
# Issue 37: BNN Question 4 (2013) — homological criteria for twisted-class subgroup property
https://github.com/555tery/quandle-orbit-series/issues/37

Formalization status: PARTIAL.
Remaining obligation: Construct extension cocycle/action and homological criterion.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 29..

## Target
Express conditions for every twisted conjugacy class of the identity to be a subgroup in the homological description of extensions of abelian groups.

## Source context / leads for later audit
Check whether the intended quantification is over inner or all automorphisms from context; preserve original wording and address both if ambiguous.
-/

namespace QuandleResearch.Issue037
noncomputable section

def verifiesCriterion (G : Type) [Group G] (N : Subgroup G) [N.Normal]
    (Data : Type) (extensionData : Data) (criterion : Data → Prop) : Prop :=
  Abelian N → Abelian (G ⧸ N) → (criterion extensionData ↔ AllAut G)

end
end QuandleResearch.Issue037
