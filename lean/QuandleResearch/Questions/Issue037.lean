import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.AbelianExtensions

/-!
# Issue 37: BNN Question 4 (2013) — homological criteria for twisted-class subgroup property
https://github.com/555tery/quandle-orbit-series/issues/37

Formalization status: PARTIAL.
Remaining obligation: Normalized action and 2-cocycle data and multiplication now explicit; compare source's homological conventions.

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

def verifiesCriterion (criterion : ∀ D : AbelianExtensionData, ExtensionCocycle D → Prop) : Prop :=
  ∀ (D : AbelianExtensionData) (C : ExtensionCocycle D)
    (law : Group (D.A × D.B)), C.Realizes law →
    (criterion D C ↔ (letI := law; AllAut (D.A × D.B)))

/-- Alternative inner-automorphism reading, tracked separately until
the original wording and context have been independently audited. -/
def verifiesInnerCriterion (criterion : ∀ D : AbelianExtensionData, ExtensionCocycle D → Prop) : Prop :=
  ∀ (D : AbelianExtensionData) (C : ExtensionCocycle D)
    (law : Group (D.A × D.B)), C.Realizes law →
    (criterion D C ↔ (letI := law; AllInner (D.A × D.B)))

end
end QuandleResearch.Issue037
