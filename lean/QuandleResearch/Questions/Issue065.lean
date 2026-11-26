import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.LinkPresentations

/-!
# Issue 65: Fenn–Ilyutko–Kauffman–Manturov Problem 28B (2014) — topological model of the fundamental biquandle
https://github.com/555tery/quandle-orbit-series/issues/65

Formalization status: PARTIAL.
Remaining obligation: Fundamental strong biquandle specified by actual crossing relations; geometric model and naturality are requested, not asserted.

Source and target from the issue:
## Source / explicitly stated problem
R. Fenn, D. P. Ilyutko, L. H. Kauffman, V. O. Manturov, *Unsolved problems in virtual knot theory and combinatorial knot theory*, Banach Center Publications 103 (2014), 9–61, §8.1, Problem 28, printed p. 34. [Journal PDF, p.34](https://www.impan.pl/shop/en/publication/transaction/download/product/86155#page=26), [DOI](https://doi.org/10.4064/bc103-0-1), [arXiv v1, p.31](https://arxiv.org/pdf/1409.2823v1#page=31). Journal and preprint page images verified. The letters A/B/C are local tracking labels, not original numbering.

Original second question: “Give a topological explanation of the fundamental biquandle of a knot.”

## Target
Find a topologically defined object with biquandle operations and prove a natural isomorphism with the fundamental biquandle of a knot in the authors' conventions. Distinguish classical knots, virtual knots represented in thickened surfaces, and links; do not silently extend or narrow the original scope.
-/

namespace QuandleResearch.Issue065
noncomputable section

def verifiesTopologicalModel (K : KnotInterface) (model : K.knot → Biquandle) : Prop :=
  ∀ k, (model k).Iso (K.fundamentalBQ k)

/-- Pointwise algebraic criterion for a proposed topological model.
Construction from geometry and naturality are separate obligations. -/
def verifiesPresentedModel {Knot : Type} (diagram : Knot → SemiArcPresentation)
    (model : Knot → StrongBiquandle) : Prop :=
  ∀ k (B : StrongBiquandle) (gen : (diagram k).Arc → B.carrier),
    (diagram k).PresentsBiquandle B gen → (model k).Iso B

end
end QuandleResearch.Issue065
