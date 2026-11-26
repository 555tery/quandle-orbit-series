import QuandleResearch.Theory.Interfaces

/-!
# Issue 64: Fenn–Ilyutko–Kauffman–Manturov Problem 28A (2014) — explicit model of the free biquandle
https://github.com/555tery/quandle-orbit-series/issues/64

Formalization status: PARTIAL.
Remaining obligation: Existence and candidate universal property distinguished; strong-switch convention and explicit model requirement remain.

Source and target from the issue:
## Source / research question
R. Fenn, M. Jordan-Santana, L. H. Kauffman, *Biquandles and virtual links*, Topology and its Applications 145 (2004), 157–175, pp. 171–172. [Article copy](https://www.academia.edu/164480478/Biquandles_and_virtual_links). The question of constructing free biquandles is explicitly recalled by Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, [arXiv:1908.08301v1, §4.3, p.24](https://arxiv.org/pdf/1908.08301v1#page=24), J. Pure Appl. Algebra 226 (2022), 106936.

## Target
Construct an explicit model of the free biquandle on a nonempty set X (in particular on one or finitely many generators), with a proof of its universal property. Distinguish the original request from stronger research goals such as effective normal forms, decidability of equality of terms, and algorithms for operations; these are desirable but should not be attributed to the 2004 authors as literal requirements without further source verification.
-/

namespace QuandleResearch.Issue064
noncomputable section

/-- Existence statement; a descriptive answer should exhibit the carrier,
operations and generators rather than merely establish this proposition. -/
def existsFree : Prop :=
  ∀ X : Type, Nonempty X → ∃ (B : Biquandle) (gen : X → B.carrier), B.FreeOn gen
def verifiesModel (X : Type) (B : Biquandle) (gen : X → B.carrier) : Prop :=
  Nonempty X → B.FreeOn gen

end
end QuandleResearch.Issue064
