import QuandleResearch.Theory.Interfaces
import QuandleResearch.Basic.StrongBiquandle

/-!
# Issue 64: Fenn–Ilyutko–Kauffman–Manturov Problem 28A (2014) — explicit model of the free biquandle
https://github.com/555tery/quandle-orbit-series/issues/64

Formalization status: PARTIAL.
Remaining obligation: Explicit descriptive model (as opposed to mere existence) is the requested answer. The source strong-switch category is encoded directly; equivalence with BNS is not assumed.

Source and target from the issue:
## Source / research question
R. Fenn, M. Jordan-Santana, L. H. Kauffman, *Biquandles and virtual links*, Topology and its Applications 145 (2004), 157–175, pp. 171–172. [Article copy](https://www.academia.edu/164480478/Biquandles_and_virtual_links). The question of constructing free biquandles is explicitly recalled by Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, [arXiv:1908.08301v1, §4.3, p.24](https://arxiv.org/pdf/1908.08301v1#page=24), J. Pure Appl. Algebra 226 (2022), 106936.

## Target
Construct an explicit model of the free biquandle on a nonempty set X (in particular on one or finitely many generators), with a proof of its universal property. Distinguish the original request from stronger research goals such as effective normal forms, decidability of equality of terms, and algorithms for operations; these are desirable but should not be attributed to the 2004 authors as literal requirements without further source verification.
-/

namespace QuandleResearch.Issue064
noncomputable section

/-- Existence in the original strong-switch convention. -/
def existsFree : Prop :=
  ∀ X : Type, Nonempty X →
    ∃ (B : StrongBiquandle) (gen : X → B.carrier), B.FreeOn gen
/-- Universal property for a proposed explicit model; the carrier,
switch and generators must be supplied by the model. -/
def verifiesModel (X : Type) (B : StrongBiquandle) (gen : X → B.carrier) : Prop :=
  Nonempty X → B.FreeOn gen

/-- Separate compatibility specification for a proposed BNS model. -/
def verifiesSwitchCorrespondence (B : Biquandle) (S : StrongBiquandle)
    (e : B.carrier ≃ S.carrier) : Prop :=
  ∀ a b, S.switch (e a,e b) =
    (e (B.switchMap a b).1,e (B.switchMap a b).2)

end
end QuandleResearch.Issue064
