import QuandleResearch.Theory.Interfaces

/-!
# Issue 39: BNN Question 6 (2013) — twisted classes and the central quotient
https://github.com/555tery/quandle-orbit-series/issues/39

Formalization status: PARTIAL.
Remaining obligation: Restricted central class, canonical quotient, induced map and kernel are explicit; full comparison still to be encoded.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 33..

## Target
For φ∈Aut(G) with [e]_φ a subgroup, describe [e]_φ/[e]_{φ|Z(G)} and its relation to [ē]_{φ̄} in G/Z(G), where φ̄ is induced by φ.

## Source context / leads for later audit
Distinguish the intersection [e]_φ∩Z(G) from the restricted twisted class.
-/

namespace QuandleResearch.Issue039
noncomputable section

/-- Restricted twisted class on the center; deliberately not the
intersection of the full class with the center. -/
def centralTwisted {G : Type} [Group G] (phi : G ≃* G) : Set G :=
  {z | ∃ x ∈ Subgroup.center G, x⁻¹ * phi x = z}
def FactorData (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) : Prop :=
  (H : Set G) = twisted phi ∧
  (N.map H.subtype : Set G) = centralTwisted phi
def inducedOnCenterQuotient (G : Type) [Group G] (phi : G ≃* G)
    (bar : (G ⧸ Subgroup.center G) ≃* (G ⧸ Subgroup.center G)) : Prop :=
  ∀ x, QuotientGroup.mk' (Subgroup.center G) (phi x) =
    bar (QuotientGroup.mk' (Subgroup.center G) x)
def verifiesFactor (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal] (answer : GroupObject) : Prop :=
  FactorData G phi H N → Nonempty ((H ⧸ N) ≃* answer.carrier)
def verifiesImage (G : Type) [Group G] (phi : G ≃* G)
    (bar : (G ⧸ Subgroup.center G) ≃* (G ⧸ Subgroup.center G)) : Prop :=
  inducedOnCenterQuotient G phi bar →
    (QuotientGroup.mk' (Subgroup.center G)) '' twisted phi = twisted bar
/-- Specify the kernel of the canonical map from the full twisted subgroup
to the central quotient. A comparison of H/N with the image additionally
requires the induced quotient homomorphism. -/
def verifiesCanonicalKernel (G : Type) [Group G] (H : Subgroup G) (answer : Subgroup H) : Prop :=
  ((QuotientGroup.mk' (Subgroup.center G)).comp H.subtype).ker = answer

/-- Candidate comparison with the actual twisted subgroup in the central
quotient. The diagram pins down the comparison, not an arbitrary map. -/
def IsCanonicalComparison (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal]
    (bar : (G ⧸ Subgroup.center G) ≃* (G ⧸ Subgroup.center G))
    (K : Subgroup (G ⧸ Subgroup.center G))
    (f : (H ⧸ N) →* K) : Prop :=
  FactorData G phi H N ∧ inducedOnCenterQuotient G phi bar ∧
    (K : Set (G ⧸ Subgroup.center G)) = twisted bar ∧
    ∀ x : H, (f (QuotientGroup.mk' N x)).val =
      QuotientGroup.mk' (Subgroup.center G) x.val

def comparisonSurjective (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal]
    (bar : (G ⧸ Subgroup.center G) ≃* (G ⧸ Subgroup.center G))
    (K : Subgroup (G ⧸ Subgroup.center G)) : Prop :=
  FactorData G phi H N → inducedOnCenterQuotient G phi bar →
    (K : Set (G ⧸ Subgroup.center G)) = twisted bar →
    ∃ f : (H ⧸ N) →* K, IsCanonicalComparison G phi H N bar K f ∧ Function.Surjective f

def comparisonInjective (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal]
    (bar : (G ⧸ Subgroup.center G) ≃* (G ⧸ Subgroup.center G))
    (K : Subgroup (G ⧸ Subgroup.center G))
    (f : (H ⧸ N) →* K) : Prop :=
  IsCanonicalComparison G phi H N bar K f → Function.Injective f

end
end QuandleResearch.Issue039
