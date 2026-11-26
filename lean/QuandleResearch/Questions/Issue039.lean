import QuandleResearch.Theory.Interfaces

/-!
# Issue 39: BNN Question 6 (2013) — twisted classes and the central quotient
https://github.com/555tery/quandle-orbit-series/issues/39

Formalization status: PARTIAL.
Remaining obligation: Construct central quotient, induced automorphism, factor and canonical comparison; current image property is only a component.

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

def verifiesFactor (G : Type) [Group G] (phi : G ≃* G)
    (H : Subgroup G) (N : Subgroup H) [N.Normal]
    (answer : GroupObject) : Prop :=
  (H : Set G) = twisted phi →
  (N.map H.subtype : Set G) = {z | ∃ x : G, (∀ y : G, x*y = y*x) ∧ x⁻¹ * phi x = z} →
  Nonempty ((H ⧸ N) ≃* answer.carrier)
def verifiesImage (G K : Type) [Group G] [Group K]
    (q : G →* K) (phi : G ≃* G) (induced : K ≃* K) : Prop :=
  Function.Surjective q → (∀ x, q (phi x) = induced (q x)) →
  q '' twisted phi = twisted induced

end
end QuandleResearch.Issue039
