import QuandleResearch.Theory.Interfaces

/-!
# Issue 34: BNN Question 1 (2013) — sections of descending twisted-class towers
https://github.com/555tery/quandle-orbit-series/issues/34

Formalization status: PARTIAL.
Remaining obligation: Verify tower hypotheses; descriptive question needs independent structural properties, not an arbitrary predicate.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 25..

## Target
Assume [e]_h={ [x,h]:x∈G } is a subgroup for every h∈G. Starting from G_1=[e]_{h_0}, choose nonidentity h_i∈G_i and set G_{i+1}=[e]_{h_i} until termination. Describe the sections G_i/G_{i+1} of the strictly descending tower in Theorem 2.

## Source context / leads for later audit
Related #2, #7 and #8; distinguish describing the sections from triviality of an intersection.
-/

namespace QuandleResearch.Issue034
noncomputable section

def IsTower {G : Type} [Group G] (T : Nat → Subgroup G) (h : Nat → G) (length : Nat) : Prop :=
  T 0 = ⊤ ∧ ∀ i < length, h i ∈ T i ∧ h i ≠ 1 ∧ T (i+1) < T i ∧
    (T (i+1) : Set G) = innerClass (h i)
def verifiesSectionProperty (P : GroupObject → Prop) (G : Type) [Group G]
    (T : Nat → Subgroup G) (h : Nat → G) (length : Nat) (i : Nat)
    (N : Subgroup (T i)) [N.Normal] : Prop :=
  AllInner G → IsTower T h length → i < length →
    N = (T (i+1)).comap (T i).subtype →
    ∀ S : GroupObject, Nonempty (S.carrier ≃* ((T i) ⧸ N)) → P S

end
end QuandleResearch.Issue034
