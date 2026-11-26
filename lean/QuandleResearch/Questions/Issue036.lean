import QuandleResearch.Theory.Interfaces

/-!
# Issue 36: BNN Question 3 (2013) — abelian-by-cyclic and abelian-by-abelian groups
https://github.com/555tery/quandle-orbit-series/issues/36

Formalization status: PARTIAL.
Remaining obligation: Literal and nonabelian versions separated; check authors' intended scope.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 29..

## Target
If G is an extension of an abelian group by a cyclic group (or by an abelian group), must there exist h∈G such that [e]_h is not a subgroup? Preserve both cases; assess intended nonabelian restriction.

## Source context / leads for later audit
Gonçalves–Nasybullov Example 1 explicitly discusses this question; next audit will compare scope.
-/

namespace QuandleResearch.Issue036
noncomputable section

def abelianByCyclic : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal],
    Abelian N → Cyclic (G ⧸ N) → ¬ AllInner G
def abelianByAbelian : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal],
    Abelian N → Abelian (G ⧸ N) → ¬ AllInner G
def nonabelianVersion : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal],
    ¬ Abelian G → Abelian N → Abelian (G ⧸ N) → ¬ AllInner G

end
end QuandleResearch.Issue036
