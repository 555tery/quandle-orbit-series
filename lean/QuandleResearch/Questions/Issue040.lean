import QuandleResearch.Theory.Interfaces

/-!
# Issue 40: BNN Question 7 (2013) — commutator sets restricted to a normal subgroup
https://github.com/555tery/quandle-orbit-series/issues/40

Formalization status: PARTIAL.
Remaining obligation: Equality is a candidate relation, not the whole descriptive question.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 34..

## Target
For N◁G, write [e]_{h,N}={ [x,h]:x∈N }. Assuming every [e]_h is a subgroup, (a) must [e]_{h,N} be a subgroup for h∈G, or for h∈N? (b) how does it relate to N∩[e]_h in both cases?

## Source context / leads for later audit
Gonçalves–Nasybullov Example 1 discusses an answer; audit the separate h∈N qualification, not just the unrestricted case.
-/

namespace QuandleResearch.Issue040
noncomputable section

def subgroupForAll : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], AllInner G →
    ∀ h, IsSubgroupSet (restrictedComm N h)
def subgroupForMembers : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], AllInner G →
    ∀ h ∈ N, IsSubgroupSet (restrictedComm N h)
def equalityForAll : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], AllInner G →
    ∀ h, restrictedComm N h = (N : Set G) ∩ innerClass h
def equalityForMembers : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G) [N.Normal], AllInner G →
    ∀ h ∈ N, restrictedComm N h = (N : Set G) ∩ innerClass h

end
end QuandleResearch.Issue040
