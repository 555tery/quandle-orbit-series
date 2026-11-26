import QuandleResearch.Theory.Interfaces

/-!
# Issue 42: Gonçalves–Nasybullov Problem 3 (2017) — abelianness of finite abelian-by-C_p groups
https://github.com/555tery/quandle-orbit-series/issues/42

Formalization status: PARTIAL.
Remaining obligation: Verify source hypothesis (automorphisms versus inner automorphisms) and finite-group scope.

Source and target from the issue:
## Source / explicitly formulated question
Gonçalves–Nasybullov, *On groups where the twisted conjugacy class of the unit element is a subgroup*, [arXiv:1705.06842v1](https://arxiv.org/pdf/1705.06842v1), printed p. 14..

## Target
Let p be an odd prime and 1→A→G→C_p→1 an extension with A finite abelian. Suppose [e]_φ is a subgroup of G for every φ∈Aut(G). Is G abelian?

## Source context / leads for later audit
Theorem 3 gives class ≤2; Corollary 4 handles elementary abelian A. Do not replace all automorphisms by inner ones. Related #8–10.
-/

namespace QuandleResearch.Issue042
noncomputable section

def question : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal] (p : Nat),
    Nat.Prime p → Abelian N → Nat.card (G ⧸ N) = p → AllInner G → Abelian G

end
end QuandleResearch.Issue042
