import QuandleResearch.Theory.Interfaces

/-!
# Issue 32: BNN Conjecture 1 (2013) — nilpotence and finite-generation abelianness
https://github.com/555tery/quandle-orbit-series/issues/32

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 21; also Kourovka Notebook 18.14 and Gonçalves–Nasybullov, *On groups where the twisted conjugacy class of the unit element is a subgroup*, [arXiv:1705.06842v1](https://arxiv.org/pdf/1705.06842v1), p. 4..

## Target
Let [e]_φ={g⁻¹φ(g):g∈G}. If this is a subgroup for every φ∈Aut(G), must G be nilpotent? If G is also finitely generated, must it be abelian? Track both clauses separately.

## Source context / leads for later audit
Related #8–10 use inner automorphisms only. A direct later candidate answer is [Nicotera (2024), DOI 10.1007/s00013-024-02025-6](https://doi.org/10.1007/s00013-024-02025-6); assess both clauses in the next audit.
-/

namespace QuandleResearch.Issue032
noncomputable section

def nilpotence : Prop := ∀ (G : Type) [Group G], AllAut G → Nilpotent G
def fgAbelianness : Prop := ∀ (G : Type) [Group G], AllAut G → FinitelyGenerated G → Abelian G

end
end QuandleResearch.Issue032
