import QuandleResearch.Theory.Interfaces

/-!
# Issue 62: Literature correction: Gonçalves–Nasybullov (2017), Example 2 — group is not residually nilpotent
https://github.com/555tery/quandle-orbit-series/issues/62

Formalization status: PARTIAL.
Remaining obligation: Construct the exact matrix group and translation subgroup of Example 2.

Source and target from the issue:
## Source

D. L. Gonçalves and T. Nasybullov, *On groups where the twisted conjugacy class of the unit element is a subgroup*, [arXiv:1705.06842v1](https://arxiv.org/abs/1705.06842v1), 19 May 2017, [PDF, printed p. 17](https://arxiv.org/pdf/1705.06842v1#page=17), Example 2, formula (11) and the sentence immediately preceding Problem 4.

The preprint states: “However, it is residually nilpotent.” The page image was checked on 24 November 2026.

Journal version: Communications in Algebra 47 (2019), 930–944, [DOI:10.1080/00927872.2018.1498873](https://doi.org/10.1080/00927872.2018.1498873), online publication 26 October 2018. The accessible publisher record does not establish whether that sentence survives in the final text.
-/

namespace QuandleResearch.Issue062
noncomputable section

def correction (G : Type) [Group G] (translation : Subgroup G) : Prop :=
  (∃ x ∈ translation, x ≠ 1) ∧
    (∀ n, 2 ≤ n → lowerCentral G (n-1) = translation) ∧ ¬ ResiduallyNilpotent G

end
end QuandleResearch.Issue062
