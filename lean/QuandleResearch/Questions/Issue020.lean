import QuandleResearch.Theory.Interfaces

/-!
# Issue 20: Bardakov–Nasybullov–Singh Remark 8.4 (2017) — quasi-inner automorphisms of even dihedral quandles
https://github.com/555tery/quandle-orbit-series/issues/20

Formalization status: PARTIAL.
Remaining obligation: Construct dihedral quandles and quasi-inner group; verify source conventions.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1705.10607v3, printed p. 16](https://arxiv.org/pdf/1705.10607v3#page=16). Original PDF formulation checked.

## Target
Determine whether Inn(R_{2n}) = QInn(R_{2n}) for n > 2.
-/

namespace QuandleResearch.Issue020
noncomputable section

def question (dihedral : Nat → Quandle)
    (quasiInner : ∀ n, Subgroup (Equiv.Perm (dihedral n).carrier)) : Prop :=
  ∀ n, 2 < n → (dihedral (2*n)).Inn = quasiInner (2*n)

end
end QuandleResearch.Issue020
