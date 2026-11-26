import QuandleResearch.Theory.Interfaces

/-!
# Issue 9: Gonçalves–Nasybullov Problem 4 (2017) — residual nilpotence of finitely generated groups
https://github.com/555tery/quandle-orbit-series/issues/9

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source
Gonçalves–Nasybullov, [arXiv:1705.06842v1](https://arxiv.org/abs/1705.06842v1), Problem 4, p. 17. Is every finitely generated group G with H_g={ [x,g]: x in G } a subgroup for each g residually nilpotent?
-/

namespace QuandleResearch.Issue009
noncomputable section

def question : Prop :=
  ∀ (G : Type) [Group G], FinitelyGenerated G → AllInner G → ResiduallyNilpotent G

end
end QuandleResearch.Issue009
