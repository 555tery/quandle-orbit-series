import QuandleResearch.Theory.Interfaces

/-!
# Issue 55: Bardakov–Nasybullov–Singh §4.3 (2019) — freeness of the associated quandle of a free biquandle
https://github.com/555tery/quandle-orbit-series/issues/55

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source / explicitly stated conjecture
Bardakov–Nasybullov–Singh, *General constructions of biquandles and their symmetries*, arXiv:1908.08301v1 (2019), J. Pure Appl. Algebra 226 (2022), 106936, DOI 10.1016/j.jpaa.2021.106936, [printed p.24, after Proposition 4.24](https://arxiv.org/pdf/1908.08301v1#page=24). The conjectural construction from a free quandle was checked in the preprint; the full journal wording remains unverified.

## Target
Prove or disprove that the free biquandle FB(X) can be obtained by a biquandle structure on a free quandle; equivalently, that its associated quandle Q(FB(X)) is free. The conjectural sentence does not specify the rank of the underlying free quandle.

The older explicit-model question of Fenn–Jordan-Santana–Kauffman (2004) is now tracked separately in #64. An independent combinatorial model and algorithms for the biquandle operations are NOT additional closure requirements for #55 unless the original source establishes otherwise.
-/

namespace QuandleResearch.Issue055
noncomputable section

def question : Prop :=
  ∀ (X : Type) (B : Biquandle) (gen : X → B.carrier), B.FreeOn gen → B.associated.IsFree

end
end QuandleResearch.Issue055
