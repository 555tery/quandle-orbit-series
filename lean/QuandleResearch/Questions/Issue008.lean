import QuandleResearch.Theory.Interfaces

/-!
# Issue 8: Gonçalves–Nasybullov Problem 2 (2017) — intersection of twisted commutator classes
https://github.com/555tery/quandle-orbit-series/issues/8

Formalization status: STATEMENT.
The main statement is expressed using the shared mathematical definitions; source/convention review and compilation remain pending.

Source and target from the issue:
## Source and exact target
Gonçalves–Nasybullov, *On groups where the twisted conjugacy class of the unit element is a subgroup*, [arXiv:1705.06842v1](https://arxiv.org/abs/1705.06842v1), Problem 2, p. 9. Write H_g={ [x,g] : x in G }, with [x,g]=x^{-1}g^{-1}xg. The hypothesis is that H_g is a subgroup for every g (inner automorphisms only). For c_1=g_1, c_{n+1}=[c_n,g_{n+1}], must the intersection of all H_{c_n} be trivial?
-/

namespace QuandleResearch.Issue008
noncomputable section

def question : Prop :=
  ∀ (G : Type) [Group G], AllInner G → ∀ (xs : Nat → G) z,
    (∀ n, z ∈ innerClass (foldComm xs n)) ↔ z = 1

end
end QuandleResearch.Issue008
