import QuandleResearch.Theory.Interfaces

/-!
# Issue 20: Bardakov–Nasybullov–Singh Remark 8.4 (2017) — quasi-inner automorphisms of even dihedral quandles
https://github.com/555tery/quandle-orbit-series/issues/20

Formalization status: PARTIAL.
Remaining obligation: The dihedral operation, inner group and orbit-preserving condition are explicit; verify the precise QInn convention against the original article.

Source and target from the issue:
## Source / explicit published research question
[arXiv:1705.10607v3, printed p. 16](https://arxiv.org/pdf/1705.10607v3#page=16). Original PDF formulation checked.

## Target
Determine whether Inn(R_{2n}) = QInn(R_{2n}) for n > 2.
-/

namespace QuandleResearch.Issue020
noncomputable section

/-- Orbit-preserving automorphisms of the even dihedral quandle. The
identification of this definition with QInn in the source is to be audited. -/
def dihedralOp {m : Nat} (x y : ZMod m) : ZMod m := 2*y-x
def isAut {m : Nat} (f : Equiv.Perm (ZMod m)) : Prop :=
  ∀ x y, f (dihedralOp x y) = dihedralOp (f x) (f y)
def isInner {m : Nat} (f : Equiv.Perm (ZMod m)) : Prop :=
  f ∈ Subgroup.closure {e : Equiv.Perm (ZMod m) | ∃ y, ∀ x, e x = dihedralOp x y}
def isQuasiInner {m : Nat} (f : Equiv.Perm (ZMod m)) : Prop :=
  isAut f ∧ ∀ x, ∃ e : Equiv.Perm (ZMod m), isInner e ∧ e x = f x
def question : Prop :=
  ∀ n, 2 < n → ∀ f : Equiv.Perm (ZMod (2*n)), isInner f ↔ isQuasiInner f

end
end QuandleResearch.Issue020
