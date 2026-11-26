import QuandleResearch.Theory.Interfaces

/-!
# Issue 62: Literature correction: Gonçalves–Nasybullov (2017), Example 2 — group is not residually nilpotent
https://github.com/555tery/quandle-orbit-series/issues/62

Formalization status: PARTIAL.
Remaining obligation: Concrete rational function matrix model; group defined by closure, equality with the source matrix set still requires a construction audit.

Source and target from the issue:
## Source

D. L. Gonçalves and T. Nasybullov, *On groups where the twisted conjugacy class of the unit element is a subgroup*, [arXiv:1705.06842v1](https://arxiv.org/abs/1705.06842v1), 19 May 2017, [PDF, printed p. 17](https://arxiv.org/pdf/1705.06842v1#page=17), Example 2, formula (11) and the sentence immediately preceding Problem 4.

The preprint states: “However, it is residually nilpotent.” The page image was checked on 24 November 2026.

Journal version: Communications in Algebra 47 (2019), 930–944, [DOI:10.1080/00927872.2018.1498873](https://doi.org/10.1080/00927872.2018.1498873), online publication 26 October 2018. The accessible publisher record does not establish whether that sentence survives in the final text.
-/

namespace QuandleResearch.Issue062
noncomputable section

/-- Rational functions regular at T=1 and having value 1 there.
A polynomial numerator/denominator witness avoids a choice of reduced fraction. -/
def isU (F : Type) [Field F] (h : RatFunc F) : Prop :=
  ∃ p q : Polynomial F, q.eval 1 ≠ 0 ∧ p.eval 1 = q.eval 1 ∧
    h = algebraMap (Polynomial F) (RatFunc F) p /
        algebraMap (Polynomial F) (RatFunc F) q
abbrev MatrixUnits (F : Type) [Field F] := (Matrix (Fin 2) (Fin 2) (RatFunc F))ˣ
def matrixSet (F : Type) [Field F] : Set (MatrixUnits F) :=
  {M | M.val 0 0 = 1 ∧ M.val 1 0 = 0 ∧ isU F (M.val 1 1)}
def matrixGroup (F : Type) [Field F] : Subgroup (MatrixUnits F) :=
  Subgroup.closure (matrixSet F)
def translations (F : Type) [Field F] : Subgroup (matrixGroup F) :=
  Subgroup.closure {M | M.val.val 0 0 = 1 ∧ M.val.val 1 0 = 0 ∧ M.val.val 1 1 = 1}
def correction : Prop :=
  ∀ (F : Type) [Field F], (∃ x ∈ translations F, x ≠ 1) ∧
    (∀ n, 2 ≤ n → lowerCentral (matrixGroup F) (n-1) = translations F) ∧
    ¬ ResiduallyNilpotent (matrixGroup F)

end
end QuandleResearch.Issue062
