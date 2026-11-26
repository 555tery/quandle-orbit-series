import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 60: Gassner faithfulness problem for P_n, n≥4 — recorded by Bardakov–Nasybullov (2019)
https://github.com/555tery/quandle-orbit-series/issues/60

Formalization status: PARTIAL.
Remaining obligation: Laurent ring, Artin action and abelianized Fox derivatives characterized by generator values and product rule; matrix convention and existence/typechecking still require audit.

Source and target from the issue:
## Source / explicitly stated problem
Bardakov–Nasybullov, *Multi-switches and representations of braid groups*, arXiv:1907.09230v1 (2019), J. Algebra Appl. 23 (2024), 2430003, [printed p.16, §5, formula (11)](https://arxiv.org/pdf/1907.09230v1#page=16). Verified on PDF page image. Classical question explicitly stated as unresolved, not attributed to Nasybullov.

## Target
For n>3, determine whether the Gassner representation of the classical pure braid group P_n over Z[t_1^{±1},…,t_n^{±1}] is faithful. Use the Fox-derivative construction and generator matrices of formula (11).

## Source context / scope
Do not conflate Gassner with the Burau specialization t_1=…=t_n or with its extensions to welded/virtual braid groups. Search each n and possible general reduction in later audit.
-/

namespace QuandleResearch.Issue060
noncomputable section

open Braids
/-- Laurent ring Z[t_1^±1,...,t_n^±1] as a group algebra. -/
abbrev Laurent (n : Nat) := AddMonoidAlgebra Int (Fin n → Int)
def variableMonomial {n : Nat} (i : Fin n) : Laurent n :=
  Finsupp.single (fun j => if j = i then 1 else 0) 1
/-- Abelianization evaluated as Laurent monomials, specified on each
free generator. This condition uniquely determines the group map. -/
def IsAbel {n : Nat} (a : FreeGroup (Fin n) →* (Laurent n)ˣ) : Prop :=
  ∀ i, (a (FreeGroup.of i)).val = variableMonomial i
/-- Abelianized Fox derivative characterized by the product rule
and values on free generators, avoiding an arbitrary matrix representation. -/
def IsFox {n : Nat} (a : FreeGroup (Fin n) →* (Laurent n)ˣ)
    (D : Fin n → FreeGroup (Fin n) → Laurent n) : Prop :=
  (∀ i j, D i (FreeGroup.of j) = if i = j then 1 else 0) ∧
  (∀ i u v, D i (u*v) = D i u + (a u).val * D i v)
def IsArtin {n : Nat} (A : B n →* (FreeGroup (Fin n) ≃* FreeGroup (Fin n))) : Prop :=
  ∀ (i : Index n) (j : Fin n),
    (A (PresentedGroup.of (rels := classicalRels n) i)).symm (FreeGroup.of j) = artinImage i j
def IsGassner {n : Nat}
    (A : B n →* (FreeGroup (Fin n) ≃* FreeGroup (Fin n)))
    (D : Fin n → FreeGroup (Fin n) → Laurent n)
    (G : P n →* (Matrix (Fin n) (Fin n) (Laurent n))ˣ) : Prop :=
  ∀ g i j, (G g).val i j = D j ((A g.val).symm (FreeGroup.of i))
def question : Prop :=
  ∀ n, 3 < n →
    ∃ (a : FreeGroup (Fin n) →* (Laurent n)ˣ)
      (D : Fin n → FreeGroup (Fin n) → Laurent n)
      (A : B n →* (FreeGroup (Fin n) ≃* FreeGroup (Fin n)))
      (G : P n →* (Matrix (Fin n) (Fin n) (Laurent n))ˣ),
      IsAbel a ∧ IsFox a D ∧ IsArtin A ∧ IsGassner A D G ∧ Function.Injective G

end
end QuandleResearch.Issue060
