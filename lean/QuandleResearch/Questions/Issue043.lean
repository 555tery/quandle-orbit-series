import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 43: Bardakov et al. Problem 1 (2020) — kernel of the flat virtual braid representation theta
https://github.com/555tery/quandle-orbit-series/issues/43

Formalization status: PARTIAL.
Remaining obligation: Concrete FVB and theta images from issue; verify y-generator action and right-action convention against source.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov et al. (including T. Nasybullov), *Representations of flat virtual braids which do not preserve the forbidden relations*, [arXiv:2010.03162v1](https://arxiv.org/pdf/2010.03162v1), printed p. 9..

## Target
Determine ker(θ) for the representation θ:FVB_n→Aut(F_{2n}) in Theorem 1, defined by σ_i: x_i↦x_{i+1}y_{i+1}, x_{i+1}↦x_i y_{i+1}^{−1}, and ρ_i swapping x_i,x_{i+1} and y_i,y_{i+1}, fixing the other generators.

## Source context / leads for later audit
Corollary 1 gives a lower bound by the normal closure of (ρ_iσ_{i+1})^6 and an upper bound FVP_n∩FH_n. The case n=2 is handled in Proposition 7.
-/

namespace QuandleResearch.Issue043
noncomputable section

open Braids
def x {n : Nat} (j : Fin n) : FreeGroup (Bool × Fin n) := FreeGroup.of (false,j)
def y {n : Nat} (j : Fin n) : FreeGroup (Bool × Fin n) := FreeGroup.of (true,j)
def thetaImage {n : Nat} (i : Index n) (a : Bool × Fin n) : FreeGroup (Bool × Fin n) :=
  if a.1 then y a.2 else
  if a.2 = left i then x (right i) * y (right i) else
  if a.2 = right i then x (left i) * (y (right i))⁻¹ else x a.2
def virtualImage {n : Nat} (i : Index n) (a : Bool × Fin n) : FreeGroup (Bool × Fin n) :=
  FreeGroup.of (a.1, transposition i a.2)
def IsTheta {n : Nat}
    (f : FVB n →* (FreeGroup (Bool × Fin n) ≃* FreeGroup (Bool × Fin n))) : Prop :=
  ∀ i : Index n, ∀ a : Bool × Fin n,
    (f (PresentedGroup.of (rels := flatRels n) (false,i))).symm (FreeGroup.of a) = thetaImage i a ∧
    (f (PresentedGroup.of (rels := flatRels n) (true,i))).symm (FreeGroup.of a) = virtualImage i a
def verifiesKernel (answer : ∀ n, Subgroup (FVB n)) : Prop :=
  ∀ n, 2 ≤ n → ∃ f : FVB n →* (FreeGroup (Bool × Fin n) ≃* FreeGroup (Bool × Fin n)),
    IsTheta f ∧ f.ker = answer n

end
end QuandleResearch.Issue043
