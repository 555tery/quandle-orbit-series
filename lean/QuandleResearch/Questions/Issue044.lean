import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 44: Bardakov et al. Problem 2 (2020) — kernel of the integral flat virtual braid representation Delta
https://github.com/555tery/quandle-orbit-series/issues/44

Formalization status: PARTIAL.
Remaining obligation: Theorem 3 and Corollary 3 generator matrices transcribed directly from printed p. 12 (arXiv:2010.03162v1); remaining obligation is source-convention/typecheck review, not a kernel solution.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov et al. (including T. Nasybullov), *Representations of flat virtual braids which do not preserve the forbidden relations*, [arXiv:2010.03162v1](https://arxiv.org/pdf/2010.03162v1), printed p. 13..

## Target
Determine ker(Δ) for the specific representation Δ:FVB_n→GL_{3n}(Z) in Theorem 3. Use the matrices defined in that theorem, not the different representation Θ.

## Source context / leads for later audit
Theorem 3 distinguishes Δ from Θ by the elements (ρ_iσ_{i+1})^6. The original problem is about the entire kernel.
-/

namespace QuandleResearch.Issue044
noncomputable section

open Braids

/-- Basis (strand, kind), where kind 0=e, 1=f, 2=g.
Rows give the images of basis vectors, as in Corollary 3 of the
source (arXiv:2010.03162v1, printed p. 12). -/
abbrev Basis (n : Nat) := Fin n × Fin 3
abbrev Target (n : Nat) := (Matrix (Basis n) (Basis n) Int)ˣ
def coeff {n : Nat} (a b : Basis n) : Int := if a = b then 1 else 0
def sigmaEntry {n : Nat} (i : Index n) (a b : Basis n) : Int :=
  if a = (left i, 0) then coeff (right i, 0) b + coeff (left i, 2) b
  else if a = (right i, 0) then coeff (left i, 0) b - coeff (right i, 2) b
  else if a = (left i, 2) then coeff (right i, 2) b
  else if a = (right i, 2) then coeff (left i, 2) b
  else coeff a b
def rhoEntry {n : Nat} (i : Index n) (a b : Basis n) : Int :=
  coeff (transposition i a.1, a.2) b

def IsDelta {n : Nat} (d : FVB n →* Target n) : Prop :=
  ∀ (i : Index n) (a b : Basis n),
    (d (PresentedGroup.of (rels := flatRels n) (false,i))).val a b = sigmaEntry i a b ∧
    (d (PresentedGroup.of (rels := flatRels n) (true,i))).val a b = rhoEntry i a b
/-- Membership in the specific kernel, independent of a proposed answer.
The map is uniquely pinned down by its generator images. -/
def targetKernel {n : Nat} (x : FVB n) : Prop :=
  ∃ d : FVB n →* Target n, IsDelta d ∧ x ∈ d.ker
def verifiesKernel (answer : ∀ n, Subgroup (FVB n)) : Prop :=
  ∀ n, 2 ≤ n →
    ∃ d : FVB n →* Target n, IsDelta d ∧ d.ker = answer n

end
end QuandleResearch.Issue044
