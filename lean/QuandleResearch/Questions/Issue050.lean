import QuandleResearch.Theory.Interfaces
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat

/-!
# Issue 50: Cattabriga–Matveev–Mulazzani–Nasybullov Conjecture (2018) — complexity of closed nonorientable Seifert fibre spaces
https://github.com/555tery/quandle-orbit-series/issues/50

Formalization status: PARTIAL.
Remaining obligation: Native Mathlib continued fractions, explicit Seifert parameters and capped-base Euler characteristic. Realization of the Seifert space, irreducibility and Matveev complexity are not yet encoded.

Source and target from the issue:
## Source / explicitly formulated problem
Cattabriga, Matveev, Mulazzani, Nasybullov, *On the complexity of non-orientable Seifert fibre spaces*, [arXiv:1704.06721v4, p.36](https://arxiv.org/pdf/1704.06721v4#page=36), Indiana Univ. Math. J. 69 (2020), 421–451. Conjecture at the end of the paper, verified on page image.

## Target
For a nonorientable closed irreducible and RP²-irreducible Seifert fibre space M={b;(ε,g,(t,k));(|);((p₁,q₁),…,(pᵣ,qᵣ))}, prove or disprove c(M)=6(1−χ)+6t+Σⱼ(S(pⱼ,qⱼ)+1), with all parameters and S as defined in the source. χ is the Euler characteristic of the capped base surface, not the orbifold Euler characteristic.

## Source context
Formula (4) is an upper bound; authors note it is attained in all cases in the census available to them. Need lower bounds or counterexamples; preserve irreducibility and nonorientability assumptions.
-/

namespace QuandleResearch.Issue050
noncomputable section

def question {Space : Type} (eligible : Space → Prop) (complexity t : Space → Nat)
    (chi : Space → Int) (exceptional : Space → List (Nat × Nat)) (S : Nat → Nat → Nat) : Prop :=
  ∀ M, eligible M → (complexity M : Int) =
    6 * (1 - chi M) + 6 * (t M : Int) +
      ((exceptional M).map (fun p => S p.1 p.2 + 1)).sum

open scoped BigOperators
/-- Sum of the head and all partial denominators of the canonical
continued fraction, using the terminating rational computation in Mathlib.
For positive coprime p>q this is S(p,q) of the source, p.18. -/
def continuedFractionSum (p q : Nat) : Rat :=
  let g := GenContFract.of ((p : Rat) / (q : Rat))
  g.h + ∑ j ∈ Finset.range (sInf {n : Nat | g.TerminatedAt n}),
    (g.partDens.get? j).getD 0

inductive BaseKind
  | o | o1 | o2 | n | n1 | n2 | n3 | n4
  deriving DecidableEq

def BaseKind.orientableBase : BaseKind → Bool
  | .o | .o1 | .o2 => true
  | _ => false

/-- The closed-space parameters from the conjecture, p.36.
Further normalization constraints on b, epsilon, g, t and k depend
on the source's classification theorem and are not assumed here. -/
structure ClosedParameters where
  b : Int
  epsilon : BaseKind
  genus : Nat
  t : Nat
  k : Nat
  exceptional : List (Nat × Nat)
  validFibers : ∀ pq ∈ exceptional, 0 < pq.2 ∧ pq.2 < pq.1 ∧ Nat.Coprime pq.1 pq.2

def ClosedParameters.chi (P : ClosedParameters) : Int :=
  if P.epsilon.orientableBase then 2 - 2 * (P.genus : Int)
  else 2 - (P.genus : Int)

def ClosedParameters.conjecturedComplexity (P : ClosedParameters) : Rat :=
  6 * (1 - (P.chi : Rat)) + 6 * (P.t : Rat) +
    (P.exceptional.map (fun pq => continuedFractionSum pq.1 pq.2 + 1)).sum

/-- Numeric side of the conjecture is now fixed, not a free S or chi
function. The topological side still needs an actual geometric model. -/
def questionWithParameters {Space : Type}
    (nonorientableClosedIrreducibleRP2Irreducible : Space → Prop)
    (params : Space → ClosedParameters) (complexity : Space → Nat) : Prop :=
  ∀ M, nonorientableClosedIrreducibleRP2Irreducible M →
    (complexity M : Rat) = (params M).conjecturedComplexity

end
end QuandleResearch.Issue050
