import QuandleResearch.Theory.Interfaces

/-!
# Issue 5: Research: extend Question 5.7 to racks and derived racks of YBE solutions
https://github.com/555tery/quandle-orbit-series/issues/5

Formalization status: PARTIAL.
Remaining obligation: Source convention and rack fibre closure; candidate research direction, not a published theorem.

Source and target from the issue:
## Motivation
The main proof of [Question 5.7](https://github.com/555tery/quandle-orbit-series/tree/main/question-5-7) relies on equivariance of translations and finite-defect subnormality, suggesting an extension beyond idempotent quandles.

## Critical issue
For a rack epimorphism pi:X -> Y, the fibre pi^{-1}(b) need not be a subrack unless b ▷ b=b. Thus an unrestricted statement using d_{pi^{-1}(b)} is not even well-defined in general. Do not treat the proposed rack theorem as proved.
-/

namespace QuandleResearch.Issue005
noncomputable section

def question (X Y : Rack) (f : X.carrier → Y.carrier) : Prop :=
  X.Hom Y f → Function.Surjective f → ∀ x, Y.op (f x) (f x) = f x →
  ∀ a b c, X.PointDepth Set.univ x a → Y.PointDepth Set.univ (f x) b →
    X.PointDepth {z | f z = f x} x c → a ≤ b+c

end
end QuandleResearch.Issue005
