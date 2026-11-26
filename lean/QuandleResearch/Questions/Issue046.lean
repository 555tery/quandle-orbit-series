import QuandleResearch.Theory.Interfaces

/-!
# Issue 46: Nasybullov Problem 1 (2017) — finite Reidemeister numbers of GL_n and SL_n
https://github.com/555tery/quandle-orbit-series/issues/46

Formalization status: PARTIAL.
Remaining obligation: Construct GL_n, SL_n, algebraically closed characteristic-zero field and entrywise automorphism sets; check dimension bounds separately.

Source and target from the issue:
## Source / explicitly formulated question
Nasybullov, *Reidemeister spectrum of special and general linear groups over some fields contains 1*, [arXiv:1708.06280v2, p.10](https://arxiv.org/pdf/1708.06280v2#page=10). Verified against the original PDF page.

## Target
Let F be algebraically closed of characteristic zero and ψ∈Aut(F) induce an entrywise automorphism φ of SL_n(F) or GL_n(F), with finite Reidemeister number R(φ). Can R(φ) be bounded in terms of n? Must R(φ)=1? Preserve both groups and both parts.

## Source context / leads for later audit
The paper constructs field automorphisms with R=1 under infinite transcendence degree; this does not imply the assertion about every automorphism of finite R. Search difference algebra and algebraic group results in subsequent audit.
-/

namespace QuandleResearch.Issue046
noncomputable section

def bound (GL SL : Nat → GroupObject)
    (gl : ∀ n, Set ((GL n).carrier ≃* (GL n).carrier))
    (sl : ∀ n, Set ((SL n).carrier ≃* (SL n).carrier)) : Prop :=
  ∃ b : Nat → Nat, (∀ n f, f ∈ gl n → FiniteReidemeister f → ReidemeisterAtMost f (b n)) ∧
    (∀ n f, f ∈ sl n → FiniteReidemeister f → ReidemeisterAtMost f (b n))
def alwaysOne (G : GroupObject) (entrywise : Set (G.carrier ≃* G.carrier)) : Prop :=
  ∀ f ∈ entrywise, FiniteReidemeister f → ReidemeisterAtMost f 1

end
end QuandleResearch.Issue046
