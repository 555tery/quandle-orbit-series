import QuandleResearch.Theory.Interfaces

/-!
# Issue 24: Bardakov–Nasybullov Problem 1 (2020) — eliminating nontrivial virtual switches
https://github.com/555tery/quandle-orbit-series/issues/24

Formalization status: PARTIAL.
Remaining obligation: Virtual-switch axioms, canonical twist and invariant construction.

Source and target from the issue:
## Source / explicit published research question
[arXiv:2001.06971, printed p. 17](https://arxiv.org/pdf/2001.06971#page=17). Original PDF formulation checked.

## Target
Given a virtual biquandle 1-switch (S,V) on an algebraic system X, decide whether there is a biquandle switch S′ on the same X whose invariant with the ordinary twist T is equivalent to the invariant of (S,V).
-/

namespace QuandleResearch.Issue024
noncomputable section

def question {X Link Value : Type} (S V : Equiv.Perm (X × X))
    (isVirtual : Equiv.Perm (X × X) → Equiv.Perm (X × X) → Prop)
    (isOrdinary : Equiv.Perm (X × X) → Prop)
    (invariant : Equiv.Perm (X × X) → Equiv.Perm (X × X) → Link → Value)
    (twist : Equiv.Perm (X × X)) : Prop :=
  isVirtual S V → ∃ T, isOrdinary T ∧ ∀ l, invariant S V l = invariant T twist l

end
end QuandleResearch.Issue024
