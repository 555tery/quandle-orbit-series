import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.VirtualSwitches

/-!
# Issue 24: Bardakov–Nasybullov Problem 1 (2020) — eliminating nontrivial virtual switches
https://github.com/555tery/quandle-orbit-series/issues/24

Formalization status: PARTIAL.
Remaining obligation: Virtual-switch axioms, twist and concrete group-valued invariant now defined. General algebraic systems, geometric diagrams and precise equivalence of invariants still require audit.

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

/-- Group-valued specialization of the source question.
Equivalence is interpreted here as equality of the partitions of links
induced by isomorphism of the group-valued invariants. Other algebraic
systems and the exact source convention are still outstanding. -/
def groupCase (G : Type) [Group G] (gen : Nat → G)
    {Link : Type} (diagram : Link → SemiArcPresentation) : Prop :=
  IsSourceGenerators G gen →
    ∀ (S V : Equiv.Perm (G × G)) (s v : GroupWords),
      IsVirtualBiquandleSwitch S V → s.Realizes S → v.Realizes V →
      ∃ (T : Equiv.Perm (G × G)) (t : GroupWords),
        IsVirtualBiquandleSwitch T (Equiv.prodComm G G) ∧ t.Realizes T ∧
        ∀ l m : Link,
          (Nonempty ((diagram l).GroupInvariant G gen s v ≃*
                     (diagram m).GroupInvariant G gen s v) ↔
           Nonempty ((diagram l).GroupInvariant G gen t GroupWords.twist ≃*
                     (diagram m).GroupInvariant G gen t GroupWords.twist))

end
end QuandleResearch.Issue024
