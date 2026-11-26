import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.QuandleCocycles
import QuandleResearch.Theory.GeometricLinks

/-!
# Issue 17: Inoue Problem 2.3 (2013) — classifying link-homotopy by quandle cocycle invariants
https://github.com/555tery/quandle-orbit-series/issues/17

Formalization status: PARTIAL.
Remaining obligation: Continuous link-homotopy and disjoint spanning disks now explicit for ordered parametrized links. The tame-category equivalence and the link-to-diagram correspondence remain unverified.

Source and target from the issue:
## Source / published problem
A. Inoue, §2 in T. Ohtsuki (ed.), [*Problems on Low-dimensional Topology, 2013*](https://www.kurims.kyoto-u.ac.jp/~ildt/2013/prob13.pdf), p. 5, Problem 2.3.
Classify links up to link-homotopy using quandle cocycle invariants. The author specifically asks about distinguishing trivial n-component links from Brunnian links.
-/

namespace QuandleResearch.Issue017
noncomputable section

def complete {Link Test Value : Type} (homotopic : Link → Link → Prop)
    (value : Test → Link → Value) : Prop :=
  ∀ l m, homotopic l m ↔ ∀ t, value t l = value t m
def brunnianCase {Link Test Value : Type} (homotopic : Link → Link → Prop)
    (value : Test → Link → Value) (brunnian : Link → Prop) (unlink : Link → Link) : Prop :=
  ∀ l, brunnian l → ¬ homotopic l (unlink l) → ∃ t, value t l ≠ value t (unlink l)

/-- The actual Inoue invariants (finite quandle targets), rather than
arbitrary functions. The geometric link-homotopy and Brunnian predicates
still require a separate topology formalization. -/
def completeFiniteTargets {n : Nat} {Link : Type}
    (diagram : Link → ArcPresentation n) (homotopic : Link → Link → Prop) : Prop :=
  ∀ l m, homotopic l m ↔ SameCocycleData (diagram l) (diagram m)

def distinguishesBrunnianFiniteTargets {n : Nat} {Link : Type}
    (diagram : Link → ArcPresentation n) (homotopic : Link → Link → Prop)
    (brunnian : Link → Prop) (unlink : Link) : Prop :=
  ∀ l, brunnian l → ¬ homotopic l unlink →
    ¬ SameCocycleData (diagram l) (diagram unlink)

/-- Geometric finite-target formulation. The map to arc presentations
must actually come from link diagrams; it is not arbitrary in the source.
This remaining correspondence is recorded rather than asserted. -/
def geometricCompleteness (n : Nat)
    (diagram : GeometricLink n → ArcPresentation n) : Prop :=
  ∀ L M, L.LinkHomotopic M ↔ SameCocycleData (diagram L) (diagram M)

def geometricBrunnian (n : Nat)
    (diagram : GeometricLink n → ArcPresentation n) : Prop :=
  ∀ L U, L.Brunnian → U.Unlink → ¬ L.LinkHomotopic U →
    ¬ SameCocycleData (diagram L) (diagram U)

/-- Literal distinction question, without assuming nontrivial
link-homotopy. Kept separate to preserve the source's wording. -/
def literalBrunnian (n : Nat)
    (diagram : GeometricLink n → ArcPresentation n) : Prop :=
  ∀ L U, L.Brunnian → U.Unlink →
    ¬ SameCocycleData (diagram L) (diagram U)

end
end QuandleResearch.Issue017
