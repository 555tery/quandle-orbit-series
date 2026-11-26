import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.QuandleCocycles

/-!
# Issue 17: Inoue Problem 2.3 (2013) — classifying link-homotopy by quandle cocycle invariants
https://github.com/555tery/quandle-orbit-series/issues/17

Formalization status: PARTIAL.
Remaining obligation: Inoue C1–C3 and componentwise weight multiplicities are explicit for finite targets. Geometric link-homotopy and Brunnian predicates and infinite-target scope remain to be encoded.

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

end
end QuandleResearch.Issue017
