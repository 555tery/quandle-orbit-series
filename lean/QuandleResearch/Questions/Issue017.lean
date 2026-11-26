import QuandleResearch.Theory.Interfaces

/-!
# Issue 17: Inoue Problem 2.3 (2013) — classifying link-homotopy by quandle cocycle invariants
https://github.com/555tery/quandle-orbit-series/issues/17

Formalization status: PARTIAL.
Remaining obligation: Link-homotopy, actual cocycle invariants and unlink/Brunnian constructions.

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

end
end QuandleResearch.Issue017
