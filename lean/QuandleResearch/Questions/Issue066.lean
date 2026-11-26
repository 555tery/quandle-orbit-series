import QuandleResearch.Theory.Interfaces

/-!
# Issue 66: Fenn–Ilyutko–Kauffman–Manturov Problem 28C (2014) — existence of free partial biquandles
https://github.com/555tery/quandle-orbit-series/issues/66

Formalization status: PARTIAL.
Remaining obligation: The journal Problem 28 does not specify the partial-biquandle category. Native PartialEquiv-based candidate semantics are recorded separately; they are not asserted to be the authors' intended category.

Source and target from the issue:
## Source / explicitly stated problem
R. Fenn, D. P. Ilyutko, L. H. Kauffman, V. O. Manturov, *Unsolved problems in virtual knot theory and combinatorial knot theory*, Banach Center Publications 103 (2014), 9–61, §8.1, Problem 28, printed p. 34. [Journal PDF, p.34](https://www.impan.pl/shop/en/publication/transaction/download/product/86155#page=26), [DOI](https://doi.org/10.4064/bc103-0-1), [arXiv v1, p.31](https://arxiv.org/pdf/1409.2823v1#page=31). Journal and preprint page images verified. The letters A/B/C are local tracking labels, not original numbering.

Original third question asks whether free partial biquandles exist; the authors suggest a negative answer.

## Target
Determine whether the free partial biquandle exists on a given set of generators, in the intended meaning of 'partial biquandle' in the 2014 paper. The precise category, admissible domains of operations, morphisms, and universal property must be established from the authors' definitions and earlier works before giving a yes/no answer.
-/

namespace QuandleResearch.Issue066
noncomputable section

def question (I : PartialCategoryInterface) : Prop :=
  ∀ X : Type, ∃ (A : PartialOperations) (gen : X → A.carrier), I.FreeOn A gen

/-- Candidate interpretation only: partial invertible switches with a
specified source domain. Mathlib's PartialEquiv supplies all inverse laws.
The 2014 Problem 28 does not define this category. -/
structure PartialSwitch where
  carrier : Type
  swap : PartialEquiv (carrier × carrier) (carrier × carrier)

namespace PartialSwitch
def WeakHom (A B : PartialSwitch) (f : A.carrier → B.carrier) : Prop :=
  (∀ p ∈ A.swap.source,
    (f p.1,f p.2) ∈ B.swap.source ∧
      B.swap (f p.1,f p.2) = (f (A.swap p).1,f (A.swap p).2)) ∧
  (∀ p ∈ A.swap.target,
    (f p.1,f p.2) ∈ B.swap.target ∧
      B.swap.symm (f p.1,f p.2) = (f (A.swap.symm p).1,f (A.swap.symm p).2))

def ReflectingHom (A B : PartialSwitch) (f : A.carrier → B.carrier) : Prop :=
  A.WeakHom B f ∧
    (∀ p : A.carrier × A.carrier, (f p.1,f p.2) ∈ B.swap.source → p ∈ A.swap.source) ∧
    (∀ p : A.carrier × A.carrier, (f p.1,f p.2) ∈ B.swap.target → p ∈ A.swap.target)

/-- These universal properties are not equivalent by definition.
Partial Yang–Baxter and type-I axioms must be fixed before either
candidate is promoted to an original-problem formalization. -/
def FreeOnWeak (admissible : PartialSwitch → Prop) (A : PartialSwitch)
    {X : Type} (gen : X → A.carrier) : Prop :=
  admissible A ∧ ∀ (B : PartialSwitch), admissible B → ∀ f : X → B.carrier,
    ∃! h : A.carrier → B.carrier, A.WeakHom B h ∧ ∀ x, h (gen x) = f x

def FreeOnReflecting (admissible : PartialSwitch → Prop) (A : PartialSwitch)
    {X : Type} (gen : X → A.carrier) : Prop :=
  admissible A ∧ ∀ (B : PartialSwitch), admissible B → ∀ f : X → B.carrier,
    ∃! h : A.carrier → B.carrier, A.ReflectingHom B h ∧ ∀ x, h (gen x) = f x
end PartialSwitch

end
end QuandleResearch.Issue066
