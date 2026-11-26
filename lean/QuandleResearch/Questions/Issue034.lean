import QuandleResearch.Theory.Interfaces

/-!
# Issue 34: BNN Question 1 (2013) — sections of descending twisted-class towers
https://github.com/555tery/quandle-orbit-series/issues/34

Formalization status: PARTIAL.
Remaining obligation: Native quotient for each tower section and isomorphism-invariant target class now defined; finite-prefix scope and normality hypotheses need source audit. An independent description is the requested answer.

Source and target from the issue:
## Source / explicitly formulated question
Bardakov–Nasybullov–Neshchadim, *Twisted conjugacy classes of the unit element*, Siberian Mathematical Journal (2013), [arXiv:1303.0941](https://arxiv.org/abs/1303.0941), [Russian journal full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=smj&option_lang=eng&paperid=2396&what=fullt), printed p. 25..

## Target
Assume [e]_h={ [x,h]:x∈G } is a subgroup for every h∈G. Starting from G_1=[e]_{h_0}, choose nonidentity h_i∈G_i and set G_{i+1}=[e]_{h_i} until termination. Describe the sections G_i/G_{i+1} of the strictly descending tower in Theorem 2.

## Source context / leads for later audit
Related #2, #7 and #8; distinguish describing the sections from triviality of an intersection.
-/

namespace QuandleResearch.Issue034
noncomputable section

/-- A finite strictly descending portion of the source's tower.
Normality is recorded for each inclusion so the sections use the
native Mathlib quotient group. No termination hypothesis is imposed
on the ambient group; every finite prefix is covered. -/
structure Tower (G : Type) [Group G] (length : Nat) where
  T : Nat → Subgroup G
  h : Nat → G
  start : T 0 = ⊤
  step : ∀ i < length, h i ∈ T i ∧ h i ≠ 1 ∧ T (i+1) < T i ∧
    (T (i+1) : Set G) = innerClass (h i)
  normalStep : ∀ i < length, ((T (i+1)).comap (T i).subtype).Normal

namespace Tower
def sectionSubgroup {G : Type} [Group G] {length : Nat}
    (D : Tower G length) (i : Nat) : Subgroup (D.T i) :=
  (D.T (i+1)).comap (D.T i).subtype
instance sectionNormal {G : Type} [Group G] {length : Nat}
    (D : Tower G length) (i : Fin length) : (D.sectionSubgroup i.val).Normal :=
  D.normalStep i.val i.isLt
abbrev Section {G : Type} [Group G] {length : Nat}
    (D : Tower G length) (i : Fin length) :=
  (D.T i.val) ⧸ D.sectionSubgroup i.val
end Tower

/-- Target class of all groups occurring as sections, up to isomorphism.
A classification should give an independent description of this class. -/
def occursAsSection (S : GroupObject) : Prop :=
  ∃ (G : Type) (_ : Group G) (length : Nat) (D : Tower G length) (i : Fin length),
    AllInner G ∧ Nonempty (S.carrier ≃* D.Section i)
def verifiesClassification (answer : GroupObject → Prop) : Prop :=
  ∀ S, answer S ↔ occursAsSection S
/-- A structural property may also give partial information about the
open-ended description, without claiming a full classification. -/
def verifiesSectionProperty (P : GroupObject → Prop) : Prop :=
  ∀ S, occursAsSection S → P S

end
end QuandleResearch.Issue034
