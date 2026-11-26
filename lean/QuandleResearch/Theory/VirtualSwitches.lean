import QuandleResearch.Theory.LinkPresentations
import QuandleResearch.Theory.BraidGroups

/-! Bardakov–Nasybullov, arXiv:2001.06971v1, §§3–4.
The switch laws are independent of a choice of ambient algebraic system.
The group specialization below uses actual group words and Mathlib
presented groups, rather than arbitrary invariants. -/
namespace QuandleResearch
noncomputable section

def IsBiquandleSwitch {X : Type} (S : Equiv.Perm (X × X)) : Prop :=
  BraidEquation S ∧
  (∀ a, Function.Bijective (fun b => (S (a,b)).1)) ∧
  (∀ b, Function.Bijective (fun a => (S (a,b)).2)) ∧
  (∀ a, ∃! b, S (a,b) = (a,b)) ∧
  (∀ b, ∃! a, S (a,b) = (a,b))

def IsVirtualBiquandleSwitch {X : Type}
    (S V : Equiv.Perm (X × X)) : Prop :=
  IsBiquandleSwitch S ∧ BraidEquation V ∧ Function.Involutive V ∧
    ∀ p, switch12 V (switch23 S (switch12 V p)) =
      switch23 V (switch12 S (switch23 V p))

/-- A pair of words on two variables, false and true, evaluated by the
native universal map from the free group. -/
abbrev GroupWords := FreeGroup Bool × FreeGroup Bool
namespace GroupWords

def eval {G : Type*} [Group G] (w : GroupWords) (x y : G) : G × G :=
  let e := FreeGroup.lift (fun b : Bool => if b then y else x)
  (e w.1, e w.2)

def Realizes {G : Type} [Group G] (w : GroupWords)
    (S : Equiv.Perm (G × G)) : Prop :=
  ∀ x y, S (x,y) = w.eval x y

def twist : GroupWords := (FreeGroup.of true, FreeGroup.of false)

end GroupWords

/-- Countable generating family with finite-support permutations
extending to automorphisms, as in Section 4 for m=0. -/
def IsSourceGenerators (G : Type) [Group G] (gen : Nat → G) : Prop :=
  Subgroup.closure (Set.range gen) = ⊤ ∧
  ∀ e : Equiv.Perm Nat, Set.Finite {i | e i ≠ i} →
    ∃ a : G ≃* G, ∀ i, a (gen i) = gen (e i)

namespace SemiArcPresentation
/-- Relations from X^(n), together with two crossing relators.
At negative crossings the inputs and outputs are interchanged,
so inverse words do not have to be chosen separately. -/
def groupRels (D : SemiArcPresentation) (G : Type) [Group G]
    (gen : Nat → G) (S V : GroupWords) : Set (FreeGroup D.Arc) :=
  {w | FreeGroup.lift (fun a : D.Arc => gen a.val) w = 1} ∪
  {w | ∃ c : D.Crossing,
    let neg := D.kind c = .negative
    let a := FreeGroup.of (if neg then D.outLeft c else D.inLeft c)
    let b := FreeGroup.of (if neg then D.outRight c else D.inRight c)
    let u := FreeGroup.of (if neg then D.inLeft c else D.outLeft c)
    let v := FreeGroup.of (if neg then D.inRight c else D.outRight c)
    let out := (if D.kind c = .virtual then V else S).eval a b
    w = u * out.1⁻¹ ∨ w = v * out.2⁻¹}

abbrev GroupInvariant (D : SemiArcPresentation) (G : Type) [Group G]
    (gen : Nat → G) (S V : GroupWords) := PresentedGroup (D.groupRels G gen S V)

end SemiArcPresentation
end
end QuandleResearch
