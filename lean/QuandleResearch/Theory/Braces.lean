import QuandleResearch.Theory.Groups

namespace QuandleResearch
noncomputable section
/-- The first group law is written additively in the source. -/
structure SkewBrace where
  carrier : Type
  addLaw : Group carrier
  mulLaw : Group carrier
  braceLaw : ∀ a b c : carrier,
    mulLaw.mul a (addLaw.mul b c) =
      addLaw.mul (addLaw.mul (mulLaw.mul a b) (addLaw.inv a)) (mulLaw.mul a c)
namespace SkewBrace
def add (B : SkewBrace) := B.addLaw.mul
def neg (B : SkewBrace) := B.addLaw.inv
def mul (B : SkewBrace) := B.mulLaw.mul
def lambda (B : SkewBrace) (a b : B.carrier) := B.add (B.neg a) (B.mul a b)
def star (B : SkewBrace) (a b : B.carrier) := B.add (B.lambda a b) (B.neg b)
def addClosure (B : SkewBrace) (s : Set B.carrier) : Set B.carrier :=
  letI := B.addLaw
  (Subgroup.closure s : Set B.carrier)
def IsIdeal (B : SkewBrace) (s : Set B.carrier) : Prop :=
  (letI := B.addLaw; ∃ H : Subgroup B.carrier, H.Normal ∧ (H : Set B.carrier) = s) ∧
  (letI := B.mulLaw; ∃ H : Subgroup B.carrier, H.Normal ∧ (H : Set B.carrier) = s) ∧
  ∀ a b, b ∈ s → B.lambda a b ∈ s
def leftSeries (B : SkewBrace) : Nat → Set B.carrier
  | 0 => Set.univ
  | n+1 => B.addClosure {z | ∃ a : B.carrier, ∃ b ∈ B.leftSeries n, B.star a b = z}
def stableLeft (B : SkewBrace) : Set B.carrier := {x | ∀ n, x ∈ B.leftSeries n}
def nilpotentType (B : SkewBrace) : Prop := letI := B.addLaw; Nilpotent B.carrier
def nilpotentMul (B : SkewBrace) : Prop := letI := B.mulLaw; Nilpotent B.carrier
def solvableAdd (B : SkewBrace) : Prop := letI := B.addLaw; Solvable B.carrier
def solvableMul (B : SkewBrace) : Prop := letI := B.mulLaw; Solvable B.carrier
def leftResidual (B : SkewBrace) : Set B.carrier :=
  {x | ∀ s : Set B.carrier, B.IsIdeal s → (∃ n, B.leftSeries n ⊆ s) → x ∈ s}
structure Embedding (A B : SkewBrace) where
  map : A.carrier → B.carrier
  inj : Function.Injective map
  addHom : ∀ x y, map (A.add x y) = B.add (map x) (map y)
  mulHom : ∀ x y, map (A.mul x y) = B.mul (map x) (map y)
end SkewBrace
end
end QuandleResearch
