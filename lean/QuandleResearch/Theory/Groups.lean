import Mathlib

namespace QuandleResearch
noncomputable section
/-- Source commutator x⁻¹y⁻¹xy, expressed through Mathlib's
commutator of inverse elements. Do not swap arguments instead. -/
abbrev comm {G : Type*} [Group G] (x y : G) : G := ⁅x⁻¹, y⁻¹⁆
def twisted {G : Type*} [Group G] (f : G → G) : Set G := Set.range (fun x => x⁻¹ * f x)
def innerClass {G : Type*} [Group G] (h : G) : Set G := Set.range (fun x => comm x h)
def IsSubgroupSet {G : Type*} [Group G] (s : Set G) : Prop :=
  ∃ H : Subgroup G, (H : Set G) = s
def AllInner (G : Type*) [Group G] : Prop := ∀ h : G, IsSubgroupSet (innerClass h)
def AllAut (G : Type*) [Group G] : Prop := ∀ f : G ≃* G, IsSubgroupSet (twisted f)
def AllEnd (G : Type*) [Group G] : Prop := ∀ f : G →* G, IsSubgroupSet (twisted f)
abbrev Abelian (G : Type*) [Group G] : Prop := IsMulCommutative G
abbrev FinitelyGenerated (G : Type*) [Group G] : Prop := Group.FG G
def NGenerated (G : Type*) [Group G] (n : Nat) : Prop :=
  ∃ f : Fin n → G, Subgroup.closure (Set.range f) = ⊤
/-- Compatibility aliases, not independent central or derived series. -/
abbrev lowerCentral (G : Type*) [Group G] := lowerCentralSeries G
abbrev derived (G : Type*) [Group G] := derivedSeries G
abbrev Nilpotent (G : Type*) [Group G] : Prop := Group.IsNilpotent G
abbrev Solvable (G : Type*) [Group G] : Prop := IsSolvable G
def ResiduallyNilpotent (G : Type*) [Group G] : Prop :=
  ∀ x : G, (∀ n, x ∈ lowerCentral G n) → x = 1
def ResiduallyFinite (G : Type) [Group G] : Prop :=
  ∀ x : G, x ≠ 1 → ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : G →* F), f x ≠ 1
def VirtuallySolvable (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsSolvable H
def Centerless (G : Type*) [Group G] : Prop := Subgroup.center G = ⊥
abbrev Cyclic (G : Type*) [Group G] : Prop := IsCyclic G
def foldComm {G : Type*} [Group G] (g : Nat → G) : Nat → G
  | 0 => g 0
  | n+1 => comm (foldComm g n) (g (n+1))
def restrictedComm {G : Type*} [Group G] (N : Subgroup G) (h : G) : Set G :=
  {z | ∃ x ∈ N, comm x h = z}
def normalClosureIn {G : Type*} [Group G] (H K : Subgroup G) : Subgroup G :=
  Subgroup.closure {z | ∃ h ∈ H, ∃ k ∈ K, k⁻¹ * h * k = z}
def normalTower {G : Type*} [Group G] (H K : Subgroup G) : Nat → Subgroup G
  | 0 => K
  | n+1 => normalClosureIn H (normalTower H K n)
def TowerDepth {G : Type*} [Group G] (H K : Subgroup G) (n : Nat) : Prop :=
  normalTower H K n = normalTower H K (n+1) ∧
  ∀ m < n, normalTower H K m ≠ normalTower H K (m+1)
def operatorStep {G : Type*} [Group G] (A : Subgroup (G ≃* G)) (H : Subgroup G) : Subgroup G :=
  Subgroup.closure {z | ∃ x ∈ H, ∃ a ∈ A, x⁻¹ * a x = z}
def operatorSeries {G : Type*} [Group G] (A : Subgroup (G ≃* G)) (H : Subgroup G) : Nat → Subgroup G
  | 0 => H
  | n+1 => operatorStep A (operatorSeries A H n)
open scoped Pointwise in
abbrev setProduct {G : Type*} [Group G] (S T : Set G) : Set G := S * T
def TwistedConj {G : Type*} [Group G] (f : G ≃* G) (x y : G) : Prop :=
  ∃ g : G, y = g * x * (f g)⁻¹
def ReidemeisterAtMost {G : Type*} [Group G] (f : G ≃* G) (n : Nat) : Prop :=
  ∃ s : Finset G, s.card ≤ n ∧ ∀ x : G, ∃ y ∈ s, TwistedConj f x y
def FiniteReidemeister {G : Type*} [Group G] (f : G ≃* G) : Prop :=
  ∃ n, ReidemeisterAtMost f n
def RInfinity (G : Type*) [Group G] : Prop := ∀ f : G ≃* G, ¬ FiniteReidemeister f
def innerAutEq {G : Type*} [Group G] (f g : G ≃* G) : Prop :=
  ∃ h : G, ∀ x : G, g x = h * f x * h⁻¹
def isogredient {G : Type*} [Group G] (f g : G ≃* G) : Prop :=
  ∃ h : G, ∀ x : G, g x = h * f (h⁻¹ * x * h) * h⁻¹
def SInfinity (G : Type*) [Group G] : Prop :=
  ∀ f : G ≃* G, ¬ ∃ s : Finset (G ≃* G), ∀ g : G ≃* G,
    innerAutEq f g → ∃ h ∈ s, innerAutEq f h ∧ isogredient g h
def wordValue {G : Type*} [Group G] (k : Nat) (xs : Nat → G) : G := foldComm xs (k-1)
def widthAtMost {G : Type*} [Group G] (S : Set G) (H : Subgroup G) (b : Nat) : Prop :=
  ∀ x ∈ H, ∃ l : List G, l.length ≤ b ∧
    (∀ y ∈ l, y ∈ S ∨ y⁻¹ ∈ S) ∧ l.prod = x

structure GroupObject where
  carrier : Type
  law : Group carrier
attribute [instance] GroupObject.law
structure Presentation where
  generators : Type
  relators : Set (FreeGroup generators)
def Presents (P : Presentation) (G : Type*) [Group G] : Prop :=
  Nonempty (PresentedGroup P.relators ≃* G)
def linearIn (G : Type) [Group G] (K : Type) [Field K] (n : Nat) : Prop :=
  ∃ f : G →* (Matrix (Fin n) (Fin n) K)ˣ, Function.Injective f
def LinearDim (G : Type) [Group G] (n : Nat) : Prop :=
  ∃ (K : Type) (_ : Field K), linearIn G K n
def Linear (G : Type) [Group G] : Prop := ∃ n, LinearDim G n
end
end QuandleResearch
