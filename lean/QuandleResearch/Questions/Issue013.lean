import QuandleResearch.Theory.OrbitSeriesCore

/-! BCNW Question 5.7, arXiv:2004.10227v3 §5.1.
https://arxiv.org/html/2004.10227v3
https://github.com/555tery/quandle-orbit-series/issues/13

The base and each full fibre must individually belong to the class.
In particular there is NO uniformity hypothesis on the fibre bounds
in the OS_omega question. The ambient action on each subquandle is
the shared BCNW representation already used for Question 5.25.
-/
namespace QuandleResearch.Issue013
open BCNW
universe u v

def OSomega {X : Type*} [_root_.Quandle X] (s : Set X) : Prop :=
  ∃ n : Nat, 0 < n ∧ OSBound s n

def fibre {X Y : Type*} [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y) (b : Y) : Set X := f ⁻¹' {b}

/-- First question: extension closure, with no finiteness hypothesis. -/
def extensionOS : Prop :=
  ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
    [Nonempty X] [Nonempty Y] (f : ShelfHom X Y), Function.Surjective f →
    OS (Set.univ : Set Y) → (∀ b : Y, OS (fibre f b)) →
    OS (Set.univ : Set X)

/-- Second question: the bound on each fibre may depend on b. -/
def extensionOSomega : Prop :=
  ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
    [Nonempty X] [Nonempty Y] (f : ShelfHom X Y), Function.Surjective f →
    OSomega (Set.univ : Set Y) → (∀ b : Y, OSomega (fibre f b)) →
    OSomega (Set.univ : Set X)

def answer : Prop := extensionOS.{u,v} ∧ ¬ extensionOSomega.{u,v}

/-- A principal series has stabilized at the specified step. The
finite-index formulation avoids assigning a value to infinity. -/
def StableAt {X : Type*} [_root_.Rack X] (s : Set X) (x : X) (n : Nat) : Prop :=
  principalSeries s x n = principalSeries s x (n+1)

/-- Stronger manuscript target, not needed in its sharp form to answer
the original question. No assertion of minimal depth is assumed. -/
def additiveBound : Prop :=
  ∀ (X : Type u) (Y : Type v) [_root_.Quandle X] [_root_.Quandle Y]
    (f : ShelfHom X Y), Function.Surjective f →
    ∀ (x : X) (r m : Nat),
      StableAt Set.univ (f x) r →
      StableAt (fibre f (f x)) x m →
      StableAt Set.univ x (r+m)

end QuandleResearch.Issue013
