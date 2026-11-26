import QuandleResearch.Theory.Groups

/-! Concrete presentations of braid-like groups. Indices are zero based.
Source: https://arxiv.org/html/2107.03875v1, §§1.1, 1.3, 5.
Use the standard distant mixed commutation |i-j| ≥ 2 (the preprint's
display (21) prints ≥ 1; this discrepancy is recorded, not silently adopted).
No theorems about these groups are asserted. -/
namespace QuandleResearch.Braids
noncomputable section

abbrev Index (n : Nat) := Fin (n-1)
abbrev Gen (n : Nat) := Bool × Index n
abbrev Word (n : Nat) := FreeGroup (Gen n)

def sigma {n : Nat} (i : Index n) : Word n := FreeGroup.of (false,i)
def rho {n : Nat} (i : Index n) : Word n := FreeGroup.of (true,i)
def rel {G : Type*} [Group G] (a b : G) : G := a * b⁻¹
def adjacent {n : Nat} (i j : Index n) : Prop := i.val + 1 = j.val
def distant {n : Nat} (i j : Index n) : Prop := i.val + 1 < j.val ∨ j.val + 1 < i.val

def braidRels {n : Nat} (s : Index n → Word n) : Set (Word n) :=
  {w | (∃ i j, adjacent i j ∧ w = rel (s i * s j * s i) (s j * s i * s j)) ∨
       (∃ i j, distant i j ∧ w = rel (s i * s j) (s j * s i))}
def squares {n : Nat} (s : Index n → Word n) : Set (Word n) :=
  {w | ∃ i, w = s i * s i}
def mixedDistant (n : Nat) : Set (Word n) :=
  {w | ∃ i j : Index n, distant i j ∧ w = rel (sigma i * rho j) (rho j * sigma i)}
def mixedVirtual (n : Nat) : Set (Word n) :=
  {w | ∃ i j : Index n, adjacent i j ∧
    w = rel (rho i * rho j * sigma i) (sigma j * rho i * rho j)}
def virtualRels (n : Nat) : Set (Word n) :=
  braidRels (@sigma n) ∪ braidRels (@rho n) ∪ squares (@rho n) ∪
    mixedDistant n ∪ mixedVirtual n
def universalRels (n : Nat) : Set (Word n) :=
  braidRels (@sigma n) ∪ mixedDistant n ∪
    {w | ∃ i j : Index n, distant i j ∧ w = rel (rho i * rho j) (rho j * rho i)}
def flatRels (n : Nat) : Set (Word n) := virtualRels n ∪ squares (@sigma n)
def gaussRels (n : Nat) : Set (Word n) :=
  flatRels n ∪ {w | ∃ i : Index n, w = rel (sigma i * rho i) (rho i * sigma i)}

abbrev VB (n : Nat) := PresentedGroup (virtualRels n)
abbrev UB (n : Nat) := PresentedGroup (universalRels n)
abbrev FVB (n : Nat) := PresentedGroup (flatRels n)
abbrev GVB (n : Nat) := PresentedGroup (gaussRels n)

def left {n : Nat} (i : Index n) : Fin n := ⟨i.val, by have := i.isLt; omega⟩
def right {n : Nat} (i : Index n) : Fin n := ⟨i.val+1, by have := i.isLt; omega⟩
def transposition {n : Nat} (i : Index n) : Equiv.Perm (Fin n) :=
  Equiv.swap (left i) (right i)
def pureFreeMap (n : Nat) : Word n →* Equiv.Perm (Fin n) :=
  FreeGroup.lift (fun g => transposition g.2)
def otherFreeMap (n : Nat) : Word n →* Equiv.Perm (Fin n) :=
  FreeGroup.lift (fun g => if g.1 then transposition g.2 else 1)

/-- Image of the free-word kernel in the presented group. This defines
the desired subgroup without needing a proof of descent at statement stage. -/
def pureSubgroup {n : Nat} (rels : Set (Word n)) : Subgroup (PresentedGroup rels) :=
  (pureFreeMap n).ker.map (PresentedGroup.mk rels)
def otherSubgroup {n : Nat} (rels : Set (Word n)) : Subgroup (PresentedGroup rels) :=
  (otherFreeMap n).ker.map (PresentedGroup.mk rels)
abbrev VP (n : Nat) := ↥(pureSubgroup (virtualRels n))
abbrev UP (n : Nat) := ↥(pureSubgroup (universalRels n))
def H (n : Nat) := otherSubgroup (virtualRels n)
def pureDerivedWords (n : Nat) : Set (Word n) :=
  {w | ∃ x ∈ (pureFreeMap n).ker, ∃ y ∈ (pureFreeMap n).ker, comm x y = w}
def virtualAbelianPureRels (n : Nat) : Set (Word n) :=
  virtualRels n ∪ pureDerivedWords n
/-- The quotient of VB by the derived subgroup of VP, given by added relators. -/
abbrev VBmodVPderived (n : Nat) := PresentedGroup (virtualAbelianPureRels n)
def symmetricPart (n : Nat) : Subgroup (VBmodVPderived n) :=
  Subgroup.closure (Set.range (fun i : Index n =>
    PresentedGroup.of (rels := virtualAbelianPureRels n) (true,i)))
def intersection {n : Nat} (rels : Set (Word n)) : Subgroup (PresentedGroup rels) :=
  pureSubgroup rels ⊓ otherSubgroup rels

def classicalRels (n : Nat) : Set (FreeGroup (Index n)) :=
  {w | (∃ i j : Index n, adjacent i j ∧
    w = rel (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i)
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)) ∨
    (∃ i j : Index n, distant i j ∧
    w = rel (FreeGroup.of i * FreeGroup.of j) (FreeGroup.of j * FreeGroup.of i))}
abbrev B (n : Nat) := PresentedGroup (classicalRels n)
def P (n : Nat) : Subgroup (B n) :=
  (FreeGroup.lift (fun i : Index n => transposition i)).ker.map
    (PresentedGroup.mk (classicalRels n))

/-- Specify a homomorphism out of a presented group by its generator images.
Existence of the specified map is part of the specification, never an axiom. -/
def HasImages {A G : Type} [Group G] {rels : Set (FreeGroup A)}
    (f : PresentedGroup rels →* G) (images : A → G) : Prop :=
  ∀ a, f (PresentedGroup.of a) = images a

def artinImage {n : Nat} (i : Index n) (j : Fin n) : FreeGroup (Fin n) :=
  let x := FreeGroup.of (left i)
  let y := FreeGroup.of (right i)
  if j = left i then x*y*x⁻¹ else if j = right i then x else FreeGroup.of j

def psiImage {n : Nat} (k l : Int) (i : Index n) (j : Fin n) : FreeGroup (Fin n) :=
  let x := FreeGroup.of (left i)
  let y := FreeGroup.of (right i)
  if j = left i then x^(-l)*y^(-k)*x*y^k*x^l
  else if j = right i then x^(-l)*y*x^l else FreeGroup.of j

def swapImage {n : Nat} (i : Index n) (j : Fin n) : FreeGroup (Fin n) :=
  FreeGroup.of (transposition i j)

def IsExtendedPsi {n : Nat} (k l : Int)
    (f : UB n →* (FreeGroup (Fin n) ≃* FreeGroup (Fin n))) : Prop :=
  ∀ i : Index n, ∀ j : Fin n,
    (f (PresentedGroup.of (rels := universalRels n) (false,i))).symm (FreeGroup.of j) = artinImage i j ∧
    (f (PresentedGroup.of (rels := universalRels n) (true,i))).symm (FreeGroup.of j) = psiImage k l i j

/-- The capital Psi of §5.1 acts on the n strand generators plus y.
The article's right-action convention is represented by inverse images
under Mathlib's ordinary composition of automorphisms. -/
abbrev ExtendedFree (n : Nat) := FreeGroup (Option (Fin n))
def strand {n : Nat} (j : Fin n) : ExtendedFree n := FreeGroup.of (some j)
def extraGen (n : Nat) : ExtendedFree n := FreeGroup.of none
def capitalArtin {n : Nat} (i : Index n) (j : Option (Fin n)) : ExtendedFree n :=
  match j with
  | none => extraGen n
  | some j =>
    let x := strand (left i)
    let y := strand (right i)
    if j = left i then x*y*x⁻¹ else if j = right i then x else strand j
def capitalPsiImage {n : Nat} (k l : Int) (i : Index n) (j : Option (Fin n)) : ExtendedFree n :=
  match j with
  | none => extraGen n
  | some j =>
    let x := strand (left i)
    let z := strand (right i)
    let y := extraGen n
    if j = left i then y⁻¹*x^(-l)*z^(-k)*x*z^k*x^l*y
    else if j = right i then y⁻¹*x^(-l)*z*x^l*y else strand j
def IsCapitalPsi {n : Nat} (k l : Int)
    (f : UB n →* (ExtendedFree n ≃* ExtendedFree n)) : Prop :=
  ∀ (i : Index n) (j : Option (Fin n)),
    (f (PresentedGroup.of (rels := universalRels n) (false,i))).symm (FreeGroup.of j) =
      capitalArtin i j ∧
    (f (PresentedGroup.of (rels := universalRels n) (true,i))).symm (FreeGroup.of j) =
      capitalPsiImage k l i j

end
end QuandleResearch.Braids
