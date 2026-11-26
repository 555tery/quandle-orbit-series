import QuandleResearch.Theory.Interfaces
import QuandleResearch.Theory.BraidGroups

/-!
# Issue 28: Bardakov et al. Question 4.2 (2021) — image of H_n under Psi
https://github.com/555tery/quandle-orbit-series/issues/28

Formalization status: PARTIAL.
Remaining obligation: Source equations (30)–(31) encoded on ordered pair basis over explicit Laurent ring. Independent audit of matrix convention and construction of the representation remain.

Source and target from the issue:
## Source / explicit published research question
Bardakov, Emel'yanenkov, Ivanov, Kozlovskaya, Nasybullov, Vesnin, *Virtual and universal braid groups, their quotients and representations*, [arXiv:2107.03875v1, printed p. 18](https://arxiv.org/pdf/2107.03875#page=18). Original PDF formulation checked.

## Target
Describe Ψ(H_n), where H_n is the kernel of the map VB_n → S_n sending σ_i to 1 and ρ_i to the adjacent transposition; use the representation Ψ defined in §3, equations (30)–(31).
-/

namespace QuandleResearch.Issue028
noncomputable section
open Classical

open Braids
/-- Basis e_(a,b) with a<b; Laurent variables t and t_i are indexed by
none and some i, respectively. Matrix rows encode the images of basis
vectors, matching the right-action convention of equations (30)–(31). -/
abbrev Pair (n : Nat) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Laurent (n : Nat) := AddMonoidAlgebra Int (Option (Index n) → Int)
def monomial {n : Nat} (v : Option (Index n)) (k : Int) : Laurent n :=
  Finsupp.single (fun j => if j = v then k else 0) 1
def swappedPair {n : Nat} (i : Index n) (p q : Pair n) : Prop :=
  (q.val.1 = transposition i p.val.1 ∧ q.val.2 = transposition i p.val.2) ∨
  (q.val.2 = transposition i p.val.1 ∧ q.val.1 = transposition i p.val.2)
def sigmaEntry {n : Nat} (i : Index n) (p q : Pair n) : Laurent n :=
  if swappedPair i p q then
    if p.val = (left i,right i) then monomial none 1 else 1
  else 0
def rhoEntry {n : Nat} (i : Index n) (p q : Pair n) : Laurent n :=
  if swappedPair i p q then
    if p.val = (left i,right i) then 1
    else if p.val.1 = left i ∨ p.val.2 = left i then monomial (some i) 1
    else if p.val.1 = right i ∨ p.val.2 = right i then monomial (some i) (-1)
    else 1
  else 0
def IsPsi {n : Nat}
    (f : VB n →* (Matrix (Pair n) (Pair n) (Laurent n))ˣ) : Prop :=
  ∀ (i : Index n) (p q : Pair n),
    (f (PresentedGroup.of (rels := virtualRels n) (false,i))).val p q = sigmaEntry i p q ∧
    (f (PresentedGroup.of (rels := virtualRels n) (true,i))).val p q = rhoEntry i p q
def verifiesImage
    (answer : ∀ n, Subgroup ((Matrix (Pair n) (Pair n) (Laurent n))ˣ)) : Prop :=
  ∀ n, 2 ≤ n →
    ∃ f : VB n →* (Matrix (Pair n) (Pair n) (Laurent n))ˣ,
      IsPsi f ∧ (H n).map f = answer n

end
end QuandleResearch.Issue028
