import QuandleResearch.Questions.Issue014
import QuandleResearch.Proofs.Q525.OrbitLemmas

/-! Final logical step of Corollary 1.3 of q525_preprint_en.tex.
These theorems do not assume the original question or its answer.
The hypotheses are the existence of the finite counterexample families,
whose group-theoretic constructions are separate proof obligations. -/
namespace QuandleResearch.Issue014
open BCNW
universe u

theorem negativeA_of_unboundedJAt (k : Nat) (hk : 0 < k)
    (h : unboundedJAt.{u} k) : negativeA.{u} := by
  intro hb
  obtain ⟨j, hj, hbound⟩ := hb k hk
  obtain ⟨X, q, hX⟩ := h j hj
  letI := q
  obtain ⟨hf, hn, hlr, hnot⟩ := hX
  exact hnot (@hbound X q hf hn hlr)

theorem negativeB_of_unboundedIAt (j : Nat) (hj : 0 < j)
    (h : unboundedIAt.{u} j) : negativeB.{u} := by
  intro hb
  obtain ⟨i, hi, hbound⟩ := hb j hj
  obtain ⟨X, q, hX⟩ := h i hi
  letI := q
  obtain ⟨hf, hn, htos, hnot⟩ := hX
  exact hnot (@hbound X q hf hn htos)

theorem bothNegative_of_manuscriptTargets (h : manuscriptTargets.{u}) :
    bothNegative.{u} :=
  ⟨negativeA_of_unboundedJAt 2 (by decide) h.1,
   negativeB_of_unboundedIAt 2 (by decide) h.2⟩

/-- Reduction of part A to finite LR_2 quandles having a marked
non-singleton principal term at every prescribed depth.
This is precisely the kind of witness provided by the NTT filtration. -/
theorem unboundedJAt_two_of_principal_witnesses
    (h : ∀ n : Nat, 0 < n → ∃ (X : Type u) (q : _root_.Quandle X),
      letI := q
      Finite X ∧ LocallyReductive (X := X) 2 ∧
      ∃ x y : X, y ≠ x ∧ y ∈ principalSeries Set.univ x n) :
    unboundedJAt.{u} 2 := by
  intro n hn
  obtain ⟨X, q, hX⟩ := h n hn
  letI := q
  obtain ⟨hf, hlr, x, y, hne, hy⟩ := hX
  exact ⟨X, q, hf, ⟨x⟩, hlr, not_trivializing_of_principal hy hne⟩

/-- Reduction of part B to finite quandles with trivial inner orbits
and an explicit violation of the i-reductivity identity. -/
theorem unboundedIAt_two_of_trivial_orbit_witnesses
    (h : ∀ n : Nat, 0 < n → ∃ (X : Type u) (q : _root_.Quandle X),
      letI := q
      Finite X ∧ (∀ x : X, TrivialOn (orbitIn Set.univ x)) ∧
      ∃ (a b : X) (cs : List X), cs.length = n ∧ leftFold a cs ≠ leftFold b cs) :
    unboundedIAt.{u} 2 := by
  intro n hn
  obtain ⟨X, q, hX⟩ := h n hn
  letI := q
  obtain ⟨hf, ht, a, b, cs, hlen, hne⟩ := hX
  exact ⟨X, q, hf, ⟨a⟩, trivializingTwo_of_trivial_orbits ht,
    fun hr => hne (hr a b cs hlen)⟩

#print axioms bothNegative_of_manuscriptTargets
#print axioms unboundedJAt_two_of_principal_witnesses
#print axioms unboundedIAt_two_of_trivial_orbit_witnesses
end QuandleResearch.Issue014
