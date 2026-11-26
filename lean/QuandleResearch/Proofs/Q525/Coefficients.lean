import Mathlib.Algebra.DualNumber
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite coefficient rings for the elementary Q525 constructions.
Iterating the native dual-number algebra gives the square-free
polynomial algebra over F₂. Only a list of square-zero elements
with nonzero product is needed for the second counterexample. -/
namespace QuandleResearch.Q525

def SquareZeroWord (R : Type*) [CommRing R] (n : Nat) : Prop :=
  ∃ ts : List R, ts.length = n ∧
    (∀ t ∈ ts, t * t = 0) ∧ ts.prod ≠ 0

/-- No external group-theoretic inputs: adjoining one dual number
extends the list by a new square-zero element. -/
theorem coefficient_exists (n : Nat) :
    ∃ (R : Type) (r : CommRing R),
      letI := r
      Finite R ∧ (∀ a : R, a + a = 0) ∧ SquareZeroWord R n := by
  induction n with
  | zero =>
    refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ?_⟩
    · intro a
      fin_cases a <;> decide
    · exact ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨R, r, h⟩ := ih
    letI := r
    obtain ⟨hf, hc, ts, hlen, hsq, hprod⟩ := h
    letI : Finite R := hf
    let f := TrivSqZeroExt.inlHom R R
    let e : DualNumber R := DualNumber.eps
    have hfin : Finite (DualNumber R) :=
      Finite.of_injective (fun x : DualNumber R => (x.fst, x.snd))
        (fun x y hxy => TrivSqZeroExt.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    refine ⟨DualNumber R, inferInstance, hfin, ?_, ?_⟩
    · intro a
      apply TrivSqZeroExt.ext
      · simpa only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_zero] using hc a.fst
      · simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_zero] using hc a.snd
    · refine ⟨e :: ts.map f, by simp [hlen], ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with he | ht
        · subst t
          exact DualNumber.eps_mul_eps
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
          rw [← map_mul, hsq a ha, map_zero]
      · have hm : (ts.map f).prod = f ts.prod := by
          exact (map_list_prod f ts).symm
        rw [List.prod_cons, hm, mul_comm]
        change (TrivSqZeroExt.inl ts.prod : DualNumber R) *
          TrivSqZeroExt.inr 1 ≠ 0
        rw [TrivSqZeroExt.inl_mul_inr]
        intro hz
        have hz' := congrArg TrivSqZeroExt.snd hz
        exact hprod (by simpa using hz')

end QuandleResearch.Q525
