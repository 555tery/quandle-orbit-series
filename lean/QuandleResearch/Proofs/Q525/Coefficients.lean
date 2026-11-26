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

/-- A finite square-free coefficient algebra with augmentation to F₂.
All elements in the augmentation kernel square to zero, not merely the
chosen variables. The nonzero product uses exactly n kernel elements. -/
theorem augmented_coefficient_exists (n : Nat) :
    ∃ (R : Type) (r : CommRing R),
      letI := r
      Finite R ∧ (∀ a : R, a + a = 0) ∧
      ∃ aug : R →+* ZMod 2,
        (∀ a, aug a = 0 → a * a = 0) ∧
        ∃ ts : List R, ts.length = n ∧
          (∀ t ∈ ts, aug t = 0) ∧ ts.prod ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨ZMod 2, inferInstance, inferInstance, ?_, RingHom.id _, ?_, ?_⟩
    · intro a
      fin_cases a <;> decide
    · intro a ha
      change a = 0 at ha
      simp [ha]
    · exact ⟨[], rfl, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨R, r, h⟩ := ih
    letI := r
    obtain ⟨hf, hc, aug, hker, ts, hlen, haug, hprod⟩ := h
    letI : Finite R := hf
    let f := TrivSqZeroExt.inlHom R R
    let e : DualNumber R := DualNumber.eps
    let aug' : DualNumber R →+* ZMod 2 :=
      aug.comp (TrivSqZeroExt.fstHom R R R).toRingHom
    have hfin : Finite (DualNumber R) :=
      Finite.of_injective (fun x : DualNumber R => (x.fst, x.snd))
        (fun x y hxy => TrivSqZeroExt.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    refine ⟨DualNumber R, inferInstance, hfin, ?_, aug', ?_, ?_⟩
    · intro a
      apply TrivSqZeroExt.ext
      · simpa only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_zero] using hc a.fst
      · simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_zero] using hc a.snd
    · intro a ha
      change aug a.fst = 0 at ha
      apply TrivSqZeroExt.ext
      · simpa only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_zero] using hker a.fst ha
      · rw [DualNumber.snd_mul, TrivSqZeroExt.snd_zero, mul_comm a.snd a.fst]
        exact hc _
    · refine ⟨e :: ts.map f, by simp [hlen], ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with he | ht
        · subst t
          change aug 0 = 0
          exact map_zero aug
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
          change aug a = 0
          exact haug a ha
      · have hm : (ts.map f).prod = f ts.prod := by
          exact (map_list_prod f ts).symm
        rw [List.prod_cons, hm, mul_comm]
        change (TrivSqZeroExt.inl ts.prod : DualNumber R) *
          TrivSqZeroExt.inr 1 ≠ 0
        rw [TrivSqZeroExt.inl_mul_inr]
        intro hz
        have hz' := congrArg TrivSqZeroExt.snd hz
        exact hprod (by simpa using hz')

/-- Only the square-zero word is needed for the affine proof of part B. -/
theorem coefficient_exists (n : Nat) :
    ∃ (R : Type) (r : CommRing R),
      letI := r
      Finite R ∧ (∀ a : R, a + a = 0) ∧ SquareZeroWord R n := by
  obtain ⟨R, r, h⟩ := augmented_coefficient_exists n
  letI := r
  obtain ⟨hf, hc, aug, hker, ts, hlen, haug, hprod⟩ := h
  exact ⟨R, r, hf, hc, ts, hlen, fun t ht => hker t (haug t ht), hprod⟩

end QuandleResearch.Q525
