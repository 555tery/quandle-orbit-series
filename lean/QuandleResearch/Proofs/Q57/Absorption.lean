import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Finite-defect absorption for the normal-generation proof of issue #13
(26 November). All group constructions are native Mathlib constructions.
The universal property of normal generation is an explicit hypothesis. -/
namespace QuandleResearch.Q57
open Subgroup
open scoped Pointwise
variable {M : Type*} [Group M]

/-- Normality of successive joins with a fixed relatively normal subgroup. -/
theorem join_le_normalizer_join {A H V W : Subgroup M}
    (hH : H ≤ A) (hV : V ≤ A) (hW : W ≤ A)
    (hn : A ≤ Subgroup.normalizer H)
    (hv : V ≤ Subgroup.normalizer W) :
    H ⊔ V ≤ Subgroup.normalizer (H ⊔ W : Subgroup M) := by
  apply sup_le
  · exact le_sup_left.trans (H ⊔ W).le_normalizer
  · exact (le_inf (hV.trans hn) hv).trans
      (Subgroup.inf_normalizer_le_normalizer_sup H W)

/-- The usual finite-subnormal normal-generation argument, in one
ambient group. In the application V is the intersected fibre tower. -/
theorem absorb_normal_chain (A H U : Subgroup M) (V : Nat → Subgroup M)
    (hH : H ≤ A) (hn : A ≤ Subgroup.normalizer H)
    (hV : ∀ j, V j ≤ A)
    (hstep : ∀ j, V j ≤ Subgroup.normalizer (V (j+1)))
    (hzero : H ⊔ V 0 = A)
    (hgen : ∀ W : Subgroup M, W ≤ A → A ≤ Subgroup.normalizer W →
      U ≤ W → A ≤ W)
    (n : Nat) (hU : ∀ j ≤ n, U ≤ V j) :
    H ⊔ V n = A := by
  have haux : ∀ j ≤ n, H ⊔ V j = A := by
    intro j
    induction j with
    | zero => intro _; exact hzero
    | succ j ih =>
      intro hj
      have he := ih (Nat.le_trans (Nat.le_succ j) hj)
      apply le_antisymm (sup_le hH (hV _))
      apply hgen _ (sup_le hH (hV _)) _ ((hU _ hj).trans le_sup_right)
      rw [← he]
      exact join_le_normalizer_join hH (hV _) (hV _) hn (hstep j)
  exact haux n le_rfl

/-- Factorization extracted from the lattice join using Mathlib's
pointwise subgroup product theorem; no custom product construction. -/
theorem factor_of_join {A H U : Subgroup M}
    (hn : A ≤ Subgroup.normalizer H) (hu : U ≤ A)
    (he : H ⊔ U = A) {g : M} (hg : g ∈ A) :
    ∃ h ∈ H, ∃ u ∈ U, h * u = g := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left H U (hu.trans hn)
  rw [he] at h
  have hg' : g ∈ (H : Set M) * (U : Set M) := by
    rw [← h]
    exact hg
  exact hg'

end QuandleResearch.Q57
