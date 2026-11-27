import QuandleResearch.Proofs.Kourovka88a.Words

/-!
# Algebraic equivalence of height-one and all-height relators

Guba's diagrams include relators with all integral heights. The
normal subgroup they generate is unchanged if only height-one
relators are used. This is an algebraic bridge, not a license to
discard the other heights from the graded diagram proof.
-/

namespace QuandleResearch.Issue070

/-- The all-height relation in the convention used for the greedy step. -/
def heightRelator (X C : F) (k : ℤ) : F :=
  X * C ^ k * X⁻¹ * (a ^ k)⁻¹

@[simp] theorem heightRelator_one (X C : F) :
    heightRelator X C 1 = X * C * X⁻¹ * a⁻¹ := by
  simp [heightRelator]

theorem heightRelator_mem_of_one (N : Subgroup F) [N.Normal]
    (X C : F) (h : heightRelator X C 1 ∈ N) (k : ℤ) :
    heightRelator X C k ∈ N := by
  let q := QuotientGroup.mk' N
  have hq : q (heightRelator X C 1) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  have hq' : q X * q C * (q X)⁻¹ * (q a)⁻¹ = 1 := by
    simpa only [heightRelator_one, map_mul, map_inv] using hq
  have hc : q X * q C * (q X)⁻¹ = q a := by
    calc
      _ = (q X * q C * (q X)⁻¹ * (q a)⁻¹) * q a := by group
      _ = _ := by rw [hq', one_mul]
  have hk := congrArg (fun z : F ⧸ N => z ^ k) hc
  rw [conj_zpow] at hk
  apply (QuotientGroup.eq_one_iff _).mp
  change q (heightRelator X C k) = 1
  simp only [heightRelator, map_mul, map_inv, map_zpow]
  rw [hk, mul_inv_cancel]

/-- All-height and height-one normal closures agree even in the
presence of any set of earlier relators. -/
theorem normalClosure_all_heights (S : Set F) (X C : F) :
    Subgroup.normalClosure (S ∪ Set.range (heightRelator X C)) =
      Subgroup.normalClosure (S ∪ {heightRelator X C 1}) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro w hw
    rcases hw with hw | ⟨k, rfl⟩
    · exact Subgroup.subset_normalClosure (Or.inl hw)
    · exact heightRelator_mem_of_one _ X C
        (Subgroup.subset_normalClosure (Or.inr rfl)) k
  · apply Subgroup.normalClosure_le_normal
    intro w hw
    rcases hw with hw | hw
    · exact Subgroup.subset_normalClosure (Or.inl hw)
    · have h : w = heightRelator X C 1 := hw
      subst w
      exact Subgroup.subset_normalClosure (Or.inr ⟨1, rfl⟩)

end QuandleResearch.Issue070
