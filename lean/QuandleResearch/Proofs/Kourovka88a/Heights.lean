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


/-! ## Literal height words

Keep the conjugating segments and repeated period visible in the list,
rather than replacing the entire relation by its reduced representative.
The evaluation theorem supplies the bridge to the algebraic stages.
-/

def rawNatPow (w : RawWord) : ℕ → RawWord
  | 0 => []
  | m+1 => rawNatPow w m ++ w

theorem rawNatPow_eval (w : RawWord) (m : ℕ) :
    FreeGroup.mk (rawNatPow w m) = (FreeGroup.mk w) ^ m := by
  induction m with
  | zero => simp [rawNatPow, FreeGroup.one_eq_mk]
  | succ m ih =>
    rw [rawNatPow, ← FreeGroup.mul_mk, ih, pow_succ]

def rawIntPow (w : RawWord) : ℤ → RawWord
  | .ofNat m => rawNatPow w m
  | .negSucc m => FreeGroup.invRev (rawNatPow w (m+1))

theorem rawIntPow_eval (w : RawWord) (k : ℤ) :
    FreeGroup.mk (rawIntPow w k) = (FreeGroup.mk w) ^ k := by
  cases k with
  | ofNat m =>
    change FreeGroup.mk (rawNatPow w m) = (FreeGroup.mk w) ^ (m : ℤ)
    rw [rawNatPow_eval, zpow_natCast]
  | negSucc m =>
    change FreeGroup.mk (FreeGroup.invRev (rawNatPow w (m+1))) =
      (FreeGroup.mk w) ^ Int.negSucc m
    rw [← FreeGroup.inv_mk, rawNatPow_eval, zpow_negSucc]

/-- The literal cyclic representative used in the greedy relation.
No reduction across the four displayed blocks is performed.
The empty word is used at height zero, since that height contributes
no relation to the normal closure. -/
def literalHeightWord (X C : F) (k : ℤ) : RawWord :=
  if k = 0 then [] else
    X.toWord ++ rawIntPow C.toWord k ++ FreeGroup.invRev X.toWord ++
      FreeGroup.invRev (rawIntPow a.toWord k)

theorem literalHeightWord_eval (X C : F) (k : ℤ) :
    FreeGroup.mk (literalHeightWord X C k) = heightRelator X C k := by
  by_cases hk : k = 0
  · subst k
    change FreeGroup.mk [] = heightRelator X C 0
    rw [← FreeGroup.one_eq_mk]
    simp [heightRelator]
  · simp only [literalHeightWord, ite_eq_right hk, ← FreeGroup.mul_mk,
      ← FreeGroup.inv_mk, rawIntPow_eval, FreeGroup.mk_toWord, heightRelator]

theorem literalHeightWord_zero (X C : F) : literalHeightWord X C 0 = [] := by
  simp [literalHeightWord]


/-! ## Algebra of merging two heights at a fixed rank

These identities describe the exact group values of a candidate merge.
They do not assert that a particular pair of adjacent discs can be
merged in a planar diagram: that requires an appropriate common path.
-/

theorem heightRelator_zero (X C : F) : heightRelator X C 0 = 1 := by
  simp [heightRelator]

/-- Add heights, with the second relation based along the a-power. -/
theorem heightRelator_add (X C : F) (k l : ℤ) :
    heightRelator X C (k+l) =
      heightRelator X C k * a^k * heightRelator X C l * (a^k)⁻¹ := by
  simp only [heightRelator, zpow_add, mul_inv_rev]
  group

/-- Opposite heights give a conjugate inverse, not necessarily a literal inverse. -/
theorem heightRelator_neg (X C : F) (k : ℤ) :
    heightRelator X C (-k) =
      (a^k)⁻¹ * (heightRelator X C k)⁻¹ * a^k := by
  simp only [heightRelator, zpow_neg, mul_inv_rev, inv_inv]
  group

/-- The two-row product with the specified relative conjugator is exactly
the sum-height row. This includes the zero-height deletion case. -/
theorem heightRelator_merge (X C u : F) (k l : ℤ) :
    (u * heightRelator X C k * u⁻¹) *
      ((u*a^k) * heightRelator X C l * (u*a^k)⁻¹) =
      u * heightRelator X C (k+l) * u⁻¹ := by
  rw [heightRelator_add]
  group

theorem heightRelator_merge_cancel (X C u : F) (k : ℤ) :
    (u * heightRelator X C k * u⁻¹) *
      ((u*a^k) * heightRelator X C (-k) * (u*a^k)⁻¹) = 1 := by
  rw [heightRelator_merge, add_neg_cancel, heightRelator_zero]
  simp


/-! ## Exact positive conjugating sides of literal height rows

The two long sides are opposite signed readings of the same positive
word. These statements concern the displayed spelling before possible
cancellation across its four seams.
-/

theorem rawWeight_invRev (w : RawWord) :
    rawWeight (FreeGroup.invRev w) = rawWeight w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    rw [FreeGroup.invRev_cons, rawWeight_append, ih]
    rcases x with ⟨i,s⟩
    simp [FreeGroup.invRev, rawWeight, letterWeight, Nat.add_comm]

theorem literalHeightWord_positive_sides (q : List (Fin 2)) (C : F) (k : ℤ)
    (hk : k ≠ 0) :
    literalHeightWord (positiveWord q) C k =
      q.map (fun x => (x,true)) ++ rawIntPow C.toWord k ++
      FreeGroup.invRev (q.map (fun x => (x,true))) ++
      FreeGroup.invRev (rawIntPow a.toWord k) := by
  simp only [literalHeightWord, ite_eq_right hk, toWord_positiveWord]

theorem literalHeightWord_weight (X C : F) (k : ℤ) (hk : k ≠ 0) :
    rawWeight (literalHeightWord X C k) =
      2*weightedLength X + rawWeight (rawIntPow C.toWord k) +
        rawWeight (rawIntPow a.toWord k) := by
  rw [literalHeightWord, ite_eq_right hk]
  simp only [rawWeight_append, rawWeight_invRev, weightedLength]
  omega

theorem positiveWeight_eq_rawWeight_map (q : List (Fin 2)) :
    positiveWeight q = rawWeight (q.map (fun x => (x,true))) := by
  change weightedLength (positiveWord q) = _
  rw [weightedLength, toWord_positiveWord]

/-- Inverse reading does not change the length of the long side. -/
theorem positive_side_inverse_weight (q : List (Fin 2)) :
    rawWeight (FreeGroup.invRev (q.map (fun x => (x,true)))) =
      positiveWeight q := by
  rw [rawWeight_invRev, positiveWeight_eq_rawWeight_map]

end QuandleResearch.Issue070
