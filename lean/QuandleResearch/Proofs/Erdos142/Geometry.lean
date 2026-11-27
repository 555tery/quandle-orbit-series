import Mathlib

/-!
First geometric checkpoint for Erdős #142.  The proposed block is described
by real lifts of torus coordinates, not by assuming any convexity property.
Negative a-coordinates in the lower band are intentional lifts modulo 1.
The gap is fixed at 1/240.  No asymptotic theorem is asserted in this file.
-/
namespace QuandleResearch.Erdos142

noncomputable section

def Lower (s a : ℝ) : Prop :=
  0 < s ∧ s ≤ 1 / 2 ∧ |a| < 1 / 4 ∧ |a| < 1 / 20 + 3 / 5 * s

def Upper (s u : ℝ) : Prop :=
  1 / 2 + 1 / 240 ≤ s ∧ s < 5 / 6 ∧ |u| < 1 / 8 ∧
    |u| < 1 / 10 + 3 / 5 * (s - 1 / 2) ∧
    |u| < 1 / 5 - 3 / 5 * (s - 1 / 2)

def InBlock (s a : ℝ) : Prop :=
  Lower s a ∨ Upper s (a - 1 / 4) ∨ Upper s (a - 3 / 4)

lemma block_s_bounds {s a : ℝ} (h : InBlock s a) : 0 < s ∧ s < 5 / 6 := by
  rcases h with h | h | h
  · exact ⟨h.1, by linarith [h.2.1]⟩
  · exact ⟨by linarith [h.1], h.2.1⟩
  · exact ⟨by linarith [h.1], h.2.1⟩

lemma no_integer_between (k m : ℤ) (h₁ : (m : ℝ) < (k : ℝ))
    (h₂ : (k : ℝ) < (m : ℝ) + 1) : False := by
  have h₃ : m < k := by exact_mod_cast h₁
  have h₄ : k < m + 1 := by exact_mod_cast h₂
  omega

lemma no_up_LL {sx sy sz ax ay az cy : ℝ} {j : ℤ}
    (hx : Lower sx ax) (hz : Lower sz az) (hy : Upper sy (ay - cy))
    (hc : cy = 1 / 4 ∨ cy = 3 / 4)
    (hs : 2 * sy = sx + sz + 1)
    (ha : ax + az - 2 * ay = (j : ℝ)) : False := by
  have bx := abs_lt.mp hx.2.2.2
  have bz := abs_lt.mp hz.2.2.2
  have by' := abs_lt.mp hy.2.2.2.2
  have h₁ : -(1 / 2 : ℝ) < ax + az - 2 * (ay - cy) := by
    linarith [bx.1, bz.1, by'.2]
  have h₂ : ax + az - 2 * (ay - cy) < (1 / 2 : ℝ) := by
    linarith [bx.2, bz.2, by'.1]
  rcases hc with hc | hc
  · apply no_integer_between j (-1)
    · norm_num
      linarith
    · norm_num
      linarith
  · apply no_integer_between j (-2)
    · norm_num
      linarith
    · norm_num
      linarith

lemma no_up_LH {sx sy sz ax ay az cy cz : ℝ} {j : ℤ}
    (hx : Lower sx ax) (hz : Upper sz (az - cz))
    (hy : Upper sy (ay - cy))
    (hc : cy = 1 / 4 ∨ cy = 3 / 4)
    (hd : cz = 1 / 4 ∨ cz = 3 / 4)
    (hs : 2 * sy = sx + sz + 1)
    (ha : ax + az - 2 * ay = (j : ℝ)) : False := by
  have bx := abs_lt.mp hx.2.2.2
  have bz := abs_lt.mp hz.2.2.2.1
  have by' := abs_lt.mp hy.2.2.2.2
  have h₁ : -(1 / 4 : ℝ) < ax + (az - cz) - 2 * (ay - cy) := by
    linarith [bx.1, bz.1, by'.2]
  have h₂ : ax + (az - cz) - 2 * (ay - cy) < (1 / 4 : ℝ) := by
    linarith [bx.2, bz.2, by'.1]
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · apply no_integer_between j (-1) <;> norm_num <;> linarith
  · apply no_integer_between j 0 <;> norm_num <;> linarith
  · apply no_integer_between j (-2) <;> norm_num <;> linarith
  · apply no_integer_between j (-1) <;> norm_num <;> linarith

lemma no_up_HH {sx sy sz ux uy uz : ℝ}
    (hx : Upper sx ux) (hz : Upper sz uz) (hy : Upper sy uy)
    (hs : 2 * sy = sx + sz + 1) : False := by
  linarith [hx.1, hz.1, hy.2.1]

lemma no_up_center {sx sy sz ax ay az cy : ℝ} {j : ℤ}
    (hx : InBlock sx ax) (hz : InBlock sz az)
    (hy : Upper sy (ay - cy)) (hc : cy = 1 / 4 ∨ cy = 3 / 4)
    (hs : 2 * sy = sx + sz + 1)
    (ha : ax + az - 2 * ay = (j : ℝ)) : False := by
  rcases hx with hx | hx | hx <;> rcases hz with hz | hz | hz
  · exact no_up_LL hx hz hy hc hs ha
  · exact no_up_LH hx hz hy hc (Or.inl rfl) hs ha
  · exact no_up_LH hx hz hy hc (Or.inr rfl) hs ha
  · exact no_up_LH hz hx hy hc (Or.inl rfl) (by linarith) (by linarith)
  · exact no_up_HH hx hz hy hs
  · exact no_up_HH hx hz hy hs
  · exact no_up_LH hz hx hy hc (Or.inr rfl) (by linarith) (by linarith)
  · exact no_up_HH hx hz hy hs
  · exact no_up_HH hx hz hy hs

theorem no_upward {sx sy sz ax ay az : ℝ} {j : ℤ}
    (hx : InBlock sx ax) (hy : InBlock sy ay) (hz : InBlock sz az)
    (hs : 2 * sy = sx + sz + 1)
    (ha : ax + az - 2 * ay = (j : ℝ)) : False := by
  have hxs := (block_s_bounds hx).1
  have hzs := (block_s_bounds hz).1
  rcases hy with hy | hy | hy
  · linarith [hy.2.1]
  · exact no_up_center hx hz hy (Or.inl rfl) hs ha
  · exact no_up_center hx hz hy (Or.inr rfl) hs ha

theorem midpoint_s_le {sx sy sz ax ay az : ℝ} {j k : ℤ}
    (hx : InBlock sx ax) (hy : InBlock sy ay) (hz : InBlock sz az)
    (hs : 2 * sy = sx + sz + (k : ℝ))
    (ha : ax + az - 2 * ay = (j : ℝ)) :
    2 * sy ≤ sx + sz := by
  have hxs := (block_s_bounds hx).1
  have hzs := (block_s_bounds hz).1
  have hys := (block_s_bounds hy).2
  have hk : k < 2 := by
    exact_mod_cast (show (k : ℝ) < 2 by linarith)
  by_contra hn
  have hkp : 0 < k := by
    exact_mod_cast (show (0 : ℝ) < (k : ℝ) by linarith)
  have he : k = 1 := by omega
  subst k
  exact no_upward hx hy hz (by simpa using hs) ha

/-- Arithmetic comparison only: this does not establish the block's measure. -/
theorem rational_area_comparison :
    (71 / 240 : ℚ) - 1 / 480 = 47 / 160 ∧ (7 / 24 : ℚ) < 47 / 160 := by
  norm_num

end

end QuandleResearch.Erdos142
