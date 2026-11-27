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


/-! Local lifts and a bounded strongly convex potential at fixed gap. -/

/-- A point together with its local coordinate in its lower or upper arc.
The upper label is either 0 or 1; the two centers differ by 1/2. -/
def HasLocal (s a u : ℝ) : Prop :=
  (Lower s u ∧ a = u) ∨
  (Upper s u ∧ ∃ i : ℤ, 0 ≤ i ∧ i ≤ 1 ∧
    a = u + 1 / 4 + (i : ℝ) / 2)

lemma local_inBlock {s a u : ℝ} (h : HasLocal s a u) : InBlock s a := by
  rcases h with ⟨h, rfl⟩ | ⟨h, i, hi0, hi1, ha⟩
  · exact Or.inl h
  · have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · right; left
      have he : a - 1 / 4 = u := by norm_num at ha; linarith
      rw [he]
      exact h
    · right; right
      have he : a - 3 / 4 = u := by norm_num at ha; linarith
      rw [he]
      exact h

lemma block_hasLocal {s a : ℝ} (h : InBlock s a) : ∃ u, HasLocal s a u := by
  rcases h with h | h | h
  · exact ⟨a, Or.inl ⟨h, rfl⟩⟩
  · refine ⟨a - 1 / 4, Or.inr ⟨h, 0, by omega, by omega, ?_⟩⟩
    norm_num
  · refine ⟨a - 3 / 4, Or.inr ⟨h, 1, by omega, by omega, ?_⟩⟩
    norm_num
    <;> ring

lemma local_bounds {s a u : ℝ} (h : HasLocal s a u) :
    |u| < 1 / 4 ∧ |a| < 1 := by
  rcases h with ⟨h, rfl⟩ | ⟨h, i, hi0, hi1, ha⟩
  · exact ⟨h.2.2.1, lt_trans h.2.2.1 (by norm_num)⟩
  · have hu := abs_lt.mp h.2.2.1
    have hi : i = 0 ∨ i = 1 := by omega
    refine ⟨lt_trans h.2.2.1 (by norm_num), abs_lt.mpr ?_⟩
    rcases hi with rfl | rfl <;> norm_num at ha <;>
      constructor <;> linarith [hu.1, hu.2]

lemma int_zero_of_unit_bounds (j : ℤ)
    (hl : -(1 : ℝ) < (j : ℝ)) (hr : (j : ℝ) < 1) : j = 0 := by
  have hl' : (-1 : ℤ) < j := by exact_mod_cast hl
  have hr' : j < 1 := by exact_mod_cast hr
  omega

/-- Upper arcs: the endpoints have the same label, and their local
coordinates have ordinary midpoint u_y, even when the midpoint label differs. -/
lemma upper_local_mean {ux uy uz : ℝ} {ix iy iz j : ℤ}
    (hx : |ux| < 1 / 8) (hy : |uy| < 1 / 8) (hz : |uz| < 1 / 8)
    (ix0 : 0 ≤ ix) (ix1 : ix ≤ 1) (iz0 : 0 ≤ iz) (iz1 : iz ≤ 1)
    (ha : (ux + 1 / 4 + (ix : ℝ) / 2) +
      (uz + 1 / 4 + (iz : ℝ) / 2) -
      2 * (uy + 1 / 4 + (iy : ℝ) / 2) = (j : ℝ)) :
    ix = iz ∧ ux + uz = 2 * uy := by
  have bx := abs_lt.mp hx
  have by' := abs_lt.mp hy
  have bz := abs_lt.mp hz
  have he : ((2 * j - ix - iz + 2 * iy : ℤ) : ℝ) =
      2 * (ux + uz - 2 * uy) := by
    push_cast
    linarith
  have hj := int_zero_of_unit_bounds (2 * j - ix - iz + 2 * iy)
    (by rw [he]; linarith [bx.1, by'.2, bz.1])
    (by rw [he]; linarith [bx.2, by'.1, bz.2])
  have hcast : ((2 * j - ix - iz + 2 * iy : ℤ) : ℝ) = 0 := by
    exact_mod_cast hj
  exact ⟨by omega, by linarith⟩

/-- In the no-wrap, same-band case, both the local-coordinate midpoint
identity and equality of the endpoint coordinate differences hold. -/
lemma same_band_local_mean {sx sy sz ax ay az ux uy uz : ℝ} {j : ℤ}
    (hx : HasLocal sx ax ux) (hy : HasLocal sy ay uy) (hz : HasLocal sz az uz)
    (hs : 2 * sy = sx + sz)
    (ha : ax + az - 2 * ay = (j : ℝ))
    (hband : (sx ≤ 1 / 2 ∧ sz ≤ 1 / 2) ∨
      (1 / 2 + 1 / 240 ≤ sx ∧ 1 / 2 + 1 / 240 ≤ sz)) :
    ux + uz = 2 * uy ∧ ax - az = ux - uz := by
  rcases hband with ⟨hsx, hsz⟩ | ⟨hsx, hsz⟩
  · have hsy : sy ≤ 1 / 2 := by linarith
    rcases hx with ⟨hx, hax⟩ | ⟨hx, _⟩
    · rcases hz with ⟨hz, haz⟩ | ⟨hz, _⟩
      · rcases hy with ⟨hy, hay⟩ | ⟨hy, _⟩
        · have bx := abs_lt.mp hx.2.2.1
          have by' := abs_lt.mp hy.2.2.1
          have bz := abs_lt.mp hz.2.2.1
          have hj := int_zero_of_unit_bounds j
            (by linarith [bx.1, by'.2, bz.1])
            (by linarith [bx.2, by'.1, bz.2])
          subst j
          norm_num at ha
          exact ⟨by linarith, by linarith⟩
        · linarith [hy.1]
      · linarith [hz.1]
    · linarith [hx.1]
  · have hsy : 1 / 2 + 1 / 240 ≤ sy := by linarith
    rcases hx with ⟨hx, _⟩ | ⟨hx, ix, ix0, ix1, hax⟩
    · linarith [hx.2.1]
    rcases hz with ⟨hz, _⟩ | ⟨hz, iz, iz0, iz1, haz⟩
    · linarith [hz.2.1]
    rcases hy with ⟨hy, _⟩ | ⟨hy, iy, _, _, hay⟩
    · linarith [hy.2.1]
    have he := upper_local_mean hx.2.2.1 hy.2.2.1 hz.2.2.1
      ix0 ix1 iz0 iz1 (by linarith : (ux + 1 / 4 + (ix : ℝ) / 2) +
        (uz + 1 / 4 + (iz : ℝ) / 2) -
        2 * (uy + 1 / 4 + (iy : ℝ) / 2) = (j : ℝ))
    have hic : (ix : ℝ) = (iz : ℝ) := by exact_mod_cast he.1
    exact ⟨he.2, by linarith⟩

lemma local_band {s a u : ℝ} (h : HasLocal s a u) :
    s ≤ 1 / 2 ∨ 1 / 2 + 1 / 240 ≤ s := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h.2.1
  · exact Or.inr h.1

def potential (s u : ℝ) : ℝ := 1000000 * s ^ 2 + 2 * u ^ 2

lemma potential_bounds {s a u : ℝ} (h : HasLocal s a u) :
    0 ≤ potential s u ∧ potential s u ≤ 1000001 := by
  have hs := block_s_bounds (local_inBlock h)
  have hu := abs_lt.mp (local_bounds h).1
  have hs2 : s ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith [hs.2])
      (show 0 ≤ 1 + s by linarith [hs.1])]
  have hu2 : u ^ 2 ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - u by linarith [hu.2])
      (show 0 ≤ 1 / 4 + u by linarith [hu.1])]
  unfold potential
  constructor <;> nlinarith [sq_nonneg s, sq_nonneg u]

/-- A large s-gap pays for every possible change in the other coordinate. -/
lemma large_s_gap {sx sy sz ax ay az ux uy uz : ℝ}
    (hx : HasLocal sx ax ux) (hy : HasLocal sy ay uy) (hz : HasLocal sz az uz)
    (hcurv : (sx - sz)^2 / 2 ≤ sx^2 + sz^2 - 2 * sy^2)
    (hlarge : 1 / 115200 ≤ sx^2 + sz^2 - 2 * sy^2) :
    (sx - sz)^2 + (ax - az)^2 ≤
      potential sx ux + potential sz uz - 2 * potential sy uy := by
  have bx := abs_lt.mp (local_bounds hx).2
  have bz := abs_lt.mp (local_bounds hz).2
  have by' := abs_lt.mp (local_bounds hy).1
  have ha2 : (ax - az)^2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - (ax - az) by linarith [bx.2, bz.1])
      (show 0 ≤ 2 + (ax - az) by linarith [bx.1, bz.2])]
  have hu2 : uy^2 ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - uy by linarith [by'.2])
      (show 0 ≤ 1 / 4 + uy by linarith [by'.1])]
  unfold potential
  nlinarith [sq_nonneg ux, sq_nonneg uz]

/-- Key finite-gap geometric estimate, for arbitrary real lifts satisfying
the modular progression equations.  In particular it controls endpoint
differences, not just strict convexity of the potential. -/
theorem potential_gap {sx sy sz ax ay az ux uy uz : ℝ} {j k : ℤ}
    (hx : HasLocal sx ax ux) (hy : HasLocal sy ay uy) (hz : HasLocal sz az uz)
    (hs : 2 * sy = sx + sz + (k : ℝ))
    (ha : ax + az - 2 * ay = (j : ℝ)) :
    (sx - sz)^2 + (ax - az)^2 ≤
      potential sx ux + potential sz uz - 2 * potential sy uy := by
  have hle := midpoint_s_le (local_inBlock hx) (local_inBlock hy)
    (local_inBlock hz) hs ha
  have hk : k ≤ 0 := by
    exact_mod_cast (show (k : ℝ) ≤ 0 by linarith)
  have hsy := (block_s_bounds (local_inBlock hy)).1
  have hcurv : (sx - sz)^2 / 2 ≤ sx^2 + sz^2 - 2 * sy^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (sx + sz) / 2 - sy by linarith)
      (show 0 ≤ (sx + sz) / 2 + sy by linarith)]
  by_cases hzero : k = 0
  · subst k
    norm_num at hs
    rcases local_band hx with hxl | hxh <;> rcases local_band hz with hzl | hzh
    · have hm := same_band_local_mean hx hy hz hs ha (Or.inl ⟨hxl, hzl⟩)
      rw [hm.2]
      unfold potential
      rw [show sy = (sx + sz) / 2 by linarith, show uy = (ux + uz) / 2 by linarith [hm.1]]
      nlinarith [sq_nonneg (sx - sz)]
    · apply large_s_gap hx hy hz hcurv
      have hd : 1 / 57600 ≤ (sx - sz)^2 := by
        nlinarith [mul_nonneg (show 0 ≤ sz - sx - 1 / 240 by linarith)
          (show 0 ≤ sz - sx + 1 / 240 by linarith)]
      linarith
    · apply large_s_gap hx hy hz hcurv
      have hd : 1 / 57600 ≤ (sx - sz)^2 := by
        nlinarith [mul_nonneg (show 0 ≤ sx - sz - 1 / 240 by linarith)
          (show 0 ≤ sx - sz + 1 / 240 by linarith)]
      linarith
    · have hm := same_band_local_mean hx hy hz hs ha (Or.inr ⟨hxh, hzh⟩)
      rw [hm.2]
      unfold potential
      rw [show sy = (sx + sz) / 2 by linarith, show uy = (ux + uz) / 2 by linarith [hm.1]]
      nlinarith [sq_nonneg (sx - sz)]
  · have hk' : k ≤ -1 := by omega
    have hkc : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
    have hdown : 1 / 2 ≤ (sx + sz) / 2 - sy := by linarith
    have hlarge : 1 / 115200 ≤ sx^2 + sz^2 - 2 * sy^2 := by
      nlinarith [mul_nonneg (show 0 ≤ (sx + sz) / 2 - sy - 1 / 2 by linarith)
        (show 0 ≤ (sx + sz) / 2 + sy + 1 / 2 by linarith),
        sq_nonneg (sx - sz)]
    exact large_s_gap hx hy hz hcurv hlarge


end

end QuandleResearch.Erdos142
